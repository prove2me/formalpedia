-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1974
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:21:31.255009+00:00
-- url     : https://prove2.me/submissions/76568524-21ff-469c-b396-596a0ae93182

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 354856115 ≤ n < 355035971 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 354857365 1250 354856115 354856123
    0x3060b010e031f110408010e0a060605030d2a08030c030106030c08010308030705090411190806060405031009030e1804050c09190b040b0301091b05040c1202030a021b0f 74
    0xe8441d010750300c02d03801c00c1c420300c1a200803c0b41d0414030050028035810400c0c02d041c1a03110f540c0144480b0740c00d120141184200c0021984050b5005607806c00005840310105600ca9100e0400d040c0007034001c1c3c1007018980c001c3d84190341c10120074019015a1000350356492483e4108940c003060b50117000c07004014041e0140070711413240340e0a01c0d1051456040d0340c1d5403100c40c0400307441102044008130700d803100c40e107442e8083c0380080c55040c0a2511104240a405d543c947c06040030320004405001060013801e1260030780e019200010050b21132604ca01c501180104241c42044d4104031982c5010805038540c68a030b48038810304040021001e00d01428414506400541401d004640543c01c101c20158104a0440120903101d8007080a51b10000043d028107a500c4509506501c0c0500e10000c121041424580e04d10b10000340c80400c40d90b920170081110314009500700425403035000c042d444040f9034015a4084644400141003210306895018030b40c8152402084036400b4000418050030108 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 354858615 1250 354857365 354857387
    0x12030504030b07110303040b13021804030906031b030f060308160b130f03080402030f030307020c0a050f01082a0f030f1f0b070c1805041b080601121103010603060b01 73
    0x4104090800030313008031075590f440010806841d0004500100d0107a0b508a8461150160003c2036490740710014021402c5031503051f10300310085180a1000110303540240180c40d10800e00c044800920551444164003419001d032001c0203680c1c0e140000300019040c0f002500c00c5008100b1440c12041030303032501c1105e02c800030f003401d40300c80702280d28440016161040040120391524203443d89440f54808285462034081c540402c0380800b01c100030000e580010300d039074a044201d074070300d40d0342d035030b91040c0040220b0300c0b130340e5500049841e00001c0400c80d032001c081100100d00511013600d0b0890301095006900f04826094440400000340040340c00c1c0c42c850250010050310000307241903034100d12044884124440d80c888000007183c100c084c82600140d56000b03107104000d032041030050481420081204590480c1c07401e19005801c01030b150502da0344019114118010207659007888105401c0c2443c0b41011208048541b24030ba03c2c540f800e001d40401548600d80221300041080005040b0b00c040c1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 354859865 1250 354858615 354858617
    0x603020403021003022a2e0b0105030f0a1107051203010303080a05091e030d050109060608090304080705090402060c0114180307170306042a0807091202100912030504030b07 76
    0x40c40083c910150504003030030402c50071b02c40024492207441d8240e042c41081400003103488a11a003c1074203035580c503a05c51a038141030308200400d01d001d100565050005541d8512002020000101c0d0011142c1c4110803580c0d40880290401e011955804d2400807114a14050b11501100410400d50080200d42c1c00c2020050305006c0c620b48281c02c43e9480c0c50710101086503446120000708194000c0c01240d40c01c601c2008140b005603115607110b00500528895600019808c4002441c6850080182c41c20b40d010036000c3c0c000580351404120741ea0f0000f60059a100c0000c0002c1403a03a1070074403e00d00c5045108100024a107803c1203031541109030b482416101d43c01c00c024010016458100390405400c055541c00d8603912440041401082154614015990100c202100001080614011415481c2d860a010b540c0b0850121141800e51180342c0340d40680034210801440d00003403000705064103240c000d5846544440c070301c401007420f05050380801d00020b424800c0c016940c001076848681 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 354861115 1250 354859865 354859867
    0xf1508072c04020f0d09021011070603090305040f030b0f1b09011209050703050307060c0903030905012012070c050d050601030b04080d0c1707020604052113060302040302100302 78
    0x241c51a2981410010440303910300c400340300103a202990340c0781d054454040101150544803000a54080010078150400303034403c1525400ca400d04078403401031341a81c0d802c0d16000c0c109480c90098280c014013401c0030110140300040c0030200f0480548203c3d50000d40c05908200342d030303040c01062102e80c1c450140c041c48805402c0c0e08040b10094418084900c146000e10f080701d0b02001a03802e01c001024100e42c014114011000c0c008103000d070010140c003055000d80000c1082c1652444203551054582c0301c01004581600c0b010021903004420007518441211001d07185050b10b800b00c00e062600d180580c07210000c0101d040020b0011001d166000b03407000381ca824142c0c03003850b140c0ca41c0e00d82d0f0521004009046c20400202041504070507a240b010b032100040c45554104203000d4880030031510b010ae845680d12000528103880010064040c58114019140010342c408540e080c000d16404a29030b100e01c1007101d841d414101c0032244c80140420ba80041e101c0d0305510400003071150b151280307420540 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 354862365 1250 354861115 354861137
    0x5010e09070f050a0903021203070203060f0115050304021f09060912051b06070501150e0a0507080708060303090306041119060503011e09020a03140108070b07020f04060f150807 78
    0x9000308650b1a040901e0034419240c0c20329030300c1151409207a0b003000b500404025001594071100101030a2039510031000d4909503902c80c0d21106001d9001d2096070841680040c400701c10a00410041d50414005030201c001892070314404c1050441c1e40c80d892001441004003000036603400440a809014103034a888101d100a488065840030b46003100701d01c1c0c0140071100700c0e00d0b540b480c0071541040e0b070120090100c696108101d03001001607110f5a52500c219100258040106100e15441911107480700d101680703d103401200c1801c0014a8640c1501c810050484e10741e5082080038403403482003400950341508481484070030301d011442801407000b08c3d40c013442019044010fa90548002d0007015040c0c1c3c224030341211034901c1030f40c8820b0b6018400a03552002c182d0507007050140e86004206140541d903521140c43e87c3d00c031030b0700c610b0068034000c0c802880145440b0f4902d4025140040c000301d401a1100340b40000680644e00600301c02120349031100a450b080741c0025845022030410851501d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 354863615 1250 354862365 354862367
    0x11150903030904051e0106030e0d03180b150d0b15091b03130c06120c0f0512060609030d020a14150105060c12040f06020c0f060708130302030a03050405010e0907 71
    0x4010515550f01c030300c0d00c80700040e00d0681d0a04807900c1440007140c0388031340303940d40b084050300034503500700c0140c200c0c040e14580804550081c011541a0402801002c95140350b42c0c8440ba11540007900c1c4101511184405410a5541d044004c0003540245240c0d800c600780182c110b0304011102d80450300a000510811420031000249004100070350f0b403801d82d407961164006881b43c81e01410052031132103401c3c001b00d003141d48151059400e442410042061001e03c2d541175422600c25060140002c5c001c00029440080641c0c00980018002d010b840c20140d410000038140709010380c900740140d00c010620350901075250a081c01050b200405001a00c0da01c1005501100e0705004131b07070003400c0c0018418040101003040c180c680c0a00b540450712213498a08600158003a84101c2005100703c8040a80a182540c0d0520501800038202031520f046540c5000302500003800d40050750101c02c0d800005a00e00340243c12840340710303903100c590320f50400740050300c00802041628001d0502900b0030600ca = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 354864865 1250 354863615 354863617
    0x50a1406090403020a0c140f04090503091903020406090519050601080f090309040e2104141504180609050a0b010e01031d030d060e1303051210121115090303 69
    0x44481070301d840d041c40d40e032810103034640082800b00620541d02c0314800079045180031041090f00504541c110000310790101000180c890744800501181c10801c010b0702c95141c096180d00d0902504105030003e550b9a4000070200c482c10b510246d081900d40041007848882443e14802c1c3c507141040400c058208000001c040d01e80060100d600445500d002c220204002c200350303103005100800501c13050f09400d0700ea5454081c2d0216214201c113440486801e200c2500007518140c4420b0550145101c440713a0800040d05202e00c100a0b1000c1c040001140340c02000c0c959504602000c3d01c0820361510341580030007201c0b00204403200d00e0385045110001070ba40a0100c8803069802d05e40450305100ca400a0b00c000024445094041c0c800040e40002645040d000041181c08420010505580342d45030a000202a4640100025401c0210b442240440c1c4507154020317000300c56280b4815202c80d100c1c1c2c19040c008800351740000c0403010084803032502d42c6080d014103104220007800c2404420200b556 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 354866115 1250 354864865 354864871
    0xc0f0901050307030e03071a240d03110706050306010e0607050d030506220f0506030705030a080c03120a020c070906050105040909080903030f1312020d030315080102041701050a14 79
    0x4018001003c620604e11030b800c500c2c52203000c0025266900002c2c40c6c0f001d4550b941038501801000c401c000184040f07604c14110920007211003000c10504510010072124521b5200c0440510689803202c101480c0104400c0000e041d81c5d440307440c2e81e82003410016010f001410646441a1400c02200c000070f500858801c0751030006003804a400d445010028000c04081c40c1c118855181c00c0000c49102c0000b9004401c0824441004010715102c00041c1a02d8245501030150581c1c01001c540000032030b044020945410b40005a03814100c80c507030001c2014805643c080c10687c0c0110b01c504000506100f241c1c000c0003061405c002d400d16240001c1e1140c06540305140d4010341d100071504c11301804404449100c1c4000741583c0e554010031205d40c18036045508051140e82c018407011031800c00c407030400c40c0c1064000340201480112558210058032040d000511080c521070340005020380c007400904083c2c1200403141d194105184561030860f8002080c5010890034146144100091191302c40d030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 354867365 1250 354866115 354866117
    0xf0c0706121a0121020c072108030408071103010c050705100b03071502010605300604030c0807020409170a0e09060a0302040b03070e0c0306040608030c070501210f0e060c0f0901 78
    0x503804c6400c3e01c80500700382c1414211401c00c0c000505007090010208000c01511800103803401d141c0f030009147d05903450920b6000709403410800108001c990000003625030302c0d1180132206401402200424203417140c8964420102d04082804010040301344048484000704c42c900304031a0280c80c0010744d0720b603400e03c2503900605480400002d458800e40104006d0315010b0191801c03c0b007091503000080c1040100090710840c5810054500b203c0031403c1c83c0141e406944240d040800c82d2140240e0f54401e41f4102c0c2e202e43d80b4400b44000604050078120364041585095131150102c4138007400c5c01c19102075861092200900b0012135070744002d11007065a40640e400142c5000c43d50200e440c105140d088003680d0b091038020800f00401ca070004501c82c2c0e0040c1c40c1808002c1e03403900055503a0040340c42056498108a50500983d441450314a4070620060b100740c060b00403032400d001c12942805030451507030b41c440c0e11007030280c00100141da4120314644050343c548418002c4100d480d020318043d82d4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 354868615 1250 354867365 354867377
    0x1e01020c060d1415120a170904090b090604021e0a09050c041e080c0904081207050f072003030406020604030f03200d0b0924060f0c0706121a01 63
    0x41c01600369000702c002d011083d00c2c290303c3c3d04100c102c01c920384e41010744c61441001c1180c9912031040000c900100400c2d444039215203407480400080f42142c2001010503040b82e03440d0000780218545104980c004d420340000740c4041d0800380144080001d5160b6940e480740070034001030b0410384805d400d18040384c0b0038150005079901c0f80004c02920b4032803641300d51880c480c038000c01ea240e03104005c0c1120071100001c0032290224400c07014408240c20442d005410b0380b806001d41c2c02901da40300b076416440700c814a4907a2500d02c14040340350326900825026201d4580c00140c0300202d04858800401001046008509152600100940d00c540003440141084040303c0903404a50081d00881d08140303881d032800c1f404400e5040032900540040044101030340c14110f0500e044d06000c4a100c2c01009501103000450744450315509903001c4107501142c102500f0403103400181c412030302a0501ca0001c00141048610f0301e40000c120f400c035284412120707403034418402d080e2222884000501c0c0b00030300f060 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 354869865 1250 354868615 354868627
    0x50a05040b0d0f0b1806011503090f1b050906030102030130120503091005040312090c051201020306150c0d0e060c010c0503010612150b03041b12021e01020c06 70
    0x205202c0012200014910541c8025140411005080d05032007090041140400500c0201c80c40c0d071354070400e10482049041400700100380034401d40020361054010101d8001104041e5a082c160303000c200c0212510b5284400188040d19002d1440c90300000110001e50855040c00c0713100e17400c88000380001025910703800d03014a560100f01c1c803000140741c002c07170180d088d4410003002422661040700d2038030b454001d0700f8074074440100902c60700e402290076565130500354180b14003000c0200b4408005803290303101a4000100303907079a00c65407011a41c0c940c00150b01c81c145041400050151030940c00104141440154040f1100251900d2800b0341c3c1d150006144481e00007180b200d2007004040060307942060703800940250040011412a00180c0d00c02c0ca041840104200489050071000d4880b41c000d41010803001c015000a55080380c02610041405006209070411040c01c6034861805004d010040d1415460080c162049412030b101e85003072410600d8000079250f05c80d000305948244000308030 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 354871115 1250 354869865 354869869
    0x40f15060e03070b0a081006023009060c072c0a050408070f0309060206160804111f020d0207060e030d031d030d0b0907030c0906080c25031404050a05040b 68
    0xf0b0100a2504541195030f4030481d007001030072100c0454030808000d82401d070010341140b000500f0205035035405002d0204c0403000c010403103218244204c88034401024171403983c050b03440000400b42031000500501040b4605145440200d02c1c4041d0103003961005c4070380804a094106150391f01074050140000c807659503140402460041d40d0026110340c0403140e5600805420035138440075a05a90210b130710030303a0b800928007041c1031002410340010780c0e1400840c000038448080349010440040603d174130b6002030120401c0500c070140c960300050b40400e440e4254141c060003036030082c1c540b030312300903990320740c90b0004c01c0d501c16801400e001055a41d9003c411003003440144841007502342010f8940c0c8565007800b600103840d19495032032103000b8480200d05c00328004d101d0200b404485407550652a4585001600c1882001b00100c0c070f40001044448282d5155101b00c2a40c1c60860b05442c2c1042c1c00c5040c006c05c0710060050200942d5810001842030381e0341c071005002212401c032000b140100300c50300 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 354872365 1250 354871115 354871123
    0x5030103061e02040605030402210c0111011d030a08220308060f1201020901080a090b0103121724180a0207031103030702062409040308070c20040f15060e03 69
    0xd10300442e80f0206000c900c0d15805402180103d0003252503600203c00c400c0d903288602c0680d40c0040c1664449100c1107065401000090030305003000000081c0d080603890080035105510000313083d07035040040c08454042d0030011442d00a043c92007400d0388224455070a00c008103581c10301505011800f000242c09584500f07940442440c0a403a1000c04c4003c03207944d82c040c0d0040d0f082d89000c256400000b401d14900c902c10b020195800c00c0702042180d01c0c60319000480c00c15070a214007082041e0221804150380c44034000d0040043c5440702d0160441701e8164100315010300700c604e10030141c0d00207a2040e21041030406030864500280103030760342510f10b401d4039110b04040d8980b4440c000030080140039a00491841d00c601142c0c0340a008040004502d041101d10b0400c0281c0c2c016030f06400308000c00c7c86014200e90028503410940080e81d0540c0740c0c40f1b40785082c00c0f183c14400745e0b455200310f02400c05014100b1680d944000510001044490114113844203002d00c208202c000440c2001741d40c0c0400c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 354873615 1250 354872365 354872411
    0xf090a2f0a090605010e090f01120201110303090d1d09010603021305040f02040603050f090601060302090f0d05010e0d0c15092915120309040b0103060f06020c100f0503010306 77
    0x20014a0707825500e070001e90280070300d07104e49030103d100b00c2c000901c2d60a01211003845003210a111455503800c2018081d410940c101050381080b00410120304012001c2000314010380044000345042f0020750402440f0021181c0c1d482d03964540c50382034088503107501c21802d05403686030a015840c3c0300c100300c0e0300d86915425800141c0c13050410300034604081440c0d0042c4141e07122560305210039503800c0d442203080c80c0140d5460a181d4840801000b07014403a901804103c000145900c10400340d100000c0c0f114800c0040c2a90340d6552515080c0d11844100000c10090b6111b003415503294040f5290246c0400e0545541c18215480300b08000400c1110701d4800c984070110303480090788030181003411210f00000c030b41d21240b00f000314003018502c0c9040d0b51009030840000e07004524084005007440013500c80801e00505050311034801003403210905203842d01800c8964000d041c071413001c401700120502401080300510603d55508882d0552040440b41521b40003d4049200207013640414001c000369 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 354874865 1250 354873615 354873619
    0x5011e0305090c06070f0b06191715010902030907140d020d050c06070309060e0402040f140d140a060b04060f0314070806070e03010c0f12090206040b0d02030f090a2f 73
    0x1c5881c200401d0706d20300401c3d640035000703050290341c0e01c2051200d165000000d914031604402020400c280540400d8050390182ca41500c00c0158000048220003d00b03800071203041d5008810002000d208000c56002040d003450138264000303d03140030400b1a05107150190081340488903160611108110500e40d444010f0310641e5101144e040c002c0c1401c1250151100040e821050580c00e0300c4e0078004d40b01504c0d04118054204e625101609190740004880241c00a0031040d4020114902000043d2100c42ea40090628580a40383c0070040760410a101071285240c5241400703921400c07803415041d03980c42418401d0300400d002c006450a0740c1540281260311a1808000700c10354006607001c1c6844050b0000e11900140707613800d48817540c28484110001e0f100003514080b043d8144c1140200b140041c080502d06600c40040c0c0190394801100da00510380c000051040e140c0c01d07480c03040c1c1d01c00d02c1c8802801181c40300790707078022442501c0d25092500e0040e05038210000d1121030381c114255000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 354876115 1250 354874865 354874867
    0x2070b0906161b03021801060203040905130f0503031605120103062307091d091f0b060d02130806040b0f151207030c0618120507050a0609030c05011e0305090c06 71
    0xc3c0c00c44080c5042804100d0207465001c681e2541e1450007502d4030706070f640e190095030402d428541d00100814005000d0034200445110807030104804000040c0c01a000b4070207113075280740c039104115414000c00c50380410494104209229401d4071103a007410740c0e0b4814004107003000d40b11060380d001440d8111400c1c00e14140e80500c6841508105224100d56981b0003100709011342042084a84004980d40d604035003003103c42d0b03480403040a040040403030a0072030000e00d420b00800403510b290040e003001e0380215800942e00c1109008085510010b00d1608001c003c1c07490b0603900c554042002a10f40d010352041c01c0702107150007020720391304009044051b040040c40380034003e80e5580c0e03c880d031206480c40c0e01e00e494003007803062007203940d0211482d0300c0d078041500300d2400403155444041ca440698980c0035591000c9100d5a641d44080020142581c951900c1400c40c100310f040030359140d201605005401901042401d8005040030700b003402803e0018a6a035070190903401c0000e0303e900c240c0c0c0204 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 354877365 1250 354876115 354876143
    0x30a08072402250302032d0a080105030f0c010c0b060411030c0d0f02180111010e01020c07060e100f0c11040608250506041811030103030306051002070b090616 70
    0x401c80e07000c1d14408201000c8541e000c0030320380300484080715200c4040c0c01600104040980d2445401c0b03c0a808170380f44000200d003141489031140150070481071f880028004500400452800b04a8055003a105801802c2c043c2c0d040c0b000600b501c2400e0000400c20720b05e8000103046a0b8883c3d010309180e00038a94007039581c0c50181d591100c44da004d004110040e600c0c284204c92401010f10965102c01c06440081c5400441e0300c0054a03400b60700618480f4a640340c84d2000d401600a0000d00240e13003122000304141070510001a10070b50400c0411800b404469450b6240d103a800700440300e6028590030418142046801c01191054510b0700c1160003a06280c1d0000706100c00190700040c1110003400803603032003c4144107220215203480740552103074050205108500c1c01d20104010a03440240000b8841c0140b822071246030000d0780160082175440b03c0402c1b0038204031821782c059000038409031420743e080485c1450940552080b40c0c1c0901000300f02c2c0c0041e412144081d0011a030440d542048a203 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 354878615 1250 354877365 354877433
    0x7051b01020904060308030901140f0604020903010207020a080604031211030105060a020a02041518090203060a110d2f090a03080901090302060d0b180106080c07020d02100f030614030a0807 83
    0xd4412349144407d50318296200380460305a0000c1802421460825001c94540c4800c106c0039400c880c80c800c0d0306560800400d40160341d001c0c2c0c0d80c0d0080030b244001e04007610309030401411105011101c2906182046050b070740b0040c503a806c40303041d10070448000780c8405840d60b040745002e0501400035045450320340c2512200d02c1c0e10070f1540440d00ca02c0084203a100c019030030142540c2d56036000941551201c0041610b000141e004140c09881d8107a12909048103c80180155440103000000b11600c0074401a02852070f0b5450750340d0400c48401041c1b521140c1e01c08501001103a10025000d00f402090700c40d000da00ca01c2c5039000075a0000c0a498842e49501c200500030f0403c3e5181610440c01e40b200d241049914046150480d1402c0c2c4880616985080c0051119408001c0490740400c09501d84001655840481c804240c00c994442c0182080342c0700240448034103400209103448034108022465400145003555141c0c445405a240c4107580360160310480e01c1c220041c442550803216168030 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 354879865 1250 354878615 354878617
    0x402010c1a100e0601020106030b012607030807150504021008040501110d05010807060c02010203120a0213032301050108030f07111507050c09060604090b0111030a090501030b0907051b01020904060308 88
    0x9030f01160031940c002e40341c05005a00700c9085120040039031000c030004200030307045100d0103044c02455a1f19016608040e40540741004142d0304103d50240d4041250014001003c1626070342d440d10340030400950815800080e40c0448601214041080f03400026080020030740104412810364840070341c940300518003c030090002401840c03806d1203101c0d000101d481c40740040302040394041e00903500d040200c10711002c030240014039600125070200320b90b41840d00f4900305400114000e04500341c100d0040c2e16000f855002858510b00160306040c0140010440801241c0e452841485c030030b0383c0d816040ca0145e26120400f01031a42c84051a244a54407000d180003c1007000c1c440d000703403021107000c102040024581513030070981040060005221200e1140d111107452801414101000045c0e89042441c60384107040e20b02c0040c0130210108001e5805009804e03a000b01141c0e40462480c00c405c2c020003501964081158442d00c0043d01500842c00390f04a414a480c090018070149442c0d040c40750741 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 354881115 1250 354879865 354879869
    0xf0a330f0e0706110f010207111003060b0d060302180c0a0c060e010e0c01110d0801151205280204030b070503221b0801051005120717010e1c080402010c1a10 69
    0x1135000d580b1000807164018400c892041d80e003c0c02d0401c05201c158103119a00401c1041c050a1603603c52001c2840c40c03018019107038902e64070b68081400e0f03040d44188185107452840396036400240100b400820b011990070b4626194852428000d40d02071810300f840502070761405441c0b59483c04803240d11071070001c5104000c01000381c1f901c203600074001215a03a140a10941400042c034130f000113100c01d6040004c08100c0d000c4501e840c1061a20054992045400c182d40401c0404840030070707140001202150089148810f072011400c10745191105004420001d1080c130403c072002002846410034603200540184540f4004109151107152154500c141e1550940c50149010b0001900610502585204081101061608034982024048041503010500100d40140742000c1040c10750b10f50b0010b6060390180000c6080b441c04009241007540d095440d4500e00b4035010035030525a0088030b4150401d9082c680500c03000d80b1410f15034034220031002c03407031408070540c414840c0d0850b0340680142 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 354882365 1250 354881115 354881147
    0x40504050105060312311e0f060f020a0b0901060e0f1005040c0527031002430305090d03080610020606100e060405030f0a330f0e0706 59
    0x22400c40c0111086800385000a910b540030300e06501c0080c040001c0c00c4040031040f040791000079074640c2c1d605070542c4220005000000207802c0104402c071b6840410000806190070940c01c0c02b004e145000f0b403518a0148060404502100800c4c1d010400358010002070480902c00580c0e030030a110101e408500540300d03010018440000480c0501d058482c0d8480c14000303858003482d200075508418890f1074581440c610686191800f005542c4040c00520300001c214500143d8580308038038081c1500000d420201c0c0c40b00845955450f0510061451501410101c0c8619102c2c0c4807d113022142c52046c2600340782c005c00f81d40500b404150f002006903001d0341c01161b5105044451010480e81c986c0c04940e1190b121032010a03074804240240c0080f02d640c1405424203140c1526280071038500b00c041c101b01030590340491a5241400710f500b501141c0205403541030f420002071172072004a0f012130f407020b046185a40b001103001030303680d590043c84081102420303100440c1d501c0401031302408040c12051 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 354883615 1250 354882365 354882373
    0x50d020d080606040f03020108100e0705040305070f060807110316062c0606060706140705070c060c02060d0c0201180c230306040b060a030f050303070e0102030c07051009050405040501050603 84
    0x34070585080c8080c0c030240c5e0f44100e01c5c2d00000b0300e9074004440008015010401c81d150720100840c1c0791321644240d901c540f002e511034585e100d00c0d515001c2e2a1081b00d40c8241680e016951040c005140d010f90195000491450141552034042c00098150311034081d468821050840c445410480d05401042070314102080384005070804100b003004020101903100742541003800029010310f4000003421041303008c0d40d40060a904031200180c544107050340d840010034800700343c003c1040045600c9a000d00214980300340b0110450340440c4c868050900d15100282d146c041800525100354010032006065548406044006042ca40c0309000f841c090b810400352040c03e1a1013070300e00700c03500c0e00c00030340058003c01496031552515586880302600899120000080004c0498402104223070070f64011405140d681c10401000b50581022410b4981590801d002c4007d0350305010a8000490703005950440010510070740c00c41d444e100503040ada902a203850184402c1c448c0542c00548a04816400c03a = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 354884865 1250 354883615 354883621
    0x601060e15162108041b0305030c010504060516050a0f0e031e0d02010603021c26180a26010b030106060201150b090d120c06020c060609010f1503110403050d020d08 72
    0x482680500da00c92020545104c04200024800200503a00002c41005a030915480390b440c0e0f81942e100c000310310400ea4603441403006019540c8192a000700403011064102c0704803440c00f03002c50180e02d880805009030b28031060368132400740c5010550300c5401070607509424001003c1010121010440c1c2a81c0d100352400361280d20b00510131841502e40040c2400c4450b42d00c00c1030600e00d284d182d00d0490b4401041041000240c0e000300ca010442d0140683c0962209012490b64071503620b001c410601c98002600f0400c0246014036105049410442a0000c3c44135911503090151100c3c1c000507401d50718140e4005426036041d8410b000c16054101c001201710b560305c8950750030f4052940c403558410f007142a03643c001594507842c2c0302a86054140958081d00c95181c480480e000601d000100e60841d01c1081500c2c0341c2004a14090404030705880141820041841c206800141e60003092540d2015000004220070054400859024044071008c5103c80c0c0c00a46444080c05480b010030401c4002c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 354886115 1250 354884865 354884903
    0x72402070306090f121b060f110f21010302090a05130516080f0a1e0c050603010308030105010807080705032e081e0102090f010e010e18270601060e1516 67
    0x404007203540028407904106c04241c80d42c400401303030705003540c4183da903e1511040c880f40302805805404c0c00c0205142c0c40306041c050049415034030445000c002301010340103000503916002200d80001c045080060b2a030345036540b0402d00e83e14403001800390f01c0b44c4510341c143d1141e1003418000f5140b2581c142d510b808145c1444695408858100505040c0281c00103140c4132542e83c0510074141c020351a0450b0b05030341d440805c1042c0c1c8207030403e561001c0000018010355030018030060f003140e00c620700706103c1e142a84000b851400b000c1c0c03100140a00c40020300848104400000c490001100070010307076240d441c85040d5540c006003020803250920381e4980148048184203a03420500090440d000c0d580841c0e0046900c04c610b0000c0c01d041c8160b1500c000350b2900c40c10310041a25818141403411400d0145049503100751501c41c1c2c24445080f030013010340181e404240d803411941d0f0341c1440f11400c0c40c0540041c140540031404c6501194002c64044040d07070b541410102d41c83d00522491a03502c4000b41 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 354887365 1250 354886115 354886127
    0xe0c03060438091b0c070f0b04170d081f0902160b06011803032a030f270308030a0905030a08160807021b0f0a03050618072402070306090f12 62
    0x15490410712291040440c80413200740040c0180713803c203004d440303040f03441c2c926030342c4000b1f0950080000c808001c541400b1240c0784600c80d55102280ca0000c1548081c0c08030010201070009100405171201e07510b850501241c10003c00002d0482808295143e008203003c00400151400c01981c3c88a03c1c407000c2269540100003106010b0030960203184100c7c15601d013a10b04820152200d1480701030f0f4120083d106000c2910841041d01c42c0e80c40700c094100c01c10005040b810201494480c80d51a100030700206408a918001125031004402d40c403a0365100da0a0014007044c840074159020000d0185c00550b4000714251145d034440010034494005404101c0e54200e044030448050703401072840e41c505c02c1c0103200c01500018024007110410051001280025203940e00c103e82aa000c601400300c40002d00f580c0d05591166900101000741c6840e007000541c015140f40340012041201d2440d00d043c0c82802210095a0000b2081c881c494a500d06406a040c054070261144100300280a03000f80c4115 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 354888615 1250 354887365 354887371
    0x1a331804060b0f1b0a02090c0c0c030105060105070b0c0708130e0714030406050414030f0901030b1c030c03110303070504060e03210a0203070c27060e0c0306043809 72
    0x802114103000f21a09400303000702c4140d081001505c0761441e9100103a64075004ca070320500c0b0014000703480309100d95490f0b20b040d80266607680309074180401c00c65540d0b800702c182ca14690304026a0302c2e40ea2903041da211518402d8440c041c0c04100001900303012005100100c40449009030100c1180e80d07103100c004c03280402c40c9042c5003158001000481c01088040d042950498019031080340013900350043d4616580c02002900020388012942d8a415078162090302204001035500d010305450b0030454804c44814018001d041c4201c00300741c0810715118400e000c0c42100c000c411030ba500d04001e00041e0580c0c010b4450074000907504003101c240e0341004100d00643e03148911405d00903022055040b0501d4024020f050210b10041c00079001040c00041c103130000303010307036038058031b00d403281d4007183c45446401030705a05c030309040c0801046100304a40b0129440446500020780780d45424001901030301071481ca07248038101c900c4c090450382842890700c0101c950f444184a402c09080d40601004000407 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 354889865 1250 354888615 354888637
    0xc0304270c0504180f09050609160f0b13030614100506120a021e03040f020a0b03071407240b09090c090c0703110712061a331804060b 59
    0x500003000004c4216540403080c80c4020401304030700100b43c0c840b0040307410203102600c950340000103005071045d05011501d154140801c0001c4803909124200c0481e03849449088940a800182c54480300c1038400306d5006180c0c018802e01229210003600001104142da0412041c0c00e520b50020345850050210780000310031941c0f080590303807404c9410000b50041c1078400c000080003040358080d41200c00013944158862082c4c2e8040060500620030903800c1c0c0d0f00300c41a84401041440b06090700140f18009034088009010303501c10540c90070708446494084003000c0c112034280c00341c1d0100361540140199040690b101c08881d56140d00c49030340e07042c5040348150840c2026010400e009003002c002c1c45014002d041101000da25049500e1600c2c0f40c990005d650042c03c0d030010001c100c1203014203c004002004410600840500008c0c142c88181d054026240c00302d50824111120281e0422000c0c41c01100042d03c6080c3d480500e07044000c070f00030280c4600e00d030110108400d18031000799640d04100d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 354891115 1250 354889865 354889867
    0xe13030c02190902121806040317071b051c02030415030203100b1215030a020f120a051e070812340303020702130606020d050f0c0304270c05 62
    0x459000d129070310600b00c90341c0004400555011811094034001002ca0340e20000304116185049070503406001c02051000405420031820f100200e54040180492000d480304100300b503131030b181c0c000c1d00d1f03160050520300703203e001544080e0284000841c5202c0342c00c07031081c12261120b841140480c0c0384c4c4030750f0085040224800300300d48000c5120798041c6034000d2007020408000c41e115038507802550080d0138480401030210301042a501d107c80da00810601d4190003c04000550f9400620120882010580502030082031032040c00d078100250302100b6040001d958084203420005060f4400440c41e44c01030307100f12400000c0349030340019202c0c0007500c148919428100302c0310041401100b02c0c01543c803001e004541c3d100d0318044c91720f2807006441c840d440043ea210003d01c1444000c2a04880da4414103140010401c00380307030049110711798081c051500316a20000501e01c0c2d480c0d4010040c000e00c0c10301c4082000310700b40c00705540000040ca200699110000c20604a00c42070722445684400000c01c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 354892365 1250 354891115 354891137
    0x6110a0f02070303050d0b03010f0207080301050310091e0f0c031b060206091908120f04020906040902010f200a08030406050c19030c032306090702070509040b04111503010e1303 78
    0xc86584007c410103802800072807540000448002aa04800002d540f413000001c010401854200035400c04409190001d02c00c403006915020660030740d24150307445440002c1d03540310411005404581000380d03c03440001c0b0f03c2c1e8407030802040010340801004046100c0700d101099090001403138a00c00c0b50010020700180c0300405407a0711030148010700b120440002d21004440b20104100d05c0d00c60364006900c0001440d2500401a01c01b00207840180034602c3c0005038800740c0d90040c4030100e05a004e00340700e020004c00d80c1d1000e1002110100150342409900001c1040024400045001e1800742c101404151030300c800f8030700a8411010040030340344010154100040c0a5048040d10310a01c0c1030008202558120340c00e881058074424146203d07009042080c0351802010041d0000b106200400d107050130200030480b000005000540f0300c3c50a0070002e800c0003407807490b032002194042c024101610101c403062510790000c0c021066480704810005582254210705000715a400d40e803032100c00c00c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 354893615 1250 354892365 354892387
    0x6120a29040b0102120d0b010912020d24020d0b030c030102040f12021503010e0a0606030b03190602040305120a020123040303020319110d050c130510090306110a0f0207030305 77
    0x2c9a01e4540741507009003e03000d1810400700c0050701404940c1c03a40131075030b810300314001030222580f50800900720014008070703009a1100079126203941d512083c246a4480581104030400c1a4501003d800d103000040300c140310036581c0c00c0f00004c90000d0701241c000c1541c142c2014242c0c0203600500c03500d502c18400c2080b00c442d4001e188501c550020f0643d094403000540205400d900982006242021680a20a8200c043d01ca00401044030346410005140e0303d07000240c5071514028134030100c25a215030301082c000b440e4111001103504c54107e42559101300544c443c160050007045000d0b5180c03140c04e408000e11655002000c00e2101d060006c6a5116501500250030141c0a04400c4112a04004050724203100f1003991000c400c022a840e0009483c280c2c040e5000105052080441801130040c03d00f00d480c444030035250201c620b503861410f0708000320303140300e01d0b0392018124a041c0200e101050201000421303168400d583e5542c080c21a04000f81e80d24100c921004000800401400c3e5002c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 354894865 1250 354893615 354893621
    0xc0403170319020a1d18060103021803070602010504031b08030c0c030c072414030a090f0803040f0c090c0e0613030c030c06020f0601060509040f0b06120a2904 70
    0x2000b000c58280c240000500e0010b000c80e0007050842000c0703200e000900c0c1094810703403943c0f0741408044410080412408001c4010520083c114a040c9a00403444045540c2e40185241c03401202a003155540c0d965040001c4c0600015581a00441e002031600a80001c005a247e070015400451452641d210401d0164503a444107005115501003070180d581148400d115200080400445044400c2c43c2400d22100c0600e00c03039102424411000082580392960340c003600e9001d44031030000a01e0101a04010900364105e4034020703c8401c00000300010082d15510030381e456030013580c129040036160354004c801c43d1030b000340d07100220703619401c0b1b6069490035500900030607080207074910441c4c2d660b907690440800190000c550489108900748446603040000310b00c02076414004100c81d500d003a102034018811100280e000302d4440d048007282c118142c100602c040c0380901542d0395020fa01180d042c0840e01611004601d45c00c2c05030a5204940003825194103408412960341a41d40e488200001 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 354896115 1250 354894865 354894871
    0x9010513030204020a1205150a030f03170c04060f0e0603180102160807120216030602071a090a0201020c0906011b02151308070503030f0f030711010c0203070b0c04031703 75
    0x40c12845560110040c3c075180007a00c07030030005890341e0400c010b1060014003910300c0144203012410701d08880c100709545a14103101200c2d00004020300c2103410b4201100c461044000c0c83e8912032000c0180888410050010300071030310b407035860914103103a0711421514248501010b43d40325809001107030002d50a0b04c0c030755031014001c070001468104941e12086d21044404030580312400301140081c10710021000d00c01101d0000d1021300341c00c0b000399004040f0000613002c05050150302280410820a24104140b1031b203410b100281d041e0718150a4040c0c0e030b105004c07022401401072821300002410401001030040405846c2d0134409004584d914054507603481e402c0e6481056500c00000202101008002541071580c03400030721801c0c02d00b9a807a0008944c0320030300a50040020900c4028580107480b84903142103c00369880e118441e04407014140d50081c44055480c12024201c8690000001c1000a10400c41f0f00c19035039401c040308455000d1840302030700140c83c0800390219150400001c41e4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 354897365 1250 354896115 354896137
    0x305040b03270304090f0204081c03061d010617090607120605060d05061215040807030c2102010c0509030c043c06050d0f060e030409050f16050f090105 67
    0x10039041100031580c00e450718002e031046500002414800400d550042a284020105055141501c3c0041042d59002c01810822810030341f040c160030180e10a4025000038102084034a030b41d40140314412061103006e00c221000325003e44900c240132144940b216114900c6503000e45410f940d580001d81c0e820ba5950a442c0c43c1035514400401c155a45a000e45000800d0607400212440c18400b4050010014165807031a40d0043e400c80075841c8900741d0056016500c40039030360322a81240707070503549080d030080000d041600c040b0749603800d03c00e592200074548145034003c0c402d440c0750000503503880c400c01d0380c101c1c0c258001501e00c1c4243c3c02c2c560041c5001c2c00441c100703031881d119503d09003a002826985681001140396418081c104404d00900d005031504544078000600d9641e12240c8a10902d440280425120304045002d0b40c81441510000c010b41c540c180424500a0070703245003008105c41c2003e41c5580c42a0741180385100344240c030442154582c2d01454452150019180760700000f041d10 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 354898615 1250 354897365 354897391
    0x9050718020c06010b04080d051303060b060715050a0615050d051b070f030807050f12070207150804020909060621070302040906050604051503070b0903010f2405030a0305040b03 78
    0xc0d260b02c0c2c200f1880703000380705080d1580e855a082c0940181010010003010b010004240b04011010103455a40c0d0b04896200600180c140f202201184c0c99014007a0080e001c0620000c1508140700c00750085031150704900801c01400d9180d49400521100b1750882000080f03061003900031440e1103a1140b6040b601340a60740403010500303842d400050707000040c12034204c4082e01d01c0d281010340008000b500300c40c0d03508010b814810201c010100e103001c0c4101800101450501046c0c021b8020700100014003500071615141d02c5030082c01811001050310102c3c00303100d41c00001500e00304e02081c201e01a400003445001d040e8841a512010b4100c00710f9038002c240110800000181e0300d5100c1c03c00701602c0b4401c00b065600d400d000b04401c41d80c0040444814071a44110100c05e0b5401241480507218614200c4da01c4001400204e03004111451049925615200c407000314020100704910001110f152107a0150341c840f03044c5902e17030044810060100d0750038403090048110240186902c2083c180c0c43c9 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 354899865 1250 354898615 354898627
    0x120f080c06090d030f050712021303020907032c0307030c2a08011a030d0513091109130c02031b0a050d0905040c0c050c061b010203190507030905071802 67
    0x25081c01826103076622030341d210022080103950140101c000b0074140000401183c54000c0c8050404104081400502c0364009092032490a600242e04080c5401400c041c209180c071103405001000170040c505d50341d00704804540c0d4408100322481e0b460340740080203541082000e80e4207442d500c0c400309040317600d190140c1800701c546541014139220074440c0b5000f19841803800c03400700d00b128103004800b81c0c0402158070182c02a1800106040c29500d640750655544000c050051000d0001c0e0700300490b4142023030307000340c0750009000c00f801421800311800a22040307402c0c104401c4501503d00540580c20030300255000d0361610f94608107808007002500e0000c4055038600d41041d6243c100440450301070802880107007000e1152a282e070300c0d2418500d20703c0e810760300c3d401e03500d0071524061880790301e00041094096400304080030700b449250000b55100e082c440d142e428511300605034140980d24001c0000c03003d503c2405040c10040e001006003502c5400c100007a00030020311224954515000c2102d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 354901115 1250 354899865 354899887
    0x6030c3f01110304030e01030b01080601050d0b060c010b093102010302040905040b01060212040501081f0f03030c1106030408030a33030c06020303010605030a021305060f0702010e0a120f08 83
    0x2c402e100c11820008964a18007403501401c0501d00c10880d90405245c01c0f40e680c4603036040241190008400d0800175105c46003c3c030300c80f025001a5011035000303c00841c0c801d140c010150410925500d04480754941a07031a40c40d2030000e5001034003a11101c080c644040403110b882404c94852040c0185000b5141544988005041d03a400742e5003241ea010500c1c004128131941801290250821022707080c0c40c0c0b0f4078200000303100da040501095004020b03c407860419410340031084000f0007402c0500c80600303603a810301804001e603619040c1c0e10590310003008026403401804503480b807640160404d041da01c030ba0651744010042c40c829000c450348254541007000d40b54004c20305000044008100303030f8178210700d81a1705c1464942e02450540d8401d00042c414660040266a07204000440c0143c80c0d01102c1c401d501a801207a005640240c40000c01035010194a0004c1c40914003c1e29203940246485051201c0c031751aa05c100b0848a900d1420103001a42129501c0d40c2c86001d065a0340c144806101 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 354902365 1250 354901115 354901121
    0x12020d0c06081008060610051308250b03040f060b01230c010b0306040b041b0306330602070b0f090306010e01060f030603020907050c03120106030506030c3f01 70
    0x10100c0802e10607801c000311409210071580141440780d000d008076040050201e2107094035014140207004002c0340d01103102010074480070007000b004c0d0483e980d545103108540340a40c242ca1050381d0380c001e03d44010401c1d41e205421a4060355001c02ea82100805c6515604000c3c0111a0183d04011210070303080c04c0803501204010011070a034403081da64002004007a401c41d00b0300e40f0503e0207a044039003040b003c00c01401e417503036005410100400f222100c0d80c0150320f003014190001040c13246484850304109034403c1c05008005415a00c1210810a00b600409941080d11460005030311134042030040f065010050401e039204c1d002c1040c100000400042e0404109811800240210303a00401c8880d40c0f1040c0d6162425060404020342c03411a0041041820000c00745014040d0011303840042003000c200300c0f6950003001c80c0b0b0f00081d58640c17200502519050301c0d80341c400d02c901d03a0034000500c0c1000380c603413028802d4580b187c28010054110203058068101c0010f0480840d900501a003d080c0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 354903615 1250 354902365 354902369
    0x9060f1e0203041e0b090d080418020415080f0c18060f0304110105040e0105010806120d0804170f090405070302190e04110924091903060c080606030112020d0c 70
    0xe00038549541c1052208030700b000c201c00c503840194100d13480800c032000d404411101c0d0880240c0d041000140142012007441c030469110003000c0a107207050100d140c0581d40a03000780c1e424462159071001044200310764242c010b44040c03441091a10100d1881840400103122551702900242034101d44500043c110b900702d01043c03c481c00001040100b0480c20203d001c08016003424014242401c004c003440481c10140030301d41c1070000e450b01080c6203a4405a882581b03610b00021038a2100156400602010058404650741140109280705201e109400c1d00c000340300d410200783c102880f640c1003101a0901030a9a02456402c2204814045d0707080d203410000400d6448000800100c14203103c11030301e0f40071000c01c0c055401d0001200703a589240441c4041d1148400c0102c40401c0c81022402d070344180d40c20305a0090789424202f0140082414070001c59021b50ac08205003010a07100307940c2c6910031219a68081010801401a074060002c2801180d001914074401140d840d44e0340d40b003200c565 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 354904865 1250 354903615 354903617
    0x20c040510051903060c030606021c140c03070b09010b10030b06120103080c07060e0906040c1103131d070206041401090501050112020f0f09060411070c030807031704020109060f1e 79
    0x400f420320601c00c40d070040201c562064903013084800d1074898006d480e480400c911007240c00c5000c040549652081140c00b980301c101890459641c800c24038000d0b601c1d480700c4000c58031500f031035000400001d0180308002c10341902070000c10f8001c59403403044006020100510703a00070000d0091000d05c2e401c0905690207544642c40480da0b42c95403070285e80c40c01d40030398800000c0103141501003a144c0c41e0f040310507412260645000c5404005d000082d640600026580c500070300c004261031481410220380b035411102a001b410305410296070b9404401c240460322000541c1c00390003c078000070388000180f048103030503200000e0301c0f50079541c5071400c0d01c1c001c3e400b03114184000d5442c2da0a520707100f00300110500e0f04031620014500110b010814003100100b005104540d90205800700e444d10808841c0c920340e02290003a00f4517101c0c078200929400ac06000c0d0b0000783c0c81c041403800350b8080c26916000e590161035511515151032401c5940080c0d80c009402004046c10850703007003100c081032403a1403040f2 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 354906115 1250 354904865 354904909
    0x6100909060e060a0c270303050309190308060103140417031b0705070501080105030f0d0806061c02030708010e0408030c13090903082e05060912070b030906070f020c04051005 77
    0x200f000031b01c03510b00c814281d11100b080410040c00304901c54081e0003100c5c2d25041051f121359560b24001e00700f0b030f40c3d48070b083c1c0b0b6001c081800d40c0805500124442c820701d02624204046601c3c0315071300c500c01e0b81c100c038002d20844241010b0b24422400300d02641c2d110384c00b11907401d000a40580954442d402254048605901c0030a06100e80e40e0089000c82c050801503000f00141c0d4400003015a442c41c41c000048180143c0c0c03400b0a4150301c50204481c074824104411814031986005c0210082d0b1048a0240c0096003020000c2070f0715101d52411401190000081402c40d100c280a07161950300170b42c00c1d545102c2101c9000200c2920b0344c09030540c00c0b0b01980340e09181349010020207007403050165940d080b50ad202c0c009a561000509040402c0d2103091396000c3e1624002804140b4421400c40079626520403664006030240352440114401c2840c40192541e50300c0705403082c2d400c600241e0031500540c00503204e00006043c2544050b50041c0340c082e4242c44203030380300b02042c81005001441d80114507 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 354907365 1250 354906115 354906131
    0x9120f1e0c0907050f2101051f0516060f0b12010e070308160503041203030e0303010303050301060c0c0b0a0302072901051002030d020301060f02010c0206100909060e060a 75
    0xa418054080c5500310000301440a011810240d91185000310001e03200d50400340100382c1103482107003038560045c4205c0c905a5196890b0011680c0c1d10300c1100c0a84c6075622034800800d42d42003412110245004820494401d00035406050380c2c41c0c0c004c081d1003d4003840e10601c2c08040f456a0089052200c03e544000031111070700400d220541c000c0c0f04260403583c5c10702e86002120800000c00e44200c0c0d03003001c1d0850302c40c400c944883c6082c04072100040c000c0c0c40082804a03002285080c072a404911907101000303a05201d03141c080d100e010910000e80454018001002042e001e0303041824040e20a102d1003855075100c02d0011581e800c9451000e000039804103848040044d058001200c410b6054040d0a01d00042c20401405890501845000308542ca480b00900c5000300159050381e64004820754a03580c460b48010202121074014800560806800700140c030b0001c2403003801902112103180495044c5198a4080d10000304101e807001d075950840c2c1c05455042c4102c50042c0b4618002003145a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 354908615 1250 354907365 354907393
    0xc050a1a0604060b04060309080d0603061401080d1403331215150d0c080c040c03021309110d020f1908010e1303031803030905070801020414150912 65
    0x400010807482c095860420240051007504050314100c2c0c10f64039020413030141138540700c070080c0242d40c0300308070f0203041400c0481003100b65009501f540c05030500c0040c060f0790b20f007212552004403101762004101840304503900103e00b000103662240f181c8911a030610303200080d4681100c1c1803407003804194049540f10981e403070151802034015031420020706021468004030200c00c5c60240240c4042100300c40c442015803102d1801c21001500040b80700c0c1c0081d6944412921480d031008028411490412030310087c034024400d0303d100c1003124450025440c1402e49540040000d0050705274021028843e130325801060380010075201000060315501e404808501c84400c2400b510440300303014400c4014800701c5641c0320520340c0302c541c61071185014016800d068005101d8030720340c4807103056254401018103170181c21070150a03114204651569645005003402c1340641d02078030b446215141c4c5040c08500d44014040700b01b880e00741051f03107002600000642e41010f400e407510801d807c6030108000307230 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 354909865 1250 354908615 354908663
    0x3250c2a060527150c010f23040f03090f06030914010204080316110d030503071706010e012003040305150109110d020703090b0d02130816030b070c050a 67
    0x100301908000f0f00f801c401c401d02a003008a02040d840703080e00e0318112188159103c481134501e00c6191a082980c4058101c0524080c1010303041090480303003081402d0441050325103050380c181070303011400c0c403c2e916141d58407029144902d8007942004441e0790f02051907429103d246c0020f0040d5200090100401d207040c0794088400c005500181c4d1052100300280107010003182e45184c88100000208001171402000100c00c0c184102d03041007ea00d404c1080680100056020b0000c0c0e84460701914410003c00e00580c4003110100e0000340034106001041d4000c8d11410030b48001c00302211101c0025600851650300194000e40c0e0750362081e4800d02482a03800113103030141401c6a024408610302c101c0c42e0950f403103400a12000c20703500154803000e151254400300054407035003c103207540b445503a88038006500900a012011410044c2c009510348000030b12030260000d140c07814400c18078545a84292480c014904410700c01e01440001c0000c0081c4a0000100d02c15001241a002841c2c507052034 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 354911115 1250 354909865 354909869
    0x50606040507020c091009060b07210e060a02030706181b081b03010b0d06061703030f07030b15040e01060f02010e0a0204050a090602030a020c060c03250c2a 69
    0x941c501000e000e0595404221440304510a5401d0181d40d160319050240d4580150f000c10300e4070389418000b213501c00d010401001c01d240079940c1d20022903192aa01e14000700d0080c0e00c00d0200d5400060b01080341030800203011540d4450066908101c2d858a0381400d03180c46400d00c9110b54050b60034842007000c0b4016200171001240180c038426410000103580d07030410b001101d5012040e82c5c2c403c407880e940035040301c02c9050b00901307020f40c0b0f010075250203005401680503040f5000504003000c6441c00000054a02c14401680780400c0d9440b40c803420380040c180c240c292a082040424008a1340c3c1100300100010650403e0461196142600c02801c4400324180e420859040105203084a840096094040ea8048500260782c0d01c424801e0001032000b55401481207001208001c0118034903405881c0d0b4814000948034039a5034122416840e1108071074840502d080d0001480e041c20300c24100b05424001c6040ca0b4410001ca0748032800039031a80220300441c0d128014070000800700490740000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 354912365 1250 354911115 354911119
    0x901050f100b090a15020d0f02030f09040b030c10020f16290c070801141005090a1107170c1605030714030a0204020c1020090607060f0c0c050606 64
    0x151a0901c180311650340d0301c09104050b040000411071498558980500da0300900c0140d0b014010070700c6a00c400703074540001c0d07619100442c1420203d43c03061030010080300d07014003108100070300c1c0040c0e1104200051007031341443c83e014810402d03120030b503071241c80b16883c03031540c550001c0c206803100c440c0705490002c0f441c00e8040c0d49070740d0080070840402c0481c1140b103040084852020b030009420a0700b0883e000b40a0a01c02c103104030100041c8000f010343c0540c03a4001b0403084030705195114015204050b9030362040540001652000440315041a03202640c00d4074050025031078100c00380c55100205400480407045403800107081000380804011050040342c3c0e00c024034080e00d00e04030010b511841240f06e040d010300040002501550b0f800d011528032140c1c018011903e03407009030600350303403034507040e588a0009181416282106500c1000c2c3d000a031031004901d494044014184003040d009400300f00d600036160b03500d41070704a201c2c0c00b030025885110351b100b004052036130a140e444c2c010003908042c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 354913615 1250 354912365 354912391
    0x510060f051e0409021005070309090203091e15100509060d031e11060f070906050702031915050412030c08090a020f0612040c0612021813060914090105 67
    0x490b445019040c0200380c003072440c542084080d0400f10340541040d0328000e500070862403080f1103941e0050050098680269520100d4540f54041d04007244001d0311210200d500424148035460382815010100d503107e00240e13480c0b510f40050a402d18941642e12003801c140307210301440399040601c5004da0140046070710f011b884151ba200506004540700d01007010100100050441c03034010209080400611000c5480c0e614102d0204a60360740c080c0e80f44400103110000003d0140e1266064524a5800501600e2406100b05c100c0f110000c21403800c031401c00444a00145d00c20307013803040c58801c03405203400c0100080c2101c40101110309418840003440222410310488040001d0a284401d0307054841c0c3d402c002040001600031301440042d50034031b644800800c0200000d0b0700c050f0044a003d0749820400712058191241680a80c03d1211504189220041303243d150012101003644a04000040d0454484605005030313160381c5000e801401c4140144001d0103802d1050581c4030072141092 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 354914865 1250 354913615 354913619
    0x1803090d020f0409050f0d0206090a0308010909030e03190309050307030c15050702030a0c0602070510020a061505151c05041203020706020d020a08100501080712090602040801090510060f 82
    0x65140c04090201a0180032882c041103110744450344120840c0ea0820200c0b500048280402c56940d0348407001180140035a4010aaa40c44001795407103805078107407910341e0560b00b4005004d0042c04404402d03020000c81c2e13058902152420b01034a06960500d104560340c1c0c110310704000d40407000c01e500076070081d07100c108200040f0750300420071025076003010210f4a03521051882154203024511010f9454000e1500450420091001c00b00456016400b0b48603010368540c200800d20b90540042000342c1c0140c81f100001442e654440200503000c100180c1c00c054607a07022030300c803210403d0b100d41c400200084030000c1c070140225a0031807016060041c4200e18180d5612054212401144020f0680102e00c0340108030080d012f5656500d0710710411520b641c90240c000702569030584888500115204000c2500e5220300c0d1058400d0302c9945031040c1d010024400ca8004040c001000c0d24059070038031010440820a015100c1032500400050981400b081102d4045032100d034460512003540641c1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 354916115 1250 354914865 354914869
    0x23c07060c1707020301060b040306050702070b07020108042a031403130b03131b090507020c092707140a06260c0702040f0e10050906040f03090f06020105180309 71
    0x400c08002d5108582c520392425907101e100d658020080025459400c0800100310f1002060141c821a07000b854180a5900d40401c10f903110391207030240301c0700b9030030030098000994000c995840c0c00c54402c0040001380381c6d500130014400041c2d0f089001498015150402c140240922013000303901c6600080d5141243c3c14440025000c80361040d010045000b00020300c800400c070051138001d98205841d1509512408090f80015401e401880d030018075010100e50542d100160b4442c0000c40500454000e80303d0040420380840018422400211110000c041c0350340c0502a203801490300c2500c00100840b6142048103500e01078109601b00300c4950810080111000c41019020039151080e484d60b0f21000c07207040c054411180d019400c40d0519001401c000e181c1e5202c46021401501900c104480044828061311000c0c1d648030000d9103c1d00200d4041066402030921507842800c01c4202c295441360078031060480e40c1c0c80391015035500c070100f01c02e03100e0100c181404140000c000d186005401c0c00 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 354917365 1250 354916115 354916127
    0x6020c0607120203120703060e0a05100314010f09120801170703030806010509030a03080108011107080304231b0109120312091b0902071a061c0201023c0706 69
    0x70010705655840700c1c950300381a000b80220b0701e83c442c65101040013031a00241c0134020f4029403180031850001100010071002c0315200d00b60240001c07000d554010780c9103449507002e032090910234241d155a03542c40e0360000c414520a14103494414869a20f542d204420302508204d41688826080d08031214800e5203030401182079010b0301d03814108883c0c15161000100c03002d00a08550b03540600c10000304000b45508826141c0c100d4030440e0080c403108a03100b4400141340a00640208070001c140b0100d000600b01400d00144400c00d0900c5881c0c030f0302e4050756145803a51035000c0c4520013180c2201007605581c40311044001d0300b000c1c1c00c11603000d54036aa00810303000c0009078441c0f450703559981c081d040011200341d9003010040800249213241e01c89075201c00175030290004a03001c501d0f19460400c50280300710018490500284911200091a94a11403c400500040b0704600503540040940d0000140c04d025181100600b03400c071241011000b002211788400b591019480314000700301070707940030f8 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 354918615 1250 354917365 354917377
    0x8070609051e060a0e0304060903030e03010906020f0d0c1b02100c0813060306140a060c030c0804030b01090c02010e0c06070212030d0209150c10021c060b03070906020c06 75
    0x22800034000e80181002030410a4928038202c501040a2841c000010b000030554007a00940740d04001e90302400d0701d030960f42d01c074610501c00414001442003003c01c0c01118044c4900f8005000414440d0444c3e45040403648449440d0940f1b05000c241e4030120001031140b422440d14504054003140d0012058070404009a2030003807103211658101020f2511621032250010b5000c00503584603251301c000708000580d20300030710001030701d030020018801e501d07500500c0b8031078000303005840303210708028046802500c0140c0640c1070210301c0207103100056002c4001c000075800740b0500c00095040c0034000c02558684100326045a041050801d440305000c02c103000c510000712842c23030f0782c0c07082032002c01c48400904071000a203010121b001800740c00c0d10740003083c0c0c000d02200c00540405c209140502c0d24040ca9844030720725400b0310f00407000f8001690061048103c030300700303c114034440182103e080c0c0b800e5400206000d08048244a01160080b40700400741541d4000342c07010030442c4000c50840c1c0145 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 354919865 1250 354918615 354918623
    0x1d0606010e0405060112050a1d03030c1905040317041404020c0601050120010e0601031223130504020711190e0c090607053a020a260d0e0d03090807 65
    0x3c01c040350b0281e001e81c20200d0444410710b001d001d1840c00c08ca054004104407a400c0e0f4948808600c1035010960210843e0312440101112341d0400118240c036110221401c400c100c188002004040301050308243d4101410030002c040558550905941ca182404940300640c040c50052200405c0e02a01203203c038103462083c41c1805c00c28104a1401221001161a0304100c5d40707000307880001c0d8140480c00d1416680200c0c42c48070b02002d07100045911704c941c0003c4204180c0c500c000050541500342c01480b543c006c080103140b00607240c100017400c9038030844046a80a2603c81c0005181c100240180c69003018111480165450860380c2040100014880384e0022030004009519940700002c0d140c400c0d800c0000c17159440e0084040c44040007854083c0310350000d6180000e5440d001c0740c0800007084a00e940900004e840740d550b10721a00141e655403042d03070030182250380c0d43e0034920f8014040d05000d10318040350380802802c4060411a2901c1c01008050908001e5404101c941044805c11544 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 354921115 1250 354919865 354919871
    0x130915020c0d12062c060108060604030f030c0204020c0c040e070503030409020d060801090507030311010606210e0d0c0c090b0d030c0c120803060315010303120f0209060a031d0606010e04 82
    0x7a41403014010b04140d084019034420b414034144c0c44e03110a85e48800d071303000300100745030554682030019500d81c5400c40d0350940c014402c0005000041c40460603000b4a48030f03041003081c100c238a03070020707042c5d80125102115960250029800c05e203403601408400c000f5103c041c21032541040d01180c1c0382d00c150302032451100d80019494518443c5640814020602036000300010101413034601d440e6101c510083c0d000030784c0940d40e640c0c2c8003018400c10b0201c0b031f06a11607101e580c0700301c1c90482c038040c8502503080116544001c22185081c0620070031218240a50b00c12129050a240c51700148206401a0f403035103146c0f04251001d41c03100409900069094180034500e514107162030421404140c21030581109170340070441c03c011120f00518054541201500e0f181c1030459806070408000340300240009004c103416003a280b0b2584d1014191010311500035103090075510218215510007001140026519068042000d514010f040c40320805800a8207460402c02c1c0001c00b080050243c00703110f103903 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 354922365 1250 354921115 354921137
    0x9061b0d0b0a0f0609050a23010c0302010905100507021005091506121b0108090a050a1704050307030804080d09080601060318050a03080f0106211802130915020c0d 72
    0x7035940402d1006001c8441d0340d00c1d03955100c96005004601d540300d91409040c145d0f0300865891134402036181040700c034824a00780c001080004603803103680340a0a41c1555600c0e160500400e10034000d9413001c8032801c0340413401342405000240b42a40c1c0c0c1d02d061400da8540414404400b40109080009041d1158528484d032109400a404c08c4641b020705102c0d0305c0350450304010f09401c00302041c0c18a0b001d8907007848075680d030811aa15100d00c0c0c0d100404075040f0000c1c100c000741032032000200c25090296020304180e120b1020070b00d81011134100303032000c500110301080381043c01c004101902109140440d0041d04d0414459552141801408103041e1991410081c0852120218030080d4015085405184041c10042c1c2850700c1a520f40102076100e400200e40a0f0094a40400c4844c00c1d01c80804082d054020305030040c1001c4e031200e8a0038550041071005680e510800300d0406400103000202103070b80d858889038030491340701c980c44094014401050302c4500401c41510b00c3c4600e04003500545 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 354923615 1250 354922365 354922369
    0xf0405040c0f060905040b010c050d200102040e1f1a07080d110a03060506040605041205071d0a0c0c0c0b0309070e0a0902030f0304030b0c0c01020705100509061b0d0b 73
    0x10301034020803860200d11800043c82da07403105080044900660341000300034030711001101c3c9181641c0b0045d010754080e0058a50681c41076012940a080d244035200c2500040c4007200d09a901990001035010000c1041c02021112001064001030702f400481d02103a242074004502101145042582e0f1000400d08006011104044410015000f6410040810441020030050700f05e495400000303851700350003007250f06180b000c40d000e813241501c660303003000d1500400840700010400111018001d81c0340010b148a81b001c02500d4081308a0b1301a040d516104821008071500710f150b01040150b107a2480010940501d80c0758113607581d05489036500d07a20803005a1424815900c201d400c030085208001454019a008050640c0b080707044e1100d08804000c000d0b502e010382c2c0400b800c520f01c154082030906085500030700c003000e0000c0000d4100798203601d07910700344404011114042621502040850442400250b03440118041e0b00e021011400e410b10403240201ca0030b0011450765402540b9a80d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 354924865 1250 354923615 354923633
    0xb0d030f0c08030a090b0a0903050d0b0112050c070b1015080921030601020f0c0f01051b0313150206090a060509190501090303142802090414040201110307020f040504 73
    0x16402941c02980c1342020690100204500c41e01910f0107417078940070500d003134901d00403240303100e0301652500d05020101c107502008080d5044c246040c4104840c13000429106401050301c54111601c00b10b4603512070381024030f00004000d100c3c0000403000d000921601c4c80303035080e02110500710f2034056620381d11081c0300ca1800e507090f411282811035a04c041c0b81c4581c098001140300300002c2c1e0980d2122401201c10341c1c1e030b9200030348055502180c0d001c0540b1031540310b5401b9003d5500106042c0c001c00f803000e0181400c56000403c040d030b09c00300e180740c00d01c42d02650582400e400002ea00c014911352810381d00107511a0103080000340700684a50116088010070001690309007080d0460920164a614025000303040000702200130a090500004100da2582032080c851840701014000441400f28618010f2441c9a000c0034241d0b400d0203040401c2c0c9a07445100c54000c01b4015654007130030b160001600e120302880c11000154010089140140ca42140c01c1c04100000d0b40c0c04030315038440d85405484 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 354926115 1250 354924865 354924887
    0x90e150a1e290901030e19210206040f0c0e150a050907020303060f031c050904052508100b0a03020a0e0306061534031b02010816032a0306090b0d030f 66
    0x203a4400c6201c10f0581f915081080303400984110b1440301c0c030750300ba06503106940048820150242e0442e8001070040340101101c2c2246a20075148007085585800c1d45280c005402d03200e0107003000d40f071090422281051001c583c042d001c200c1d50310105107090b0382c0c029030340c0c4402000140180c8854845103401d0b2410841080c012642e604502c3c40310b480c4240081c1a40c12a401b050f00c0741e030a00b0b012036550b0ba0b0b280050b14003101030013080146500c011106407001180030b410342d0f0320010752002c0010017030220400303420b81040558025070b42e040345100c0101000030004000307110742c0000e41445510303544d0500d2010161401c4441c1c60310350454044440e840340000d00c501080c40311181543c05801c0c1c4045010303010314401d48444c0050312084a590366540c260344002030100c0e41c40c0703010420031800703602c040c003d28202d403a0202d1a040030b020b503800903600f4043c040341c00111030b41825003419094012840500b4201c48204141c0504000013003500c0c200441c06001d0004845841500b5403044028641c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 354927365 1250 354926115 354926141
    0xb0109020c0a05011e050112050a0209151c0516081b010201090501020706140903090d02060d15030c0810020304050c0f21060f0610090e150a1e29090103 67
    0x10303201c6050400c0e00b80004262441411031401b000450801d5205c002899a40d81200040420084507428000c4404010307003180032404070300450007190750340c004501c5441052584401d076004031504d0130f40e02d0b006d1469141d400e107485240c410700811500003940070940c1c0d1505440c1c880180010010b0307005051240000d8025400082c140302031100b00e400c043d1211100440c13203002a0303140d00e00f10382c5a0086c00b03c0190701c104d80c0003002000d480c26901a203807121001c0d00015404040008540c0426a103900c12100c403c82018200f240901c20b104200a924030340005501c0e41c540b90340c0361500c0c1d60000700554851002540d10302200d4a0b60040c01844003c0707007111049050300c0c60390315941d8890407250a403103407141074006082d03814090080711441c042e5442d104611400e0524411041c00c005020010300d0071120a0484269191181c0704014401c022850110f204075601c1c1d0742c41444240c00000c6185900f19112240700f1040c980300c107001a880c0d0455480301c40c18401200a00614112a1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 354928615 1250 354927365 354927371
    0x30b0103052112071b170403110312090405220b04110109030b0a09140f03070507060f0818030d021809070806031c030b0a060201020901030b121203040f050d020f0c030a0b0109020c0a0501 82
    0x440800c0b00c006c0140140c900070084540c0c41c00710801010303907807141001d00001868060003107a805091980091350080301480706418860311080e6041651029140f040d260284840140030a1200c69000852060310a00c0d000003c1415a12004d0307802e08003402001c03405580b80244010301070414140006103089505403040b80e58403503c1c4c5944c0703400038a01611380d402000340000b02580550540c0810300340d6030b140c400c503580d2529032045002100284003c5113004c00c100f80b140c2000c0340d10080440b924428403007044201d18401303121001d0030007090b00c0f003031001860900056507030020362a00c2d0303640990500ca840d04541307403084014000f00c103071960308010b220501203000f94041d00540840350080e0380822000600300d0410110703088141d8928115003140d8501071080c80102d00070347c2e205006122980c01c41c1c00943e1010300d0040c071141c807840140c00c280003030500d4501c1440300b1188090110010800b100c4146c0340d2190420301803144e040c19075400100c515071400284200b0510a070024020 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 354929865 1250 354928615 354928643
    0x903030c06062103030e1b2830020306060618060301090207050c010306030309061803080c03032e050f21030d060b070c0e060a030b0103052112071b 65
    0x2003c84401c2103078089010900702002841c0401001541c8515003803e800142d04030502c920510a460004e11058071003061146842014250000c0240c0c000704801c02940c0889540d40d50410003800d0001140443c01c528058100007580d40001c5441d001a022205599541d882400c3d034007611582c10758440d00202c011000144803079090b03002d003000750700030025102d4a84118004500310f500a01004000c200c20403428441d5900c03908002c44126104100160311940b2502c80b807071141c200c0e0b900b41c0301c03543c4000100001404c519001c480c0d08140151074003900c030100c1401c200102030a010352401511101603481c07055980001d503541001920178040c107416a0850740a072241d01c0843d080f0211414290000303114034944d8102c2c0ca445c0e40000d0001491420004400082030300a001194050461071b000700100c0c69507201607008601c80c5000341b20049401e02070001420000c1d1220392a07007000d1141d1180000c20002c119400708807031501901c416443c594800e085000c3c0c000242c1a01000144 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 354931115 1250 354929865 354929909
    0xb0d0f030807080718150e03060a0e01060509040f0602031905040507050306060f0d1511130603050c070206070213020d09050a020a0806010f170717060402010e100903030c0606 77
    0x6150302410550340d0340300301544d44050981c0e21201e82c811308102607034080d004100c0c0f010b96001c81c00c0148403138a0004030303650403407000070b00c0c00300c0c2551200e0032284c2c0c598220326040824841d440007003005440c191010f2400382c4450700031003990b00f805030415070004000b07040c0703071002058000c041400781303401c2085050030700381207640791210301900d1300070701c114408601607103402458600c80340c4c0001c00000180c10b16540d8296403802c2c0745410440303a612505505600075404000d014000300d0038500c03003800ca1422030000c013600c0300a0030364501000c041041101585408007100c0350250140c07001c01050800ba0401e90080c45016007042200d071600042404010001c2100c1c4919070003250a0b82400341c0b1850101d0b103441c020b10815140c1e0840d0141007082100030501c4070281c04245040e5200d440d528080c240100441d0211000c3d0350b0001402c2008640e00805070040c014010707208043d100160020181001845020107400c0c091a10025002c00c50309800c010060300c100c0e1507c0c000381d15a00301d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 354932365 1250 354931115 354931127
    0x91505040501170d031e09170703050a0f030c0c0305071113061d06030723060f190c0b190207020303070501060e07051809130b01061e020705060307030b0d0f03 70
    0xf00e960744a004041680303054a03c28062104e81d5400c0000003903a06040c0d114000040280c0780e0201d907803902c031850303000e0075440d0308000d052a98000d481c1e140d0345441002d002417110b416404003606051810300706807007140c1e200425440040e41400c190b65611020700b4002c0d40d118401c2505035000841c0303128603100100680050b4101c48045041120002c1c510030300444400c02258000c5d0154812082080f00c1c05132428402e8144400f0302c03407822012040350102c0c907035900c00160780d4130111001815450705a942c254518100300c07246440810100b0075aa61700046c400a003180e168001c82d0a42d5541d48440c0e64112b41809500400301c0e95070713741503c1e00303034040c210a20510000a0343c2c1030018268a01850840f4562003c00d130750311048080da1420010a54401350510700101d415003002800210481c031194040c00180d103820800030081c12100754a80344540c4440d08540200904000d241c4641046d02e8101143c0d05000c0b442803074400101e1041c3c0d070483c3c4040c240303002c01701454040c160420303 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 354933615 1250 354932365 354932399
    0x3191a041116020f0a0b03040303060f0b0c1c1202040923090c0103020d0f020309011a04020708030f041b18050c040303020a3809061006020601091505040501 69
    0xc0e605102101d1041107111a501805642200c541d5089110400616200051400c402002010942015101c0c00700c40e402d500300300c1e821400f003940c1d02c00038000f0b00c0e480c01c100c0d0000c009810300a4540f104002d00f49445503002c14203c2c603500c643c007104504a901500c2c4a2106141d403001c00c540f02d0b0b550311501005840800b85450a100c0802c5010404510001000d40b02e90444001030081c3d14034080118020750061032202107550340c0c0d19403001480d40c80d00017140a0740c1e0040001c9080360030302405401c040c0401c28090312031407041008000040c0c845041d20791041c0000365003082130340c8a00f848102e050090051a54511080358045422180c00400489103945481304001d00e0351510b00a005a21980c000a000b41e0b012010000004108441401d800b401803141d2001c5080e00200310480c59622001030703264004c803801000306400c030410010b5440030101c04045402860101d01946521040c05079002c0f1585170101c44542c0307001c80f006003000740f00c060000c1140b9a07441100306601340f00b813 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 354934865 1250 354933615 354933619
    0x1c060501080705010f050a091d07120c0903020906060d0c0f110d0905040203040c0b04290a0f0c060e0d0309062405010c02030f0f0607020d1106010b03191a 68
    0x2400454035080000b1500141c03076068582d041103080060080e075040c0c020a4009041040741080810720f41c00c1502c810a460200004414080c00d20000181c0b00c0d140030314403840e099141207510308060790f221419008072601580c007a603e585845020601600c01c40715845d0a103801d04490644540d4481880b0b44049121b07528020380c00000d422050311a00000c452000141c07600e0000d0000780780641c02141c005c1d209004200d15181e80e5181d0300c6141d0007983c0202806c010344105e045070f0907a004014441c991102ca0740078646004503501408400e5041c0140040200c541d00010420416a100480041c0ca00003255000101d50388010040c00c19000201e03026800c000c1d5620004801e80507540c281c00b42c00c6001e00051741400300446103038540d180306036070600c80c00344442404a800c0c03200c50400074980001c3c1099103414280685030807100310021080111002080e000c0000200b48241550f85401000e070342e0ba00d6034689610070b02e80c00b6201980141c9098805504039400c810902004030341 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 354936115 1250 354934865 354934871
    0xf030a03022d0304090f0b040f0213090608060109050403050c03270102060f19060e09010b01260c1c0e07030606060e091902040b070605090c0604030f0b070e1c06 71
    0x1148240865a02240b45441c8a620a00c0248081c100c260805001c960040c07500290704140b60000a0075107440201c1142065400100003500505104091000d8030540406000403450648203c0d958041441303462050b56603007010400b0144168200c9034441d40200440c0c1d21850085450100580010540d48803403890380080340c850350010807100d2260100702c82c00c0080c0d039100f402c0d0400328040c440d0000f44103983c52001180310b001414000d801540b0600c000035200403240005009050320760012109190310000540004403203107d49a80243d10041054036148000c200e20302e45000c0c1000d13103031001e0500d13101d414200c0700000c111085a015407014000303580c6d11007064070344450910580303400c090306000090041c0501301c02c914000c00f10443c018503143d600c001d82825908683c40c2190b03441d484005108041d48208404038880804540310303407a01c0d140d41c0d50000540700c201c0b0000c0c610501000060161400788800181c1c40c50052f100311120340111080310443e046520044640c189 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 354937365 1250 354936115 354936163
    0x2070b180907140712050c010e01051515030103110612040b0406110c07260303090304060f0207050603040f150f09150b18100503010c0314070f09140f030a0302 70
    0x110501c45a0f4002100072070792450202c0e9500c4039451051030340050400c0c81010004019140b90074450004000d141c04000034140c00c0416a40e80e0301d5410a6a49105201d0040f003282a9a0250100c0741120741c07244a030426480841c000c030383c51380035012160760381c003581d4400c00c4207011725030a03141d00c203502c1520200036412040a00c0800d0740039a1030b203040194002c0c14240941c00b6828408505041c1c0c501f442c03052016000d8609186038003c545950040d007000c90f01700308540e04551000c42034040d03070014102884c00d00000c19441d010091000e000505003036681400d20009911510088070b4406007409000e00081d03041e806070004020894113440071041240007036080e4441c00340e458200071f044040d00c11004d40c3d4610320000190141c02d84001c0064001010754091180c186042c040d610301061030001c0c1810440709107001040401400503804400b201b03142c0c0700400d0720581d114030340c21007500b5041c040031880c490190701034580c041c070a4070404024950005000023607000004684050f5074 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 354938615 1250 354937365 354937367
    0x10f0504050304061103120106021c093b07030b0f060f1602030712030f03060e060120070915030506010506070b062115090c0301020901090e040302070b180907 70
    0xa441118080c009400521040c00000e225149a0117410444012242046a5034030407103000c0900f0390040380580d10a0620030301d15900e5803191191400f5a04121703403030b5440c141e50750207014106200c1d6801c02c040400c261005e8042d00202080c003000d031035407101c01c6251044000c1c000306840c100ca507204500381105040c0c585040c07022205002400704045091030300c2118030103212080303003608076030500038000049030349400701c002c422140e0b0203540c40318464100000c02400302c80c4260440e01c1850502d5081029503600003c1c211418448114458120210401d21604040d203c0d0084031300e05050990350007a444e00030009000382c0340100203442c0142d0340c2b5001c01400b48500c000003041d100301c050000e001840c220440a00140c0e0b40d00c42c02188000f9442c03501e0902ea40c030007100c1d5400c0142814042400c500f040f074801c684d40140e00840c504003020f000079001444038806c8210700d21103000010109803080c0301d8140149910f800146d2203c00900c480004014501d210038050b054140001c0c0f00a = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 354939865 1250 354938615 354938621
    0x50109030f090807050a140d2018063304080a050c0103050f07050c0a060c0c0318060c35190f0c080c0f0607020703140706170a0603020303070f05010f 66
    0x16171000389021b0314140740c588000d4101c1000c00815074010b10320f07135860000c00c1140403c407909104020304185681c3c004820840680f04001d6402080c414140030003a403600c86038030034990480c0140c400c0910340d0340030b48000194410107503100c443c0500030400040300d010015080600d54450810ba4246ca124640110f04941040b6000c010a0316080c02094491340074000812078044a0000e64400c2900c689401c02078540f00c24228000900c840c0903c0180343c0d0083c100d0780d21008940b0352240d0107243c10300040a103c100700c809018091460b15400c00643d01c1e040d508020120f460b481803030f031107900040340d0880c0c018a0307551061a40d58440003904910424218000c5001c42d140d22800740030756283d48110741c20409104a882c0308081c0c1c0039440800c00c01c40b061203800c0b168000c0c55401d0030b40c60540010400007104c10001c0d0701800041c00006d401034508603402002c012480c81c00d5480304548805080380e584069094000001e04005010464070391400941c003c0340244001c0401382959011 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 354941115 1250 354939865 354939869
    0x6030905060f04171c0207110f03010903080a0c0504031704031403040503031608090a0311030708011e0b0102160b03040c06081006030c020102210103021507030c030e060403050109030f090807 84
    0x50f4032225800c040ca041c0441000c0c11455000090015100304100e00500880c0d0100405603010246001025801c0c6811051127415140c1038000340b01604580d030740034181d50000f03060301c980b031511000800840b61103003041e10001d5411220080c1d0039000c0324441d2030194007500084c0c076403150018091104003070000840c1c088800c064029403134800070b9821030550142c1020b00700c0e043c44c001c20882e41c003079980010341005180134180034508030501c0000c162030300c1c1d5294481d0105905118641e0020400e003410440000406c80d0040b810004004c0104e040c41c0d40740030710b0013100d00d003040d020541603521000f030352059201d01e00102c030f0b45840700401c0d00c0c2007d04403800380800d1a001814401d0a12075002840510924000581850200301518402022240044d1010b48144004006501d03004600411700084041503e1402000d81c81c010035a49009070050148081d59160b03c0007501c540c4101d40085401c84000c01103881c542ca401080140703598144400500460b00219445002107901d8003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 354942365 1250 354941115 354941123
    0x6010305060f040305071208070917060a1a15220e130302011104080c0f060703080109090507030210030203090106080c030706200d111209100503040203100606030905060f04 76
    0x5065500c2214070a20110b00070001c41c00c0050038800000080c2500c1601c00c003254080c1c0340c1c440c0c1460400f0004004410750b500680c40f42542903264011104041041c50300302c0f01c980c10103e60712159150740142001014100f9405c10100112403410541c114080d00400c23859035014940b82010600001a01c0355138010309211790400030102d24040740240d1150080c81c071074000810030300c05900129019401039403104903180c02100e5440b091f407418481040032108126102400e220981e1402091010140504440740e55508a0802803140400407880115070043c001034100101e400c005010303400c04d40c0d4013a076540c2840380100340381030081020042070380094000d00c0b4603403500d00c0482d075212000041000c049401c40390b441c4003007401d100c42540404107032140c481031400d105041d07240c050600e10190b8056001d101209036551410340144203640c6c6890701070b4480d21240000390400a4103048855824a0b001001811b5a019008202c5443c00f8209680035aa00c6994005d02c1c980100c80080c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 354943615 1250 354942365 354942373
    0x301030b06090a0b0a06050a121802060c010908041d0601020a0206160f08030421080709121b0e01090b010503060d031103040f23060702130c0c020301050a0203070e0306010305 77
    0x1d6402e0905000450b4001220700001c50b6004603400402c0d246240754019000240002070501e01854002c001001d02c00d0400c50200640010805515004044040c1c000d101c1d002c00200c0c00c0d0038860940081031007640003c0959a00c0383e6070400344c0031807005d840e003901d1100b00a20019a41c1d60000c14180c0d4040e80103013100780341078000041070f5060912450700719041980782d44e1040c04159110080d41c80389210346000940f10790308a103080c540e81c04800c1102d00300041c100c10051b0081d4410040c0d01120302c0041d814141c0d0241c3d25110b500c2c1ba030f894081c608462545500010003550103405507040b0b800340203003004411034000c01111640700442d4000e8005a00e4101100024412100320407948411402d0303909042e10380c0c81c5d00341c942005a00a2455458400d200d890060b014240c0d500c822504850a9261840b1903010500c0d4a031b103c0c1c01244082d6982c0c440342c401e14010583c9199540c0d00030000c000c1d92070300402c110004d4109451030800607450700801c0d00217043c0090007038180e0384c02c40024 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 354944865 1250 354943615 354943621
    0x109060b030a0c0b03180303011e081f02030a0f0218090105010c0b151c050303040611040621020f0c0f0c01030e1f021204110306060108101814070801090605060301030b 74
    0x880005d500241408603075120412510040420070b001a5010740010b042e080781034601584554920255500030b030406411182541c6d8a9000754000c40c80503e800c003401688039940c04c01c0c128004c02c003400120100500000b40c0303008484800421580c0004110341006103a600c8400442d151004164020070080384034021440342000d400030b4050041008050507810504106034000e1422002c1d0102e0b8154404400c3c0070401c841400f4050412961a00070343c14980f50041c01000701074110400300d502030030424074000c405c1c40b40e01210b0024004440c0701c0da45001e00c0700c8450781c0720040803c0c502c2c107004042842015601c6030194950b0148800014107210592981841c25860400309201d000b540c00c1005002882021100078071444c01103d00300d00c00807101060506242009103030038100040102004000026032260070300383c4007002c02d5855020941104d0000070700f400c52040710920b0b500c00802200c00d0348031003094169000458180309181c2e6070014003105000c2800002c04403080c503400 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 354946115 1250 354944865 354944879
    0x60b07060f0209010203040605070c0317070b1506070308040203070e100603150b09060c0102070f1a060102060f130c0b03010f05100203130605030c091e01031805070b0a020313080109060b030a0c 85
    0x81c00720ada000e400f40c0880300b50b4030359481c44600d40c04181400c04a0010074400207105080c0140c90307010019001040640751503900081c454030030003a008081c090306101007401d545041040c6c030041d14402c003510b03400d820020074420390b4510320f104030b1000900742030010490025138540300e000c0301c000ca2400d50921000004028480d0010303020001590345c28000e03000030032400c1c0c000c0c00d0340e9800b0705017651844a08001481d49001c005084a040d503010100344000c002000b1f00250f40701c82504080701030fa40b40392401c4600606030740c0c000c801191001c000403400c00c6603070b04900121402121245c440716031060050341c40c0d02130320009142415000d80200b081500030002950710800300352400b4a4020000c0006040c80701190322810815810b4454107050b58240c4a030204240405401600b4a509592645d40c1c41041e8003941c03212410100e12807110f5070003007050344c540340011400c5007083c0e512419994002d01e2890000e030307141030405006040783e08001c41c1803070b00c50781c000d0290b041c0c882c14590 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 354947365 1250 354946115 354946117
    0xa20030c010905061218031c140403080a05070504030b0c03061833040c11070501110705040f1b020f0c010302030103030f21090506041712071d04060b07060f0209010203040605 77
    0x12801d544564016640b0541101c10320003082c0307118545923503407403044500c3c160004450f500300031030701c814026a05100200390408500d990100012a01240f00ea5880008031900c2c0920b03400104945410303000d011804503d90061442020291135003030000d902c850140303140030000c1e82c1d440001e008101480c4c5c0800038405943c0e200d80d1240d07802d40b15903224030021400f1285100c102c04000361042074810400f1005200c002d009141c24a040c03420b81c05070041c80364654030607200c1c0510560780d844150850180c40d030802026100700c20000c5a0303280355941d000e510790200c010541d000c0c0c000e0200481c8558002d109890590b5096901c0800c9000ca80c5400d440d82c20b44807a411414488884c000340c10000140030700c011083c4038001078402801d003403500c2280c103000e460401c200c00e00c05004810b98035002004241e8403202904e40a48508040c02d008001070003450103540d0480c1c10710310081141403040c0f000b031000501c00c443c104002540c9001c05800c0340248829240180c2007040104000ca01c904 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 354948615 1250 354947365 354947371
    0x2040515131505060c01020703020c010e01090b091c0b1e0420120321130b061909110415020c03060114060d1a01090609050907110a20030c0109050612 66
    0xb41041c1c40a880b04009403054000354181882a90001400c004040e8103210020b00b0010a00700825103400d00c0e80060101d103254011400070007000b00d41e0100d41d80d290b401840c00701d04044a0f910019460741030007012507004407130203c0040300b00d501c5608001c0035844158811900311403044d28400045132a0f91001401c500f035a5841410207805104440f03082c00189000401d11141da042144031803201c0c0c858000080100e0601c0805040900c0415a008030280e0700074400c468888015000710074805541c2000d80080b8039807464810f1403c0060000b4008105035080340a25580c90b80c0f020b14101d80d1140c0c134031600c40e01038004500410034a08031294130000308000030310560030040c10070f0740b1104440d180c00d004407030980080344003080d558001040902906a07464800c0002d400d01d0302049182002078070303800c10045500c1520340308001c00d000c11518264004100708154035420030314009580c0f0041f07903502c28000c00c800034520350701940c2d28808a50001d40020304000e10344103a005054401 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 354949865 1250 354948615 354948641
    0x1050f090403200304060e0108133807030f020705150606091804122a0c1806090605040c09090c0203040e0412030c030203150f1203070605040204051513 67
    0x6560301c50750010501c0341c8283c82c00542e00110b480300d02d0140b0085c0322140001e022030512046405001070329000220f03942a0517000828004080504010b20004841d600c290002180130060803080042c207004003603020b48400d6409000c900c182c1d41c400b5040340701d003800080c055030100131130455180310440300d40c0d440903004140350b04100011002c104551201500c0e03070400e01011041200700824601c0c907103528525468440d12108611480c2e03041c01e600e4078036990800078100320b482e00b04031070340c40c03c500640300003801040d850405142410191800d4015802c1c83d905011001c581030426218020304d030700d01c0d962014031072803a003400f14009017030461048046020400020501c00129905070740168807074404201401c0042d580181152540085030342010b00420900801c0079100403000320b10641183c0052180001c1c03000110f0822040754503407050300000c1400c1052101c00c1e80720b680300394000d813424042c1da511000c00d01845d8662040160340501200000140105a03510445104240c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 354951115 1250 354949865 354949877
    0xf010807021e01050621030403170d09030206090616020703080d02070503031008010c03050f07110a060c120e0c06120406090203150a0b1002072306030709030b0f01050f090403 77
    0x50000a02da203144010b0049540d607443e802440507906102681d00205d103e50029846031020f040d85050b02d910032440090100c02041c6165841065800111001d6000200c000c0000c100303946800394407035400b10b400012a01170b1100103807090046030425440b03c017035503014000c0d040c2036a44800082d0031060700491074139824042c000008004100035400b42c84d007030071084282450710000e00d080d03900c0501c43c0d80801d13090400707101c0c54060345040d0710b42018150a1940c40c1d540d2540300e0707078909241018046d04940c00e1011040f00141c120100c80011205400705020400340402c0c40c40c1e40301554580d00e60008801c0002100a0040c0c154060b0418841d000c00f254049841c1c000a180200924240c0714180c1d404050008861b0184151447c9a40a0b90030804a00da006d10207503c500300341c0300787d60704200c00103503c10055102e42d521400002c0000c284980b2400c1c410001421500c0601046540020302d1f804202c1320010550683c3c1291001004595540700c4a024020301580c007500450a01034 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 354952365 1250 354951115 354951133
    0x80f180301090f051204030206090d0303020904150816140d02031203040606090605180708090a020301150312080c040302010507141b030c04021606020919091e0b0f01080702 76
    0x6020701941d15003d0151182c0390f018940e505009090030881c1c0496030016008000400040e151042030300c018840444520301946144c0c01c060740a41300d42101d01f0303482440c0c0091041c01071b40c000e50b00d4007a05c600b982250294071904401c400821400d01800c9800c44180604500501d42800b110048a1001d0217850a25120b00e80b03484407900203403003c540c3e03aa00c034142401218038030b1003500f00034401220f085184901205040c111a00060f001c5420002d001d800620542d108015407840664054004c01080300028403034030003c9820701048a08081c0b00010110701441051500c0c0200c100841c00ca00e0700c0c0c5075030b0040da040d610596040380c00e08140c89030202180d40c01d021070b08109140100a41003106407004050600350703080e08c6107114520501c070400f01c020440400810069220000590349e03510344c4001210426510032401900d0203100000c10042c000d500140340f05501c00205045003145100a03400f503401403240700d5004004c080e908080f56120b01020341d08510315005a942c006 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 354953615 1250 354952365 354952369
    0x20a0905040c2c070e2d030a0b0f1303081812030f04030905090c09010e060d050702031c0b090601030c030f11040608010801060e010b07080405062a0a080f18 69
    0x761150040c1d2541c483c90804403071910030502c6003560100c4a8503007010b440a4a000252116100346642850f40c108005048034212054481541584000301243d50031000e03464140001c5404641000101030740801003981d4205c40c580c014080c50303141c3c441e400242c4d1156262810260140c0c60420203104142c00796803440e40c168020360044d80b400038003034681d01d49401c3c007920003d9240d01413801030000c5410014081d1207130b8195000c541007441c14a0150b900e00c00020300d50702440c14024185445c00003401421500000140840030032000d81c408000f600e01e400500319a5428040e60b004103030071000804c0c0d98442d038043e041082c140c0c140014010065850102210701c03103603015040601c0007505202c03243d00247c0041c0180b903404028008503040918021001c0018403401e00d0380d882c0441c13070104000c940d00c1941e0140401074001910381c0342150010000d2891070481c41a07014031500c0c0e50013141c002040044d90350303400201c030b103181c00410b11000040d075100842480d0360028105c4070713212030303 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 354954865 1250 354953615 354953639
    0xb0405010e01050f19060f0302070b1e0a0509060708040501090c06080a140c040302270703021b0303150f030a14060406110c1023090616020109020a0905040c 69
    0x10300844401d4419940c103003000c2c04002e042e00d40c801d03441404c1034512201030210b4840540e0940700e06150040c998500542d06501901035900020203a10343c0c5010085520300c02e0307003401945a01c80f1a64000340c0c44a8000702c044480c10360750031202c2e4202c00005489903010315411500548903078000180e01e480c64582000103202d40d081000051100414003204171081d0090b10480b04141745240d840b4100f0b0301c0252050300c80e0b484000c0c0a1000c11848025694500c45071400011151654030050318054200900960240004003840d0200711030340c5500400001c1540c1c403441400d580481c403401054100002e00041101455141c801c01d06100e0008480d120011610101000104002c0c00c143c40d1072800d440c01c6100b5200000c4041c0024400340c034001a58134542c1403059000108044c03250b8984212150342005500384101c41400d200702500c00140b101c0c8101880701e00601c0041480500f2426a030100801075400942c0002c18885802540e2159030000d20851181e50b405640e00103882032 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 354956115 1250 354954865 354954869
    0x15061d0f1b0304060c110c180a0204030c14010215090a0b0a0f02210105011823090103080a0305010503241819050d0f170603101503170421060b040501 66
    0x70691120081c0f00301942000d90206206d00180190000070201c4000c02e080081c0250102802500c800120f081d6400a40c11140559002000c01ca40161a07000e0001c81f4085211402d00501c240303030b012000341c02054081401803510101508091006031203460b10428054401c20b0169641c10520030748840d20310003840b5020f4850306582d00d400c2e03410f81c01e0f01c1850050b4402418480e0a00c50010300c3c0412198503400c0e1421401e500d0f01d101410001c05506460f040c40b06500f2030704040000c001d1000020107404885440d507010302170303a038030754041c10780fa00a100075040c042d400d258181030702c1b4031039000c41b47d82c01581c41003241c041c2461036190600c2c28840c030f414401c08590280c0030000b07005081c8a5442d2051807810880740190708604010000d05025404071120040200410583c0d602804403421007542c440c828000038400142e504003040c0c00303103c1259a51504d007101c220071349040c1e058800325488240600120881b0400402c480e04118500b1680c85541e0340d0704030f050355214815580 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 354957365 1250 354956115 354956123
    0x612010902030714270301020406050406050a0912030c14010e1c050903060109060e0a0c050a0c02122e06120b06030a060e03040611151f0503060415061d0f1b0304 71
    0x4622401028140c00140020b45e5000ea40108020312805401c4021a821500b0914041c2d68581a01c6000c55450f0b00c0f82d00540104031180a00c401032660000202c003000e8090500080715080d01c0500030700300c40982402d42a160054100070b0040c1c000002100700203207690418a1420b60181c00207400c11000760000ea03030080c0d441c1c40902a6811100b070307031035200014403001c00a000c03491401400d50f02038070854204125820018408544940701a4480c51610404a844e100000142c081541440384d1400c9520f5103040303e00060380c02c8030b000e08411540514001c0b0000c01040c3c9a41e0701c0700200602d959050700c1000550070008103244155a4034400f0b40c006140c49600b80040123003156421207071014a035102c040481024010184040e41201030400c1108401c0c488103411301d14410558090384e45401034004000c10302040d01c480010410762400f041000d2a1952403400044000c00a1116a1001c0354001000070444c1a409a086907411094015074001d96002581940c0100c40890f = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 354958615 1250 354957365 354957397
    0xf050f0705012a0504031e06060b03090a030f090e0105132a0207052d03010f0c030605090705030103031205060301060f03050c0a170a0807060f020a1d0612010902030714 74
    0x4264103408980110091070624004d441e061858642c006580003200e1412640103540c00c02004010380ca0340108002c0c800c8000241d141d113802020103445581111060b07000c1102550080015403140241205842c404400382080385d00308824490480340c3e5010700391030380d03035a00942c1d1680700c000c24101841340d22442075000e6600124a0007420080c0c03c0e808180500c0351401848405110b864050316840c01d400c030344031031404084e80000c3c05040c0311034100001c64501031600900c00d81c16085941558030039aa41803030b170788402d00c1c01c4415103c00d10001d400a50303206109000701c8a00d802840d08108010008507030991189a030310b01c40003495100321044d6000d0070f5410018103040d0181d40c004e08000301d060030518076520086840309040f1100a1180c000007070503030f0130043c4c25484400030380340d88441152911204a40600301c09180d1481c1c174130031440d501038902c5528140080340c00d0b03840782d04a034030b41c10791030802d0b0b01c0082c3d0809050042480079006500340200c100c80d002d00285601c0e10426 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 354959865 1250 354958615 354958661
    0x108070603060e06010914010c0b070e0f120d1b150509010c110d180b1201030308160e0409020102150702010605010909090c0e040f050304060302040e070f0f050f070501 74
    0x34007116a03683c82110714a10403010000b8680c0c006c580d140444c1c61141d40710103070b03045000040760949440d0314000d01e0701c09060284407030070754000d5400c240a201510759091094090080100c0b00c0e541041010b9a1b03805020340c0300c007062194140ea0703011000c034810050040c030503640d015000350140c1d200d4080ca0307039101c0400180c000c3c24004c142c1958954141048500d80e066030654a540120504806002030440608083e00901344048000c2031840000e5450b46004041c400d8682d000f84415400112a00042000c000000c003171070814451603140c800041000c8018040a012024016415401040e416030804000c14800d5407190304550f000266040c1000c0014085003100e40140407958509107401d8002600646402c042e140c4141240e403040d5554a02000003030070b0140c005020f40404100000c0854064000d4429120b004110035041c0e503840e213003200c0c45034240d6489000580c100c4001a0b60b5405003000302002408005080e140c501e403502c52500391038941c9440c0c200b1241e65154 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 354961115 1250 354959865 354959867
    0x70203070b060f0d02060f0c070f060e012d2a14070b03150609030a05060a0b0d240b1c0b090105160305090a022d0f0a03141501080706 59
    0x1074640e20a108a031011190a60200440c0c101d06025030000e019410010b1100c00800c0b04405036841d03004044102c40a0980328403148081200510a000200e5445110b10b241980902101d80c0d001c0c0300720108118840d038a115560075030755210074140a2040b0401d0140f94480803410320b0400ca22801c0301405955028540614030999651084055421882c000d00c034442005003200d4001141d41120448842c201c0c000403880d20031031074801d80c10b214070202c40c410400701240c0301d4420000d680b0f04000c0000c0c1c21040c058007480c51900280f00c081d04200044c41800350096403140c0140d00440000c0c202820400305550143c6141d44180200d0680044810045014881540031433190000c2c80305050a03031345006544803180d101020b00d0344a40000c0e103500c0c2d042289881e0542c0080460545280d515038007a407250a502400014091488800d5158205003024000c140d4002d0103016015145840d031a0340c80c8611800101c0d14051480c00c02d544407414031119002c1c00d15600900401d85c60400 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 354962365 1250 354961115 354961133
    0x180c06080f07020708030f0903070e090f15010b0a05071502030a0207050106051c1707080307051c0b0913060908070308091603030206010e190c03020d060f23030708030307020307 78
    0xc0450b0455001003824408503c000c41035a6041e070200d00201c2c0c4500a00000030304000150304110745c00c6004804112460100243c0c4078a5008980107407a580c0d0407106011000c00400d010b60030203010208003241c4400e210358000c0508034051013101ca04140611081d00603644183c5030b207211036402160583c1840028483d100003400300320741d22401c10701c0010000341124690000a446840486184040c00450380200d840e5103903c08a4070740d603840c105001030260340060001d0040d29004d10b141380c001c5d400a11804200d950002c21680c0076559030b2540207040c071100305044400035203d6084900252081c00503103400f40c40b03501c0f2800c041c5083d40041d8540054200703800f04c1d4000303003082000425004102d0fa03054900070081c1003000e40d61111091a849006007001d0640c034036001400c0c0c9205d074182c0c00340c25650f000c0305050290a5840700004511000c9014202c50424401c0b07082a43c18060380b03d84100140250948201c240c0da100d07501d0444e00100d40b02c0001d038000003480c40c100034004d0303 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 354963615 1250 354962365 354962371
    0x912160816091805030c01020703080906091209121b1008130201050901050f0a0c030237060b100203040509060a18050601030e010e0f011b12180c06080f 67
    0x600900c0c21141c03000210068440e03900c02c289109a0f11500700f52400c0c103850800705200d40010880e80d6039444005024000e511802040c0d0018200f440490703603400b0003143d07a80c01500408020000082d40703080307540e06a408030818070790224110703c1c0206221420f0154034000780324144110701247d807030340074000b401816098000401541c441004521941200203046003a02845c00684070446600144c815110b110740c02c00002c01d011800302d00c1d0507030160070709038058400d40c251aa00b0081210607070041e21001d010080c60600010659003890b4010f94420b402c81c09450042001d0140c2d07004150100e401d0b00c10140180c00c0000e0500640c24844029900100160340680385185851010b4240e141c0c00d4107540e48168860001c034489a00c07942180401018240080040701c1d00035400d189d985001e03118008855007010300d40b410200b240707503900202480710b445d00c10121410f10300a5004083e80b1010380064080380d004000410400100d40010f00016200d0a985041c07079150155061001 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 354964865 1250 354963615 354963629
    0x106050a05040618090203011710290a0f0803030108070605070b0f07031d0c18060f010809070b0d05071b021302070507080102030c22030b1b091216 65
    0xc00100d8011a4020211400c82d8840d1604c5880d001040c1c0c01e080d9441e0f402d6008001c241d0000c000400c40014050b0220340d4020510f00711000002d10110000581e04500c49240d0711403483c9101761003000594107108080d5800414424080e03454402950707440c0d810b504103070742540c8040b0042c0b20030801000000044e00550900b20705120b0340f030b601ca007030f4103070018102200c244001c80811161402900443c140e040044440d89070300107021210790b40c5843e0f01c017810744184070090700c1c602e080305070313540160145c0005008081107582200040d14451000340c41222a0b02c100c240000702140044060000d40520000110315402c0c42c1034010541c05e80103000118142c0107009100041c0c0c1c3d541c540c65012044510050f0b11241681007050070082e0302e600c044402e5000100304030460030000010008502e50a46004114120f0b1450541c02002400010186090b03240070a03280b814020303965544049140e115854104c46401041c902c035040042d80e9200d51000520720721072200c0340c507070001401d0b00e = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 354966115 1250 354964865 354964867
    0x901090c0e0c19110a0501020c010609180f0201022a0f12060f06030102040512010c080c040303090303050d240320130b03070302180603010f050106020d1215030812010605 75
    0x310202c00c28052040080c0040d402d88806103110050b4040c40c090104030920301d044e11042481e50402da030103540b0a081241c25546404804180300d401031084131060072403003650001001c4140d981204d441541103040c0e066206030700c00c0b0900c5240c0b0b000c880341c5081000d80744161804444003441070056000c2045407083d01d0b440a1800c0314880040c1c980c3c1d10080b00d00100704a900c0d01304c08030340284150b0300220b402030040f4001415005054100e4010041b450351032451300e5450f1243d1184501540c00300600050820070308001003403151001d0301031410030250004410340300d120b58074011200b2011800040f240c1940800900c41d0003d80694030403080c00308131580c00998000500104030203419070b01215a0f0703030b01c141c0d443c1c2c40402018018603030141004000d03d186640e880c081d0300d0708480c2c8511960034503000400d00080f030f00446040307640303940041c03215140c001410707150b0806071600303140e10325520424206144d050108071802580101201c0359549030740c400e0710444c110140c00031018814 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 354967365 1250 354966115 354966121
    0x50d050a02040902060d0c031e0e1002070303020d020309010b0f060a21141305010c0c120509030a021f17010302060405011d060a09080d08010e01050d0501140901090c0e 74
    0x1801040e05119260704031000a26190103100298440c001d803204422024600503040040540550103644002d06214401da1483c074004120381c1500c2e41c485031484107070081040030100d1412a005084080c0c402d04005d81814482c01c0480200d810072903085c0d00b544c0d101d0800c988242010803802c03500c0388050321407a281020b041d401910540c5a88032000c90b0040c2e61850090080c002e80c0011000908410300c03420340e00700282d005084000125013a5240d503e404501881c0c28017442420f50305c1c9601421602c014407a1000542d41a0400401650540a188501c00041e03031082e08010603000652485802d402d850302c4005c1403068140360b01e0303d44886210040c40035030b07606416141114030074a420307408002d04101840600c0b4144014540000011035008129600000c0c21380c1996a10310455001c100c00c19400c6441240a2107070018000c1420018810340c06c210400c00e01c018040c400200c0c40c010003c2c5030104140040b240d5055a9654490358001c0040d01c0c4401070051640340c0098916003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 354968615 1250 354967365 354967373
    0x3190902100c060e0303041a010b130501050702041d010f0b0906090408070c030c0609030311150c0c0a02090411040507050a0e010806010c020d050105011e080309120a0206040f030309050d 82
    0x40d00d0314074050602101c80889000c110058214220004000080d02e8581c21b0500e000f00350121408400380f51610281e001203500307034495094446804c8080044490030303141400550315580000c4d8166000b40d102c0d8401342d0003040304804e1051070b401150000803589450a540b504590080b0b5030b69106000c50401d11009544821106030096040022a0307942c00f014078120003c10400e5000800301e1820b0030000520903000071140b42101d00035212400b500c94808840c640300c0300c3c0000c2d4400200c0e580c0300420078141041020f4003d01e074204040350b1400246400003409464202c2d42118041480e400c0c3d00c04c00e041900030305402c0030036810303e02e00304080510050710071842c40c00c91904004a0b00009a0603030f01c00c260317440d12290058440ca024400c2030808a01802d024007a00c0074005008054640403601c800501c01100c200c0c001450400207648100b01c8031090510a0805c180300e614804805039540100a000505140c40c078502900d03e14078020f070001d1115030080f44170b0603007004040042 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 354969865 1250 354968615 354968629
    0x8151e060a0905090c040621021e0a02100b1e03030c030426070e1302030a0605010603050402182211090702160f0e01090c021c0201060521070e0a06050d060203190902 73
    0x48d20031250554103540d071a05610080c002c20784d1000c1c1004084542c811118140c00050104040c0c90b401d0b9103010f02d6410002d02a60541c0310303410380040c542c000d00000e8000301d1065000440b4002e040d24507003450041203e1964105401106541040100510007844610400c1c0500080b40e0050424140341400c0b40c0003100b0001d1203150510100c00007502107550611003c0344142e8402800c10855845da0030040041200f05c1e01207004048514018407110000540103201d8102c654510440c090710b40b5400c00c85c081010f004488404229180c42110340d200300c1c400d8821074842d40146114040d030074840c0c0204002c1d1344042d0a50704014000d1003c0e0980d80786480c1583c40c0070101040654848900703c0ca1304c81c0680d07010303801b0000005d1240185038190401b10444104031800083c01885001050038034615205908840e489480100140890780840c584c0c007506e1740e14005081907640000c240c0301040c80700120340d150307800001c00c0b070242003d061003040100c40190420038110940e0204d844 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 354971115 1250 354969865 354969887
    0xd1a040509030a1d0a0e041b0e01140402070212031c0203090304060f02030d06090e0c0f030607030518030a1206170a150f141608151e060a0905090c0406 67
    0x1004643d4101805865181180201c0740324040c0500315466902c0070140f14040c4103540c00c0700da0340759025030714075201c50056a000540303805402700d207001c0e440d05283c40050f031260341089030456000d00c6124090782e5400c9032030a81074801303409941e5030400701c40510645003107510791145003441442441031962000090350b054035050b0800c0000c0c1100804140c1c99800340034004d100c51410002c01259600458000d840f50034810000c858078228120104221032190000658142d48000c0004943c10311942203507402c0950039401090b80c1d0500280c41e401c40e40101d0000c00413500036264680e90032142d110b1003000349103040322035840c0b090180d421511b8034034800c005030042c61420001aa00c2d5041d034040001480c850408000c5e00441e01d031f4110a03040b080314240a291280d490504020340a1020240f290301d42c0803404400a05140810407100b05d011000c50007004000100010394503031000416003081e031921f405000901d084100803807200e000b0001d000f28001880708206280d004618101 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 354972365 1250 354971115 354971117
    0x609050411033009010915020f010f0b010c0204022203061e0507020c010810080d0c051002160f1e030203130b0a12020c030c1501060210050c0307081b0d1a040509030a 73
    0x2c0d413102c0104c0120303a405c2054010090f1074955150781c900154000500902140e402d5009101e4800015611000c46240458050114040c540d22400524081d801804c0c85191110700c0303100c2091500d001c0a1a64280e04208c80303099032003105080d00e0380ba81c2e55400301e072a0f8004082c001c503e80100020b450f5090300454506122015000c44d0750882c079005513401801d03224040315034514100800070541c040072407096443e0b003c0c04042428220a070300031100b0f41c1040c0d040600103081702e0f580b955074041c0145c4054500c92170740c203440780c00d4010282c0c80d4001300b8000d03801140c884c00c0001c034501c5080e81540c4410407440c0c0800101350b1054108030424628521804016200c5603034840003400c1d80300d8441180c059005085464040345074010005050f2003140c0c0c2103600540188800200b00e0360199030520000e142400018521481031071207d51240c59483c00c245d107900d101c00444540d4200d04c003803400003620b030352a041d1040f6030824078070250780048034241720b0781c100105226281c0c400c00503024 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 354973615 1250 354972365 354972367
    0x5130309140a080d0e0405090c0f060a021002030a090b0f01060f03090f0206040e0103140105010b16020316080106060e1f08040c0308040801050105010914030c0402030a06090504110330 81
    0x20300710b40d9440d01c10341e000340011020b8510403411550001c105100c1001581c2c811890302c004a1011305c0e000803070020740b06c3c01800111000c46068100302e01c0e40c016165440441c41944040c0c03100780b0030350020b10b00075034818101054014440c03401c82075101e0024851003500318050010005c02c0d900100c0c503445100d5506000600160f241440590400301030b101940000000500142648011a200c1e0481c1d016080c1c04c0d06a904108405090350b03004e02c40d148800c40c082c004100d1100004450312100b0707100401f00c3d50340c03258030904420301d440030750721000940c2d40d2404100f2195401500b07142d100c0781c0c119910b004000b00d1410720342684420800c0c2e0310401c08003000103010400c002550801464005000c103840d282c0d610807090103072500340034240c0080c0c2e11040001c0d076151941000444620000c02800503c50904d09000003034000a1202641645514002841e00c826214160042d8001c0c01140d280725501001e152620041a6000e849680c0200d00950155910100070b01c117680305074040c03 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 354974865 1250 354973615 354973649
    0x801020307170603010b0d050303040c0806090a1205090909010606020606010c20061209030a090f030b1f05060a030e1506090106122c0d050a020c06030a0e06130605130309 75
    0x309004001c000d0103160084407030301d400c07c2440b03c004042c6104912410703400c50050b0301c80541a032210310580b000341c000d0384805881c80000d20b510154105460040c0f9240d41000c00680024018810540c0c80b044035964070b140910801c0e41c18400c050784510282000b10640d0400d41d03e40540d0540591504406944504001096a0781004507845483d07034500d040682d060241d40540c40e0340c0011944c101180c2040170005003250902e550360100c0f5004003401505030345064900e00c2141e400d00601030035400da0b1001080c00d0707440101815a1000d1560700240582c071b421219071a100b62001012500d05000e0704200c166a203c06000d8103541c000d08d080c00c402980143c204020f400d48600e180288030134403c05404081003198514088140c0e02d0444c1c602303038071030881580c0601c1032000d80001a00055005034007401c0c8440159040ac4426000184020414180c14100042603400c440d04a100080803014482240125a0002c401d0701c42289451265640982441514440c0d0745103e5804904 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 354976115 1250 354974865 354974869
    0x5090607031808070b1b07121b0e0a021804050907171f0b041b0905120a0212010e06072604020f211905060f10030c0e010f08010203071706 61
    0xb400000308038440841d84410b44500c03414038503400000c07100d1640038002c64601000d00c80003c10f5004c8403041c1565407004082611414803c590030030754603281e071340110f200040080100119903ca611070350401600d40c4030885136141d01e2600c0300e03562449a03003840c0c1840b8440310702084007400c682c1000320130203030f84401e4541642810b480500304013484c00590040c11b01906160000c0746080c00440d000c03c81c020941c0020130341c1c0c040b050568000100011018000c5082c84010441c620a09100b110780d064000c2d40000c440400c042c150ba1001c0e5100c001010410204100c610340101180c03d00c07001e1441c050300700014a20a10145050b40e0459038041815074607114084600c07030b940541a5040c80860000d100e030754406510591049100e508601a01d40c0c1c042c0d000e41131000c0d0b1000107407181c1d403a40300280684400c00380c00782d01c4444242d10000b0003e00d4a201100c0280640c101c214100e61501e40c0020328405580d0256a40781d00410400112030b80c001449203000d14503103860161502c030100 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 354977365 1250 354976115 354976157
    0x90606090414030f1206010318060b130f020909010803070b041101030e1522020a05040c110d020601080601060801030302031603052203110d0309093801020601060509060703 76
    0x8800090780400990080e42d0010b03200200b4104902c40c0c8085c0490300c940707004604079100c03c0050b03440e40c0103132001d000c00500d040e00606d07505500184145140c8064034011f03400c550111196403039460380050100c0c407508103005410700500c88007003d075081200e035454804045070f004000605440400c554008540e001e58040092070824500700c40e100b820611061401d07140640f9900040d41c1d080c01912401425040c0b000701c841c0d80605240d20a51070482848090325840d0191420b00c99040903020745084100004083c4004c10b074000d2015514180e0740504040040e0080c00c2000300440050002c29000001c5401c0701003042d121807031504042c04c040300d060107118560900c0100e180c1e094181c0e00c074224194000d40f4054106012606c0500d07081022a00d401d100013030100d098080c041110305166403040800407400007000700c051070082024880c50a0360958012008202ca194441c6540d0401c0094094011414180d1a1801c52400540680140d0f034005003005052040391504507181c0c8 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 354978615 1250 354977365 354977393
    0x1203021e1603021203070e0d0204060504050c030411010513060f02120f04060207080706020712030e21010b04090506060d0206040b03071e0302090904080f1902010507030c02060906060904 82
    0x21003041d848401110a40185000310380e07003540144660544050081100d10407a40140d5007a111418050295024807040d40f11200e802da030701c584d03207001c001415192030203064400d10300309206694910302880c0440c1151848010903040150074401c015028803988008810b80d081410a92400180d1b410201c0c680748001c40000c074103d03030216406860501c0100544141c903450380035224402d480d141c0380d941e030f041184201d00c0144c4c040744042014910b848043c42c1018000c0c41c4c005103402208000c0783c038400b0501e219010320b10140d0700842c034000302803003442480541140c06020088803501c0e0196543c40240a003446091840c0c407800c01c543e00c2c2030032a03008009100d229501d03450014030107441c1362003d9518072000702c03a843c0003001084c400d10848101d190010046400380d2070b02d840ea08015040706a8240105004005800d03200c500a03005d505151119030000c074652234221801000d0b1142d1114960170f41d4010801d001c0c0004c4080f400310361049043c0c0343d8050540e41c074100010554147d03 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 354979865 1250 354978615 354978667
    0x80114060d0e0309010306170312060102030d090b0402181302060c150f0402090717070e0111060a0c1805030307021009030b011706010f0b07230304091a0409120302 72
    0x1080d0b880c0c1d8078044041c1c8511403090700c3c1081450307560541c3e4201c41c0c8540d5401421500b0401c400300740441101c5155400903810310403a814500541c0c100c070100e40740c2c04400e4482d142800100411403500c000300d802122186070b03e4030f25600703001d941010300c50b0b504d0350024840e80d408101d082e007a00081200700306810099a4080d01403c245240da0150305040e0760a0340620302c00c3d4006904640120400309004145220b0300c446607840e440100c0c2e2403c41444103d041280122006902840030800030f4007811803290300041000709140098100c00c4040002e80340c4005840040020356004426140d030140c041d6083d5101c0c0500301e20448600100e40c1004114805203000810f022071071120582c00c000442c812285580d0302c8580d66490b0ba11244a002ca01c5c01d8100005800549104094075003501e1415a94980161011084c1d085070400c0d080001980e0783d80345c2d0b1400d09030750b85c8140320131240182d1b81002908295100c4505021480c0c0c4d034a42410b4000030707195140c2015114082c18084070b = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 354981115 1250 354979865 354979871
    0x60c191712010807140307090b06040510051b0c06090f0609030a0b04030809150105100c0b01150207140a051507060c030e010c0207060f0c08040806010306020a0210020a080114060d 79
    0x140d014001c049520078007901689202d104408a1072405103102031449140080007402a40d00d0403181700c0c080c09202c00241c0d003000d010702c80000c40e900c84080285001c00c964480c0703510340d0049031241080d1115100c502c01550b04c4100c1c4d2036040d880c0d890840e04042016101c1c10400d60303240010512074441c4443d600d13050b02c603548158052224007900d2034015407095913400401d0300c0300d0281c1c95941d0031074020300e40c58041c810010811352516400f02003d15260703081c092608030668444061040099004040706c030b00c40c0707a041c40f0f0705505000e0381e000352880d4000304400300709813004140c140300e240c042c15000d000c181c04615400d21200051fa030580e039011005100103858500011b018100c1c1c203030341090540c02e00010a41c25800030450b0b0040d1840c40d0b503990071481c201c1000f2503c0a00d0500d0544112004000c0402d2000b82400711a0295003c4c050142e998088070310024500000300c10342c20803803481070040600803a0307c0400e860454105010342e00708180c8020000380c036803040c2d10a940700c0a00d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 354982365 1250 354981115 354981127
    0xf090d21150b0301030309140307170a050a0c0512010501080309061e0d0f110a020c01200f070e070810180b0409210903050a060c0306030f0804080c060c1917 69
    0x382c00b50081d4140c030f1003642c0e90299650344a80340400040038501d2198541c100003403d0240c80038541102c8006d40c4800c00310b134082d0f9245d80311075050814410064802d0000081e092005050001e00c148805980c5070081060f507245c074003041e031a401180e064921403800000c80398401034100d10510001240b5018007030340c1d07000c035281140090107054402524181001601c0b4035054490055500c03000c1c454000d000840d40c000011150566819134449220708115500202080d003080b10700b02c402014401040301c5d508124000e0301c150030041c400810005c0c0c21041150f00c4101c08400c1c012140043c6400d544802c0c08500c6001901610220941280c40c1c8890302082c001c3c41c11900721158100b8960b800700060b542012544018140405001e07503000c5846100081c142da80410300d540c2640c070340094085d03104d0b135801c2d200000484d415182c10102180030302001c8000d0029000723200007106d00929011207050419211580c010080600503100e60070030741880700b4100d20141c0b00c180000e03910741e980 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 354983615 1250 354982365 354982379
    0x40b0315010e1504091e08041706040228060e0a0b190f091508040503040f0b190c120804390f031a0a0e010f050f090d2115 54
    0x30b0030865800707400203d24102a40c0c1801c1030310032049425001000c0403207440381c00500d51840c242c0c01e0011524140108800107850b000200c107280d500b68580d000c0d002c01d04280c0100310061480070880302201d880806400103885417481001d003101c440c2c0c142001d60321004000030300808002e5201900c0310341c00056820300c4c803801d450460250a01c070340303451034004640300045403454038a00400402c1c42d80d03c07050181290080030010381c028498002c69140035145c0303039540c141080561011500070808624031a0105008541001c200c10358a030612910240c1e80305d100d410181010901c083c000400c02140c2480a000241c940d810340b00f0703080d2407401890700c12074841c14401e85a106425050b800780401c0d0004921000307030850303030800d04a10070308c1180750040c0f2004001800008a0558401c43c00d462804203001c0d407480c0100562000400785010000710300c0000380108400400e41000404a00c019000002003200180010704055640204124403001340b1282410034403103800d0040000d015 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 354984865 1250 354983615 354983639
    0x121704120221061b0705100507090801020903070b091201110c0f1b040209030f070608060906061204080a020f03040803130b030c04090203100302040e0d02010c0c030e040b031501 78
    0x100d80309940307140ca8460100b420154100484005601d140c002502080d1880e00c01e0403007004803040701040b0791800016564191403d030707800c0181c6032034130345072001c2203440c4e908005454014281d450095150090b00700000792078441c1c46c01055030802d0085210142521848604072003480d40100800c01e20f24200104541500554550f00040c8100d03029142c0c01c12010845002003042c3d5508000702d000240b00f004080d4204004150305440740417600c0380c0c1030608020300d83c010184e60311402c0050510b5414000c86403402007801c2d016440401c02c80794080303001c1505c1640f140e08003000030346400281204904007a0701595003c002d100100340401c0409002c001440c00d502500040300f030980d5034084189850000321035410310913009000c2001592074076002141c2c4442c0c0c8010324111581c8980c0060201c6148101380900d581c400c48140702c8c140c0d0240305107003840101303041610342080e0310355008021041c44540c0c6405140c55000c42c1910362400c111500340c01c407c07030305061020360311699400c2c01 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 354986115 1250 354984865 354984899
    0xc0203010f1d0114010b0912100606200d2102040b0c010b0a0608130303060b07120306060206061309020d060c050711090403120e07051c05061b0301121704 68
    0x101d510002c104140901d8144200d5004102c00e40900b81c907a0700c0c006020080d50054030030281c01820381d1400603040c050500040c0c16030f00030a48000b4015081107001088880c8807000200460322482e2003a140210001c0c000843c00314614000101320400104407e01c4d0a42620302c05013240040740114108500e00701600b82c0c0e000385002007100101441c104100c1c4401485036402103040c2d074005c0364820800b16801144923000341404500c803941c80c101c4990561040c40141e6846052008510b4a0f9a050040b80001d081d03900c0104400e0074400c1c005000458000c5101c503a03943d039180c11104640300c1c400314a582d079400042c10003440141c040c001d4920360091500301c03034100d45520603401398501044858051500743d59640401c0450f105541c0090502c420034462620500500140640d00e40c80803849100c01400c0b41c05211100b0301e4000d01c3c082d03015045459903000700301c90360006281281500d0440d20000e0035409000c07240e0425882d02015604841c0280c1d400107804036006241001c20b480c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 354987365 1250 354986115 354986141
    0x3031b030c030f06030b010b03070e030d27140103020c070e0c0403050d09030f0308090f060403031d07140907090b0d1406010302091011030c03040906060305100308070803070c0203010f 81
    0x46a5480010f00c03004560f25800000e21603010b040040c40891402000b5660200c0d07641040844041c590707001030314050464604a000410050903c40000642d54031940942e9002411850f0740b03041c003c601220195031203000b410103501003104002c0c00700810410700140306c1418600001e00300a1800c09080e03001d40000e07946482507848802c00c040c031402c14042141e0700070890000100f000e9404a591080c040c016030601e00c50f41145000700b0409110701c60040c7d00c280c030300003603520b10413103800714000c42c1c0940c035803403504184010020504d1807203004070b0f2130400311808842030352404400d40300042d03503401c6100d20242c01700340307960024401d9100e00c0100480c0154603c4a0355108011820b92084c02d0840d03030007812140840c12018010841c80c5100c02201b82a00d06084e0b0703000030701d491500254042100c1903141c010800c2103541600c034844d08811030300c0103240d0050030744d11040700c20b00c07800350014120f1200000103040a0301c1240c3c2e000566a00800078440300071301c0c00a0300050140000740e48 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 354988615 1250 354987365 354987371
    0x30f040b2d220c030209100306180209060a0506030a0905010e0a032a03200f16030b01080c030d11120408160509060d03030905010209030a0302150a090b1303031b030c03 74
    0x10140d208035072031407000c1d0f070001d5540c220700e080d035003840060070001d0450304024070540d8000c00003840d20301500d4a2280c030040c0301e5041140038010040d00f000043d040c1c0c0d00031503176003509000b00d40b291800c5951020320440007003040503291030314a006108100c00d103207942c0504c01c802010107900055000c440c0294070300c07058041c1880c201c9440f16244498004002c60005800ca41c00d040e900c1d0609504210000140d4264a002c541c101d414101e48000d101800b100d240c034240b08010503100b91501502c9414000d142c5040c07980c02003540c84c064134041206000125401c100454400c011907440c2d402104026901c50b0341e101d00c1c09a44180751141108414151000880c02d030400480d0345e441180000c1040d020b1100b1a14150b0041c05d03030b40c01c1625155000c22901c41c840e01e00704004900c4c00e1080e03005113103040d80380c0c880a5003008050680008503083c00d00c50008180c4850803160440c144040c1030764000c81500e0705a00504084404402454809608080d01034069002e138032281e00d192014 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 354989865 1250 354988615 354988651
    0x70f1403121f150309051914030903250f0902030a0e06091f0f060308030402100824010e03060c04180e0a080a1701080318030102030f040b2d 62
    0x2e000c8401c00101da440d11101e070960100f015049541070720011071824100011501003c0c0c8405040c0762440854a04405180309210104601000b00c00c861055030006075061030180000203440700848408181416005188548008a8254000000d00d1507000c2401c2c816911603058002e0342007250403980c201e00d800d619002004001c00e07100d10460001d40540079011002c040321201c000a8945116000e941d580c1c0000050b81c244200c90155018018054aa24140c4100034107071000d00c0402040002003002e210038045060500010700c8002400380700c04c055001d0048642102042c0d180d0780c1440341406202550745031100070020f640440800d02803000658100704d0a0f50842d074520b410175840030000c6008602c7d260080e000500c00c524002e10001c030b9000143e04510001e0f0012056074100140e409004582207240d0080305c0000d40c001e42c00c40c030384403012480c500401040075102000c0400010030700180800d0256109844211484042c1401184d001307146030202c0d00788505460440750 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 354991115 1250 354989865 354989881
    0x5070e030a02010804020111031c0605090c04030305030103080f09031b03060709030201021b040204030c08060109050a1e0e0f0304031a0609040c060c02040f02030f0a060b0406090b070f140312 84
    0x1c0c03554041e1a0030403242c496600444104aa07c202170542d03010500048950740b4010b920041000c02d45007001c40d100341490f0070812855070207014440300c14400c000400c0001d41010541e41141c2d0000c40c070a4565041c07004991061103020304099050081c1000311030044e10320340f490080d4032030a50860f8219503500c082a1064001d0b4040070340075901102c0d031040004070310308031045507100c090400740c12300d6030701d81c0e41c203c04140541001c40107800003401401014030341d20500358030000041c4140800d0445429140143e4100c00c40c9410f030380d4030741c000c40028410070025843d4520080d400c680e9140d40c0c034202054405048007070380800c852124045081440e0055052b4000c64001141c459980d01e0048165500048139004a801549461850190710400c1c03028500c0380f202d61649444500d0401c0786801110103607000410158018842440748540c481680410707105c004001c0fa0f42d52202d81028150040c4050f4010b2600c8401241c501203e14044041d00d41c881003142d0100c1d6503152960 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 354992365 1250 354991115 354991123
    0x1e1902010e03090f030712030804060b0d02060a030203092a150a05121003081b010b150306041e05010b1215181e070503070e091515120a05070e03 64
    0x24034041c00e6072090102d00118500308120340c281e00780060441c0c2015541c1d440b2400d800d40340000a0340800c80c8a010403090007102e01801000071301c1200c1c059410b00071540003950074060208000100359000c000109901010003501004608040449040c1c01281e40e010691000000c507040c00f0b00e00741c0194400c02800141520b4600c541c549880c1d0801e905002d0200b001103000300f003141001c076010800008201094010012180d6204007080005810301299003581d016491443c082c403120000c480600c01103909494001c2000c85004c00e01c8a420856030720928140b0100c2c908091404000045c840d010758010300d014295000445816621146451800c0300803a401c1508401843c03118074100700360807105903002d40761650960500e9410707590120206800c803624400710302c001083c001c20f1504400c1101280c5421501140c0030b10b017211480c022102100401c5004143c1c4680302d4600c400880256040c010070080350300124503010a819001c0e00050f200300e000704580304000507032414041 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 354993615 1250 354992365 354992381
    0xb0c0d03020f0405090601121407090b070c0e06040e120a02070b070804092d051b04060207050d23070306060b0c0607180f1412060118020703051e190201 67
    0x40c00107070403c0e20749010711241150040100b1704004100302c3d6041d04284905c10144003500d5008120510324000d54003412240c0250008112442c045c01141c3c001940460f44c1d805036420340e0768140391a215400400c010306180c0303690030604d000f055007101444081c0300250030122410350840358007d42d00c601711f40e01403161240140607994100014012020290050100c01300c0e2410641d01034101940ca452a480c40342585000031600c4005114607403004050050031900c0700300e059450310f807602070003941d10800c41c170801d03000320422811002480070b41c040c1900500c0421501c121000442c0060700d40b5030700c080c041115854078022000c0b41d08441035090b1041d4000314001400d04d0740f2144026100c0355030031a1907440010a841001c0ba0f8000034041d03d00c018440c02d11103001c400d4a202c00c10090410740301c2c81625507400000104030301da171075400c40b440d0b610080350010390300c402c281005c981d07510440d074800050b807408045004084140740020004114000284a10b04031142000c03802d841c5a0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 354994865 1250 354993615 354993637
    0x801030f0305030402030a060f020c010501153e060711070605040506091207090905010b090709030f05100507051c060501121d0105071106010617010605030c0d060b0c0d0302 76
    0x1031600000203000310011a0407500007822a6003d1009940d00010303a0f4491a40c110401e17000320305008013203803d0040d0780c003400364100d00070405040d003240142201004403000d4000341070050340c003000c41080025109030700c925090580c0c2c1000d4040805548003020b45010b000120007a001010002000c1000b0b81501d0465540e03500c1d01c1d203000c04000c400e0b0000240198000b00240200c0c403e42820400304008094408000c60080c0742820f24030301319040e9099840c001d607030a0742003003c4e82d40e0200104041d03e81c0b010041c0440c8004e405c019181c4442102d10b11300c46450041030020311600b140140141d000d0040420041b4161000707500151843c43c400c0760b010036041200d00748441c8080d00180c80110705401d04502c1c0b04c240680302400d5070301c160f072810041030814856440560007030080740d0262105040020b90242d10218840d40980c0500c91030342000004004603e00c0ca142c001190011159a901442000d4495070341480c954002189035940f8443d00c072034105824041e00a98070842e4803 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 354996115 1250 354994865 354994883
    0x150306060406030b040e1c090605090d060e03120703060e010b0c0627030708040603050f010e13060b0d0530030c09120610051c2102070b0403030507060c080103 70
    0xd4400243e010b04210b00ca12a4440e031556041d04105901304010b0005034801191040510f90400c1e010342070410581006003044400c2000c1e4007a80c0350140c00c4200168003a10000d2980c40418009045009003c140822a1500401d0110040c0e050b0841c400740d509912040143e030340c0c6c444680c24107110354059000c4a170000030001d05c0c074000c00c0f40b040d60000301e0401700740e040510074081141140d100740012282204045000c1c070015038140728482e889040b404950850754100350000350303003d100400c007104011424140070100302c640d800075003c0840c00b800e01c00c400d459529007a80c503582e4080140001c9080c070f05c01802c0c002d0b0806800780704811240000c6183d5198065401c50075480094015080b03991080000484001080054032440c00c0b00c100b054540d04000420200c000d001e5440d00c0c180e03020889190214480034203c5540c60a42200c030010a41011300586c245001340c0d1010070001c10202d0000300381a0040001c0011520030101000038503400c803001d4520040038000540f5200b0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 354997365 1250 354996115 354996119
    0x18010e1012090804080a080315100503040b040804050607030503071202030112110a0e0106021b01050703121a04020309010c11010e0304061812140607033803010e0604021503060604 79
    0x1e01903001814150041000340c0c030b0039440380006071900d00c240500700c50300a00042000180748104245095440d02181d40a0710901103980c01000b23400041c2c4054090b0400002050811218408441c0180805000d1503214005424090490f42084440780040345500d00130f054000302c00d200720b07810784003030078a0a46810110b803110100e014100b4440c0c1d4009000e880089254206200024020b0509a0040c000090840340d4510381d81408103602307060200c10300500300081c0e08401c104034600840600003d40401042400c0d242e0300d041602e59400c1440002401840a03040d0840000100d45d502c07000017a001c0162101d0803036030b00030540745240d042403005122244c40703501c0445000c0c0904101440382501c035068510003080302d140494600c0440c0d210401180300c1070103225407080b4942401c0244c107020120108040000f0440a5001d00340c90081211b240b82114040d180500090001c202c4c00804281155030342101743c90a0f4030500d5144032041d02448510120f0303104400251166003468 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 354998615 1250 354997365 354997397
    0x4110f13020a020c04020301080a2108060f0409060c0f0311190e03030d0c0e12030c060106320705120f0d020d09080304050a0303051008070e0702070b18010e10 70
    0x2d003011000300300314001c0c11400500c698a50024501a1003400c000e00581801c81c40c2c01000340b0106c058803030102440d0b0744031001c200e8002040640c01441a10210700c2c40300e148001500900d0b40e00030007000c2602d040204021668012410003401e0702d191020800300c16407203680407403809580c22050340e02007210266007000f8440c0c0307940b03103000c00c1c0581207030308282008100c0400e44099185810028501c03080742106450000580690402001c015600d00321b000c140c01c91b140c52050040704140481090042c07035540d10b0400c2007000c0d80d120031000b0796840107151f0f2007aa40c1c0c4425001d5445100d8010b509000301000c03c200e9030f090a00c4101c85260601000e00c0c840650001800031035a43d55844c030030004101000300035071140c2e00c500040d05540d1214076006e400c43e10060140030020b02c03141014442418005041425507840044a140943d15040124035088482e000040318030b03030100d04881e840c5a00201c1410500003621000c003903083c0340080c401c1c2074900140c040700184070f500700d0080703034 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 354999865 1250 354998615 354998617
    0x4020607020609130b090601030b030604030c02120f0102130f0b030109150b0d0e01060e0c040303030e01060801022205031f09020a170a110907020604080a03020702040f020304110f1302 81
    0x2503803018210a04020f29400003a0000c0040c482040e0030b25200c14600d0304921300810312603403010b000d090030440f00107040702007aa40c1500030801014002c45da40d0704c8040d940c03142114500c0e000b0003402c5501c0c000403040d41501030b4000b080301301c501900555001c680720074100c0640302900c0c803222800b402d40c0c2c6803c00120150640c43c592000280c01c8410224509407084000d05c42901d50107800f040440c4440405400c54803651700142c8200040310230310504020040489040381d8162a0100362244203001150042045034400002581300040748028001d03040c941e1048403c0401c2a003044694070400d264868000f00340d10910300b02000070f05018807282307601c030206540c005021041840c1c3c641030341060710107003040c04115941c0306450b03076810001c03144943d2212203c00d031802482401c0c000380103942e5006c0540010048040407410908540c801d1341559150340d0000d1091150302a1030002000070751044d10300f80e490002046000300c450628200701c403102003003c4d12012080f88030030099402 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 355001115 1250 354999865 354999877
    0x803040605030f0c0d05040f0318050102060604020912070e1e090601180f0c030e0111071e1407091a03161814010902130509041e030e03030a23070209040206 69
    0xc501c0c0600c405e0948070054890340b0f02c151b02c600a80354510807581006407440100141022040003019814080350342d012502d2500503505840150311904044006411401198913451091040400009056840820b00343c0202a54410a180c5120b40d00000700001c804842002242d8442001009100491106e444a4010031400060400c1400e84140190744605a8030303030001e07482e10a513401102c428882d504c0031842460a0034a091816903540740341d0203c42c1401c03844103e40286080921007503e00000e08400420b00341c0d0f0f0050303240d01c84800203141c015040c00e115900c1c1c00840303900d42400129500b00303400c0b42c969494145d103010000303460052000b05042525440d8008141040a541c8069019104c8440c0150b00c1e10710003103062490b0100f961040c2d119051240c06d210200b02d082d500d01c02c0c91800c3c0581406107280500701545c1002111403001c1c1c052200103981c00d5401d6020301d81c0324001c841c0d22084004151f40e002001c081d03000d5200060f50081c80d410114006280150041203 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 355002365 1250 355001115 355001131
    0x305070f0c03081b030f041209080c0402031f060c120807080a1d100b0f04020f1e04030f0b04060506060301061d03070305010908040626070c0609021e0102070803040605030f 76
    0x104090845513450510f40041d900603034a00403032400e00042104101800c4002c903100c0c900050380701e150140780e41d608c2c0d01542c01c103030049900002195170030038040241d042010380300750f078485096901c2600405c0154110320903940c0001044d13031210314030700c81e001301c0d4050602a91504415250058050000e000b0041039151118400d0482d0480e6001408005428060030800281441200044c0b200340740c0910022441684108010f0300c0f01b0380903400351105002c1800d504095a06c0d090050787d494070483d04003a121551a0784074a0822070345084d000e109600c2188140000d84858080c0f1010b800203020703a1001c9400c00025030180082c1d10001c12130000024101e50710f141d600c1d00c0702c81c21251441c50a8a12000c000740600480b1f400520528426a0714010140303408100c58201c0c0c04c885002d880c01040007131036400002405402d42102c0c0c42d00340c000b81000d80218283c10760030400e91003e0001400b5008120000482850200076901118400e8990914551b115642c007081d080340104908 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 355003615 1250 355002365 355002391
    0x11040e01210507081e0102030603120d0207080711040e0105040203060a0207030309021002031312031b02040f05090303011419050f0d050601031506090e0a031b0503120103030305070f0c0308 83
    0x350202d8420050300c3d0003008074401900d8000700c00354000040581c41240745040d40c0c010001d0084da0380700018901c0c5a8090031240070344805000c1440d80c0a48a0000701521100b004a100002e01c121120b0032008803404070340400101c0b5002d0703255801c0e5902160065810b4000000003140403049030001d103451031003460000f5080340143d00052503130450b0880b02c0c3c0181d0020074000306d10101d00c114034000e41190400104616002d58009141c03052004462800b541030a403010b0840d01c0e0b0344c0114000816800d0148091302d040a62180d5a030402d214509803c0e1201c14081218240b2035140c008001d141c0d244400140c0c10701e01407250103140e4601d0a50042c48400c507120200380301f841114040c41c401c41400c1c0060740014060015214a6004240840e24100380030014200009908141a03414100f038525600c113800010150070541c08068014000014048010300f100e2402d0350699119840070005070322512400ca4541d61401414400708540c4090000440d0080d00d40ea980a6140c44400c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 355004865 1250 355003615 355003679
    0x31a0117151b090a0305010203071b051f0f02180a0906140f0d08070503130506040b0a0f02100e0619020405061602030c0a060f08010b031b0f0c01060602070911040e01 73
    0xb00341808885da105540a07540403041c8417031a0b9014031498a03000b40729615842481c003a481d11503d03078543c3e000107040145001b1050800e2106034204104503010360b40700315150380c0400d8111500d81c1c52460711502c1003c0c141da02080b0f180d0b0512411058440c451548608100c4007001d1001403204c521016600c00e014100d150002804d0350001e164280c4100e02454484d0070000d00b25142c0c502c0d03a00103034407460040c0010310081051700241c03482401c9500d4000035014074203200741c2c100036044541d40500d600b8540c00d80b0301010002000c40c001c1c4840349844e240038510031000c404a0180740034041e4082020490440340341c43c254100b1040900080a582c10041040001058083d0550015011401816541034070304c0d0003100c09401011355000140ca1440c1c2490a1107104050078448400f0140100f5045d000c51080c4044c0c0d40711204a0000300410380d19032401a41d190b200d0b106000c01603042134001100c0e10302d40c000751011180810030060407642000a41c1e800c002c3c04c0c503245601240d0007041 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 355006115 1250 355004865 355004869
    0xa020105100f03030c1e15060501050f0a05070f0b0a0608060606070302190c270b0f012a02030a0803011701060317030406090f030306140402070f110604031a0117151b09 74
    0x41000024411220305803071004400c1d1203800d8802c1c51b44158103000c400e12044036036503008400c83e370740401030f46401e0f030f501d482a1400e001e0340010b100000d4050b159401c1086907501540e0720403425591048106e0300d1940d910303c10406140325442c8010010303040032880e052458400030000c98181d101b240e07608015526180c0807070b41c4290300c1000003221540e00040038102225481040c80c40c450aa03540c0c81e02694100c0003a052105170300300602c40c0d041130600440f007082255034026000350f00a0075241004582e0a101c5400e410a014242c2c01d0304180e1640750502c08144240c0d82140e50003240c141002509010403e0183c000034400e403170494032100c03000002504a0550a04a07101c3d440c009005400c1070400d4045d2070009103142c0c05280f04108000108046e8008291210340c4000c00c0110403a4600c0412050301403584006c140c4c00e40420800406000894100d061307032a0075076140607034076048110719500c4220021041e0042d0120010900c600080b00c0802e0a0035142e2275030724079006020340 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 355007365 1250 355006115 355006163
    0xf02061e07080717071a090c0303030c18030d081f18140a14190b0604080114100311010e030102162d0512160b07050a020105100f03030c 60
    0x10741200c8400c030001c0c0703910802441c2206021840c00c071541050070500d142d56495400364401c44180403d4a0510024003910710400c02c0c0d4071400805001d990312418103c0d40c82880742c00460b081c00240441d80c449000d41c1c00c1c001aa01000400c69903a903501e510703140002007180000820600d50300c201c0d010b0104024075403207040c0038174100e10540011342e204100640070040401030f011099107424511031002d41d11454000c44d400100940030150f0420501d102100240084640c2a412902c04100000c0784441036000c8840141d50541d00c10031603490b00e41c0303032010005c1c50000030041c5980103800b00c09544200e1141d5560f0001038001494400c009082036401a15902c0460b023241c140080000c210840801c0210310381360101d0710040000256440c0e680304c46c000c000400c91a01e002c500008007850140e6a44200d0350400746003000382c01c0812001300a82d00c8105080055130814000c1446426056030f04000c849400b0501d240f0142140c0d01120712000c0010291080341800c500d03078224880e111 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 355008615 1250 355007365 355007377
    0x8160209040b090f0304060c021e0405010803040e0a02190e120601090c1b0b011503021606020c1515060f0408060703060609081501030b1f0b0a090509040f02061e 71
    0x520702c501c0902d0602d00940ca044880000702149400c244010403107030350030502c4042c1941d81140c00921001015480d522008955170328280e00a0410000048840002c0001e02c01d495020849201d039542d4144900241e200d002c100341d458040c2054405c11852003018108515000140f80031654129492070324581042038120849565949005020280e0018110b01500e1603012400e01c2c00301c03094503040001381d014440d9a024180e200980c0040360f00c21f5040b03075081e50071400055004403407410000020740055691000911800070349058081c070f0840860301c545000c2d050885070324094010310040da0042c0b00c801d18000d90602003c070b803804060003038610614140d0760008050303290000081c0501010780c0021419005111164003501c1c5858070141544d030021071000e5652a04103084c00c00e0303500110846454844240b01095560300e000c003c003841a51a50341d440070fa03454a041244c480c400ba14000d2407000010071200050a045001d0281d41c1c500c99207999050250710a903c0250f4800 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 355009865 1250 355008615 355008623
    0x30c0c0605160b070c0b09010614010e2112070b0402010e0f0d06020d02070812061c051b0a0e10030c08150a05040f1e03080a1b031a0d030908070b030408070816020904 73
    0x6500138007001940a46031407072b01c131007480c4c220301400b007200200b1440c50440c1d0b480e8001d060300a0740b0b4546010200243c4041d42c0c0c003180c1c429039644a07800c0201d443c05040e1003c81c0040c00c160900e0421b450808101d44032024000c040c0351000100d45e07240c030000e501003c83e001c1f00c183c00340000e03001f080c400d20117003040501c840c1c500a4a0b01e408010084050740e110130b071101d45c1144110300e502107040028480d075080d604821038000c0c4550040050042c40066100040442c007240810000e02184007000086a10a0251550050b140c08180b52210103d240d1184000001000030310f01071751070b03004030360880c0c0a03007070001400c8a0760700c42003d000c030504034415001c59101c541c0010542d01c1495907601c410303443c2c1d003080300b40458182c07900c80c02481102c0208254807055201d000f441c02d00d51002303002d100102940542a503525015024004903c20b403420340c042c6103800100c011242d82101d11855111800f103151102c0b07036039000540d801151804098100e40c400c0c180040e19091200f50095000e = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 355011115 1250 355009865 355009871
    0x31e100f0b030d1403280207200a08190809090405030318010204120b07020129120d0807110a06050708150f010f1103090d030c0c0605160b070c0b0901 66
    0x410050500e058001000d4004106a0415000c404d1010700c068981000d503001710b10040100195110a07030f0940d55035215445840020094104128800f00351650102006800501c0403c54104400140148100e01003a040100c5a4211040103e0001c60941c4100899030908000d200840c900202c100c504072441c1e4000000c2c81a000d29640601c04e524a182c4c0003075152904100701c0c29403c03011000018100b0601c9030106107214000e402440702113000b041c2c48000c2e00280c929040d51160142911401000c1b080e400e8a003a20002c01c02254040c2240c5801c607150711042002c03125207a03c3e10300180140501143d2000045c544c1c01081d002d00300d640d803408010304010808403180907035101c2030f42c451140402042d200740d801c000e001042610303078100380c07418182c12070360070f8158072035404042d60008a54a0708800c040d0841609028a4010408a5980c6840c4d020507901c034407414480c1084100d042c0843c0c0001040f0110b030715488811441d00703076110040c680e0b46107102e030020383d004000380e51 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 355012365 1250 355011115 355011131
    0xd050f030408060c04081c1b05010c0f0201050114220e0601060e04090209390a1806120b010302070204050406050f0604020406050f07030201060e091f0506031e100f 72
    0x300310b9035404c00241e80419107406c1c5001d040c01e507100303441c0b10500c003156040d850341c45040b8060064458400e21004c0001031030052490458000c00d0400c0c3c024020406200400d42810b02c1482a0340c103079103007503c008a6200d148010066242840c0760340500104c81c510383c000c0c3e0908c050040c120036009107001840103504204015103248081c0c48803130b001d981b0340400315003d66264160309400107101c2d09210444c989032803128003000044000388003090062100540c42ca80c0300c0c0000e01e041c9000e81e845920b4411030f4600780b809030615101d1000062200102c83c0019641940080900d80c014100185405059400b04003958411201a540d40d41d0390000c0083c2d0b4884c09034443da00ca5401c46045140078200b207406081ca000f2444101e203800380110362001018004d42c0718101400c104000b0448a1912000d5035035a0303d45280092014000c0a01e55004065640200c60181070010301070725180c2c6810b203148802042c2c07a0011000c074440d9204110f03c4c0d80c43d51003074204034a030380348000c10b074a1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 355013615 1250 355012365 355012379
    0x509090f160e0105041a04051012080d050c0c12130e0106080a060501030209030717030403020d0803100e06010e060a0e09090c01020601080307020d170c011a1c080a0e0d050f0304 78
    0x2c05a100c1c501071420800803082080700380704200e0360030b03d080360002956244d40f000f002d010019900b01240c1c0b2480d900240c410301894070f01a001c1d61080315000e00c19035031038210508060159659440441d8480780b2480242c45088000d050b0b10b0600d440d4582c03d00da03840204141c10102a8011808503030000148103500c081c40c00b5201c064002030905500d006d1105000c41c1d5940414030610aa042103110010300e42002841180e00554000f050345841c841d050070090711540c01074550343c1c10704405c0040050b18000261a41c2e100d584141c4948065000d690180101382e80701540803402c0003c601c40c003e1780d40d95558a510f018100311002454a80c0d0000700191134114103811407034032035009100b0800160760340c0f1020302680e54048141d40d0b05000d10782015080e40680305803801d5035401d00004040c0d82c101c0240181d490682100c9000c2030800c0e000301030703040190302c0d04042e00d0800c00300020084e150060b0300903801584041c080c0741101046441d494101014400c0340c261036000010200010 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 355014865 1250 355013615 355013639
    0x1e030f0d0b18071b05060105010c020103060504090308061206150402091f0806041109060a0f170717010e0f0601202505010203041404091109090106080618070509090f16 74
    0x145404204451900356161a0717141e603214144500c604215083c3c10403404c6900c00c0d0080001804007800912a0070b040b0718010f03004403401c5800500510f4000c00904004a0001e0518000d0460408641455010100b8017002c0c1d4040044150040030680380084034050013460300c044050959100d4070301d42006403c1006554041d10b04060421003406401d41d1541c0d01303802c40d401c0020ba0b040c15481c10603401e100341c4103200c008040908401911040008080d042400e1151028140b060003509a0300c8402c680c811444c03e86214000c00009400184154080c2d0172614640100701140000c0c00e2000256a01d048200303040b403106043c90001c0701080040004581d4060842400074500781400c1c05100510742c203518880e14071907901d4600c8d1500340318501001c0340706450044d10344141880d040325400d010b0803a910908140b4440c850000380006000035890495904400141403518607003c1040051503000c0e00d9403c0f01d0080c00035040400b101080350351000302c10410800b003960b01d442554006 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 355016115 1250 355014865 355014887
    0x32c1c050609032502010309080d05091c020604030309020a15051b0d020a030c230a03090f060e091b0a0818060f0403031503020a090207051e030f0d0b1807 68
    0x6582c2c8103014040008442400e144840700502e814030f60b1500c138600040700505070712180075049150024582e040d1503855045944201c4008080315034100201c412244440d0100c00c800005030071800205000034031941080032210b0000701203000329925001e06040401c010110742d00030400000e1100340100300e0103000742602010340003404500800303170030203912030101d104010100490f40100f0301c1005611105821f41c1c1c4c4000342c1513450550303004945541c800350b0750030540120f804000d0029200c1c1d20b000b41003068403109d50740c1c1050400500c00b40850b01d00d019240b609a144944818500a40e900f40507000064165951180d00d0628060807071420060a101001d070390130560070084403500f841039950300305038145000102d00224201a99180700c48d500001d6000e0300c0c0e003a00081d20349054000d414a24041c000303640712001d0030f208010040b248a6070840144d0010300c07540301e4014000000d4421040e010401090401c80038000603552100c3e4004a610010a0310034055901d9101345001d40c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 355017365 1250 355016115 355016131
    0x18150c120507020712030201090b040f020301150b18060f07030905090a0501080604290f150d0f0803070c060204150906020307020f1926060601020a032c1c0506 70
    0x9800d210740020741303d800d24061401e403020724940360010580300350b0000c81c442e5004060007130319080c68586086142e0180310160f100c0d6003040c600400504000c81d0000845001c1158585020b0006101d515510000483d02e0f61200c0188429202150724034003c0461314401c1d640c2c81c05444c1807108100464002504140150346840b006103c414000200310350441e4101e0036a51f400c151640701004044010170725034810b00761450078001845243e0610385d001c2c1c0007203a0086802c1518005114400c581d105024200303907180d18044000c11507410045810015502d40358810909030344501c0281c0c0c0c40350340308c1003541507206010242d00380d01040500103002e83d071010b1403504049400091110b0391600a0600c01e2401c4483c42050030a80620840144001040407510706a40300688120580104250125004580c006031a962002c9800490035906803204400207010090094021181c15400004880484001c00c1142d4841e181d4003802401149117100d03592051910900345103000c1c0c8866 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 355018615 1250 355017365 355017371
    0x60d0803010905061c030c030302031009020c0c041d03032412030c150f0a11090d030801081e030a030c0905121b06030115140d02070b010e0106020303010f0918150c12 73
    0x11000941c01f01303654005030b030145005600c030384803030019401101c15030b44a480518800141004001c00125540f152103030300300e404014000501d10310210030001c5454803205034104100143c0d50031480344250310001c54110180b20b4100c141c3c1c000c500d14801c034090002c072340d81c4041400012003504102c190b03d0480e50039031900c0c42e42030a0065041c141e5001e4040d0505544601d0420740c19a074038405d441c07044000500140000501c0e0501802698081c041c172101d81c0143e100c4d40c11035403021805090f980300d02400039032030001500001c40040c49410610801c0205400000646603900d0301031409614030302d8050b24201040342152018501d8017400c040c020f070028001008a010840c400311080000740c10a84807030440180710300030780d206101914100d18408105101400400f80841c1d058a41c151000300a50342c90b13040a9aa03800300348220101c29400304800c0c0401c6049812403180d90b14002c40910511100d0f5503190400780c00100300280b541c2d581c03003c02da030950b4130405102003d08480410 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 355019865 1250 355018615 355018669
    0x70803090901060309050a15060810060e0402090912120f1f05040207081303081b01020702060d090203031306030507020127060c09090507030203010311030d08010e060d080301090506 80
    0x7041488105200741c9040c5540d5007010f105100040c001007891903400b010250b00300036005000401402ca9000310282807050305080481a100391141c1c0054601c011030152480d078603a0b082082d1041c0c0140148014021240c42030886807000000e0300004000c0d41000481c1c3c41c190044c46643c11005140c0d4003003a010700c5c0b484c400c4c1500c869681c016101d050b00c001d0380d101c0c1b603070500d40781d10310503406122049047e0003800018800400c02070001141c070100301102d607114081c40c5609034010b03010b010354421010031440035080c056910003140e0b1813000e0b081d20304002000c04103c00442c059030088000c641c680040140d51503080c800c4602e601d442003a1030624030b582016620a83d01c000c14010034203540c91401c02d02a40c01011a2001000c03410028030851908200040c0a90800e1108845011b8031a24210140c030700403501040d0110195a5124181e18011000f10180070107000c59030400c44034149140801d140170700031800b90481a00224042c1420f03800e100b41550f07600c840d01c05082000d280 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 355021115 1250 355019865 355019869
    0x7060c110a1214090a0b12060603040b0105040b040b1905150c06010b13030807050c01080106110a0b0a0b060c06010e0604020c070905060307090c170615091e04050108030c07080309 79
    0x403802c0301c0000c5160036030100d1084900c100052041c001c0440c0c0c4401c014000044420164004045842150101c2c9080b51501c200380603c6020555009000c0f141c140c00502c40c42c181a401b04101010083c400702c2c0c540c0000f40804c0484964007040c04c0078003040c0ca0180514106404094014030b6540c06035481c01101a40160f101e030018043c88080100014880c001800c1c41c1500c03002454025072640c0c1d94030b0303151904039544c014141f43d2a01040c900d070000030344a4011840ae21603011340c20081e0160030060b5442c2c0c10389020003050395425541c2c6582010680e2a044060601c51469100a0100303504006003604024801003500b889240100034003440200c012130044111a2074040101d510b44071003000a0603c00503406c924484c500e01070040883e99031154a00003440c2a220512046858000c04d000f14140302d00d59402c3c0e01c20041220512b14102014a125101d0341e0000720001c2c1c00054001400b582d10a9202d644250300214441c00c100c03030184120b0004000702401945010582c00c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 355022365 1250 355021115 355021133
    0x1920060c090405150901060c110108060105120703060b03010906050a0905130f0f050d080712291c0b06030d020601061b050f07061805010c0f0212100207060c110a 71
    0x301c0c0034007698851001c0754016100613400c0210700e4009003009215038403030000030242e007072140040d545404500c02e0b000705540211829400b485069584030328003164503000c07507120b00c1c1c0501100101955210001510481040618068000003801040e42490301040100306020341c0c010a480520306002d02006071801803500c2c1401d60300800340b008507241424a102c9824841d07201030518080d104039402001d0780301110a1080c0e99688405404c0f0100554030000c81c0d03200b088035030741616030302240c4442901000d090710030007400030261680d0304000040480080c0300e00c01c04a4098450b03000340107041ca0300303011285d10045070b031004209961400600401c074240050311505142440441c6a00340001800001035080781e810071241d846a45000051402a00450802d1840d12160000c00c4641c031aa149c249a42c0d00a01c0450444005400300a02100b41e42200390540c8100480b17490141c3c007900180c280743d07005210009103a03d20002c0a010540f607a4074982258200d980c600c00040c101c01 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 355023615 1250 355022365 355022377
    0xa1403010b0d0c021903050a140304050d050c0c0a0801060906051801120305090414040203100905100507091802040306050c03270705150c1002091e061920060c 70
    0x4400f00340404052001c1e1304000c4070040d24806200f0800d4040d0038150410014044240c10b230b994060300c0e47e610304040515000c19103004015800410507401158403540140821081100a450700041c2c094000b542460f00c41d400009503945496003001005440d1040c0001401d06481e0a40c080900b451501102d09050186e00c0c0741d000398503061800e151060b07080d1508254084d0003007004041040403105144011a8100e119214442c08400c400c0350f81c1c020140e0f01a0b1010080001c48003081c814009060010700880400c41c03c448006610141c800b0072200b00300d41c461005944c6c82c1035081c00c2d003d0b540c0080610516010800c01c0c00480034005000c0c51900d8200c0f8080454500c04519113400d0508540c001a40900c2140320f208290003101c00400e000d220f44000c80b024408005c81c1003048e401100c031055401182e40740684030240760185040d142001c014040c81c509160500714810402d05509110009402c65542c0c0d00b0170b51680d0901c008445020b4020b0045140c0800c7c00c0c6103600c100c07 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 355024865 1250 355023615 355023637
    0x501050d09031202030c0d0e0f0d031d0106060807020d0516020409151b11010e0601051c1e050c1906031a03100e060a05040305161e03050a1403010b 65
    0x1942100c0c145445644803041e0f44010079425543c030b090400d9040210b0300f04060300b281c150724003407449404c41b40001c3c00000c080507000140290440d48081074008105164844c41d0107807094151581c80032003803088101074440398907094600d0519000003480c00c031400202d4000c0c0304040040c245851070821643c280b00ba0b0440300820f1070300b000d203010740081d4440c201140c98a41000c120080b103100c50701d100300d0341c40078a40d10780d0300070480c01d5252800e0700d030b907051007140d0364010318018442c5d8140318025290300300e0700780c140c02c2c0035100e40d0380c0c2d460784640414455036450f00c80e850b50f0010003c0071302c100550040210341640850031200c24004c504c002d103120780018141c0d20b400c9031010303941c40c140820261500030241d81c40f9480d0b403484580035280c201c1401c14140950400100c0b25401c1c1d11a4030301885e0103030b48003410120500c00e2642130b040552f42c252440c240c80128008400921070301000da0b0742c800d660321038480045040c0a007188600340032003400f0344008e0006102024440301603841c01c42c83c3d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 355026115 1250 355024865 355024871
    0x209040602030a23010503210301060804140d09050a050405100506090a0909080d051303021510091a01081012060209010e0307170d0c03050a1d030a030908010b03070501050d 76
    0xc41d0f107090002c11118548092036500d81301c0202003001800d00450490300c0507030944043c0c1c002c142c1002800b0310303100300c1801000401d000500c100d0f48203025a940c002d12541c031070400d003403203031522500d8041448030343c0b00000d59149080c0841e04055803064000e1809480a0090f81840c2203925001800c0f401828019180170031080365507a40d00c0c406030000d0030198005c1007507800d141030000547d8083d91032000d285003400c02144903040c13400d95140140c0d0b015400303403c00040c20402c20341f1848024080c10501d001c40c038404228414030340306281c4507a4880700301501d07405210f400580525801000b10302e48444c40d1404116010240c1040e5100c0d0350b014500603550401840107980c1c050103080701c50b03010b10a0308804a89480d050601207160b4013481d00310303010220008800c640d8249651001000034800303102109005000f03a0000240c8011012450309035101d4001081c07810f26146410b9002541080003000070240038400d14050000540c01340120a060800103001380c411104034004c8665 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 355027365 1250 355026115 355026121
    0x20909040212071a03010e090c03030d0c050d05271c0c0204020714100615090b03040f020616060f0606050405190906030c06030f06140f03030403060e0d0207080a020904060203 77
    0x20107014040203454407070f03281c1d0042807130003000c020b03150000d000700b9031130b1025240440c00303e04d0001a480103809000300214a04803a64807000041e100355549441400014003200040d0b10182c050b280c170542c0d80300a451010007034041032028074a132505c203907003094000840220309003100c140c844298841c1030030700c2ca5504106101180003403007480c4029084480c1c4410a86900c070700490b01c0400d810f401c4d032003440304036100c42200c3c1601d40003924010109400314010005042c0b034101855129014181120f5182d26640106020b07038080c548080c800e4400003005030810500e40b00e030285070990710000b0405079041035805003082c400c03030194501c28a040b25040000340e5180d0704181c09004a00e0701072040d01d80c3d0f46022080e8203403900444000c0703804c183c2d00e42042c200074070401007203a8001844144501d0304400b0301c01c1e0290507c6012750540001c00001c4082121800355210300181d0f80004c00d14212421002400d00340740e40c00c117076041d8101c0c40c0041c0141e6901c20300079400070381101c00140c0e40d031 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 355028615 1250 355027365 355027399
    0x608070b03240a05220c211b030c0210110a030e070b041703040807060c0309060503062121031512030d0b0409051c0e01030e1504061d1c030209090402 66
    0x502c1c45d44084801508118080c40c88a42c0301c0360203100c8429018805c860080002561410707901200c1110f403100020a03203074808240311b034000814080e09401960b0580142995200a58250a004100c2d402c0002000740c5590b0f8540b14140c0f080d0010300c0074014050a0810021040c4290b10401407404090713000606a58024001c4900402d280012964801c1c0c4e10b0001402e4052012002d0300450b14180d03000680d00d000703c044034440d0000034022000344000203105c54400c110f00040500e140302d040b4500201401d85541a10303607214101d8101e441e4605080500d11032540c400d90b103402411035a00300b050703801e000000c3d6200a20000008a12100d203030010500400760724101900502c1008501c0d808400c440c481ca100b17000c0c0c55524034440008c184015030550f4400110800c00f43d100030f41c918441020008429001446080040f50f40c00e00aa40d4405c00294440d42c000c0030340180540f424540519a00c18014000c5400e0070b50408019500042e4010001080030380280240f81e58a0b20903 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 355029865 1250 355028615 355028659
    0x2120f0301030818101211071a0a110a0c20011b060f060303030b10030e0a0201080c0d020a090e0a050105092701020a0201020d06120203031c0608070b03240a05 70
    0x80e0054105880c0c050410001040d400001d1602500c107458400d498103001c124008032488c003a005030200ca100034014004003105500100080b801950303c408490303078012000000c0000340001d694030480c00300d143c280380b40d000514140c22001ca403165402da2626036000b070544c81c7c41d424000c50300e00d648260f034182070b4003a02c00040d00c1049185400804410150585e0151100341c106443c040401856a4800d408980f080791501d2382c640d01c01c4c003c4800562203400005e0380815000b015130309003c0c1c128604016600003103038800101d040c00b00c003408085603207a480d0368070a0040d0307414003281d45013101041c0500d9010b03115907491404040481003005d803003502101040d00313500c0215503030143c03000028000d4201b0084500c0803403c000700000e00b0146402035414440c3c008028515006049085038004000e80140c100c6e441c1d2641e100003038400b0103000da41300522440a01907500c0c0f51444450100c00400310850311b1040c0805100e045a03250710003040e080d9034041d1515a01c004004d034000e015 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 355031115 1250 355029865 355029907
    0x1d070903080d23061e011803030804051c091205032208070f031a13050601091d06040f080c01060302040e01060614070503031f08010c03060602120f03010308 69
    0x360180041d481000001c2ca601490700351407001c070600c200440c40c0c1421842d250341511083d601c4030800103000032580568910310703803c1c1c00c1410091740c41000820b8114030240d4960095001c143c4075020001031010a00c200031090020202d0030f8511003a002010b40002a54015007884003000640b003810002c041040303c1035609003940039151f0f44401020008401524041c81c0668041c030040001c0c107140d056581070580398006040c216040b043c00d040780f000c11004198003401c18114281801141c0300b8406c00d4087c1840e44000701d44d50000c402003900394500c00504010035404102008080380c44940721a015940c424842650b03402247d80d814094081c036080079600501c0c103190000700d580154008811943d1a840343e0355180245c0c0c460413944e00410300040d00b150410000200ca9011503407519492412060b00d400995840d44050790860780c800312002e010075a02d880600030345804120300c480110315003110303928141c1d0303030320b54080c40c0e01041c40010080140403c9402c1121760700b243d0801 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 355032365 1250 355031115 355031123
    0x1116110a080f010501060315140d050c0901030506040203150105010e130b130b09060312040b2b2009060a0806060d0e06010303170609010e04031e210203011d070903 72
    0x5000c034011400700f8000c042c20f00c581c2010a10f0007202440c50070904000c1d100b00e40301e04030004482020b81d0140003104022280071240707402807140c243c515546d44107225002c0d40c040c10081c812483c052041c10303c0c01d200704d0322510824920300700401c456a17000031280c40c058000c0d2800e26802c0ca111a080d401381c018404c401d07601c19801103511902a8003540700130440034003201c1c5240f0369200c000a243d01c0e210720803c4864a404200f00030b1100c9082c4030010a50348010701c00b0b403001c4141802110544600b1600c0000340700c6d40310b05191148010201c2c5420000c0004030b885031900204400141e07903445072100345014000c10f100042c801d1341d101c00c20303030b4010360100c3d006001802040110070744508007404100c020410001c010700c940c0d00d141301441c1c4104070240070441c141e401d1401010102d10010021020031800c0841000c110703040103d0075204062607280c08003043c05100c2c4100442081ca002c4a59030340c818070042001d001d0303904601c00803241e028030b008225243c08604079448031240e04054 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 355033615 1250 355032365 355032373
    0x408090d0f0c1d0f06090c131a0306040e010c2a150e0f0120090d0c0e01050406050d0c1214010e0303071209120e01180314011116110a08 60
    0xa003c02940910b0101d41d001c41d01c0301006a6500904454034400c1604d8068001403885e0001d140c02e20400010540c003480104050206a901d00001c2d4000803400c200030144000402030000904290050350032199080c0700910441c860080014242d004120003c2d103000030203001507003d0300041c10b02e0a071041c3c12602c0c07a0866085003d84601400b80f980e00c00c0c2280c4101d14140c0011401882101c2d030202030a000901d48000141510240740c12019007158040500101e400c002894000396400801a04150741240d42c94841080200c940650103d805550041c29042c00101103090050a0340c0e454014030b10b0b001e540f0b0501d25013121100302144a690b282c1650510003d000002562007800319507500100f03000f403a50700d14269000c200c00203216400c099031002d5a40c1c01041070f655480010300d13010f40c2e00865111660110541b40e44140c80411001042d8940d142081c000d40704920b0151030ba081c41c2022000320342c42c3c8a040050043e020704484001280700d035454022501c003c2440004603 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 355034865 1250 355033615 355033619
    0xc0d0603080a02061e0403120b09090c0a0602160b0c0c06160b070c05032a030406080f0c030108120a030f0f1d070605040905060a0504020c07090f050408090d0f0c 71
    0x611a80d5010150040c054031540000942c50105c2445000031400203200c40071694840d0fa500307484096441030704540c0c00740c46410010749500c414015070300c560781c110000c001d040c80010602c02540201c0e000003007190000008140c1c00b4030008000c908464405104656800b1400d0401d410202c0c08074000c3d074070000005039800d240d60340d0300c80c04403960b0060b582d03c8040d840b415000c0e600c0f00c81e1480e0051030794000780302500281d484600314100440514401e01604840000c1c06411580150014004600d00340140909030200ca030480e070303201a414024624550420b605682e4840607148c80a041b07501c000741c4a43e046210360042098841241014032201703001100001c040c101010020001000b07075683c0c6500f29000241000032a80d29480e6507182500b82400b81000d050300a0001c0e0308800078800021710b41e107840c8028105002141c0103051100e04007005c900c19561290658440c550034002032001289605044541d22001150652100d250511b805a880d850a082c09001e1284040b00 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 355035971 1106 355034865 355034873
    0x5010c12090506030117071202010212070606030602032502011a1014030f1006090302010203250c0f08101505010c150216020f0d1a0c0d0603 62
    0x4244040d2540b001c00c2d02c80c0d0080e845810b1855030240b0600301c3c0101401405e01515410051070b01d005241d400003951500007020090450000180c5082007200c180c0c88100190340c4010300395200d1408628020070000d241c5622030f161014a0b814406803413042c031880c103400c2c4031001170a0101c1151350a0041518400024205000c0711914255081c050040910b105042d5400804401e01d00340107080d58541e4140c3c00328090003446141440140c0c0c002c010340c3c0180740407000540e0a9814200d580850030000c0e82e000e04668a02c58000c1843c0b5445072400e4242e4510504860305040520a04012034103000801c8880d180d40d50340a000d00d6108100401599004410080c145d81d04072104400f207a01040046486150b40000b85e02103040c4030a01c81c001d80e0741100d07407040080342c94403028861030642000f48001d61002c000510042c0c10b11080da400d052100c142004403036104d140c = true := by decide +kernel

theorem cover : BRFrame.Cov 354856115 355035971 := by
  have h0 := BRFrame.cov_init 354856115
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354856115 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 354856115 ≤ n) (h2 : n < 355035971) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
