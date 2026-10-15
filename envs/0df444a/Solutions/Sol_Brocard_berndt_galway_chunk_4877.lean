-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4877
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:01:48.301011+00:00
-- url     : https://prove2.me/submissions/59d749f4-6bc9-4a39-8339-6da68486fc8f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 876978417 ≤ n < 877158273 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 876979667 1250 876978417 876978433
    0x30203091c0803010e2205100516021c020109082109030a0503041b050616050d020a0c09051005060d05010302012606010804030e0a08010506040509011b1b0222050604020309 76
    0xa180200c01c402010101032181b001840444802c2d0700071507403101030044001e0960703d0340020704030064820152440320700344682a01100040e83c0442c5181c03006105400b8044443d10800d0228090032680700040d1010b24001241c24012004e00f21200c00304141d010710a0603561500b032007076100d00406007400049902040003400090008041e0000d4901c0c003509940d500d0b0315103020515542100d404880700c1c1d244031810700d05000d01040121481c114902c010002000c075943d68062202162050200321500c076804128022849820a0f000d84006405151186c00c9440b4002c082d040a201c05c3c0c1c0031440e0100086c0c0c0d4541c0310313540c3c000b0448900c60048a144c88420045501d1540140141c0800001019949590707407038040d2036008111100002ca4141007810802c400c030307400a80b040c002070303242c104c01407600c1c03600b040ba68114072914140043c466800c1141d02c0582c4907001c4009600c001250304d201ca0031801c1d15503051600d08031388003c20036655134009000881c801920300603683d80c00480 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 876980917 1250 876979667 876979679
    0x112b09080a0308041e1b150509060d0f0504080703090b03100b0d06090203090a1a0f0c0c030c24061504050d150e0d0f03090c12030507020d030203091c080301 69
    0x10b0714036005441140c003550044001d005c0d04a40860001e0100e652008000c0841038030b02e400ea1000c07024180c0ea61085801c00300c1d44030b0140441c8074000b24180906030100b081c00086e0780d550f020551103d2012414841ca00c4c081c03805461a50050070704801149144030f01040c0c000d44030040d030b4814840b8074840c07150b03503040003d844084c0c0c0008407080041e079140c1901181e0804c03e400654041e2014400800c940011841d180c801e8444165400020401950070003202071201040c258100400400c01959000c12501d410f05612529107020f02c0b9100d1000d0900d00740c44d103a00e0a41c041c4807d5012401991114000c220f1032024460900103120824841804031b883c207001c0701d00809110b8040446840b50415820055403507060100c0390b02d403c01d1b0124a1895001060008075010929041085601503915100e000f01d0702e000e080c014510035184031040502440c101d403481500102120b001f00000d00e8001d5595004e11050340c015080c0d01081340350350503490b600b43c80443e4050315040c156070802e2 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 876982167 1250 876980917 876980927
    0xd061d0a051003060f020702040c09150507110f1c0b0106030f0c020d03050a0b0d060b030d0c08030708061201330506070b0c04031709030d05030114090403112b09080a03 74
    0x44041d1a05c25070030001c036030050b036641c450305229580c2a100c2c0d49145150503203003e00c03c80c130300c3c641030203019003001003200003081000c500ca03c80a08680c6501c1d2003405101003118905410000d02e00c00d414131030034000344801c03505074604807407040d60b05005d41c44421440c0c8043e107641d44e1074040940c0c0301010000000740607401081e4080d410080005a0003150310004060844007401038502c1030387c0d59010901402c0c207120b0141c0d02c407440c1c208080038140310354a800031480000c1403a010000340101041440e03807a14100030f6211070000082c0302080028502844915030fa8044800c103201d12806007420621445600d02200c0f00180013501308403584d00d903420518002440844454820000440090000d03c800c021020351050300e00d480b091040145450800c2441d00e8006020302031004200002450b0804400c2130015160740c0e0180e00c40b4030b819542480d2810048005006044002440b42030440c4070303050041007481d5041c10040001d4041c1d50711031883c005c0c8081a000b2106140100303001d4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 876983417 1250 876982167 876982181
    0xb030a0f0302100c03020702090a060e0408030a0902090702010213050a0b0a0509030307021824100e0409080301120b0c0a020705010507080415080609060a050102210d061d0a05100306 80
    0x28015600880c079010303264003c484d07580301c0100100f075000c1000c0055007094a0020750202c80140c1c100f212500740f13841107607400f900400007442c03154000000303040c112807038005103245507010302614118140044080d02039040146002c0f01002880340c001242e00c1c000543c60215054044074500d0558041c1003110710303038072542d01c082c2c044c40704004440c01030302c407c00030701500507802c520302903203061000c2c3da141e410402a0760804c0340c40d600e444070746d401d0303880b6200c20b0f05280160602c0700c000d4058001203000390070902c10161500501100004801c081c02d0000707602644505010200303650b0b54198001d1074003d0705002c50050b4882e5200b0310495010b50000c0c5441c6000b03041d41401c0580d5800400304818803544540d000405610520115060070105180c004104a0782260700a05142c0001d41d0703040d43d42090013440a0440e406141d10a1140c02c513248498009002c3c0103040d25040e503030141c170980d03454a090100410000035442c0a151203100d008802140107844410300e1a11020090701d51 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 876984667 1250 876983417 876983423
    0x20403030324030816060e1002040e0906040507060f0e0406031b2309180304330f03051305060411010806010f0c0b04080c03370203030a110408121c0b030a0f 69
    0x250f00503200c0100ca0803c02c23058a10110003001da951800c20f5140c000480015011a005074004005d000001c2c00101e29902a191285000e5a1300e00b001502107403502c010300a0780c0c1e00686840b1011007400b050200d9940d103074440010448a42e035444410308505070410b816400103000452105580e40784c1501100e800450303070380000b25039024003200981154003903842074640d88816545040390010801e0000400a0940c80795a40c801d07403400c0203040081c6c62601e10301016964400980c4007c1c0c64400240c07480d03040740031100300745401c0c502040120091041503003c2402c0340c000a40942c8592980d0712110b4682e960b0700e0080c150742c0d45640111038098000c070790885041c0681d0401030f1081020708a9050101c00203400101e81c4c0d1010794183d020843c0403080d44c40c4001900006540000484e904810800c00010b8140c1d0441d120308000cac040c0703400a2980340a940d03144142802200082d06c0c00e1580300340b060340e003c0c0c2040c0040045500000c0c0c0503426810204150021540041c400880790380 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 876985917 1250 876984667 876984671
    0x3060903031e0b030c060918180d080f0c2701120c3b0906060d09032109020a0608130c0f0305060907050303041e030602040303032403081606 62
    0xb410718140c001c800b6009603501407060742c40f1068003280c03804015604000c5025260f20386015107101c082040004801c10a5801e004260007240254034050304040000091704103a440000481400800105043c1c41500808078100c01048148c860001240c0350740040c0b03100540184000c5000d0503041c074100701e01c24180a1201c038007854a11450061500c0c0380c80701d40c1c0e64075103c84850b284108000240300403d0307130358074481d50058600e130107104000d100f11401c603603542c4030b80d45100000721207100c0d1829161003e0b041501d10410035400c240c11030b6010b1131000b44509003e0750021143c00300d500300a4082e5024803000400c1000c103000340c06098120400e2000d4400b01d81450300d0300c2e5900103080d44104821981000d080090100c1408196003024101014018207494400040c4c0e072406140100707070111940d0490310820001e8000031100540c0e0002d410f6441c1c6039a400c000d0018a401c0f007500812001d81c034000d51035442002e0700030050340c1d031100c0481d082c80300e2211481d4800742d20443c03c4514035 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 876987167 1250 876985917 876985931
    0x105070f1118010e09121e070501020a030203090f010e03121f0609090e032a031306030902041407200c03031603030b031209040c0e0409050706020d090f0306090303 72
    0x515442110b061421050108201c29458101802c0201c60028020310031a0041c1e1465000c0d880741c0021101d12041c0390b4040018021006c4030b6041c60701c0382a030000d001b984001101c040c11070300354010350b01c40c10600059030f1200c50410a55400c0c0c58150341942607580040014680f0300c1c409406140c4c11020150800000c00e8128003411820001d541240001c10920101040b481c0ca060052100b640320031006107051150071a0840c55000d041502d203001100100c4124400380070400070760f414095602d10340d01c045543d41c90054024040b24a0580c012403d14016501d02420f02c00e001c0d00030711a6544000c803d016264070170001c1d100c42e010240d124013458065403600c0d0b80030800b07041002c90b52508404000c40c40c1c5000780c1282c0a14050a020340c0040000f400020b144506607111040180c801183c0302d5402501240d60740d154110039503000345040040c80921070002180000e4800e19021185200744580c01a02c100b180b52007100c04896004c1401d2000540d9074118124061013418013045034 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 876988417 1250 876987167 876987169
    0x1c030207060f05092205130b040f500c10030e07030515010e041703060406030b010b070c0b092404080a210804020105070f0311030301090f0f0203060105070f11 70
    0x50695204000e00f4501c00d0100c00540480300e02c502a0080f2407c1e0a00c1014920341d03654002c0b103440207001030700e41d804004054017800101d9081c00701070280050840161503000c07000c6119450b88060000520244190300e840d8522046141080e8803440d100034019030018204100340d5444401440c010191212120490100c00700580c1002e90b22070405030902401f0180301036840c3c10b05a011000382ca4091050101040520101210307114600d003030695240e4501d004a0089c00c800c3d48001c02d100c0b000740002404070201406401205d2240b0003a1100540e10b1100d8001ca0080134401d55201c9410800c407111b10350301d6208130740403541c6241010704056586000504080c8009420b4400801d1264062113408214040c0112071f40c2c0e0b800c18101c44e00f00303500001c0107030007040c0009240d400c03601c040900341402000095501c0a69400f1281e5075a161000c0718080c00101c4800304039075040143c44012024a8004c1d0384c45030342d0603074905080605549034103681850070b150a44046560ba0280222 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 876989667 1250 876988417 876988429
    0x71d0a09020c250311090a1b0c150b1e040603050f0c1002030406020703061d1c02010c02010603021804081306020a17070f02061e0d0b1c030207060f0509 67
    0x40e1415040944083d4041c480d5a018212285480340103090951034103200051464189000c85c082c1903d5030903003030346e98090a40c0184203130756840b000703241c2d202e10041000e039002c00340c0b400c40c0b481291085801c443c0c0b140304006440840c0078003035010415440c040079015205240580116006001268040d81d03a140c00d4281180d405440700303981c00c0310030b00034014100b09495140c0c0c02e0310391008520701441c0600003910b03105075000080c981340d10340164410041c401c011058610540c5001c0d40d0400d150001030070081c0d032a0905080140d403c1105003180f050040c0706000031030340c02900700490410025001181d081c1d004004507180c0030140f0008a007540c9004d0b10b0030141c10350b078000749110403039424001a8496182c0b1118900202080f010740040c000403a1400d69a07416245a5124603041118400c0c0309001382d440f40f01c1c20300224107000c00318400c0c0c000018459059a2820b6002c1e50b01484860720007a08070080c0c0545c1c080081008401d00c00d22070030391209140e02d461414a5401c10009031 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 876990917 1250 876989667 876989677
    0x90102120a05160c080d09030504090c170903070b010e0402010219050f070b041202010e360702070602030316020c0a1203021b011b0203010204030b010b0304060e0303071d0a0902 78
    0x1c40155140100800d07589039500402d902c40e0581018034444005a40d03007441c0e4410954403101c21a1510341034020580620309132805403074240b100303002503401a14001c0101c41444140b02007095941c0c04240200c20200449490680201068845a0030094000c48120010380128114031800d03802c2c103000e180c614080c0508074070440241041d003c0e14040c0510740078140d00420010030703081004109003542c0b000c81140d0590b0a00742003100036640c0c000200e01c00c800c10034584010602d0104140d1001002038140744003c0070000300051500c03000000c036030b0344029002e4803002d640104041003240c003141034800c0031080c0c00c5c4106ca9003e21010007003203c00d107a0340c0c800c80c14444201e41480805805110307401154218000400c16038480302c000074034000d90540480c1c480120382c0d00b48429501e007074044034059030b00036221080c107580d64202c1b826151700459040c0d40444c50075108049072480441128000e0203d540c40700444041c0301c03194401807800038144c580c800d03c2503000040705115800942 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 876992167 1250 876990917 876990931
    0xa0611250b06010e011d040e06070201090501060b040b04030f1401020f1213020105031801110f0c07080a08030402130b0d060b04060602120d0e1603050703060b12060c0309010212 78
    0x240903910302a15441000b81c20181032080018101c19980d92111414403c45462030003030300003840140c00306008109006511900703014081c1000344940d015089a4560342c0314100800416a40d080f8500580c01f46000b07603044071400300300030800703d09020a5120a1401042174040c0220004035643c00c990050340110035801021840041c03206040328610340c0f103c09014a140201d48940c0000e11610008101d440611a003403a42c1e50044400d40c0107051241c1c0703201c1016039071640030003e40a180c01003954400341d4401c000010440003c045084e41c0c009a200000e9801c584482e0308100450b424002614411682c6803018002c84e52031000c0140034500840000814882d80410300c001c1d110560040710555011000c111641c0303020800300c03a1030190030400050f030303140500c0c2d440b414131203c03a510302c154006000c40401440030200b442401c0b640300d1a001c1090500307820a2242103c60034961418070b4010100103601041850700550b0b2080c6d9a60006250211011500340c0c0c0410644502c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 876993417 1250 876992167 876992227
    0x2a0506071101200a1101081807260a05072c01060302360901050609130c091e081603081803030904061d060904050d2303010e1014030a0611 61
    0x3c0312070750b00000c00d140c0102c0e03103800b0750f504402541031103649d40c681407094102800b65404035010880340407442031049003409099400280042c24400c3ea9004507010715013606000007a005003c150500310003030905402c02307410ba1039030b00e0800160000d40021580882526102040302c1d014608801010034004000c800303443d808017107a00f0320400000507000039006000c20007912040f1b43e600d103900e0043c60210300012a1081c0b24a000703d411034090b0340600d100b0303251440e802c4071603545071031900d080e07400350300803181c0c0015244540846603090b48005419050100700340801440f04020030800c080001c1c1c2101e01d08202000843d0880d181070303002c4100c210003125408286029240c1080c0c002c1d404070358558407800d1035181c290b1034511003600c201c18444082003461032074880f41c0e20180c2c3e04156100c40c07a01c940e0f4403103101480e10011100300c0000c41061801284044a81000c1d000529010340145200c03e03207a915903000f02030004400c51601014460100c144584034100c003000c0e40c0303414032 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 876994667 1250 876993417 876993443
    0xf040f080a1101110a1b030501050c030a05060910030813171b03070308220b0a091706010e070e0d12030204032003031c092a0506071101200a 62
    0x754001c2c2e0400940604211310000104103008002502d1344006800440c0815400c0120700c1383c1071044082d520080c1513500b000c00304030041d00d0340390213584030f0b20224409009503503402e0f0803c030b00c182080382da09030900300e004428004602d915010f0056070040c0810108000d84401c2c02e00141c0d41d0800c4004401c0d44080802041d1114040c180141403800340d0040003107500b181e0790210035014541c1158007a028044510740c00c14541c400c0715004159400302d0542e10892032000502801090150f80d03c0b01050005810402c48005100d504a8015005420803616110b0b01154141d803a0041da41d402410140324001190340315800e40c1c15038140f40c030016a12891407420590050500c0710500c040f01003da0003150341d407008002c8034047c107620b004045201555200001c0100095a000f41880b00c00b0581d03d040002d240d203c1c6500040e40b0f4850380c0003035503540204580b034816450f00410f080c00404001180e540110003c0c485602c17a00340d00000f174249880702510b80011132505460b40e01c0310644c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 876995917 1250 876994667 876994673
    0x1e07080f07230d110313140109120b01031131140a14010608010f0e0406021c06050103060909032a0b040501020310050a030206030f06011e0504090e0a020907050f040f080a 75
    0x15000140550401c0138501b01080c09040100720511481a4580420401690031240e072190340e8000107003000c1d4041d03030004c0324075040c1850b07c0a403d0100310745040101c4c03000515032514a0071514450224060022403c961605000c1110104180000050b4450395102030403622103034414410130310b440002130209407103007e041c030020060f4003d8050000d20380041c0070303d000c04140d4009480700070f60651016120362600303400910070b20340f064030301d060201d07140c21a24a0036007283c1c044500903a01400904e8840d9424011100901d0b802808100e00d00941c02e52212074070751640c01681c2d18110806000c50a032911341e1a8101100c0c06c40e002d940c00410064110740c4484043c002c0c00043c3c0300302034614115400724546110242c0386902192550000490030783c411140780c2440300142031420142c01003030030080c0160300319000d042c0b100c0b810007040303580c070300c00c00100c0440113a001050403016480fa04401d950545c0040165003400f041003001081910514100c0030060401000402007003000d81 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 876997167 1250 876995917 876995927
    0x130c0f293006010806180403141803010f0b180915040302030703020f06070f0e0f100302070303111e0d0f02280f020607031a0306010b1e07080f07230d 66
    0x70b20481c14894060305121030b0381c40b44182c20002c51200c41311880107488604003554a1030410071a480021000582588484140d64906140e11001d80080c81403102d00101d25058500025403143c11446503100c49083d82401e1800540003580c100a0344c094820100304079508641c111020f60260b03100003004070406074108141031558101d14081c001504000c900240354030f08850494041040303d2101d4121684c40e03d004404500009055200071600388101038040d4100c2c0c2c2040e03021a252a81084429103510203c131045482c000701860750b04400b000d185025008654680c1d0060f9aa01910884000e80d10042603a103a00316013401210b21900350354850001c0040070300341041134890107200e00a40004041c0d41103d40ca003000b00b030002c8094041034003424903050035170341071050400005a072a0340d10010300c24405441030f42d4400c2401201c2803030503440303400d07030083c07402204001102c40405801c0252200901c54001400310b104d9900500c40a01d408104685c40341c1c02c60080040102d03001 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 876998417 1250 876997167 876997171
    0x304060e1003020a050901030c030b0a03050d030c020a02030d03050405031605160b0903072606161e021b0d02130501090b0a030506011202040212130c0f2930 69
    0x40c5020f40c42c24180c0b450050003030194554803418940c40e2458114024007903000481200c0c0060030740c200c102d40e04d04100d80d40704402c01b0300c000400d1a25455285007840414030b180c9254019004241002d03102c141207005000091042e9241c0c0028411070544150900d112064180200c0090a152140b2140328881c0740541d40002c5040004110b4a1442e44003c166001112110200100c011404122000d81842d148040e2500c90081e00100801d5202c0d0310507520100c42940d80303e40c001d0122101d146100ca500c0b50950000d07a0007404059110901344061448000010b04403000389540784e404544061300908901f95810348910050104011602c61741420754001c41d51a03401e2403464a900b510303444180030b0b800340d1040e5907080354113640305ca4048960341c00700c402148005107002040220035840f0080e040382c1c03421407140002441e51031089000103403011520a000c01c03071b0740e500f180c81c4141c16803001401a040140030051420001c180f4001300211201058480d446410710103040503040 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 876999667 1250 876998417 876998449
    0xc0503100c120504230c040e01060f06170a0c02100207030807121a041a03031b0d08040b0f040302070306061401080f010303050a050d14010303210e1209120304060e 72
    0x107000c00304004120f0414507802c1d00e0040b403411340507402c5e50400d00750a000030983d0340c0390068201b0042c510089015401401147c1e01e00c9144038123940c44ea803084074688406820b101c82205140c000c034802c080c203076001c5201d40015004482040e5002440d2000f40e80040b03c00b9004134007a601007140b0560042c40c8a0601480170204102202042c4010348031440d03c0d440c0103014903620082c03550040301400b00221000c1c001401c0700c2d207524540031103039400b0507801110f070f18500074100b8001c20180151100340c061644440351162913561000a0390300100d00600980c00c511402000101090140c03080901420300000805100300c13032080050207150b4007070100380700300071203c00400201b54064142d903000c2c841c91a0580e030701e05041c503242c400381c0f0038800b104080c511000000030405402100030302c4844000280c07461120211400f5104450b9410324045058000010000e0503003192002000d00c3e03034002f803000030310303c90b03140200d89107812580102000c12004c60700d50382107203001d000307404103854 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 877000917 1250 876999667 876999671
    0xc01050702010b061927030212030705060103020d30030b010e030c040b01050d02040b040905220b06130513021c200409050d0c02090106090e040b040c0503100c12 71
    0x1080b020884a1240c5c01000c4016081085117040f024401c03841c4503140220942c4003010840400d48200d00e441c01807000324443c0220950441185402209580030340d07130403501400f10340e03195030240980301604680440300d101240b401c1c40c0b2242211814244103002607014580140310760300f409001c0702c81d0b111044d13061101403d407600c89c69400065480c1d5500058602194198540300142c2e03590003810310919006001190210b0400013480280040b201000b200740140d80300c5080c000941000a06080c0d2004c2c206034940000c1041c004038075030080d0026003600c44203861082244104d40e8203451082c110050701905000390301d04640744055104407403d200c14900c1c0b0b590b0340d100032001c8441c000c07103408804107080c1c840c035605d40d8007419204c5c0c0c00c00c080c1d0b200d00c2d85000c0014890001e40c1c408a1151500400215096100b4600312096031003802013400240c581ea1103074214079400400844801386a004003064540702482144180e501e40078000c101c0170030f041ca003d00a44e100003c0c1d5072001e4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 877002167 1250 877000917 877000931
    0x250c11010215151c060c1d062a031b0f0622170d0c03050f0601020c13021b0717010c0c02130b031f0b093d03080c0105070201 55
    0x41c544000e90704a142d00103003108510000001c101c148071003140c460b11402d9140203110500c030170f0390007261000c502e507542d0800b2402540e8641a0000100c442645c1001051040d200145100c6000c2207103182d204506003100841c481c00b861a5a00803c8070754500c0c3e00c040044a94034070100002041d182e02480648040d2130181e4812010001400b1003091243d001034481003406803590881d00c441480c500715642d13400300c2c0440c40e0058103203203019400280c60034000070f00184000b102ca5020713100580c06842c02c00401c0c410400c42c81749207d40307480455820800c1e0310650403454058084895050050a021072500150728822000710b42e04410341e0341000c84040140c2d5020700c0c062802a412914000e40ca0a04400e0380d0041120400868040c0300e040c0c010030500c0c82001c1c1c0744c410802100410b102080e040018030a2510f401e89039400c00b800c01c2581e40c040046000f03481441d502403407803005c003d08003803442d0040c80d0070940e1003a1041200007031060380340182030081a03803001c2207000038040b030 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 877003417 1250 877002167 877002193
    0x1020c1009110d08070501090308070818030a05071b14010f0c02030d0809100c0305060a05040608030a030e10091104061d0601050d020909011d100b040e250c110102 72
    0x502c800303010042c42001da151454081103824016541495044002081805030034500036010400a950000c0821907481c00510340b1111100c007048406000b00207141401800c0342c0a581e01c0e00300d0481186e203a0304485603a890201448100f0000781864400c03901380e40c00e12800901140c14a80c11801000704640c02c080240c6c400183c00660840036160000e1560340d488541401c11401c41e0b043e001d2a400c119803015415890740005008000440325052250344d00e00c104400c8402c0ca20551085410602200c0300250182c1d00c01100948510251010103089411034011a04c40840c100c82412801500d10014142486510007a0500e680c103c45e40500700c07605028110002031590b41002000aa00300040825030141e0303950007406442c0c54100d503101d0750380c20800307076400000010381c071000c40014161303540d810552802c0718080e0304000d103014184913406c07074400310040624005801003180c0f150039280f400381c0001418116036030b403001d08a85203860504d60b0704900700c09046510811100c040 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 877004667 1250 877003417 877003433
    0xb0304050c010c020105120a151d01090518060703090303140603060a0b0f03160801112b15120b09061905040f02060f04080f060c160c05060c01020c1009 67
    0x1040409003003214200c0d503e440102c0d407500c90070b00401070b843c08000901001c680142c00181241d0b000c00a03034000a0b0310340000c081c03000c9000d0b50101d1034101001c0100302a031025444140c011080d0004062146000032207546040e000741c4040d00002e54070301015050503454420710038240080b401802d0765042040009590306409028050010b035035a5000384242e507507100d10b461828003e001d070f800664400e86030403c022800d1082d29142e50a001030301400f603003180201c4902010b401803500003808194850080e06070385002014140c1c0e5a007403120b8500d50030706084801841501890120100185441c03038881201500d210003e90200d401e215a10085c0c454440f0744030880c001c001030a03583e034244104a1030143d00081c0d001000020380014090449000b44240d030207034000c480c1038000c154810b6507141d00880b02000814010301c0080700070400f94840350441c80c0903891340e080712a110b00c0002c00b60750080f05030080582d030009041c504000140085000b40f402c0e88030800008480f03890b4022 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 877005917 1250 877004667 877004683
    0x1b0403030806010309020406080c1801060c080310030501152405041707170606030706081e2a0405041103060d02211005150f0307031e140a020a0b030405 67
    0x10a0003801c00000e21544d110342e000461440d002041444556035420b440f5460301680711415014030044007030000300c200070159060485015545000c1d0525280c2c503107507034582015100042d408045000040030900034011301c88414039801500905a2518091102001201841c005001d100c84554074016420100f030b10304943d0002401d1022a444046240c1400c005401c00203101d540b0300301c4881e14040020f46984207034001d804407540180c540c0000c0d54904803c0718003651714580c03a0250b10455800d14030140e040704080040140840f49003148c0140a5611899140a02804101048186403a00680c5800318503107542078070314108180030403a810140c840190080c90703d144c0402001808100d03c00003a1803107416981e021810720b0440028020a542508070071116400f0402c072807030004003a40c4108401402484030a28691710280105888412015606060301c84580811484009840000c9196002c2c02506425204100c0329004039000740c0030542050081000240c000101d4013 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 877007167 1250 877005917 877005923
    0xb0a0302100305060d12031d150a2f0301030606051e040b0a03020306091005070905031e03071a0402030106061d0123160c0e09030708090a12060902090601033b0105100e1b0403 77
    0x4258bc00c0a244d081d03d109100070468400c1d405080209003440c60707a400a54140d80c0308a07010301c09950303a9810090070180300800070300000341040461040d85400d03807000000781c001510341802d45030f6980009061150032980c0944a8101c4810f15030288203600c5a40c1d03100c0d5442c1004e4581c281083c010941d03864405280040310780140e5051500030600304190313450b06901a030101302496110603001c02c1204203a8040340290f0a0072808140d0602a150000381030141c030b803c20202401000c011101070b40c80300e400000342030504042c2c07442c1e6070782000180701400c42d9010310f900400c00b0345420b0840b003440354000c00d400f0140d070f420721200003008070454500035000300c011602d0302046000240b603c0610f90140c0d106540c2003007030404100040d0001d064050084910b03070304581d110340040d41510290034251604d03040060900c00c01c2c2c401410b010136030132100c40c05440c888800000c02401c6800540f58100205d011541c01c120f984161900268020030700c040c02d110040360200d61500da4003680c0401 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 877008417 1250 877007167 877007171
    0x3150126100b031602010c02010212040b101a0703120e120c01020931090201091a0c06040c03140c100503092a01030b0a0302100305060d12031d150a 65
    0x10038000d502680058002d042c00b0000982da904142030282c400c5007407548008050750034109800c240600620030344007803461131174540b170256480703030780315081d001004001d0700b0840300440020506c05074100741d107200c000c1e4590180f552110a808c002d040b00c08101e40302d80582d1300300703030310310501c4031020403034600190030927480c140c95400c410085400381c0603a1410a410403070355409040600c042102e8010050b40c1c90740d0708442414204506000d440e50350f140a0302044c142c8504010004c2e542e4018404807142d800000d041900100c400c1c1d013025000ea4090798070801d041c4007401401460b47c1c0b842480050040180300d030140030404520010603503440e4000303205000c400160b04210134005d2032803000010a80c6042c038040068001c00c3c403c001244540020300c4c2049030b0610707060000c800816680c0007414081c032604000002c41c0038181c0100344607048803d900c000800aa15030000a88906081c0c030040f4485034688194040400c04400b00d5550b40d014003100110482d24111598100c100c880c00 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 877009667 1250 877008417 877008421
    0x50d030e010c0b0708010501120e060402060d060909110a050102060702121602060706060602120408100e03040518040506070f08150339030304060503070e04060b0a030203150126 78
    0x42c0ea04500300100905030800c994200b00031503070300c5011107060310341c240c0780c2c3c22032540035030807250848420041400c0d107603225101040140c40c001026019030307904a41c010400b1078840300310303401395030640004503900d00c861406c07a8640d103403420b10305014020a10041aa620342100d0007517495084019040346e0b02d10000d88840100400864402466001303400c203507843c000e038174101c030003080305100b1403005010300250725104010550031070301110312403001403c0300300480d5110002848684502e1040c0d1004200000d86a220840840304003580c20f01da00e000f91519003001814207200a0907030080207008000c2c5241c0541212482d80c110708180c40000444070740c03030082860b004030300b045091840180c2880300510810402c1c009070b644912904401020401803d06a481c0514010702010940a000080d8014840d0001c22076400000740081001c690750500340d4150f0340540701d00d50010b9000020440300c4800b65091101e038590030328001402c004020458241c00c41c0720000c07200812450304c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 877010917 1250 877009667 877009669
    0x60c030a02070206040b030906091b19151d04051b0702010c020306130212120403140c0a0e0f18030f09040f050f01061b0312230709090f0501050d030e 66
    0x705a403051980500030558803a01d41c9801030940d00201c0380d258251041200042d400b49000c00d030007150b03811081001c5035400781e9204200a41160300007101604440020018002e1118280790b14504455103030580d40016841c0d40034454101e502c40725004600340418044000a80c104441c02082440c04464a0313820301d100498071012086800387d030511442040c4010b1b070640c900c0b03078240e0a108403005010103502103520b075101c0d09030108040466606100420111310420046040a0407880940310000e00d00800504861703035079044145a0341d8a001046400c03214400c409401c0100340b04603100c030080c0c7c03038a030507a40e00c200b10076030784a8940400c2038601601c4a0304441000da10481d814006494059a0307240514824850280001c501c5855851081901e490303e01c030641e01581d6580d10040b0305d18151001d001581e40021840c407403541d0380f0f501051560551070040d100c0d41e42c0c180e002490300f4111010307100c0420124907944d16140041109a0320071040c1f13094564141001208100c100d4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 877012167 1250 877010917 877010921
    0x306010c120e0a09060f05040911010305041e050a031418060906040e130201090b030f040b15060703090806062209020105160303020a1206051008040c0f0608090705060903060c030a 79
    0xb86590088040d01d03021030090ba46400c81d2040c0c50380540c26200c00c0e6500c40030882503c5000030040c0c41071007458082c40665119402550703229000b10155281c9070106c041002660000d80c8090341d098200b055404c0800d41d005590301060000050380505000e54140f0745101c00c2140443c5920595000403442259207488080e200204000c540c000b80038070340450103003034000040e030342280010f908400c0415601000313420342c2c0c0112031b03103291700006961740c3c2e4507040380c030350301900101c1c965103c501c12080c80d944001c000c100740c1c2d12070360b6034588440c60583e81070b240ca070001d040d0a00c6900c0085220504a0008080108403040107201082407901800140d60620030304240c160390b20340214500003450b415800411039000181e46110140c48014600c1040f03a0b15409000d500c0803032404103102542c410302c0600d80082c080d003403280c0e850b43d0302c1c04880501e40d0954460004110b1181c02c00c829a00103200d614010a1305035a01440c001000f00081c0d1144002030448001c400b001c800718003121041d03 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 877013417 1250 877012167 877012187
    0x60a0e1908040801063501110a0e0405090c1005130306142202130504020f0a080d090f080d0f14130e090109050615010c1709010f0201020306010c12 65
    0x800000c140034209091003210755016010342c1082c1d600b425030005038203807070058003100301c1c1c002d51003540e500f41000c401051540c03101c03d00da1055900c031071a03400400100c100400c1e00480300c0d192031900d6070426051209a8800a0085a113a0000d8980510035200e109001000415910f800d644d143d000100d02a48080c1035000034280a140904c4803010520030744a0901403441000c480d000c6010400b0510301c14119260002d40129500510803405038440e000b164200d88002d2207001c2c4800b840010036030482c503a52110500d40d0089807851140c0d5009807402010f4440b000e00c40c0416401c210900b6034400325040702c00300704940201c65481c518800c00200584101c0088201c0e51900007030310045240d060350242c0d141c283c41103008a941c000c0305200ea00d20325940000507001c82d81d144100b51613a0381600414a060007241d640710380010f1124151200d2084008901c2f5031507920300d000041509980c44800c400350780c810014405260f0f0005c0c2c20168a65028201440719004a2402c560790115 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 877014667 1250 877013417 877013443
    0x120706050d0e12220b03010815070c0f150f0b06040e0714071109090f100b0a030c090509060c03101413020c0a1203063b130b0106090602060a0e 63
    0x8030701c00c00044444c003602040f0031031803a903040c0c11545400655221344000e00c01d40b10a0f078099600005442000e00510f94040e00ca030400001410345611400180d24108000711a450210040380380d0304101440388103240b42d149001040881e440d4008201b041c4600d000d14203600002c840040e003040d108200d0380d81ca00840a1540743c5604a070f1900002c2d24801080d810700c00d0555078005440300b640080c000c0c00300703c0e2500c000c04410b0302c0c0300c103040300401e20240c640750000d000d5040800881c003503c2061000380100c0000003100c0c580741101500780b40e8007401d0f402c0f00c25070030800c1c45800307500380c413080d02078030140383d02c8080038210140000d14061444c900f5404150000c03c160480c00d0000c01c00c4280c0c5030091310340e0520286203100480c00c9412600035890142c1d83ea90000c3d03440c2d042040d000516510010784048030317030952800d030024960115400c50700d610000035508208882044540e0041000d814440300017807c0c01d00280d01c0c0c40d40140300740c3c1090383c1c800d10380c5401042005070b4011818 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 877015917 1250 877014667 877014703
    0xf160b0d05061242041212020c06011d040506040b281b021c0804020d0b0115230307030e070509160809030c0c0105070c0f0e06120706050d0e 62
    0x14003807035403c01c400150041c200f101310420560440b210800182940085011070014400303550300e54400400c60521544002044031010444480442502c010300d680c50f6583e00074101580b5001405144010714100c1c8100200c0030b009000000d03c0000b0003e4000794440d0500c0940d0791590424450108104840d844110008210800d075082c0395000d0010b2445981411031086807005050303036034400002e280c0a250842c5c080342e1003194441c103c8190007030702c0140760284102280d02e0301c1d40d84030002e8001c400c401000d1a82c1581c07a9030400080e140d8941041c4e001c0c0c000804100c416529800010207400c01d141c0c4602600c4080c3d202405000080c10740280713208054240b048040514203070183e00c0d140444c1110012a840f01c0d8004103841c6581407000c0200081641c6c43e004607900e4114400464840c004514085410304681000c0d0300500301c840225655464141c08020b41310496449910b1280c00166007400303056880f0381152112959100080340d210b07000c10606142041644071000004 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 877017167 1250 877015917 877015933
    0x7080c192d0302100e030f030f06190317030403051b070812040503071215020418060b1606050c0904050408091801060f0c03090909050f160b0d050612 66
    0x408100445191491440c00100054409440000c0725400c1c032003001c0d001d644507241e000107074a400d80001214021407001d4a0030021040d0040880382c00c00e9440141c00c03405c500c1000150b041440540f400700c414000c07540e4a25241d6252424007030005021a002c01c1070010005040c10f02800c221009041240707030040c0741401d9644440c2d140d0741d403401080268007401c10740d46039649880040e20191403000780604101c0786403a00c5101c200c403031001c0840e44940c144841d640300707003214400f0700014035400b01d0202200d0001c0342c11030202d038040d80050342484002d0007851019101d1084c400805030740903d00050311b03240c0c000003000c1401a01c5103298428105410802041209006041c005d042607860f8100040e0400605500c217000b4041d07200000c080040704e00b050b40c81542c0101c0c0580c001c0c00e109110030348808204c402d4520305501610030fa07006c10042c0c21690020480241c0010f0003121098590b07051004400c500c3c82503002c4401c2d604c3d100d074081071345680e60301c1000c41c100301180202c1e1004 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 877018417 1250 877017167 877017173
    0xa0b0303071104050a02040302060f1e030106020607020c010518280306060e0c040b03240d050c010f0302040810091505070801030b13080d0207050a082d0f07080c19 72
    0x102c0c0980308640110304000c04644a107416000b6502541d40c000d0006003000c1403c81030000c2f540010005c0c441040c00f40064115801c0140011030107829194050b010a281414010f880c000c40e00796401d040210801003d0103031003c055450940b407104549000c104405208418442003042c0034403011207110040c00410000c0f150700030400c07202c2000e00c054070b544e986905210540524418080c042c02c0800c001a070000720016100000700c110204a03c203551160013180360501052811144c9502c48040e0300e5940d038100000350a41c44062a007546001c3c18454025201d5450160b0304011580794070900c810020880000300d00c6a400510400051800c1c040043c00c040c02844140c6105100301c02103113141c0e001c2070713038004c0e0f046d0010f00c11842d01e240c030f4540c50001d40c4100e03829105401000c0701e0400140149c0700800941c0d042a2205012600b861280d1410308800c001503260468104460171051031020251682150056883ca0b110100702d40301c02c0c02c0200344101000404a114624020 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 877019667 1250 877018417 877018433
    0x60415020a210801080a0f02091008010609140a0e1c0507060e030a1704240b090f1906150807090906240320090d14060f0c07030c03080a0b030307 64
    0x7503865243c1c1d4146584c1daa800d031807070b1200b24040018005c000b500446da400b42c140aa107c2d90450020303a10701c500c41c5d07a0750445500f101c0850f00184446a290800600110b005110303890b0480000301c410421204610080d66481c14030074019204e0700700c0d040c4e80a11480c010420b0f2000c4680000052080b466031074802d503102d51082c40d200780030540f2005410000144105050f1140380e0040e800040a0b0707850140b004001d1001d001c40d9507240c0c454600d481310791961542d10f80540b040075086581c078100381c0500401c0002c01e22035a03904c1d80c94003100300440500f003201075844000500b0700203407640b034008088410f0a0705400c05482070f41040700004203405020301100382c0c92209062042c41a001190031800c0d100d0035261039214000c203508004038168418000d11400798014503810b040c1916680701010803102c4505880160809020000c00c81130511009501180a46920b4600350180d030340505508107500c405410440c0c1000014400c03491035102004100e80101141e8a9040710300c1c003411 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 877020917 1250 877019667 877019723
    0x15061318121112030c04031e1e05030334080609010929060c0a0b0f15030d080a1d061504020c070513150b0c010b030c060415020a 57
    0xa1159000203080750040d2040d41c680c80401c1c000d8019010301a299842000c00b80c0001e0708004400f003041000000050400d0f07a0111884000f00b1440e5601d00941000b460114401d910142140c00b00c03c8090b0000e039000c81107034ae0050702641310201411101039220b24100300a000d4020041003041d404240300d13080700d40d503445204100c5840405030b8076014600c0c02d4601110801c0b00303000c0b1319004030840a03600c01c03410140d520050704960030190302c00301c00362801d100081e0030f8510443c1841400303c1b06031603102c1e40e41c0c8035400f068050300c3c1d204c040340440c0d03a0f006204480341c1040342d400040340c0841100e8211141c84400050b80c240c04072141d00303030142c40b2081a210000e400c10048211025810140280c4813901d02d0840a085010720302021312080c000050581162640d4908007122002c05014280c00505500050f4a0f20303281c00070302c0e0702c2c21150448000341c844d6104aa5090f600c0c1d8032001150140e030000c018141c03002030801c60a038a4180210700040c9404000804420b0140000915135 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 877022167 1250 877020917 877020923
    0x7050109260607200a020a031103150c0406020f06011419050612151f11010b19050102060a06030f12050d0c180501051201170703050f010b010807030b0315061318 71
    0x110a44070301401d599690b08003485c00941060104c1c004002040103992101221302c0081e01b50b400018031310450824140088400440c0a8000302e810302c0381c6036040041403e541d01e107400400c4154145154a01249450016544280322246d000302140244015a00c02800041c0c1095102e14074a40001200802190744401d42081c0001182c00c918055081c040d8818056402c8840c0c0032010301d0440d0403c0c1704030380b8500c666403540000300b4103440b06210095680104843d1100ca2420710000904003140640f0b0301718054281501403010801c0105401d2035164415400700d20010b034000195160b02034006179445003071411061501494000c8032070303032485006c5c09401d98207030345550040d5142e008030020880d40e402c0c1130b0010710031110390510800030001c100040710b00300c580c0c95a5280c90141010b9140c8840e9440b1b8500343c2c000c1d40c00c9541c140c1c02044509041c0700007620503001c02e90303803c0d100c0c603418100310001010030200e80fa5180c0710301c0003180d01c103414807041c92100081101034480100031 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 877023417 1250 877022167 877022207
    0x30c0c19031116050108071116090507050c030a0309060b061810020a08030610091e0303030c0318031d12070807170615030309040c02160807050109260607 68
    0x6049012000303e6820807240015080000c01c900f03002c011102c40c3d500038105014000088401c80d82040104149490841c0c03100b154034030b0608068a520030388078050140303401d12200b8070041c00000004810344100441606e0b000940140d0b50500b0005400d034400265009400001ca080303c02400c01d065600390ba40c191002c00001080300402c80e03682c0c030080000b400d0201d090007c01c001e072528406a0320f004919252020b070403900c2e10b140c0507011043c0d2030034221001c01c040d010000c064043c0109034840b0031a041c200001e000701040868000307009440101080100c6003051200c10210b40801400381d40900190f02d8400d80100d11542e6003280d0143c0d0445105a95000440c160010505250055003401601d41c0d9110308000015207601c03c030b0a907a250005022044194413a03100300203602c81d180e030003490031120303004d024405484136030810042d50700300d09401e12282c0d030408060411900c4903031510502e6442c1c407428941040c068030546086008030b009101000b81d00203100b14440c001405c075 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 877024667 1250 877023417 877023437
    0x10903170106090501270b070b011a030a0c030e03130503100903051c0603020414010320091504091502030603060f0609070525240203010317030c0c1903 67
    0x560400010240315160000e043c0381401c0c007141d446414080c00d040c1040f01808803a009002c074061150b00982c0044c2104400828202c0600c40c1c902e40b400e00401327034030b02c452010940a02000d015807100400340800780b0380b6001c14444880c0b1075486800509101c5040d652130b090310802a8111141500c5100d02c01d00c200e0044000c4418144208180c403a41511510b02c4c08506c6c0114460301c0c14569440042c2c542c1d02c0d580000962201d020305108800f4101e00c4680c19815850280c00d4402072042c19002d400300640700041503145d2414403500514207400f100d2900c00f01800040181034004030080040030410403819408050782c02070341c000c42041b41070f41d0180e40e54034a175040c032820481d1196408500b040c007050040380103400030548c2480c2010240300e13400c200528140b100e14561411110120f146000d40c080c08511490000300782070b102402e62031549952a402c80c1c0b00514103400c900c030400003011506250508003110000c074903c0003960f19044106100003000c1c0700d070403000e9012030b5800b18 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 877025917 1250 877024667 877024697
    0x301090516080c0a031b03080406080103060608060f0f130f0633050d02040204091404060e1f0e0f070e0a0501050a0e0703050703020903150603010b0406030b0c0f040314010903 77
    0x15034960540014204e40c1c061461034980c4c1310144c2d04001e04607000c5d0ba0f0f5200110124001030000c1002c2c1c000d0342c480e4030855155241144c07c50307a0310b40c05007141d030300494140060078040c941c221b07401040c112005490bd0310b454201d0b03001e101e18801c00800e03107613007002c0751400c100494001d0707014030742c00b0000800d0010100700000c2d00d0200042c100d0f00511001d2400b4415890100d11211009001030401810140c40d0301a100c101d50400080c818006616001c0104018041c041e01d15404621806412081c8030a10054161100807903030255030742e120b42c540500c0303110402c0458100942c070400c030f4a10710741e508030b400c02e8141c003505c070304ce0a031b410140007049604040c40c4c0350045030b410101c0c5c0117140d510740b901280145000341002c0100350302000045460f56040043d41070782d1400b41200c41480c207050b420142111036444445000794100a010000f103440c0d100b025601840e0060515550b000c1000c860790740f441940c00040088010054400d0011015807083d00182d101c0d48030f4140308403080d0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 877027167 1250 877025917 877025923
    0x3030a2d0314130201080a150b040308130506090a0b03040503070b070507050d0804020d0813030624090608030924030703050f0702061005010f0203090405070c15090c03061a030109051608 82
    0x3c0b602a0203c2e2161001c80d101504c5540113440740c1042d41c40c00da00710f50300c41d2641003495200b98410340f18081e0100e91055950360003040b6200030002100c1241c6010196004640010124800da45c000803000c4006000e00006200b2291070796031010100311140f0309402e014041d42c2103100d0580b42032180c06035031042c00d409041100c0c0156001014100494940e035a03080c400e030b1001d405001c6043e01003c00000280141c0920115500300002c0180c00110403a80307010050000c0e44011001414503000300a030650201c00c43d00303440c000b6030f14ac542d0b48403d0b01030001004d82c1c81c0405100b4020010400042692550004d8000d07a00001d8482240d26000d0307049035074500c143e03140450209512400c10081d0f0050440a14601c490300641c0d003440424000203003203943c11038006010070480038a0744100040d180040c041d00f18095810030103901103455140d028405400001d14190355440b100b103407168041440c85411200800a0141f103680d8500951160600c510140b1684202280480c05640c04 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 877028417 1250 877027167 877027201
    0x702060f04081b06010b0c10150b090d151d030c06060f01170916150c02010305130506070c020f04180f06061a210603030a2d0314 57
    0x182890a80c141c03119103501c807182d0312510b01480e00300c1d1900d6800ca010541072202c24000e000100001340c8a200c0c2e0f809190401c203804014125891a05008000c2d1400c0121400155410b00344099110319505000c40c03043c0920201c090038640810007811100011900048130300309980500700080c80c00c644d0019680d0284403181e000f20341042000840d40c2c1400c050000300c5400516141104418510089100000c260307071409442e0170000310f10b00780c0c0303c0700c00002d401400c016441c01003040c0d0651008080f042c241400a0406441d100468912500f15540b040d03d00e40101c2921181c0c200031b4400b402c21054500f040f40510f612000754a050301e802e1250030007031030541084154401140e511506aa00f031820121080d03959800041090451205d40c1c1081c4001c0191040e0344110640c041150105485158081c00d010581004a56100401500c240c0441410851480c0c08688c08800c05039900c1c3c51841c06d504603040381128219410780041c031000f51202c0345c800a54590440880383d0b4041 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 877029667 1250 877028417 877028431
    0x615030111040b19020705100915090b04060509030a140d020d08100b0705011b08090c060301150f0306090f020d0b060c150403021006120b0f060108010603020703090f030c030b070206 80
    0x40c0a01307550702031200c0840601e51000c0c4199080e01e0f0b160400210f80180b00d48203040012000481030140020401c443c40411080b4103006886034603000f44002180300354011041004404181c00d110703501c0800000b0140c69101d0480740c8034907800742c1660f659090b0110b0400041c49064804021140a40390090003000400344031042a401e0626160783c0341c0c407240b0100c502d5941c038207840480c0341e01409400110119a99070040c60305007010702500c2d10710048440c501c5242c0400040040303040c54030002410030b0003070401e00190310301d0900a90080189510440c540c606000303980400c40910760050100ca440c1c070780d01300006900075003440014003c04903200015440050600c448680007000d16500910a00c11220040d280b01d00d1081503446681c0004076070180e20120a0030030081040351944058414040301c0d251504c0350000340707210818401c807130515a00143ca0000c2c9071080e02440c02030107480c5001140d40341da91410016031540c906c01039881c2c05194003c14011440400c5050041035 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 877030917 1250 877029667 877029689
    0x7030f060807061803020a080312070201050f060405070e09010906061b0803070c15060612110a0c0b0c071b06170708011e0512010504140f0616030e061503011104 71
    0x2090007819120302c81105818400c401041301c00000580c2c0d80c02240c40500900d1004d035880360030752031400302c5038400a010002564148000c1100c2c6400307010340240e008a00f00e5000c1210b40f11140e0513162482101461034000031540d00110b200c0300745030040000c4407002e90703901c41198041c1c1d4044c0e44160040000502c4c91008202041071288514030700000240602442d0b00d14a0072a0f440303104403803850b401500818904102d564680903140f0596464207000344060b071400030300e044018481004100c00a15049184000c110b0000700d0b8419a0355465010088001a144c001c26520f04c0c00014801e010004100032660400d90500111943c012034064640441d5a42015030050306080007410b00c903861a524440001e02c3d964401304600b00f0b1100e00000101c500745402c20020958422031071049542c80405000b500b110001a00e0398482d103d800310365242280548100e014040e8940040014411041840b00d01300c0d0080c0800b200d841c0071002000091040ca101001c0c60280c0d1041d154000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 877032167 1250 877030917 877030919
    0x1203040f09020d0608070807062606010c0302280b070906140913050103030f110d050d02031008010603080408100507081911160c0e060306180c0d030807030f060807 72
    0x401c20b9000f070f05000715083d0f4042480b41d1a6504c00e450f0400c03652110f892507000440403c542c03070f0020035450702140010001c1025016003030f01c2d49444071010780107d0401c518034800000703252080c46000545003070791400d990b070701c02c078a16500d80d190101ca07001d60f48192064041004240501c40b0b90301143d94984aa09101c407100d007007404d0a402c403c0925402c00f5801c00041006049403103064042c51290702c903100840c0101c400200448400c2a42280581c80001e984101e15080300c103480e40701e8070104001d656035503000103460462171103600141441d030901030080b0402c10f1401c040c100b40c50341441150314018100305800f00340da03400d54183e00031400b601c01150320000a1091034142e16075101020504d41c220021a0201c0c0d0700513104018100080004401080080c0c04140b008144903045d141c140d0402d000020388954001d40402c179a201000001c0801503410f000c02d4200c00e00081c182d45034812a81000303000a207040f07424400003031425403158003044051080310207581308040140142 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 877033417 1250 877032167 877032179
    0x50f040209041a0c0414010c0c14040213060215072607020123101202030d030b181e0f0403140a02010e06010801090611120604020d110d0603021203040f 67
    0x70035005007064a0041c0c0d40c04140c401c5803d80031046006000da4032880e6990761516a00b180d003200e14081c02c0341001380818115020070340e28241c08099402c09103ca001c50540c10000400078840c004809400450044002034140d4003c42c440380b10b0102d46c0081100c41c1c0d24074500721003074845100d240c511031000c03e040304000d040d61042e0703941c030100b9800001402c8140b04c100c9a02c442c00041d82c0302901c00340700b003080b81c040c503000e10200c0206600020000c00c0c0300796a0029440301d070340c2103280c0c0030159140c00030441592040c0315041c104801c4e0302c50348001c0c00c1c4561b44514012681d03500314441c40c0c5120118500200c1103403c40d00c1a0b800d075481040140b002811a0060742c804000c2c02c00b19074a407a070300021140188000f0303000700002000010300b0209450034009481145a800c20380d26028881a10003c3c40f02c00c0080d8401c1e0100d80060340d0340031540500c40103260051070300c0a51540802d102c000001654050400d403402125000d41103203220300203543c0ca00c180c1c042c521596144c20300030002 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 877034667 1250 877033417 877033429
    0xc06250c030507060e0f070911030c0304022d0901050a030302031c0609060807090c03020310061407080a08100b0c1905010b220b04020f270909030a020709050f0402 72
    0x220500c42c0c68494070385043c1d502c40d801a51402503c2881e150440068030b284c91030104080802414411020301400f44160080c011034000201119280000000046c0440d503a04c0101812400523880c103a003c100c1e00c1d00d0000c20310b04000900f601a80b00180007003281d14196010904890b07141d4021403034001580030818180803c594020245a01d0322400b24044486000740400b404402e00104807241c0f03081c005400740ea40d0b803100342040c10b01c100700344194034100e0341c1d48100341d42070707820085150300030341d08101c990744035070071000d0074060000c10392480280e0f100d46000c0c001c070080f551492020b0b460f041481410300c269141924194000325101c0d200d0070344074008502030b41c066000090303140701040115100081c80e40c15542c41d4585100c0d948885111440b03800c0140200303440450030f204049280c0f00892045005404841d040480801c084010000618482c0c140103420a1603c0c00c001103a295244c1145204d1005801101d801084c8400c0c10310519104a2030002d25043c9500d4075024411 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 877035917 1250 877034667 877034687
    0x60f0a2d0e130e031c06030f120909020406090302010e04060806150a17011b0e030307060e0c041509061e03290c0a0e030c150901020f10020c0625 64
    0x1d04000b8481106010450611842c070038218070b440034503543c1c0c001003450080400130f400c0100f034280c50040180040b80f10310704182c50065001034a0320604450010941c2c9864650b4803102c0f40b036000140110300598402e04103021070b40300782c9448021781110740410040d030f4501c2c000c143c410f41c00b540014a020002401002c00744101070103600265480e52181103c18060b031194050b140c0d1544101d1101d500c1d0400c49081c2c03007800c0e00d03004883c80070a40000e5242d101e04038010b0300c940c1c0c4806a5846045082c0b20b050130a820060003002124001464070408894a1107298481171620130009102900101182c0d8031ba07014030703001851075041d42e440d94101d00c003035952182075500d41106106183d03110080980a0303c034284031706460341c8040b14010f2001c50301e00c0803039000c1c0e000341200c0481e42d242c0700980030700d0504080b0415291401c400c0100c1c42c01c54480e01c0001c0c0d911401c070181121030070130341c01045074403082c1040d684640c0c0c0351080d0760310b11148a14624101c0c1e4001c1451585a48140d880c04 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 877037167 1250 877035917 877035919
    0x512060f06040c0c060e030a0e120a03030f0b03150f0912042d14030106320103112d0a050a0c06020d1b0f030b0604060305040c05060f0a2d0e 62
    0x184c1c0d0329400703888890454039640f0742c4604941c8002201841140c2000d00c200259004449416003580111419600e0304903542d0020706042e110030400c2031001260300310501410005c2c0445800b5000304010402e48801a5840240c040c2c0e001d010680180002c40c003910700001101909140502d0701c1403a0000501c0c08408018490446a9151840c2c0024540e00000c00c0001c600c0030703003c4200000c0500310b658a07400011001a8006010b0b8148000c0800d2a000e5001e4550310030740364040001600a0408403503a080003140004007403005601162038241b80010010b204c01d55602c24005400a40c401c0e0464400403a00620112007894881c1e0029a0441c0c425007016080100605c00502504c1d0b605440200402444942105d0103a00459048000f07a19140c103100c0025804045082803045009280405450303000080500051510745c000802024102540e14068003140040940100c664480080c0150400d544483d13044504045819003422011842d5203d051003034846c0740c142c41c082c0e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 877038417 1250 877037167 877037177
    0xf0e01022d0a05070b030103150513111f030c031805060c0a14030c1909030305042108070804030c0e19020315041a040c030207150c0c08130512060f06040c 68
    0xba00000e0041c00b10030004c3c012107040940f0380d411803600c800c02c810141c134a0703021140f4080c1008800c030312a4600240e120b810500c8407a040c04510f01095070140e654180c1d540da00040d4960601c1e0540c942d0054031410348540d02082488080c0300e560500c601d2859001d01182d0006000c21080701f207a000074040c0064504200010001711204c4880640088907144041040440d2101d40c0103030580702c1c0d451001680c508088001e0440e54042c0041c040da0281c09522004880b416a03070b8020400a1201b17a81c03c00d815076201d48451511001c82d9106000c1101e5406500100081d50b00c2c40e00750003805000881c00f0712008074624588000290802402d0071007115400181003c245c540380f2640540380c2e001d8200603003118105040c842501c2400f800102010300c1003001b20040f48200907421248601940003145104040c6011030700060817003405170075148009680400a15001003003800c5030300594040f5521500c0d08032880c0c4402048501c0d0041321664400602d0394a07055016815403690b034145 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 877039667 1250 877038417 877038433
    0x40f290616030905010f181703070618060e2a041112040c0b07030207030b130b100510051606051b0a080105040509010e030d1104030807030f0e01022d 66
    0x240101d100c0c0080000da0105103000b01c280442e5920421904c0316029500700f0000030001000e990500b160f141c13140310945100c21101480c11a0240200c404240d0040800e003d482da594448042452240d44100c40d51071800c0c54004078070a0100324111407900d410000e4000b1035920000304044414071400760f6000e5a1488030026a03445140a40304644406c801400c0c9450702d071800840e47c181d0f642010000c12014040d20f0000307030703000170804286c90b42711003107103519190b02e1241d40120590060051072080c0300010848500d02a1345110101c40080b1070242c450004071500b56040d00c00c418070411000202d45800380443c00d65005660040c0c40903441800d500c2415042880303d400c541d40100010306007400401135854140181608440c0490080140080b1548440c1e80ca00c61a8950341c00161640d003180701c4449840184c4000f1038000040d581e9400141c6002012500844030200100718280e1a0040e0b83d440040c0e0303060042d070313900d81916104c0b0b007030b01d9030f070030014285402c01419228500c6 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 877040917 1250 877039667 877039687
    0x40201020d110102120a0f0e19140f0d020a0318030308060d150e030711060325030209030109061b0809120c010b06070b040c0801020f030105040203090f0a030e040f2906 74
    0x2510a5055506c0010300c00d403500d49200070388449000c075071046d51004140700d0998190802c000300095000001d51031803400e80d4401c0307003000050209c0d04254040e0035940c0340410b40110381005820b01c0380d550701a01c08200e05040c12403850500001e00000c01005c0000c560342080c40c14840c03054041e28100005a0010740300c5001e882110341e141c0320b10380000c50741404200b011030440d80402c000b03c80041c21440c00300300c0d0b800076a00042d000750101150f58003405a060090b8122a007039600900240900b5880d4184040030700800b060305401c0f031010b0070b007919035244a10006409103403d0380107000e15413081035000042da0841401c0381e59a543e0f1b48013600b02a81e8810040c600b480c0f04154a800391302d09400d0010388103013640c3c03006550707900400c801001300e0302c92004c0b02d054400c1101c00680321307151002800d150a128040310b0802d441402c008405042d04080646081542102d0901400b00841c0c04a025240210403110603001e140402c9031500603041a68224014042d01c100c1c20aa070882c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 877042167 1250 877040917 877040947
    0xe01020d06090b120a0b15011106091c0f0212090102010605060c2d0a120e1002010b09100b03010504020318150603010b2e03020c010c090503010e0105040201020d110102 74
    0x50711400c0b500303543c0c0091141609083c3c044c2801080588042c0c8065000340c1c840d4121020001c0c20006442051040c4500c66801070303414040181021044a943c2d15003484117075601d0000d1406012841102003166020754401d84030178070b4295a0b503000c0c01101d03840b826280d0058200c0c0d4032607815035488003070105407921030300090f100c20004e403801001003102c492030ba424000000e8800c1500c800b841c58209202d500001844041903500c101040030001850708226070812188005507030091203603240e005055815048400d8140c822900c8800a844c2c0001501c95000140718000450340b0500040000d0b1420f40e011b541e02c00568401d82d01c2038010384103420b042012104c150005810413001340003860900348a0000d40c50002e849000b03026014107829140c1004402c0b06080458805100842c0341d40b117601928100c0200200031b004042107124090401c030914002c1c28029881d01880c56819074050050354010398042c1c014000081c5461400c58075200711141401c21503401b01301d413102412800c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 877043417 1250 877042167 877042169
    0x150d05010e100603060c09060c14010f0e031207080106170a020903030a11011503020d150e160e0f0c0313032109020117010b0301060e0d060e0604050609070f06030e01020d06 76
    0x201c40300042413411482c00500b114582501c03070301000102c03081800055000b03a036255009070005203043d201d000204c40e40c2d02501c005203484003460f0810541400b2201d0000141030180911008590f441d07507101422250f400d0240b00f00c00001d064025541d141c041c2c00d945a03600018a600058501000b07500805c1c038580c404c0030706400080340740b01c544100e28402c1c480c4410900b410f4005448507444c42d0001561220300701c6c0c000d0511020002c110b00b10240a5001004d010200825941410440d0401030408a854840c0a24541d902400a4001c0404003916442280280d40302420f41d155510407000852a950040f02801140c0700090200007440b1450410011010070206d6061070500c0010010340300404090428800340d40180111000c00d41130300c0c195015031500c003100003c03041c00119090780f1800040d01492601c400850251400304d86244903601500498806488000380550307036a0184c81120300894401c0c03028491507219420180003541000005400c10b80e9034030035a0111286 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 877044667 1250 877043417 877043443
    0xd020a0207030807080a020f07050d060c030212040c140f060d09140f0706120b0f04050a021e07020909070f0509131e0303060501050a09090b0d120305040b010905150d05010e 76
    0x3298500c1b00c582d040211081045500000d090024034000200c0c0d105d1060038401071500c3c3d1517000d00888940300c0c3d41544c00201e405111280d05040c241080800710700356000308003200400d0410f50740203060039140c1c10900840501414504800505144000d29080f0412a0034007006141201031030420805000c1d41000000500211460a0005400c01307148040e255850381c20700783e0208180ea6944017150040d8400d48000c900d83e59140c20f204000d1180a0074190624242080f55050000300740241c004188241d500f444592103007200343d9a1200c891080788081d034029201030142d800c00d604502c0d0016403202d04a5011280c03940d801c00079080300d4070843c000000c540c000005155060189000030002070038035520340024124010801001c60190040090703c035204000c00d5100c400d0341c8400e543c3c10a0280e01c0b0100c43c504010043c00d002d40d41030701d0f554814000803d807801d0300d07c00d0130301641504484203070304103038101409030f185281c4505903a507551304c0c10070304a15002030080d10500b0724 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 877045917 1250 877044667 877044683
    0x4020a030209040c080d0c020d170d090f1b1203030e0118030c05070618140630012c13060c20060609010524121501020c01050d020a0207030807 63
    0x420105000e14062505d40c2a504110b41c00300f1f40809a2541c410381c500c01c540041d000e4041200141c50a05540710f8040905000c6103401c07180300902041040340380210744a800501702d80007410400d0040b00455004541110221205100020380640d00c9514400d541d42c00100316502c80c02403505071a01040070980119408048000410009020400c00380610f03003418001250003045103071248040e40a007046884100800340b41c160380e16000c0d20f05a030208094201d80102400e94443c07141800c001000c1c450040c00000716440d080702111140300300400440044120703205440810b00b10010308041d0302d10320600d8441010800d0b138052900343c1c44640c0c41e02003040a075004018141ca210a0340c0e400d143e08400c01780140c40c2e650820b17650440310304480c030b104040010040c2000452a100c0002919980022106440e12a4414980c4035400c015010301c1c8bc40b40607130069884103500859a4009442003001841c1c0ca00c20b58013402090440303204880034180c8076901d540c19a400090181c403121 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 877047167 1250 877045917 877045919
    0xa0b060d06090518030a0c03110a0c1a04120f0206130602031b0c0d02060f0f03090d09212303040e061f090501031e29030307150504020a030209040c 65
    0x42d11600605800824013001c500061819684d0540ca034000c4010600410841c40114800d152140b8441c03503280c10510b040d10441000c918100030043c2c160b10400a07201d0303081c06650350448014064504650340b0840310703456071455599404003c80444401c03a03000905110b00c160502d14500c000c4042c03d01038004580d81c1060040f0040a5102e10b6541c914907404a0300703c00d5980c840c84041c2d142e580d1705548490700c5000c0b640d103410041c000c441000811880100c00c100640e41700064039420524180c0b61858215100e48107200c00c07401c03010070041d04004800c040800203070400c200c4d014208a040b400c07101074041200c1181564000e600c15260002490309200051900340c0e084412802081c145a40480b00d0f03440152540039103201e40c5040c559a003840544015001c006aa6820090381c400c0090030780c2c000c007500c00c000c035980030003c1e85003440703120040a00300001190031242d00000c03d58441d0441c00b40e00c00107024010405c0341c000a0030340000006032a40c00905010764810601c0307080d85 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 877048417 1250 877047167 877047179
    0x30a05064c0902090a260f0610090212070c020402040f0b0909060406060f0f031b120c050f041701060305061e070e060a030506040b03070b1b010c0f080a0b060d06 71
    0x58001d0740024200c20f00c100910100c80d61003140380802c8400b8a603000d00d248554014408a40c8151041903072603002d800b40c0c02c202c04030f0206a10707100d0b1460340001500141c40c1e184180490080040c50305a0664540229000a00902242c508688024000340c90541c0300e09688080a1883d401140e0141001c41e440b405841c1c618503540d881070003540d003044500c0c42c2c490b00900280d03d08100e24103101d501001d40c0190cd110303030400700540d01c0b40c00d4009a0f24084540042001003240c00d01d084443c5058036003e44144603034115032000c0750f5800820300701800c20740301310308110b0780c5001807101d91b60b00c010000c0000e6040c002c99104442e0651007a040348001003c20000d044010001c07001c21842c040510178075500c1341c040d0384403c10a480c00040300e66170080403400414050030a2036043c03044500008100300184005c1080d6164004102d02010030030754014262607103020748001041e910383c1803000031340c8600711a5611548118002c98003a10000c0881c00e154082d00800740e1030b03a2284020f20403 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 877049667 1250 877048417 877048561
    0x30c12020f04030201050d060923060d03080c0d091b05030d0e060d0207020d0204110c0c270c0d230106080403170702100f09030e030a0506 61
    0x1054800460a6140050625034400e05110340d0000038140100420ba084007400130380d02580c0908500901000003041d03001120b486544111044c552440480c400100d03542000b6010304403c6a00da103500d0503d880e0300076602c00542008600e00b030681e6403100310b50041014170000790b1881849101020246007043c05060610710000164002c2c4500740800c2d10f11521000300325800d8010149005072542c2c110f1001801154407038101a50103802e29010303040c00000c02d0024281803100030202c480c24076030030060181030300e0880b680000d0410080704454449104500f07281c2d00c00c00c40d166140c80e00001921540071241346101802e548125485051580b5000c950390034003515403428003441520b071554009101e110f0001c046900c5101880108241d280204100b01244e02c80314024070000340c000c20000010800c011040e0001147d0280c050290b00f400b16843c404250484041c09440c0d0310384e08070360344c50040080c800d10642c190340c0c4070a005080ca250550500c2c06881101d0f10703100d080c1001000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 877050917 1250 877049667 877049687
    0xc0501090803040b04090f060b030a2918070203041a0703140c0c1912030e030c0109051008150603040302060f0906130201030504080d1e06061707110a0203010c030c 72
    0x74069000700003d10408000d60306a40840d05220008900b00e0300251500002d8002c550002202c0306004c0103011866400d0b4109004145c00e1221000503110306003e40810b000040c130745103801c51212603403054140c4e03440b801c4a51081c01f40c011640350036540c00556140000f80c01e41300d0a07035000480c05900301544801d032118104402d403078860400c01e201c81e00a8840100500b26481004403a0409070355601c0c100090004000c0f003c0c00d11910f0000e814064441c1d5130700d0352041c2c483d0094214800d03081d80106441030a440010b88a81150034610740f00346e80c028000380030f4000240301e5000c4030b0760507a00d500c021407040d4420380c00b5081900746071405416801c070281c2614030603084081003081440e20100e802955580900c0c010a4945850a102c220b5106908000903ca41041c2c0502001060190301e0000700d41e1541c3c003006642d1740c950080b9480019618a19000034186020132810b51059809a0b031103021030041d1020703269180d00003821212003004e01c3c000301e43c070381d140d1094440c0c02030b00010b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 877052167 1250 877050917 877050929
    0x12030f0c0111040e150d080d0c0201320c0d0c200619020a030e07030f0309080d231c0f0b030a05061b070f030216050f090105060c0307020d0c050109 65
    0x2d824035003031010040d107104e0000c050a030144041c007403d4110742d0700e2604044c0c071706400c401940c0e90f501031507003a40c000d46884c041c48000341d801c1c451284c00c00041d00306418034200b80c076131110b4100b080450b0512008080506844040c007410301202c0c07000940d5205440d203044c0e03503803102c4007a400d0b407504004952640340c01400c0d181e0012020004d1440b03009140042c003242d08080160f86806040c803d400a2280c1040e035034003441048400700030850b410700600c10050090320740d002c81540c3c0b6540142c0c3d600300701c00c0350400510806150014003030414003c0b0040000c45e42e010b41800485441c54404440303034100445841d46070f0b1000707040b010152140c00d442c882d0580107805400d090f074440e15690704002e0300192900e0b03444813002c58188103003015621491341c07090307461000c8021810003d54a06001c0c00b809004c03808543c00103014684040e04041c150b1000d403403813050360f02e040c082190b0740e082245140d00c9400104082030050b41c4540492120390321940c4041c03041801c140005066000c035030002 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 877053417 1250 877052167 877052201
    0x63105040f14010603020a0512010f0914070207030602090609041a090603010c27120303140106030b0d0b0402130204080f0118020105160503190e010815150912030f0c01 74
    0x6800c1c1e0b1080700400c1c10742d0068200940e40e5821a0703402c9480384129030400000c488850004120341040e54600c0f021240c400c00240111100d401c1c41034848075007030b42d003980580c0c17041004200181440c1c0140003200c200a1603903013403050b18008035043c0e81c07400300d00240007030403d6070018051a1000c07003190015020750003004104403238000623000c406221200848100e42001c0d424200b880380301030320050010743c41300014001c09854080c2c00b0b400b801e6008980c0b140c0d004000300d0600e02c42c0c8074500e455003000300000a1201c0e940c48180484c0c07070160059800c91148407501988440c6c07400240014031504009000380c00d00344030a103003100c0c0c4008142e00c0030110343c14603102503031740314060b41ca6203080740704d55280001c01c510744145144904084030141041404d041c2d038403541c000017038240b01002a2914109940c641140207040d07200c1e1b28025522036403034503201806015840c05402c0403030000d0107034030f15081400521855a081108196206040040e4491034001c3c20b0260f080200802001c0b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 877054667 1250 877053417 877053431
    0xa030f050915040807080712121803050a021528051302130b030613030f0804080a11073c1511010b0a030b01060e0603010b09063105040f 60
    0x1d5030341c50380340181c407400320740050030302007010700c4120005c880c01550700440b002da40c1d0314940713010349441703500b06030310404640c1415503c281c90540c0c5c000c8810f600d19445420380145982d9509986680142030322200b14841d264500804c2d810b465501406960454030096102c0364001503200c08800751100c042c101070400d02400f03e04080314540c1c20000760304070341910383c8100d400c602400500c0300c4044d056140c81004184020320403070f0f1480d500e0384c600980d609280040010310503101c81030705940003800044100075242210784100d4240400e0000241a240d42655a8030307200301c200f03541c50010108180441024910401c1c54588040b024003800d034a1260034907003106510700c4410b801005080c41413014030070704050f40030352101880e01c90040503501015101e00b042d41c490002402a0030120b0b9640070400401e00d002c070140c90480307401301c41d024a030034000c60600000d45c000b0418030540d2207103100c00e100c070741044400c03283c412402d12421540103840d0000304001d0b03031900e4080038282498000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 877055917 1250 877054667 877054681
    0x31e0c0d0513053a0c05040b0d080a0306030f0506100e01031106160615060305070c0b1518010b1317250b16061d0a03080402010c060f020a030f05 64
    0x8404080341c1040b5914444d42d4200209070165110032035816800c2200705400340d440c140115140342480e8001c60244d907515464200340000c80d03c40106096102c0103068040d000181d038880104280c030201d00d804a03550ba03403540c89625039005d060707088406811040400864802d42c100000040401c0d14508509501d140c558110104030703003400a008000014001070f24240c0c9130000440c4661200e010010310802e180720300905c0d00a4014040080d00b000045010144681220850140c01408502c3e807601c46040d20a0b0f81d0b14502502ca400c6164404000d40c109140d144036402825080c00c100d5a40c0456603e241d004005600516160800200c803d100010000368402000380040000000c90302c000081041426582c4e02210600d00e001800c84001c00d0500000041d40d4031456007070000d00c40c0c001c41c0d0b41c0ad05507480700c1d50740c25501c84608800400d1107000a030790031600604101509801c0c40d1100c505071152256103500c6141c0005140c8a0558140300c3c0c0c40e003048070960104000c1c14000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 877057167 1250 877055917 877055947
    0x6050f070804141603120305011e0e101e0e06010503240a21061505030a080a030219080105031e070b070201050c0709051e060a17031e0c0d05 62
    0x2400261040f00d20074699004220100300c601880c01d46410701d8650b4076924a400100000b43c1518840040d051800010b40d050504402480d40d0482888900d000350400b055130441110003803140d10008003400c0b000070103034944042290740708454030f001c002060400204801c902d80181c81c0c90b04004082080000700b00080d0344200c0e442e4009814441d04800c0c080c006454461142c020070615680703146020101031114074200c199501c207400030302141400409224082c0070300c0c4100e41e010741211f180c450020f09050001c220ba01c005050041c14400c2e50813548083c02004150000800e01c210014000c900d0100440541c41e40c200c1c0c4109421084182059210b001d03501c01d20740070090100b00c0d10210780c0144c0035240c101d01c580003100d1885503901242005044207694032000c02140154840c0c443c0c0040e002244a100041c1081850b14600440d02503040d003410322188240c04188500029260303000d0f20205641c05165400e501c42c00021100da040c08021903404080c4841007088001c1d011041e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 877058417 1250 877057167 877057171
    0x705070506150f1909060806090a11010c060203010801060302090901020306241b0d03051b0f03070c020301050f0a0c1815090e18120909040b0603031e0706050f0708 72
    0x445441503203008480401c600345500f2884642c0710581102c411000f2105181c0e00d811102000014045c0f29556120aa02c890b010780301d400b040c4e003121000102042c4a030140e02d8001d101898003120203c0e40c2d86448089070007e1700022000d9458880420075481c0000c0100c3e08044664021407a50418100155405005c0700700030a005488010050300449850140c80d00140400811800d001d040440251214600f02d1044042480c5c4030114116040305a1401107800511204510303002c0c644041800350f4000130114002c01c013502040d00700603107080c010103000c1c0c1c200321034402c10350505400d600203992000c1011410000748843c405521103002100f0021201801c0c0f80341032144158508560850a540007040e48903100da003403007581d1200085a049103100c2074169074540c0c2c100d9110358601d1003101d0650707900032514008207000c41c80c0f525035960000d100400b240d1400286582c402c40010425112104409003c90000c0c1072001a0082d0355000312041c01f020f5445ca44160003401c0d803400 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 877059667 1250 877058417 877058431
    0xb01060f05070b04020301060b130f0b040803030403120f060801150b03060d150b030f0a0c050102010207030f08130507060e01080a05090a0312020c1507111c03020d060504020d140705070506 83
    0x1c3d60b404038040d07442c20342c8900c0c0a09072424800d43e4452258070042500302170b0b8487d14010900000b400202802c4000030b407400d4a002d903010358a586c54503103045421588080d0040c5007107aa413075400701c1622481c400c1c44022700326100003042c0340c2c82c01e22580c0361049103940301c0341c46c0300000c00401c4455540d803c541280d0b1ba44c00751020f20940c0030800d0200c024549040b01c05d401d4231848040c0e41090500040c1d8440003842030031441ca00c1601c40004a090740171b48a40100030402280a41c846d0300c0c0030703202c560b48c1701c12030031078043c010300968803650314003c9a544110081442c0c55950515542d00014866001a0401d403c1c803242c182518041d0b82d5108518000e41001408084d62031410711680469990b601d08804036107403c0c18101060701d2030030094a000c00842d0031000044000400030645081d19014104d910b2048090f80f0701c181c010354000c080e041c200c02c1d0341d10070104095983e403019140c04102071100084045851580198008020304040c0c1840414032002c80052000540a548011 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 877060917 1250 877059667 877059683
    0x3020c060c0a15050105031c050a03180510020306150f0904020723030306210a02190b0408010c02070b0c06010621180c0906030203030316020c1302070b01060f0507 72
    0x10190724981410040440100000c0c1c5140712031180c410a60071140c140d503011403d8079641102606502c031804884240f0301d01050050210110b1980a9840703408914422031250050681136524982003c680120410300703c2d0780403041c09050300300076802c0041a10340003425480e00342c6003248140d0324010800041d1080782c0002d104401c00017050300c0c1140c200001c1840504950503070180302d0302d03a0011180d144c01444c800c0c050f09039040c409200103071580035130740140010800d2074080c030016040090380e0801580f820100020350f0300041000700000d150700c200015402d41c00d013000a0071301201d6888200c0700c03407040c0212003517502c01182c454110350301ea0030b000e0b0b01d402d0076006032002c50000400742c400840c13400310701c0a4403054000103c0d48040c85003204808003034482034000100d1f111804065090341c4140002034010f03c410701c0c804405486801150003608850000078031000c1c1d4a51036240094010503103004010030702000070301500107420801c006c00030301c074001410b030700529001800d100 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 877062167 1250 877060917 877060927
    0xf1c0504030f1121061914180c0303070501060807080604080a0c02030106030b0705070201140c0d450e2203090f062d0203193b0d03020c06 61
    0xaa141c0c0c0784c1000f4806031804244074080e40454040e1104400c80305c0c00c500710111103070481c1000051107034810595111b04000300319200d880c0b901099140f075440700d04540c0300b02000080e2940d010406030010901c108008240d450401010701e0078012554842c02e4a03501413014080003e105005072240801c8900d00080004810300000e07000d04660380c03000c0c214040d004244607000e07600400030842607000f030300c2d4280d83d02003050100040d4402d6598030215504580c0c40c403880e01c0c2c400d128039010b14802e4011103000c2200d5040d040e4a144e0040e510b81100b034030386401007542d15000c81943c03006080c44482c0524a1500542003004401416145001000d440380140c0415019038520b80180010303040d00c14100f13071214009080f00d280102c044003110755a58a21090484001c00b503a141451540507505244a50030b00c1010b80c280626080d05101b2003141805a03031102c0d4000d0030007000c02c1c0010328110381c4082c5516480c6024074140c640500d1001201c0c0011a80003c3e546141746403c1c1c511655813 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 877063417 1250 877062167 877062169
    0x40e030a0822110301051501300c05040e070314130302151521030904180605160e271009091416140f04020403050f1c0504030f11 57
    0x1416010701c00c1d20b034141d601c6800c40244224051000852501940204415150100802d03c110705a03055180058841198141d00a1f1034498402c6040034000500c80315a84a034252416560011145000100e002c1001c0141c03040700300301e8a41082c01410100064009100d0303115510034000c0010000c001611a103d040520030881803074100c14401d56010181000e1480c00240349120709a07a204200031041400b85002190088a002d55807000441c9000d4580d0203100207488801d682c03540341541114003c02255160050501c40c88030a481103581c0001d50754003404100100c41068090303e0102d9601c14034000000003114101c06484542505543c1c40d0301c2014908800e400005115042c50144000c221003000d04500a041141c160381a108a00c01c400f8405159031044401c0324108003940442406e1810000c1c80480010300058a8a600c1e80c40e124680f00d00003200031039991000134864a640107003040500d02c4205868541d1601b0300d1038440122202d400c45001c0c00d2920264200761075 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 877064667 1250 877063417 877063441
    0x905040212030d050f100e1504180303050601030f020a1715030114010503010c08090a12020a1e0501050a06080c060c0a140609010c0c0c090c03060906090903020705040e030a08 77
    0x1c89510000b201d50368000300400801400d020307246040d41c000b11202064014031030001d5070060312030103880024035564000324030381ca503242c809415821565800022610429041c5002220f50180c0c501142a0612200040032600b122940e82c0e0041d10500100d40340690225006044680c050003958071a15242d030851203896100c0b9043d6855813911218658650038034440904850085000304032100440d10b080da0340c0603007200e107114281c20110443c000079a0350941c10069820b944122084455107545d40100343c189031740903100500c02805400d0800100b4011944e109003011001d00c0b00b1440c00c40fa0035622410300760914451080403c07070b548404002c1010107807843d0040100c2d4002c0340105150741d190030082e00c0b480019424585000d1620303004a49480c800360303210701840700542c076001d8048001c11808500900705915090005420100c600400c0043c00d44190002801c2c0d51500d00a0300d4207045a12190259007011054400590013005640c903040083c14603120035500c0c801040c0ca = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 877065917 1250 877064667 877064689
    0x9010f03050a060e130b1302030601150c0b0c0304060c020f07050f03010e100506090703061a0705031909090605090105090c0c0304030f030e01080705030421050d0207060906150f09050402 82
    0x610320044da42080311003d800840c480c0a140156405152915508030107600ca01503418082e405600c00c0c8010004d6146950303007101e4074032441c50018100099580d0749130303140750103071001e2904003008014013080c030035180300e014201092030000704464010010310b0351f1185854850340e0311030307000511040a19102908520351050806055604c8031100e02c075031400a19040c1c482c14068100d901c0060303d828068881d03002a20700544406003a11103803138686015500a0310300b1551808140950504840d00542c0c0e4000b040c100e45034002c50500300038004046030764a038030243c1300c0da0780d0f07070010445074a64202c0b00f40c000c00a181e5450740e4403d0840800c0c078501c15030380010030300c000d000e8825080c107070b12940388011550266034400e040e4440c441c04035528041598080e18802c1030141100d04007020414119200100e0300f400c40c28420010301503802c07078100b4001911059120b800000070032903280b145040f061102c0100d11491410003820003c6407040f409003159295075003020405551f91a0410701c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 877067167 1250 877065917 877065929
    0x6020129040908070b1e0103110907030212040b191e110f0f13061412040c050a03081201120519060609022223090c0403020a03031706040209010f03050a06 68
    0x50742d40d501500d0844201102205e1b6450880700d10160f80c10302c0c1d401041494122a0051400703c000883d07001040440d05010b080c01044c96420004e418801c01580700f0280b1803030043e1201200c03843c212203000e040b00101e205d0704403214900305400704402659070703e9198240d00300000040c010203c0110214074810036515040e07024010440300200d1f0b0001005190030f040700e040188041d40d0324001504c0703010000380b01e0306107400d081c0680c42c0100d81240007503600c00e01800d51060b403e640e030404920741001c16001603500e0b00c4001a83c2c820021410040c03401040f41500203c417600182d00c508d6180e51030f03800856030804031b603201c50b401c1c4241c503000000600b15908003155a14000c4442040300303120f101031036080800c5c4000009902591981c02810440c40804104d40100d08004000304154010300481403044240301c00301c0561a03291402e80514401c1e2203903c444c0a0050300c81100c000010030540c419401007001c54900c0c7d0b40180c4044005040e42004a06900c50101e002c0c09001c080d040747d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 877068417 1250 877067167 877067183
    0x5090114060a032a1e060c0f030804210e0307080a030e0d03020c0a1502011b0516050307140d021510090e0c19051009030c060509030a0c06021501060201290409 70
    0x109410011503031018117850004135403c0b09566481d002e0b10640c0b4010f41c050418514100c3c9903002c00d0281442c0c0354007a11032600400d8018000c000c1c4c4000c040d074942c04030002400e00c1ea540d0741900341000605d01400200703000f03241d1401580d40040480380c001d000240180b0070444550308050080005c083d030031038010044011a522002580441d4031507901c0d04005600f030080514548600d01003190b0800d0325507480714074003051003040f4103440405a0b011582440f00300031100c04111030301d04102000b19287d000e0b040c5c214010000a01c0c001d503010780324650f41c00074020f01441c80e80313406401c1e08881c4d41034004943d030000c503c00242481403000c2c9440d001000780003c0c41c00c800024164406070f4400b211000307a0607140716412a0240d800e070100038110400305005100b000d005201424000000400f12001e141c0c66964280051396075520500150307000d1708000310052001e402050242c0680e200800203500010304c841500c0420324a91007a10303060001910107601c03942c1050712050f400140f4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 877069667 1250 877068417 877068419
    0x30406140705060c07061a0306070e12100603060b0a060503040201030c171305010608010c0e0d050307080f0c01051510030507090f0f050906010219171306020105090114060a032a 78
    0x5804c40d40e01c0548121001884d0641c10082c0141c40d100507107540c04043c00a241e03541d04d03414165018040000d8869010a010480c1815808204000c51124031401d0010503000c3c990300d403910594100b101e9044c42441a08400c0c0000381e03100064951103902444c0110714044c207680c044d207040c510240b00505042d0f0001c200a000c41091120303c1d00c440c880c000811005a5440e00d01d401c0300c0c02c01030104005078841c025415680740200b4014804c6002c3d105a03440c00c00c0990324010300d90f21110081109010126068501e00000c0c8140c5520510540c81c072450009143c0006850080741448403003030640d0748001c00d0189120b007003410040c100111076441e010361034881c0c45880d03180d98403c0c6441003042400166442d407011456042d100e260810950b0f00045e29554042d040441042500c141e4000707114000d648000310300c0a070024081ca800000300c0e8100005120b080d9030040340c0d241050403c140c103020154440310303001030031a27030014921480405220080b032003003e403890502c2040020200 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 877070917 1250 877069667 877069681
    0x170a0b06120601110f030d020c01020c011d0f07050d2004050c22030f0803070e0303040306140a0608070b0c150a0b330a11010501090507180803040614070506 69
    0x1c0705024030350988844030a03044030341c1a5036a07940d510341d4445d03c1d42c00502060348141d4098001d44084c805a42c005405c01c0008903404e4215005242c0e85081d480e20614007046915081c020034998a1254001e800424100b0000c20141a01b00300004e106440054040300403146002d00740d45a4403004200380709070300309001209100c1d0007401c003a80c564522040450301800a0491007021207038045000100c4c1e8816403200e003000d40000700000e00380041501e09007a1540c0c207000800203180721762000150940c828500040f0b00000500c080a000d261100c14058488000750010440d82d2161000342da43c40030380c015605010000290843c180072400c24401458099006107040c0c5909a650419032140c40c42c20124200490020507400450340906940000b00180245050034070382c140841d02281c600130340c4d800c558099001d103100d140e81c1d906100403c1e520450040c40302c0c1c142c0c06d06e800312500b01407126840784924401c5405102c88172581842d45103110301a180d107540c010041d68003510300a4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 877072167 1250 877070917 877070947
    0x8070807121812020d03260a09060e031c1a0d050a1403070c231e0909032502120f0705010e040903080402010f11010c030605040b010f170a0b06 63
    0x1200d6000c112001e54030100b6410180d00d00340083c150000c180d000c1013510b0340c40584041c3e8070140c0c5510107401000017900b145400d40c030200c2c02596503200008215586040183c100c5003003218445150b0020083c0c8101d0403000c900b48101811140300008075022070041a0b03101c081200c42c82c4d0b8102850341604424403070b0226510442074003626102646480820400e9120300c82e07800e0050540c621b5420512081510300c1e03c03a003543c0140f0303e84005070707140c00000510f541250b12444046088a0310a1001800d229407803d8000301054011414000b0b2032400300c41c034400403c1940c030b00c48003440301601990b82d00b90305200d6107981541694030401645140e81d894900d5070281c01d001c20641c0d201034009007070a01c00e5000707281e01a0b50348629030300d0390b5004651540c0391441400403c0307882195844012000c2c81204542002d546002903542d140c00c061000307030b500107455241485401c0b201088010740210810740c000401002c903403195955103003008002c10144007000e810101c042444a0703c45040 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 877073417 1250 877072167 877072187
    0x152a03270606050108010b0301270e0a02190501231308071d0f0601110109050303070c030806150301150203040801020f0d05131115160305070c0603020310030807080712 74
    0x902010b100d483d031a88019030300c041080c850354034880000c000422011001c4030007001109030072010107940b440a4a546425030b5910880388a0715000707058980118601034096005415500441748400da24002c00a060003084074507840111300710b0101d0603030300700b0300100b00c5071800360b0350f80901d1126450b00c002c2583c604560240b00007898880000904a91442804502c40c00702807000c1001559440011214111801c601d00c0d1a507407107181640014605002540c130882050380d600c2860422400c00a00008011b45100d0040004007240d5000100840440341502c00b2035032501c0c098015000d08a1440c403c0364414881540301003812001c120241c0c00802c141c0c030300c001c1c042c88107032901d60240d0109203120340002d0400c03c2181c040007071824102a03450303810000d81e103101c1c00c0980050a0400d0381c900b142c0b0842c000b49000079108100300d81e0510a2028103168034003142503103045040700c1400440d40c000038103200008035007441000b00000c112030740c1c140d002c0d008100c645540003001c1d0900004c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 877074667 1250 877073417 877073423
    0x3010626070e011710061505070204090c080c2b0b13150501180e0c1302090a29130303052823070309120618050a152a0327 54
    0x2a02241028061580528020b46020b14587d125595101009540b242e01a001c12078000380c45800c100041207120514038010000c49002c1c01021a0140c20810804200c04030324402c0b211640300b103184004c41d4130703165080982c00034103181d80e500c2d00400c00c08250f400f0304000388208021b03908601c0960040d00030604a50003a002c84034001003402112080e44d009100382c032001d50010391020303074910f424506941c038218200001460162607070080f910020154110070b2103041d41440c244841d8402c1c1a022040c180000f41395420401101348801d680700e598400a4100300010852541a1101c01e00c01020700b50048403640050701400d0016024064100b2030031800349014003174a00301041d8500301c500056140d611615802d0915100c1b01c4180e0080009030b0341140d0303480700d1920300a6070802a4250074003803001048001d019180041c20081612070380da41c0c0c1820010001000803282440c0f004055490302c011541e407103080e6080300108070310300c2c007030b01140b8a08051289a241c284e03200c0c5401c0b40 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 877075917 1250 877074667 877074673
    0x1515120601091d2706040b071416030509040504030e0f0405070f1d09130b090c090a181e140304140105070f02060a05090f03010626070e0117 62
    0x38550005540340c0c020341c4600c012441c0b844038800d651032155900315910580c07415a4085038960b400d09401c200d0001d03c0e20b02403076070010b41030000f84200501140d90220451900c0715200081102d03940c1c1034012b0007501030070450001c42e103804041c00b42065454040d8041d01c02c01c4107184c02d0074028541400c00c22500c1c0a02c4040e11080c0046c101400303000d2140845480d0100b03048142e0304116080c80c805002c038000004501040000c07569880c1d001e138000c0409400c0c409082c1000d00380b0107172403003025000800aa100b5201c0300e002d5110364444652042c03900100003600c100501c1c036116409040840146190403291141c0030710100c500c2c201d9405401620841103010b0038010040c1d41e84164000d01c2d400300400da0494442e0341c0310308000c1c11190300c0340c000d4900000c550381c08507001d40c000c080003501041c0d001c94240d005040100b40c281c040c1d0001c42c0244600c92a101d103c4919802105401d90a452a4041c000300700c4420042540208440ca000840543c0d4400d030f91408442a21540c81e140c1c0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 877077167 1250 877075917 877075921
    0x1063204090b06280806011a0a080c0f0919181811010908100506011b02090c09030f19030f110d210507020f070803041d151512 56
    0x400c15118104032240d019818400c140c8800c0308000309110a4602a13000001c100c5013075000304c2d9243c0005005040c0c0c800100181e504010b00e5603440d0891102c0f1040e080001d01802e0307001540800d490b03400900ca040e0071942c49a901600c3c543c1440740780380542c5c00103804a84500840311345c0d2070100841c1c940048840d54082906d0400e026610038080301c034401e180189114000c600e181c01501c010071030506100ea034a903900d155090400389192159012142e0740c1d010800030b540c10070031580c0c0200c0c0000300141c9010107540041c400b040040c05c203c0e40d0000225203107080e5102000002d0384082042e044480e40c40d2404c50004200c4c110460403800034100c02c0014019038000c1c018051040110f0018142c841059501160385014005200c4003015405100b054201618420b003400343c5078a9018000c1c04100c0d284044c13800d20030358443c0c98540e100f080100030060241814200c2803210701c4101403545c9171082c0c0514000c4800c03035015880b40e240b2080821200c4100c0040c17510380c602c030b00061019 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 877078417 1250 877077167 877077169
    0x1104091401210f0209090c101e03020408031c180c1e0b070803060a0e0133050a05090406151e05040e040210030e030a020304080105130f080a02010632 66
    0x40898184010b01c0c11082c0c040040040c50003c805c0d0741d201307040e01d0461788044030301c030300094000200c09118008100010845190b1302d41d4056001c10006c0c0d03e0805500c4c1c1446d00c1000c55581c03107240180003103000c003008203001807002500001c40310303207404a109a145d5140c0c1032001812a240c032030065052034017503251000c1c03001c108086040703800d42c0f000ca505120076038940c940d0650004010649c030528010380450187c03240d070700d014083d0030890b58101c183d41040026911030f0141d13054006c1c101c50302d9801e00810540c0030b4200e0380c0501042c50240d88410b59400840e016004581140b02030129034821207044c10f0744446040041d020a0302000c00c0103002d44c5d0151500d200d030740112006d030240a40024003504120010314481c1e40700d8a8001f40c410407480f10a03055030000c0e5074000040e00005410010351109005064001048048400403000300d940d40c240201558940140180f0001c554008500d000390b21000003040c0700d51626124002c0100c2021540b03802c82481e01d00c040600c400741010f = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 877079667 1250 877078417 877078469
    0x40515012a0318180204060f02060108061801020705191e030e01030902120601180e1c0f17010305010605090121060f0b03031b0f0d05030403031104091401 68
    0x10103116109100e594030308075102103c0c00034411110703d0440c240b10000103002408265443c41140d0701ca60016255818004002d0440d044c8580d9041158820001032010707100101d03d8076008800100c8041c801e00129003454064001d984000e05a80104821400c400bc028040080f445100715a4840140c5118501000740040c5980190000d0349050398400a035001e644000d0f00280000c190000c50341180c18100c0c64030209800a03111050303200700c00001c405480c002c03200003201ca80d002c3c007141001800c0c0340800c885001c80c90310420401c003000c0c44050f4012030407401040802052003581c1d684030b0038114041d1803144180780c00349071200000070f2644441c40748040c1040000c200700304030744c01d00e0301d541000e4040000071524444d510700d000038150760304000400f00c202480258154607028111401e044c20300040845015800141c00c0c3c07040150f011003147d034031541c07600300051460a0944107103050b01494110305003d900c0c1400107000440340b041c00034101d40400103841010420b0705042c400d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 877080917 1250 877079667 877079717
    0x30c040f0518210711100c0b06040c0206040b060105040e0f040c0905070806010320161509050d03090f080f030f010603020f0720041409060c070c0509060f04051501 72
    0x816100000030305240542030003d03d4140d000b1030a0f420000c0c40d210000f4024402e0502900107c0c200202d01020842540d031190380c8240e04980030050781494540c003a446410052005083c0f100c40d10004040d68041c41c00d4070090442075054080781d240079203482d05003090580b0140c0e0444d07000c2600065140103802118802d18090741e555007292940001500909180c088128001c3c5144001403801803140700a08000e84c1c1180030180115031908110b2008400d6a0041465500b0406084003003200050104400a00b81c1340c0002c104615082104c0d120f1a003040080c11018000340396511290440051801303045800c900c0d00c3c00340da813000280d0486c8983e000b10401c0480078843d0102280c1d10414050b12500001c1030110740120940009048884d0801c140002c0c1209005000c09110204907169200c941d010081d07180c2011a180d5002407003051040e2403003001503000242441d02c0724443c1c44844800948103122904040ca49580c10b84444030741980003c031100e00189940000100d444 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 877082167 1250 877080917 877080943
    0x203012402011d0a1505010e0c0c10050106030507110f1e010212010906030c150905060901110d0504050f010806060d020919060518120615030c040f0518 67
    0x8040c0400e00c22140119651030000341075560b95481005507881e0020801c0344243c10001a0130b0200d910319000020b580418032603040c3c0e504c0c0c9401070051551000341e00e5000301441d04055100c07018000b00714a030403102c0f071040e068242001c00000301141c240d00014012405c03070300c0394400c00120261090761190940542202070f40014500c000d0300300c070f030580500c546c1c503d440050310f00705005207000800c1c1000c0e0300140305d81c0e076519020014000c14030502e1020700607601b400740c012021440014000a65800307071501c602400601d11840380c0c01504102c550880305003d4403004140a440502307076030403512031640540801c0b02010760542c400c82805104100040140b030a12408800716002500b01066268001440b00310603220103422110610003810f46030390f1244d89200d040d4250250300d8101c2045030140b949400c0b9030090504c08281c0307943c0420f504c6c18000088003020b0000b4601100c00e4040d503001450580182022007003500920300c50022695400350ba542103500056840c1518002d00c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 877083417 1250 877082167 877082189
    0x7030b130b0a0f320702150714091009230d060203072006071b050d0c031211032a1e040e0106030b0405010602031806030402041b0c1401020301 63
    0x9181c1851075400f0407554082c0500004d451084805a94001c600943d489490761a095030350380e907044101d01100c0d80c0480b581c03000d4400080081f07501a00b2007009800001032045400c3e4140245a01d041502c0300d0000043c98641ca4003030240000c0c0403149940205c0071804040200b02d1014001c00a000581c0500034051004966154884100940018090b1001c200703000806180f8410759204484115400b64041e05403400c01c1c034400790600c0c3e1520100d40704011070358500000f103613000c54121039144013420040c056800c07910341180d210000ca140c0710707052854100b20198400800018600c1010040b08185880c40d00c40105d12030700c1c1100410b141c060808001c1403416100003820b010b00c001030b90100034289900d5040ca41c0d0003c1007604110002076a0b4109003c892803d4080e0b10300410560000d9803a2041101d038903081c11190070780c86809540c00001150454035a0b074401c82500c1d15141079040a8000180c3c01000503a0f01d0340290341010744210714101c20001031088a040301c1d010300701c3c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 877084667 1250 877083417 877083421
    0x301141315030627080a12060f12140f0c0a140603041e0f0b070f08010b030109020a0903050712021021050a020904050906340c0f06020c07030b130b 65
    0x5440240c952640d1100502c442525204d07804154000304030080c81c451442d503512140c00804c000e0440582a221340400c0d414020708000008200c080481940e0541a034024102454101400000c0d004c2d40c00d10543e206543e00400d29174130105060001020440741c81004641d50400c00800d00c0103444282da00540800c041800070b046103108042088008400e03004409154a0b1516643d20034201034801012210402940c198071008600740c0c02d002c2e01b0001465418000e2a0089000500681340120307400a01900d040b40142d41031001180c1c007a0840d030341c007506c0710200c40c884044e241c012409001c0c1e0300e072100c20306402a03407108070840031500c074030100a24880c40c010191101074000f03d161982002046082c0d00c43e800341d50f02c500b6800d001031240d810091103240c1694045d0750744044d450b0f01c052a401c00c071000c503180c02c1426015854400109109402d100e0307840c1f924114020004d030b10000380501d940c40045801001c40b40100d070703411119541c83c1c4040c459080e5a0034020231407908000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 877085917 1250 877084667 877084673
    0x12090a050d0302160b040f05060a080f1f0b0a090506160813030609060e120f031515070308150a0b0702090703110408251a0904020f030114131503 64
    0x7034401085000b40704640d440e04440102c6003450940d5009401080c60018003801404181d2901000500c1c056440c2454224500c1c1c1c010011a0047d0103ca00218a40086601c5003003503d01c0e0070b110b107a6040c410241990b15444140700b903000161160201c0d42b9503a0001e62890880c058404004402e0003880c2104d400d941d419911364003081d050150242e0448000c00420901d10886541c01d200e00d2002407405072410b031251408100780c1d031142405800300100e80444010030103481d0800712018045a580404800154010711500c98005103544045165000d041c1c2c0219114041c801c0d80403004401c100140602501501070b015581c0d20312000c2007204014204084400d521007039510b800110214104207060302c40e4419030101301c01c0d07400341140b0390011949440d20340d010040746030030144461806180100d003020107500b8001c1703480701045000c10707501c441e01210004c0046401181e030b84d42c2c44e4025441c0260500c01114040c5803958071400000d5481d1203107800040e03100c01e0690085155907 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 877087167 1250 877085917 877085929
    0x111030412050f030a0c1106060604090e010b19090b0a05101b02150409061d0c030a0b131b02010e2a03010f061d040818030118050606010212090a05 65
    0x51203070702001410070405900e02c40342c2001d10f0050a2115010036542004140200307040d005441165558105005200c12a0385080c2150300302c170003008010a101103400e01560041c0712009807150045808200c6501074903203840e01078151380101c0c500300462100d1005008000341c540c05000d4204400800410a842c01008929204500007040b800c0c45e01c03669000c00d00038268028040c0703403401d011400f403000250501482024000b003c00ca2180400303980d541124644002d443d034003a910b0000003048445060380c01040369041c0182c02d620442600c500d0303c0c0024030a036500856448403114880c859184103018600820590400400c1c2030454901e50399800c44084c0074503565040100e103145404e4800f170080e1595032001040001d0f0040c904808501020342074040641d80250031810440024031010659011580c02c6800b02901d08190001c0f03030040c02101c03070491283c04000584401c000b400680c16101d01800c4c0d0030341d00c240c0c1000480301080e0003100d0140354007140040c07090200342814 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 877088417 1250 877087167 877087193
    0x1141f1409031e0601080c010e031c0c0b040b060108070e0109170703060e03090406171c0c050609010b040b06180603040503040e01060801141e0405060301110c0c090901110304 77
    0x2c0580d40321107458031030801450401c00000e403054210307000410540c00e0900404980b00710a092103000d04003201e0000341c070742000044224060341c0400c06e0010691080203100b1440790b0003500701c1320f241000d00b040100031604031445800190f0100c0001c400600c1040307000025030041e1580c03006103040c07543c10ba40d160000720b441c1020b8401e003480080800c170f8a008580d040048040030790f030750741d082000380000e41d00f440d00b080da01035a60080c100c00782200015110007159030343c1c0d030040405400a5081f180124400d01c05407541c8189800d0001341748040d40300395204a02100c00308400851482403110072302603036003005490720910011158a090100c0210381c0f06100c0d4003500c0c501621221a03004d844c80a07080040040c40c030f480107000205032220264441036080b291440c071302202e08030180304545400e101c40d0080e602d031004100e071a24250403d00c40c11891410058642c01030f00f40b819540c062a0385421307c20a403031000b01d44c41440c1841070011885103030000c140f46036107607144c5600d10242 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 877089667 1250 877088417 877088419
    0x30c0210050903012a0e03070603020a0210110a02010b1905040506120a050a030e0603010e01120f02030d0525230a0f0f050d0215150a08010501141f1409 67
    0x82048140350b6550300303104480c140c0c01ca51503150303420f403c40502d90500c1d8850445c500d060102540c07503d99070b942c00180260441c1c2140c41c016a0303a080c80740080307042084141c0c8030400a42091500c1e41c00008000c09840d1070349071a4001c22100307032403104206107074100c0981103c0100701c0b0300c2c042c8410b007001c0d0001a0310040240c2480c00c806c2c2032211903032801c40c45003000c4e1511f030051991441010f600c00c40c0c8906011341120814110b50406113442c000900601c00c0b8040780806004001c100840d154500d030010350010151200f201c1d49445c058415808491a50701407204400e8601810140c0c21502e09801d402c07000101528034080b5042d00020700292044203184a10b0b11032200040e40c0f031004110305803151b02c00200501d0507180c001c2c40d0203a0035024500755006030310f2101150890204a0f9407000c11740030000004001d447c041204100301e03401015495082c007002142003984079516041e2401c007551403100306503100c03202c5883c2d5500191024000380000c01c2583c172210140c40540303101c0d84 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 877090917 1250 877089667 877089677
    0x11012a0212031314010203040503090f011806091404090b04020d0807170d0b0619120e0f0c030c0303040612051008100e0105070314060607030306051306031e030c0210 73
    0x1510740c410816003003254002c1d0790601003400c10080100020301030024444900083d4118141079403050784038001c01c2d207114015520a20038004a0b80f081d020700c0c607001d4035210500121505c8103c002c00e003c0450080180040401c940089281403074416540616001014008940c4880d0b080200707451245030305480202e010701c03da0700460f003200700260645030400d0006540303110001303800301030303030305644034984107141c03d0281c02102503400704162900e0700c092600c411401107800c01035004000c15070700c0c0740140c4160552104240f0b0005a00c40b0300341011411500a00038100825031b030b17442030b401000c0000300e55145520840000341c026503040b50b07100010b21949600c90307000714501908950100074264407994000203009003031080c980c0080e45c03840e00703000280e00044640b0b034488010700a10702805001031940b0a1611940c0214042c041c010000000110320b0600e41d4050300341404256050b51038841001012545403045010155040d1150740c940350baaa020000d40441c0060380f1800d02c2 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 877092167 1250 877090917 877090933
    0x10f0c020321040b0f12220201080601020f0a0507050a050d03021b13230916051e04111c0b0f220216050c090702062e1511012a02 57
    0x1074804806480c0c5e01e2010f40003280c8484041480c03100c1d84601520141910042c10342d014602130203c1d410102954083c2007028041e220400100d25011281050b025036004524481080140c0403600071b01301c45080b2042e112030f5441d2410090420700c211b00060250780980140881101c0810080c02c54540041008541ea0101c04070312003900d0500c000702145c8049640360240c1d00c401c1490f45a000358070b2000030000061f0320117071803201044600945d44140080c1180200000040c845c0e42c0c20030038094010b1001c1d01000c2d4414140c1d8001141c1034140b0b000e060480c9000498038415070304c4000c40107100c50b4108841c4018003200c020703848910002010440c1018070300c03410b180000c01741b00d00ca545500e080729485080c21400c01d070aa001c0e452289260f00d003440883e540c001010742d0070280b142c416a520340841d40c40c411450384003419501310394580541c0061070010041c09a50b2141040d01c4c3c610a6001426026017242d140e20300700d6504d07403500b6108a088010016102c0702581880c0110342d908 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 877093417 1250 877092167 877092179
    0x30f0c0801053d060e0a0915030201020f0f07050907030e1b03070905040b06010e06040819020a12030f110f10020403020f060a0806150910030b010f0c02032104 70
    0x9510b04590091480c2214424421191a400a210800140301d00c44028001c3e9250801003081c04601c907050411280382240c109640d92024400b0040504490030051520690f00c401141c0b400d41c031080c0c1c0940030b040f20890051102254016000a0030000303408814109010091485000303042e803010195240e44003880c080c020807601003d00b010707480740341c0359401c0c18080503e01180c94012285450a0405020010324401036840e084034003400e103100c0101680011914600840c0d012200f14072402100710b40d04640c8621710707501c071402a20800201501c0741c4024182e0303884504014009101c0081c502c1ca098400c02c0c2068000e025101928883c400440155207001e5030700b007051080a500090800861810fa0f0030082c1c1140c09850044c2001d04c0d00310060300004008200c180070b4088216011036000647c01180d440d1240145204540030344120010700900506c107910f40400e0f0340d80c15003146a4007605040c0407142c0d0040092008081c589401c90344a0b611801c5402e01240921000c030382 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 877094667 1250 877093417 877093421
    0x11d06072625141e12010906030c0906030506071815020724020a140312040f0b220f020f0907020a1a01050d030c050a0819020f010c0801030f0c0801 65
    0x2400d940000d0b404280c01e868901c54036502290ba4001072000c0021281041e488410944100e10342e9001e5180381506818442e507030610984100130070148092001090201a0354031220641b4000d600c42501700b0303250503208044518600025000780d0100d00020b0205208038004203114414203e0007000e1a542d0f04c240e2400c03c68060740c500540c1119000740111003000e007951038080002c1d041c0b02d20790702800c070010391208404000507045c0200643c032a0803880e01041160700321040141a407026191a007450503001c0440c40e400c9030440d01c0c07403000c9010100c45582e007410780c0d043d490403849003c54559540590744902e050807a00300c8600c1c1010655a604d04464500c10601e58002c0c20404070246030131444401e401c00d40c044801e501400620071916030403981b00240c0e6150400c481a03100b2030800701e182c00d0303082c1e10050108400007086001442c0703600035800504525005c035402d035040f000145007650001e04914001409140040000c940d840c01c04005082c0107991040d0980d0701da41c14113003 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 877095917 1250 877094667 877094671
    0x1406161401060302090901060312050c01021201090c11120a05090d060c050304020a170703030804080904060603020c0f2b11120a080105010507020306190b120105010305011d060726 79
    0x18190b5595074081042d4181080302a500c82c2200d402088a03a003140c1e1261554401c0001940c20031001003880d5090b108258116a0301002c00b5200c040a0b694650144000c0c0c49058544000078011210701019503000089804420b2021714405080132142d81044a044d003188072903540c00707020940302c1004229940f1840072440300c00d0740c60564a19081c010b100b0030001a40c0142c07000000ca0310110500040841c4031010740b60b162900c2259034517a070400e03081d18054080069442450301a0000e4165015802400d822440a0a640c0e42802ca070701c8254562412182e60024200d81c03400c5c0c1c80304814070002000003a07406041c4101c0030292841402c6c50326815554034503440c1ca0000b0701080890300070328805d0044c4000d1030028a0410943e01080d1283c101526050f01e47d8080f4500051203882038100390a444800360140200b000343c00a041d019200a10041d02d05528015030380f4070b140d04030710440700200702500040600d03031250141200e0029104042e81800700000081d101c020000940ca68 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 877097167 1250 877095917 877095953
    0x1a011e0f020703200a1d01030209072d03050702030c1207080c06010b030a0506090402032d030c07140409020a14191409070503130308040219030b0a0510140616 70
    0x22010f950880034040400d9254001400d003541151b200131402e00c10b0101d16040d650706035074015042e110030005440c50762141542c592414181d03d65007201164a000b10f0003090700a039030502c070a8a4140741a0b88911540b40040d096401031100101d00c40d02450080003650702c9803030391600d46100ba80c803003800d2100c01c1e0040c030240780002042c071103240d240f4081c0b41d4210804841c061a0313803c280c0d000070707500c84018501c503000e11400300100d0701141841d000004500f4624081d203030b45240b103204145d00d0300300741d0140785444100340454010350704152240b00c4600e6406884840300a0408050f00680510000040d0340100c0700d4581982d6001c0d03541072400280707002030890460394000800c02c80444001448801001018410401100e00c9003200c00c40071b0b03405051240c2d060300d42d0700100d03100650100c40003900a00042001040140f070f100010f10420b940e0700200030f1521240c0554031401c01c83d00c10a40b0440e210b07004010149002c2004005003100407039018902c1c00c19030350341c0b801c0a000f00040 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 877098417 1250 877097167 877097213
    0x1112190f0b131202152a041d01121a10050a030c0504050a09080d0b01020307060c08040b0f01080a1101030e1e0730030c060504061a011e0f020703 64
    0x10003841da040000c0803121130001d00400e0b103804d603111100c2c0800515224040030213441a40125240c0c101c2c50748035040c00907146a40b982c992200c4400300b1454100c2800800c161300000926006040c2100c2400743e00460404420700104008113101c0c10251480003480c2c6129000241ca564400030031004511840d124480c8609e4502008102e840003808000c6640c1414220030004036048215150700d40b2b10180003d824100200403441c2d400340c04401040c4074541410503400740e4029041922032849100000780568604040300c0d44243c00b031041840c103038031014a4034001180e006c0e031021027440601d030000304c0012120a240c500b0184560100c4a00c480b280c0a10007044140f1503140980598000040d060b60040c18245a02c200d80b4000d0404200c000703180e804262044001400b096081a400e02088c03c0900308040200054003c480b00c04404514042d22540580b1011030400d002c22601c50301064001416105d070f4125403512803c600643c400840000d90f003601920a0000e18850 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 877099667 1250 877098417 877098451
    0x106110721030f081005190b07060b0a0605160b22030c050c010e06070b070314090303060913080703030914030a03061818151b0c1112190f0b 62
    0x2c0540a860300b14900300c200302c8402c0c00c00c0035505001e0400f00c115102610507969014507100190551003040c0c004690f805400a0303042d041c0881500b20040d00c030700403614981c1c0c65079207880645262043c00307104070b8070071b1955510304041109a07040d140d00c0501c6040303010310381540800c0100f4210018400f200407800744090901406810407000b801e04100703007014903441e8480c01c001941c42c094903900030404601940000c021074440d03008000c184010b65201c81441c20030394605a02d0b0b4104450a07406600c0c25800198200b049804440340d032500004003515280c0d664800b01c010304050f40058442100c2e140001c6040e01042000f0094901e15a40000301ca83c10300b07221000e400d165144844826082c292004046a84c01c41d0041d040c550010010322240038500701d10024141d61482851703085925250511841e41025113070800d1441030351100041141c400400c89181e500d50340d805143e61040091807041c860f40241c89658074028196076801520690303903c80c1c0d0020860704a0860718070070074 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 877100917 1250 877099667 877099673
    0x408090d080d1a030f070b0f13180c080c030408090a180204030204050c2802010b0301020a05071e150c0c140f10020406050a0503060d050a0809011112030106110721 72
    0x2003842c10800202c0140105e204440c2940b40e554016000340c051051000480b051124185421544040c0d504000171030407541d5541103414402c584010405a142080305d07140169200c1c00595108003120302090342191515260700071035403c0180c0b11038216041203002b1800c0f641d40f00380160080544207016a42e00c0c107502c140001d50b40c01030246e01132410240202021500002542e2441d41d034607005619640c01c7d4090304a000d005c41d003201e15015440083c03504031059020b0000c1440134041c007400c041b03000c000101d031052a0600d55000e824941d9080741341d8401c0d001504002d03440311603841d1003e50f1300d00940300d81c0e05001150b092440d25a100f201c854403040e500740500c03400300424100860801d4a01035000c0c3c03244c40354207207001c1000710000c0014180c0d81c520b00f0200702c160300082100d0100000b40303000b10b002d5118a51880c003066801003000c2081c000028502d80031800c800d603ea01b180d10f400e00550781ca501d103d40010045c010b401000c560483c20740031240c021100300b800340b0242d0045c1d003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 877102167 1250 877100917 877100951
    0x1d0301050a1d010e030d0c09030c0e1512070918020415210b07030506061b211e07030c021804031404081c050417030c0d0201020702090408090d080d 65
    0xe400c01c1d0b03060741051801c0540000100a1310408210502c02280310030740b0f50304c12265006a48c100412500d0018004180d20403150b0a071031003860540260415904148204802440c84004c015400d82c400b003020f005401c250f410501034200a0704503800c1c0119580d00180980c0c0c14409030900c402c00842d410002483c840c0707590030340014100da08400825103502c03075140d10b450003002c15060648807008a078480e16004d0448100382e2510349000000325207010103d40780c0c41081e0b031210f440103085042800c4a46681c2c00ca6290340c08030109010b0317003959411000d03140c0d00160b0058041c4100c0e40228005038580045000a8004602604156182c240740160519411089081c0094020310041c040076038005400040440e0450044000704032806045a00788a00c0d0000038044026804980c146e4400101604400c1070681c141e41c100b410302e2030103d08138021624080d5001c00345101260103d030751040203294122005d44010303101842900c810600d907200d02ca08144140c0c0e9481200300182600c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 877103417 1250 877102167 877102211
    0xc0c0203120a12090c03150b031615082d01230d03121506110606121203090304090213181b050d1d06010609060215071d0301050a 57
    0xc076001c1d034206100d40300020f0201d910350703070301c40700701542c0e607022038148410101140c0c02541d1200c50340b0000b0041410714000f800700900305a0203407084810540d55084401c00e10010f81e45010640846403e184000300e49400c0090400400508110303500300007082d00c4010b440c80903040c0b0301d45d4813095141c40c0201601c4039490542808103007181c8803a801c150f4841a40204050701441c2c08090440c2c6401e000004184403550004d000310035003000a0090382202c0d809001c601a40309442d09030781c2d04420f10141400c007024028032600000061140440007101658000b480311085030b050903218508042240d0150324000c01a8005000412004021403c10518202d2440c0c091004200072034490301402c0da000b1a0300140000402e04ca00401401d03030200e0408821117803025440e44240d8020fa403601800e000e814002942501c003c142c0c54000a14450b03094400341d0024007581e01c2400494501070410003c807a040b003c0d5070a8127159a09009031800707040d40900001c1e222030f10f1045001c005c031a0b = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 877104667 1250 877103417 877103443
    0x17010204050a09050c090d0c090b0909070312170103110f03030c0c011d0a0308030a180c0b0a03020c01150609051002060117160915051c240c0c0203 65
    0x104824845510740b41c4109085420300400450340f5240c1e5140b808141c002c0e603101c550080e950b110140300b40186c0c029920308540440d042003118500c10000d001d2980011600c8035442d074420801000002ca005080340745c07400031481d2214082000c070f9034000100c0000ea00c191103116850f060442c170392402d2403c002039448200c006500d801c103c5601d07107454000c038211850502240702249001c41036200140c2c5101c50000340243c0325140c4a150150150300207490b18849149880c202141c51540c3d06200c0103815000132030350070301038a0314175406001d038000c0c5107800c00c240c5c0a006541800c1001d0160300701c00101078298a075410304003e4014030205007540704921500380f00b6100e40142c2d40104413281581c00c00420007031781c41d4810032064039002140704210510300c1d0b04000043d81c036500c0d5004061540080c00c4681c4220795520421031031104020440500a100100708800250075010184c2444600c50518441402154040c0210350802000ba0045003842d4401030840c03501303010100607211 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 877105917 1250 877104667 877104671
    0x4050d030e0405221416090f0c090302030304180908072604060504060813050f1f091e02030f01150e1006080c0a090f06051b010b0f0409110d0c1701 65
    0x91907240303940b0395809240018001614105d002c4a00700c1c030601411048280000c2c1074010266039540c260010010b691030b82a2952074000100a0980b0408402007200d40050065040900309000c4250039200e15283ca030003241c0e036000e0325000400d90005094800d00070300b4010000c0304042c1e006024000842c0740f40c0c0c0760b100104028840a41c204050f00e080c0d400a1500b95a25a030f0380007044900400d080014000c1d1060f41400e254980000503000641810403480c1c408003006001444152448000000e204220300c030b96002d4031600d00020072703400c0c40c001800c485001304d1320f040c1c8508551400340c21301c2c0c410f40c04000601210b124007078416044541144a505014941200240700c03a030090001d55140c1800507082c0e071010310404201c0c02600c0041b29103100103a071032078040c000b03900a80801c07101c100130348a0611902c1c010f06c114004a04090040c140918480d02007200404521108540321005a004180d107034480b01101c0c0b007124821205c81b10558104102003010b030141e148031140340d84c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 877107167 1250 877105917 877105951
    0xc080c0904150c0e19050a06180302100c0b09060a140f0705070c03060c080709140f040e01090c1203080108280819020a06050105041503020f0604050d030e0405 70
    0x5903010041a804801d00e020003c0c2d107031000789007119901055468281e114000e0b464462410b5403021204080341e00480c0c2c0c8000c8650390f8034095446072010f021482071400310351070400142c00c04041080c90380141e8648100d001000c1d03a11265407040079207141c1c0346548090100000ca1190707205114038001c008001d0748451420130396102d52150f000b03046000704000851040200100018240c2c040c2d58031030300501070720041b0301000300000812290a1f0010702103034400900c0070b1144c40503010800014102c0c2c504290300c1c00920019002c540480c140c99036a410342c91000c82d85d840000409482495030021280510703040050041406030004803154101d50640c40c95170582e40400001c140511006110003030705410301c000203000e406400030300001c60940350341d5525400710f00707440740d18440c020030400c0c0d0362103506110844400002250362400c050760103001510300b24802c5a202d8000410030ba2030703c0d888402003041ea41462800f24041043c0d40c0d0f9822051529015850b4007940c507000b03a040072 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 877108417 1250 877107167 877107173
    0x27030c051203031b12070e0a0e0c0d0902010e060d0b0a0b03091b0118080c101e05070203010b0a170c090c09040c180f060207051c140a0606030c080c0904 67
    0xc0c1c80050200311084c2d841c00000100100324a05442c014000d840403607032149080e49024029921030094036128400307131a000b164003607041d0a2103002c0c035030a6280c00d05100381080807800520341c4107016814030003118200d603180e9941e100103182882200101195850240090118005c0c01303401c102c84502e0f0503c00c108111400140c079020a94a0340c002c40035401310310005a400200011f0040c40204010b2f002080c0c02c0c3c0b000681d101c03544016905203d802d0308041003110100305220328100d2071007120114902540c41080a8031100d4001400021a19607840000b86a0401940a00301c840c40f060882c240344501400b8003204048185c0d0f01e60314920300182494554400c601441d03118603668496900420b20a0040c20010000341e410b44101036118540418100031510501c03005100300300005c5803a09215002c50300501406d404200d40500d80c3d580c1810f6a03240341c455040d144104100c4030007040303260040200460042014400e05802c00240c1418405041c0c6024081e101d160180000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 877109667 1250 877108417 877108423
    0x60604050603060d1506030c0503150106020615010323070f03060609050d0816230f030d0903050f1911010209090f0a0b0402071208010f08060c0a27030c0512 69
    0x1c071400849119114944515151000a083c40502e170001458503102100700038000060000380c075021000c540c0c2c101030120454007130403003d00070342006820190215100005e13118510030b4074501414041074200c58041c000040c0f0940300700100ea901c82042c00d11030003a40110148140402c207150501405041c00f002500301241d52050034000c0104040c0c140501c40080151002202c0318204079500c20014200184c007200c459069800d0017030815010b40038014001075090b68052504c01840c1060f50480c40701c2c00418000c4c0d020b8007840001c10646600d40d42c8040142901245441c0b00425491a00c50040400041c0f12602855078410810481a6540c0b0243d841e40011100044410340d07840070f000c84060309a020752550441e00200300e42c0d003000b00d40c05503940d003449190369440e05d44e0782e91203c1000d8074400344518030084d0491070102d290b05a1300340062400d112142444400c50070241f002da08101140c040103e08090491000d20420192955034801040c0460320300428112040c1c10f251 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 877110917 1250 877109667 877109671
    0x3070605270706050d021c05010509060d02090114010c0c0b040e07170a0b030c1e040b040c081f050a18150b0a03181a090c012606011205071205060604050603 69
    0x14403c4c0403819500716007040c0c044403490400d0308865002d070001c54030140c0c0600700a0003164840c6201c000016428180300e01c000c0444c84d001000d503680c5900e07040b04640e40c84100c0301c40f14100120342e00c5090116603000302d11001411460703ea107641d103190800d40899803001074103882c03c0002e00700b0f541c01001c918401281d0400204540011240c030158002441c1c0070700444000d400000340040c0014814000d030800100d81d0090b10241300406104080004552841c0c805402041075000424254540781d05e10141c9044845220f4000a4540000030007984007030340003c032003e402000440c0307012803d00801807d203009600c6118014208a03100055001c0c85405500305555814602e84d02810f050400440980003210030038035410211014117044011150381e00d980c03007a05200c800c5548070701044030a0101c40c451900c40820440806900d611015150504120b80e07606492008070040c40b8250040700300d03450309690541e0300c80c803410554000500c2d080c030038881480208075646548003169 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 877112167 1250 877110917 877110929
    0x8130309140406030c06030204090e0a08031315021b010b030c0901270c030e0607140d0b01021e0105011403120d02091923040e1b0f03030706052707 65
    0x200100d2166000b01e4000c21081c1d1000d031880014640015419815900070030598081070340c1844210208010196140039140c0010443d48040000500b1050000502190188580d852007280b000426040081c0e030849411820302181d003c0304400520b20034800c490000c03030160007800028204100003220410305220381c8030b407124200c80501514203124151039000d08507403c10441d5a20501d401001400f0340c484058440c468ce00c0820340250260721804030341410300d9152850070700300417a600c001d07154103031042d0305503ca0310540c900e0800d0b0100e50740100142000001884d580340c10500e940e440c0c101c0e04003d01030b42140d04c0c0007590000c040215607034500701410140c0d650f1424008550000c056004c3c40c2c0410051300700c04100c907003041503400d0440300d0020080d061001030600300401c4400b0441c4000d090b900a48024601400303252603285e10b0140140300070500454440460b0541d800800104c6000355600b081007005018142d2203014415040b240c810310b0030610031465664070f840e02941e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 877113417 1250 877112167 877112189
    0x1212090310090503030f0c120601050702060706090b06100e010e060c121215090106020c0f01141303061404050712150c120509030f22050a1508130309 66
    0x180120303102040007054007008041c0800c82d292039810b00c113403a60415034600924040c010301150035180f04405490315103001d0307150224241c83e107034010340b425070200d04104c4e007101083c8a2100401c0c81031298050315406512098045c5c609042000b50f24140e40b0b4201080c07000482c03501841da6403013031010004250170b4510650b10740c5456080f030301d010590702c102c41071410002192881d000072150300901035502c001412092180030810401241c1c0e0074040c8400603840602c00c0345043c070b09544200d00e07461060400c10858a4052140d071031941c01303030741e20311071040c4d14020070410048540706441c0040e41810108645051640d80c240e103079003240c403903007400c0e000032078541080c030140c0400d928481699071801c0014400f6040040d2000f005504013181c0d240c64403000410b265008400c562030110503600f440d14000ca2040900f8460186d0707205400c0f840e61007540032409881c3e620102c0d01401d000ca0034050301c018450b171700030200040180748940c104038409aa10001b40c1002c0d208082e10494200 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 877114667 1250 877113417 877113427
    0xe0c09060c010b06270d0b0f07171305060f0f01030b1819120206010b04170f0a03211506081e070f0e1806060318010606020102181212 59
    0x15840c054039004110301d42c852400640000100841c003c0500340005d29299440004900c60402c14040c54486c000340480c407100e0001080840140d00e4264412118101041011038540050031004404c5880d908000a0503220310b06002c0c0030064140c1c001c09100b040d406914020f2440f18003107030b0621004000900b5070000c21039404000c1c28605042c0000d000300c40c41180003001503015001c442000b035130442c54110f240a4031600c081000e9050340c15040400303181505d0048a4440c03584458101c0c0c8290048030500c2c0300c8540c051010720a024000e5494101c03a10558007440381e804a484920020700f850151410441c1c40d180103044105c80ca40d003040007040e81e0f10461a090848004110b242d6404000104011690840d001100300c245c0c81d6214850052040244041004010798001e465010f1000059135842c044001b107502240c3c2d450200404041c0400480c20f40d4166001500980d4010800b4030403044034860640348004d0449100010a04c6060101d4840d07003600d020159000001035 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 877115917 1250 877114667 877114687
    0x1d030a110703050303131103030a022a0a090e0d0207060f0e0109090905010e0c01020c0a050909030c060103060212070e0607060903260402040b061e0307030924060e0c0906 75
    0x44401c004582120941c0c0d624902084030140301d003040d240845084007691381007040e0342000010381b005101d1640080c06907803921590728049040d5803004940c600540910710354151201b8440800900441c80e01007590444101e00c00d003490828001082194440c92040014580c42240403541d4061814800111564034004070b0304113029801041c0f020b41000f003001c0400105503c0080140241800c1da180003000d503004980380ca20b2203003801d40c802c01c2800140203a10b44a14ac4070b03002070b01d42c41228904040050241d041a800342e1003035403c6d50780030400300d603c40100c080275a400180d80c540a41c1010400c0000395450084a00241596503142e140d0420140205410130815020450351149142e84007040c0080200c1194100e0080c0d00b000d4445103181000320650750281a440c41d510401d4003864004401ca03000101090100350711040044085200c04001100700507100c0214424028000710b01e01c2560003d60001e0781308001d00003000212040303801a13401000c800c88082e0f42c0c1d610071034 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 877117167 1250 877115917 877115923
    0x506060f010f032028080105011d0d02040c02031e03012601060f0f0906140306010308070512120411220c090503060c041a030c0910050d06030b07031d030a11 69
    0x703410702d100d83c0d00050b00d07900d5030040c4d100d4000802c40b09008170303851400c203041161a5802840750324042203a401d55181e01844401c42050b0082000e400306d00705200b150001010b0310200850700d03002d42c000081c901e0b4191002e200112400012303884c510318652408030f0101e89804082d6404881105008107054101800e40000009101029100240030f440d580d000701c80c142907106254849240900000341085444628040d20100802400707050b0300e140c96038140342d480348804980364042c1500d1900c104541e4805410750b094080048080e9240c81d142000014040c0d2403c2480344004090803034060300c2603429040c207101c500c500030031042c2030101c050743d030421143c2040c0d905013f03040c1000b031f00c1000c40000d0b00895103920716054840025110302d00e0a84000c1e99009403103d000c012000f018140280c0d004266155860054988031030754030104e003100c030b454208a4040d4a2a0f040c0f00c19507506029180f803072543d0707003030034180162181305055480c4038442481d82440300410321000f11401c14 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 877118417 1250 877117167 877117211
    0xc051c020c090c13060c0c030f150203090a020a06050304050703020114070507031a06060f040e0415090c1502030c1b01110f030301050312032823040506060f010f03 72
    0x5042c214060815403014029a0080300040c0001c0d60202000980203104503201c4900c945c2060309442194116100c040c80030401312015125410361400959841c0c0c183e01c000c6200b003800c0d00180181e02d130644100b000e0f101841d8002c004101050003404042280421014101d0780e09007001003011154144003007003030142340805010340c000c8080020078003641d1907510844280c00500403515644501c20082580103c203207030003a03a00280300500030510304c884c0c083d40182c0114201c0c80b04800040d80c0320141d801010084a4010352014100b003503c0c580814a5884091400a5802c0c01e40c00110a80e071b8074620f100400d1010840c1c3c14203002030b4061221102d800c0c4110302624001d52040c405070755658002e10607a8003c0c0325002603008000000002e4034001c06284001160034205c05201050700c1c0c40c0700310401d044550340d4044c43c1c00000200c001d405200c000c500c8080e007501d05820100c1c108a00285464040c45084c140b68026aa0080e10f020184c444c40c100003030401d0313560403194040c1100b = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 877119667 1250 877118417 877118419
    0x201020c04020405420705070803070f030f09030c03060b09070305011203230c1c05190c060f020d0f29011b0c0308120a0b1f170a05160c051c020c 64
    0x104e01e034401c0b42510001300a0011b01d00960031180142d039640a45662840751190207880f6901b51146180000d2140c03800790710050703081c640280c585480e41c45000040141e03070700444e110355803000d0104031810440c0c0100c0c2d0000c1c0030305040050350716002e0114003140318501d0007002c010340c0380d55442e103514880021045014000900980751788441138165076501000350302801d854444240d050f5114410f2007241c640740718840303041030907103200003065038450345a00c000c031181602c83c04802c1086481d80301909468249a6020a4000300d9150000454451200c240821824502d0607034403052001780b0351905000030310b007840200346121581585041050303001059007541280000902c56070502800319000d403100750b45115101c44030b84034121402c0c03140c3d4542101c4403200045007082e4030320110036084010f080005c0300100c40d8000e19881c4408640d42801141c4e0342c41071062407241d20340d00300e290b0b000d60305045840c40c81030780b60141e8802c2910086440c40d004204100c41c00c5209100c060440e1304 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 877120917 1250 877119667 877119769
    0x8180a180b0102100b0307060e1c110a0501140304080306220501091b02060615040806160f1416061b12050a060506070b071110090201020c04020405 65
    0x400495140160010081c0c6900501c900c00040b03031441900d1250740780241c0000c0040400500c1e161041d94261400314086510044c42c5010342c02c20080121405203180c425501038100380c810900300a142040da03040503041000300d041c0640510310010449420a41001443c0c3d241d58138200090780200d012982030b00300d80150b00801030b8038a000d40015050b1030102100703007c604011078194811049a0f155000140d00403008030f1058200b00305580e1122042c101d54902d0309842d04103007031402c1416680d41e00100950084031415540c4201101070b0400185040300010a060070420312900808104600742513018505100300429503110b604240f080a040002c1c40f80c1c0340d800034200804076450050045d08003000104404214461802070f120002c09050a0401e1511389100c40000107003000c0a2185042c0c00044100c1c0410840d50900350011011403021200e100090805824120483c021070061009000341e030740300351762030001c8000841002c4045a80c4414214021038084071504861 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 877122167 1250 877120917 877120949
    0x70804030606080d030b0303120a0f0606090812040305120c0c04110d2403060902180c031e01050108040807030201060320090f010803070206070521030f06010c08180a 73
    0x49401c07640840f5000c1050310b00c4aa074410094058416100340c860713154004010f002c8404c00140c580e950002503510000482c0040704042c903088842507007024020801d50402048440c00410100700f1503602a404ea5041c05d00d15500c0c80da8034403c4410002c281400812000c051a000b040003507460036004106000000e20020030b801c0e640e20040d142c07030a103404e007110f040708400b4041280b040480303980074009203146941c644800030900708100320382c860b55080c944d114030300d0040070b0640035800c070200d420394038202003065808400c0082c869003101d004803001040350380c3c1c103d20f126a00a40000782d1a43c1c50009140032401800913400080c24814504160828503c0000d100c40545409403079a46d02d40d1100c0c0d5243d1280e0700244260102c0b036004108190040c18070b44082c041e403510401c1290302e0944100e03840700b80006c2280e0f00f011200804400c01c8000706007186820b40203c42800c02d2222052180c41d0402648a19070070400031202070580c0e0030407910342c101000010034640e9040c4400c0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 877123417 1250 877122167 877122173
    0x90406060801230f0607110307031a07030e0a02090a411b0714030a050316030b10140913090b01080712020405041a0403020c010207061701030b0c07080403 68
    0xe15080c06203d001c032801c1c0d003510050048a50340c40d06074810080508000c481c104040000c95030040c5021601c2034608081b44841c3d4604000100296100d000c14900441241c41840810800140000c00f0981840e80c0805d041001181600c0e0543e0146d840680580d21584c1103009480b030741e6404403071000c00341d00c4080c0303100040c060302102400d0006929030301c141c65001002c0c005000e49106042083c40280b980032641d0682c001c010359441a0400000401303298047e80c15134102030405000305000004004800700280f4809640150354101081850400700c0420448000301e0714070310074401c40c05014480c01c540b41c400c0d0f50b00c41c0382c020300400510791440b01c160043c061026040f03561046100000c220b07050041074940965520300d41c2450140015003c2002500c00a48140c0b40c001c8a10146258207020080640c406c45c041d40003460511152000280380910a600110030814951a0f030072101140c05036090440760000c0011038613843e406030b42140b511034030500800541c6c00003400010 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 877124667 1250 877123417 877123427
    0x1b0b0c16060c0206060a0b220e01030302032d1c02220302130e031909030204061205101107111801030c09150501301e270b040809040606 60
    0x108402d6900fa01c0c0c030354036014240150420240140000c50343c042c0409218020410360b00c49041c243c000c1c09208070b40d903640c0214411202038000758010b800010b04400103070805500a28000c0c603900075850215a00c4d450f403c06400348641c12220a52410340191422070785806aa06044410b0b5004100c440d28402807019a905444200e00070784045d01410110015031103030b8000c1d905840082c0d4646842c005c00904441340b400608014441d60500200158407540f00e50000751000740104680f022042c240689408802e081c2011101e00740203403224004060802d4440144e444094060340a54441c001106155408a40005070850200010601c902040c110045030f002040030440e08501c025006860f04c454028980400c0d4801820706000c4142e1000c2d080140c45000310640b110603034000e0307134140c81c0b000c0803074912131a10750500400d08030b09104640c2e07501c805155030f003440d031110b01181c040205154001b51402c035040d40041d09002200e0b003140d901c0c6000400c1009601c0d1240c0c80030304 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 877125917 1250 877124667 877124681
    0x40f06080c09090729193f020c0307121e05070b04060e100f060b180d020310090507060914011e020313090e06071b0b0c1606 55
    0x12501c0303210a80c0c0e40504150481c10300660058010f80191428035a054103240252174061440f010708480c02401040c2d400c018080b501c0582001800001b809a4018800c44403100c03020010110440c801c1e0041e0342c050300c210313411855003619150030703071080e540d0784028092080346000501001901c54200016482d00c85a0090951660036a052041e04440d0f440309000c1d0802001c10010041d420118115824641c0e01522902001c01e88144000c2c60038100440080b0304404140c640c40d2019a4040e1402103801800240b44c00d1f90501d10b10b00510084104030103500c40c000c02d0b202a0020540d00c051006200c0150f56640a20100400d4580155200c00502c038440014090b8800401c8050030005100000103050f5540003160301046200e4075104882c1ca4484154881044940c5201c5401d9002c1001010890b070001342140e071a2100c00d0900c54001c00901c2001208a845440103181201c1082c44940241c04040c0342d658000940d42948221410888110306528080b8100005900448 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 877127167 1250 877125917 877125929
    0x1d040e070b070204180b3402070302130e0c0d050109050d05040317030115030f06080708030304060b01110d030905010b060f0a02120313030c02030307020d0302150105030a0c0306020315040f06 84
    0x200802e1100790341040c2c0001d880081a80100e50003003051618034401e111078011500494a0f07000000340307407200c87d203c540c907503903409600304090400962a1420461550180c065014001680006426503c5507100341d0540e21030440c803800b14050000941c01608241c0c3c2c07260456080341007078240a0213540103440112640d11010b0840c40c2c1d140e0a0318240c034129000e0b41118003c0e02d080f05800e03805489001e07030b88001180c1d80c080c005451107013008405c00601040000d140d4900740b40c10300354140c560740c1d0316640c14482496421403d00c00001202000745001d481c0004e0083c28901d4078902420301c1030001d9902020110344444010400401400c1c0e8103403640803601082e0103403913001640d0004488504102d010010701c90040b034000ca0008403038502c02019a86045081ea0006803421140c042c1134006900031000d9804e104075501160f80505422001040e60900541d96580303410001e00004002c542c010010501149100c81c00341d80c1c1c940000e105108452151046d90b0041c81103110710 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 877128417 1250 877127167 877127171
    0x1923190519031428031a040e030405060d02090a0b0a26160c0b040b0f0114060d1e0e0105150402040e072709051806071d040e070b070204 60
    0x5420602021034003000000c0e0b1603115410b4032664606151030f42d40007440c2e01400d034a001440542c5001c003007100e0038050071503a100082d40c05078a05000201c8881040364900036441c013440a0b171021400030076503040320801c135680f07a922140c070843d800181c0603a0301900c0d00030407a0305000c00e802d00c03080c0c00390080b0305895031042800003034070b0188280c622100c070381000c030040340f0320214212581705000411704c16a1410051040b018542d10821485400c450644000441c401404202c440c40e141c028010011030327403005000c03211200069070328400c625031000c1d0659591001180485002d00030b0011016610301082805c0c8440f411901a2008840308400003000e10344d080b0340d070310b864400e980c242e4040c004505003503507580e042a200083c5900302030758140e01038441c0c100001111b60180300500018000800c0600300700310030010f01c00301106502015007011041064035a03016070304058410003e40ba030704004180300c020030001c100040142010780954000440c07000c4589004040c814825502 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 877129667 1250 877128417 877128433
    0x20d020120070e1f03031103040b0f07060c020f06160c020d0b2545030501060501050c0c0d1e030201050f060d0f0303020a18030311060919231905 64
    0x900103070240113000142074480c81c1082400400e02c18a82c98102c40d14042c100c0b4501601e0f01c10801464000d10441d2900410004540b8108015802042c5401c5c0c414001402c0c4071243c04912131320f65a001745808241d00d100c041e0b03c00418851804004020b402174a89540c803042e0781098901c21204a0b84501c0c030b4402d000c1c01040c0740306600d0000c1140340c00359558a084445040d071400a001c40003000d810003003a1200c44112411171629415414168200c500a0301451841c0017801e455103a40f055041c402c09000e80c2800b03c0002c906202002030072203201740300d10b001d850401d01811142d103240980f1185c0585840400d41c0540c001d40c0507034211200001d07690b9912040190860900030000c00404003000320740c0c00280650090581c54a45090111400821703051900d101c4503960310039800a04d43c0e62035411030950505c030213504215490301902d003040070001128420815282c00031701e2220201680c269840248075122050514041602c03442c01180301402d650300c041d60400d80d118080c10030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 877130917 1250 877129667 877129681
    0x702060f090f12030a060b040611010b0301090c050f0d140d030e0c15030703091704050103051003051b01050c0a0c0e0c07170903030c011b030f050c030103020d020120070e 75
    0x20a0401e01220b10001c209810402c0c0003242150001350100c40c80c0c40c0c0307440340031a890001e000a031001d4240c0c0e5581102d05400c04914170b080d103504401441c060391501713161001160744202440190380080e10300180307a03104ca60110b620605000005400342440940c1401048000714003103204184a54084c40a1000c03641030076114010078032603a6028900382c50164a80d00760301c002d15800910f034100044e11032402c0d110158800d4030301d0101c512031000020140310030768051107915041462052100e0740345007155545a510345811714038078600700403e80d4440403a8412411035441202c40016076450b40d1291500c007000100398002d440c810b034502c10000f8489103443c03081ea001a5000a5204401000e00b07207040807075482107503c190980000c1151101050302402400b5406010360049844c54030145402021200d6640004a0b481c0c00d101c240722090b26100b09803410f480e011294004000c2242c80143e90000c05084943c0d1090000400030340061008100746007255600c0d03031a10010b9403206 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 877132167 1250 877130917 877130923
    0x180918070806060906010e12070905071e1d0d1b03050606121510091a100507030806060d090b160e040b031f060f08010b180106050304031b08030702060f09 68
    0xc1d00f0540100e06100001c056600c51980b9a0398804c010f800440c0c4400c1d06003081e41400c005810025126894501340910181d00c05460090303642d00c1c442d81c95000507500001440e0b55546d85a641480c442e01c607014049681e10b1055500d05544000091082030740300011110880c0103200607221402080d00203612420100b1440540303070f1000e00a029008104412000d1402c00034045528086151401254603c03083c0304444222054115811100050204108800310380e5800d240402c0801e02100e0000798000c01202e40021048890645400c034001c143c034000c10750b20201070080d540c0e25040c06010354519029203072500051f0354800d9828492030034841038807840d0300001c2d0154807050b4884107607a0000d05a20216507108070101e4043e5559000404001058000d003005d6591041c1608581c0782c034519103586400a141c1080c1150301d41704000d002400020000703014803502e0541002d0b2046040d113525051035102000b46c0d180c3c02c040c40004d507140412035040221100c00f10104400c41000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 877133417 1250 877132167 877132171
    0x1181202010501060504120c051804050c0609030a1e060c09080601050105030f04140a38070e100509040203010605040e0604060305100207111809120903070b180918070806 75
    0x26851762490186444665503040b228501c090b40c0b000c05032800030407141e03900c50308070a071240e107151001e006050a0410300d003019144011207102e5001089014150344000c10000746d0b240c0c108a2a090403043c450f1606220450700c40c00905003850852000186508002a4010b440e4038a0803280300c0c0e80c0740c5005503014403090310f000380f0351030741180041d00044c40740380603848455141c4240da1041c420341e9107a090364a05003008102194110300042a0450a5011f4502c8070f80450380c0002e0318109079a001d031040080754442d5024089024100302d0307242c0500101d400c0c83e074010380115a00d6039511801441600680506045101c40b2404640c881c176203070081c1400d803504100900031030310004945d90000d5201e08000c070781155010380d48400b02d41d40c20020036415040e0145001e1180b80811300c0c5400e1150300311006103012002d00c118089a10001051000c1d62000b9003030565540060310301c1c0ca001103c540085601448040410001626202404000c03078104400ca0304031644071030301e41c1e440f0201 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 877134667 1250 877133417 877133429
    0x1002090a030609050a060501150224060108070224070909021806090f0402040902071b0311091b1612030207020d17072f0a03032003040801181202010501 67
    0x10a081400860b00b141c0c0218000b510440894500180554500c0d00ba00e500364444c81106074410b18001c41c0b682c0500111080314009100c1a084071010b0800c054030200144c025410001e80c4400645154020001c03605000f1420380f140314028620507500d0040081291200002140b0b80310000b6070381c209009403440c2e000c0c03030896902c4503071312582480300a41103401120b43c820210301045205860703030310090010b0189010096521442030611342c29601540911049420040d001000450780200310f111000700112049030706074803080c050100441b1988488000301000051315091031070410850a032292041a10080288101009800320700810501a41020568034101c000130903c00310065289881d03a5410708010094441d144082842c9800070500c010811140d21180840c495280d81890b08660100b041c5007180e9009080ca02d81c4146000d086240a02030552000e051003aa000f81603d180200306584090b003030a074803c040c06000340c07210541ca01000e041544180140781c16202 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 877135917 1250 877134667 877134679
    0xd0c0e030a060b010201020d0f06090b060405100503090a0204061d060103061d040f0b0405030a0809030901170402030c090c0403020103050a0c2f0a0c051008040b07030905070807060203040305100209 87
    0x140035100c0c103001c3c12101035a941155420046484c0758100c900c1010f0820301d0034540000c810b420158442d0032100d007000700314441c2d482480100032075511224501c41c43e481500d8456100d841e58000c5030702e44800f80d600258010708004021801105022840c07401c00115619202c1d1501c60100550481700c0178080c5036104e8501c001a01d082c00301046110390014400e41412441c2503842e1901350b492102910120b0ba2508002010040c40303500c084400e801201540285260905c5540041c0c88201d00c0e002c010349850380c840021f012765500b444003005004c0d000d850b1101c1c5152801d141000fa40c031a0004902003803805001c285244240e2143c81444515602e07100b0071610f04800c1d5040002c1d4419180b10403825100c2101c01011091041560302485250715080d820308200c00c01441c208000e5191040200c6230040201144c20409019004916424002543c0000e4100729003440562380201d04c25104180c0e0024400ea4004020800c49002e441518101c030140c5001906074440c00591a40c405 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 877137167 1250 877135917 877135933
    0x507030c1a07031a0f0d0804030c1502060108030906090448030204030f080c030409020409020714031c0203060303070506130b06030a050604061a0d030c0506090a15020a140706020d0c0e03 82
    0x800d0106564409034041c7c84006e04159032039881d541c1038641500440b0340c0c4054160808034113501003021602500d00303000030398103280d04c99010402074021818624461a100c01c5180c0426003009440d1500c10644010380b9101008003a801c203c00c010024094015601c3c0642d140c826480703403007a0303020ba036480b40341240c0c0b0007042d807500c404075005a4404a441d000c00c210000303080420384010f00c01003201e40c1000d0307281c0b82103040c00d4610340f4000c0c90701602a002000f42c01030001d92040c440b03614211b034a030016100c0e00c441d00400d1940c058000000c01c0e510490041c0b0076218001100e180b0402d204900c12100d65075110145521f138095203000a240364882d4011031b000074515042011034150710000088003a007480005110403015030f20a0300812800e40713010082c00424803145900071016001054140c14650f258500710407540d06202c409980881c108007007610411849490b0b40c1c03070340f283c19203544543c14294000d500c10403c81c443d59150200d07400c0014020703c01c1907445031004000d0300d215 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 877138417 1250 877137167 877137169
    0x1b101109091f0f0e0f07080708150307090b0901080c03070e15100c02031c1b0c080105040b160c021c03030608060c07060e03041202010507030c1a07031a0f 68
    0x844014141ca00d010700e00a10107000c80c004404540001c00f04005000111860071500b0300071a03d010303200b5103010b805202000303461904443c9a503008440b602d410000d030742c1e80d0310124040c0754810003002d90501440800042403071180e00281e084903421100407106907600c0081580d514440a6480d400d50019041040311180c1814042c0d4040056559084103145150001d0700c2c4900c0003ea10020036482400f031429803e0400031800e0307509404440660104005001524103500c2d89282c182c036241008506c010400113038041001040104000e1080d41010b20382000940c0044501888030a0b01031140800b0a01c10f656001c40d00350003400902d1034115500c01c014000324841016024140c6807540051a1002004182d109003600c070101510b86940e0300e015001d44448202108450340144030a01c0b171000000c000415039a82420083e0b40d4074510b16050f110f410340320b00f0180207480008042d074160b24403520144e200751030f80c0e03400300624605910b0f485140c4000342c500390b8000200301442c2c216 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 877139667 1250 877138417 877138429
    0xf061306120b45040302061024140301090b0123070303050406021e090f040608191a090106090e15010317070f0507080f070e07081b1b101109 62
    0x1d000350190050f00c4040c1da02c14031190100c18800049650111404001c240340c0d062141310341008081151403661071614491304502700041080303602550007254510f4900c3e00400440c4010646c41d03100399140c0d82c1d100b03a1100240580c144e07a50228400b45150511114000181c44036604180041d60925000d81c80840c01411b00400890b00c40d542041007900c12401030f440d82c00000351050110f990303580c0780c01c14022800c040d01e4030749002d54117056052040c00c002055000f1501070302540c0540341c0c11f0504101c02c0c25814503e464901c032522000b030041602041d000746d8217035030300310301d090004c3c200302c2d45699a85e07031658039104003007240480140001244100d01c06002d05e20408480c0c200032054035141d0340810001401ca03210f83c002582009034902c00d01074003c00c05e43c0b003030142c16003034940a002c640d1900010b0034078040190240002d00218002c0d254548000388a800540d101c2d0600880910714403c8085c6114040c0301e00c408000700d03901d160103200e0341c03464952850360034484000280a1 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 877140917 1250 877139667 877139719
    0x70302100b131b0306080106030c150504030c0605071a09030a0309051c080906090604080712021905010e0105090c1014070f150606022a0f061306120b 66
    0x1d405514042d03007000000490041c0e084180b4032042242c240c3d14611400790441d43c640e0310100059040210400214822000030300071512a80c601100c112866002280c091043d43c20080040c4000071011030400ea100000e01000c2e489040303403a9042110528411008030704480d0306003240d0003008040817840c881d0f0010180c0714841c0003207030505010865007018480490f0f5520001844620412011900401526030428410b2003d0208c1d401d06072200c81d00342c40b620601078120100d001d1070242c064401c1088261700015085052082a440d00c5d02074043c12001c2e0081c82ea640c00c01e404102c01d08800b107001c514203580102541c0c410038543c41c094400e040d030a150b030300d1131701d50901c21500030600c49410404070510403080c149100010301a10411994160007000440d8001400d1440313040541413611041110000d10340c100b804844001040504042486900188040307280c8120a40303a401d0402514200d4552812001d8442c2c41501203821000c0701e15402081e800265842000c0c1803d544 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 877142167 1250 877140917 877140919
    0x8060d0c180e0105090a1a06010c23030d0b090a05070f0f18150f02070e0f15030a0318050603060a0b13170a150203040c060f050706051005030d05070302100b 69
    0x440c2d034850300b142d510300310b400c101e031041d0140c2c1064941508000e4a034100e4010000851011901402d213400000c02412038068010090200e52660003003901c030014001c3c2d40b401d103c2048940e103110620140c0d016186c843c1c0c03054042c441c0040401c80c2060607000303480c45600039a407280c4000070303160000c0740d2840c0f0b0040c59006000e05813800411700c05580e02550064165200c9004800141c1e002c004c00f10b03110f2904050440d0480c0209120510001c0040c50308400c107030a190465489103038941c1c8200584083c3d040e03252080f80010801c252b00122080140d02a001103294030590b2358050040a1008927038455009c40207030014030240b0701020181400508a010301c0da00503440741412002c90600c4c105800c4107511203000041003081c1500c5a000914980c48254218181035541c4409100140124818040c90002403100c440c4508146c984c0c41f07810410920240c20a02e40498010160f4018a80070703008806c10078000fa8014000c9804866069008213001d2016a0081c0014202a151a = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 877143417 1250 877142167 877142171
    0xc0a150e190b070c061805210a0e040b0918010e0309031905010e0307030c0c1202010f08040602090a030f060b120303010905060d0c0602060a05161205041b1508060d0c18 74
    0x4840881d0040c403411501c4102c0711b8185840782031906000d4070703200c1c100d201c03c0540d804519031208401810010b40d000c004103400d054890f500d582d0f00103000b92034941601a0000a8442002000700c06050300c100c560721840000c20150f000302c103116442c0d200d2140e1164150b80804551010340c540000303a132000701d02400c0000f03800d0480300c4003141103610580041d40040c0070002610305026840410304003c19070304040100b00d060f00d03400030300180740302140f0905000c00c6400284c01d109098041705c07507e960003065000c944c1d48030300d484800318090781000d6031030b103151181c410560700300101500d071040c4030407009500f960b20709881980a0701009094039013004c2c030042e206001886034000d45006c3c12594010308040e203003094080c42224001400b204100da03400c0404c0c00d069810170420602c00301003810204244c1d85508244c00c1c220b148143c91601d4688200300091700c02121842d0320040404d0f070365400800d88a201c1009150700c96008080d000c0f512004040054100c000001c0310018800702c00 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 877144667 1250 877143417 877143437
    0xe100b0103020a0905010522170715080a1d01050c070308010806101a0c100204080c0910060e0d08070812011e060f030b03011d1e0d030b060c0a150e190b07 68
    0x101a0400300c036a0008502d46107049d1400c0e4078403400d00031030018009540d0081d40844000c4402040c070013000e04560310369907031099548035001008000d000e102e0700c00d00090040703042c0100e6040c0d05601042054001481000c008507140c0e0300802c1c1c2601031100c1a0612441c18144011512807400307000030500320303060811246202100c180009003030003031a10700c010303102d84c070b002e0300c450400d0000360825102c0c0105004114a00014222070802d507075a0340f5100402e025000301007600742200880240a0170004a2402c04210006004191a01050b85040c060382d80e9844070a034241200b42d54600e04000a4070140b00061088080d94001c03556403030003040381a40a400300e03003103480180741e1026a0142c918860940581040500c8044051454160103420401c099030b0b2540034501c02d032020583c0303994091200e50740b94015a2a40441c032020f54584000c9440c1c41c520516045542108060078174034140e40c3c220001c640c0d5181d200798072038582d03491200b40d9503d004004008010600340b01400007 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 877145917 1250 877144667 877144717
    0xe03072403023a290f010c0803062701080736110304060605100f020a020f01020a0212030406120204050f0d030306080307051516022e0e100b0103020a09050105 70
    0x180820500308401113001c141c0b03151602801c20301e4a40600e50003000c2d403049000b41a40e014281405880c1c00c0760015403030b500e07041c0028280e0038071405900b030591014103001114407403201c002c034101d0340440d08a4040b1581c13022951039044100221500c001324041803001c50340c51040e82e168010001840000c2d90500d000d20203c3c0580042d20306840f0359070748060a01c8541046e1b000003145106504211814002c1c07544020350300c0c100c0410090044403031901c0114580d0007082018066a40242011300c0d280c03400054551f250094490b00b40001c007006000058183d03103100f11810b540e009480c01c000d480d1a2028082d00c9141761804500301a030b5240300152400381400a816410301c540d01604824950140c02e1248080107008250043c0c0c1c0c03a140c00ba4a0758000039100c43c001444a040e0040d90f8038078100c507040e9140101c804910909010f0003078410080031400c0c0031a0042c2d40f604002909020700114102e000b100c0c0b03008045031840d20140300e5036006402901c444100d858a60034104c1c4024 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 877147167 1250 877145917 877145921
    0x60c060b0a090c0801060305060d021302120c0a0e270711070b07050111040f0501080711030307110f0d201e030a140a08040803070e03072403023a 64
    0x9880200602d58920f0b0b40300c420303a40801081d0041c9a2440c2c288400e060880c0000c0203c1040da400a1040140513443c8481c03102d41c2d0150359502c00500203034a84c45c03611a12810b80340d480340c40000c0024580100103111490040c2501c0c0a40320030300800913607600c138601a1482d44002400240c140002226003c034000c408004030f10107041008080340e01c2c1e058601d0850b003900d007082190441404140003d0003000346540304403049680910f402d61280d1202901a10400310403900d1041c0e9001c000104085c40350404212811038906100300c1e1031811150060b551500380714050303035001071700c042850011610b007440c40c40403608011003600c1c3d080c800500301048008507000d03200095003002c074030881c41c44d402c000707000c008450301042c003481d003040798200a01d042e00c0100020641c10010000c10700030340c03051001c04801c05e40902140d02864031118204213101c01889040e1184046c1d1248942e654824000c0e11400c0710f00703100da284100014594245c02c040074505040030f42840d80200d9995100c0d0b4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 877148417 1250 877147167 877147169
    0x40609022215090e0c040c121814010b0306070e01050c0714011b050c10120e01050103050c0a0e0f13150b0f150a1107091109030705090108030301060c060b0a 69
    0x200006140b0342442442900c40710035610200c074540c64000d0389058910080755005043c00120b0300003c04000500c1d082c1e03150040c0380984800f2524140e44440c0d4552054a4088036500940440e00e180c0c8030b2860b03650031303500c540c252503400d43c0005004c1285240240000c0010f400705040490802040140700c1340f512851b948074480031405000241c001d540c010300310340300c040ca40b510b8800c00c41e6a00d469496032030203001901402050000c2070700300001c1c801c5800180d16150300310b0600880821286081c0600030a0100356020300921340450308502c3d0029002041f0360451010200d6030f5640603d101c1d956100411884009081d40c484030700148403051a15500132a04c1c0f000682d0001c04020300201d1000c500e0850701481480c41601c6e6441c9080003503a400d0265031030514206540445403034204022640110881800c00519552000e03001002d4030440d50306408036450556a0000c00003149001c2c07140304440e03081000140a400d1140c030083c01e0250003004041b40b00c2948a001ca1f00304041d03 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 877149667 1250 877148417 877148479
    0x409032c041103041703040c0e0a02090a03030c0303060512120c12070308040c050103060b03060d05010609022706031b0304050f0a030f110705010225030503030f18030304030804060902 81
    0x2c000208020440c1d08200e2441050802107040e0440c0342c56961581040c006003d1034412070f5542c00020400801390f011100c0f0400007400d1044c2a55591402070b00c141a4405c0850200341021008100c505100c5050300e4130401310802000100074020805005510007880b21560b0b026009100d845065410001e0000512030761702c0560794501410044104415900b000341003500300001000980d01440549400c00b40840f5000c40c01251442c12034010b040580c40512000d0000c00c09490b4082c403105804400214040c401921a105004200b40c0344001c550805044500407015011a410070000e50750142c8128101c0303010012541c07403030b0310b03051140da070480004403292001041654403421190005104000038051507061500103500e81000ea856070058071541d15031140c3e5010303500c040c40010f680180c1502d07560706007004c400c1703501c3e0002c540d03240c0180e40700c0b0b180025800d400022648142d4050f03075040801d03101c3c3d9032508050b2404910690b44049034030340028812114100114020f40 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 877150917 1250 877149667 877149701
    0xd1505090a021201020a0801090c0203120a05070318020a140613091b080601020d080a06170309031603030206011a070501050702100b0301090f06051f0602010f0b0409032c04 76
    0x3072901c10003100c031100c80350781221039005004400c6131642201100c2c4c151170f44068007044034000918124510b0080c50001d8013401401014040c5a5485500c424003a0074196414401c4848460184038903135a0820001c0d004000c5a104000c6a10f241000b16510307003000b015a89040d28401c0340c11f2405669810070710000366a01e60b640341442c11078011086142c2c40b030501451a141040000c0e4407151040340100c14482c04e100010540300190380800c0c080c0c194848401100314a00c001c7c40d69a030403981e079060107449201d190b050305a0725290502d013242da0542c0100b03211b07804c141c0f46036143c5150390203100052a0038003504d070009000307005291081c0c5560f80240103907844980748905a074a50482240070782d00d40003149000c02c0c070b81003403440f205070401c2000c2800d4866802d6400180b045003540d0406440807140440e00d0359040d00484039a0f0000c01d024001c0302400c0081004480b001e001c0140032034455a205008400600c000041d10340300d05440c01c000300588008281585d03000048804011 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 877152167 1250 877150917 877150933
    0x5060702070603090b0402041a0d05011d060f0a09030306050916090f0513050c09030109080d0606030c12330305060c040b1c09020634020a050d150509 66
    0x2960400400d00100460b140c14840040c1e140c03540c24000b00050b102038021034441d150711a8080600380c05044584001c0c082926880345030600074000c12400189072404203440c540d00308818000103215020700c40c10354a44100307849200c1094010a45c00303108405150300d50a002401d50b0320903032082d201e0302c200d96000400090b5030100926441c1c16030441c0038001c0c440d113400e22407511580c0703c4800701442418001041d45030060040070074010040202e42c50b6003002c1c0350a0030041400c001d002d03908a5500144000c50711040c003270b0196545844044006a82c0d000468008211380c2c0010202044220140c50003e0540b4042e501554031000b66001c1078513040307420800c0003001c1200740e030f20904c0c0761249030800d0708089240784944076040c40400c1613501007203a03680e80e100701d6005401143d0700504070381e0390350100c0101c0010300d01d002020640e01031203444010380400c40001c901d00c5d415130003805003a0090401c0200040c084404800307a405030350340c0c0c0e01c80c0f4070b4140c00d00c10540a9030080340200004 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 877153417 1250 877152167 877152181
    0x503030406030b011112042303010e030909070806310e030a180e0604021c09210e010e0103020d15030f0c0510080c0a0e030102070b0a06080712080a02190506 69
    0x105240c0413145d00c150f8441c00704003900d0700c1c2c403034203a5050300c10300c020003070501a03480d29200c402d04d4004542545940703406104c0c01903801c004000e002140c1c1c00d0301d60000c00e588000342910151411501d1176004000030782c001c0e602000c9030307860044c00c07a508615800d00002c00d05c8100704450b1800741480341c65100080000c155034011baa6144c02100c0c144034243d03807034100400745142ca41c024120328000d42c0c000c1014600309100e250343c021200070030141082200d400303080011104400c0042c0c20074510050760310030704861082c0380c541288041a112401c0401c0081d004600952100c07441e18001940e0760901403e200c0d4200705030000714050179640c03a2405a504040e10f161200d0361010380308450200c4c001c210305030007000d09984409804200c07602c4540c0440309888031109010029410b500c0003882c07004008164096a00550620100b001515100c84901d95558018080ea000a1041c11016000104014001d26100c0ca0501c192030720b01c0441401007000c4003443c48100c0c0c03550000400c00c401 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 877154667 1250 877153417 877153427
    0x7050c03070801060f09020f0702150702042018030102210405010f1812030f0606080a0b0102060c09040e0c0a080f011a010e0103020307020109080313110907270503030406030b01 78
    0x103082038200800241740b5040740c1d110020414401c485035036401082103400016010184c405480c1c01510a41c1c15075005200140d00741d00c8100100c0c802c3c0d00d8000d40300c02c03400304150350400384107008510500c0c0804c1c00e540245d1000614403a25815034003001400300900820100034908075114000e484141003074944075080d91010b01d01211214907107a10840075050ba032415051050f00002c41310800c010b02c8130205d0103483c9103a500410241403000000300141d006540da0301c80c1003a5081044252100c030012a22010160b460a11600003032001500034a02940049000d821280881c0c400d01d24400c04504509002d500554040d0803440003c0210f41e030030b01421402030060310f00003241460241c000313801d038552090039030304040d40403000403080740c001d41c42003030381d1500812015181c2c40c0081e0100d40c0e22001503403c495010300c071480b548a904100801c20b01403d420707110b5101c1c0014150700000d00100001103c00d044030304083c005181e1700c00f0f000800c00b07842e207507801058000d030b601c002600e = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 877155917 1250 877154667 877154669
    0xf1505040e01050f060630040203010b040c09090b040b0a060201051e0103080406080c12090706090602010b131517100e0607020703060b0d0c0902070c05010908150a09050307050c0307 80
    0xc5164140f004004404030002c5541754007180c203c4409803644041c100f003050403940c010800c041c0107924003440c0314841004010511a506c02c8000707000704080d08081c401503600c044181c102207587ea8405026103009038100046024002e0030000d00c60040300006220809590b100e100540d40d6501030012002007200302125601d003402c050f0f622540341d0f0356102d615104910420082009000c0490980c034880e200f1110007102d221408404c1d0f05107030780e52544404a500c00d40c8082a0900790000b10389006004031f5000d0b08009020007401401c0102800241108c45800c07114001c51600110ba82d803558803000d081c48031098000c043d9210900841c0040310034005126410398030110800c13041c1d40d40040d540301501e03030041021441140d5840425002c1c1d0007500b00509240450a000c1182d01d183d40c05861400e004078130707440006654800560303901c1c045002e0410303aa00f0035016a1b403c1105001c6c8150022a10007001400724a2912002e05641200f04200c5031508424800c0407680b80c1080303040 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 877157167 1250 877155917 877155941
    0x6090b0915060901120c0e0405070f08041106090315010e13020913061e0f0501122117040b0f2217040b0a0503100b1312060f150504 58
    0x400541440a00d11108040c0e50807a248600e4000860b4200d99105030003072516070702d40c2c1c40180180386801c140a8091a802010640150329060015419030710a00303c0b075150140544a02e8032646070342c4c4410038014040c0002c41e030881010081c032642501d0030088504c000300c0081c00400c45504242c5000340c0d2a10240200310300c90181c10f00f0304050390f10390803001d0704014580c2d140d60b0220054500540600450304002d400f00c103404a60b050141202d8002e1658103c110b18100050780c2c035101540c035100071210016050f840c0700208140c0450f505040d0040304c40550a000c0c0203602c60740180d5100d04c104903012034081ca2250103110b10304007000d070880d400000d80c7e08000b80a10805240c003d90003014030707026040300c0342485240b04d2100404c0850703001c1e01d14450450341c2d0300207500016040d588151004440b040b00200d000417901104c80980e05500744085203031a140b46000c80f100d0365031348091016a0000d0349d030101001030400034403030b2204580000c080e00d21039a141204000c222a5090106 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 877158273 1106 877157167 877157179
    0x6020d0905060109090b010e0705040f090b030f011e020f0c0303040c080d0c080720030d0f020c01110d03050403021009110a24080702010e030d06090b 66
    0xc840000e00603800c030781069903075030300000446850701e038040c100186c41c2005000c0c9a010800d2503801c0700c0b6515040b41801d03140c0d601c2111200d4241d00c01404c560344c6140c5004182400d200b9103044030741840080164000350b40d500c5a007543d44803032014a80ea800900c5468403002e80c82078844001108003103d8807860546040030464089000f00e81040c0704059040c19614490740011a0242d0b00c158060b050103050794500f5819240100e1a005254240c0a111919103040280078400354a0759a00701d000003028202905290512413014100a80d0398401d41014400007808080311805240c000fa65941da030808a0070040710b518402c200d0b90034411030340c00b40044800054001c440807251080c907550740e64210f409006004852445002030309001c20034181c0110310035640300c3d0482c0008a02654000240303401c41d8072044107040c103155903141c10b010469081c407401c1c000890a0f00c075 = true := by decide +kernel

theorem cover : BRFrame.Cov 876978417 877158273 := by
  have h0 := BRFrame.cov_init 876978417
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876978417 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 876978417 ≤ n) (h2 : n < 877158273) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
