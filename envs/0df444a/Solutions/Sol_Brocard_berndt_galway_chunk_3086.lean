-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3086
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:36:50.22317+00:00
-- url     : https://prove2.me/submissions/4229d0ce-6ebd-4ea5-a47f-66264e4b9a95

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 554856115 ≤ n < 555035971 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 554857365 1250 554856115 554856121
    0x801060f09030b070507050a0203070b0a270302010c39120f0803100824090d020312150409060b03060109061a03071404240504060503130201120207060b09 68
    0x8000d08140c800d60f0340c0305104828954502e80100c40e141c03c14078054409118459440c030242c3c806010303142c0074164012013603648115410010b402c4030060390898030186845500300300b04a12880c0400e0a072903092074101c0d9851402e09100070100c0500c140ea800d089841807028034040e400100307201c0382d00202ca01e1030b8030741540c1c1d07491030b1907001034035001600d400b03501800000019089002198000780481400040b40e884030000c03458818a030b402040940481050303008800c403d01d50880d4040c101000034403030380340e1400c0d00030348034011001a40c1d100652403000c03c0c908108540e1026058101810400c440109400d0a0026042c81c110440c003d002d04030000c036a058050007440c05445c2030b503261900385ca0000b909880c1c0c035400144038078208900d00700310945850398007009000030280f440322242c1e0a0040ca121072182c02c042007401003401020031081007011342060a03240c0c88071440d00380442600e0f043c00103035511f01c03020792401c1c204e9100040007403c102c0250301580c0e0003002a140b103035482d5 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 554858615 1250 554857365 554857367
    0x150721060e180f0313050f060408030d0e1e060a290d0c0914010303080106020105040c060c030248010c121103030406090b130c060e12030a0801060f 65
    0x810900600c070070340300807600150074030507544900e03a00c549141c01110140845820030034255048040c02c8107610b80740700410030003840c1c09060042004404c480c960310305440e1410066030f0b4422004c1c4940150345801014001000070b000305418048181030305c000720380d0a40d440075142d050854400d500d0a1501a03030166521000c6203015540b185001040303074151043c0700300601e148030168211030403101c00a0114ec90022405450603501185003600590350542c40c02402c1000140c100508584c90701c4c0400c40400c0b0041e5400b4212030803410001d42c4c000c103608040341001c02d01c1d40801d40c1c1805084040800f00c8040c50b0390650624450244598401c0c44050350380e560300c40035003550020761800848404143c0740300000440314454206004184c51072180c003400c54004607000d81d4926610749142003400030b0100595032103039052400010101d1a030b84c0d59451585940500d000308450000015525250175030102045c000c00c008403034888844c03250040654a00b40107000008010a10901c3d2807 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 554859865 1250 554858615 554858621
    0x31719111b0136150f020a080306150d2a020c0328060603150b01050328150801091a0c04120f020627121e150721 50
    0x31000583d211014103031284004488043c1041d88041c0038030401d80c2c40da031012070403240903005289442181042d50319420b4058009140c81946209540003851030900040741001120740c44041117800c048490b42e0022050780500402c026036070694034000505000c40700030441e8102e6483d120039600000c1107209412a200c07200f2401c00ba03015805110620071040780c01280c0f41500c01d41051030002502c00e52500004d4400f29441a110212221004e144441690003201e00d0100300382000d914504200c02c10180c04100306815414120800243c08182a015044030884104c60b80659803120b0700c4410a5008001584086440c6c1901181e401081c54000003e5441040d02001142c00e040c0740c14018104001d18480840d00b00c016041744100580e10301015022698642c42c0119040c0081c03405503640d02d8203020303514442e503080200c0c4806910b001500111414201503854203444038080160f24010480d00c240c030703a0211081c10003141c079901610826148990b241901c0c0c20b59009040c480031 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 554861115 1250 554859865 554859913
    0xe030a051c0b060f18041b0c0c12050c030c0d02090112080415030e060901020c0d05160b01030f030e09040c0e181002070203070e070903171911 63
    0x4110180074050090818800150611035045008a00304100d40c00080311503200c1e810000030501d01199100900444101e0005c4a40040e9020007441c400c0c0c1d01034007000740b01c2c00300d02e02c10002980c80310b00030419800ca08100504500fa00403104149925101d901c0302d000003007250281c4a880000c800c10b182c0000c5c1188541d40107001d0980c00c0c1d0a218041e50040004c0c1d4047d542590100700c00a4100c402494880301003042c0c0d80c2c00107160803964640c5090a5001d410740300c0503070041c8030514032103102180e010004807050400a980b1351480380d44c10240445003001821401c140c00001040c4154441010758240c402e80c4c860040e101583c0c104204000142e9025212060b1070805000d602e201e540395a41040d403000450403a200303141442460883c05803200c07102982c000c00c110f000c5080400c00e0101400c80d00102c0f00315450a028018a0302d501440041c0401405240c0e4002d085c01c5a000c80b8254070b05a20701c030700341c041031000c0503144820001c0301c10180d21400880100d00c11980500d020 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 554862365 1250 554861115 554861117
    0x1b0c06030105100c02060313030e090405030316020a060903050705251214070f08120319051e10050111010c02070308030a0605040e0d03064109190e030a 67
    0x3056900303003020710034415a4030740c80009204403000b42d070001d45e40e981d001d107201f80b2210a42454005851400038524220081454040d400c0f000a0000003540401580c0e4000c40108003070b0200f05114000300d2401c100f1000c0071301481d103440389040606900c036000f0002e09000303100b214551031803e010500081c29403081041122400388041c8503045c0602038070070307815021300c0171102c00c94041c1181605080250340003c207101e204142c00c02c1002e00c144021a60200411003660961410660440100c24040840c1d0000c0d6520700000d4001c3e450301d0488269481040e903820760510301000180a105028050503000ca02410800c4100040c1405225100862603024210003484d59407200003d0304043d04680845d611804007060700e49032442000c0943c50340500a03c845007040c18007404030356003904400c2c0c0d189130200480400e17108100082092010780c680c41003003c404900e040b0340c1c000d14189127560001001040c03201c24001c40c1c0308269000c4400c0e10401440d45051582c650f00e10a0303c0100c4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 554863615 1250 554862365 554862367
    0xc0911180103020f041d010602010e030a200a050604050c0f0d020d02100509030a050c0f0927070b1603031506020a061a040e03030a06080109031b0c050303040801021b0c06 75
    0xd410307511a8000d007280c0301510820034186900d84248107201a508140b1070b420907030f2040104104ca9090003160181151030002c0d42c98203551040041011100729065101c400300c041c0c00250007038040040c4009680c012042d1210f605080c03070b000d9212003558910912031040112008024900200c640c1c5030154018100b0080942c6542841004414032100324103000c028407030600a920140908580c451241000d0045610750000b005402440c0e082e1841c0148090700c01c0040038030794074002582c00d10102000602e004a04006546031211540003038070240c01c08500c4e001c0800000761901c0e1103a200b51003c1c802602c2c458030a103a4956207124190060340001c107000d02203880d41d030020449000100200300c0400c100404074040c1c6001600c2c020301c4c0c0c0c0c0b0000420105c007216108400250160070000e021160054800800304240c0038a40c1103035402c0000d07d0000c014996124100404000c0c0c150780c0c95503900d00c001c600035000040003071010007030b06c1410300c3c001c01b01240c0700c0e85c5400010549 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 554864865 1250 554863615 554863657
    0xc090f03120c0c060e150403020a17010e2b0804030f0309050a05060f0601081302010207170c0a0b0a11011407180f0b0304021e03060705180a030c0911 66
    0x1120102240541e4081449001e01216002c220342c00001d5000c2c01031610f0303c2d40c1565888041c070410383d0f400f02803101004000c0c0001c2c80103903035001c2c4000c11240000040c3c441014101703d258014101010901010b1041200c110a0700d403440c10321f428400490683d40c04400b105e544203071001002182c2c000c0009001000340101389020303520510049004070221851920035076034181c03420704107461100036508000704001d0590fa00041c0c050303000380d82d00e1490040100681c000b13580ca0041e80201c1c001680c1e800c41030912980c0030040c1c0c40b401e81c0b00070500d1000c20340d501d1540000d54040d40203280040c5520b80c0304601c040301406804000c0d540901400e01e29900c17464111101d81d5540403080d030081e0070100004852813a848580007038280c000c023255480c01d00344104080e8071486000c026842c01103000000c955503003c600c1d164000613508140303540d03820260302e010002a0200c18642d104050400110a00580703c8202003581c0f4041010031000c5500312068000303016580c0c0d248244030b24002c017 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 554866115 1250 554864865 554864873
    0x2030606011d09010b0c010b010f21020c0313050f03030405150c0f03040f0519083409090605070819020d02040b0d0b0f0103050106052d0c03030403030c090f03 70
    0x25069840e00500e1a840c0004282e0010300009400e03400840191310200341080184020721650741000ba0908010040a0700b450014044584c0301c01003101c030341841d000302c0d140f030345040c0c04980914100c003056a658246541140101801d0f60240340d014002030003144c8034a0400100b01c8065860050003c2802200750703000c080c990f4014444030388030340a40030150800c95400c02c042d20103000c10082444545080c4028000b1485040102100b02d07952290301704000c407400301e207801c0e00941410030503899010000c0c2d810103c207014400c2c4404007c0000d000200700d6a03d42c001040c1502c10703a0b051215445200049800c1c81d01642c01d41444810407118148541e170550003000110060003001d4207003a542c1c02059050b8110708613410702c0c5601c0f03a10584952515120100c0022030909081006d541013000041007800703038a29400707400c8400380402d0110305d880008600717400010394100d50703605d0304000a01d44030380090710104c0100b801c150f42490450300407904030054038a014807095210b031941e11 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 554867365 1250 554866115 554866127
    0x4090603080327101e0c0c0b0a0603080414010e030709061701090309121104050c0a02010e0105091b0103020c10090c080f0606010c0609230709061503050c041d0f06030a0203060601 79
    0xb01c40303011002170f80e05294000300640120050301e05c01d511403151220f260b0514980014005000c0ca19052130300d0000c2c030010b0021001c3d1810744142407036103d03803405c0410058400180c10040c1603454401d40300000381c0242d203900711205903075000403003003003103403003081c0c680c1c02c0e29030b00240117010800416092141104884810f8a014043e204001504090700082000c80702c2c29200f4010000001070301415590302401080c070004a818000c112920b460781019469070750103002192a480b081c1c40c101900e038030a40544000c03104880070b0f01d042040222845009100e14403040b100000107803400510f80343c0102d0329054280210340540825a99440116041d2810000458496aa9499180201e4142d95004800c80117402003900c04150026805182118562040902d141805014000039010418600f050146400e000c1241e0321f5841241c85c443c011034001e003840013000c9946001101c07564155900030000200d20310b145031944810b041d01e4041508001c3d4255024102152080d40b00c2c6c0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 554868615 1250 554867365 554867381
    0x10020705100c140703120c05030f04030e01020f011a04060b040f1215020c060f060a0f030821150405060d081602060f0708071e0506010605030604020409060308032710 73
    0x4030f043c180b4424680d10400301038201840607000542e0a006101d610491072280b400e00c0301060815508500c0e1403a81141039130340c01007005041240300281005130f64001c025504180c00d40b04028045207802621342e122840d0750f8087e141c440c0b41822800164089441c00b1901030b50f00c4031244413049800c0011070a06040d01c0c100444038100c070a00341104550b101e1018141000c071060117000d160516550801040780c01030702842c450084c8940c20400843d01060900490b640301d03594a40300da0405445034103050b10b4100404801c1c090104000c0307100300c01400060407000480b4100b1040e00d0340010300070f090380441001402c1d124104140420b4001207050042c0480c4002d000c20b01d003e1070012140c0d904c0c0c000c24401c0740c199402003210410080f8504a142e0880b8945c0f0443d442c0200b0758031599541e110600c5044d052100000100e06103445036011500030b130030151005e2140558a03e03001d0404d0b80101e8444243c03909010101300301c100c0000c105007071601c051008102a02201403220010a018 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 554869865 1250 554868615 554868617
    0x160903030f050f211803030601090315020c0105070f0f0801230a05060a090801050609090a150e0303010b0703020c01030510061b0b0f160c021c02060d060b09010210020705100c 77
    0x240700c1020b900d001031320082c0c0c8a01c0000ea040c0380d2820310030042e22012051841c03e4159810910810005076409811041101e41007d100c803581c40440d00301100a200d00050390030345508140421070391980001c0c0308005a504c1d030352560b13000e4038500d1007220388800a00540c1034001c0402c40464800e100c0072001444994010640f01c20070f980d80c40055801d83c0000500800309920301c0d8100701021080c0300b0283d0204055403080721510b42010340c0c4c0d40b1000e6031003000300640d502d0840030910000d6580026071105846d404c503996544c4901c000320164111400444c0144a0141c00c8540380d446801031a00401209000750016401c0640603105010b00310a032f845011001e81181022900c0748042c98082c011401c01303040903003490010111202809043c850034010911020001615000b10f450310b1000b032106400820aa03030b10009006200c1d06400c00101c80c201440461000030700310041ca0411000d80841d1410381c041c45484051380545a005070140d0081070071061154440e4001d03034826501 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 554871115 1250 554869865 554869867
    0x6070318080c1510080d020a05060f1b27010e090a1e0f0209100c171b100c1b0510021803070902042c0601030c02030f04030b160903030f050f 62
    0x100360018094500807640300d0104e0400f040c040169520034801088003080501c051302e90381e40e507a1a220342e41c46001d045c065401010f0800500800e03030030212890240b40c80480c00e0390700c1c0710034002034210100342010590b140c07c0f200b0640380113600840d070403094020050101703440c0e40e6400000d100109041003a0340645240000e0b042d12103000d512900c0c40e4081a802c0041c2c03a10650310074819200803280702c02c0c0c1444816810034020500c1e44803000584031030381c45455503aa031011202005405a5010382c00755210f800c0e41c0c0340c00b0300d1054202040203e21503a51090f000c62a0030403640c4000e580402801c1034016051528042805400410305908420141d5483c1c200c05000b0038905011540130420807075002c1003e10480c10580321003e40c584113034822000c50205807000d091a0a0042d01c0b440c1030503600e02c2c41a640e10300074002d45140c1c8124025241e00e4076030340d0a203215090000c8420600300c1406079007101901d400340c2840b2081c0c80c3c055503003003071143d81c20304296960f82c4415100192070030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 554872365 1250 554871115 554871133
    0x304050d082505190801050102120a0207050901030f02031b5a04020306060a0e0f061b060a020f0301030b041401110c0d09060e0d0219030605060306070318080c 70
    0x10486180252081d903480e665180840f2200708013001c80c508002d010440c07128010041da07030340014a1919049e01111807582c03104d6100007030346003007400d80c09180c06c00741500c000070500400c13401c444107880c000d9050360040c3d100103007a80d9611109002d0320b680091340c01052910000340c0209841c00c9c0d42486295540c0744a40c2403644980c03480b4a13aa500d80504040300c8105042200b90f04559010b002d5506604505000c400603c450041c080e0050400a2090900c400e5554500000d201100d024001c1980c0d0740b500c581554175040d05042140300d6214480100304205a00d1084944a1083d450740317509603400c42e581c2c0192a00082c20a07200c200141c0c00c144114903003803007024010400030840c555150710140c407041c10890034481910034020042010441181c114010a038600001c58200050309500d2000034850f06c1301d941106500f83d00807601004210f1554060b42c01808110300b101c01f640d0b14680b041b01596007040f0b101e00c0c4d2800c1d20581c240051116005041469640025500118 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 554873615 1250 554872365 554872411
    0xc03021f020d06141801241b050d031419090201021509010204060915022e02070b0103020301060f18090807140c01080a020a02151003021e04050c0304050d08 69
    0x1612600084404200c58001450b1441d111240c528505c1e4100503582256240c06003000d0702001d12603400364080c5050030b240140038483e1081d00050403072075000c3c52959115040543e80e645c54160b08801007031804c1c81d64821a2400703011244109a00004010040846c0c60480c0141041c100d00302d043d8440c0114881805044a0010b842542d105000507107891800500808910403588009542c142c00d83c040400c0642c0072514100d642c810072201e40807050b40300107d9500506401c6850440d62022404400700034248510314101ea000310024006203440d0244c6d03849020b8907101c0c81d280a4284a1080005011500500c85080c05074404606004441e202d45d0751024000314402c80640250700c071031641d5070700700b11504d4012032100c8085040001c000d8001c0d54606810201c0a1903294880018101907012281a00078590182030074810141414103014040c40c4034120701d101341d003410001200d07007031030340152032041c1d810100030040040916015148064084e0400702c09030780350a0500180c3c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 554874865 1250 554873615 554873621
    0x3060c18060304200609060a0809190303050f0702070503070905070e13092a03110303070203030c03040905011a09190b0301151b0302150a09060c050c0d0c03021f020d 73
    0x291340550109902841104d5004244a01e1440f84d58419002800f05090980761030090710541d0185080110081e201d00f03150074070f0400345004002018500c0a0300e4000c05915820150040040f415811450349580101f662103e40c42d0050b40c0c4c242e03200030420404507115420103504111103003000152600041c000c186801c00b01d11000a110345c0320342e070f203c04000c4440f040f80900000201e50b00b0318401890303148a0075400b40d10010f428011007048044079981c09200300c0d910035500404030303039603800c034142c2141d00c0303421600ca03d04426240000000311840ca0100800395608118241458198200c080040800340c40800003000c141d10103010a03c104002e004502812880b07540000300c4462600c0107203509403030801d080b503140420001d440001d800040410042c195840700c0728442d40c0703071007103540101601d06014000e103007400702062080d60000010441c40748034105441131010413400a036106102040000c0059020202508c51000180340341400314014807400b5180c080030403542425 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 554876115 1250 554874865 554874871
    0x30d140714030a0c1e0803130203030f0d061d040c09020307051b010209150702150c10150609120c14040e0a0605060f0907080a050402010c0b09150a060503060c180603 73
    0x400c010390500014401c4108440c0401045c10504d401004415501c42c2c4050201038044129000355070003210071950240244e903440e065103926151284000602d40000d0a0700d84607005c404a00c00411115045281c4911072266401ca29200c542a141191400003988014000e034100b000500101c205102c480c1c15072413403c02144009a143c0321902d003003220f910140c1c071001b120400c0401044005884a5940801c00d207512441e2940b90b200420380141000350356068480c0f01c600e0003503082040359200032a0000d0710115514200701e2a00d811204199410f4083e0180501139050030030400a801d0007400500800050404913407100403840c110f1800c4542d0100321011625002088003500b0500e00d5256500c900300c0304611181090800502130382c070054924280b1603100d40008040d0b90040040804156224117800950301e00082800c1c2c45090f000840c0440703800900114407500540d000c0c40f03050f03403002009010740343c0703410700e44d5100d641c0004245640f0143c0310f101101c05903070310005144 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 554877365 1250 554876115 554876117
    0x30311070b250912030203160827130e12070b06040c0306030309060c020a0e07021f0b0a050d05010e0114010f0b0711011b020a090b0301050105030d140714030a 70
    0x540b4102550001e200b90b0511000b152842007140c1c035075001c10303072202050048500b6407941c42403207501c50500b00e007180b1030001c0d94000200d26412650030000d03298010201e800b407102d0542181e021104001080d07400c12844c0680c04140f0f01100d1010f905550722401403d0134030b40803a40d0140c003511040195820110096030065103000411a8030b052601034004a501285020080642036680c00b0307281c954107002d11070401070f07030264820442d241e400900c0d02419054100c500f2519144c1d4001f0350301e24240401c1c04140080840018849265008000c503c81e8003d080d0001c140c184428000b980c260014269925900d4405511080100f0b10030020203c7c0e445014002942c18004044030201065010500116040040901160010100c0c444041e82441c040c0040910349540c9800e420704a03901a500106004000580314181c1d486080740c11020740c020301c1140e90310000c258a50801c2000354020070149013961419010c000000d2038000c2c840d20710181080e4290000c140b42da0848051a4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 554878615 1250 554877365 554877383
    0x20a020907050d0513170c010902060f09041d0304090f110a030c0816050a0507020409060c02030d180f02060307050d110301260c060a021212040b061507020d03031107 73
    0xd00c45442070050700d40c0301795216101c00d08019690b40d80f4009000380c4081e407825040202d5040f9600d00207402082901d50018015510b03840309480b4080303607910100b00e0911035464407643c00d40c5002041e081c0000c140d2514091820546084071000160030032424601800d50748040700c03244100141c01500400d482c030780c1d00058803113208034040d00720030015009800d06296241801521544002200c8910300b4a01d03215898003894401724010381400540288424200203004034160344c0000079051800c034603030301402030340c00e0100e43c040400544030024003403050228096015081000046400044500d0824a1314440b501140201c07000c1407168003440c100000108041501c451580954803840700fa12005880c40e01e03245580c5030384010040303008010204104501c54024040c1c5d00d005145550803a5848a00c04038059000d20215070840d895050900030a40324140f05034240d03c5d100030146064600038141d000c100b846141c42800700c0c100360711850b98100705c900c81c00107040c8883c850400c0d1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 554879865 1250 554878615 554878627
    0x5010e010e0904350a0c030c0b04050c1003020a0801050f0109031502090301110a23041d090f03070308070809010b130b030f01050601121d030406090305010c0c0803010e07020a02090705 81
    0x520841e40c0c60324500e011020b070254220758a68010001c4818503402c03804c006c903508515240c29a100c03003007054050403001e48801000180f10001c1741500c20761008403804070a004086505030f00f03d02038181d050002800000060116081c454140d6551003014100310003030342e80e0f03036480031445015600700008840d0007080c01d07013150509000b481e0221420014180c140400340304001d121004444120078144155110003059505502c200e42c050700100d408028000500081e04a0004c000c2e03c03040030500c80e03400b51088820001c4140c810341c80d07140d81c5016172034480b40c40032074403214081d00c11465956108021100390760780c0d1030204d07058103052002046480c0f01034105414034910300340782d40041c0d040c08202b001a030791100c030381e146800b481800011140e904c0342408652001d06040041d581c803000502044d84e0350042501070489101310000e000b1000381c03c0b011182c075401c1c4000100640814001404403d01b821911544903016204545a080403900010507140007603445001007140085e40d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 554881115 1250 554879865 554879903
    0x3130f1a0d0626070b031b0d0e030d2301081e0106120b190506090a0c0e0a0f17031c0207060b03060c03090106092702121f0b031605010e010e0904 64
    0x1518000c0c010222146d0a500e80624903440d42d036200c1c0300c0009103400000e40040c0903011540020a200c0810007243c0e210598114101c00a04498003118664001e50100b041d0300603603074400e241a01c003108085c00741c01420000d8410054040708140140303540b220740c0450300182c0c080807081d046000b040385d50051b0070056405410034108045038900d01d4144030400c136040e110228425002802c43c2d0b00020f00d03802000301121001032052141ea07101141d03060018002e0318034484001543c0441c12401e881c45401e0a1103591707841107004528950503249008040301d404c41c4d000e000140c0c06007001090070700c02500080e09140c0c0440e08043c003060003109005210009104017005050b0444003003111011407030101032441400c18900000501d0080170400719141c0e50100404406a03004607011345402840800c541815111a180403500e40705500b562480d00007804400e404032104803c50460411004450b81090040e0f42030600c0b150348030b4010561240c2105030320560298400f01703444910b03454 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 554882365 1250 554881115 554881123
    0x50f01050301140106050f090406170c180c1c0c0c03090501090b03010315020c0a0302010519061203080c09030307051507033305060c03130f1a0d0626 66
    0xc640d000b43e250004203400128414034a506443c0c05041040d00c45003100c076a03680c0c9114144843c0e411a0402000180718124240ca2010f140312200a55104015140901c10000348030651000001503e4001c01c0004484000400c0064031207004150303032040000c014420f0f40c46141c10b940c00680e05420100a241d402441c103c06040c003440d110312140c0c5020220340c600c3c001800041c0c41049031200d403e0115100750f0440b08150311030381c00d5447c1ca00380f504001c0e009042c21559020103014070104010710b405c03e0700c290780c181c6407412814129103041e500c080700d50401c018903403002484100304041c030541e410805419100d03c01c00007030080d908440000074213854064015000c0c1420044201c100c018142c59001000311400180707103204144c45d020305070481856000300c2d001200010f485000c0c40380800141151101340c14a000700760b035106288040034003180305100300035074070500400c0b0000454004000c80030b628200410210b840d80750900c0c280014401a407187c810390350701e8005141c0144 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 554883615 1250 554882365 554882369
    0xe04171908071409060904020c0715030b03030f0f0c0f0f0a063b0304030827030c1e040b03060106020708060c07020a090c03140c0a141305010c0c0315050f01 69
    0x86043c1840c03410f12100d4004900583c91018403510b0301084513500d6458507816140c3e0f4000310f00442da2200e0381e03444006081c1c4026102c19001a082407540c0145050003c2101d2401442021540c94280b1018a810762070300044070500050080c1000c0c040000c81c10014088200b208101070850f4240c0f51800300220b54200c2d00039402d036200b81c081c20118203440810f110302940000c044030901c81c2c544801a00398840da4000500800010800f0002070400c2c042a0402000d02e500c106200d2119034205540c0300200000d107a8004010004016a15000310400303000040c00303040450240f01e00b4000908044003604842c0050b8800fa20400500d0410407a480e00500c08000c0c2a01e0800390307030003051600466000700f65005e82c40c0e02e80300715091303c6a440b207a18080064100700f01420a006c6007501d80e8031041200002841100301c444108110384111950980d4501d8040803181c60480150b4962500c07141c00c5d200c1014003c00080442e9007150641c0700001400c80015192600c0c03100750050020607 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 554884865 1250 554883615 554883617
    0x1090c0905090c0a021005010834091e021803150f161407141c05070b070905030f03030406110403050a11190f0315050f010e0417190807 60
    0x50410071103a1100d805003904000f48004095481d603e5103401c0e4680680c1c034680c040700c180341200009080d17074041801c00d054015201c46150040394050644800405590303404040031b0308143c03c2100340400c0c3c0c081d06004e140d14401107100425001110200c0c0c201500e0081e5210001c0c444000c140b405102400340881c820710702c40c1c0a410024031200000c80024080785044502100342c518044c0107007001c851800b9100340240c1d5881080c07411840420000e45141c2c0144598040300f0380b44058000950b224518036511070307040000c0b64480e180310407400f03400c55082c4110290082110388041c0309500f0740413040700056581e030905107050300495140ca000170755524024881400040c0010032034408454005440c240d210071140e001484031901c103075041301c0802c0c00110000d50113540b00d94000c00c82c0d02440c200308c08128100018000c0e66021034901100d01f8000e4014002c20b07008595454115018081c5280d51907112101e04920b640400740e0765040f0107070901c20340010b40d40407900542c17003016 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 554886115 1250 554884865 554884877
    0x120c180e0118090213111306050f09060906070b04030c0515060f01120605060301090e060603031612020a060f060e090c1f0e030102030a020309070b04081c0c02120601090c 75
    0xb4006818403a03001e0600044100b03a22140c80c0d40c00c1d9039440380c4803202e6013031411003002400ca4410b000901c940c8000f4100c0e4101080b204002905401202034403401d11900d409145040782500400005520840c02158003075001e01c0507170b001c07079100c20507070307100d21310030341b10510040b286003000342c6002c1c1d0080840d220381c0c6d000410004503803603c00701c40709210030a080424400451004d003c0103001160006900200013000001d80c0c40031642001d024600d0080c2541e9540e10b03500d0074940c481c0710740058038500d24070082007240040c030f40c03540c3c0c142d0b00030b00e52040d2103461003999603540a590141200010042d00c60b0b00c01d206c480c0d0501901074104003018028250301c0c1182c000704083c10f45589010000711a07000c40101e00340d0040904060a0030001c2c021982e03803a181e90194000c0d001070741e0100c003500c600d14010803410300290880303068503600c3e030041ca0302c20600c3ca01001f0004a420300d8804200e403108990006840f04450030710364241c6000a03000540c140868034040702d11041d40c001c20040 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 554887365 1250 554886115 554886119
    0x51b04030804060e030a0f0501021b07030c0509040305040902070c1404052701110c01060305070614030f06040b03010f09030305150a05060706150303021b010815010e01120c180e01 79
    0x103900701260308468007820510036841a8a000905205203003502818841d070171640b15040200650003030900c00f07071444040c1e01c0c100e444d0440540d1000b0600005140d2a909403051046240c0300465039071040c402d15001d403030142c54a100304142c0e0040b5000b1200c403480980d003884411000034003035a002034151070070030031407504401c5c0b512039101c003503100c0d0103803c1e0a51058200041c04e4004401078010750711055543e40401000c0c5009041620007500c40c1d004102010070964801d902d1140703c00d000e00c101c542541c840c80c201c08403028003d84030580c09503440c814074225131001c1c052125151084e540000b0314002d1402c008c2c056400c001e05001c41e0301458103203008141c0e1026280010358005880080d1120b08a00d840001001c8807020842c02100d02d03040001010b42c0058000300c920a801c613541b5401c1c7d101c00041d14040c4041e5031038080326403248000d03a295403040c8024180d00c0414542400e451540c0600c0c3d10442e600c602c0e000b0002402c070840051103c3c012440d51005050028034141158 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 554888615 1250 554887365 554887373
    0xf11030414030d14060406090504020d0311010b09011502070501050a2a2102012307030c09050a08070501140c0307020910050414040b0702010506010801050f030a080409051b0403 78
    0x110004200800101c810928144404401c006075210b52101c503c040000444480c0b0825494008880141c0303d1400d11001041c184018007500d401650701400a58000b180340d503007a6500c0f61524032540d2903650b40c84401c02a40d4032111044d0091103010860340740707005816002424111207402160500c2010071001e403180383d10a04000c02d2055601e000e42080c07049068080344010b56880141c0341d0a81014540044e401d0703942110032200d00d0b50000c020100e40e140c0c046906e01c42c1d13041e020500c84d29540002c1c035014005d80294044500610700100095241d0b00080c002c6100c0741c003c404554407401051220396000303640344c00d0f8280e00c0c070982030400301e0000341c85030b41c0e101e6444000c3c05008140c0101c0c002c4410030b50241d0103044010000e00829020b64801c01448104440980c0c1c400030b00000b01c2c41c103500600ca41c90090324107135aa0340c070603820841440b800500314100540c00d8450210240041042c0801130700c09000b07551000300e00d5040040c40c88040c1700c000e40c0901e40343c1c5e0040204000003 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 554889865 1250 554888615 554888617
    0x9051510080c1b0303040812010f0f050f010e030a03120e070810150f090203160c0b06040e19120e010f0905450a0903050f0c030403050d020a0203010f11 67
    0x200c18505541c0c403203001000440182800100040f43d20010081c030041020400103070800007041d00d40c04507640c0c3d850040c1b0b0034086440c80f4200e010100801c0510050402c91000d800552060400700600c001c80c1d07012a1400f461108260001504500c1900e0720340120f0088603d04408400188055802c0c041c00c03980b144c0001071403840c840d903650903441d1198910100c800c001d10841a40080d95a5140c142d0300c00381d481102c8940301ca20b40c0035103c072802070090000da0080354112164078000d41d01c04c0f003440000c0c00c1c0c43d41c411240c0d1044850180c0e80304041e011100c1860f02c940c8102d0b41110560801070a070f051160b0040d81808180203144500030340c4030307031094219030007124525100300b15080f1914080d0062103221111480c3c0306001c5003901151041c074006131140101004c0d00360741d08d01c5800e04440340c00307a004000031403c1102110310f21049000c1c0110010060603a0b2a1079030b0b070b03075405103040081014a400b41e023140a1680551800703206045000144174000d015586803050700c4002 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 554891115 1250 554889865 554889871
    0x11040302150c0703050d030c02150103050a0b1005062709161b020904051c0320031008060106081b090d020105031305010513022e050c160905151008 65
    0x207040030226007001425030421582d030096401005864400349400c0e001805028a00c0345400548183c085100b148034411000038103c0350084d02402c6110555915010700c044003070042e85403541d4500307000c101039440000524503260307525100301023015517002d001c4904640d004150304c90302e607040c00c00c4022800001e039160101160300d000d800340f1081c9502d0860307c1c40c0b01384010b034005600c40104810013a0001e04a030300480d115100b0030000c010418205e090700c20081c02c1c44000c0a0b2440c0d441541c0304204040c43d00203e510a0408415844220280c607047c400d074400400580780038103000c2c4107192191100ca03003150000f8101d182200c220082240e503404a580241007200000002d22620718403485284266031007402480a81007030b9910b000000e1010b04140d02c603151a04134481c08000b041e00a180c40700211140f60224000900180d4a503044030031811300c01d000d03125182d031107255000ea84d1005018501000141b0b030501c0d03032900a6429003224070070702801070900c0c1301c4041500181c60701d034 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 554892365 1250 554891115 554891149
    0x40c03020d0f060510362019090b0301030206040302012d0f0908011a1005070611071e03080a0f0f050108100e030a1e0e0306040f0611040302 62
    0x40703075900529201d8501c58a41c0da014060a02c1e120a020049000c01d8001003110389001444211a001c001002c1000060310890080b41d002401e0481800350650041c03040480d417800070428080d43c19482d4140c5500105000c00c205858082103207041c0c1c2c00111360000b401f1144007050079503040d913000c507102d0700c40e9010207810b0001d181d006640c504001035030002d240042002210b001c0c0e0b80010302425040480443c1c00100c0d4080c0307400701e100c180c144682d400030701043c5084500c0320305000c10b0003041c4407200c043c142048004c00c60900800c4090103100c030044e4200701c1041d40d503030380b504051051031484000c07403100303102c0c0c4d03044000030991224800c0c0d0840303111080000e444e0062590784000b8404211a00038044c18100001064080407a000024440740b2206100001998000945074460403103030401244945440c3d01d0281035007041d07840101070030b05080c1e0f00b000c00c5000007454400c0803203080345d01a0382c080c84001000090302510303400300840101c013400c003401c0d580010401d039140d2944903 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 554893615 1250 554892365 554892379
    0xc04060e091009090606030212161a090d0b010e0c160b060609030a050718060e070807210c021005090a02010810030c0b130510140a02120c160905040c0302 68
    0x20b2803001d0821281002002e510b40100a8a120703860220043c0495100581c8180114480c00400030703400b156111000f4040301c1c102c240d182c201032000c1141c41517029400704c8102c080c1301d00700b6180c4520240160090150f0203103030300c640c50440342c2004e400c401010390844180c00e0201c00b070f8080e00b00034030010180e80400700715421340d5000c0100d9650700070618500d0b03141c4070f0011b1036002d100f80420124242c8445040c00c0804a4111a140d42518124801c60030f09044030b10010b852544503100381c9802004914000004803e8004a4200e0136201e20011180903950303076959541e80e404000380c8102589942c0180b0170342ca85400210b8581c1420700001c0d040c8803050002034414071040c1340030f02c00b0b9607000c8c02070152662248580b0700c1e00c0d041151b0302c0400c6009a0804506490080d15082d003219a40d550700001c81d49010720441d490f0005d052160540c030400c0000060b10b81c04101410442e20450000c241c000c02007084090403aa103a03200c0c10780113103020203101c0407552185207072003502d4069440e5 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 554894865 1250 554893615 554893621
    0x31208091618060e04020306070c0609020406150806100f18030b070203030718050904060b01050909160f030b03030d0e120d0618180210020f03030a050405060c04060e09 74
    0x190800350192200300006007421404142d510004442c260214440482001540e442da00c0d1500408000c0d18080e5141d40302c0300c001051580318104a040c0030b0b03c20000443c0340718441d800710f07050f20515001407018100410581b02e0741c40d44006442d41c001402c0b9034446042c40d0602000d0490072400700150208495400680d003043d4030404508015540411040714070b14003418000d403240c009a44481c0050194204241202d00b4681c4031011349000500b4541c4a840e0341d603601d002801c10402080c10300c24144003000d182d81c1c41c41c031b02130320030f40424178044200100e01d0f2006042c1480358940900785882d18404049585001080d00c03540722058100091042020000038540b880c00002d014441fa000250301480d007006422030343c21542503549079109210300c0c001010541d05808400060411780880180140c42d0a80784004034100600554102c1c0000100060030f43d0b1007112020000760f01c03441030208001d0304000081c2d0101740c01400504141c00c0c00300c014400b03010850068032800c204808 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 554896115 1250 554894865 554894881
    0xb07030b01090e0f1f030312021c05090c03060601171306060e01061214040f02130605041d060108070f09020d18030f030b040204300204091b050307031208 68
    0x40c400c090594030b000f03400715140094142c650080110b80e18004101c00885c0011102540d15031035051740d84c56260b8503c14140e0f4817040000f90403510039440a04510300202c02803918a1240601400260024020f60b20042e400d03d440c1140140c280c0d4104011503802e84640452070481c207802040400b120b410460260411401500750740c2c20220417040340000001e5100c0d00400110b4070f14030082400c1c45181001806040c02d400700300e60141880c142035020900520301000c00d04108003c580002172520784031400b00c0c0891360365045201c40080c502042e8103034541d04004150040c202600102411420b11500702110b01252048492042d008682145011240e4100707120215404103102d1194a0908009240d040a050500c2c013203483e03d254140e960138540225001d61304103140c086d003001c241440c0764000c9181c0300c110710580310000078901e0050b6202c2c003403101c6180c092000c1c0702c0303072012000d510543c3c1d0109600c0184030303a0103040100f0000d00c50800c0b1845494550505450650755001 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 554897365 1250 554896115 554896127
    0x30603010e011d07050607030e01030510090204230916050a0201091a2d0105060d1512050f010e1209010e1008070f030614040506060d02070602041a070b07030b01 71
    0x40762410950804121040801480302e00c0f03422000050200c13003856640b003040c40b41c1c600c1003c00140029144583c1c4c503106500a4122503049015101003440149c0c0d106100d00c00c070307006900943e05008002c0305141d000d00016400c2100c03031070200c40641d07580c1030006080a034034408809440a02c00041401000c640c000e522880c031013030300f0140e07803040403c0c0461000c1114500b00c40c10350050000100c640703410b50828058803200c0c1180707606042075908207020410181c01031284a1241e60b03c540a5208107162840a10020a0a480f00c15041182481c03d1414410b4000c01c0c480715a01d040140200558000382e400100c503e5141c5155480c82601c004072040748054096a4005881e5100340d10745a600101450ac2090341f503407030b4002c1c900905421001d44543c0e12896109448443c0040000c0c9400da000c1c607000200100000e1604408499602c01d98220640a0303404550214080140300812400440341000c04260303140352000903664500c8482d00038207a20704150b0ba0310100340540c2d00800d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 554898615 1250 554897365 554897381
    0x103050d26070c03051225030509150a20090f03031201270e0d090609050603061e13021806040b22050d0c0302030106051005040b030606090a03060c0e0f1503060301 72
    0x207400304606c1d01c2c0032021840d03403642c080c005884000c0d5640005915612a108081c028076a01c03014101c42406219504140107001c0c003492400d65641031041c8000541101d8420810560f1710f040c0c2c0c84040b000100240c03900406442c41c001c5e0810046c0c40d282071504019141950325002c1403549c800312401145400c034076519410380c00646400380c2000403010028041c40c0042080c0c0d2001007013074861404403004101d61007540d070002030500126a241c5848550140314107205480e00c45000041c000142484181501403030b0000d41c0054840c0038000f500041d00043d01040d1580c0b0302e440d10384000c010852003001161300d950400c840900036144841048100103110082030f1001002060400310900791130303480203e10079031a200340050709040840714404504160740300d80d402c0c54501000803030035900042000d68000320400205078165103040a810186000300300000b081c1c0040b0001400d220080c40c44284502e0074559001b9483da100d980c220001950310202039185e88841000c240500116 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 554899865 1250 554898615 554898637
    0x43302130b0703050d0501051c17070506040b0403080121031809020301140a15080c1b0a0b0f0f0606040b0a02070906030b09070b030708010905130204050103050d26070c0305 76
    0x42c0c0e400c1495403082c007410725000c1500c010452030345d0712010400380d641c030030319411140142c03890140c011882c06940905000c140c20401032615a0075680c8a080101c1141c1c02c454050f004428172050550001c0401d026010111a1181c003000c05030501d107580444039001810080680c1510702e0348684102588014074031703e1000e54076961a80000000103003102e5285008040e1600000b6034440c044240505101d4036071100c0e555506c50b42000c5103a40e12004c01035049980320f20340110810030070030041ca00382d401100c1c1909070f0305000385501460f201c054012482c0c070300e43d030040c02810b940702c0c012541168040014507aa0f0010b100c0141e0600a040d44014085442d0050000c02c3c0112020390700d00c140a00d0301691016a1101c070050300381d02084c0c2e039060003e88031400601000745164407050700850b88409079003000300c05500007420744000b41c00480380c907040030191591040d080124004011074150b1040d403001d607401d030b0814900000070044020010154980b10500d40648100c0b0307515205 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 554901115 1250 554899865 554899867
    0xf04080d150f090c1404060309140d030504031d10030c1205010b13080604030c060207062a021b1f0c0510021206150a0f050d0c020105043302130b 64
    0x40c03840300411004452060303003200c5051540c000d450502c2170500b00b4044440e4580c580c1001c1c20403104038000c0600a50460786a02025261905100d0070402c180400c0d002d071f68041240c2c5007514000f011000c410342e18401101d03c005040015581d074501c8204040103d00c0d00040c40d071118542103812003000c00d06110f40314546000420099002002418241c107000700d908c62072641c403040c1a03540d0a04560190006001001031000111190000c003e21800b801c4042281c840c0e41c480900710882e81004811280c2d69036410125070354040c0840b041c18842602c010030041c1042001c11280041c482c000540d86091010f8185024042c3d401a00d8264200c0304a0f07140c0e060024112001f944a0a84043d12152620004003145445042c4c010702e480480141c50078141c45582c207407003100322600c3e0801070001c1030145405d01d828510400c0c41c060903035030001ca00360403e820566208612620300c482503c2070061140d40c4040801c1c0c2941d0952003a05005a4032405079901000981c404e82181000c070384 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 554902365 1250 554901115 554901119
    0x601090b0a050f0f09072a020a060806090c0a180e090c030106080a080c0111041d0606161e080c011d0d05070b07020705030a0b01170106030507140402040308040902041d0f04080d15 79
    0x1f500c1900503402d00d10076107401160350345580d01500d881804944581e480f0303800070006030804541c10050038213521a800d000d0802c3c0c45a5400240d4080f0540004544042c60320800481c00380400a600f00e03440700780d000300581ca0070840710903110b01c3c03010000b40400300005a01d4001800035403165007843e141e05c2e100340d00e548d1106110303d070804004012149507c00000422818030340801115850f0a084c80c0b850013a540c0c550b96a00000000300d24000c440700c40f07280c3e80010130076105c01004440f482c40000626004205030241e13421041c02c40d44a056802004c540741d08541000407030f514180c0100c184040e503a02c00c1c034100d01e44070081c0c110316014018a110304d02040591087e081c107039014403901c0f50349010b03c52010b5088a007188406042580240800c0109030300c0c80b1000c480c1742c503028001620f82522629050200c0d80140d11144983d076000408005a4185850390400e01d501d0340094483d40c140a41b85040d5440060b002424100c2c0c00141545c100304c0a41c0040f43d022100b181c0c08040c55 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 554903615 1250 554902365 554902427
    0x1a03010608010b01120c0210050915041202010c032f0403291608040308060f041103041704030c0603020313061d0f070308030114010e030601090b0a050f0f0907 70
    0xf030100202d4041050240c01001d900d407180145103c8400d03603030040c0003040500d151700000e04806403000c0603034002c502c40c110404000c0050f880c4554040c80209501424078600242180c0c010240710302010724041c1589900300480c410503001c890250091a0400002800601d07648181c2e400140300c0791802c076200c03040c2e185803080240c044040001c4040d059a401c41034440603038100701a0070018a500300010000b0b806245a00e801100250600103800005c82c0810200e901945014902d48000300400c330070010342c01d20900e00329070004006070070649103686440d52800b581c0a00410f00d600400001d403480345034054000307100d400003030030302401a401081e007214500c0c5000710302c3c540c054038044503652080003421404881d404a84280303140e182807040590100c070321410307904000081c404203400d5502001b01a000e45492040050300000d0030301000b1950b1a16484540a1501400d8401d00e076170743c00413586054542610201c0c10360f03489950440727003051070307000000d0880c450f510588c081c0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 554904865 1250 554903615 554903621
    0x405061e0a0314010501050a08040b070219030206010801050928082b050c03100303080606130609060e01020c0a090c1110020903060c04050901030206070312020d0b010e04110d1a0301060801 83
    0x40f2040205942840c2d80b00c200455151044c0c003241000b054440001c10005103420417036030307032080d018410b5440011515156001c0c08021450a800581c003e40051248100a1103616007049030000141200124412400c9913650b82801d00206c55500c00315407802d0041c1e00080764003030074261200e102000d4408480c00703a600035006000410310714103800110f004045800700c0c3c2c02414442da00d1003507546545c0d4129090350000304495040241401f00c152750044011241014014944640308c00346e0502100801640125180302e0440d0300100e018021512003544038019a0280360020580800c4c0900541d51581c0c619111052441000110400713040c40b07a003e8502500d04505846080d01c1c2e621902490340542d010741680008a40300400040c94220018162a4460b0408500164152000f0b82c1207070410340c90b244d1401d4482c00003038050360f401401d005081c041250100440148107540c12030714042c0748034502e042d81d900c4010000e01c00401032030f541e200d80000c000b80407890b11801d0950203 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 554906115 1250 554904865 554904881
    0x80a180818060a110c0906061c0207020907020f1203040b190e070806061c20030a050312010513020307020718150803040e010506040806150d021207080f120405061e0a03 74
    0x10303000d556408404d1b440e02208850040381c00520842c00e0848209080351822020302400b0420341d8208680e00068444a880c9449602e440d0090580c80d031081c101c0d1800e2281740b69200000b01002c10070000064582070703860b80c01a90030080107580c031404c4440000200107029000b403140c441c0081c000303003506001134114407400055441955002d4075a0100751540c8038044001c2c0800018000c06400d40c40041c105d0290000084c12944203041d01d880e00350a40e80501c3c120b050070b0101400500c040d06064900d42607201146204510710300d00010000e44841d000e001d0503d0219003580750120b94001500507000c0070007500110355503036664900030b039078a902c14420b1030980c090240000401c0e00c1c00c070341a18111076400d000340c04207584149403603003000c208113405079001312554040005030311100f040000142c2d40c8802810f12505007038005103041040e98500c286a44100700d02500d220387e02c0c058600722542502c0940d03d40d0644240c441040c0d45895141080401c0841c0c007180c5564580c008100d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 554907365 1250 554906115 554906147
    0x504021c1b080d020c0405150a030803090d0e100c1704060215130203060a02091804030c0302060a0b1c150c020303100b040303051b070e0a0c080a180818060a 69
    0x8160b40d1068660348031101d6844500c0035811403510040503041a80015510265400d942503400c42071100041411040b03400076502d000002c8100007400d030040024540b5211a41070040c0003200701c10000300014400005441045035920110081060001d50300b0700740c2d1131504010ba01c0c0d680781c0000035230b27a070350700c842e0030441161300c002041c1003020f046596401c0e10b40203405001c8654400400001035440900b0640d00301d102054105400010000c0e40d6000358842e903038501031500503090003894210040c006018007031814101c08071030b036a441c4141d030b940f140892440a4000190614010340e070284400388400070f041069082515a0103c0114070070711176242405060354407400c044000340503500008000c1074041090001510b00d40c0711004080c0c86a80454210716211021140f4a00e0242e44030b0030242d48a1400e0069550080c0403540d202a03025003c121020702c1380807605a01c20751103030150030180f001070740310080300352500c1030b000154002d00070b2603841c40c02c1301004007608034580d0708035 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 554908615 1250 554907365 554907413
    0x2030c1204120b09160605090907110d030c0215071e031401211a10090b030c010c02031614011403060d061a030a0f020406081507030504021c 62
    0x40c0c540e00107640c1615990b62080c0e4000e00d00d40c0d502c0480031405012000346128200412010b1768000031048082c1c08035030784040d2a06000401d004030700c00080c0107041030020b074084401c041d0307000203202c500881c2d691502003040303c442c003401e90a1020641c40b44642e1659581000505d6030001d089a5081ea100e492002184010243c120226505030811005da8800c1400420581004003091381464060303e40e0303003000d41c00d02d0755405000c1640d0501d204e009200d0100300a1030040310800d140040c01c4032081488843c001c5c3c2c00098980100200306414442500312503030070342d181000760441407804074031500c1c1c4054540c0041e9208140c060060382c009140300c1c10101e50b82c1d00010035a4042d01c4054480501200c00359103c001405009055040d050b000400c01030055408004000303030701e40102aa0f0307010240f240180420354841e504030140d0380d4041c1c2d882021801c0c1c00401e041d806401d51a00040584862001400d40710138000d0405c6c3e0307031010140b10002c1c03101000d420075090704140d85103 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 554909865 1250 554908615 554908633
    0x5120c0c1e06011e0e0403020c040c050708091c120206060f0a080c12030c030424140a12020f0708090a050906130213270b0d020f040e0a05030a02030c 66
    0xa200301030107500e08481500a02d0042103601c010801800100c1c84541010a03115260003d08010801c100c40590040c5d00c10110f80282d82424803801d64500c0444c54990702c2d01f50103455050161191035403040c02116844204142807580c004e03210091a03010805c0c0c030b48509003c80080d9200f00603241c15100f200540440442464a9200c1c0812141c142c00030b01110501030082010311794503002c40300183d000402502180b10030070301c001c0026180c1843c0425407250b40f1600d9541c11109120305000b881180c004560143c0c0e0b42c5011349400b0b01c03080c80d0005522512181c407001038010260201d030000e401140202c02c01c0313803620180c601c0480c26940ea41c002d5581d4020049054026035035103070040070040541c0407001880c0c0050001062903503003030016a07035900141140c1c0282003100005000b402d01d803e00400028012a901c5000480320b00d190401117400042c05040881c04c5248100c0d540c0c80050250304c3e09000382040c66800c002520380350100d030500651030398272460b0614002d0186240d070f = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 554911115 1250 554909865 554909893
    0xa030501090b090c09040b0616031b0503040b03090709050106030f050a140a0e0c10021e070501080a0c0309050d091401080f0a0e07030b010f1508090a020105090105120c0c 75
    0x25845514001082042a52122043e042032a4007178503040350000d8a0f081900a59103c5200a01c49244602813440c84044903081c0200f00325000c0740983c014007415000c902c0818000000e0320261503080c21103503926240e082c0c1013441c224144d07200c03021a9040800000300350744c040c0e1100c5c0741980d00080502090340da50a1800c1154810030342106542e002201180c4507800550180c02071404400840310450010000038032500400d0360007500590100a546031100b803580800c941f07035003035140108042030030b141c00601401001000c1c28907903507a0340099032415102e60800c01c150f580080641c0c0d461464582c0041400d012401a19a81461207200510551041505c98809d01881c0103100154840c04c2d203a60142c4a0310703903180c5007403090f080d0100c0464491900a07008110400950f41e69915146400140341c1e5114a0802801028800c00c01006404244007111071344c240703402d40d45e80030410010f07500e86c090950302d5030001c3e04440c1085202c0084c6001421718805c02012a070545002400b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 554912365 1250 554911115 554911121
    0x1a040e06030a020a030b07141303110604081908190909060b040e01030f060b090906090c010e0603041209090f1d011e0c030f0e060a0c110714240a03050109 68
    0xc1c0c000d40004c6064410000f14920000103070300090f0505c1c100c00a51628164a8655004a111442c204910b9201002004a688841c14042800340d80a504082c500004207450314030001881040c5c1c5c401d0300380c1408004214084031507003001d0030203800400c0c81c01440286001d080c0e004d400081490140081503001c1024285d40c2100c2003000c0340046607095542c0d5040c0c1083c034560459000d511460118916516035540d40d02c101600c5004040300e141c034040c91460f00481802e65414011841590440350712035004980c0c0c05074000c4441464000b815404407100c5a6581c0b04840d50781c90044840c84c540095040230100603501020084220b00c5c40301201c0c2207404810f814820078014104514a003c280d80106c41d0380700d82400d0010351041f400e201d86082d500c40954241c600e801030410007560502c0cd02c83e520240d07045250611341c0b40680c0f0324070f56503404036024008a101c100150402d00d5525030f148582110111a8500500c8000407481a2107402c40b18000c00402e00742000403c8012482c4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 554913615 1250 554912365 554912383
    0x4110118060e19030b2a0306060732061803031f05030303150310140601110a120504030510020c0a02010e040f050408090f0616021005041a040e0603 65
    0x42040551a00e4181d0070744458a60302c00d81600030740b40900b05418404900c40703060086004214802261804450a90004403005900c551541841320034060440e60382041e0795210307800f41c1d41c031b554076411810b01454030540f034003c00781c0c00301031140444030440d41096030001001401046a62030f0312810a80000c00c40c6602e8014156881440006c9038510f0300340d20704140940c14203c01d50001c0e01d40740882d0455004030742100f000c852600301c1c14880d003010000b414000110f01400c008401c1400c1450400002c05401e2034100414580ca501038800c003441100e0b5120760128440038202c4203e400600190814401070342c0354015581002e002400b14009c0303860840005020381900d100990054a1000409070881d4101c0c2c0e0f03d55100b08100c10318424940503e02400c101900c0b058010104010360607010080d40c0201020b10000300210426505404441e40c121090b150403001c0801c2103e81d80181c0d0720445030542086c03c2c40740c14418002c028010350303940030b4580820b03039100c0043c559a440e0b80 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 554914865 1250 554913615 554913647
    0x5030f06090d080606131e12030e040e0f0a29010810020a0e13060812040b090603040f080d0203010807140105120a15090e060a050412050f0d0207030305041101 70
    0x2030b520700c03155244210303500d56011100411130340c20f01c5002050122442c200c0d802501c1010b130b20300313805081c0100e904101e1004090030206280440d9850b5402013102401020f824061901e4652507000e614003400138101c00c070b524204640945206051865060b11004580e03007074003245401040700c00386580c020b40e040e01d070f10a005101c900c00034013124009500031f211100401003046141c030100d075200c8240c2c1c40100350744403011a420b07080084a42c18100400c01c11071012508000030000a100c180503100e88400480d21261207945a04201e450f02527600c50041ca100400a80500c0020559000d1416126203904071480c482d01c81100c00c901c0150981d050740415024010034107485c51502c3c210790302681203e00490b03100080e800c0100c455042d03400c030220b05501c84200e0000302108210082c0d21080038001840300342015101e104411107091002020000000390308160040e01104a41034680418811075981040e03040080080100340d404440e5a60421a07410081d0f201d41d42d134030065608 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 554916115 1250 554914865 554914873
    0xf080d0203070305091311030906010b0a23040806041b05010201021c0c0309081309150b04060507030c020a0e0601030b010c0201022a040c11060a02070c03060c0302090406080705030f0609 82
    0x1d030780b0181e9585c0c0191580035405054111410390441e41e07070081e466400400c498983d00c0c1d00305290b20a040c01c40581108014440920413070013000e6020350415028034040c0540c40740f00c4410303104281d0a101e00e820620a134410070061104000d152403081d000c0175881e0712400c031000c3d11007004a0903032244d8000f1024400038240d6000030700f10154081a4030440c54140040d1261581d9158851500115200080c2c031200c0700b401c00080d8224090000c680c4084111408254104541007005010f14003c0740d04000001c00c0d0f44080600400321014115001041c100d0030941d10380000e100d10004480560000b03040850007800340d4006e03410446400e40c140c001d4068150600f011502800000001800420400301079150f9521148036a94081084c0d513107a030541003950404c0c0e4541725025012181c2c051040024802040440c142081030345d900c40000314400c002080118082c0c090840d4542c0e1107880e0650000380c1040004021086400070b40c20784603071006915501c0d40b6006c00b29252403090700 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 554917365 1250 554916115 554916127
    0xd08040206162f01090f1203120e0c040e0c0a172d0105010501080f1902041e030c050a050906041107080406170a050114010807030209040f05010f080d0203 68
    0x24180c8040d02c400c44a08000d800c0c4607405469446460004800a403581c0180780100000901800d8140035039040c03e00303050342c18900c0c04042c0b0026060501c103280828094180c0141058440c0c002d80c0300c0405503e4041c01a8442e892400303071150b880b141824403c52803e03015074400b120109800051200040c0039031a42440c042c41c121006200d40202e00c500e000f60f5540c0f00b1949054184419000c0545e1916503070290490119403c450341a00300301c1c107001c550005c104036828041c6003d6440072035068414087d00f010286803020740141e8012518400c2001a50080356440200100450303019540c100c0c011503688082c440c030b42c6214014250406003150018006003010340140b90b1481e403c00c00689441c40b40c3d110210290010b8000c8400543c5241000030120605405943c0100084404010079494400841100018958094140070540c400921000c1c0240d041d0b0302203000190007032000090344c4114000030003003401394459080112001244841000541c42c07526030b09a002186400 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 554918615 1250 554917365 554917369
    0xf0608070c021002100606030917040e1603110c031c0203060d0609151409010c1d0f030c091501020f030a0905090c07080d021c092a08060f06120d080402 67
    0x4070448030700e04103500c202020114500e049210301b01c0109aa075900045100c0c10380740201d800c0c561500618110740c0140818407064000d04101381d0040c9007050383c0320b10141e080c02d00b600586540c0e1b140c60700c04900803482a0410702c0c00300040102c9031003c403403034000c0c141002241e000c9002c251613103030300710440540b040c000420a9110200701c90203400c1148250001d952900250b44140031b450503c0310040e402c0c8007609400f402120304180c03207800e006201d1000c00108000e03164220011510800018045051030b40f0f0030f1254a001c00e801401100c01490700469441d1500141050b6600510901280070040384001c0145c90300b144440c0e586101c03607881c010820550707240180920824075010810b420009501c0002800c03010351421003d600c0306100010400701c42d1001921515040c14020550000f07960441045d0f100c0c07085038803162409c508141040080390258016000340c0c45024184402e0321900d4030b5586c402d11f000c035038403484400d100202c01c1c0c03900702c000742000204d000200810014 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 554919865 1250 554918615 554918629
    0x5030d0c0512040812070309020d0609020f030d0302220807061404081b01030c0e0a0e090a050106080c090702031e090411030a0b0a050d020f0d050f070b040f0608070c02 74
    0x208a62030724500300310002000e40c0c0e98040540c3d0889480e0030000e901643c5c0e51580d00f40f160303c103d0909081003000125000f04098001d030040080a050344c1302030005c215681e600c2808501c04000c0c0403508143c98241001e4000d600c803d6100165049141c5c800700803289540d0313132070305480c85a8013418a50349001016030b00480e51040c84449450140700105032179004110302582c82d903003540780040d411030b0310f000941156803031b0402c1c50400030b240c0c0584108d6150703002c0807403c0b18100e00c850340856640001c01428081c510304000e1095003007840c00110141d000a034041c000ca4100e80018481d190801e0a994a00c60310742d8041e95104c1d090190402260707008042e20107008041e002107018603216081020b1540100d80c0200441d42e42d00c0d0850540c28050100700c0541000d4529174000c3d00c0070340006101090022200340b04a10010745c1404201c41408031200f41045441100c0ca4540c0311020038043d500940910b8010b1200440000388541c418040e00e03001e800d46448040445449030288419 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 554921115 1250 554919865 554919881
    0xc141809070315020703120506061206030709140901060504090302190203030706110c010c1107052b2a120b1b0a050a02070e0105010f08100803030c070308090a05030d 73
    0xc0d001e1200000b010603031244071080004400c00d00182d88070358914002c1e1400d00000380a498003071a0404020003919100304527844000410b1b0075502c0b03503807070500092502c4c0d40381d0040c600c890b052202400c0c0342421000940d0045030410000d0150303070703103402c11b01080311651400078006900a51034200040e2080302030540743c50019050340d00d041038030703194501030b9607206400010203480024401040c483c20310034481c13100002d00c0d204001d400010f40090780c903401405440c2c4110030040d02401c0c00302c8280c0c0a89580019030701c48101c014100d007017910400040700e800c142040052000035110b41488200441526080248071000b00000e88942c0c3c50b4aa0041810840020050310066540c3c44d22001c0c1070419125074503640d507950040e100074100450343e84404021601e0300014003a0fa07030405a0440001090f1030100c245507502c5081c01d441c41000d0788040c01c580000010f10000343c4192004110480c001e0701c0354207143e10303000b8030907a4491001c00080d01c01d0b0003d01c015607200d0782035001121 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 554922365 1250 554921115 554921131
    0x90603040c120c030605060f060d0209190603020a1803020d030809010207020a1502070b0304081801120207030c0c050d1104020c070807080f1516180b160c1418 70
    0x1d0054070b80112042c800c2c000b0600b41c0d800001c8a00070010003001d801120f034814020346038001021030450101c1c0d00740c000c454040f00310300c2d00490034200a4a410000580880c2c583d907202d0130083d55810040d00a42c094a000400034108200f1075484601c01c0006004480e030180c240d601503030036924100c5060b08050b2813442c031550200a1600035030313544da0541001d408405035100340c0d00d007aa1001380c82c09800c4e034031110200b00180200000b098039007054610000051040031030145c041801204e02d20700c1000c941001e60b1010800e1001c1c075510031704d42140c0c3d81c8983e000840040c0c85804102041c02d400c500182030070001482c4d84114289a0050700001d80c01b24112040d40341c07250b015504000b5107401280c1c1d1070f80805904a00300031308000403000503083c6245090030341052000c58104036044480007007071001c42c00c182003a180f6040d03d06030082011501c12600c400b0038003004c207034821140b00240c64640100201140e803045c018408580ea650040c0011184440c0c07031002140540c00400909d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 554923615 1250 554922365 554922383
    0x1905100c03062313090819050c16090c03060b090d06060f08150f0403091a070b151008090a030c0501020c060711010c0e1008041b0f05090a0203040809060304 69
    0x103088009800340d01032034214290180b09408404050011007669513400d604d80904000e65040030411100440e4420054104c60104041d1210010707109480f880982240520910701c0b2015481c5450243d40282c0e07100c000188035002980c83c1c04c8054170024000c07450302c20410002d150b070500c0c2a00142e011240315000218201e69210b40e441d10b048440d500483d03242e00804072002e03e00d42524282580b00c0300103040c00d4003c1c10503840040c08403c1d1401103045007038240544920740c07010302040d50001e9134002c0c41d4250074504008401c42041044100601480000c0705038910140a1503486200d6951074000704508103181d1411078a40d0001202038402d55420807101041c80410f00c0002d10481d042d49400d480d6880b5a00c0300f44c00c40b90a050600d040054440064080b9a00c1d002d4254000d22a854555000e86942c1401c01d80903c8002c110411800300310b00005007002110b203040201c0303100310703501c013801c0d034603903100e18282c1c88101c0d40140303111b208120000c52480d00002441c1c009000741c6501c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 554924865 1250 554923615 554923619
    0x606152805040315061410110601032102010606020309061e0f130f060815120105010303080604200304260304261e090f0904141905100c0306 62
    0x40e2008010a8000c1000440001d0144240428483c1041180f030050000300f00441c54111175681646951041e41d100d1050602c8200078103108080700541c100380c28050f24450350703503031400c540940010400c0c00418410f01c001481c2031801886244211801c0343c02461030559101c04100c1c40e54030804142281d09030582c00d02e841408010083d018040703001982c280d45280c0f0a03088091207d8643c414810942d10030810304c0a0f030307401a00c458002c01003280c080c518210840004020b1289400c01485a40ca00360002041c140e2045240340991000d54042002c0143c10030158908000c000c1050854801000490005400f0050100130510300710101007040300c1840c1d84851a62040ea81075681c1010002031025541c100078410900c40151886a86015011002038032040c42941c240c0e51022030100b000c0c40700b0782b19944489a041001010050540390910b000c0d018200045c1380c1d811548502184e04d5075455001080c0340201c3d41110003840c8501d545420003019040e861000c00405884000c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 554926115 1250 554924865 554924917
    0x4060506030f100606110a0812100506070b0f060406060c0b070302040f080106090b0a05010210050c090301090609140c01051b01150909060b01080c180a0e1314060615 73
    0x310f10f80c400540324010580c030303207081d07401007400017900140d906541115245400051034001260b0b108800070071400d07103641e40c7c45007148103411079600668012000040910400c50820f406504c61441d010b00d000f201d881d80010f200413038207207004080101d07105042c81d1020401c0304c0400d940c00f107601d00d4054a09030b01c030340d580c0c000c0301c003540c1c081856607440d1001805919030034090840d0304d94090b100e0901091911000039941d011038000210b9181c1e941c004984c03000002001c50f20034200c050001c0c8039444e218a0014010026801d0503114050242140c15012030085120703c84410160b41d05030505c1081c00040d880b0842c0c0a80003800c945d0385607440030100101080c0301005007041c480000f41009a8246401a5051421503e0400c0303012402c0018113020001070b600558052047c00030703880890004101480920740107a80d58082903020002d04496110000080502c550301d003c00c0c1a5412600c0b55980c50141c0300d06900900440002080302190b034040e00e014488406514404010028 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 554927365 1250 554926115 554926123
    0x1011160206221a1c0f0608070b0a0314010e0408030a02070b0c07151401090209130203181603110108060d0f0309060e010801030c05100c080d090201080601080f04060506030f 76
    0x41041650a004800f006583d540104a4440780d0390448101e142c100c000a8070102010300403000d00480f50346400710321202000e9840b19000e492120216400241c440200302e01c0d5070068642c2c8030010742043e43c5101ca0350480c403a41d034101c8250102c101419100c81d5201881c6404c0240b02c1c60f1000da0034400d01c400724196401c0640942c128092a07a928045810f00008101134400550750250401c0641100c07060711710051411030350391403001601d604250001036080702040100c481d000380080706104c80310a00181c0d101d1140080c0040310040c1c2c6140c5031302a496140ca05c0040c00090000c000280c2e294050303d4000d50003000104920305801c115610300b445108000070550008075582004d01c80b10ba0811400303442d00d5002d081100080d03241d0f03644c11500e02c03428050280141e00030107110203440e0240051640d4258000b80c1c050f216180384001000425910301c0590016103590042402075024002c074601602c101e01890400b80e4035a00c9120140c100940b0041d010301c205079004807038a030140 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 554928615 1250 554927365 554927407
    0x103170d06030c15050307080103080c1f0b01090f03050a0b13050a1b090908030c0c12041404060b03010509040f0203030c01090302060105040606020d09060e0d0819021011160206 78
    0x305182c0040c2c1e0070705040001c08282c8130581018848200284076031160844505d03411254406200c0da0307101e540643ca22300703100c450000d051040d10501e105450b5055560081854490281e81e002d074903030307513901d130f0b1401d200924030024085401490321000400c543c1c50303040c0c1e03202000c0004892443c601e680c1e19485d0a151500c10b8441c41c80301d05c011210102018134880080c860010107000b024910f49440c8010700c00034124480c24200024040b0781c0074002d12032002e400e0380c0c05001d25104c640c0c2d4004580c452500710603152240f450103401041c503c086000b604d05885028003850307083e0703031166100c40420301011710070303039141c8400d00c8040482202401703210000c1e44290301403c0103500d1301c024841500d803544c01c04000e49d000707441e10951842d4040c200038222090303442c0100030888142d010900240e99214044c0180c01e00084181440c07009045070160840540e0845815070740d00f104240031140c0c0c1a2a2690b481020401ca02e10610842581c16080e07000070a124984986403603101080e140e00 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 554929865 1250 554928615 554928623
    0x9150902014407050a05180324070206240415061d030303090c090421050705060709060210201201030203070e0f0a05040311010c030e010c03060e0103170d0603 70
    0x41084100c21050102e107010a101c0c580e08900a24104114003600381d01034a2851400c01c8008980301c5c21124104041c400b0050f0040c0c1a41c020000c95031003880140c02e4205044c14243d6580d02084807a403002842922a4050040c1507900c3e44c228040405481d80550703c00b6840358645038581c101c0c429000440700242890740310405294281806150444001d011151080d0001c0c020840080f00214004060100440d15000359546a2804400090441140480424140e4010200e10760420001c2525034020021500b543c2d4806000b01c0e1082a2030048500581098000c2055049941c000180301458500030b54204001010b205900703030040211011a410350000400c19402c0510448011300911100c800e010700d4000320020904c1009030590100607903e41c002014188525198800444404024840d018800c0c4000f005040d00821080855180140d5000342c24040d02c10b403010bc6a103049103c1c0c05030b1958a07003030480c1481e19030032900607008009814202d800c40c800c0e04091441 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 554931115 1250 554929865 554929937
    0x1505070206090706081005040b210615040903140d020405062206020d0e090a0b0d0507032d12110d030906230f0702032215030915090201 60
    0x210207070241c68040144e00c1841401804003e02c40014051820101521001d441c003182d41041500030802c1c20b081c10b42940701e210391014900d22400b02c00b1907a5401449002000304280380c4810401040b1020300e800200412507113003059690318600405000c1d486154000142803a0b9a1400700e4141d91000000350850b045103002d0100d26440c210400d00604454401841e1a054210000d811422100400d07031180c5110340c001000491181c100403407800000d051b00d01c5201051810aa8454141c001140c031b1445d6001c40014403440000d80440810140c2d4440442c0c1400340c807131310791024402c0c10003010088900640c5400c030004000800004802e56800268140c4a0401c5000c075080404400e120302041201e5600c44581a408a504403820414141c920340380c00c03c0070380c81d61007a00c034240317554ac031040d03500d44101454400c92022501840e0301b0a0129050a80c114200c41089000402c481040072405c40c0850f050b6104070b401e184181805030a041070100390408490000b00500c0100384 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 554932365 1250 554931115 554931121
    0x140f03031605030309011b02060c1606060303120c0e060d1a09040c06020606030a12050a17090a1416030b041b14190f06030b01090b130e090c1c1505070206 68
    0x24440c0741048a191103c7c000d00c1003800c18001d4448002408003c4807240205818804a0b12405d000e0751702c550019041041c0f554924000e46400112181800ca0300c1c9011409490700e8048c6c0e02120406a009105a1511508800f600000c2840710f918503102034803d00c200c0762503110203c05a024900480040c0d041c6440c0c420000d240107002000381d4001e0304010340f400005801640c00714004206820b04170386441003031108a644c2041003c0400e043c1c2c000c2e4040c41034000b400715031007940c907004110b541b00840110340c540e50f80765041c2991000d110b15008041020a189d8084180c0041c401c1490803800f0648190307080030b48041d60000c1c5401da0003000d4102c00391030041f024165407070107031860f40441c0345841702c4d211800300503204d100103140d190a12503c8680c421140c83e0003400e075140f05142c070703620f00c0d00c09042c51401900400d6020110700d00440e00c021000141d2900603d40200483d45000702c44501036203d48190381c00302c86081c11409205000d058038040d10303104a90300c0c4c0c0248201d00d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 554933615 1250 554932365 554932381
    0x131413050f07080309091e01090c021002090901030602072901150f02070905090109020a090b0f0105190e01030b0414061903030e240f040504050c04140f030316050303 73
    0x184000000200035885000100080540031090b01c00e0b4105c00c9806141554075455090102400e008401c44070002100c000b0500c2c041b69440400040110342c200c9001040182c1900300301d04c00e0300c0a40b607020010000410010385290000c0190350310460458940c5030146c0a40a42e107044400c074801c3c20702400005008074a40b00100255941c040c1c588000131141d101c1019494081e10b000f8040b449444200261080c6802d41001c1e03c1c3c1380d0301608003071000781d850702c86000400c0703032684441c45281c103030080c20601c0d8400d07800d94071148c00144040e01c4940010a05442046d4104c00700f0b81810b850300c0118006a549214861108a24440c000c15500c0c000d0308004000380034200340c02c0c0e29000840c1c1400420391048044104881c10b440348101d41e00041d1400c140019203840031a00e98000280c4a07810340d4842004d0070803a0b50079034040c40b09807074888118480e40140e010303070703c0e1219510300303100c500789010780301d29003800005000ea03403a103c00421803e547c00003001c0c00350380d1340e440002804928 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 554934865 1250 554933615 554933623
    0x90b180a060e0f0103020f010c171605010612030207181409160b0c07060315030b0c0406020c030a020d031d0910061106151210020a0906020f01140613141305 69
    0x381c040c640e10f0300290f04650000380001e816103820f0b03040000c56801c20040040f00755001c0317564009040e48a45a01d040070743d1007002c545007103084401d942020b01c006180604034440d8030407240e06402510150303040105090740c81e07203c0e2600180141d280d000c80c2135412100110f031070080c082da0020b04848a00c07800d1249503101c41d0751041810200800080c40c1d090000720b9102c09440301890081500126101075171a450b03415080504003603800c80c107104124400c14001d004555594003551200240310040503240d0303024010103500001e0300c2d1a8000040d11070380318019a9100010003c076502040320100d21703924000c90741074840c42c1c203245003800b119410015a00f03803d1980700040c4403901d03003800080100c3d00c1076a0018010401903d58444106040c01106500c00c80d210b421922000d9014005000a170307188584400b5014081024000381018011594846149518025140c86e480140101d554452024a40c0182c0d42c9514001c07010a0105642c02806800c07034601d081c0001d420700600b0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 554936115 1250 554934865 554934871
    0x6090201081506040909140312071103070302071401050c0d051c02090f04091e030206010f06030c02120a0c1506030c080f06010b090105040504050f04060c090609090b180a060e 77
    0x8400032010002c1c41581c44108071400e0322100480403131040928640086984282c0b001e1202600002c0741c2a14014134803140e6901c0703070231a5540c0743d000d0301250f0346a1b501c074880c40d8070103001030300034403014001440545000c8000d2300062410901d45607020311641c1c2000e51284c400000600001915800c5150880d00e0900003100c60b48218a0319800c04001038502103645421409262208000e03814400c0e00e044860b903a0145010061180e00680f60003900e8000900560080c20400e00c0007050003403007031203800041d0700e0301c0d0020540c0340400076851980d9000745a00c07000b0041010000d1001603034900b0143e01c98910700030089503441c114540b0091418054028200507400f100740140c03c6440000c2c030604503000500d00a1ba581c00c50780040700d00b171040f50001a005802c100500c062560300301d00c120300c142e000c0c4004211510518804403080f103d030b4403a96000603031f201400c4c0329103441a4400b118001000f0700e81384140e04e08907441d4844c10340c01c0b0360101115030354000c01c0080d0b2010b5031403903074 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 554937365 1250 554936115 554936131
    0x720010e100c030b0909071a0313110f0307030302031305220506041b080403080c0306010905013e1c1704060b0a090f060e01030f12050906070609020108 67
    0x2000200e030403a801d94032064000d25440c200c0e114641c108003640a40d008030391070103001c0c098607824a006070f000d65039038400f8800c07448040204070518100b0314522003501e0041c2000c01d042c5058181a0b1515034040201161041d031058800d105084141c2c1c041100310004c44c840d401850b110b134440c9044004508072503210380d018100031041c03081891500c00e00040c0301d03a2604e60004458880d80c0c0070070010081e081d05068200c175441131604130941c103c1060b500c614440c0d42c81c1e00749a590004515014081030fa130b000c1c04101030403000d00c4198002c2c1000c3c02d010628030012402c0ad40d80e20350000380482c400d032500c01100b112204200c808042841401e10460340341c440c07401038544021006100396042102d6202c1d50380d420020030200001c68110489502005085604154036a50050003c20100011500c03003480d00c00e00180c0204103002b030a0481e50021140580050103498240308071b2040081c020411004000450a82d40c030b4a015210b9140107900002d40c46089200142c0f01c0500606421 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 554938615 1250 554937365 554937371
    0x20a0e190503060f07050c030f09040507110c1c020904030c0b0c13090f020705060a0f1503021005130f03050601150206130213020c01060308090a05150a030c0e09072001 74
    0x1c00107450004665420a000304e5400300c09a41d424030413174441c010b1a500380908c0c00000703290004800c0d2078016003440b5600301c0d000c02182d280c400d4107540d285503c0b46030440d550806074503540649001c01101c410301038450758001c10030100707a0024244403000c6030100d001c2500b9070041401c0c00350000041c3c0d8050226000141f80083d080d041941c650411700c290380e10b080d00c801c405101e081d9550162030005520034111100d03420030f0040d0341c015240c101680c0a100340391542120740007050540150440ea0050016400c0031010a4100c0305540f14012046400454220020b2120300340ea4a0384000e50182e0041d144650400c0480f140700e4500612450440d404141400295050a0302c418075241e4100d4005090f07216a003d01d801900800d44845115460980c00005100c1079000615940c0000c80da00440301b0780302c8003040308040e80302910501111007840480c21f06030090740708400001c130509201094480003000200c0821040700c1500000305405241c140c2d00244000b402c1c3c820300098028 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 554939865 1250 554938615 554938619
    0x705071d040b0114150a090501020c04021e030a090f030207030b070309120c230139050708090907030209040f180201120608031308100c08010302091801020a0e19 71
    0x19180c219041c020518654401410a05980c0d101c800001007040100c145c4d98070f521246602901508a51003194054080c0071103082140c0351510031141c03907401040c01007248683c027254503409074100400f440e004c7e90b6070b900c800c40030425007800c2e01242c611a5004141081c103610b00482c0d5100c001d004081854248504400050200d2007484070a024070b10b09002c42c040c0c0d500348440d0039048103442404000c40f182d00e80d9107200c03040d00200c0c40381142e11069114880710311007445801d01c00038a544031080e101c3c1c0e0032141d0a4440c03070081844500803804207050411031030004095510075561440480e50004900b150380c20640503008202c1c00b420010440f085400352889104038000308003d0411107007100122844039141e0003c005010940100d944803103410035a030012202602400030a80300755840304004000300d01901c00c191055a075901080d03440e42d82403181016014081070284500d28120624400c401d10240514500981c0c03848219048a0113028040c1016000000411941041 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 554941115 1250 554939865 554939873
    0x605060f07020402090d0210020106170d0206071d1c0213110a14070501050106020c0a0816090207111818031e09011107030c06030b01033305060705071d04 68
    0xd03070300d000780c040c1c4015031764429501c00505000040000254080b0718a1040041030307030305502002c242d80101c41512081210f141d511960ba54405420a00507881400016526072140414940080310106030031120000340000401c00030004500f00c800d0089010f909055107403022544c0e64200c6030304401c10101d517107450f81007054454800b01c8030510141002d02500c400b10316003242c00d05078200c0020403180d42c444800940f0350004141b41380c0304203029000810000e002041d5602180c011310304008003a484c00d00c17460060342140400340c031460f10700c030380c542c200e42c5401d04507550070301c11110f81c009540340c4898518030880c1180440061540203110700c1a503020002d015040300050b501c8025120b03069140103c0e1111008248420308e40180800003080002e001611070540b103403a00d050101d4500303034004408035000c00382c00700004900c29050346060449841c8240d6440320800c0594511038445020905036400799008541c00e51142c00c1c200407007690320100b80c01403144d40840a40310300f00741e10703 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 554942365 1250 554941115 554941117
    0xc080a0c0921020a030501140c040e04321e010b0618030c120d2a24020f04080705030a08040902130e070f030507050a0c0305090a08011404060605060f 66
    0x2d021050100b144400d20180705100c1030300c05154000c004d03e4100d92245003040c0609100845611410302d0040410090a540000d0b0341c01e80e0304003016070301155250344036103102040644d014042c82e1035081a50001d10005d02c009100b041904000b841c1d043d030580515480c03030000d694054903503403401d03186280c503a03103a60448161103c04041c0d815907010304000a0b046c090f40003c215031160444541c0c1c00c035110041141c040c900800e403126403414450652034583c02d0002d0700d42c060711140b80d1303121100003a425403245c041c604c4895064103006104001034000c9901c141200b000c0f490000c1010040341904101000103010240c0c042c2000c422250b82c1c03c0c5440c0283d005a00f0803d4020604103280c2002c5140e9400078410159040001d00b0200343c050407110071000c0c1500007a0a03d400145128080c20840b007111405a0300e1140269840d02c00b21143c0c4c000c5e080251780701008010004990000340911074400241c0c0c84244140d06086c6414030840e070f4503600c200e00610003802580d8041708460 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 554943615 1250 554942365 554942369
    0x60f0d0c3002030402060903030307080a0e030319020c010b04061403010e07060912030c05070b0d14070806120a02090f090f0a0809012109050c040e0316031b080d0c080a0c09 76
    0x410143c1c49444900c0000c00300c0c082c0c64100358240c880031040000c2c40341d1109283d40143c02c0000c00f085034000f644045078492104a8030090103890803952040c440481e0360090404904100001541100719400581542c2082d1300c0000c45200c03000c80065149028030460901680b41002807208070729081000d410720341903115a920702d0103038408200c00d0502480f40c5c8480946e100f415900542d88403400d403111600030f9841a11094500044a00c00480082107180200402d071500005075540b0740c01c01030f055102000b03490040c0240d00b1018016243d02d40b04601802d292104040b452405001d01032820301e816040044951044404a01145846c82112100e000038617210f03090264001690000602110207600240e251103103001c28010082200032405004480921000201c00c603156680e000d511006040954100d00e07110000e4090308a032068084544c1e80c03442501c80c191204132443e084404411406622200c10000c0f142d0302110440d80181d0000342008410014000109a00982c0c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 554944865 1250 554943615 554943707
    0x5071b03121d030618070305030325181427150a0b120408160309090b0f0a12020103140403090609170a0b07050f0406020a021c020904060b060f0d0c 65
    0x85c0301c1c0600d150381c041c000b0748040c541100c2200d6480c1041100071403198403454148030742440c0d40c2c0d80c0c06040c910415071551440c1900780001c90b503609001d206558a00f04201c0b280d842043e1454180d07045120a841c00c1c214480b0400c192140d00d044602a014441d40300100c0c0e1003121950000c0c050724400005403010f080948694549546c2c807032918141c644540c03009420110a0003401404244e444009001910000e805c14800ca4411308103124840c00001241580004030b0b060a00103c84204940301080340149004035600003440018128080281c40540001e002603c0c203010498110395120004d10b00c4103ca0044009403064458542c603c03004000c0100b440540420703000c92091044e1100103001c0440b00c1d59035070340c0c0c003000b0b0354070504c52000b2030103035050700410703522810344440b8400c220b030b000792085040c0d6031640c4e981c000519644040301d500503c14891440008c49007409002c800d61034081c001008038126801070144c01001c4007506102c1144142c036103103449000080382844800c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 554946115 1250 554944865 554944891
    0x114012103050c01230402120712060b031002030f0a0c0801150c05330a090c030311121605010b121c0e130c1407020306010605071b03121d0306 63
    0x240443e409485040d0100d015030200289090010344404242d6004500c211258a0300703c01c0b081e04151100302030303c00ca003a0b44c07400d41c9004010503061b800c0080036220007400e5030782d1040c00900e103d040ba00103841d9120000300103c20007807c00340d14455808040d0840c20600c1c61985003054040c501150301180e5000c00095480090401504000e49200d07980020000100506011404005107000200c103282c0ca070801c6c0b010460014147c403e10007010307000145a4600c81c21514133440ca01840d001c02c1c1c0b442c3c815460b00c0340c810410840548820700040171000508000390038040e0070b4803041038295200e01380303090040c5200c1034001000885240d0412401c40d000040c40c000f642c46591460800c0d0b04064144913a007070b07100700c591210501c5110340e21452404501c205a80219020b07080000f90035501600041c0081c81c0034401800d006417280031151810710402d882c280c1d030045a07a0044520143c4120071150321900108401500f034a071085c8003410800c0e620019548001c007506000078260 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 554947365 1250 554946115 554946127
    0x41203090618060209030c010c0c060c03170108030a09080c010c140a060e21030c0d05060f1003060305060117060402040b1207030308043810120302011401210305 71
    0x50300b6000302046582210140c0b04200d02d504000020798824110948603009009805e1450b602500d8440c4200b904107540101203810701d1810f0301c1041101800f90180036559006503080300c4503404240c06440c00001460b110388504201604c540d5040c1c10002ea1504022074070011070740e03c504c160304140c1e00000002c02c0501e13480704072814408a200085d1440b820521910490100006d510003110071070b4003030441a51694064444e03d0206541c400031110007041815001413140d00403a0b0401d01c02041c0201c000c1038a800141c00019089800021070f484041c20418481d0500129006211010700708111702c409100c1580c03107500041c0020720880d5210112545510741c803000c050258a00001c840740b0300e40b42c2c1405445001b0448045400041c1850800280388115218000d5400ea0f030110651140018500c2c03100144010482490b100302104001800c050114820140c179000f5000000d40f02403480070450340e804160011314400440044036000050310340445500184c1514000b51150 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 554948615 1250 554947365 554947373
    0x3030319020408012a080903031303020c0d20010e1302160221010606020a020d03030e1c1205090a0f02010f030b060403030e040f15140a08100c090b0304120309 70
    0x10249801202913503103040b4080c11108051500e13440c41d0b502502c0c15200142c0040c0080385c480301c00315060480e0350000c2c80030030072800c0c03088103d10500c0d200c0d0050302d026400013008104114162041034070b5019040381c00c0f0624282500800107001800e18062001840b0781c0041080e101d50302d101050b5081d400a20b00540159a1182e40342c00b650080501c00400391200f200750491316554003600b01035103402000a2801c0c00042c040f007180c2e50180c0000303019085502c5c19401041210200c4419000d040f0036042c20490198200f02d10001135200d440c5410015540441201c01c0240340780c0039a0304c68405d14012442d20760440752120340c240f801c201c40581c4040100c01034082d10748100d03003041020402004040e000b03401041104010740303003080340d41e540c41981401d50714090340841401401d0081409405400d0030b00440a00001c2d01d0020816911a201842c0000d001d0388d05071519030740d98100804a41c0b043c40e41000b400d15030311f15030442c2010348030150125410781c491824107944121000800c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 554949865 1250 554948615 554948617
    0x303030714090a080708070f061d220515220b03190c0e061e040f0e0729030c0306060a0309020907081008030a0207140d170a1d0303031902 61
    0x220400f50080554030741d60f00450703588140c140a640414010742401150300045103400d10201d840300c0d80c902c0e058007141800007000307041804c00b290b081603107003107961014824000581440440a04009014582032094403140c5000b6640b40c0d1180700582d03800100704003010280104500031000000320341c2e48000012f8a40040c2450400b004014000400240038111050301d003280e00c0400c80d204541c0c0ca04c01004102083c04030820107045040b1005940713420300741e0107510242c000c2c1100080528401000d2803520161380d010381a9446500d000d000344540701ea030010481e0241000705419410100c5072240c4600009050600540340400e04480ea0b5200e41c02890340660060244800d90828840041201c01c0c2204d80d0a11208078000c0000c86280005c01c60784588039940c06818050706015403d180c43e20708810b003941c400340401c0c40c0340200701d91400c1c80fa4803507085446540c1d038104080c800f40108000c1180d110301a490400d03190381da0f84000c0304480e4003091b20246102c42c00120150f101c02 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 554951115 1250 554949865 554949877
    0x1d0a1803080901051303050d0506060f1218030304030c1103151911090f011b0c0b1c050411091b0a0c0c0806010815090c03060a05150405060303030714 66
    0x46404824a04014150006001405000210001d000a07510030400c1d07000f0229030000140090810043d01010b15059030015401210040c48540f03480c40704e81898a040d00305010204405804c02c1c01d11038000d8400404032003003008130001d10b0951415071409004440c4101004d0140c3e0140440040c1550f010b005400503a0f9140704800c48604202280c02c0c4e03901d4800c014480611310304103100c8050a50340e42503801c40c0600a000f4140041a1401102c540c40012541403144070764080100003d243c0a0801c400780002113035a40e2610141440340304221400e80e2809802d5251030706000109284801e074207110b031001c4e64042030350f03100c2486103440c0e601140d9245500305404540e40e42095032040c854003005004109003085a51925103075031300c0326420b10542c5150381c4041c1c1c41228000c000c0040b0340c0e001716040151601070100001003030400300111540131070340d55100c7c100420041210081101ca071001d550030403c82c075018010030b540c0e201c040c107070304144820980404141c0c9031500c00c80314 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 554952365 1250 554951115 554951141
    0x9040b0121050a08040602011515031d0109081c020f0307080c1210050a05060f0a0c0312180618050a3e0406061107090c03020c01021612091d0a 63
    0xf031036410000910340140c018400107500700441c04104203062030072603080c0d400841c0041800703107c00606800420000040a0401400d403090000b180b40c00e106230007100e0300500e0101d07980c00400507048800c501c40100c15080c24414010822a011540140ca03884502810b21080d81d880303403c1040043c0c000c070740c031400310401c101080213080710030100a03400702c900c01e8600c3c441c079a8549080156502400e0700e810302940e41840f03002c0c4074910401c0d41600d050b01a06000c900307608505200802e44520791195160100e1400b400000c11610740f00303a07480900c410319461103900c80c554406845580c0d40d03101901c5000500c4c1d0003101c46845410304402011807285403180e94401e80e000c02c2c121001c41410600c1907140080019466000742d0203d400c20b0003000180404030b00300420600142500040b0404040c3d081c040c008940e5070901c020442c0d00c0b41300818001d02c01d01440d105030341890040031007003000307000072040111840c108908100e145c0901d03400402641c5811181d001400d10840c102 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 554953615 1250 554952365 554952373
    0xb04050106030b090a03121112072d020606090601090914090c010e0a060f1206090902030c06160204020d0b04051602060106030b09010308070c0f06180509040b012105 73
    0x2004415802141120700c140804040c41c1d8a280160703844e40e0003400041c01180d51510000580e40302c0368810414462625201d5081007001440c2140c00c4a04403000f0000c109500b4030030030346103004400e426407203041c80c90749030b41c0000240c1d000b5150403014207418082c11003440800e400341e0003459220043c0100180410151005a14030707070070004142c42e0350406001d04c2108a00e1540310b008120000d190143c42e09035064586030040303440500d80c4102d1410070240740e20b03440c0031019500850005004105000c07807038050f50b00400d4146681515001d208100401c0030841c1690100403000819404071801600c03000c030707048100302920100f0100d5030300521380010810420103005004040004c19421504560780b40e01098084901c0c4030089603120452100400001f10321000602415200c0c03001815116590700c0c82c4001d500c03480d0000380101d10124080350354206402c500c00000c00d000c54048000781841d44640c452020107000c2c5480801c244a41100c501501c0c1440341203465001d0116 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 554954865 1250 554953615 554953621
    0x201061a07110a050306040b13080412020306072c030a051917040522140f0603160e060409080c1906061415030a0b1503011403060c091009030b 63
    0x140e030551080008481d400c14100902c14581803022011082d5480a8002c2645850303e4a81419a11004101c0c40902208404090004005070060070040550001c18000c95030244101400d000e4001e22001c201b207400580e0250484203c0c2c1e10000e001d007d2040f0482e00119030003c41d040c03111420000d000c078400c20082e029588880c541d0344103050701520740100b11042c2a09090307810311561081692120844050101903001c12000c089100c04d100d05c00039024544a21034011040110340e00c5030000c5246080120170f007024050042540309840201038030500b0054002c203054005040180541e644058400411aa007822903035070500800440310300d1800586901c80300c2c03000302d03001c54941d400c0403000208010000d03c484401100208800c0a814000c2041c483c541c00c01450200b4164460101140c0790304c48010320f88503041c031031880582d40e40c1041980e0940c4140c901109000f03030300600421407400342402c00d6884071132003120480f58140c10380d0011100341c480e0786c00207000c0e40c80707400034 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 554956115 1250 554954865 554954909
    0xf120a08030619030b0c2503030606110d081308250c060e1e04060b070f0c0602070501080123090c0a031109010512040f060c02030a090b0301030804090507020106 71
    0x61446010b00301c843d0840d0300b607441001c403d940c0e03051000800d010308203000b00e00582c81d1903000e802540000c5412040b030140c0310302400341d054104501035000c250b891200b40005540003580141704014800107103203040310400010100c06000707041d41e40761240c0d4411041042943c0302121110284410241c500307491404c207c850310f07442c6200c1141c803074004407030001c0e03058002c007052403140c0760040c4603e50000280454000b682c07420403020350720944c0c500740030a001d000c0e140900b12241c015030b074071541c0d0b400303d180c0040d001010f41c12030025540700c0401000503a91090000f8151507a40007240302043c045079100ea0790984040c1d0440d407210304d0208000108940303002821b1a01e080d60340078071900007000c025030f005108481c06140000c00411440c140c2644c5c507480d1a810074440c42c14500805c10319190b0001b100c40f00c080f1000103800008404441035400403040b0040d0028000c1c082c40d6516542e40c94041e449948201002d0070307107400000d10b03003500031342c0018020400c010640c0019840340344 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 554957365 1250 554956115 554956117
    0x30522121e0c030311240106080601120f020406110a1e1505010e0601021e030421050a0c15080c0d180f05071d060d020f030a1a0105130c0e0f120a08 65
    0x2a000c001b4451003120600c03203090000c8150f40700d408680150a6039007008011100a0002000c55041c0724811b03903900b918400c544a0b020403581107990041e121f608000d0003e001010b802802c400540c0611460408520004003400c40318000f031441921a1901d4585880211400c411075174010b0329210002900920b8100740c4d603ca00b4099094820100000c0d0301c0300008011840c10401d5544244020b21040c4107100f99002003016066500c0c030f01150950b9900c1c60841141c0089500c0e6041c484204902c000d403900c581d00300d03405418090302500e07103070003120a41d029003103407861000e4546800f6004980c40d4298031070b02d1034102e072560506040318203000d50303202d82038230401e11043c40d140490f1100c480404845401380000508030025107445400f0010111408140958580070700102c2c0300c0050b40e4809601040c03523800800718050361501c1c0c10400c8940420806262107410141d141c68900c1d44043d51080c5d0450840c1d5413400018840c010500c900d52042038407866100b00701c000c5c0e0620050314 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 554958615 1250 554957365 554957387
    0x70e3102040b0603090d0e04022b360807150903020714090a020309332d04050106090c0e030c030703050604081c09030522121e0c0303 59
    0xa9014082c0800e00014031000c0c2c4411100204260003409800c401e09106aa5540c46040e0040001d400c100845a10701c0c141400800e94a940e04135068181c890702816000300d140095030a1505407028402a800e160080083d2640040e00c0020300343c1d81c41000004821b0380d020f541c1002004858003861000e82c401000713045030550261065400004051071010011020000045d1a800e613070b031135105200c0043c1d000905010900e004800303c01541388030003407840c03280c0408003400c00190b0300503542080f20340d48060580c81c1c130410810000410441442020400091598000350842d510b90a1050040c0300b01e40040b402e880c284854011080e601a2032154000001c50070307101ca00c2c450300201507880e40a884000c000d0b8100304005000f284403680500030b00030240b80a4012281154503403000c40368008001c0700824800304082d041000154001e0310740034101600d20320014102b8031030390311003250a10010305a4600d030780b070401001804810139415a912400407100039440b85406441d141c044 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 554959865 1250 554958615 554958619
    0x90f03050d1106070f0e0a120302061b1e07030309020303040f2c071d19140a06021209031612030f03020a09170c030607020616020a0203070e3102 64
    0x1010480002a021525038002c4904c0c2c0c60300d0980d040712810945250031282d9007950320a1840000103480c404003501c800c2410303c26805405240790060f03c907901002e43c41d0040786d4060b0f091280c01d1000c0000c1050034071444042000750744480b01e45c6000ca014000504000750540804140080c00c0d540080e00341040d00c40c0c1014070103030300742125030840035145540414005088903c0105101c5401140c11501048501c4015001c1c010030034041001000312050301514a421000100003030010740e000c19001c90812200440d0325450302000960722109001025908880090242400da408200412110410503503144140d9034401d007020418054043c183d0100b4070401035203158501ca442241c03407010705901c0d15994103092146440082c400c182c3d94070603034845c0d400300141d1036500300003061259803194010b010300d24100c0c00c080c2c0c000011440c503000750342c0076142c241c0059401003243c0301075170081e40000c803180d9608000c00c040b00103604560740c003895000c4642da02012548011301980f50003 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 554961115 1250 554959865 554959877
    0x602191d09100506130f0e10051f082214010c180e060a0306021605120906040b090102070f1d07080f07031d03210601110d050307090f03050d 62
    0x840d038284580c80004845100d0302c5030701070350103110901d0f0100142200800701c40b034104a65031190760f10800c1d00000e412407500c458031901042000b0301400e03032201c050b00043d100403403804094121030035540003500c2c4001c103200035840010a180065a08020401e18151061048011a00f4220400c403141c203482446035080442c0411030f5401419140e03991040840f000c05030354601420920641405045158403032194000040442c103580043d140c4039444050110136000175240407031404200881c0d91003544814440c03120365546140941c3e0403a00c1d03902000d5562805600100d0802440f03070003102079440d01c00301c0400c64246004089105810034060b0158a03201c001041c0d480c0241190f144068140c1e10b0300007062203200790040341e07c000204000e241d2860315000820b0841d04650405401030110140c4128107560400103d50000001e09004440700001d048641e243c280d002407080900800001040341c1314400d6401d80018403940364001801c070340300d1801c107440e0b55010b1300310310000d80 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 554962365 1250 554961115 554961167
    0x6051801260109051b03160c080315040b15071520040608010806061c020406051f02010605040e0d23032806240521010e070801030f0807060219 63
    0x5940c01050005c19040c1d0350030340e9a02d002c02a80c1c40340000066081100030f83e165000500d0440182d8020103480d260a40460104400c0c081226030b054001031240c4044000741e1104000749048a0645030800c510088005104490b1005842c04034182000e00102500c500303180271028019106640183c3d4641d60540d80e50b45849588110035203d05070700075008020310021901000e103140d0810302c060b101041e0203664200181f5042840c2d9100d0882c0c03030704452407603800c56080c07003550003400040302c0820040604082480e5200f4514010009102c512003c0841c1050340c1d07880d1140e142107000c0200d90302d180c13103d140d0840c462514645080301c1340740424030b180351204e03001d010141c1c2c41c010300342c840c04040d032004400700d446003c00c1042807003c2080502006010002503403034540e42850306040551414111034030f843c000034800740c20020200b0041c0300280280b500f40130030355005541e443c0c0b5000603040001c02482694222007010b0040c086405003a03420182c0001c040d040541d13180e407a00703 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 554963615 1250 554962365 554962381
    0xb07081006030f0f0614040606230c070810090303050c071a0606090312072609040c050c06040b0603060603030c0c0d0615080106030209100605180126010905 69
    0x840030349015852960000091150901c81d81c41408440c07003a1074045602c1c0e880340041400c8504580140f41440d4901190110300e0809000d0040240381a20f00708a510890000c4121000141e148a110100001030081c0c1608030401000d80540390300801e0703550100500d03405400804a03018228042814400040c4c6c400a03941c081e07604013a0042d0048502d050a10500360848000808140e8092030030300c00c02c40c0503281001000c0f9038411400036999617030013604142c04604101d0144000c14019404906030f01040c150603206501c0c001d9401040082d15258180d0f21401400040b014901c03c3d101080103000000c058240a080d044e01500d0441e22814203251322072207030ac407141805074072582d201e481600b800000800000d00403680001d21680084a101091106a003c0b80382c507074441c0c10030b000390b03d884004182c2054000e03541014480c85c00f03034054400d018416a081c00a90400d031f08812a034054003244c410109410140c03052464080303004004140c00380190500d0fa4078000c0091420 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 554964865 1250 554963615 554963627
    0x17040812130e0603060609061c0302010f05010b03040305040306090c12110103050702010e0a1709040c0207061d090f040f0c12110604081c0c081b0c0f060d090503040810090b07 77
    0x50680a8040c1640b65a41c06c2400700d0804054030050708032038203000541840d84103a4002e8003c2c0d01c0b86c1d002240e0394a44901407400c0c1ca506070800710f1494020414080000e410400300c0d011241c2c04500420820401d043c1040c01101a6118a1105103207845540811002411841c510703902624100865100c8840c202e00b00c4403c0020081582c0c4640140c1c0c0c0420207111034214061400b40c1038610380701e0b004c1d002c43c0a40c0e80180c005800b60b4455841401825000884035950f441d204804505d941c10040c009403120401603c802d00c60005030340410b050000c070380581d0200c00c1c2c0156010348401e40d1144030300c0d0f0b05000c4481c20b9603880c0000402c0115490030004507411203c924000f480300c40103110309041a00144419002803100020701000040c01190107030020081006400f2039025040b0311b0b017402d061282050350300c60000106603440c140c3c0c2e898143c07083d800003003c0000710a5041d10f0007528500c51a0003820fa1445a5122050b850b1202d401800b810b5220754058112511203700580315 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 554966115 1250 554964865 554964871
    0x32d050906011406070203120d02070302061302210a20031213030209090f01090c0f090203090706050f07051603031403090703020f040b090403090603050702071217040812130e 77
    0x4601004000e00f2645410000341900d2400141510081600906045507a0b8440e11080e0707a00b43e0007043c840c0505d0703014420158004610380d00400c02c18825030000d08555942c0090302c40d101d003035907260142460100482c182c01640302060843c03402c80a41144004190000d03650710038407500c201c081080100c2400d81d110b4003041d0f4481c0301a181140d0030448a00c0c00209240360703500c1030007049490750388240500c427403aa003c1d594240d006420b02d0040d0316001d81940142240d140104140440c4004c00600d07001100d100f85042a00c404061014291300d2044030750141580c4203035020b1940b00c2c5101c0c9800b4040381d100c0d0700d0fa051112012400301085000c2128006400e0300000810809410110284d02c0c00c1403004100080c08c01912001994010702540c040d000070300030b00c2040c050302e0340520a4503045407403070009000940c90300c8110501d010012200414030018054040c442007408015940a85420002e80c0c0508150ba03000f0807103034008a2034560000248031000427985405901680 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 554967365 1250 554966115 554966129
    0xb0717040506241e010203090a03060e0705041a01030b13060b030f0109060e150a0f1401082211120d0f09050a050f0103050915090d031a01020d0f032d05090601 70
    0x71100110701c013408059000700c803640b81035020412003240c0b103035607811a500265100c1c1e0000191998003400c81490151140c1015008519200ca0025500c400c5c0000d6443d981007468040b9a1020030b0b008610201f9924540801d140d08200c6c2c080303215075044d009140720b84001390300c00440381e0762011903c066868521a510000781148045040342e01080309580f00b1700000f038000b500090b0b41e81615003040d00c2030fa001101b258080c0c600108e542d80d2218002d0f4101084480207040708075004c80d48100c0e50042a4010035220300081c641442e034444000d40141078680c0001d0b201c910b1643c01d4042d15000c240a20790b00050a00d200214051808146002c19184007800070703445041d501d0300550040002a145104500c030710044119401d0300701040d1441901320300c000d46150030a05002800fa00d08002101903603403040d10741a422070743c1c0000c00708120315251510400843d40380344150000c01440f8030501c801d0440c0b04000c4d80c200701000c40c120301c0b80c0b00314904110315640d03811030503240c20b400e001d400 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 554968615 1250 554967365 554967379
    0xa02120c04030c060818120301030b0f1902070314130e010f0e0604020f190f030624080403050c070806271b060d020d0501090b0d050a0b071704050624 66
    0x300120340710b03038a4580e21480034080140c0c083d01d60f140349441d1551f03050240000b20400030051040203000c0380d00036000110305140d620b09080c596030300c1d0303c03071040d001845d207a01d039010494a003494403d2409150f6141c1c4491090b58071081c01d882ca44060b401d40c02056040c5484000009254114501c5201100d6030880c8514840d12038208110180d800340900f04844041405801d803a040058a81c9503450760701e80340d510f84e1241401001d41607402d180e0014040d001d15590202880111420035140030000d460000f60701d980710314054038079014103408031605204001021401101c00940c43e070044100902040e01c603074002e13000364400d02964031380010301d400400c0340c1c0905815243d103000f0580c00042c00582004410384180c3d040b85c21001600144940319001040315201505c240e441601040d00c0b40c0c03465602d5521030f0b07543e501050f917008040081100005100c0c9200c1d100f50100039941044c001c0345820103052540d51002c060b20326180110890a072007002c51510f4107032581d0314501800d80 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 554969865 1250 554968615 554968619
    0x6120606041e14010603060f08030304020607020103020724150302030a02130f0e01060320150304051204120302010c091802070507080619110f0301030b10030503030a02120c04030c 79
    0x403001a000c0854848107860b869110a03206801900541d00803007070307280f020b441943c50700d80024160381c40d0b42c2c070038800540340501c20310040c4000310880f640990140c80c229035400240c40103c1c000c3c0300b850006004000c10081d400074076140031014040c03486c0d81070014484813135550000302ca10402c41c400254907a111565400c0141042c0b00c51804009840700c1c0002c039280306100300c3c82074400840980d20140d64914041c010048501c0301c4c025050a101180580c410008000c610901062510314488820100000d81008400c000460b4110481803030303035403070325a40c0e80030b07460704c4000c008210055420005ea12110901c903010010407140305c07c59400081201c100418000e620507102903546024409021416200820915014094035045107841700070b0800d0036000c45541c2c501d01e2001c1c103000c01034101401b1121050b03d0640350444640d6102e5201c40200750411400b41e03000400c580408010000d42a0741603025100841d01040c0343c080030380d90028800d001d80f00d580402000c0c00b0b240001 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 554971115 1250 554969865 554969869
    0xd12110a11100f091e0b01290403060501050906040902210a050d170901050601020304140f030a0b060406050a031e03170103051b0d0c152007030201030506120606 71
    0x3402101c5004002076420030901e0049103410341d0311a02442252548510100040091a07110700341401409040100305e00c80750741d10045060810f00c01c0345a0b05421602d00802d00d07003948010794203175001280e580d83d52541d80c60244040d200034819588200715000010b4071030308250044900581e0300038180c0c0d002454982071007200c101d01034100c5019104103240309000600030410001880610348a4243c101c564404035500560024490450384e4107000601c855643c000007a80d05540c0006100d036405014900440c40d2901e83c141c10706d915100703585042e400d100790f410b03400d401a101070b1414040c0b65103601c14040c0c81030703041c41300928514003154500c6882146c1000070300000e1003850302080200b81c00d42d046050741ca0030780082c1c80c1500203512a1114003d0f00080148140044c1c0b05509176503981e49a08540a00e58071940501c514418403075480c40c0d03c1960707083e50700b40b8000d008004a505008034140d0f614103901040740841c1c0307010003180d820f00c0d02030060a00000080c0c018446076644800b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 554972365 1250 554971115 554971127
    0x20705060a0e040204230a152d08070e0117040f050a0b0f0a0501050901050d0609110a0305070f0504053102090703090b0f060a03170f0c0d12110a 64
    0x240032001c00c584a49044681d90b40c3d40024401000705103000c1c40d5202051141080c03403171805040c00d2045803190380c100840301c0401e1065040c501c1741c0c140102540010304040308000038150002c4138100e04a01c640c0c403641d03084002240542c000c0c0e51a203014000490044d41e55000300b15504000c090541d00040c00a20556119070700350344680300362018101507540b0005102420f6130310b840142601c1c1c04002c035250851180d1401484107d031000070740c3d403401021403011040c001005d000c058070340b00404207110510307409951200c400b4100610302075403814580d840c0c03003050041d440d0f0440b20b0340780080d80f0710306805168082d0b171400010000c107804103160500951700000c0c03440050f03082060700c80f015907500d190311441340c00700e90cc0200d41e490381450440d540307100080c40491400c00b8a4140619510360000850549602036617000b0a4081c01040c14114018200300c50030000001540d0b4400c05404180700416a000340c52f10328480b113209054205460400d1820f602c5581c0a000303100c03a06220740 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 554973615 1250 554972365 554972377
    0x706081b16020603131b0b0706020c01090c08100e070501090b1e0406080919030203180d0210050403151107151d010e0c060f040e04080c06090c0a1502070506 69
    0xc01151401c16103901088054208558024200c03280071071070010f0020b040d003c140503415802c99092200d09040310644640074000025104d20307404181c59011140075840105599005820000690b40d645481640c449050b1582241d8509090850b80c92140001d1045c041d903005854a18140b030401501c00701c02e40150f00304511408002050036011100c81d0010805004a9a01c0e4849464140d01507860188422440c1e0014a404c10380c0360b021030340c00300a031111090b501000701c00782d10220300000d8156070a1f0501a6004e4248050500c1980e044401071048070710515110600440c0c12117140c0440d50342ca0103412800d6070412500002038842c201080c14080740c0350700003a0a0316480e040560601107400d40c3c441d0b0b0707036440104200f1010101b0030703010f081c0300856080d8a40100b11010f6103190003644950700884a4801c04074080261000980d101030140808444461502041180c5d950020320003483c0035808034840032860094001b00780440044540041010920b006e0038888594011 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 554974865 1250 554973615 554973637
    0x30204140108042109050f12120c010f1d0c010801081c300609090f080c0a02060706020915120f180d18063207020a0e07020706081b 58
    0x10300c28240e5a00000800001241c00e42e0b03480340741034148020303c0074100110b10a03c2c0722303c40d421100002d02d400010001190040301020f0ba444201c554070712405081c0c1c1c4007800040034245032501010001a040070303100c0010a2007155100700f00140151103500c400e005242041d000404040d005088520a003c8540424601104101503100b0034610f0020080c1d10b079256454140741c140114901c40c0160000b420381101c0801900b066079503004403034102888002d01007480803c0c0c1806002082c03140c1c28809030080e001c3d80e07480c0b1092800304029400b420140d4410004265000d00300d04980050359420b15280203490240e03140c4122280e0305090007000302c0c90f5600c2100002880b168280700d40c043c0b106040d100c0100140c01c0f041000c61740106604040102b0550002c4030184051080b940303200c4242c80901c00100d0780410090511a100300100079402c104219800900e02d940440c0562240001c0d034250f6803c680c88402c1201c4254041e03550600c450071022503252404181c000528554410b = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 554976115 1250 554974865 554974883
    0x105040f060e0a1a0403060908040806100806010e06060702010302090a0f09090506180d050f0d11040e0a0c080106140405270a060602060a0c1808030901020d03020414010804 76
    0x62005044003120854100900140d29100d0724005420711405100140c40c50041e6910b0000d10800d41103802d00032444040c100c5a12881c156042c41b41d4103003228007400c1941c040e0b40c4c00d071030140040c10144400e0302c0340c0c26140c8074000001400706417807010b0a0141030000d100a00d4140300b5001180650014800c003944400c1e4860002017441d09000d03801c0c02809070801c027144103015401c1013802e1030702c01003103a400c140106811000320000401c4d46445510785081103501c03016054602c2c80e4034010400148030440c601545c0b1a013001040d4003500840d1f1410420295560320a202d1406444448090310041010007005001a80c00303540042110460307101500c2c101540c840003d11080c00902d121207030104400b001c000c0c1c8890800b9000e51040142c101841410302d402c100a59480000345051703e6136640b40d5840b41624400d54813442c1c8265154018651715031508692900c9a1188040c1c5026110300201021118060300a850880703101e030034565044200ca10040d911000c0082040300d031090 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 554977365 1250 554976115 554976119
    0x20d05010305010f0b0108060603070c1a130c08030a0e0603130602030412110706020d0e010905040e071404110d0c02030c06070c020a0e0408091e0303210c120114010504 74
    0x1191058500a500400c0040340804c032005568084807443e80d8071504020030101000041d855250841ea044081e510f44001c2e98469030800501da01d040e51032120b4813107105004c1c03080340c501003007030070300041d01500c00300c501d00e0360319406550f4a20031404518007042d0000c040e4891885c0603006191301c200d1081907070052404aa982400302d0b8001c4804585031251201c00304101a0701c0300340c2c40f152004c80c000030080d05042c10b41c06980c4040c0c0b034100c1410030159070b01c29062a4465000e00c4001c0ca40a003041c810364100885082e20380383c060150804a001d087c036042c0d41860f2030b010703a46201d8102c00507145084c880d0241031010788072080000d03040d840200018004448100308103841805283c1c0c8520b1040440c0c030420100c02e1480d40300000a003004420310000ca03c4182c01c65054050848007141800381c5c03024620040c4040403180c943c18040481c0012068a10321000340b6080d042c541c074560300d40d50348030b0030201f28016150314071003040e210b0005001c0ca03400441101c50004050400c20708181e = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 554978615 1250 554977365 554977387
    0x1503070806040902190f030605090601061d150c01020a03050901110906030901022104121701090b13050c040e1b03041b0306050c0c010c0914010c15050c07020a0902090f04050a02 78
    0x145d9036221480c00500c02d175080050100c5481600e801c05200f0300035110551600d42c0c0203110852403285007410304c1e4025500c034140d540c1e0110319071210910312942521214640c0c606070003900210383c03150100381080000b480301201031140382c4030fa9034000c0a4a06081e5007109214080d080100004415075080001070201d41c401800c41038138406440801016140c9803070096000b062801040040c440000401c4414032044601a419101c0001c0000703080411907000035140c100151995100c2840c14081c011180403074401402660440c0300395007100d40794001d001302d00b07400b0007440c1080d4003401c0c40842c0c00122500c1c00701c800400b883d50750b50a01d079281e454000407680d0555540141540008008400c103000303014030050503142c0d0a185860070b2400e660041907140d155445130400c9000c01d200c100b01f00000846004154070301034204414503050018125991182000b41e205005a2000013041d0f034030b40c0203d681402e805410441f0341d140c00b10030f000103801d014100b0030410780c081c880085c00e0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 554979865 1250 554978615 554978659
    0xc0708070306061701020301060c08092707030606080f0a1104030507062a050c0f011403160915020c04050601030e011b09140117090106170a021503070806040902 71
    0x41c40c0a004001800c40c0b521001e60203c4240f0705108007642d00620040100c5c0c1d0700040340340000e40e0410440d5644a070214001000294102940340460200324040e6800141c01710b4070a22070005620100000381c0c44040547d1b4400048800240249142c800030f000000c054000a0012454410490a02d0707140da0b074041c1013483c80d801c4070b00080c01d541c00c00c60903440300c4c035002c0d40b0510403900c281441d500f05454181d01c4c1d181c1121840d01910a0b000569810791203194030a440640e109402516030274031111581e400b004072042900060060b0b02c0200d0540c040001405051406030000c10807680044140005804020b0169040c96a200e40540410500307000395640c0c4040700c2191140900b01080c0a081c041c2d498100c2c5841e490401c0e0301d500545d030130002139500c40402444400440e5505650305014000c241c02c03050455000a600d90043d880c000b41040c041d61003262694800d000c1200c50b04c4440c081264680f00051030030b400300e001810658044030300c550015100c0000769001a010380a2 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 554981115 1250 554979865 554979869
    0x90503010c03140402120f060f0f07110312041112030711060306060a1b06110306190b0a0509041805030304030809010507141606020c030c010b030304050f15040302030d030b0102010b041e020c070807 87
    0x11100750003c11114100104410f40d00bc121410503070304102c840b03107209a4a0080c04100c2c14540303c00800306043c032400c200c2402080340024200003141c00401c0341a912074209000840b00301003c04081d50080c64054240c91040e580a418582480d192000885251503074400b0308445041b0f5008000104440d40143c0030408280016503a980c2048024000c000991203108024002c42c8141440000041c404850114100c1d1400743d48901000700002c000340260721140c2004000f5810282c10004080051071040e4040d844000300e60361510346070385c00d03110204d50000014441c0300700003401044100c040c100007140501c10700d100142c181c0c0c81404982c098138404159034400b052480c0b04020901480340900c0c41940614101072030700010a28041007841c4c6244221030103082d8140480c0800c2c10740340256002411501007030500ca002170b0050910401c21401075081400301d03440d5040030300410201042000300308500c900342469602c020b40040b51069181d005182000440220405c0401c0c0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 554982365 1250 554981115 554981131
    0x290402040e04021c050d1d03061b180a08060708100b03040f08071208092e0507120203040f140a0c060f03020403170c071707060f0c05010c090503010c03140402120f06 73
    0x141d1501d0300c010301c0301194011401540f2941c45641040078861514000c280800f85074040d0784c1d09c4041044131900302f21040800c95810148181c000500c4810001d80c507405042d07280c64818203520f8081d0100c520420600404902590800100b07000034540109044100d009003100c40c00c18115688140d1507040d8220400f0000c4c41200902005510600c28441494913549807003013405c10000d8240c003000710082d9804c1032541d45100051015000e1404003036074900607101103640340341038503281c9800a200401035401d00108100c400c00a07200040c0c4a040d55044106847c44602e410f00c11100d45240031010002c040e024400000060326043d0300100340200c12111503182c081003102c0d00c0c0f400d001507112015000340280002d10b8601e010850509940f2640341403409001c0c03000007602c0b0007240c0880140b05628200c0040c00140c0c0c03141940c030580300110000c0c0916070551400303c00b030f0b502d41e428040d6590b0b00c0801041c018940001790401200d0311000b595103054001030b4250030400c3c00c4421030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 554983615 1250 554982365 554982377
    0x50c1003020417010509060109140615090d08040e070f02061501030b030a110906040902012102120a02030907141e0a12080c06011203080a0207110301290402040e04021c050d 76
    0x1000d040c003400361b20f01401c0c09c040d0400003440c1c0d81d01c10303080c10040504401c1c001c4564140b030b40102c1c00020110f400030000540b4a401c501042d151120306070307005100348a00710507000041035400e84070391602078500400c0c4d8001c2010b0b440e480300c00d241160307010310a10b05169417402c0380d40c0b15440c28042e603c0c01a02850000e800c0042a01c144031201e400202103a104901c0c1c0400c45006070780010003041c5504c4980c205000c6030201308850802171040c441e000c91500400c034100080744105400440c40391054200f65050a0340d00c03001d6040c1000143c0143ea8014242c440d04100000807010450501a004100c100502c2d0b0300c11a110614801c890300369080c3c0d00029100d5285030042011500501e41c03401203138400840c9440080011034050180d010283d000101c8600340050140580d540300c40040081068140c440b49480800441c0b081c4450016035041144040d49424801e8070100d03600400c0350310351a0369030ba0801c0f10740107806054406240e4242030b00400315004012000920840ea1030364 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 554984865 1250 554983615 554983621
    0x3150608070f1a03041703040f020315040b010b071b0b040303090f0302090f040602070203070b0c12041802090d0b15120a0201020d0f0c0b0c0d0612050c10030204170105 74
    0x1030409503a9007011610301e000b403204100d040c1c0c1040d034a88890080250302d07512602c80b89030505407440400c82030b190707144001c0309210034440d144958000701442101140ca2200203150940540e802c2110f02900c0d05003440d0040000140140050001c2d40c840e00301107443c2e401080c0c21a4580156401500c40b8040101e8184101500601c940f00174094000e6600940341c070b16070014003540c8006002450400c10040464104141c90301503070307502da034000c050b104c00c4c98030b032050f0046039003000c441c41105100d07000301034243d0190311048406680044509040e40919901c81c44041d50050f114542c0014508e2110702c041240d11009038068030340c4407040d4030b80c00203400802600510352000002e441d00040d20800050703030002289503460360a0b04124032003103103412096a4452946102038180640301c4100a514003040000b0b008403440120100501d5841c0d240030041d03010920002441648070f5941c0e1561803400b0800c1d484d002c0103a1070702601d4191140f440101d440ca82c43d00d40c101c0b5030344850034 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 554986115 1250 554984865 554984879
    0xa05010203060a120f020d0201090503030d1b1b0b090a0b010e040201120204080c010c23060f0109060b0a0311040b19020f1b0d021302070b09070e0103150c020106031506 74
    0x41001480b0703002000403101140d80b1409568917100c1002171080d034040c1411411a40117484e45001002d00400366616444114031080c0a002807048020011130440d01c1000864020702c00e01d500c0e18884e140d08100c3d20455a04c0b80701182e8003420304912440703819503640000e40d203500200e02034540d44000d00c606050a100140c66100303021604003080f80117000c203200d04900010009001c45c02483c1036200c06640b8242440c181004440041c1008100c48109030b04900001d0180d00400042e581496107030707a1380c0d01e40802c4a8550068101800e8204510301c074280c030a130007041c12440e5a107072003841c1c10782d03401600845510003900b04800c21903001501c01d003190140500c400c1c0c00340020151000140000c641d01200e44501d60b210b00c900544020b01080d500c0d01c1ca1700c4181d400b00c06004540e030b400c030f904242980c0c1d2821a00340c00d140c032800a022582c40300e00d03c01a4100d03039100c450a00f04885814000014000300191403045640e9407400002181d403100c08024022009880000ca060421107 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 554987365 1250 554986115 554986129
    0x1f09030b0a020f0d0b040603061b0914030616030e06070c12030b06041701180318060c0302030a050306042d06060201050405030403110612010f0f06170a050c0c0a0501020306 76
    0x7012080d40c0c4180070300340f40da460060490700c40b008000e01c0007602c9903405000400030400c3d600302500d0317207250040d035005080d400c0e4191003284449855000074503a4500001e0b01701b400340340909030181c0043c00031604801e001200300c80601e802e814042503a1040c503060a107800030407903081c6c0000300d90101220078402401d400e10101e031400d1509104002c0020b0100d031240c070440c0f0a0348203091041d400104c043d1001c0d8006185c42c500e80c0c6207240a8480c0f810010002c401d0313244180e480107480d580c0040c00500030101c5030820340d4141c0155092451108090b90301c5d8100030002a0029165601c80300041d80c105a42c00d1181c07044249001543c01c0d0030706401c100c0e0802c0c2c0125096a00d0710b0240000718000000361011641e024500103186804c21010607861702a07000001031b5494010004034400c100421034409070f0b19200b07543c1c107460ba590801203540412507003194503e280d208003c82d08891f5190001d540c40440c224070280703040107803034143c0d03e0700149884c2038403207960101c00d110392071401d41c0d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 554988615 1250 554987365 554987371
    0x50a03061d0a0f2315060103021b0606011701031707060b06070b0702010b0a050a0513020c060705070201030b060a230c0d020a050106080c031f0f0e1006061409010e1f09030b 76
    0x50340f1200d40c02a0b26440991750f4001e4440039000000c41c4c800685240c2c840e404880c0b680c1164407901403003180180005907101d03000d407101741c049413001c45801080105004c07014122a081203585c120340340d03070400c4240c3c01d910150060b00c059440340e46410060715440010712040703100d00c0a1b00d034140b44c845402070131940103100c81842144c907064104001c1d5501040e8401b501c00860310301100126114460740240b003030030024000da020701d00030004840e40240103050301600030b8a0922400c0141400c1103d00d01c80c11580d0700220309031038544641598071501d410703403c001c104010303494618400c4a0070f2600240d4440e40e401a4000c032008001c2001c280244402402514002c1c0f844812000c00a80c031a000c000301d40ca0b003801118211072088005401c2144120340440c400c1141101c040503842c2c44e0386d44002e028440314281000010000d200741c108a80e209181d0800c141001c641900450301509221045580034030114040c6006410903890092110056101c2058072440c501d05845501001 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 554989865 1250 554988615 554988653
    0x20a0605061c1401200304050609030a0518030c04022a01060602030a050a1b120f08101a071406070908030702010f030e15150f0406050a03061d0a0f 65
    0x19840c54480074a40381c402502a80251840d101410200307405004041c0b0301040e8501701415240302613540009001075001c0c502600070780f41c0075a80c21031011340d01c1c0704280554000032410000000d0709404000d00c0484150b005040da2900c1800c580014140e070000141140110703c889030448040401c1d51408098040000090003114078120b801381d00c03070081c41c059600b44030f4001401c00710103120f0008800c00c500d40d814000c075085032038100351000742c500054000205a03280c00920042d4000c20b10725100b00b443d413210304800b07030400c501c0d48801e080003505051800d030140003000001d4014026418407960300d2004003110300d040701c001044d121140d8000b0b6420f4100704464400b50340d00020407000c50303926090204075114284c03049490004089501006c0d1500350b4107018020b40196070051304032004452041c50500c00400300021035249110342c2d64483d452100800000c0c9080d006000c007600502c41d031030003a000c801941420308000040c122003c40205401000704800d8010400e203403030023 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 554991115 1250 554989865 554989879
    0x807050a050a0308031810050c03040b010504050f070f050f030a02190c0c050d2d0c0b0a050304060f1506020106030201030f0203091905011e06050306010b032404020d0c020a060506 79
    0x20b1920780303c01d01d00c0003400320034505020b4211b1124458040003400444000450204a5858080e83c0c00145410a40e0112044401e5400001d0036150601500b070288503111021112900c83c00001d480124802c000001408802d0018800d8103c00c0000f40d03104003c1c6000140e078514010501a01c043c0c82e2003148003c0c840300708171040214031115000380030740d00f040d220324540c0e620030b00346429502a04860300003070145a420b0443c90f44050060343c3c00c054494030701d403c0140e4903582a20198010f10205100140047c000940401d80e66040480d0301e00c001032000a014000340c03d544c455088030f030841000350307444200c00c100b1035a0602c01e11910b0341080300304500b1400e0206103507481d0b041c0c0c3c910135039840100144460034440c00394000344c0b5150040d0f012510074501c6440013800b5115a11030b00d4070a004400001a1400b014012280700d40d444003203c4220300480d0355018a880320450500c1d400542c01c0c01101f0900d460b81c4900101c46489400600e02c0c0038031803a00d50207880c0010315035401409 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 554992365 1250 554991115 554991119
    0x10608010603050c190602060c22180b040e0c01180b040303180b0403201318020f040504051c12111c09020a0504020a1103070308070815030616180807050a050a 70
    0x41d0201e2040c1e000300e0310404003556015105c445402b0110f04400c2c00d400344900c1a070004000d60600e03520200409016014800994540301b007104441e00c6040e14141a004a181c40c04550300c1031a940b46007014540d0310218007506c8910131001da030401d42046000ca9160070205440d01842d25190005007603046809141c28195a204510310070301c1f142e00b00d02d440c80c04a024030981d6070022400708034140180c003000744810a50340005240110041a40291100e81d11610346090500905100c1c6400c02c0080040e40d403113046100060864405040800060107100c8000300c603140190700c100442c0b0341c4441d4607080d510200d084851203103100702e040c07a40742552030340068491088420484000b11401a25000007280583d52400c02000d002c800b40000543e0f00109038006468600800c040c0d905c84038180e640f0010b04080700c01c1c05400d5941a407101b030000e0745001d1800054119035205250200030100a140003800301d44031a000403d0b241c008800c02e000a00b000c4108400400313040f00c405107054 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 554993615 1250 554992365 554992367
    0x615090b120a0c060f020309090c040f0503061003110d080c01230708040303050c07020301060e0115050c0703081b0a0f1214030f09070e04110901050a03080a030e010608010603050c1906 81
    0x186688185824000345c4c8100010340c074001d1042d07c2d0143c0700600030610503d09045410b10a030300038011202c1c2d2103070b07506021605080c00151988500d011980c00049a8116111010100c0d01c50070704a0740103041d80e240d140051084006024094146400856084441002c400259003c0a03460201907941c07410001c0d01075210211030340040c0c1604000519403100054250700313114490000e034142d803d111700042e5508044880300c2c1201c004000c1e88001c5113007144200e42610440c00540e920750702100f014408204000020502c42c614400e0800710041c1240001c0d0400b002e029003035402e80700b0b40c102d4a05010070380c0100e0848000510300b8107039003000c08140a41c0c0340030241c4103ca003074080d0000601070450030002c41e006000104c58013492480c0520b0620900d29803010340c0c6000e80c070f1400001072181440d120713007070942c3d070b11840040c1852800c2e18114024030a100e4200011744d21042d00140301c80007030fc2503901840c02030b030260070001d482c030091084400390303000d02c0c009541c20004204041 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 554994865 1250 554993615 554993633
    0x1e090b06030420030a0803012103050a05090a0f090c0801054203040b01060e04020403080a080421030e0c190611030f03070c060b030f0c04090615090b120a 68
    0x60b40026208501d403030700a40c02d50070000720341c00c00e43c06101e05c102040c203001d1400c001e075040751007400d8544045019080303044e0007200c003036000501040040c802c0212044c000c40190044a1020701455405c0340d940e00e00b654071621a50041c40001d6540b1034404845070301000144c094401690394691009000b01102c4669001a0f910440c010048800049500c7c14088810030460b6a120258480c1403e00f402500c015082c82008041032004800400718201030003a142240e41001441e0f003002c00750501912011360052049882501c000031407104001380c10540614007007160740c0064400c40c000199443d2101e03213501e0354454041c01d061001c4007411f01c130307910068400502d0140c10103182c0d10b48031480d501482d148603105c420007108010f03459034040740d023100980c020401840302000c42c2c0c06040c0c403028104420f880d9500144a00b01c0c2e5414603420480c0002c0c0b0409000444a240c80312890700200030750040c00d20640c030b68950038628981800164002102c06016101d1a8180e0790f17405c03c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 554996115 1250 554994865 554994871
    0x1905011b03090b0f0d0c090503240c0f0d0c12060b0301050604050609060c0d030b090106050325090513090b0906191a0409111311030c0d02090a1e090b0603 68
    0x42002c0010f451a025080c0d6404e841e62001706001c2807000c00c81052019201c1102c9004180c003e12902015060f2901d80003880c038503110f1180d0620440c2d80781c0300d54042c09a0302c83c1701c002100080c05c00c0300e0b4404043e175206070190300b43c0680d6001075000110a40c00e05986540d0f004004000c418401842540d07550030484048540071079079542c1d00c03000b1002140c4030740a8038141c0d405500440c00616840c41d055004034051043c126441c181c568ac95030f0080c0c0e51400242c558910404045106000003103203a4a00741d11120309041c840040c6a4030070010390402580d001d2803403e203480f00010b004120384802da403034211b00742801030300a43c60008003200c0021b42c00541201c4050312840c07914001034000c0c003410704814015005000382d80f42800c00e42d42804e0400006404bd541d5020034030016540c610900704003d500701074861440c0c4174109941000e420881c04542c590790f080080410903510403030789100030900702c0300314070010022403034820100c5074aa001081890820226034216903078001280c2e8 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 554997365 1250 554996115 554996129
    0x2030d08040b0c2704270b060402070503180a0902070606140105070f0b04030c02040603050f1204120305090307080f1b0402071703331f020a201905011b0309 69
    0x18a070b10000c002030160210015041103061301940b4540000c5540354038003a41b501807410001203484c3c5409000c1240701d0600080d000e03400601070a0034110b500001c001800c0402040740c3d000b02d80700c0038240102d9100003c202c50082c0d841d841001010034000303c0c109000000d00380320307007004042d80700c8038001502c600b402804855004006000c01d4080c00d0019507244c0c01800070003950b6101d00c0c00d20b60714540c3c10711001c02482039000749402202c8410444050700c1e460040460308120542d0241c07107607000740f08100c0d458019000302103102e4000300301d0031140122100007444c40d0781400c46240c1c0509000d840c4e10703004a004020b2440802d128a0390700340080450345003603503690b0312280900c0442d030403000c0e409204440110240c1482c0c1310701c40d18480031607013142c08c1030100100e83c03258400030009848080158001007802400b242c0c1d007043c4148201c1c200c090028551908000140300c208044503a0740700000c0b8510188140d50344029000d01079694100e02e143c5a6415031400b8001040d2486070720 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 554998615 1250 554997365 554997427
    0x302150a0f1107030c06090504050604061809030507021305070908120423191715010632030a0501090b090408090f1507210c0b100302030d08040b0c 65
    0x1c408601c1000782c20020364104000a58081c6c8488006040f03c0d218410b451103130782854040344040c9450701c5044105c50410744411288800480380c80e01402c079400e416001d00000344120b80158548114100c00078003000070004461604180c040c3c00604250400a8160301040c40c0c405004004002c41c0e050710100002c000c0702041606010314010310960050350480415601c04440420114140c01510b03c210401079400010254595a407803090035502c4003c261b08004000071402032800600404144020191001d220010b16174501001c404100d0310940000403c0b011048a128030781c0540002d0700c051000d0003041c1c3c0010840940a0000b8084020010303642d0101c2c0d48504061000d0300001e8003200464020318801056601301401c140e40c414010014010003008050701400f0385091600c4e0b680c0d04440d1130b01d4113100280014403450210304c4405020016075020042190108401e54444101d481c1c0307480d000f450802c0140c4542e003c440b0501080e4444011046400e4410603000020 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 554999865 1250 554998615 554998637
    0x803010603050613022118070b0f12070903151415120709020d0c0509060406110304050405090d020d030b150d0f0c050705010b0306060f090a06030b0705040302150a0f 73
    0x58414a080e0008414184c400181c207106e41c030b11138009032208150301d400322110f641c0b00901b00c60000042d502c451000e40140c0790500030001d0650140c0038403003407050702608081c2107540044080106561040100c0e00c0d60b0300802c10444099040280a030248800b07000d00d90401c42d184480504c05052644e104c84250203180c1b4a4541c00140c18061390950111411140d40c1e6201000a41c010298441c0880c100400544480e02660071502d2814024080d00e152915112040b20b81078030354001070600d03000400000640c0e17600c50181e01d000e014008040d005016250301c011b4507205068020f6024035040a031111501e075500180e80c00d40e5503000340e407180d80303180c80c0a05400600840c0f03800341ca4546040011140b00b90f00030050450148520000c108203503040e000c00d945e80104454040e0b0007000220b090007075061031a01650410338000c00070942035182daa490000002c1200ca00300002c4011070308006610303180c0c841042040243c000d02d850004485401050305081144080c1445038000d01 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 555001115 1250 554999865 554999869
    0x402121909051e061305060c0a05191d030d020c060904060806070c0b181903030f09080c0705041e0e210d0608030c0c01030c09030b010b09030d0c08030106030506 71
    0x30782603140c0c01802d9610911501d4121010620b480011448a1182c2c100050052039160700440107a9001801030240c0d96842c0350203082948450110002c1000502403070340b104c00040b0100c002d0707031800d13101da058021102c115074000712002e54901d80700c2c0d80440e040b200e980750042110700002006031419581c0b00744a07030100e805080c2c1031f805018248100c404001031680d01892068104c3d126842090705a140e900754212081c0142d00002020303041403c0369602d800d5039aa00403480c0740b0904011882c05600d000e0f10b002c80340b6401056543c16000642540200c100b071045130301404040343d0400180c40d150b01000002540d080c807440f06103503900d5142d9000042003000004404d90b01c144841040701c00d01c1c05080b41c0d00048070201070a8100680812003600c088169141425600010700140315103800460186c400344000b0340901000c040f010000c170360701c080694043e09410203526540e00004061600c0e1042103031100d01045817030301c840c03c0042c840c64105c038110303599407602060a443e00c1d00 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 555002365 1250 555001115 555001121
    0xc0114120a0b0f03031603110f070b1b0f0c040b01031103041415162a0f0320010204181503151409010f1512030302030a0213031a0604021219 62
    0x304a135040c80003050310081140e04210440b91284a6030795440c1ca40b0302d100042e0f0382ea011418620440e6040101e041c007025074024094015801341d2a00c810106202e19030b220b0400b00203185108203a0080b2070b070078142c0e007001c2c020b001c0346001c02c2c80c3c02c2103100d04a810b00315041c08041e00040c035030b42c25040020000c00d0204440c00d05441d29165140e25400c011414440d4a204c01c0100004121100c0004e103240c41a04c2903460038511092030251154115580c1c0840003c2800f4101d09000d01d40303510260f95400c000c032150003d0401000147c0d50743c10051105042d000e20034052264074101041c20280da40c004845004803070740725001007070302c1480000020282009505045580c10b10300704000b02001e05401c0801d0210307003060100b02c0c142c403980d41a00340260b01d0050044850010701d110000034480d81c0110b038840f0900b2303001810440900c07000c00000d1080d52090703480303038001600c00112907d02070f021a0002d1085804500d88500711380903501c01c10000307080c0f1f202040140c01020304040590 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 555003615 1250 555002365 555002389
    0x22104170f190308060f01080406092307081c0c261215030d08060d060603050a081c09110f01030b040501030803101406090906031009050c0114120a0b 66
    0x4040e00c0101c82c0014002080c0d410082d0140e00213110703079000c120b9500b019124203a083c0c0d4103075031310401540c1d2500c401000c0c18804000300c4482e041c03030070f04880c03104404041078001700701d00024110081c5070100640c03800401c0038155016641840009154940100a07503042c5903010800000d07074241c1460f21070000c3d034113a618a22840c0c0000b191400044503120b51413048020b052204030780021007060664508410740e10078042500640071400703038074090300080c0b1407912400340071034500c1c0c4031f9459a09003410000102e5003c03002003040349034095584201c8520043c010010000c02d02a9204c0b40b502240c51000740b40586005050100e00d039100c1c1c0c000c9000701001070014082965649040d007803d034001c0301c000000c0e100b10400414030a54802c4504e0030400014045030402d075000c1e041043e80503024110b41d40c140f150401c441070803400c90041082c028004c0c0d001c1c121788103850700050080c4034000d0051407a40410002c803020900200130b000c0d080140b10400240c900c10f210702050060700c0c2c038 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 555004865 1250 555003615 555003643
    0x606170c0906120307140724020a03110c0324010e07020d0f03060b0a1701090c09031101030612050601060f050c1e030904090807021824061902060702210417 69
    0x41d5208880358080018804112812100c0e40308d01022580d43d100100c2c501c0e01038110050b00a600d503a000b0030720070f041c06241035885a059615404078400024500f9100d00e40780f181344080c2c031819100703420b483c0403a94014619441840c04504c1c041c90700035202c03040307038568005104100c500f03070800c103200764440800f8114820711541d03100c802103005480070030030b40c2a0402d64800240081001c42c0e440c01020f0a6042c05d89a5000c02c60840c0c1c1d81101002e08030007118105030f81e4540004800c51078000e007a00c1d89001d280075018039414808001c151201c2c999038001070210800a507100701000042800f01d604840d00b000441507440c160b05d43c1035200710480da81e8001c0c10720145005000521006040c058800c503142880441c91400321901300c01c0840e0303505d0260000c4140151000b01300c0b0181d01c1c402400602003450901c40d5401c442c0c6110240e1a84801603101104101e00340350100708407041c41015195018140b501d090340d190051145000f00b034082d080f84000d920520070304010301e95a0b1544 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 555006115 1250 555004865 555004883
    0x5150c030702070b0304051c0c0b010b0408100f231009050f07180b03101d01060e060c0102120a0203011403060c0901030b030f30040807090504080d05040606170c0906120307 76
    0x40d15100800444800e1820744ac480c001c2000040e0358040032080324100ca1513400034000022003850410300406680711850803c0d0b445410305000d40c101281100c1541c2e00694688600d82881c0c80b18000e40350b0b07945c0020710b40901d000207112100400c051910391100e01858400c1c5038000882201c14100703000e9011345220407011042c0080090f942600009560a020500070107034604942d9541d641030a00ca100041075040d05811000c0c1400e60081c940500e0304e40003d464007151103103420000d44200e03610292181c0c08070060001c48041001c24804060403401002c05061002c280f42e101d1268020990516540d400055590b0f00c003800302611400031181600c8862101c10b945503902a11a06c040d400c005a40c80045174030128601a03030159144440184410303424810024000d00703020f04142c80c4880c040c07103904d14100075401640d204920665000c18803614241d080440c0f865440344121175a0440c00404605440d5001d85641c4680201c41042c81c2140107040103080d842034001c09070440c11 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 555007365 1250 555006115 555006163
    0x180a0216030503071101110403080304030908060c25170c07170105090706090b030103120908030a11071202151809091606050708120705090a0305150c030702070b030405 74
    0xa0490003840c4502e04c5611003171040fa241d9a001401c80d00c401000100715401440140007286812010f95803040c80381c1084480c130354a940b1920700d410401c945c41306000800003641a03540d080c22810421280c82d40d0000c0344050390b19903070514544400194480c881d440070414020a24042040e50001c1c0707940f86603088040000c94526000e410100d446000070302c14114002100d80c860f003840b504031070300c54407854196401c41e55038085044022440c00300300a030000c004141004140024050740d01e06460f40c003401515684003034100072050f8044514007075239212035000368440c07a80c3c5207401481c000724150781c2d91380d110307450b01244908000260441e120703e0400c2110000000d08607407058480703c0300d48181c1c3c3d980904440700d100d1020000c1c582c9405124010a4840c004401d41d0040d1090400c00c0c01c01280c48003207642d0702c02c903510544007a401031410281d5921240400c9400003491000c45107980341c03251000c1e507103078181c1c401e00301c80070310020001d01030210038002c5d04800c001c40135068103c03403 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 555008615 1250 555007365 555007367
    0x6041101270306050105010801080d12111c14070903080c0a0804030b01080c0301050712051e0c1b28031101110901020613030e01051b07060305071409180a021603 71
    0xa94500040f5107043c54503001003010743c051180d8a0480d4114001040082c040c60021110079100c44144e0302042d480304080601118070703001600480b554180c0303081da1200c0100250040e0b660b007106008080049805101c40954171100001c140c07500182021350720384030603030801e2030091350b602c01800003440810003108006003542d1190481d6041e000f252040c5422004050803190160b4025000c41c0c05040480244080384e000540d201541010040345820b644805400d114030403503007160401300000303010790a0819600c4004807290680018004d03500c84d06008044124100344c2d00d6410003c084414080600c5031940b0100d81507100024880c2c41c0c4a4401c3c0c8440f50420300200307016000b40d40000c4c100210b80c0b414107120079010342e1002d40c105990001903417a58450340020b41c0c1d03450b188500300c2ca00b03041000039500400f0542d500041c82d26200d54014280191400803a120140401c2042c045558101404078010448074041c10307181c80344002a002403142070303080d54180c0072000360341c1c1c281 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 555009865 1250 555008615 555008687
    0xf1a06130503070815070201050c12091e1c0207030b0f180102070803061509033309070806070503071d0d020904050a03140a091401050c060903030a0606080906041101 73
    0xa0500d0003ea2480703510b4482c0c050b402c2c0d49d42100e50130401203080c410618058520b402c40c40e0454811420740c0e854521f951554105a481c8490300c1007aa0b0020a0700365420307800800d000304d410b14070700c054a4820b0540e83d8a010407903018101290181114021513242c1e18a880c1c45c050303041c94200219034801603460700f0b040b250011984c9501c02e900c4580d074801d03122016800c42e41800001400b0302440306116008280e804104203401c41c030f60079006000928a0712800645014407142e6004003031540c0b41c40821440d0040040075030701008000c1c07060200d1281c110034000340c0d007001410009941c540c0c031004240c0391402c0c0203010754044003402c01c0c0818840b01144030301400d40a03a6a0031441c0107801d11801ca00d21030780c5071401c0019451a0108440c02c1c090006071400c8074145841841c210507070420925150741540d100f800c9410020030310001c0d60a502c1440c000b0072440c1000051403402040ca1525082c0080c001303442c2c40c5480070440001d070706c5500c0174902003a062109401821810b0b928a0803 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 555011115 1250 555009865 555009883
    0x402071707140601051f030903030209220c0212030103060b060913020a0807020304060e0105030c04030209010303050a02251701090b09032a1f18150f1a061305030708 73
    0xd40e005503000490710b0300f4130280304c1b0203483c1c408899103850250080c1c00c03401490b2240094040590900c1110f0142c0d81d80002c018001d07c601000001611810003020105c03a0315591501c1558424030000300e042c1942d0741643c0c1100d400c1000006c1044440011407e103200d40c0b01050fa0241c19012001d00540466006e4075441d00280e459011554908000783c6e43e0b44228044c00c00440c0020138100d07000d61052008581c0a49849a0141419507035070204114090a81044000c101c01150394036820358100303d140845000c1e401d545550354608411800c0d50100c50294199022000442400b501c409400c0700700100d5000001d10000c0c40c0c210f68090f225040001107003604201d030090303c064074040f160035078005880c01c8050044000e540014040e04030510b07920002d450340700e52014a0b19103240c21101f06150003000484103a912007131007a4104e42c10381c1881180300b4a082d1000e4060b01a0520780b614801c01595010b61b03524074080006410309856100341c0c0d15118080d0080f849500120360004 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 555012365 1250 555011115 555011153
    0xc08040605130b1f0b0a08070225030f1109010f14010203031b032206090201032d020c03161208090303070507080a12020307030603020910140402071707 67
    0x3880e295068030400c04120124081e10070f04010f0041880b40c06101488121420740c0510120b01d01e50b120380341a0300d604079900840100b5a544104000240c0600c011b00b04003c0499460030b809081c050741d2211001503000207014800c281c0000401c001030083c0701545040014030f814195a9144c080d0300c00c0b00b04900a480c1c101920100d401c02c07a50001090b82d004e0440c201040c96031020314a14100702da04000c1800030440119801051403081041091320001e000f1900813a0f105c1c8980005402d4a040303124041c905144006200008a0072550b44034032008119405695140902c08240c82c500500c10121410505440958100002e11901c1d9150f0074543e12000300507616085519100e0000b217030400c0c0403440401040d00040e03282c400601d02c204030344c1400b40714103880403044800c81c0c1003287c40030b001c0fa907520720500075032920308482a0f00090b840f080f00c5019042181e540d001c08400003420b80102c0d0045019820090868401980c200d41a0300490721000f03241014041895079000c290 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 555013615 1250 555012365 555012371
    0x90f04020a0501110601050f060708040305012c1506040b0a0e0f0f0907030b042103020307030e0f070b03100801090f0312111b01060915031109040b0c0d020c010c080406 74
    0x10740f0750044a070000103036104c50141010341c0c40c10050000601002c0b0303840303500950810001c00000c405401405c0554081c40001814007004078280a92035900040800c140c0114424140c0d800400985142e8520200c045100280c40f1140440c020740a000d0342c07141d004810000105880440c4202188070f4242c603402c401960701c455400b61a02d04081ea1a2015a08624000d01c041555942c4994100340f042401c070480c012181907903191083e01d805c0c000002a000402c0c401e600b6031601640b60041c8015018040201309902d52950310000341c420f10005010110001342021840c81d6030300014943c1c1402400059450310301440b64013000c481c03c6020411a0049018000591282000c10955600510315250304107a44020480d81003100c1c00303070b80d9203031540890302055030f000c2c02441813440c1c2002c1c01d07200e00718a01700c140e808070035441c50702a41500e0200001f28ac018415107400c44084c1c00b05550701d000300e902c070030083c0c80f5000c50041d1643c24140b9807000141d1104540f403003980560410 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 555014865 1250 555013615 555013619
    0x10f0b1504030b07050307050706060312020c030726011806060501080c0301140111030705160504140f1b040b0406170c1905030a14010801090309050a030312020f0405090f04020a 78
    0x20a100d402a400090714030100000050300c00d0340174000440d049240d508006042103500e41c0c4003815500c441c2c000300d6401d0707000200c50070078a40400200500c800100d014111319410312a000389880e15129612043d15561019800300881c00c1d803041d84024020088a84c1e10034a6040c0f0700c024010600c00c090000d42030078001a142c010708810349060380d1a00c0507000784440d50800460300f8000c1c500c1451118041000794400140042010702258446e040d0010105841d02e000c01046404810794010034286040400400c025095400c2d036009a1283c0d10414142c030340b00b40740d4003030f00654129415078080081c01040e8150404502740b025002c0004100d10f582e0340c00008022405000c4007907155600404070850366a0082c4090341d07101541c01c2d40040c03030000419010780c04800c03c0c0d0202d0ba480e5500d45880d02803607845801d500250030306030307454801c161855230001c0091311001c844048056000c55aa500f16040800300c070002c040081038007010b42405010304484100544003240708121003000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 555016115 1250 555014865 555014899
    0xd0e21120a09020402120f01090b0f03071a07080a051305043b120d0c021507030c0e060703031d16090209130213030c1a0f0c0c03010f0b 60
    0x1200c0c500360314040203a10540320701c00c0c880e01900c841c02049a0042d002c0c440a015021201c20251160a5880e0301c54019498042d185040340e09003003400f801a011012243d543d40c8002546808461814100c0c242401c03090600368606c1c06a910014061a4009a4aa401a40840a05607020b10719410100c1c0300c2d03803581084102c440b44018074080c05514450403500480a4081100d03000c4440503a100c07400c00980c480d0300303005e02d10034109080700d00416102d07103001c101d11501c2002c0e1500e00050094424441201c440444018403407800c0548070464241c45901c92014001400c1000d042a51a4000c40c41e0140240c014050307210700c2100f0140ba2816a60740c0003510074280710084a803000e0341410b1081d82c01c00381d4403140e85242c002d5101303c1100040041d620081104031440c0742e07600f10440c01c502d03140c070000038690b21080d01d0040e02c5c18400c00702e54a9408031030960481500030b65850108001040c2401907650207294503505e0306c414404e40190940060303000c01401c441b041c140150b02c0c04 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 555017365 1250 555016115 555016117
    0xf0f1c0804030e0f0f0a0617160918090215040608071404060e04060510051902010203091009030c120f020d030522030203070b04050304091109090a050c0d0e21 70
    0x1070181c00152140480101424501c41c00b034540c0c000901070f040640510404155040c2540e8446400612000c1204480080c914142e0f9008601031507000c040d40301c613980040c6481458000c019480540c0300c500039420040b688445141a800b400110aa00c58120741710f030321b03410500c50100441c0c2400000341d8841e110b401740d03d6020355410061420181452021070300681d00540283c7c200360f0354040400c00b955841501070806c20190384407685c035440170700110410a01d1100341e00a581c010301c20702030322010228540880081200002402010b0b50170100c0d0300c00341080c000f5200c0c0c83c1a910b0788541c694880c100044446c4c03c0d4003143c0440b0710489080307045850469069000c03103811909415450290102044964000d204070b034100b0740981c41c1d4000e104020781c1c0c101c03042c1d407001404012110b01da005014411044503200d50418500001003580740100410560310a503441300080c034407040810588100302c02c805810851042d0f0350812940d01c240c0c06281040c0d551a80c69040021045c9030 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 555018615 1250 555017365 555017371
    0x715020301030b15181f081606020a0302060615070f03020a030e0a210c050a0f060201060b03011d04080d0c0903140d02030d0203061302160605060411040b09030f0f1c08 74
    0x684405d0b00407919202c0c0710b50441c40504030640e4407002c0392014580700303000212507015012200140894080c4c8082051030314059a1100042d50805a0945c0100340c001c64600da0120303060b501082126005910fa01c140d21602c0d1006060b241541c01e24001d00d0303800544070141a1003601c50b140702514000400034031301c0040c4280020007031000c80307144055041d041e000003da885004c00d455410b4540c0001014248160051400700300c200c6010040554240220b5000b00340c6030184074a1541030401c825a80e240404545031401d04140c00308040104201c215000482d00300001c124454040600402c4115030b840262845d00c051400740b2840307040420707440d04120507070700218a001801c0c1d00c0c07800a5040200403540c001001c9408080303801ca2170004001060341c4443c41d5030314000c2464a0801c44002604a50080b8600001d120305118000304644c25111142d0011341c0703411210f00080d1410a8204400f0031034001d0089280b40800b000840000324510304914800c05041082d084450000403 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 555019865 1250 555018615 555018619
    0xa0e0901080a0305070c053303060f0d020f090123040c021f18080318010605030709020f040b130f080d050a0804020f0a03110310021215060715020301030b15 69
    0x800024800280908010140c03541b0070341c4c10f14070140e60b90f030029400c600940d10140381000c1104148407038024602c040b0150355020001141182443e80110f108484841032890080a80741d401c42d081d9642c00b510502d844000070322400ca19a110300310001c0e8003003002c2420300070321030260300c0000514180c00f542209002e00d500a1448426030a42c05001030714501c441c1d4401a61180c940c42c041d801460f0b042d84150041800545e00d04040010f0700e0400d8607001e200110f64074000090000e90303008a1701908680c051040035844103001d640b920754070f129039403000480340c83c00544000c454520000a9003250004e58486d0981d030703584d9464584072032240c1c003900001042006840000740c0a1104207411500140904601c0094030303012410b42e07100d581080d01c400502040d2550240f504000030031040c0f00f00c04c401c0d0f00700303080b0300c07079032a280e0a01400c0310041e02d445503404502612480b0964040c2038100203080102070141c0103410081d4800c2c0400d50742c607580ca600007051010482c41840102c500 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 555021115 1250 555019865 555019873
    0x30e0a20060c0706020313080f0a0308181006030c1a070b1b0c06010509010b1614010905120304021c110904170a0918090c0b07050a080304080a0e090108 67
    0x9044415005900340903100e9214800780302840092008000e00c0c3c01030503084d0010b540e91200070324071417000030707907640000b185511044007403001b0300700480c05104450b4182000840307600c030301400462401c8081d032132110301d1258243d098084501c0e0f400200072a0300440884003240e85500d040280f000c403858010b540c010b002c0103c0c0000401850020303074000f03d495240d590110f410099401103520110316850765030b20020062020345094013000e80103264a1061070315200390403c03d800c02c0003041a001d00302941904030100d5041c0c0c00e400110398550b00c00b00ba1401007c4103402407016401c10b40d0180d0190446d255128080281000f04001071f1360000101d0740860000c0c000c00044c01d000034022507000c550a0341d041741400c000005012000185d484000059040010710303c00411103100340c0c0d2101c2e061040010216030401e0f2043c00341c1d004420015520b0604d810024030307024100a004142d21000030400007844201000341440501039640d0203074810484040150240080c042d810090304 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 555022365 1250 555021115 555021143
    0x80a240b01090303120b041103060a0501030b01020d080411090408040e07022116150c02150c03180c1003050609072a020a0909050105010e1006090b090301020d0f0c030e0a 75
    0x40240d170591480900c000700850840c040b0350200c0e040d9114100742c010b0906001c418401145080003800c00030b400c00f80f904004018801000039600d00d81218143d00303224000010405010551040c000c5408016000c44100d003014680650382c0c2e03116220b0b0045110a12021519152010500181d98034244251102c219511100d28145030f011381c91501c090803400d0000c0001546440070341c207a001c0314110004801c172032048080c0c00c0c1b88003c0c409103c004604810052010048000c2e40d80226500503c80500c280000103640781181e0403c40f180d2040d80321401e4411140e16070051481403905841452864075a00c5c801c1e00c4656551315030f002c481c00c9800c200500002c442e050301c4081400100b4000300d40390f07140c80d08411541100010380741a51100010320580c00400d40003600050b0700c020110f0710314a4600010152905800340c0690170a00140450041d43e09405441c40f14076030080410141c4000255407000b0301403290498003090074041111007900c0085082d490883e00107003d06403000c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 555023615 1250 555022365 555022367
    0x150906141305151201020c1b03010b06091c020a0806040606051206060916020109020604080304060f170a1a100c050f12040b07062702130203060d1b080a240b01090303 73
    0x200c4440b541d411250b41c2409005030311401000008000e98440020300040c41623501454291091005c005000e98020405800151521031890030550b00103400801e11812500c000380212106521004292007503005000a001044d4452800c4844c1100c150100c445100401901d030481100c0541d4410481c000181c80f1000421126600e49101d100000b42480da65000816a4010b5000f002c240d5201080a203e05038210b00018034450306030410b407940145806440180000050480d1800c03230b2181c1540e0000b103a4009103400e01c4c0343c02081c11768545680c40d001048181c0b40b64090355248595008912019404594248140110040c441c54070741007900354a5194001d00741140c400741e480e181045920741d0300158075920380c0c0340011441490101d00400c06071690101c20000a60b1042041c4020395a8982e0300f0348140f40d0040420110070401c20b22441140500e500007084e83c0214050081080211102282e074042d40d880d2051000c80100078a0086030034040300da901086540c2000d1000c2 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 555024865 1250 555023615 555023629
    0x2115070e0108090c060403032007050604030311010f05130c14010504060c020a15050315040c052a01020406050a020105100302012a05030d0c02010b0f0306010915090614130515 77
    0x302c3d6403c4115512400100081030590b80194410b5001414100d040300c01170054a46c1340d107900c03801c00010001242001e00050440c45184401014441c41c801001301c09a420f4200b1540c0c80da40910810a5180014140001035004c1c142143d5122700100c0210b005c1840121111078900d040e075482d410a41040c40658181038862426a030001c051000050b80010980503110401801e584480d1030f0304255080c0a1b0180c51003034000c0c03107607083c00d01d0b4880030b0390b01800f5596180001d00c40201c507214920030b0b800c07139400c400c08880007039400001d002c82c42c103410400801c2203144c80d0f4003c12150340c030030321800704400c40c80c00000d0018805d603083d92800343c03444c0f00303510941e8664241811f84010380d569035840e41c1d0201c60b82d107031555111b6076240c020b2502885407900703400040d03070851050f4220700f0020780c070f806050181c0070b9132a6684001d20a20351410401e03030082e19615200300b003025251040714400346c0c000b0003410312480f8541f2091040f5040c901030342e0f00034814200765000800c8001c00300450 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 555026115 1250 555024865 555024871
    0x41502120f0d0e060a0b150309060a0c030b030106090e1b0609010c15020d0605120d0f110a0b090105100b1305100e03151f1818022115070e0108 63
    0x14041d15222081401078040c880300c5c2c080c0c2140321000444c491700c41c0a00c107020402864900740c2110600801040b40c1011400a034040c0d810000050801071002e030503001042080900c580540c41d100f0041000720251b4015230341301c100013040701c0351804501e80b1030842d09201822903401110500c845035165000d403a545540a210350903000c9000c42a0b880070b8100d801940c2080550341d22081c04000900b4465402c494883c140d0019008a440c41c04028054030340d9480054108041c080702c041c3c10340300034064060600e9000d0a0751440d820f00c00629406801c00b13907250002003a400360006200101081203448010146c04000c00c0c0601e40b03000c0001a01c169210078003841400d0140c808503580c03d010400c403035110400404c10a0401e15a1407203919500784030130450101c404403d00220300c03144100c5981c1304101e000450201807412020f807420078070440080d0070284040700c0305020840340703941500c040840c400b22241c1c603981c00070340003000800790f0303503500482d6042c11100104d5210b0480a54 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 555027365 1250 555026115 555026137
    0x302040908070b09010606030f09120804141b0324070311040911120903130308070c0e090d0f090501080105010e0f090c0c160f061d0303040b041502120f 67
    0x3081c002d09032200c89031984115905103259540303110903c01d80e03416106a444103000c0b181c003000f82078100c0d624802440f600c0304005060120010005040088001280c1000c1c9120025251904a15000c4071101d1803101c902500c2401868100203802d03008103040e03021442000003124035500c907900140c00800140c001101d80b0b09040001154243e981d000f908901d0000c201c89603500c60b800402e9070806000640004020307002042000181c804010650082c0d0790000b459070741c1c0380107503d000e9a0303400c015808590800340300401c12002e0031010400c000600c21640703480949070313403d12040725481954040d080c0031605850060080b9441003070b10b03099098018000110005c0040d0010307103401012944420201c00024001c114000103112840d1440303044c8403000d2101741031a04000b614400c90090408015400a03807009904564010b5004410003400b5a9580c98850f04240c0550b0300900030072060030001403421086900c0042e014064a418140d068280039158040c0452540a071803c12 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 555028615 1250 555027365 555027367
    0x303012d1710060510021225110108150f1314091c03090c090e01200318010b18090a0f15061401020d030c02070306060902031b0a1e030e100e0c030c06040302040908 72
    0x810f2341024000070404074003609403990b4203461600010080440140300c2e00300b0100c640498030003a103d02c1c5400f0140c0c0001c48510701d140d01000501c90040c11203441d044c207038035420700601805180c0454061800100441d242c400114000383c150250341d4154002410031040d2501007104051941c00050b130402088008640d0014a400540c40c801548501d403c40903400414840300e40d02440e80455914210700c001e00c2242d40c5080054000400c081c4185802c1548200085044509021007812564082d504460a40d030a08044985024485920705007524111000c00e8690780c103401c00a05400584c010040e83c1201c08040340609415000c90b030030752140310300120000b5400c1c040e0401511f00d01d100181c403032400c65542407411081405148140e402044000c210710b51103903041c0c3d03640015403062461401410380c00c070000c01d20392030b500800340030f1485040c070801c80603003000316049140c20031640075030800b60800d5115141c1e580e25640c004402c010410042c140b9403c0801c03981c0c003449503a = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 555029865 1250 555028615 555028657
    0x804030501050a0c0e0406050d200604030f02040c0302031312020106081005040c0603061a030606041206090605090706020703030815090403050703030e0303012d17100605100212 78
    0x50300b510000e941e62000d65841e11900013000e40c0c4268026649a82201c0a04c0701c0f62800d00400c044801100f4054107402050350080b4070184482100c6181000c0588241d55030b07552070a047d060f41818000803446242410b00e5022050310078001d82e03005140e400c2003e01c1e46160f50740c404100b10f00c8012244299500d805001490940038001120300a0440801103100c0c54203140c100e004122942001e4141031410b1000c0c85041e07146480320321010340c0500c0c550b0350ba031950400101203000745ea21100200810080440401905800c1110001c0c4544014402030712600c000c0c0d603c801072030040000503031052074104046882400f019821012219154404035020004110088811030f400c3d8007203900001c40804040c0d1512034980a8224807000d036096504084046d800f0100d910b0303503841c900c2400a00901c0c515452071030000140518946543c01402e203020b20f60b220040d5820503800285011340018032401d1014003400180810f0340a40b0018942c1344a03029640c1025400201c281e11032806 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 555031115 1250 555029865 555029873
    0x1030f05090d0801050312030115092102010e0a0e1303030b100e0a0e060607063c06080106030f0f051501081b0d0c05011b0f06020408060f0906060d080403 68
    0x65500500c0000080c0455220002c40a84524810703032040d802903201042510b01c054040d410741c0d05540e000d0109694201c8501d008403440f130403641040741d811600101450450369070454400e4418800c0c0c8821000c030203010204000604988241c0925800d1103001404c16440300d40c00c2050184242000514003640101081c0038084442c2c0541c003050022010a48915100c0c042c04001c08030210401c1043c07a200300440c40034091140000c02c056107070440a0b502004001d0755035070100940b0300d0b161103406003503d0000c3c880352140020140b1440d203100412100018020728043c2d85e003000f9100414039499a0709046410400800c2d103540c002c1e031040c50000002841111300815144008014a030340714458034020061130940301d88526882c1108000040003c85031408a0348242040e1288103e21201c11621045000c40100101c003d40d00d41020040700760b01800a449000003120801e6561201042e150003060b11034155a41c0023000150f001d103400d54010304858440c0320001d0810755079a80e = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 555032365 1250 555031115 555031121
    0xb06060d14040501051f051c150f1d060f06030109020d14011512060c050c0a080c0c040b06031b040512012003060d080d0207050d050a020d030b090c0901030f 69
    0x1e900700c5121040180418000240112a001660840111800b1214644110248060f07100340d40c0190084804121900d41080800030300d03070703000014030701c5c42c4564203502030080c000b109071810a00c0ca0120304964139000301030a1b5580202c2200100650b48a101c150700304550000e045a6066480d4044100140c8620211407069441128807079454898140030702c0c2501c0d0701421000c04002040800c10424030040c403141401d6401000c002185031086204891621a21034034002c14400c443c2c41d02c2c01c12140d1002850384070f80e044117031080c0c0f50030a020403080d103280c000d1180d842141440460980300d2555012004800c6003001c0d0351601d590388010a00e6003541c80c044040995440001d481802c2c068890305940421a02445145d40b4000001814510152741c0140c04e0f11004500e0501e0746086a04440039281c1150132140400d84031440204035130f00804403000180518043c26442c2c60090048071500c0100914240701561841c01c44041038000108981c10903482d50740103560342d04144 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 555033615 1250 555032365 555032381
    0x602100f0207140d1106100501110c030f0f060907061e030209091305010e0111030a0b0a0302060d090507060804170d0b131a0303090a0e04030c0b0a02030a0f0c08040b06060d 76
    0x140505003e4140c49005080c4100d084864105c0da0000d108018000700300d6082003081e50f03803d007020400300c044010118038080500c01003070b030075108407104204035010000c0c548001d04400411280c0d595502ca85443c1c0300c405034407528010400500f06000d11548064220301280c07124070b0014100a4118001086d009056a003c41c0c42003200c2c5042c1c0030b200d4280580e5a04511680090085480384c041d550384a1100a00f078022085d500d0401202d1a0f40e4800708034000c2d034004044035102d4000d03244040c0205041807048829104e04040040d01c9401841c10314480c640142d48410f05134000c1c0000c140d00c0e8451400711149554803881b4441903580e45c550441c07440d12106000680720101c0c60780f100c0191204441034481e61060245628070f64130b55200c0d80035200c041103548029100d91030203584048444c1802020540014104000b9501d1075028520540703041d0014004400800309003411a828001e03041c00003404000050081201e0b407030303115080a80580aa4500980c010f20b1800316070150b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 555034865 1250 555033615 555033653
    0x3050c09061f230304020a03020f0f0d0602030f07080f01030f11030d020a0302070f0506030a110f07080703030510030209040303200403150b010801120f0f080d0e10060602100f0207 79
    0x3018024000607214080d074241d00e445503c2e42d895802c05800040030f600b041d11000744610681440c00481c0d49603c1c050b0406600007034609604000e0501e848000b80d0011240000e40451300d00000300410700c0386105600403a0317001c0a0046036402d41d02d400b580b4002c3c0c69003d44040c1a021400d20858404000c0e126044017298040c0c49401401d18000f403d00c13469074003203a2802c1c4416420310080c1d942c80101c9401039403070070000403c864012495840d600418030801c10b0103001160b0102803102c803c2c010840b69100c0d40c3c00f00200e544520741c1c034401501e503002c003a4111010304000b40020b03000307500c40c1c034440032107000203400c211407000131550f1944203400c11549220064102c0c08000c0040c02903401000003400c1242927581032162a43c220807403600e0180c2554968050344003401442111001541d42001501c0d07074445640c00c810016055030070081100b8070803150100d078141247c1c41b416040e03031155806040384107a0680c3d41b0001d041400001640c550303080000d1400030f512a02103c84030106 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 555035971 1106 555034865 555034877
    0xf1b070c0305030403080304050706091a2a030403060b0306090c130b0607200409050c012303012d0302010e0103050408070b041103010b060403050c09061f 68
    0x31644040c2141c040003802000340110000150b00c5a070003031044035a90b654406007103480f1115403003106d2001d001001d41000e4811a42c006154080000030003007a0141030020079000480750010b0803e082c0d10021b000c00400046010b00400d007803003200504918501422101e860b060036103059841110075218042c3c0500f865800002d052002401c0c85840f01201e1824400c131803846400ba50305202c40310110038140c5054090000d80741d0307002000c0e001800c0c881f00155040c180e10040396a0301140e0381c404240040000c00a14020880f50101d803881000d00c54031800b0007420341c0c01603118121041030500245c0d0308001803102c6001c2c2864001440e40c1ca43c00c100b0780d00d004104004048a240c0030511060000e044104d0704800000c9008002e684014400c11405208900c030003000303900b00162000091030098032b4258040c0c8082c08084520350f0f00391102c0703110540e240301c40d008902 = true := by decide +kernel

theorem cover : BRFrame.Cov 554856115 555035971 := by
  have h0 := BRFrame.cov_init 554856115
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554856115 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 554856115 ≤ n) (h2 : n < 555035971) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
