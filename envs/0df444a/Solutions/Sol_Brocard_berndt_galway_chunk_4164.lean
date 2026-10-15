-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4164
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:45:33.067354+00:00
-- url     : https://prove2.me/submissions/a4847b0d-b728-4826-b94a-cf8224eb72aa

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 748741007 ≤ n < 748920863 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 748742257 1250 748741007 748741033
    0x61b0f080304170d020d0e0a0c051210020f18060f120406020d0504050d0206090f0c09040507050a0314060a27050c0d381803250b07050906160203 64
    0x11340d009400400e00b140e00410501d10f2060301e032080501c0c1c040e00500138081406541e96080000c8058421588690702c240ca820440401c1032003402244025810f04650300e601c00b0703441d11406c0d00311060200e40d40013086144202410120100c8843d41c58000c03a450807d6030010740c8241500c8000c0c402c40d4925003c0c8a80520082c00340540c5003d1882940600300c0082d080d40002d1900d00c3c001c0420042e03502c500100070b45140045014040080281d03034a03c0c1a540b5800d00c0ca00e00704c0c0507444560031101c4644001f0038400f06003800e5081c440c00c0c200b50b035444d4a070745084006440d51018108072a90389100d100d8105a50414240c01c51445403054840402d80040000e4041c09140801d403001c00791078406e00214080c01c01c00b4031000030000d10b058642c600d141119020108014400da0403a1000c50b000d640080d01002518200d4003500c403000d44000c0440c00e030701507032881480304981e4840d280010501a074040c1c0c040d1860300ca0007074070341800c01900e002103265002c02540c017070741c05004004c00b4000c1d03 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 748743507 1250 748742257 748742303
    0x8031603090c0b12060a0506040e100e01030309091b05030a0f0b03010c090503100501030302030702090403140f07030f110c060a090512010b130203100501080c090d0c061b0f080304 79
    0x1001c03507880d407988a010840020307484044c0200210301c2a0302158060019688010960b801c2c0c40c502c440300101c42d0303604482d03286020b10f250001c15600403080300020130194000340781c50546248403828040d02d650040c1d0b2200340d003c10f8100001083c01030000460050f0580c0c44010040f111400201d5419594800300e03007104d8030070700c504000ac0d01c041c10038010740c201001602816885c1d85070404c030562458030025128011250028855900680030805051140440407142d01819801d641c0c0d504400420703d07103651020b141200494406003e60040c0c070f000d1458506901e0b000c00c040d120b1044402c003004100d5000507055001d00c89034810214440c2c648880042000800e0000090300300700c2c0004014a0003141c1180c49001801082003006101c43e2580c00c50440f8402e0a0662460b00da5148589260040c0784105800800c42c907141002d00c010b00014608817a4952241a07a03043c40107802e5080c0c00e403120020b8810f440918038580090301c0c40c4011944a4003901080781c00c0c0c4644004010 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 748744757 1250 748743507 748743509
    0x60c200d080a0f0c270b3705030a0e06060d0312021309090c0f03081801030b040e06040b09070b22080709050405010b010503090c040b061c0e060c040308031603090c 72
    0xc2d40c00b0300c001782c844403141616040a03a030210400c201600c2d04081c80014860f00e003007180e1003600c62a0354190304014041e410800000c0c641000d000303071982c01d4000e206400441e440c1c052981000c1d21a580003002041d8a40146405000c0041f5800e40b51026030b84852001d6156202990030042200421010f241c0c05000c0c145820380403c2803c3d55040030907640040c0e402c244026920082c0030800925100d0031644001c0201000c0500c40d021180142c004190380c004480d00542071040c00c03214018003190703941c40b462003155008499280c650080c2e944040c640030b1800c2c220800c1015140499018454015039100380b028106026220170030303a428480329074055142076803940c05101c1080000c0c0949021104280390107800c40c03a082080c81c1ea24000468000e0145581c0c1707070388003440e41307842040ba00111146246155516244e03c1244000c0040e4480401a4002c000205640c1c0c0c80010407282141d410850036810341c1c03078541151345101c14401c01c1c501895514104200060f1000d01400 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 748746007 1250 748744757 748744781
    0x904090503190804020406090203060303030a110405181f0b0a2f0f0105090a0213091a09030c010b06033c160807090e01060302090d020a03060c200d080a0f 68
    0x8102d404c0c40d10520060b5106a004603280c0c07401401081000c3d2400800d80741c1c011803600c004a450a031182d000c5040d4801c0760400d42d00000031460f40c00030782c0001e040d01c0340114085405214001038002c1e40b103d82141038002d070f2910b0701c02002540c81851080500d1700820f030030182c20040c00100f01030f500e01d0085d00f003102c2c0d80701508844440e00c40e200d82849140e50040061016145050781d40e07000403940400d1441c45412155110038103810712100c07400d01034204250245401d03941c100040300980e01d0b08003080c0c0358919070030400800c8460410030300380c0e8001d208548400303a0500342024070911203040d16124030003110360600c04800c103007442e5400d00c5c052025408403244c035074080403005020074030040c4005e089c004410010408000000400f03811500701d49001612003e0340c200090b20191000c401951060904c800401400301541c401000942c1d15107a84201c40d1004074224140c01c4540d40c105600d030020360a8031105801040030681c080d2021900040c0c20780a045180101c0709180800313 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 748747257 1250 748746007 748746017
    0x12080106050d150e071e03061206020a12090507080c0d2003030d240b09150c030c03071b0e090a0320010203040f120c150b0609060a03020715060b090409050319 70
    0x18400b82c500030030546607005040c9003e0108d42d08081c101081803030904801040681d0000b03481506a100300101c00c2c2c071141400d402e202c1504582003440e5180024041d40c1040d00550840342843c0c941002c142891961010b002c17a00d200741e580c09a410020030044050f01400300700001c1c1001003003486800422425900d140c200c845240e45030041195164000c210030b154100401e81895441c400808002c10703d080000c0d90343c41c0c81c0c0d1080707400c601038a81116103c2c41b010402c0402c0084250020400c0e00041c000c03209480d41d070b041c091071040b60584451200345c11891813400802e1180684400082c081001c0c00c00154808101c1422640203c0b01078075030f000d4280c0c40703404001507046000800100e501d480005444d06484034404000c02113800607015a445140d41c400344c43d5802039600a01c00203214989814088030050044e41c0600b00407035140c00e08003040c0242400c0c07032264005698a4280c0d403800e0104070f00030b11000f021054029500c510041c0001c038410042140c035028454266070781c0f = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 748748507 1250 748747257 748747277
    0x30d0c05010f093203130e0603060c07060917031303090e10050d020312210901060617250908100e061b040315050412080106050d150e07 60
    0x8110300311003070b01407212401410852a02d01040000108107401c100c1880a4801414240c5203000384003144400c203c414000851501004122070b822001240c541d0b0120201e0f65940c0300400d80c450804a60000080000780700480c045201703548549009071240000c2c4032071a007034180d1610300350400c0701c0b0148804144240401010351111134480141801c0c0c5094000f41811452625110040c3c00307818001c2d1015000c05066581c2000b95042640000001e959a103034003100010900e42e140095112039081b900108400d19014414402213413031590300c41c1c0c046040501103920f80d81d8058688044401c0614001002240441c110021440d071034036444c011078940b285060030020340c030700d140607414908401d00d014841c001c0780055120260031141c40c075803402543c10801034003c07a00054544441121004c00144455200c68055401010407102c1c2070800c100458982009001d0306e0001041407181d0323101492503070468110b11141d001413120729500e41c090074000c204101c80300740004280d914 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 748749757 1250 748748507 748748513
    0x240409080415080c16050106030f0b3c0718090209100302030c071211010c0c0c050306070e01030b060715060e0c04030b010501080a09020d050c0108010b0418021602030d0c 75
    0x45902610030807424903441502e801c1003104d20501480b0340701c204561000d0400d030b00b005029405000915071200f4610303140d5500341040826100c0c11103515141039000303800c402c2e07460385107200c03108004012604000b01011550800e00030320b401400600900158036894a01c103840c1c1034902c00982409800141c44101001c1003082518189103204207141c410024410303d40c02c40702c211014030340c000c081601100310325407048545001d44605c82241d03500c1c0030550b01840390b02582d912691400380100b80c200b1900c5e1420541c032004150b4940d00070a04d000f48580303039540640c2250442540082c020760505180d07450300e1a120262203d00b40104c1d540303000500c410381074101c2c0700c2e402c0032040340d00f1803c00d810f42e030b1a0390112074103015107414440300308005030f040c101c0740e0060a0315640c05414031107281018500183da6034402040350380885c0412001080c0380c0d050740c0c00d0f102104e80051404458100c0407070300300025484058142e01c20310300c411b0f8000c050b0b201000140100b030300a51700d2a00640c0d00781 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 748751007 1250 748749757 748749779
    0xa1a090f09072102090a0302060306150f070203060105120c04050601021603030504080d0905090403030b0f130504021008061c050a08030906071115012303010e010902090f0c032404090804 82
    0x940b41c200f0900c18041a2180d443e0841d2240969506a0785560799844a0300020080042c8401200911000003203420b085100c403005491528800d03000c450860740c95030208914441c1d071440c04400c50b072205000e1f0754a4540350f00029006801030041d2800340f400d105062002450a410550100e1000201040199010400304c956002246000e0030300318108400034800e0107000e00090201511185400d515a441c50b002007051203005202e0b00d5060246203a20024060407201070b4411247c034044200c1140c002c010302e91003801c0040c02940d0424030140b640c20031244064050b212072080071030030030029103208000c5001303040340c50041400c1c0c602440c00a000c4905c440c41496550011100c0d5210400c3d80a1120b05488110f103149403e2442c05101c00c4802a540103115455800d190310902601030650080e10614025901000d03640d03540140c2010107102a148000480410000103222a900a4946000d45a000e0004280840350720006041e02c4148000392440b400000e410041302c0c0c2c0070 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 748752257 1250 748751007 748751057
    0x901270e030f0a0e18071202090a06030b04180809011b06060306060312020a0309050108150d030905120a05070b0702030a0b04081201211203061d0103110a1a090f0907 73
    0x40701c4803021480784204042485c00c001c2c0c2080c0a001e4410041109a20b2a030107076194503001506c0020040c0c0d80301001005800400c040e030780224681103001c0070a5080c5210b0b0207060b03420109952600b00e10b0801180c82520201c00b014500c40500010000200c10b8052030008600490001c1145800c43c104603009440c1d5071303101000e541c0450b0b04180001c2c0c000e2014000c43d1800d0038140102c1d940c108081039580b05480e4019440b550710b00a913010145c00c80030043c1990415521401c40e003c040c88003035950340f0b40d0807024016902c901c1c402c020745503e20b00204507052001d4142c80c8101c07010341d10b050321904296401c4072155000300d040000038004e600080d004140040d001d1101e804920011032010920325405840760b51a115407902d141c3c001d0700028001c203045043e950303605107910280d5024a03420f0000710b03140884034036030001601d403540c07403c401c0d181c10003109000340503202c88451a40d4403059043d0381110501c05c19001568400410358410340c5242c5400c03180c0c8604488102c005109 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 748753507 1250 748752257 748752259
    0x302010503072f0633010c0203012c030403030509131b0203041806140f19090b10090f2d0602030304030908070602030d051803070515060901270e030f0a0e 68
    0x601000742650014030038140c2040c3c0f005c000007015003200e10300101c0e200000920040e4156080800346a00303450110480d40403030264440f151615030406c105140c0341e101e288405000210103010401d0f462900040031041d03c21401d90014844900c2d0035215104154080c5240141c5c0000c80c003008100103031030107150404070001c0c08100303160800214041000b240c4e030b02c280c000c801180f40404503171039054140c5500c060b10280301b01c07240d0392000c44901510554034494044c00c4441c1140cac0b5401d005441ea10191034214859030407240c2481d5100401c0c003c0c0c40701c1c0a0070400071070020210800140409009403070513070301565580c54a814050405001603001100c17650180c0c0082240315404000c2c1d4000f42e408043c00f0419031103441c60318000442004544c0e05600000800704200704000900b040c0c01d06192000c010281d42d0541013010050092007620140010300703e581c4000325030003040c40d039074640c590030000304440e000794818038680101e81c400710310300e50004c3c0362803071a50004103841b84040 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 748754757 1250 748753507 748753531
    0x809240a0c030204030c2d0906051305010e1b0d02040603020307031802100e0a080f030c1e060106030c03151715040503090d031e0207090e01150302010503072f06 71
    0x701d15580c8000c101928411103d4842d03510188086040c007110110120341ca044102c85107031501c0c8d0040c007000780394034441d5601c10401228441d004070078500545040318a43c0b4030040e140d6582c004048003400c5d100b00c005490714030405c01803110410f188090000380c0403640c1c0041c2c41e4507004401908a4250780e001078112a0000e2081f03005903100102d0250700b02c503d26058450814000c0030980201d441d0700081640c2c040c10700301e0410b456000011386500c1d5806811149a180080f41c03459800c80f0401c8030700031720b0f00003030010b028080c000d800180c050011858005018046142035103002c440c40e8100e440c0c100c03564044803c40920070400101000440031500d0510305060f0b6400c0c1d664480c02e09894061822821441c00b0f0502400c0e24001402c1211002c20fa409030900000752030384400e0240b081024504200044501030500c6801b5204058400000005046800565036030704024030030020401c2508008140c4805542103044030040440c42500c901c3c190701c05039083c000000c0103654210 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 748756007 1250 748754757 748754759
    0x504060f0c17041104061208180a0807033206182a030a0c092c10090c08030a1107140a12021302030c071a06010f0809240a0c030204 58
    0x403a0041d83c0d00309071300c20504054a414100424007600c0164008540054074480c40b90074010607600400c00c014048140c03a003a01d880ca42040302208050094501a6002c168244000740b0903903000e241e550090200c4010310544070004040010303ca1019000d150080000e10200800c015000d54204080f00003818150100ea000e00b480c1c0c40d0846280f00f031740c0400001d0040c00d501c0c14030042c409540c00501e41002103440e0f20061024005d164019100002c0e0056000100c442e0554100c40c600300280240201c1c0010010101c040c1c18a0182503038203034440030000941450030070041105c058a500d4015a140030710000d203007000380c0e9a10072866408066640e03003040d900d20218406494150042078030710081c900210b81c2c004502d17001e41c0c82c80c920000a0000074518100503150303403031243e40040c420317181da0341401c442c003041176880a020170704c0300b05040201c3d03000300d040c96440010700085818040e08d1241b12035a0501500038610707451034800510031010094005d1b5283d900c240d0070250f02c1d117 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 748757257 1250 748756007 748756037
    0x18020a2d0b12041401230109020a0c021e040507020c1509061c020d020a080f18190620030708090c060702100e040e16060c11040506130504060f0c 64
    0x1a01c00c507000e480c14002d0b224001810410741e6004049003800150080145114092110b041003180d00c042e204501d510307200004001c541802110303014142541c1c0ea00d0750915513400c1c008071140c90000c02e000d0b041d121070280c144e5140d0380f1030148645429030040c03a0800d04001441001000e4000400141504101c2040c0340e894440c01c03078000000c5d603940d201e1450b0503040300100034000d0700f0b9440140350000a10528007070340900c1044c010b10072200c0b006415250440c00d646543c02d000301d83e00c4950804444605000f000524012420340070b00ca000c00c901c40740d0f03009605d1180c1808050940d4050100a00c040701f80c0c0700c10000d900c00794000040c51022b507810001952400762120082c4034000021100302c0f034030b02c1900b8000d89108054000e2000c1d60080d42c0c00d40e1500410000b05a812000c0400020218858001f5261a60b00039030020304400350f18040c44003518000340001c0d048401000d860054200c00e2051510450103200300103407204e1740050368400d41703028800c6a001c00142e5142d500003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 748758507 1250 748757257 748757279
    0x60e0a23071a1e04181407080a0b0a080f0d080619090f020423030f0102070206031f0e0405070f060e010203030a1d1e0106090e060a18020a2d 62
    0xa00d10114800646989183c5950034840810340e0300c0152043c4080340006410242c02c05c02c0700d0030060f020007840490140c0d000664161000c6070710400140d00c0c04041000781e441c95100400002c07010345840706181d29001c05030701d00081ca21040c00765a104001c40540181d00c4610260420404c44405600d0350001c1e040e0b4980c0100b9011b00c46205550b425104074005082c0c1c12100100740f07581e55035403e1132410640c8071220700ca04100d503010380124103900b81c0002061088454550b40104483e05640300e180c07840d004000c40903040c0b100040e05100c0400c100034800d000364491482a801080247e080103448d00303031500c80781c0c001e0f07007400030081140800c0d81c0c020065950041c1c0000e000074041c9500044459a480c207444048060b014071f2540b000c40c002c12001003200300d80344500911859603945100c10450b0314155404480d80c1052001c41d094190300d4000003845a18034080691440c52600000e800490300e03407190501d0107d10800a01d00c4000382d000c4030a1004030844000307028901510010 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 748759757 1250 748758507 748758539
    0x11030a02030304270c0804031106090a1b0503070b0c010614130c2706030e03130b03090a060219081302031903140f0915180607060e0a2307 61
    0x150000010031075144c110300c40c0070400b0000a4100180520070399000e0250945500740c9080d000207958140c04055404002070341c900818002c0000c000516480d140c99000000d1b00380d1101c080011042d0000c0e181e60100070604c054801412541e80d5054680d28560840300254043c0c6c5401181160040040d543c40085100358103001c80081500d0080460440351140c40082c48038840b88415440000710020170000c409450450f2010003501051003481c0e50f80380160165980c10082c01c5c0401d000801e02c4030069a004540d480890340c02c508030760b0320a41aa00000440302d40360142c0d800c1e0440b000d60200300309400090350b5100d81001826031300400d4030b528040102d00f00c26840c4130003001c2054403908540004000a0801c141c6445000604204a50090b0001481061048414a012501d0004030f52081e2584070503441400c2d040c2c0c0902c4590b07000344e801a200b00703a640c01421b00c0030405009086c1034070311482403440800b10004200c000b40c10100d00c0f04107070ba0b003c1d0505011038105810740c07007 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 748761007 1250 748759757 748759769
    0x2c0402030726061f06020a050604240603081c02130e280c020c0105130905070909021602270a0f02090d0c03020a0b251104060602070311030a02030304 66
    0x202c0b0482084450749101014031050340c406105080400c03200c0440c500b00c411345518001800c240c010780d2124226036600b841200a0181d402c114081000500c07650707010302483c2841d845543d803145201c0702602c1200d1140d40709031245400060b03d10b4040601c0410300d00002e11214085003800121400b9411400c01409032080f10791a0502103003090210b01e000394544401c0c44030411008190103e000b020f4030a401c0c54901511840188600a40c02041681c6d014002961010381052170000d4440281c1005042042071044000004c29210b0940c001400b5404400c0769800c2180894410701c0100d480600e5041c5040364440301800c1404201028a5000f2000c0c6102080640710704400f90000e20403c1140c80e80702983c0000202080981d440c0c02d4222402250302c0c042e005ea5840d03003001c0a101c0c4242c1940b04100d0007003030900701981007640d0140b4600548441d1900144900440c00315042500441c0140e8801a801c02c01c00108141c201c035200b50a5020308035650707555011036942d0066000300 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 748762257 1250 748761007 748761029
    0x60503130f05120414090c0702060d15121a0c0a020304032a030c1502030306010818070e180c040c020d080a202809060c08070501062c04020307 63
    0x4050020420040fa00f4110075003103d50b0b40d55a81a41469081d00118490f00809450000500400300041542c9080341c010703200519240c8034094940040180410002400320b030444003040280640c03140d001140e1160401010b8064241a01002c1103401010043d4940c0100418910164080180c9046980c86140482c120101018030009035411350490141350800141c00801e02200110520856441c0b40b490340e042c00d150302d4101c0c0c4074802111261b0114140c0c4010400d56410307404c09800c1c01340703200c0c1954001911104100864001500c500760703d5580c0e8840365140c0c200c14801100f0a20040301d00700034103125050042d4032004620150801c3c4005900042e00740e01240d0050380681407426441d54002c0b01e5040b03840810b4005055081500040343c104038079a41c04603e500380c15601c07d441c2c85102514020040740c00700e00b484011100580c00f48818400210240203202c040c040b00204800c1603a80f9000a4012860080a845142045106000140c1c401203010429078901e0001 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 748763507 1250 748762257 748762283
    0x50c0f011802040b09010305100c17160f09030f0b0402060d1506030b060c070b030711010e01020d060b1e03091e0c030c01020a0c05130209060d06061103180402030711060f09010606050313 82
    0xbc0d191101200a0144007001c00401c001520f4038494010f44000c50399102e001102d692084200e07901c14282c040100445041400000881c00c0800ca203584284000c0541e45091000e140034001e6a0080c410ba002d0041b1021080c00125014061120b00d00010b0300c20506001d040071685544211511681800d83da0000200c0c18140c0b0410007540d010540d50000d100001d59090400e0003940a01c002140b06894041d003c17590120100c12078010400c1d0521019101d00c011610a100c0c4d8801b070084440c80c4145c8000e48900060a8a10485200410003038680000204e013418105800c4005240c11904200c8a480c0010070340300e03d15054038000e84118030303a941441c0c81d1900030722500340392641c4a80f02064011509103960071400503104c155603500c403802e0b44100496664040c01c1402c103030b40401d840d802521818280e018560200c040e251407103961150364500360a01105440c0000901c02c80410008045800d010340340042c0601d1501514525040881c00340300c99998070000c0000c149258 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 748764757 1250 748763507 748763531
    0x2010e0c040b1507200607050a0b0a0b15030609090f070312020a0804091a030f0c0613030b0108030403060e162715030204110306060a050c0f011802040b0901030510 72
    0x740030340c03c4003c0d124215580b1422030805180c070315002c501146101e004100c4a00c92428000156071442d9484030051240900c16910308010202c010040d40d5100e5807046568056a108000090200d111000da240d8904141d070522601d03440c001c1400380f9552004440001da190002109001c80740c0001c907800b41d010052500700d0401d094410090100e210100d03012030394034081d0b408040c4074001044210781d10b000141c01d040c0c903100340700744000554120340f034038444504021004201c112644001d1000b400d03160f544840b0840c5081c3c02910903984045020b108105441c4600300c044002d0000404d25080c0d403c000d00b80200ba10f002d00480c113103142800b13124202c3c00284200d904901d21800b03010120301c1c8600d9130800341680c84281d200d00c2c01c104030140046415004c0b0b9000d0f41c07020b85454174190341410107445540c0042c01ca0f289502c04d040b103d5290a0f020700c6035002d00703058000c1e0224000381c0c42c0100310640b00c0e0445098460032281c40104000b99001401c1c1c01070040003030001c140031400b04 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 748766007 1250 748764757 748764769
    0x3020a03022403040c151701090c0c0c0305030304031701030f080c0a05010e0607020c010903080307110a1509141518030405150301060f11060402310e0d02010e0c040b 73
    0x40d5011075a03010040c8130405c02d010200506441140004220303441c200c00d41180e940a400394241070300c1c98202c00501000b4029000001d00d901c01c2d0502c060200400c0d610050003a000c1d0b070080d00c80d90030201c140000c15502c4003641c92030502d00005084c4550454a407a0b560450203e00145609000941c000e2804c8043c032136030355401d030042c0081000c0d4014000094854204a400780018000d001e6030602c07640c0507a040b20162074001c036030303182107556400d0181c035244140b445003d01d0744912606140003e509080141c0f85680c0c0c000d001c01c01d040c0d01e1030060094412002c0c250f0711500194180341001c0e10050200380c2c4554104140700f002c11a0034451800d51055821207a04800700c0c100c5264409400c1c80150304a0700680e5684405007036003101240c020349881d0b10041e80303400580210340986401404210a0800c0341104488203180c0100d01c0d03464a12071840ea100b0720348030700f80d00d20181c009000205442c116400207100c9a94900c008544400c0304c4000648a030b40d4683c0c841901c0c0e10b4003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 748767257 1250 748766007 748766059
    0xd0e0601152102033c01050f120610080d0903020108040f031209030503011406030603210f1c0e0304061232160f050f0304050f060112050c090103020a0302 68
    0x303120704541d24100005090342d0141041c0008805001400c5074144145d80b8040c00c400f0003041e04100030090b400c0c00e0801811b2030300d8a6800c0c0c1e2101d240104110090020b110361805004a0142d00000c5803900f4a2a410070440003840d10a1081e03075501000542d03009400f50344c0c0203500a034003042e120074a02d0207481010050882c46002c5150000480030036401800950580c0c0e6522241000c1d101842e08102041c80100d44031078140d0011b0707007900d80410f419915469203c2941c01403a042101d28510302c0102c2d00300c400c1a12070700483c078100c0a814401d80c400d09103401c1080380614a07141c10320001030995100f041050007100c0d5120300706550003580303c82d0480070f180c804000c207802c004005540400c5ca80240c44504603080741c24101468940100f61803801c0220503114182410034000c4110200e1304010415a03c45c09500c00545074441c050200070f0180040b03c460210050550034034a107000345440c0c8103406035000388014405030b50750094a10072241d04a829294180ba5007a07556a80040c2c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 748768507 1250 748767257 748767317
    0x201060308160201090e04080901050a1214040b06150f070201030605040e0c01080906070e460b130506090a030605010f1404020315011b05070b0d0e060115 68
    0x2000c20a07000089400200b101518000da90f000c0e031264032181031044036401038600030405a0304005242180d40144090300d011300e0301d401e03c8041c1e90b028016aa096804281c10440a2081101008104001c1448150304050280c072a10118100c2c1c01122202d480750207560400610082101c81c01c6a209402c03200140102400520114060850b040d69488c00358542c41d0114100c200051030405000070310314402e030403c0d9510749034000030a080c801e00460304880c44e60411000d0581101d50450910000b0400414100040780d5103080358001c440c0048942200c0391024041007040400c1c3d08402c4480e068400403104c01ea52040d105001400580203548001c1c049070629000286496409270000100c2d1000809042c6005c081c800300b204911040701c004100700038142d9409415403103850306010594103581d403c01800b000f0b490f82440e01c00c1907444002c5107180040d058105040b28011000300709280c41c001c20095040903440c100c12002655014100b0002c40952201065020a00381c2e00e005 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 748769757 1250 748768507 748768523
    0x30f1b020414090105090d0215040303181203050c071a0c1b0307050c09060603071d03030711100f020604030305150901060f1d010c06110d110403291602010603 70
    0x48542c19481c11003004551082140d4030380030020740c1c11100030882d4a401811540600303010f003000741c090480300f44080c00540406680c2d080da20718100b0094400d00c1b0481c01840414500034400000a0655400404003501c035082400244002080300400c20001c0b1010300a0700b44690b100d0940c1415801442d803000c6903440303076599541e0741d07100c01703c0205041802384040d039012080040c01e211003403805540c0c0351b070010005c00010718140c3c403450b5040301d00002528405528003040340040d285070409103080d03030200303902400c44c0c015190458056020152504250031112051800a91254402407014090640701d4002610b41d41c070058000c0e01c00a401000c0d0700942d6120f050080c010034500b14140c02007034000601d0790660307850000f003030b000c0d0380142d4034035002200315529039010f4400d04030011442503003800725003442e220500440300440c404e090400d0b11103140d418580541d01031000100e41c60039180106103450b0008442c2c0d141e1003054440c202c29068195039003240100019440502241 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 748771007 1250 748769757 748769771
    0xa080a080103030e060a05090d030c080c030a0816020c060a03020c07060906022506030c0509030a0b16090506120621011a03030913110f07060b01090b0304030f1b0204 73
    0x903400c010028103980c02076450b0740049103000f052048a200e00c08080f0041041801241d01c10300d0215401860284a80b030488480c07141565000c500c4d40055910615581011820760321a541c0034141b02d0b481240c0340403810000c407a80001a4442004d01a1076008481c0081c41219482c065011079554000c18000c4883c000c0d960500180a044103018050050146903110441c0b0800d011100180a02e24103280390413502e840d10580081030752030030030010300900740300511711513909102545c03030f880c01074190300c05d00d02d40040c030064400f80a081c600203010002c10280200c1c0c40f00820f45d041182c3c16200c5a0041e220500025081d0a40d04010400840f80716510000d020064112140c1024a0f018000c40c041481042503242e0165110054201542c03510910303420314686c100066001148440074035242039040c8044e0164081c400a4074110b46500080b60f0b996031081c1c1c12030040c5289402241982400e6070000d14141d403040040c010040c032100420151806500d003003543da907000384200440 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 748772257 1250 748771007 748771027
    0x130807030605060d050606010503281a0a03050309090a0209031b040b040b06190509030304090e0d0e0117090123090d0503010b0304170403080406030209042d020304050a08 75
    0x1414180c00116121414000442c1103418240010050194040d014150035522500110f4150700000c01350f001e02c3c0a8044981343d072031072a00340b0341c17401401881c0205450700d52101e001006001421035034001c40d070303640007003011907008000c0d140394980403500006c0701d456021032a0701901034040c60580c5030098a41051010850112074070310340314161400d03c4400d401004100071a400310206c140c000700100442c2c50b041d2505440b200484c0c0341800c11078145648813000c645940c005810070030341960741d1020501e0000c070401500d00300047e503143c02030002d8200350009240c17040700300508001c1050540072800a150a4203c91fa0640d1000880140d44240050503071800c501654100230901030010107244070380c807540480341603841400c181071030b4bd1141d5a4078408003446504c5441003040070f01000c4001003141c0020030080c01195809a2525203920800084441c440b00100e90408004c030000c0300c8000080d10106050100c1c40b00580b00d50341c80c2810303818141e8800004001c400005040091 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 748773507 1250 748772257 748772263
    0x24050d110301091505060c0c0d060f0c120f060b0403150e190218070e1318030f031401050a061d060409021b030f04090c0512040302010c020d02071404020f1308 70
    0x7130030480040001d503d90359800d006070741c480c49041034541e40100540c0301e00c0b801d09840c16441340d4403550700001c01c24408880b80c030441d20f021071480005404110001c0c2444541d024252000400c0c01080001d186003034070843e0f282c466880010424600820300c858582015442140d5442030102916014000d020f941e050011001d4003c038400e030040e00c0203144200d4880c581c3c0e44136900d075455002070341d1007890404c92084400290002105e8035600c0300c5840d18600a0404d60300d502c00c2d160b450614103454006400c3e1040d060440c1c0d048094800104000d5940c0c1d64000b04076051401d0482c0f02c4103403503290903100300d000f000c100c1c1c00060000300042c44000c135a00806032000c0c0941c1030010300d50781807407250701c921902c1d100e50040c0c4410302090014205036407000032500034a042883c035010007080128070b020000c07541500540d5680c0350066804d0b8040c401708880f07004030310181900d0703814020011185608603025500030b550206522031208515000c5032804a8211080941c4540c0c503060195 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 748774757 1250 748773507 748773521
    0x20c0c0d030c1403032202240c0319120905060f0c0904050408120907030308041b030212060106091707260a0b3310050904020a030e0724050d11030109 66
    0xd40c410307680c961b030049524481d00e103028003075005040d01610300c005090019692aa0304801c455004100319140b181c6008000500e00c5180201ca4400182004680501340d40200e08807584030600300035403000003580c0414004e0b8055003000e1188940c0c0c6921721614003a0051624484d000392905e003d0100b8045910302030007010b29410000040b50742c0e82075500f038440c3d20700c1c071008011400e00404100040c0a80c00ca140f1011852176046201e60740d030f500011940794006200030f0940d0013590041c82443e6010301d5480c00780200000c006000d00072015070f150703582c0551240382d01c480b6003081910312780e90200a0700d204880798001203d906020704d0800c0d00000000b95800e450255802000b141c1c08030011003081100130021400301441c0000314140b140031190380110108001c402c0104802030f41c1c0314401b0b081030040d02c1e81c0000c0e01d25018880701d4034010300b54201c28108540d901400140da00c2198507601d4a035803a240040d11000850503440140040c2d2041035680240400041400c1905070302c841 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 748776007 1250 748774757 748774771
    0x13060e090c1603052101060809010606020705010c030513080a0308090d080402010c0609030e27060f090103140703060203280e1b010c02040c05070213020c0c0d030c140303 75
    0x404240c076031162811241c418941c1401400030015003003400300c0d0013100a411040070224a458400303542403a41038030154240c0240c404110042c0500929180c06d1192001038030342e600080c8480c4e8200b0300082c12075240c0c10700003010064002034042c000c80700c030074104000b4841c40c1c0480d08221050702c0c028110341001c603196825486488495241c1c0d17403107071440900807a010b03100c90000c106513403a034002a05081c4010f4090042d440b41c440415200e031765965498181141f44090221801103403607503906805840548034031030364580c074050303541c0f16000141160741c40a88191052150720109050508070781c80a405944040100408100081c04003d60b1108602c40010002e01790000002220044107144806a0146441800c440c0d64001e202944c200f0504002c8581c1c2241d50001c3d007a42c4c010305611000880209501045040040c0d1107542d408000c042542400003000440c2d58a0381041100d40c400c4403134450a07400e150180c0d1300ad12a451300000c1c190582a4050300c80b642d81d80c03041d0b0350380c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 748777257 1250 748776007 748776019
    0x7020405130506090d170a0e0d0201060f0e10170703050318040c020607021005220602070209060915091b0a023306090a15080d0315181113060e 63
    0x10400c0c107011448258191715030302d501c03c408240242032200075200a140c40316680e40d401c500c0c0044082003100441c901120303400441e10904081e60300b03031001c20039401005207081c01c1e07003401440f010161a40b001e5504460300004005c84040303840c1e10780000d03548050700314080050304800e586d001116002c6220025601070000d001007000c100da440300100c46540040e0440e182440c1060195005660888480790f902e0400c0190200c00d004151034603101124000c3c1d001407964110f040c0600f5480e44542c084070f40c010b0390314101e13184040500001c0d403058868100c48000030031451040f00d004440190266416031901d28202002e0354502801500c01091540c07042d441510502206400c1144025580072a01036100d42090000c0e105000d014281134a41b04c202c02000c0c8100e6004403001080311000a000502c42041c1c040e003250b03041a5403110750803d2a40c10b01981c828400d4070b1010200318480040c2034180700c11003510b28002c05280c2005102c0c42c0c240011040c1d0f00c2610714103040400c80b49 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 748778507 1250 748777257 748777261
    0x20f180d080d15060504031e02010e0319050c030604020105040b1e03090c0306061e15040515042903071b021c030311160f03050f0d020703020d02070f120807020405130506 75
    0x20958586c05103200003440c070b8648840d5008030441d014010541c8610606090010007800c000003402e000715084600e40d01c28042068100748241001640d81d80780080d0050615030500e6000284540301e1400307641c0c1b1103200018540dc4114441e0502410000a914107585a0400c0c0f0700c44ca8545010f8507070944240700b210041a07880c030f0074000340b10001300c0c002c580382c00c1e5281410a00007a01c0c0100e000e07008540301400000b50300e84800958074103107103040c0c3c950390703840303003401d00000c2d519980c0ca6000c010150078441c85540c1c140f403801120b41081c22400c120b0540101d882c0d0300700c0169426070340290003000480c2e9502c01c102c0000072607001c0da44252014850b103a000104040640980e8803d43d0300c2018021791400481c1341c456070030045500900d040703458424404000202ea80c070924a18100c168000780540605506101d206507402c0b1910252003080d1816440c1c4a44a041c0d0158603981c1c5400d84421041012590858030419400f0f0000e2213240b80020000b0558813409609507524060440 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 748779757 1250 748778507 748778519
    0xc06111c050702091b041a04030204051302010f050313030305090c0d12031a030304091e32090c0105030a0e120403021503040b0406020a110a12030609020f180d080d15 73
    0x2400441c0700b030b4032000d5003414a00300d07421f9004540300e050b8086003e070070400400540c030b840c01010701c925002c03d6120510142071000604001800d86441e00b000024820700002900c842460302c1c00310f8040c5404122522140e58103418111300d904400c1d4441d2a54200303c1c1000101c03107800d000c401c1d240c0c404000c00303580041c400f64000108880b06606800421092003290070341d40c003810700055110004880d60312148002070448002000d41800c0301c40c1ca501340800341c064107542102c00c4140703c03402c881609080180660345c0010440c5141407040c04400203020001d294080114028960125040c00e4005039402031903500c5070000b41c0c050070061a105443c03200140c116030181d54403807044101ca59494407150000d402c840044410011052082041c0704410000c2081040c02406100100700c55404080c0c2160792640c41410080c1c014002c141080603c01c007038803d0324a01480b21038040d1f146c81c0001d04180c110500c001d01e10b03132001c26018603031034103548105409071005940c000c01c26101c00c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 748781007 1250 748779757 748779781
    0x1703040b041509020609040e1204030f0b06010f050d1d150a05010b090a0e040303140a0c030c0801050f0607050304080708280f0807020312040909050105130c06111c05070209 76
    0xf40010f50481030410140380d480c20300f0751180304008416030907140340c0b0824188a46555101ea40141c1c1d03882507540f0010103000e950800705401c01001d083c02c400c1d912604c000075215018140240c0241c641d1505039198490b080b880f80c00e85401d0700380030b456084861944542c0c04c400c0507101c00d05454506400850054111400c03114142c0d00103024040040c500483c00c0c1500701c00030421010103844180084207103041103040c900800e504100880c0f80c1c01a00c0f0001d00b01c1d10111084030804c0300010040003c2d1715209000d4810079015104240c0c2c860150414615505c00c81d4071240e20b520880000207400d02c00420064204a61207000070390140c44d05180c002a024180c6c40030b09100202807a190003e0410030041c851907201038190f4204000018005c030460700150b11100510303440b09400e07002c01c2000c3c0b081a030722001e22904045e002c1d05548518400700814001e040601801c685e40e185095030030040c2444040c42800c1906045516160007040c1d80c2100004a00032580c40020811241c894 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 748782257 1250 748781007 748781021
    0x1060e0702030f0c0703021e03010f0b06030a09021503100f06080712090f0515061809060402040e030d1128120b0d3f1b1703040b0415 59
    0x1d90045081c000f080d4540c2c2903560101e04241c600780316100c00000103031240038285140381d860850110044100d60241400d4030017403182040d09130b14007100d10000c0e55600b8183c03a002070344d0800008170751200340301203940a0540324034003480070400310410050b6681d11348031006540402075004819940c500c0c0a56480005607070305d00100e5400800464500119405214000d015140c00001c40c505900c8403800c09000c0b1201e4030b8114854410031200f41003c0c0030310f80410019116202c1c02c0d180070100d460b290000500300900c070355242c4070000032210f0f0801c1a10740c0200c0f401c00130400018170b107081049540c0107401440740768160081d00d40001512001100c0c48100903211028080100f003195030007401c0c6180381960040702c6c1d44140300851240d2142c058a41c5180c0505040010351143c0c055100d2805480c100e0a0150b46041d0100e02ea4442e05800944501460101d16112070789030294a4282d2100c1d51b152604000c010841030000080c00c290040e400340c5110b41407400da8408a80c1070301d1031 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 748783507 1250 748782257 748782271
    0x13090f060b1e090408040521011b020303060603180601080a0201020c1815031c03020d11070f0311070b0a0f11070614280918051302221b0201060e 64
    0x2524000210b1410880d6140d0b07401446044c82da49420341319400100e40900d03e002a00000f003000d80b506c51106001d01c0740a1201c0010202d094140103007020095982c40000c1c0180d01035007000c4040740c2c074009210b50300b41c00b00e064001565425038465407010350310052007905070300520032402d0104181c2040c0040c0483c90340c0d0514150140e503200750a1072294040b121203e50903124a95a849401028a09c800302c4e80d2600c0d68050380d0381a810380e54400751019107200c1c3e02c200004100ea0707030010b4105d5601081c06941801d1602c950a0704140306401d00c4810f030303c4102d20900000750798094a40c010002e00c2801120b895602280c07035051901079880350140110400304041081c00410404000058a4000000e421002149016008c6420384030410017074039000c5001c0400a00004c060710381d21038005a0b0a000800c0146404004090145030807000a8001c0380c03c141e20660750515964000b00300f0607603c1d410700078140013240e8a8440708800d401b103801542791005c0428220341c012001303800744034 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 748784757 1250 748783507 748783549
    0xd111011040e1b0a09051201020f04061b0c0306091b1a070501091217070215041205160803090c040204080a1b0807081501120201090e0613090f060b 65
    0x2003442e0080406420180101c01d2071103809003c0400c4141c500700904002d482c3d50b544031502440c00041c0b10703140100c0411811140d006114080b880c0b4807110a6404880ca03900e0419070f69180034062030b9484101d007001510f210761084000c03040c48a2604031380c4215100e0032250400c1c4050444084c900015401684180107840c0d600c1d4000080040c060201c00d1701031000000c59500d5965080d6000d29148107030004541e0f050000f124190742014030551007156030001c5c16114080030114504a48001d200400707171030781045800b20701c610990503507a00c0d0381b400034902401015800c08042c0e5410845203007029200740c0c00c40d4002e9007491f0082d50103e501c1d10b401400503182c0c0d9a9080b43c140c0c0100e5400001c0c0c580d05000050508080082100030030003180508082007000c40310307944901e0140c020110141d03440502c400140d81c4005840211440c0c00c1140190f5200c410000b40c280d9000b0020140c03085c2842034001c1031003108480e51109078810101001010030810138480d0203c0490034a0603022 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 748786007 1250 748784757 748784759
    0x170a0815120723091e09030304170304170307030e210d050606070b040f03091703090d26090a050108010302011b020f13091119090e030c0d11101104 65
    0x145400600302c88042a03074003020000c407900b0081841210121403030031103a40c540c500117890428002015802640040c003640c6149801d441e076050315400100103032548640000010140310800001c4902c07082450082c40c1d982c14260401405001c041d090b03c3e105004640042411f55101c0e5001011506c007000074a0400014103100e00040100408240d04240304220000002c0c0c001131b121403040d40700e43d021000c00101070900402c40c26007504000c034403050040100395226400010307180001c1d41207805141941003403400704181080c1000b0130790781c01c44c1490905842d54040340034205080060fa40910721540d1980110341d0030b50f00b0300c80640420400c00c01e0048a18000081c00701c1640081d003400c841480d003070003044e0802c5054030510103843e6248031403400c03c0001880340800300170407182560950014181d0f1a8520058407c8158550b80e4a041680805040c8141e490800d101d009a5029030300103400034001c1007a0403031001040c003803480010401034040c49044414410003056a00742 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 748787257 1250 748786007 748786019
    0x9030c0c0618060301030b100e060901140109051c0b0f10030206070804080613060c020a03020c0d050705131508010e0a1e17090a081203070309170a08151207 69
    0x15400088402071560805800c51503d07100d4500440c001d43c842c403807940720740c5090029007003030b007260b504002c2140102000703012a558401300030340c1c1501c0c07c04040030440025500166184800c81e07101e5504001840840b440d5009a840c071008802d0180c005040f0650790306208080302c11045980d041140c600780b40070720250500381b000e02001c5101d4250545803e881e541042c0c030709041200c002140d8210040f0310410003030240035001802604c2c1c0003d020721146550b01135250f0056603055809034020744680010700400700f050400034030b400b42009034464400035008018051540200b009201d101d040012103090511031080040700c001c1c060308103214075545010417011014050082d480720494403001040848510000150b040c0b4109035468604400b84882c0071000c0c0c0c0241115004800c00004c81160841100c4e84214203141c00a140150f070303e02002164030806410301001c9020031400e038260740010016000380550491070b56908003050410103002c039404846010303134014140400030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 748788507 1250 748787257 748787269
    0x402071220030f04060e06122d0a02030901060e0f060402280207080c030d090b0705011b09030b2211040b0d060504060b19060807030f0501150809030c0c 67
    0x4a44111040d110010345407410003407540d007000c0d114802401002a040183c40d80103a0f182e200c42005031403072400c0030358880e0032040610f001407030250000c1c4d603c00e42d00f00300b031a0b01c1c0c4142511001410040510308100c0d009000035042151074900320f6203050808113190720025405c0748154100181c1804958898060101a401200c40031000d6000d400705410034101c000307032040140006a0040024614005116180800d4200182c0c007a821118007401e21643c01021803058511041916540344041d2400a004200c00300c03620101c08920074035100c0c0391742d000c070507001203a01603100350050351504280c40d400d2035031546101110000c07100200d00001e103034080d0203907844801003000456002e61800300301607040a66080b22015034680400c400c0007000d1048050012043d902d41c0e41800138425070004c2d892281c000d40d0103002d40c920019078028401d800821120080d8a014446540d43c2d04460207030003080581180800d4084001401070040001501c540c0f0b802d000c020189039000100303000d1 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 748789757 1250 748788507 748788527
    0x9010603110412050a15060b0f16050102070b0a0c44074107080f0d0506030f1b012d02070509090706021f15032004020712 54
    0x41e106014080040c2c4030038222038018902e402400540780d00800c2d8600702500d00100300122440c82d29114062040302926000e444405094051450b070b41c072282803051108200d101001070180d03000103500f108005400b00c4c401d01a076070207042070142d00c85110741501c422006200d104082d4a90910f0f01580649030001040d41283c0c0300d5031004489a500c04900c1c0507601103070f420f404580c6542c030136a100301803501d8229640540c800103480c0d00c81d504881a0550705603054500cc129800b003058010300016030103d443c0c514103100700035501c100c00381446014100444010788240201c041402c0b0500001c140340c0010b00f0404680890203602c600103541e80c14180b0b600c101414101c803000980c003147c008401c082c003142500148880b519110400054690080c4182d400380c1142008020990300000d03400020050300d1130500d0300034200303105600244070041e800034128003074440000622180c4550b0201c00e600c00c00307118040420610500080e0b22507101d00819008141d5441d0140c1031054107440 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 748791007 1250 748789757 748789781
    0x10030207111f17040b01030f03020f0604050a031116091806090b0609070c0b010b0906160c06081008072108030103060507080a09081902010204080a0803060a050f09010603 75
    0x100d1140c4950000c034114994880c407000a040140118820003900310005003c6180c2015114400d0302e85591550780045041c031000f009401e4903d1020201402404103d920f5544a800c03a503680c541814055991003040c0c0307058001c00c0010710700c8540c0b00740c003040021121520300c01000b00d00d840c0070940d80c002c0c408400c196400b003007034110f10400600103020b02ea14182c044c45a080460800b90201729800c0c40152115060100b03005503140021700105603181111000880d85803515120400700e10076200706900810700081015200b002c001c440f0750044140c65650341d820740300d6a604510540006480d00508600758004001048400710400d45440c5074510303884061000c50084c0d81d40e01d002e800a820850f04c6503158801c00461700e40c0440b138240d103d4080304043c00303003140d0740d20380c0300c050b202d006481e1890070860500000e0240c000d40454004210760002c892480d030180c10885083c4d0000d03100036228000c00d0f2000a00e51a003445404102c0700000c0420a080c1d180010907001040240700170 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 748792257 1250 748791007 748791023
    0xb090d02040b2d0d05060c130515030a14070905090c0409050c0414040b0d0b090a0507090e0c040231030f0f11030f0c13020d0c11071410030207 63
    0x40e00c2d15440e031029000c0c0303000c50440d0101965400c0e10300c2c05200c1d6102a2414042c4c0302216110011490004000d90803440e0586441d0383c64000c00030040c000c1119070013030b81c0c0141c014404018048200ca00131841208400b0301000110412004146090402d0316000006801640144040c2c5880301c3c14a411904645d410b078502543c580d500070664400f195030385078048001c2410040318404481613a40c201d000c40e02000030080d0480000c0681c40c3d551005804030f070303000000034840b40c400c00000400c0d50b00302084420144c1d640c8880409400b204500c01428000c0301e0004c000c508050080d5004100b42c0c00b40341c26502012603292055800540654038030700240f210000204030b100c1c6c0b0a2015900500350f44031b14020505024806c800210a401e001307911102e00710307000190101302c001c038406c0115804004045000d184001a000ea4405d08103980d140143c00040160401d000689013549042130f1018503559514900c452040c421001d60404c0d1b80c10b0580c50740c28480d9009040061241c490 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 748793507 1250 748792257 748792271
    0x40302060a11032e09022206050d0203040303090209091c180611160e010501080106080609010e3c180304050409020103020d0c1206150e090a020c1207020117010b090d0204 75
    0x1864041950740c040003c5da0b0340000e4030803402900d8480541000d514040c64404180340a030010034920503c2c1301840c50b10380c00700c08101014443c1d0850f05201e83c00030195a00e6040c10344031240c03a148440081c400b41481520220103070350243c0310502c581c1205d40c64580496240800c15248104d010040384a03601a8024883c44c1f880c90250070009407010880c0d040140d03040000140c0b1000c0c042c0c1102e010322480904003c080d81e154240b0701c0c195041c14024402c6619441070415072034408044103d000034150a40030a6a101e0a0f81ca001a070300e50050540f094070794421411400c281d43c2800c08286d003042000f8452810f040c2c001d640413920600d40103260440403103c0d101160300e03107044400080c8555038280711a1300d65000d440c029112001091451150b200000382c484081d0740b101600590700d19000441000859045d94040014181903a030f81101d200982c4141d0b6000e408100d0110304007076030b014280f107401c00300710381610825a042c40c603141003403080040302000784070220381c09600c03448 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 748794757 1250 748793507 748793581
    0xc070f0b010308030708060a050310150f0305031905070b0f060f04050c030603011b090311120d051c05100b0c1c020f0118050303061e0d030503040302060a1103 70
    0x803480c001e5009103040e64480c280b84800810b50800030b000c0754032400103901c0500650307078040303400b901c804854200050044c110940ca104074200c3c560007000a0509910000103102c8080000d04004681162414011b07440f480c00381c41c503000308903001e41003030101c9001030b103070200660303540703820060041440404001050000c1e007514000c64406807411004028403000d07050074000c0000104001c41e40c403074070300b8100100611840040c4000751942080d1244940c039034446000c66540720b4803480039181421564400503140380d009004140103482200c40b00c001300100d030320400f4055001d003a01d21140a02c1d00700240720b1600b254481c00745500031500a800d4111000c10381404102194003c0d0400c0041e200d6142d0031104060401040002c100001d00c000640c0841181d0380910f08460400400e0161700001d072440c801c00d85143c0d00f18200441117810306820030055441640700b40e00312200c5549004880c016030390112041f8940542c20b20200d551119034a01d4000c401610480d200a62400c0300 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 748796007 1250 748794757 748794773
    0xf060b09061309021c0e0a24060f0b07021509060a05090118060306082505090414031201030605090f060403030b030c0a0b0705010c020319050d0e102a0203030c070f 72
    0x40400340182003c00803882c40d0f4406000b001b0710300c000e84018000c4680580c60358080041c4080342003903080441070070365807030112075031060018003c60030b8098001500c0e100e20100c0c0d60300c071800980c484c3c90340c04000b214400369a0101c0e03070400b402424581c10041ba2a2040d1843d4108800160501403e4174038401889030030034011008002643d008281c191500000f41d00b0300c45403803804241000c901054480c0c51007010341600c2104c5099440110607951414525030880c0450a0a40e0a010010701520101d140d14040c9040c4e0b03015800810240d12000760440d682c005c00c95181605401c4000080d011900941c410780c0d4408002e000c1d0345165070f81c00c0024542d00380329009038000303600126903402480400d200d54083c484841c0000c51805103031403e0898901e070010388050170031100041c9100190540e800c4981070540c0401105c0d180e00c82c01408201604051500745022640036101da03902c2e0046581c44903487c01c0302e4002c1d51664549103180c600350351003040f00f69598030071048002e00282d10b83e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 748797257 1250 748796007 748796017
    0x3140708090904060f0e0d0801140102070b0705030c0d0f0806090c0c0d020318060306010813020102032116090f03200a030b090d020a0b060409060b1c020102010f060b0906130902 78
    0x1d031200054600b0903904500881300c03081d140c10007e900c0b02c8505a1003035004910641981e1054640c01100e14040d00101c1c0350400349d0f0007009034060003042c07070f1041010020152207180e509000303a076041510344d0b00c11500344181c2d01b40000040d035040d001c1100da04000d07555030b030040090800c2c18500152001c640d480e05800c03020b49030059000140410210f8180600e003441e440c022100704d861410a040020f241c840d010300748a4000b01d48820700c00441e07000304216160240000403819035802c16094000124000304c0d0003060b100245421620074521920012044e201c200c00c00308901d42c15a1101084451306002e0706400c010810640580c40e0b86d80c00460303009501c2040d0001c01450801d500c030b801c1201c1100c00409642c0844100b40c000703034103034118070360241c415070b00060030300701d00d06110340941005080d040c0c001c005011070848104000f00c801410380e00030b0b00280b1501c440d00c01e80c241156007500c5001c0302010148540a024a406001403a040c40c42100401402d0349034103100049a00c5 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 748798507 1250 748797257 748797263
    0xf050105091e0f120f1905070509070c1b03111002210408060108061f060903080703020c0406060806151206041e060906170a0512031f080d031803140708090904 70
    0x1190131540100400025107030003545805402c1080c07841c7c0d942e5a0fa4401401403520a4504500182c9001c0c0b080159819842d003004284aa00700c00c0c0c5135009444050340010b4a91602c1542001c209082c08650400c01d44007550003003061803200410131405240c2d43c0410310113501c04105c0001d5085040200c580a80707001006040541050b80402c80c000c1c00001c020000380d540081c041128941210b0000201d940003074040755039146c0c070320341241014034403803150740d215144c0310000c10b9513988021010f01c1484207175015901d4590310070310400c0314021800200c5503052854001409814283c01c440710b004c10008145003a20088110102030301d01c0d540201c560300d56546410030a0980c42403100d20100c1d0400c0141014074225181d6503201c03038070102c004241940020203d20340da45c01c0700d0301040d01358907140e00640c2e06445801c2c10740c88403008510400080c1c20503240c0c5040c80d400b450200303d5030340c0c9610782940c07840e40c81000210641040e0700903900024103011400054980d131012600c1284 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 748799757 1250 748798507 748798513
    0x306020d020c0c031f150b0309100507111c11071206060f050607030c080c12130e07050a031e020708131e0306090204020f0a02070f050105091e0f12 65
    0x1102482a038902850806150702c00c1e8007064055100105c00b00b0745240303290fa1714501003001c05909240810310317405940440341c160000000c00100c0e80e00810300d19035229406c02c0500454039440d9044440c405000c46d101c0b00d44d0048021150802c0c1040c6015954035150709180030040c1da80044141030081550003284100301107008542004218469840584181c80542140c90700f0600402c01500441c03070028103100b9407000840c14445000c098030303d0292400c0031510030407104200006140c0160f00703003a01590311140082250781c030000f0b00c00e2041e102640c0d103a0030000b51030012800b424030f01c64501030610181c0495100030076580020204203005542d0719070340300c0a0102034496074080742c0c820f050740c09035030950040c0d860690820901b201d821110115440741c1d80c1c00000c0091061100948105038002049540b060b00400c0304001c5030001614800300d80e81d10001900c19102c0c00400c04e600000b201c1401600044030b000402c3c1114000d042c1d1180f031015180400c220892161440405078 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 748801007 1250 748799757 748799767
    0xe0a0c150e191202030a021002030901030f060b0a1b061812090503060604110408030a03090510020c0606060c01090c06120c0c02150a0c1a04020f010f0c1b0306020d02 73
    0x1940000030200c51450030b88542010104011102d04814054019240d081d440d6505031019540d08110080445400a0102401d101803a8000e9a05e0b40f1040140b0701103828411400c0d50b1400324400c2c6411180d04001c400d140c041c075039100300c9000d50650500f19002c2181000700b80821064841c0b0308101c0e029014024440c052070070007264200d465003018003045681003040c8250b88000c60100d40000301030b90042005110000504800d0090b904002507a20010a103044515032541000b1a81c3d0300400070340e00020144c800310342c203900c5544c01083d1140d00c4180031a4150070000028000d03440c0704400002e20b000039640e11003003e01580d1040c000515a1070040000c8202441600c40c036813454181599100b200c1c0c0d000c80c0c40344040458400c0b600c000801c0c0350410a0145c05070030b65003a4040507185070303480ca02e030b10b00e1032490307040d07500360f001d0a01c20030403030400e501030001120100d1071394075201d8582d21240d03034420135990300d800c00702c2000c07908440000024035640040d004529800c4000b40c1c0791 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 748802257 1250 748801007 748801049
    0x408071a040803130314060601020d0e2d0a0b16410d0c02010210090804080304031203180f02040c110a0c140612070e0109030c09020a1202031501030e0a0c 68
    0x2146c0e18038054903904080700307101e001d07038001600a0300007510b81446260380300c0c0302e0001034030f54905241000765101d41c070411000c503440544540780320000440d0790542454840740411500d009000211051a0b29840e001021540c0c201d21140c007500340003040714000c2c3c1da030100e2035150704000f00030340d03034441c0036110303550070694203116822800945188c01c00f4000a9500003e6454426000e460002503946801c1400c1c8170007181101c0241440000b1282c2c0c8035601e1070111585447e20403174400080c90f121503488401d50348010040b03025000101d00e910425242c00700b20003008280340036001d01480305c8901c1002a4180042c01000d4080e2201c51020b6250000860b04800b10700205c9200da0001c00110700c1c2d85029a0381035801c4000c03031808801c11800b801c0141d6414689400c09011005e55400c0020108070540041040080e41d43e2030004610204015205900041d100c1c6c1031041400b452405255110b64480ca140c0480d030300845411745404d0300e442c5c6524800e90000202d41071903904150304 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 748803507 1250 748802257 748802273
    0x90115090902011d0d0209060d0204090803091b090a021605070b0d0b030303010e0711010902031c030c0f0210020f071a01030b0117070e0601021e060703060b0408071a0408031303 78
    0x14281440741004500190200041d40b002502100280307c4d00c0031070b010810781c0e1a03842c2042412a070261041114803110b003015010f03a003044070403001074460316000503080380790241c1840712441c0180c071042c01d40d00c511580c90065081848a5013900484145030004580e041190702c00400440301910303030361440c0c0000d644c152107115a245000b030340f042004100114000001950000da00d140c02d105480202c00e02c01e0240050040c003039858810120360074901c4502c05040007a003400740e2030070442e42c19141c8055030b40e80390450340d8074050380002c001180703644d1641d001458800b1150b29190310340156030303480160134034080c100e922648940c0030043c02042800300000e80500080b405d440581220142d41039a15066070280c20300c244803040220b01141d0013003094408035603902e007200034481c400c20083d0b070346d032442150181e0009081a00001d015400c1004650039180e000c405441024141800c070741c03400c0c6502c040024048400c0100248100c414009000410344c45100c04081c00e1071410705c445 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 748804757 1250 748803507 748803527
    0xc010f0f06080105040b0a18150b0f0f09010506032e050306091504110103020d050a0b1918020f04050a0810050601030509030a0c03020f0703291006050309011509090201 74
    0x106a00d13103414000428040361200741d0144c003254001c511907421101d006060a580c1c00002c0003602c3d01000e0040d2904283c21000f5541c0042c0da0902d41d115a4004115510070099202c079001485180140702e07a06040004652208045628000b5818403440e00f4101a40c103c10200301d0001003041030225103001d11034503030080c1070040241142000079640c46124400030b40014403010142048249a90182e01030b11845030701c2c002d0412242c506400300d10081c00580ca007162140420100c407000c03542d0916a881c0503a00203a460013225428920920300962001302c01c24020342d801e05c400245a59407007201070146c11004c010384415444c10344050142d9030013414a605040c206010000c2c891070000070360710400329928001d41c4040303081c282070382820441401007545014000d0040b05001c1664549001640c1414400e410441d922b81c05800306201031710114000010080200026846107029503004a01440005441c0c4240000005c400b80f40c0d600c1221507640b901044010341da0011510b003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 748806007 1250 748804757 748804769
    0x60103150b060d021309060b120603030f07030806041803020a03020111070f060f06050a0902040302010806030d020705120316060c0e03150601050a120e010e061003030e09040204020c010f0f06 84
    0x1000201e40c07000010400c0c003403020702d0909250b011800e0010a802440d01e00c00400c040c1c903080003000d44416a0022076440210182451700200313000c14960f040000c1190001940c020615041400d0b85c0d07030032071fa2948041c09050b401510307510805122044c0503103d1483c40d2003600100b0800c08140f41c007900356100102e0b07000136100103020040204002005030020b00c3e9118100045101480c0c180070b00030310351604102d412000f11070380403409406550052080d139000740c03a040660740d100005c0541c0c2e469004806001600480800c01c13003418140b040400400c0c0d104292070504900451290250f400040c0503209551a40780c56035130990469281001c420054015282e0022002006803c008000d800c00341003100000e40700c02d8962040b0100c407010003041206204040c0652800da01800c04401c0f0841c040c0940000f142c001ea04c0000310300200c1e139154070740d85582540e01d01004a864001401a41c2040d000c01c0ba102e49080203100710340300281d6811000503c41941000e50085400350b42040b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 748807257 1250 748806007 748806011
    0x3090303070f09060f050d0e010507030e100623180903040302040606170c0c03040b1201060311071707020103020702270604020c0705041113090204030b0f0601080403110705100206010315 82
    0x1e1000b503170700070f800c2d01d0001d105041c201d40e034040030004180107240d01d003090703040b551038007003880202540740c1c00c00001d07014607030215103042c1103130500901100e22501c42e40010500700c01e001c110030880703500c0303d500101b0014076840c12600314080600010340f0454000c40907030000101401149071900c02e00c07025104174680791840c0c440310218080303031240213080080282004540d040144d401041140c0c040d20304c4a05080d02c858a07450000e46225080c01000003290401c41c80c81d00303010b004016500c4080d0000390b402000112084023031182e50118400f681010b8003000f001c070240c2ca614144000c0103088102110b0017130000380300c90301010006499240b0803401000070001c040c4000500034140c0ea0201c03000220811a268051118410301412408130460140009030103c00d550151085a0260310004d0a55030345999000c103d8100316002c50100301ca17000860082441404a2030351003800504945211b03880d04002a40c0403485094640140c1c440c07001401008030385a180c4a90040401e01 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 748808507 1250 748807257 748807259
    0x31203110a1223312312180102030702090c07060b2d1306150306060f0f232a06040302070312020106180504020f01090b040501030b0a080303090303070f09 68
    0x202d20301e103801c0608228114144070035103c2000c130007810203002c00c0c010388580300c40740383c00c0b85004001c2d1501c03842c4080c1c00e1021407000035803095021500070003808070840b03e03034500522048480c82c00c00d00e400c036050442c8001c3c0018001604c5009505000e07502c0003000356115421450300c42e0646d800e90450902440301c0280182420100150710b00c0f11580480030741c0b02c0c0e407503004081004146050301d03005020341443c00020307116002d054a104400185e603010b0101710344900303080d07400c00079101d08103000480003a41202c5581c03040914040d950b10741900005080899405583c0319041112455003000340c0300c40c45946654554415014108108041d1126142c076480182d03c2d05000d100207840d48656544842e40a4401e41c4440b0140c92030f00102e4000700c0b003041101004100c1261f049014020300c1510308000e6008071075048c11611100c0b4114541400e000044000c3c1000c2c9000a40107100040f002c00c0d55001807025503c6102944019502c0f07182c100c00090031b034002d05078040d0038007110141c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 748809757 1250 748808507 748808561
    0xa050c10111614061305120306030709050a0b0d060209010201060f0506040b093c06070c091104050402030c030601140711010c020f120a020103050c040609031203110a12 74
    0x10b5410200111010a407041c040d400d1444500341804601002c3c1c2c0102c40401c07168010310441200010300650444000c0410038014807558441039920742d5150f403000c001004010741503082131b50b010280c80c0340032070040c0c91800860821443d40904a03151074004c5141d948039642481680010000031192154140c5040f000c00c00600c40d600940d61a100c000039150103544072108240d0881d0038510748001d00070152202c80c1020362002c80c48244d80500101500c1c00703480d100003a5004035800c482d5007142e0b285018603680c014400f1101c0490110800e0000150541c1c0c0c61000e1481101c0d55444640d0328900900010300c3d950201e89002d000400a002c5640420b07c40c100003092114282840c0d80040e2143c00090b140818601d0b03236552000c5003020400d203404021a0000c403091007a00c3c144095111000c2d8000103005501a01c00000c240c40340400200b14082240c0e03515421500340081d401d4a80c0300441041d60001801380c1c04202c0302c0c4d41c00101001680301e00d0961046040c41181e041000300 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 748811007 1250 748809757 748809791
    0x90c0f0e09060f180108060a0b0f010810080a08130501020708060a1a130e0f0f0c0105030a1b08040c05010305040317150915010305060a06021f110a050c10 68
    0x800240260301c5030002880030344900281c0800d8802c01005900b00360000415040310980034000c00c18580505804108441036601030701201103401000056481c64020044039000001000740d02042c441da640001e004106010540d00a03001e10091652840594644601e0b0055030340460b0440d8084941001460303000314400e03400c11200c0c0340c0070902c3c1016107900c81450390901c015540c0905040d4464512810540c0004108100f40e401d65519401b010000d98840c03040c0103500701e442c0c0000325403101e6903110704003c641c41a146100080e013081d000400b104400c4415a40b1008a0200d42c213120030302c051030b0000c6000303200900c3c0c1441540b525940041c84240841404070701c080311407021880b040c00d0f40350b6090b900703003000e4008170f82ca141101100c020750245100342400b1901d0f020101d0301a0414180c00070941d0b131140c00900d03008012611a42c2e00640780c5030004011560345840d0303d200f8100c0c0004150342c0456544a9494070010301c030b900d041c007803549440c01d102440e01b480c0b8a5944006 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 748812257 1250 748811007 748811027
    0x903020306010b36060f0a022119022b08241e042903010501031a1f060806040f150302040b0102100221070221090f0613090c0f 56
    0x144040024030036040950301303c28070080442c0381d0b0201000c03070b4202000036440b010b04a0300210fa400c480518400c210603c44520303031713a504046110000c006007042e1408030200d5000090343c42c812150b03005200000256030004620340c0500c503005013064450469072018903550000e150003a10b0040b002c84071401603415078480d07070761400303622a081e140c1d40e800c1c0e0b400d2142c0341894011b8070911886100407410481e610402481500308104024581c5603800c051041c44e069a81c0044490740d4049140030800d64080010921310640f11003420b0388000c001c3c01d5000400400d840e0b20752450700d0a26204220a680d074aa0000a9540c078000100740400c0b41d40002004480d019100090708201d603c00403030410030318001651301c0c14000900320b08020846100041042e110b2000c0e604651030710070049880350b1411110080030309282d00107803100d1500d08000e004010740100820f5624180e440030030140d8001140081607940e203024100042c147c40c3c060840384541c1490710844040d00701d41c024105e0790103 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 748813507 1250 748812257 748812307
    0x909060906072001140a150815130218090622020918070b090a06090b030f0606040f0909030206061f030f0b0303070819080402011407051c0903020306010b 68
    0x200c910308543e0001a800e1515001d0400c2c024001003074201400702960005940d880c90722031820b100c0c142d0b034026000d54041a901504017a01031034403d04c103616110800a040c14800d0302214900800595510600701e044280b8901d56100d140b50881001d0b050540041048929805001101d80380381c0d5480f210411240d0b04980548840d00c0c1c0418020300c03140c414144d0790140c131070702c0ca0105074910018081c0c0700203a802c48030100b403580c44200c100d0348800b8a10405055043c10300105043d070200403402c60784240050500e90400f039036003034680b00388041c1380c0c040307000e05030344400a000740341e418800954010420350388c2c003200341d0f07040307000d08103140d43c800c1d16004040d503403141c44080f0441c5400c500d4882000408503502c0320380e0b40c02c247d410b90b842040c0041d14180024802031985010f40a041e00c40c40d0161118110041103d90283c401e50140908039203d02854a0342d0150280c00440302403070840c560384401446041d481450701d094011303003203142005428081c00e00d0110908518a041c940 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 748814757 1250 748813507 748813517
    0x50103111201090c1e121a070302210f0f091209010e040603122006010b0a120903081503010203090c01270303050a080705072018040b0105090906090607 67
    0x481c90691a0041500180c001c054000f010b100242c543c0c0c1c01c40808990340301010344001884c1c1c0d110200c00491540c3c40c0700906000c00500c00c400f05151812400e50b1042040c1405131130701e80d043e42e41c0341c03407403290800d03030303101d14040d00207000c079081d19412410350100e0038034034445180c01c21084540d6288810300c0c00c481c40b140300140e400b041d64440c2030140400c01c0c02170018808203480389890501c00344e5801c07803880000c003090171912241070416181d02e05001c14101a1001e6402c21106070020350250884c5028002917100e01400c0000c1d5218880445020b82c0c1c07041300c2c030300b003503040340003c00d0a41505070301c20383c014400d10240d40c602003950401280c09090502e10228142e0248000b030111038007005504401003c004281904000107040c43d2121350380724500707642c5204040c0d80c039010300400980b040f030722180c82c012b502803031002555002000801c4d0610010181031088400721080b642214820142001003125003481611590000c130600040d1070a031030f080340c48942d521001001001000 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 748816007 1250 748814757 748814779
    0x60705032109012319052502030403121b0b07090f0906050f04181202060f0f070c060507091802040e061021090609030c14160b1b0118030e010305010311 67
    0x385116164045d00003c2c03c3c020302c11071400e4220b6034058400c80346440042e0744002d45401e03600d8800720032501030369801199100c9440c0d0043c5c00703c464071014480c60740f490344105030407404100000f88191042c052076451040c10307400c044207a1258a80c550000c2c0100c1e0500303c00303000c659200004004c04840070f0350000f4071a100c1c519040e0180f42d50b95000340186c00f1030300c2c208800c5940491520b1150150f0301035100a5180d00c0100c2c01402030485102000035422000c4000040b206e4000c42d8010180389000650a500c410b014040200b01c0104a00356a600084c20000702154003030440e400032003200c1c0612103e00110000d03100c90415842e440d80300d0000d180801c00c0d008143d009408450f0800300030800c40381700b80740c0940081548c4030144e0300491551402c1250b807030006480034018001442300e075000c80c40c21000c0d01440e04800040814000c0f103000e1480c00100906c030312254040c1400204403500315904024101381440200d0758101410940103102080307d0340100c1c000c0c043c050320b1000c250 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 748817257 1250 748816007 748816021
    0x6012d0503090307170a110d090504020a0201060801060807032307050d2f03060f0411010e010e13061509080a030804030302070c030c1502011e0b0607050321090123 72
    0x261290b0300c1c004017450040112000c0e0603103040c02030300c145202c9466400108a00b0414940e0f1201802e40d220002122140240513604064018020100150002003000b0343c40d10b42545c2940c005801801e001d60203080c0800520003500402e5600c2144c2c1070102c25603000c1c41c01c2064403903500c0d025150099400c902d2100070002403007441c841402c16100742006141030305020384155440a01141d10030700c078900c08241048480c1141c14021540143e02c0b00c0d000c0f4040005496401505042ca414880f8903400f024603911100218000c52800307020009071207080000c2c02a0790150319261074104503102c007050140b0817000941100864150500b5211035407a403408a0181c824440003d08406140750000200204e41803180d040d00c0503035070400c60030411044120b080750305203503507001d481ca034107028207420090f44d40c440c00f840c1401800c00c40c6002020303140c0d02d03d1603010000c40e105040c0c1c80d4100345031186500f869140c100c0e094074001c0c4221541072003424039100c2a0320540042402a80103e802 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 748818507 1250 748817257 748817263
    0x30c0f01050d020a020c0a0e06030a02011101020f03040f02030106170312250f23030c0901090506030712050106050a0c062a081905041509080d09050606012d050309 72
    0x202c224070150358660300000000d4407442c0320f11000340507a03810003011607040d1405601501c030b0030016008060804090700112031902444085907107a550800540014075400c070020340c4207900940d80841041c0051040c0b60031202540d1022284075042150401c14900c003204680003000d01860710b04d0b03d80c990910240d130009100c82c12604114a4901c19201d094018000390541043c58941c0034411041741081c0c503445030101203081c1099000c2000809800c1c252001d0320300c0c25018500b0308040c079107610205000e54002c0d81d0080100c0c82c081d8502809920900801e400350080d49051814003480903009480c215a0180081c8400d07103c0304c44100000342c4054400d003e00d0342c016040e6031a084a140503201034001d48010100003000f40c44030034000340c0c42c050301c0c2c042c9912402c5071592101e0240128010920a0421150b001003000018001d100300e00441304d46900400241c0303074130704004001500804694890101449602c041c11501c8405d8103035445414041d402c140703580741d41d0000b000b81 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 748819757 1250 748818507 748818517
    0x203090a1113050103140106060519050c0f07030309090b0303041401030203130c06110c0904020114032d0712110a0309150c08010806070512062206030809150702030c0f0105 76
    0x2c0d1452418000006000c850b0003441c014204e641c008020440e102d01013180c991192620400aa400c090b40000c001c511500040c07003c04000c101340c416070010180f02c80e003046400e50080c0c001a51060341402090180d00c03c80c0d4211904070011842d042c941060003000d04003108a6905044c1d0110014171003600140c200554603520007449c2907219121230010300045440d01f0503e605105030020302900d81403840d0720074020383d016114801d10f001c5000004020b50f000400080a024602c10300808035088080202404420005070f00d52601c1c01c50300040903000e5440b00f0108290900d4000c204118610b002ca94044206140202d00121203007001d03c0b100d406140041955840c10156481071a40098040c2c1a541076030f00348d900c0e603156014102c415026020511440043d0782021a0040c036002d4004181c098002e280944855402c1404204545c400c0e40300f0341c2d14640c00118001103141c440440300e030411140040508000242e00801d81d00c501e0800a103004401d1014007951523030040040d14 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 748821007 1250 748819757 748819789
    0x3070209070206192c1006080c0f03160504110f030c070308010f06080a0510170c010f03020c0303040206070f02060a0c0203070e010803030f06011e0e130203090a11 72
    0x40154100160025520407003141d2283c80d01401c15150b80700d450850007a007003a28508101c03c191780d5115030200721480408022004280700c1d00c031144074004200d0081000400940014022110601c401c0c0701c400800c80d00200d200e07070070400c41e031644c000381c031a45903003540c0003940d000034807d1500340741c1400c5118400040001c1c1c5000701c02c20450301d1504000300a81071181e138407020350380d90b90741c0b099502882ca4001e00d00450005400203d481006502086c0c0c000d251030700990340c2e43c1e913401404c0003000d0040300b0411140c0254840041558118044161041c0d503403404615003850141c1145d2a80000740c070003881140300050b4501840b9469400c81015034004080700d60741d074410710b000340040e60080780481c0a40038600340010140509030300390f4126400e460255140d0b5032035509160010f02c0061800d410300070382c10140340c1040c1c2e04030b00d4000e0111442c3c58041030032070708604200018000c04411007240e40102b04000d030904011a4200641c1e60000391003c40007035010022b240010200060 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 748822257 1250 748821007 748821019
    0xa1d040f06090603062a0503070221131a0d09020f09010b03090105130b0718090609060816051008070c0204110a1209021c0602040806090102030907090605090a020c030702 75
    0x820b84040a40c04181124464001008101030000680728110040c0c4d9016000c0144c00a41150550040c002540d00007a50300c10b44180304840300f00701860583e20f007501005101e0220f003a040314460401c40030045c0c0781d82c0b910441c0300d6400303112420417849401d40e01d00388592600620340440d1100d80181c918400e005113140c00175a19000c188075150000c03145085190300b0080400d00030320300da031809075405410408079101980c0f0f0780341c25200d20144254505009881f041c00041c4c41040348640c801811400078041016854070070402d15041c03a00d149011a400c000c141000b4036524107010300d200000b2410501429500e80308140c881119100010750000c3c10184c841205401040081c6904104e07600c0d043e82096031100c1c044111400200003d400404024408001030030309590401d41603c01c1802501e4251940005401c2840a0311003030200c3e900031050260358401409942d0103030081440c1040b15030300d45000100314010281090340b14a44c0010b041c401c01900344111085150041c0c04 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 748823507 1250 748822257 748822259
    0x603190c03380306090c030d05090a050d0f021f0207081606030506010516030206060a140306060906040e030c0f07050904120f03060306090b0121050c04150312050306150a1d040f06 79
    0x91541321070b519a086e900c00d0043d12007003001d50340108142c45400c0c10242181081034188000d000d81d1760000002030347c880c081e40b690400161f407071000764185070040306501030313140380104e4002c0c1c544110303908881c40c4e5400c90400300c40e0020050030480700325200d80c903001c1000c3d21050016a040d10800301c0c2680494001c01e489400c3c16000030b01140200c0d4152251004155074048803511207500100082c1d0640000f40415014a0a080040c0d0800703001080000e00500840c41180f842d444122503100719006142c420010290500556000b40010345040d8040d280950b00d40d44251003107450b46040c015132900f0805264403030751017540903542c0300d00c0800509805080c01081761400b403223107100a150310f00c1c180944525994072071802035441801008060640303800c104c060300320080300030070150003918008040758001d6120468813180e0b4960580da804c00c1c85c2400603040e500e1800d031a40c5d400402281c0803040d8000c60f01d0015100021001180c00310010009003d40f801030f09002c031150510f40 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 748824757 1250 748823507 748823521
    0x300803070c0c05010c02061902242221051e09131a0409111f020f190b2703090f030714011d0603190c03380306 49
    0x75000110a00a442240b6101e903a0780045807886501200250400d01c24400c3c14900c94107981d1031081d240d21801a07038152205601d0420030003860388605883e0380600d40c140103440402c50b005444862410320003461602080d10390a09490041941e45c00000c100704500540c24410b0068642c03083c400c800201850a581900001e143c0003c00c03100c0c03141003400c00000c10b9103031604c161300c00020f124040d526081e40213010040104480e5006031b400f120341d42c0712406141d0323500c50107558042c5034200003201034030785000007454500e207032400f042658004a000c0340c444100d02d10529240343c4c801e082c020f5660707443c08600b40e203900790f05aa0806000182c03980c003005c000840981070142c0c058a11340b10520307541c01055614103051203091800e00032145650001d5101c2c4149442e0007281c41d0122401075103905c00725006500842d0220350005282035120f080c070b0518050781508681c64a01400542c11580510b8515a01440301e61203209112510958410f032449003401c2400300182954698603084c8 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 748826007 1250 748824757 748824767
    0x813030509040f0f051f18060902070804150509030a150f050a060501121e0e15040f060f0b01090e0618190c081003030c0c120303140702010630080307 66
    0x14003d0b05444d410880011081248450001100002045505842850409520300546010150121f241d866000110319210580000c0000520500c040d540d0380b86025a4110214514001c1c441007282c10804502655000140000c04035045456500000c401d48207290051403c89003e41c251400d000810a078410aa401582143c03020380355801020707408404141151100138404c0b4505d0301c85d1212403141010350f40f003144ac1950000494a040740d03061121180782da03080780c04031101d100c1d00d0000e804101c4c03540030f10301100020204c14070600c01c3e0f080010344011090f01a40c8641c40c00c0340005041e42e620001c480c031100c2c1d014800e00c0e00d113003450141c1040c5a80d80000e010712080c2005c0301007064521031920795100c0d400118404411904654040b150310f05d051b8001c2d14001640c08002c141000e0038010084c0c858482d4a00294940340104071007100c0000901782429645049002c00030500079942c0b8101d102c4808140e4030b016020000c03240800043d4050103040c080c1c0100400401613000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 748827257 1250 748826007 748826021
    0x120c0d1805010b030309010518030a02090a0b130c0f0c06060b13032d08070c09020f18010504050a091e0608030c010612120302030a0b03031c1401060813030509040f 72
    0x100000d02c2480003c0050656911414405034005001007004803d800800c410010b18490002e007500c40c03002203600047e003000401e03a01903804603600c40d0800d1251420740c4400400b01040d8109005140f9041c9020305490445c400c03a03000d11042d80740f80c008101300c603800170010f00340300d240c1c464951041403c0c001c80c01210740002c0b40e1103101c02001040900147c148c904d14508201e0100d03009801a0781e41c14025080300030112601e1050b91400308420819002801d884080000c0050302c2c0ca0349003a928140d240456442410300400f040140401c3e100d801e6003505840d601c1c0e20116104184401c12a150a190020006e00754071f0b18802080b0040c0100c01000d06050500083c41910344901e0a414107007922800204500103000361030040320b0198000c1c40c1e201906140c0001c00019200100f4210b03407207030302103c2c5030400710554481c003800d0900c504441003d00542c940d1481d0705110001e018104050401191a071950900030101032142c3c0440c0c50310075028106210790a16400400003070918 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 748828507 1250 748827257 748827263
    0x1802100e2202130b07050307080d090203060106030506030d081006051803160f0f06050a260c04090c021501050f120d03051b0a0c14010b03061006020114010b120c0d18 73
    0x3815000613140c83d9242681c080c01c0c0c10034055480d00e14260f0b62001d26502809082c01c03000d880340c5000000d80e8043c07100d03e0003802c9603200440e551814404050511403110700f06824000d1000a03c941107072512140ad05540450602c15610440710902e1b403c0c4d080701031b10b102d0f4184510211512040d502c0068030084516006400980b60b0b104c158150303a44060340640d000140c030900c03845103510f00c101c80348612511403415502d030002100e1403005070f050084496400d401c000140404c4410b995100c1c0c1038040701144081e0100c00500c00b50040402c4040c400d251007441d0441c54441c042d0355a010680e500c0c1000300489a401070301c4000034014000499402c04c0315107004484035a814000c100f10307814840c80c0d41e980e103219203c65076920241d038031080200c4415980c40c0c4546001382c07010094a03004014403214004064a490002401d6030004010703000b190f04880010440048144151413100c22007451030300300c6039200307203100700075002c0c1c0c1c03200c15800c9081000440c15181e88440c5000301c00c1c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 748829757 1250 748828507 748828537
    0x14090f510d0b0f04080c0d0c030f0c0308011a1b0f1b030c0112020c0f0105181212190603140c2706030712151802100e2202 54
    0x1030200030880c0303204503940080c000207402030025107099400481c180c0e01a01c01e100071410075190103041850040309000d144081003001c480ea0041c1a0040440c2848514510302942901d00c143d40090600006103d4a5500e40310b0780c00d1400d86895600941e0466030000e400c02c006036141056580e92000803030008107a50040c15108201003600c9a8844500c0700064010107030b030010100112105001c00000c800078641c240b103a041e030300400f48a074081058a12001040c1800e00940c00c58401b031111a1090042d440200c16590380c80250050300c4600005010741c103810364854000010802030a840a25aa0303d410f001104102c0e440075944038007480070003218a0364180405000a0b401c040310345100300c119000c107201701034052100030382d808a4041d060305c1030142d0760f040c0218024600f00d0b040302d05c01104892940389651600c100420800c80108031080000560042104900004840fa00f0000e400c00b42761590785070074140104003060069002d2007241c0c50300a0701c00a400051030505049 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 748831007 1250 748829757 748829911
    0x4320414011a120c03060a0b132a0912030c05010e010c0206060402070602041a0c1c0c0809030f100c0f08011511100609050114090f 58
    0x84814820b110081d01403245501070804107100700000396042d0b1048405900c81d402c220422030701d041c000d40380280c0c0305203808240d01c000d00e800c010300c4080d0110081640d514125200700c1e030f0200f40500203011801c0450a5040086100041707614640682165031a40500101c040070190320041d03101d0018041c40003005501910303c0014241c41300301074032a0050303008801007209031030650b00a20640d84039000046c5000e40c0c2c0c1c615070440603280f503401d105902e030100e4401c2cac1164081c40400c008003a1512015044065a1000341110300401c5025110680100e040403454808124591060200900b20380c003003001130603c01c01030107880c00c0c0c0f0740000300d500350607818050180244a0580c0c0d00d14601140e0110500c03803c40302000c400002c406140700c1c6c8606400305031010b12450004d00010301c008a410b41c189001030700d09012016480e40121194010080c4e801c0001e01001d80000301042c4241c4003030b11584109030000c480840c90038524040702c1c0c04c000c2036080020000d5203058076130781c580d02d80 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 748832257 1250 748831007 748831043
    0x9140706051c0b0904020609031f0e0f120d02031b030f06100207086106201e0616020705030703060c03091e030e060309070302043204 59
    0xf90b40700030318194004085038046401894540060044050007030100c500c491000e41c01000001e4011b031b541294603aa48200900e0001c00340702004c1c2c0c0c401030000420300003407000508082031164500500d0450f9010010455480d00003c0c0e411800700c64071415926400c2403440542280b0094481601c0341e40364906908a460003c2405000c4458441c090f110080c2c84100e05030840000c807103d00300f503070160700301c0306400380109105c2810700d01e9201040342c0070840d018054503803410785a050501c0080f518003c02105500410003414440b1400014051480c0c1026052810070b00304030068031003d100b078003107507001000100e0381d220341c9400c80180341500654100740c1e19112140140c0e0b415401261051000c103046030000d844e40801c0d4a0001001041c40c0c4641001841300c104c80302906607001017074000d055000507000803001e030490b41e452450500d400300c103903510b41c01d210003406681c441c800044086100f02c40003044401c00c20308048482c110f01c2042c5aa900202c1d4220f4400200010000f00 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 748833507 1250 748832257 748832261
    0xd05010212090d14090d050a0c0f0602121801020c030105150f040504020d290403080702160b040501121d010b0306070809060403200f060a06060c0203030a0309140706051c 75
    0x140e42050f00c640e24007561040203141c840e44480800e0740c00c505406c1c60140054810007412520758010075128000c18241180d82603804820340c0f040f001c643c0040203244415000c0802c86010092035480c01c10510038400060b4100302d80e000701660f055207001c04212038002e45d01440c5045070011142401103424030401c20003200d2042d107029400603440c500140c0000d5003001c2c021142601d440840b10402e0441440390703030403e4216011000180543c1c2802155601003140c040b042190000c1003403054189011400380740503620a4a04100049110840500710703a4004400300800c50b402100303240c0040d5502e4040c11042000c1d50192140fa40091030303191081c0e000c0d134010304080c030107000c10f6116510111403407800042c0281c4542c030705090344801c2120400240450b00800405000700c0e18200b200c25003161000e034080750074008815080c6d40103942c080126807041480d400c0c001081d0044e400c095451030150800e107400303031041400204005410001804021003c268865540f415490001702 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 748834757 1250 748833507 748833523
    0x30a0f090b0304140a0519020a0603090b0412140c0d0e01181404020c030d0902010306051203030a0203151908011d2122050a080f07090209010e0d0501021209 69
    0x3607210010320210300000d00c525a03a030156402e190031205400d0f200d856032070824031500c0c45400e604081550110850030000c80750320007031040b070400300300101e19501c90b050340301001440100804011680601c6050044140007680d181848017291030b040040f554594503005251000041080403800c20110343c864a48840600d0444650181103440c1c101f840c03208080001c6000d070f005400b44411b000c1e4220030006404030311040c80e004161810319000240c111660307604041c0c007030518007044600d59040001100d4110300400b42c0141c2ea5a14003903081c1c03071000da030340d64164484403800490030751400308442c81090b90407110080108040e0540003000d540c90105031561650400f500314a04420b11f0715a09103125500f0f0105460402d1203080c540410300038000c621000281c205084c0642d050200c4c8203006046018014001c21b141d4080c0542c1e59205403142d05005030300059154aa64840c2403a0b0700000700142c12003103d103038640b420902035007103154070900348220100080c0300880c0c0058562 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 748836007 1250 748834757 748834769
    0x30c1b03101b0c031b0303050f0a0c0203120402030c030706051903063618170c06130503040e040c0e15010509010315180504031d090c090d0b09030a0f09 67
    0x4510a20090b0155410303081c60100741c2c00d02600c00c0c104100c10143c072103444020b0b84070b50740010303851a080310b180c140860060805a03a940c941010035075155000011601b49200840c410f0b18581c2d40ea00c00a40307009110070480d5054090800c0000701180c2105c00303404080200001e00010b4500744004a044541d54810040b024038203417400804d040c01103407546a0300d0074a13102d4400b00100312402405541d21503902e802c1e41c004081194003800200c90382c0080721710400b5685450156203050040d52140050303e109030084920b15048100801081201d004007070302d00e406241490075082c5400c0003049442480d00b00300d2a60002030105110001002070300c08141c40d01802c1110500046009084680c2803102054400c0c8000c500040501044010701083c144080b4030b0b1300d000e2030000c1c041500040507000c4c034480c0c007403400555540c0659290b44010186844c0e03444251245c0096007020450078003510440b82c40b010300c4040a0080001c00d90500703070303071180b41c240b10080b0f03011115484940325030 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 748837257 1250 748836007 748836041
    0x71d01020c0904060e0717010e0a0b0a0518191719051602040906021e03010305190611180f0105210a02040b0406020303040c12050606040e030c1b0310 66
    0x24034010b141c0308038010b400600603400012840300c4a02002d1074001c0541024550240c14a4071500c0b644c0c09000c0d01e015030002078060031400300c032981e500650b20005005600d0301034684c4000759105249040106150195100b21002c0c2d100241d0740340420914034405a0b80017413402c001417070b1411000708640c621501d403009414406440341040b55190420303948042c64456980e02c1c4805a130300da000e503501aa0103510010303658088555038028040340724000074441c5009200400c0070410202c1d0f800a00c5c3c00803083c400c0071079010f140440003001d103171010125000001c190004405109554011404429200c1e000d4582d4080f0040d82c2c00c0c0580e20303180000013040d40110713a0440c8050445500044070300e0015060984900181c4c141c2c1d01700d0380107200107a10200800051042202c42140200750070009990622166120b0544441740104038034043c644031504034a00402c00c0040307600e07541e512401e0f9100c00d16158907044c131007000150614402d110383c0401d404401c1c214406c034881e00140e9415 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 748838507 1250 748837257 748837273
    0x50a0506160201180801020d0501051012180b040b0402040b0103050c0426010207050d0305011e14120303011215050702070302090a0f1a0102010e0f0c060705010b030a0b071d0102 78
    0x51511034181c4a4102e04020940600c42130007410010303c0d4000c1d00d2258000350f11180c814100b501140e0050b4480c03441009425109400c2c590401050b0b0521404180b02141940f4100e4140b0090b82800390010000580390040005020318035418a000c1c030320131a070a00005041030011810354030b007615100034012042004102c2d0b900f860501500d041074aa044c914080d10031b012044c22030700179260590390364100c0003101c04800d500d4813585026140d1304500a41001e64800302c0b0204121602510000080005400000f5910400344c40340e01e0b080780c8101c90f942d60f12002c401902201610302100c0345404800329081900103401030501ca021a640208000c514507000c01100041c0607000781c8919681d4400320380c1c07401a9009510340b40122041c0c026020304810002400c48540c00c40c4141c0a07000050702d0131a0380c00108a5078410101100c03c0b45c1c0b186050b042c000d004150400708a41d1610a2902d00707001c0100c1304112902c1004140c690350400c4034201a2800b5410801e80c04600607001080c0c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 748839757 1250 748838507 748838527
    0x117061308180109030b040309080d08040f0b0a18060c02190f020f1f020d1403070e090709090504050d09080f0705011b0618021003020c1207060e06130b01050a0506 72
    0x8502c0d03003900c81c1450034103000c0c0d0340c039180e074804000d054505500164401005111805040001c80880030541c0307428860345c07a00391142c4a01014800008102e81654400300b1010486601300c29408070003800d215000e8490b82c54140001c0c40011a845c01600613001044e40303c031002d13065000b000703400910048400c011030382040f01074141540d20541c00304000b0b20000c1f507003103074100d0f260101c0d4882e00140f40c44240d1001c00390013100800c0518844100070010030448581c0007040c5000b80a0999034100a82c80385282501c0311580742e0020121203145c04c0400c4107120b0009441102010151200c8001301c1d1100c0c640307a110034031511418202e501400d0208015440b611002c0922000c07900120402c090660712042030342d100c0c04c2d0420030401d0758918a810740c0b0740000350211424044c03c003103280099030050592a030034007a80c0300e20708c0d00d408241d40051140ea50444606d440c5904103503445841c1028400c10f441a0b56401903449270030b040008620b034100000b4440580d40001c000c1400e005003c4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 748841007 1250 748839757 748839787
    0x230417090d0b10410d0f051c0324060f0f180b030601030510080a0b130b01170f01060308032d01090b0111120f031e0117061308 56
    0x28020b0781060000f00d10020341030f19a1242130f1000c8103c0c426003060070342c03550fa4060340e0400007200d00489141344681c01859581d80e48850040030fa21440320b80d0744049500740941400b2a0f40d1041ca0700e0301c1400e8075144050f030f00d50b2106034000e41c44004003107034030031200540003440382900800c00892800801c0c80e15890080c080a00e084500c0e01e8643c2e4044800303c090003551038aa400340006400c040240051583c15019407640304110005c03115002d4a0a80151b41d00d10860b6030284c00b80c9801e00c0032038800050180c0d191071094110600d070182c1d595a03000131a04e80c00300c07000c1000a029403440d4041071441030082d0011242c01041050458980d0001496045284040c04c890f00c00350b60171814480515140c858000c224048002400c8640b0a001400000714cd9000209941000340d280441e1040c034416242d650b00304e90a680d49030344d104005884246a1b604031004070480d04400082d401d0b16a040d18003110004806031003241c1c603074015512403a00a01c8004200140902010981a0001c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 748842257 1250 748841007 748841011
    0x1f08030c150f040203121c02210a1116031101150e1303021b030f060702010501051c1a04030504081b1e011409010302210402030c060a051903230417090d0b 68
    0x8003920900340b605030f1010348109c0c0d000c03032883c46000031440c1441240c9006442e000c3c1d130000d4102c1081c02014070010044000b0700c142c0c1101c1d84075200d10350960302451f08c2045a50b1060525600810072941c7d25030001007403212a100b42840085440006030b440e507090040300b1022907042d0000c1043d8000580f81e40c00c0e0bc1c881b8060981c262081031444070228004109140c021400b41d00005625414601845001e203609068010400700000c0400001500c0360401034070b6148680c010314054441e8501102c035441164054011441141c0080c2e041c8009103585a0104404803021401e004000310520014540d04007098040341500301e1030500820780d90b0040140480501d0f0051909a5601c6911104201600f052030a203000808000850a04101c804460b4804480d403d0504491900084c001e100b501c0240502c00054407000300380c280282c02044075001181c6420030483c444c824071500d0341904642c01d4460046c6852014031040c1c0c0d0108482103554013505011102d2001c1d1601d1190401c0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 748843507 1250 748842257 748842277
    0x81e07051c050a0c150e0a03080304110303070b0a14061f090906081e06090703151e0504020a140d022103040605130506121f08030c150f04020312 64
    0xc2445520300180c2e003070006003400b41c42060300c008054101095034031134080c5004613030140407400040c60425555072041e01e08aa6108a80d1030352903503246008881241400090398040c4804039540c010030210304001da220307003401c5108000130545505101001c140544c3c899400ca080a0400e49410750a4100841102203504212034419641c1140400700c5003143d0000390190441001c8504107188400d01d00690507903000107181e03a080ca40041c43e1203a00e80c0c400200200300880b01c10f003042c0c1c1550000c2041a40c14042440520380d260003000141c40c04a400700e21550022001140f007201e581090740354014081d1802e07800580944c00d014005c010f0721020704d00c5038401380841468a80800c0240042c09059441d203171610203110f0140184025500041d2007100d00384400d000d80c802d800c01c0701d9401840941120221850725806041040d01c80c0c20070350f46400000ba207111a094001030307401554400a100c50025610121040311360300302914025410b41009050440e090a001c0c041c002c4441c1c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 748844757 1250 748843507 748843549
    0x41a0f070509150a0c030e0406030804120302150106030504060b090103050c040e031204030f020f030909192301180612080c1608070e060303031005240c010501081e0705 74
    0x42c40c00503c1e40e00e411191040f80000c0c115040340040540c80800b001e4003031000e640070320920341541e42d41d03030903030140e80101c60144008032820403d0620802c440242200d00801103846540c55a5008010f408100d805451040c10f0050762101810031005090480c0e40100c00b50556040c408108400740000d000034641e0740c44180041d04c00309180c0786049000314400c3d2203c000b5640703c000c0c041e00304413450202d031049400a0101c8121350310381072048d81c0c0c44510002e801c010b030642000c0640c01000d045d030342c56501d0701001d10140601008401c0702c0b41030b00c0380180e40c510a0300a1038030a500385d560a000321424101005000c2c0f00181014015101c1d891892094440205081c03060240040380750b4020011507201420030088440300440094000700d044e4040c51a5140055500404242d20321900e40280c41403811071342442d5103500d040326007190000d0020b944440711001c0a007c0e20080c0501641c0e8001c03505034028806c0700c41604400501000d000c1c0144500e0401040210210035007034000640d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 748846007 1250 748844757 748844779
    0xa09090c12050c07060509030304030c0305130905150a05120a081605061f06030b1014040504021602041802150c190302030703030e032b0e070806041a0f070509 70
    0x80781a01a26110f20f022000840d19503081c1c3c00c0400540f200900400203c0c0c00c200b0610000c00d80c0240485000b0350142003040ea15031340c1a103802c502c94555401031680c1031600e13051294101300e803e00c0b6440c01c40121000c8510540318070030050500c0003005d8001b41c5900010070b030030014007145e000c2c0800102d01c8078941c01034101c6449550400b80200c506020301c040b0b4003100d000720ba0541d58044007412052800300038032a503260120b10803040e0a01000184100c0320038258500010008907809482c3c00350095413225480c0e030b903031031000e07860110032407041e400c0c108a5844040200f00c64940075070020422508101404009030043d031005c0802e40c1e160041c50603095a081c00700e1140000c0905c02d900031969808907080c020100d44174000b801c0300f1900b08100000d1011701e034000603000c5070030907031061600070a00a03512006203110b13100131045020301031700041c44032004101d03d807182e405244150084201c4a60b00604c0c0e540440e410428016024082841c0c00e00c91030140c600c00300c0244c9103c11715 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 748847257 1250 748846007 748846037
    0xf0f071206150b04060323060103051906080d020f06150105250c14220f09170a0206010806010302012a020d080d0f090b010932070306050102030a09090c 67
    0x4842d5003040f8241c1c0b10000b001c01034294103200b00000e0700c0d000d4109000c222508070b008441c1210107000d250405480340007059070002d46003038852204144039401c00110380c1d2034802d13a48a00c084001040540a50800c4000d090000328a540c85041950f01c03440030154040c0066805400246024200b09a94014010f410700c03004e100518080c001d0f030042d08600d1030043c10400b2103240c07007605030040c1c03c0720002c130910100030111250380815440740840c0382c42c01d8210741c070000e0403803060140c003035890007000039000c16101009200007204c50b420395070261380310030555984032001c1c4402400102442103803070f040d006030750850460001c11004005a66000d80019007843c121000c141c07804400003a800880300a01c0c411401280c01d02c81d07040c40408116144c409074110140700744a5456125146864800c10707844983c0028510300c1801a2403040541c2c02e04101001114620040307803800d5000b184c990700001c140c40d60b40205640e1119458100707070070b8070083c0484544034001d101c03103200e0840c45 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 748848507 1250 748847257 748847291
    0x5180702031918060f12020d0221040204050f0c070b0a020c030d2a0e0d1106180102070e0f28062408190506030c040501080a050f0f071206 61
    0xa186443d50310042c1c0001c40301091010422154000818003400b40e001d03183c01904590358801340070741c0c3c403001a1030301c0709800d50074040d20624124401882c03250038480d0315020b003039903040d0241c0c1c000e44081025a03102c0c01d283c00300b003005072151265103605021172400102032010382640726038034040242c182124012400c2c03650f000b128100300015120b00d0080c0310b201c400006203040c0780540c82c050b8088160244050301340746104400900070100703040300c182403040c2030440064201014000560740e10110f41100b030f02d960351880003401030107010000550b0307218054441d03000d01c203181d00250840e150b00d604811036500044540b820050700410740e610282d9244214001452011081418012a004941035a8500111800a2155010921030502c10000350900560f9a8000000303040c1c8400300000d1900c1140c0445d150300500306000800c2400000c82c6218007544a0811951417003500b007183e0382c840000103141e68172039002e581e04019440403854141c220a015400000354588086201d0071 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 748849757 1250 748848507 748848547
    0x6041707021309050d03140c162a030c080304051e030a0b0a0618020a0e010507050307150e010c1409190305060a0204050a12050d05030c0c0f07140105040518070203 72
    0x20030380c008170a0f000b85035030107001321402003002c0c079035010440c80c284201103e01e0091011110380106010500c504210307102200454803c00c40c0c404603a10034038095041c0300c8c1c03602c0e8042114070500401e40010303065000005c4d10144c82000b02016050b48035030891040c5a541d03c544951b16100341d4100e2004a41d103000c1181c054802c10501180c414280300c10400c04041e03a1121513011441000014026070784111064544d441c2440c0680d038890107402c0051540c09884000741514051643c08060803d40c1c0c3d00c001500d101c1e510081c00300c201d0340e000694054000c031924000c0044208420529403a0078191408400d103000d5a11584036282c2c2c45c1c50745411411503075806003541c0020140002c0c40d041101200804024411144106281c1d0354691500c2e4294102c40a00c180400400e01d001e460100b910319888240701103d42c0030b13400b110380640d070751001e20400e00b051000c2c510440c4154850400ca0341a40e90150202c3d40244041c80780d0010000000c00c400b0841c08284240c051250010525038 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 748851007 1250 748849757 748849763
    0xf13060e010209100e030304050121051e0718030204020c071a0306011803170a09030501143c060103150905060316240207120308150306041707021309 66
    0x1600ca4080c43c0038091314038540911101400000710032940c1c0ca0341d002089805035007080c070708800c2c01008405a816101c07411070702d207041c150810b410815500040c0d130f5a0301d24120740901c1189d0644400700305a495100307102c140b0050703c84600051002d8240398008100d00c29500381182c0006568454490001340da858240128540000c03c1c44003560303001c0114a0ac6100400a00084c0d0707146558582070401188081545400042644d0000350f02482c070744401107400000078481105100c0d094003120f1002c445200000090070340c0ca128480e1015010b2051181b102c0880660428849890040200080c42c40c1d0400d42c480003107030031501c0081c003885c00034514110081002d007040010036041076450310401480c903004642c104846404607000714442c01d0550115041c91151a0b001c904100c16504039a1511000704024000c150380074030014420301d4600e80040200e040c3c0f40426454002c2907801400c584030b0080000000d410560040c58100d2006221340a0502c881305210190341c00d900b419 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 748852257 1250 748851007 748851011
    0xa170f07021e0a06030f060501050306091302041b08271e212817060310050c1e090102070513020c1608060a1b050a0c140d020d05070b0f13060e01 64
    0xd000346c130f040d8082c4201819007400c066085103032503404545000340c01040d10440028011095082d0b44566000d191024605000c04000e4400c5080240c9802c0050318038454502d07030511034550ba4145840440e140d5821040a0100341d0710b106865203101c2540054548d480c050140b03210100f1003041300c1c152040011444e000d8560030141014054003800c8200d4048110103000c0f2019120303803058260250391034030244003c454962501091a201064900d0154580303400140a0349080141c0034003455440d5189419a00c6003200c3c9038526402464000c90140c1d0010b1410300c12403a14600da50008040c0034001418407840c8058207190200c17013a40c0d405014a140c4050150360002d000d0785902480c50101401400c101304285000c1c0c0c03800800304800c116001c2042441c0c94400d40c17007005825040144807215140340807110303496884110018026110b40c150f01c3e22014050b1003a2070000303411a1a02040382c1d1080c54620003140700920103010750a00562070301c0056030502c14031880391644000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 748853507 1250 748852257 748852271
    0x161107080a0c06051204150e01090606140f060f1617120705090904030f030e070f0e0f0f011a070206031608010803091f02010209120a170f07021e0a0603 67
    0x90051a062500f200042080812500c80c40413030303405125410680c4030030784416030404180007400901030300c041c0c00000e50034022880180030032078201c101600c2880c60404008005207041043d10050045219048107090010742a00345116002c0c15010f210000d504000710100d9031072050761044218074090000d40803444104403500c01c054564003006c98208540344c001030707000260f4016030003030004080090b00711415881912030b030803441d03140441e5822a50003648800d80c0054001c3c250207003080501c0120300143c1c00d03040f1840c009000c1c030101d103030040d1980d003810f660110707110540c0e018105402c0d0411020700186c842400a6200e20718492109a40380c0c0807040040c0302c4034069226980c240c0c021b0040105d607aa826183c2035045040158440d40325600d4003040e400f9024942c0c9265200304100081000c098010410b5580e607440b030381c00f41c100107241000d090810300410104410000040c80300c2401800c2c04c0000c03107414003c8104000240d48000d0000e07911031010341110000a4507424 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 748854757 1250 748853507 748853513
    0x42105071b0b071407171b040b0109031b030804090e07150212090a15052104031b030c05030a051314091b120103080a170609161107080a 60
    0xe50301c400e2a014101c084400745054102049802100c9028100ca000c0d204489511001045864010300701c1c6120072095610b43d890300c9403250090070b0b003042000b0220260011510b8030b88900718030840161544c41d400750646e111848075a11501500151a8001c20048046440315029100410407000003160104051500901f802603d50140040460404440e944641c01040d0b01c42e011032441003e07a190b400150015084081ea68403580064440a8401172020b0380503000301581e224a10f0100c1c0c14140e44c542c21081c1080c225805030014200354661407000300002c412000701030080c50034000090b0151640ca095500500c00da02c085480007581840021030102010001d01e40016000000305078240855400d080c001c0a0204024070000c2024032440c82005540910f00003c8884d502582c482c036003c00c3c181d1058581c040410320702c81c50f0500c841c4200100c1e51090101400c01050f035190b02a040911641401c0ca8105201b80f0000e00890490200040f2001300403110042800744000c0c2 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 748856007 1250 748854757 748854773
    0x9040b090a051614010207150e1c030c030216121101270f08011a09060303120709050f040b030d05090303090409080a090b16080f09040507030b0a0506090f0904210507 73
    0x4c80404c0c15500306070000c1084102000c0c141292000c40c2c00c200441c3c03540c40000074904141442044406090001c101045c59803201400325420710a03003c590841005400d03810300702c0300501c900307019001900344081c0010300e81a100c18000106050035800c4110040000b000d200b00b101007281071664a03601040040346886011008003501c0008200500c1d80c1141d0340c0c60701e00e800414a00500745d00c00840d0054500300210703402001052071141407410801c00061034040315121707183c403c0411305403070103081c6410312a800c2c4800004008001e60a0719140c1641d958010302090740d4140014042d1002d241c40340e0080c1002c076440b03460003030f948210016000c2d00da10100d4008610080050000c070108402602d00d055a45801031401910740c0c01010b40b9884c00e2007001c54054005c0c0c10310081c002e82c242c041d000500e562408648007010235850301c05212040c00358114840d8403150740103402c00c2c20b08001400a410170300915460303180041405400444d03d110780c0c244000500002801401d0050030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 748857257 1250 748856007 748856039
    0x151d180f0106110c190509010306050709090b0d0b040309120b06120307170d1104080d031103130b060316180b01090e01090e0120040e090c09040b090a0516 68
    0x7410020000041c1c40c00d00e44e5a0b0001000050082c5d400120280c50342040c04a03820003014001c0440c0c4040d82c69241c080f0107014196015000b18103a2500495401590b01034045d01c104054041e0b411003205889140321014050810307801d01a5400d000b00304110380015500c4d07414060900c003a8541803d00c10301202c12803c600081043d00305000000000300300700310b05c080080b55051807a840b106880003030300003004e0131301648005050024000441e070401107685086240c0c3d58800304000e0303160f01802c00f124407040750f08081c0c2e1300c04d036807070800029100d280d00d0707800c00d601800311803900d007002c2603548481b5080e030840e0524112105001105440902991060417000c2c030f4191251441c164203da02c240060180b140d00136186d06183e10403403425880034040002902c812a4201034115482c50564040e00410550450250003e4001500042c10404094016006003400e6075903031140c00e80004050500d000c507010f06000750021900401000c25044a8401002d500a01e0841c00074428001 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 748858507 1250 748857257 748857269
    0x2070b0405090412050c010c0323040506010b07150507170a06060206010303052101030305091e06030c1c022a01141603061e08011401151d180f01 64
    0x1000140440d4070b403030341d03882c2d000781e400160043e54015a400a075414000d032118202c2640c6802d1070840d02d80e5241d0800314180a4008040c42c0303c41c244680e55a00001c122809410b940c00740004206010003080100030840c0610007512030b03038a42421040a880041e90305c04002851071010544022688101c150480030b83c5100700b000302d02d0120040d465402c1413001078140040800c88014000c29a407807080d2203000b00304045c149603140d28001e02503400070310131507000700303241148040340d12002c1103090b0f03000c00c0041c54a030075030f910704500d1460f40d03100c100e000c80c4101003841d01c9915443c1074006444805e0941c1ca0141b140301d01c4170020902194248051802e680c1800c82c81411032944004103500110312180c2216005000d41e81500a01841d03840560b0316169903000d0286081414003100c243e401007402840340203405070142c0d030028800c1c020500c4081c0d101c000320840e64010b040120703000703c803401107800800303114001900c007110100800c0920781c0a80b0811a80307120000095001d845 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 748859757 1250 748858507 748858529
    0x5011707080c010c06020d0c2f072105190201030b01080f0a0b150c060907121e03180b0c070e010b070b04170a05040e0f0f040809012703030207 63
    0x494a4400790b5a40c112000041c103004044101d00c2c14498035804031450500c2c0c0100c280180c0b646290003c1602c001b100c001c0e035a0b03132000101200013005500c01c150315054250300030a0b0050400007c010424129584082c818074203c2010001910078001e4032400e0050020443c120f0074940005419070b401e071424a4100110042000481034040b60180e401c484606400a41d40d4a14808500d604000012050915501082d0640c025100044e40c91141c0d05950030340701e041b0780d603040e01c01c090003220600034010812420608500c480340703080803034024028135110808003400b210022440c081e9170030038008a480001e442100403c20803c541c014800c200c016000ca40c981100141180607900d001042684000c01080c1407000000f00351503906030720b030303c502c0c3c0e0789400c084043d0076903006201d508803609040c00000c040a003001c651a02c074485000c44c06900b40d0f03540e42d0751800d0764040581241405000f105e408086c2c00c0300c81d0080d03604150b180106006030700f1420041e107800c00c10760180b14418 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 748861007 1250 748859757 748859759
    0x8040510021306051c050903040617040206070803040f0632010501050301091805030313020a1d06040207050a0b0405160b03042003071e0501080601080609060f030c0604080105011707 80
    0x4000c0c00042d04503038641c98a1622920300c150180c811240440d03212603158100414454184408002130085403515251118582c3c034498001d0700d031203400c9030013130350080301801080049000740b8019a4098498a138400c00f02c01d403030f03803044219414210400d02e0014107402d525030101d1400648864030080143c0034555624020000b402c1e071005003d0060040d40300d1102456400c0341868142a40360320400f0360f9101d141c0400b030100d00a400c14000d130321640d0b640e40d0019082e25014917601c521400e03500f00701001e035116000e10000c1d500c0303ca030441c0d83d48200c002c0791000c541e003030100501451003980508141c04000140070001800c3e034002c3c1e030403241c0401c144400120007049001082c0031140030a60034280320350000c0c0c2001015401700f85031800d00c101c2406100010a01c0d03000303562007602c410b51240c6401e00111021401100c0480e01f103005140803075414582202e0a0760380cde150040850f200c160803040858629001a44070084580d110300c0140031802e80620002d0740e082d41030004107402 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 748862257 1250 748861007 748861027
    0x150408070e091605011209081204020102011b090605031302060c15010906061b032307031202120a0b0f0d06060503240a18060911030d110c13020c06070804051002 71
    0x2c3d8a0601c00c09050000580160b4078880c4160001040f490308003072078a485207110083e60070400001c41d0103d005511b4040c46d20420901d400d121425954982d031001203003803c009040c0c840380d101030712401080650a90110059980c14002e042c030104c014091b00500c0c104210a408510301038002100c1141004010b0200d5903101d0601d05414034091001c000494250500359185010415040c84c0c01c440c541c8038a440121240042949521981d100d1805076a481c3c001c508074004d0000b580f80040041c00407034180850b0350805010420028000c20080e14500001041c1e1103484000304e548c1d0303884080400c1103203403d00a910740e510045501501c00d820f0340403e05201c9800404c00507600d42e0790700900c204a1000ea131030b00e050079407043c0304200c921740c00d043c5114005030144500b40709205074024410464401c0702c3c2580d040c43c4010040c002c1e400c2d10310821880c00c049403260300a155003804a0012008208240d6000e208a0389840b0001d08203428a00d0a048040405243d981d00400200c0b0030 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 748863507 1250 748862257 748862293
    0x7080d0f0f0e0a020f0a030210020a1202070e07030c020c130609050105090105060a080403020c15071101030b03030a03020a020a150506030706030207261e0901020106050d0807020d02150408070e09 86
    0x40c190b411915942c905c010303180000c01c003580f160000f9410a507480d00000325903800207008580d0501a61560740e120880740c508a0b80d8820a008001402000c9004145214000d40250b92260603500650b00f01a00d10804a50f6804c00110402c00e4581c881c0e804111030041c1d442000d026000a80c0c00440c03540c103101c0403a40d540b040c0041a02007100410000b070605200b4003010401440041c820329a03010f100a881b04103800940c01901e06611558825146d903010303109620390000090051407c1055416080d402074001f000070300254007a450240000809010744800365a401d1800096141004001c0c546081c1041c2c000b401418410411840443c2040591511301d00d01030a03a4190f03d0005034031038803075004a000c1e200c444e1190303c400c3c1ca030400106000c0e252141003a4000c110280e9584200800b034100c489000d8101c41c410401c5c3c0015003480d1030441d08090010b04405840c0340d841c00400d0351039011350300800d03d03900940380c11b00101640d40c19140e0000c50220092640c060440c030350b503003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 748864757 1250 748863507 748863523
    0x506030a0209130c0605190f0f26010801060e070801030803060d1e03080a0e150417071202010519050402060d0509011b0c02120106030b070e010507080d0f0f0e 70
    0x300c16010030b4001014038000c00d0415901903030010441151540e221006805070300546941412041c3c040c41200700303148280e0240402164950f038501c03180d15050400e0394000c401100d4410341c1500c068400701d20007054104d882c0205103000001940303d241c000e1026080b000600500e08000a0400402c081099007040da500888125040301c800cbc00c0758900b0180c010500920300101006110f0045c05040c1c004014910801c44824140100c001d02035006441e01ca00d1082926104510000b09010500030104c041d16040401134151030f00c0c5407910303404100e1707030480c2101c00140c1d102c2e0200507201a15450b40c900700d0f01018014400c90500e3390008500f8040d03002c0f1441c1042e6079030005112136030250440d00b521004039515200642000c88014664200c41c5000c2c0d0280100c10f8220410074014071032181107030b0704941710101540f5907550440c3c0b182200180d5034100502403110701c000c59000707130040c104411001c60024070340989001010030340b03092a101c040d10b2803401110015a080c007103070843c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 748866007 1250 748864757 748864759
    0x16030209060f0919090203092e09050c090907060e040203060114071119030201021203040b01050909100f0b030c191a1908041e0f0b0603100f0b0f01030506030a02 71
    0x15841d03c0007400854a80c0c101d411198544100303079000001c018040343c0c0158041e0303005c91705650b403403001002001004107203020803903003d018061000304551901c0d8085c5020500c00c00c1580e240100c0f80c40095540e1106690035100b6400030300e0100003098010300f0b80c01d00d12205076020f5085180007000a00000140c001d918891400050018204134110b1218084884000e060a140400704a0f510700b00a2907800200d003d4410040040c100030000c200b602e22440d803000d00300300c0d031380c2c01c24080c01064040a40100303e00d01c00c4000047d995201070041940c0310b141c0200029044282c402003600d07280003500f150340689410f0128400c10354105000c5015101c002211580541001c190032a81d446240c2080c042d0710007040c405402e10303601822041c0940e0058160344401280401d0100140b03c0e41c100c010000800c0d561040700250800c501b542d0302000080640380c1c41c0d00080c0460040da002c40d00c5449800380e40e00c004146c1c43c580021030802801003860100160b03d0450701181d5100e08584001e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 748867257 1250 748866007 748866037
    0x613050604030f0e090108031801020601030c090902131407090e06030a06051b0d020706140f04020f0d0609050c0a0801020a120e031b0610120209040b071211031603020906 75
    0x200034103d000780b04c1381e0b42c40c0c007014000b211030f5a5a00c1c1d445840e40c200680090244800305020b6601d9880010039606803604040e203005854035102610009107107810040341c00011008010040040c144150010010b04180e40d04252519032320050080b0344d40d170000ca12070521582440980d450004810800b5035000000040a0700d58001d1049140017030751494014801c002094001ca00c0d10380c018052407441030320700340f1240c1c240c030090200f4000f080b10300c54030032207034400040d000d4036024802d0b036110040504a00c44040013a1248411380d40e0011098500381d0120350310032420300700002804007c1810f00e00860400302119001041d020303803030400041146d120401c00848071414411a0309034607440030700500c800001c188960310b0394070413520154001c802d510000780e903802c00c640149803541d004041240d2a42c9541c0ca00132884e00240102c001c00424000300311011421340701c0c000152040c0c0c41c5450f143e10702a5030025681035600950010580144802601c130341f80d0340d00385e07910701c3c01241c3c0b0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 748868507 1250 748867257 748867277
    0x320030d0201020a1b1106180906120a1101020f03042706061413030b0a1e0b03031b0c0402040f0905100b191e0302090f040c0905091e190c0309020109260105090d02061305060403 78
    0x101d103007059038040c080d40340c003001600043d940a42e4f0349542042e641c441c06051609600c02c1d0b410708440151241d04003080f1100d07a0402d90001d4000100010f0320003401c1615601c0e1281c0719224185e01c00c95140083c165180d40c00b884039008107403200490101008140004050301e40070a489014401460070f003190300c2c2c00c080c2c01d00c1400740b114a483d054007030411500c46545003408840261184548201a85060080740180310761103a42c03402d444410035a1850088450314074002071050100e43c5040001124040044003842c907120a034500c402c1d0303801f603207802c3d25008100d414030414444e2441203207092941c80100d90000203a00c21204115a100c0d1260381380000001755942001c5014800c1a04600b04065007030300c1030445849669041e010000000b80300e0f000d8040740d000c0500a8041600e0690410505c01c102d00d1206030481204000c0c031020586802d1117003910419103115080d5007200b2204815141c4c100f002640c06038150340c07144014101c42d1500c44d201c0c080900050108119421 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 748869757 1250 748868507 748868509
    0xc04050409031403070827120f0d060605030a110310090c050705160609091e020a02030c0f0a03140a09030b0705040320030d0201020a1b1106180906120a11 68
    0x20010f000d400e03000c1c81c941e5a40b400240040c0100d404446140495a50f01e41400134007005008094211240800804c1865410080348803150000d50480404000420904142e107140f8069440100b00548425807a401c9c824a501c0c2510041d0503c4503000000740704100b44c2c05200800c00c012111860700005602000c1481203c480c40b41d034070094010702c41e5060815005840c040b0090440b1260740c1e4040160780c8038039030082503c518186207030b00b45c0c032110043c0e624000542d00038101c480c003a00403240b410913140c20407814400d619240040c3c50300500058030034550082d6100030307801400c070781103858865044800382c01400940000b80007250200d0020303560b13074000d0381103402540d00440b00c4100b02e4169200900d940858446050107401030b500e44512240c014000c0d50440c450b0fa0b01d0b044005100c001840019803c00c00701a50b03050a545062401601c0707071801800035503034601003c0360b100f5024007803100c4480003030301c60350042800b440b00c0b540a0703c02040d03503500c4660250b820204a81004 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 748871007 1250 748869757 748869767
    0x1401021f09081b060a14060d02040c200309040c030905071406120c03070314150d0609080c21091008180601170106080c09041b0b03040f060b090c0405040903 69
    0x49403c012001200291041842c00501644150001d12003880710a000c5101c5040368401522500e4001c09050520030061415030050345056655140002614101426071040c800e448001c1081e0b079000000d1000182c1001d0158422502850400b4042c0c14120750ba401d5071440103200790581c056425025401991b6000704807001c3c8840c002c214481030404800c050304a0380207039101400f00c5d20308820f246c0e40d1507070382ca02903220303000804c2000015400e07507052007084002d0800072116159a290700b00c0025040c00040e0000e001b05034010b00f8501d90303800c07442d80490701580c40c00444480c1030148d503216a643e01c103454031014442c03404100700d46851340400350300e1220a00c6112a0f014000c00812035004601c807400401c20200024481207a840100035141c024485005801404400000d0003003054905213a9481d00111103a110a40d40e0750700c441210740064030210380401c4881200d000340703e00c80c050514650b00440d000b00c00ca0404c03682e40c0c25a0310a51280d9801144c4985141c030515000d0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 748872257 1250 748871007 748871017
    0x3041809080706060e060a030b15040213080c0a1a0d0b0f1305060a170a0210050c011401050a06020d09210203031b0d020d1d0a0302030a0b011401021f0908 68
    0x1180c003075190780d40ba10344070004d001e41e4001c29607070180c0203000440078900702500388112500660f6401058650b81e507480e140b0140300c98643e800c40d80800001c14601d0342405990014082c6201900030070310410104a0f100c0e400d40d000880c2e02e1415140b003000010560121041000c41c1a00029440e41d10004a4132101c000316880d94440a2621011014001038100368805c02007123903840145521a821a0f5100402191000b81036104044220060814090565400c021410910300b000d0711207100a00f034841e80807051500722402801000242041d00741c81c00504004c0c000f4000c40d04151070700603d6820325103c1d142c803061000626241101242c0d030354a4029801900742c990314000221100c02e10807020355015540e10407a0510341041c2e101182c8264080003d65030864034190501c1d100710244410b0320b15075400030f0b02d0100000181d50420200da10316106a190308080c0d13161508000361090030f56440c0e0b0664100307088040503504000000458503d03042c1c0c000906001c84d0504004c54011 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 748873507 1250 748872257 748872263
    0x1022118010c2009010614040504090c030b16020d030b010f0806010302040911030916060807031a0607060507080a06060c0212010f0e21160b1503010c09050f0d0503041809 75
    0x600d0443d00e09107039070082498601c4001e803459880303640d8480c0111383c1040d229010244020007480107004614240e0042d04119002d404004847ca407a5280d01c0041042501c104007444e180414424003960180a401c05107c924141046407031320072800139040c103c1800b011030400070030744002040c40c0e00960540340908145c440170840803940da241110706a000340c80b030b5511071040d4900145c0034071006000d0002da030710380d59491140d03407540c00c03098020744075800c0c000d0401e2807400481c00c07003a282c107000392621768014a80800d050601c20304c083c0003004007414030a400c40c1061410301880360081c074101c032041da046c1d07084100c8043e4001118010800009248403503410400c44140240c00040d10b4115560001c01c650076691442c0d081001611804a04070707280000d1800c0c0c040819800500503034450180c40050200400e0680000d00b1a0304081c200000b041000106016509140101e000400e4040d900801c1181c038548409946e40514455094488403180c912458050b05400900322268 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 748874757 1250 748873507 748873523
    0x17010e0414061f0504050c1909030807030c02010e030c06160305300906012115240f05180403091503140a020304020a290705030901022118010c 63
    0x10300c4049500c03c14003042480031020000f1074042003500d01841514082d103071300c0a14901c1c05a568120700300381348502058070280a20401d002011580090007000d41ca1f100c2d58486526115510024050a51071402d040c02903100f07149503041611500102c1c0e0404100300d2107024041c0c03083c40c040b00e00e8810310f00d00d2101207181100f0806002e05c482d4071000152080c2000070495034840d01401d0380ca04003445420408003c4c5517006441a6103a80c1481001d030142d42d0903440b02901c00e001ca0251014a8085500c03031050f00c840400c09081c50304da200203441c00034640410185400c3c0040c04034888940d48501140b0104003143c10107020f81f20482c002c0003d985c8001e00890070540c0600104515107820103100712500c0003440e009814401c5130701c2103078004c1c00341d07880c00d00b03044890f510034600141400c40035644026100000480300e02a010f42403060f0000c51b0750f000b2510009080c6010000d221a1001d405180414403104020035116940c0424a80054840c000e40040b03540307030000d07040908a10 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 748876007 1250 748874757 748874761
    0xf02150d1401170a12121407080a0605060f03011e030f0503070b0711100509010b0d06090510140406020304170c010e2b081503010c051917010e041406 66
    0x4100c070107181200d420b075102ca060b800c80c06184584510740d80030028441118894000500c50080e01303940c00800082d100054441003192544111804c00c0c0ca0103000301c0c404404010001449000d140080d003020340d0400c0c2440105038080ba050302040c040c541803040c251851011408110380f030000119003140c0a519403560751305006803250700c04481611110b410314005140c3c94020b03807080300d00131500c8008101310301103440090000c280103840401c4554030790b900b081c00707559154026801203011741c0001072001081d1a00f40d203817458004040b40c1c0e0070700307060656004103185826071b40d209030040809a60ba0b6a5450800800000c914001280c40c001140b00900c2d54415408515141480c00c100d80c3c0600616003030542110024808148003032680d003034413440d41e10030306910f9001001c2c0745d08420708a644400090950344100e814100040e0042005030010b40c075003039080c0c5103070040c0c1000805d0000704420488840e4050040c01174112410020400300001c4426400c1d1401086064030361074 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 748877257 1250 748876007 748876031
    0x319050d090b0126011104090906090b011503050f1303050a02120304060605030609120a050922020717031003060b1305090106050f0405060604061b080d15080a0f02150d 74
    0x100c002410305240c80d440504d090624038505208422030a1001d03030f80d0909080c07034034105401030034501004450741921000c0c1c0344001601d03074550318044c1202a1040300403107030011005084820050841c5403079040e61080c84515208001c1180c0f100d0381601d03205959907440e01c0240e1505031091800909028004200400c1c4035641d441003082c2d40f402c80c240c4506031202102c0b19038540c007004415014030420445544000d02400c01450401009882107803136207860788900b42c100811107407844029400117001c03820001c030000350b0040002c200358554110300380130959055045a030b00004156a0b81c1c3c0414000a0362008000c0c021000b445105201d1031400301d9215028003854480c02c0d000d4010140448240e00d45030180078031a24010308400d042134540081100c515508020341c00c1382070881036407000071403440390080c00208102640400d4079403a002030300b15052030b16441000c3c103800c9031105034002180003010300c1c00309804417603c018441e01111034105520078140807074002d03854110300d1508 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 748878507 1250 748877257 748877279
    0xd030f110d021c0201052809050a050f0c0108071b080405031f050c16230307080a1e0c03031e02220504020c100c032909090319050d090b01 61
    0x800c44100312029004078800d406a085e60380c2034a014510701c15806038801f084205880808001c2d001a0f400705905555071a4a41802050b06c000d44442d0881c5880074204d80040140c0d20203070b80c0a103801e540380d150030200140090b031200310b90004110610050410b0011800a40f005404024140d454010620f4000e03140350050705a00d003c0c541c200400602155050b200b40c4d501c89801203c01280311456658081c000560080004403400320784480280c0420200080c4c9070039132155054940d6070049400c0646a5100084014820200380c1c07510f0481a13480700494000c913516007004071703808004000000540405040c52007c003840819020202c0c09051058901d080814401100554035842030005a2256103403800703542e40310448020520b0901e80c000c990002c080e180014600d4001c1d01c2c4041008101d016841c410780c03151414045910f0258920342d000300c0c100004510f800e181e40780f41c2080d184650071020034010086003103c2c1000c0145c0210000da41e00c141c1300166580c44000e035200e = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 748879757 1250 748878507 748878523
    0x30813050a3003110f0f041505030a0f05190b04141030080a030207060203010b03040b1501080105041e020403030504180605010c02100c1202031c0b0d030f110d02 71
    0x800e034401c08141e0040b038080c0c0705488006124843c02440c0004840d402c0e84c03130b540135605a8040d140d0400c8000340045220b44900900304265942e99640d00f402c0c20390742c003542c01c02c0c40481c01861401c0309101407211a40f0400740e40400d080030215090515200080040010700c00301d620070540402003041c5141001e00c1101550421844e4840014a80c3c0e42e0f10b071503603a49034000e0415149a205030f00410410303000307044081c0c161318000d4079011840d540c14040e60020782c42a0380d540b4005c02488104610000c80036440000c00760013240c503c0640000829044041c03050307501079a9039a410701c1d07400448081107000c1004c404c000750b580e035640f450000c0c07076923101d803080352148000d0040b41c080c260001e001e5482191070503901d141f84d081c00c0d5000c204601c002e00e41c0442c1440041004000028401030000703c1c03608654029584603612401c0d04281d801021040c1d80c0f6240c60300501d50382c0390796620100380091750981b900041203007a1040c180c03800800600075040030700c0b83c01003075540d072980000c52503 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 748881007 1250 748879757 748879823
    0x140112020706052e050d02060309070f1d06190b03090106030f1202120307020303160309120801030b1008030d2309010b0f0117150118061d090103030813050a 69
    0x11309034252115145820303031641c1c058554400061042400540f908002030342d048620310341a5000e050355082124071040c610f0f800907445581c519070188681c6101605903902c0441910b448030035442228050158142ca030041d40c00303041d80400440c0f86900c09600401c003440d4070218060155015007481240f850000141e20010310540042c01d542c0c940980c141d074007540143c1c00450542e119071251040760001250780e58209540c1d00084230202d00c036041d9018840d04c40d51620066541942001c0e80c4c0d0100c020030703400c825075016008018403030700081190700544424200154105088150342030a0403000d403c425611101c2d0240040084190f0041f51310b01c030103c41c0040b00303203413400040da0b5000b038a01d1403001a901040020740940b1410104030745245051508ca40c0b03442d070380c40c407240074409140c201800040e0f446126503001050003510350890107040381c02d800700d5859590300400b400e0b00180401c0d6040d003101c42000030024104044140c113680142d01c041802e400c0e0450503001e90f800010701e = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 748882257 1250 748881007 748881061
    0xf0516030b1006090e130f0206030f04060c030605010210150509040c06110a030807180510020c0109050f0303071506080703060507030c0309050c12030c0601080607020d02030414011202070605 84
    0xd8814010041c1100300c441400c45021946da030314405c03a03819210100281c0344030020400380c00040e640d00c0001c1d0b120340c88900a0b50032500f49410484208c030f030148544000d052408206010790b030380025011401c440b4031100811031212001c803030b0003031600c16031041d43c0040003807082c401004900b64050050703c1c0e4680d21101e0007685000d0090b81c0e07440b043d0002c2d011a00107804110020b2048219400c50310b80ca00e40100e0b101d642c0c03404103a41c07404016280005030071403504040c1d150b80c40807c900080c1802c0360710080c100e9070f03840040d4503889111001401c0d140b0044c02c050072981aa044517005047c401c084c0e940440d03881c2444400707400b0031a45500040d141c003401c081018043d1140000460f0080020044044414113119400b4200010341c1c410788005e0081d1000003204104442c040e00264000c0c20351824035040207450b00a4489101d015034200b804184602420303184000f450100c2482c2a020745039801d00004000e12500e44040d007000e081000b0440d1031a00f80c1d0150b280201e2100c03070 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 748883507 1250 748882257 748882259
    0xe010f0902150f0f0a0201022101140604181517060403030c0c0b04020913210e0105040806071b06050907050a050a03020a150521010503010f06120f0516030b10 70
    0x584050f48551034040d03a03108428031841c0c0078480d500010303111100c8103000051400d148078640e214400c0c02400d440303d403401c0707440040c0a104194406da501820003562001c3c14207050403040b03180d001c80c1d6000036000c1e45d076640c00c030300b065810701c1e0603003009004c078401c1010758005486015850340c8045405a020038188007e186140303200e00c96601c10341c4d40080b00782c07190341c03296400c010f01804090440c446c03a8420504410107e4400c030003e803564007004d1030040b0820a0031201a2521107100304450500005020800004002283c800d038003461a00e421712a500000100548002140c0c1028014900c0c010800c031714441e0025018003603407021690802c00598031000c02c80c6402032400b0094000e40701c02010029401c011444030030580c207500b441401d02c1c44641d41c179191031901d600740e8030168664000400007824288505258482c0c2040148000c40c02c12003c0290303844005030082070320702c61400c6942400024401d504841840c0705581a803030340d40e801c040d5140841514400c0303a60140c800 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 748884757 1250 748883507 748883539
    0x708060604080309010c0206040b27030a12030903170406140a0b06071b0e10061101021201050609030f10020d0e0a02030d0c060b04140a0c11060612010e010f0902 71
    0x161021210103100031884d00f41802c00441d074408a0103001ca801640611000c5801412000900106a56104031203900c0210221a0f4a0754080101c5a4042d4000c40168400702d00b490500109080b01802c0114440e0103528003120441540d4a200e4182401d43d03041c8820440c0d5508440d0089d0900c03400b003101d603114200081d044403040d040c038540c0a5420010800001c403526101d41c14152022034200400741c0e1b031382c0f0000100204544040340c094803540c06000031a042401da15107207031004003c504108141980001058040c01040c2c803498011a03540d459940c00c005200300802400207440300b40c0411014a03010b50014542580c240c4d081c13541c201004200050107052036900203000f0002c8140c403000075a80a1225001911155180c1114001da03407914081c0007146900c48803690054500601038104440015282000704210903140c20640b50b00003441c1504004100ca2045040d0b1044900900510000c892000e03e5405c0c1078400350b44480d2a070040c0801d500a4030320001c2c19145003 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 748886007 1250 748884757 748884769
    0xa030503042907110a0804080c18010f0b09031e06090706080903040b30040c080303090c060d020903060c0304023307020112050f15031515030a0b01080105070806 71
    0x101c4820b850120710800500a184034441c60350806080b8030542d0b0b610400c5844036442a80190003c03041e56100a0040e40e06007002480c00d02440c520382010304055041c00c0c3e106103024090310030315103a04004540450b00d56010700c1314030b001400d01c0301600c11811a84034071503140c1c030003100c001105001d9450001001c9000d41c0300c241c4929403840c051498035007000c0d240120b940102400c24104523440035010092603032110881c2804190360485d000520342494502010310f601d4200b00403a07003080c0140061380d400080e058071070b80c1d8100c403895210401360750700318024000c80560683c907100c0c20051040c500b01c14001140601e00a40d41c0c440c98008501210f07c44805408075401c06003217a06480449005a101030f061584c4145080c80e01203091032241c50070b031882914408011302038081070144c0ea10504200404130001135014200090380c4021518148800800c40e001c80c4100001d541c2d4070760350506c0401c03001640009038604550311400018001e15003114100d01003080302c808202c0e00d2503c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 748887257 1250 748886007 748886063
    0x40e0d0f050901080609040819081005180609060f03030a050316091a0c070e07020303151c030c080708040b030a051003080436020c0c040506011e050403050a03050304 73
    0x1a10b65050350740f11a0240065100024000e8807108e009102d11951850b100b400d603202180320303a450030540d01382000c10010102e0346500c8035100741030034800c00510407502140b00394400c004075050455981c039003020602c0d83e41d1002c4087d5160000250341d4450075004000385000e00002168515004450700080d14a40e0040c01060703110440304001c601500a0100200607042c4007405031042c02d940c0da0081040310030140c88070780240c1c001004106061100c0c00500903a1003080f43c1d120404400c00a0000100b244041c0140401840e801d098080c400c9500031903844690200001c5e07a40c035510807061006400680d40c0c601c2442c10200440e6500d038070b05050109072500030208500d4140f500103141c581d1121010a800d03415100b1000d00080000e225400d01c1d6010591005a90b81c03e42c0e0001c14103000000380070718491850a0140083c503648488860b120312142c111100780d0020b8907006840a00441c2e100a0107481b50555000c10503034004090f60080b0300c01d00d120701034154030072050b880552203 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 748888507 1250 748887257 748887259
    0x60a0302031c0e0604061710030309120507050306040302010c11031309050a090b190c022a03070b13090f02030412050a03061805043806010e040e0d0f0509 68
    0x800710300b001482e0a0080c19507050320042c1804215074070400041545508640e2004011406040340440c01540d82240a9808040000c0110b425411654090b102c42c1440c01510514180143c8030380c01c1000400400b80507000c01003c5070b20030720b800d00c0c0c0240a031104c03041c000006051171584003c480030020a8800450750000380d20b08403814014800000c010003410700da1102e899108900c00303d00340184150146841c085050241e400110151b81950903048141045501407403002c1c1064404072040c0000101c8407500401e8142035a00191070244d10b81c008840c00c0c20300060024803010405125801c0325103241042c002101038241c681c00300e000440d009001490052107511034103204500404400403e401c001880c5510f480540360b000501200004009a5a809210920801c080a10710082000892195070051100b8075140d4100c000107a003c19012000440c80c643e000d0080c4d0008410060310412040c18130000036642c881207000d0000100d45440c11142c18584264111050008 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 748889757 1250 748888507 748888513
    0x10020a020f0d05091e220c0c052508030301081c05121801060b040e06090a0905031204030e040c0302071202030a090e1519150c170d060f09090b060a030203 68
    0x3403100e0170302c43d0103544640e503000c8007002c3c080882c18903076512440749900752001c1400139840c4201950003045450740400f45042c04a18048140010380000ea11041c05503000264191444624211500d2403802e40006c0c1c41030001200214541c03000190b000c02e18014404c40c1e01050a8460094441c2d208008a070b0f640e041200c4002103a2019084120410042203000011070b40d658100e42611600640c01190009040c0c0044c0b01c001e140c229102d5400080e507103000c00c07401209944450743c80c071883ca0300e0b07480000b10400040c28180610760303a09681ca07016200340300b4021907840007002980a040304817901c03d01c50040703148080c80002a81c0c0c8181241c0c4824030428140180c4054140c2c1c000c24044005800d00b404d00220382f00d084070304600850030743c03000748017900b45820316100307005080d4044100903521084001040240b0003404039400003280459a44001715402000f42007550091480030031840000581442164031002100e400744108415989805080006d40100340c403001c0e41c940c1c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 748891007 1250 748889757 748889767
    0x806090403090e0601020f0d050a090b12070c060902031905010510060f11010e250b0703081302010e031f0f061401300b0a06030209031005090f10020a020f0d05 70
    0x40703d1420007600404140116100340911560880c0391800c1c20340383c0380c000f031004194442c4041e008407003840900080b42510741041112418100c02030001041c10b03040006a01811092103030a6001c034080c01d4015058400842c64a417102683c00000391040b5241d6103000c00050140100010034016070301581d81d075142e458074043e8122400c481c201c628a1880d50788200401f9450400c000c0700200780c40d101c1000007005540e00c5450261412a4400383c1400006c0124400003a400300809030310270203503a140c10380d5642c1400100c8214812020583d003610890f0b1800085c60113180c44c0091440c8861300500450039410070342c40503132701c061040c00b40e44512805400710301d43c0600a00316040c90101d059407007841220350603084058660f010091900c0e030714825082c8506000382041c0c0981001e0400358030f0a4859000f0a035a08800c018940c40b065603040458100003052000301c00c00388020302142d21302044a03004000a40c444500c80303015100d00c02d4031030f4203040d01082c085100421601d91038100 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 748892257 1250 748891007 748891019
    0x906030613031101240501200304120f05030318010b040e061801200408010b06030f1303091203120b0901320a0303020f060a0b0a06050708070501020a0f080609040309 73
    0x60003488850300f45552244254450015201030201c00b44104042003000245010000741c04c803040741046900f8441001c400c0c0c0c0710240300200f150215415032072a08001c07009801d200304090a00301e0f004107580400428000030302c04403169088000139190080120b18803460800c41240d18070f05208046800250020305070300f9284511908888000001045a00946811311061301c00c01c1c95210200c1c1c401b0a00f0f00c41c02500f4440d4402180e003d44d40c941c035604048520084046000300044202419094070804240c460081d880080042d15480301d80c1c03d0341444c000d480d43c18414280300d4041e10341404600305141403000355040391210201a05c000c1d02040009804003060042c6540c0641d648190704041d4980d44070903c000d50083d07016000310720300c19402c1c1d41011400391440071842e0900740450f036907a0310041054103d5241c0d00f4015615000da1400a8490281e00e10141295102140d120a800c0d08181000e5050812355030f040d0349a0745080c200444540c003500c2c0a400200c42c01018001 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 748893507 1250 748892257 748892267
    0x16120e070603050604151d09190602070c030b0c0c011b0e0603091903030225020f0f01020a06050a020910020102030c07060b0d061a03330403050c0105040809090603061303 75
    0x81c02c09400490458100d1141d00302c17003080d1b0303403115641c6001c00d488903803403002c2002c4250304420420040e0200b00c8600601d2949c0700705c1143c1c042c040c81d900250349810020003000d400000d5900402c00000703883c01002180094103d00701d003144030350038102d8501d41380c0b400082d6002400e03200e458090018001d0700c00d024560b000100241986d00c00c1141413206c440d280851005011310039500542e44450141010080d440811216048801120040c1006a03510308444c000c00304150303007006107045141c00403490150513400c090b050345d1800050100c0151260010803205a058884a0341c0c1c0394050707812400c03480100e0321492007000a000103000600a03410048105500400000c0b0f103405c90784454bc00c42d0701042c441c91500710721040e01340b060f050901405800c4044401001c1390704007081130410380d20080d20310810412010350009030070140290103444c3e180071460000c101030302d041c2c0341c40c5140703510402e40f107482500f0540c0000d92a14001810034804c4615201141c02e1107841e54040d99 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 748894757 1250 748893507 748893511
    0x305060a120f02040b1009090c05040b031501080f041a18010c0801080115050a0314070b16030311041d062805190b0a141216120e07060305 61
    0x64005204440003400e4540d01c010510202e0150000d20a4101c480c81080201c50000d400d50307010380d84079481245841d41041e0200116581000b0100300081d04901c100c89922454119003c864404001e0028041980c023200094039001c1e2500c02480d266484110b8204208480040c20102c91807074240410035105420380d00811000000002401e00c0e1400782c0c251001d00440c1d1001420140042001e55824090711b181600120391206c0004e04143c081703664130185000141c045441e607a5418203a80c400c1240d07030010501846105d403980d04d100c405902441902c1400d070f00007801c00f0700200710040010210784c1103403038030507014100102c000c500c1c0200d118010b108076804010314170820b041ca20f0144140900c0690381c00880c003224203103410401c5124525000c0804104441401e02c415001c03070b42103c000303503001e06103194100007140800c40d00b0301c03503501c3d01411089448148084032101e050003480c640c2c038a407104088035031450900000c9440c249140302c41903101420400c80a4000c0c1e05c029 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 748896007 1250 748894757 748894759
    0x17100503070b0d1104051c03030f140a1b0c2904150506030706050720040f271214070204020a08070e12070b0d0e03040308040312050c060f060d050d08070207090e0d030506 75
    0x114034000d80c1240c51003121072083e02f07241286900002c02c0781c0911180710310a0080e04c00d0700b5140d00c4200700c02c00140320100010b0001c1014118840008001800060104117054070548288451409240001034000c401200400703003418440071890710310b00840da61301524140eaa8403404c20205445980c1000d9801c3c2084850a0a408007080381e61140d010b14008011948404034034040e4880044008154550321501c0100f8101141c0002550aa8040326180038501c0c042a914441a401301303028451850020f60080c80010703921250354201c440e8a20504030303a1540c42d011784411042c0480c080e82c20740281105d0b00084000d016001c1140054400d0004030786001900b003540e1583d09140d0b50041c0c20603902c00d01d02140400411589079003140101103203142c0030707050150304182c4a6503040054140d10071000c1d9100010603984031900e04a0825410208443c40800d44620203406281c0c10b492010050142c01c0300800c9003007450241c94221840d041c018011941400c1040300204400f800c12 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 748897257 1250 748896007 748896011
    0x60424090201020a03360612060506180102100c020c0f091905180109051c1103070b1509150907090303050412020f030a060b01080a0b0117100503070b0d1104051c0303 73
    0x4000540f841c486c2d000c5032070522140e5000c1031750600001510700d024203106030035805e04084080c0403a4a42c0401d0310328003001c807001040c4003105140140d0030702e000c42d03141d8a03000345406804e064099000a030032800351026201c010105040c0014410401021200c3c00d00035400c641901c0741d001060360005034030812a09180b02c00064a48002e0300b0b4901c0704d0000c0e0b03200c3e03000080729030740c2e4414588800031621150074420f1150500d01601501c034040c1d040090840200c003000111070745610001034112040041c410745030341c5807079001001c4e5024070060b114042c02c51800080c003a5400740000c1c0e070540c3d0301515141d04061610f081e0440d504940c1000326040890344510280310745003000611025807240b48041a02c50b0904001001044020414413219050001049071382e40c0090314100141400701c403400e441d6490390456030121080b030380305e5034141c45124000901c030604007000d0a4418000720090002d403081002a80c103e0190340240c0c0e80c000310486031449900c09944089280e140329083c0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 748898507 1250 748897257 748897307
    0x31704080d0e0a120f0506090610090c022b090501030e0a020d0503040905040b01060e013b120a110405040c0b1c1107021c1104020714060424090201020a03 68
    0xe04c1540014103021106841030002080070444140010b91b4030600d050300070484d40c540440c000e840c10405203c0e0510240c0c3c0c54080700160f40c0300b80015201502031040103041c42c009482642d40345421450030700c0009502d5040410150300c0b0b40030b82c0b510728080d440148001540b0343c00300400b84010400c201c0f1684410040050064603070700a0380c0c416405031402ca1070f20340c905240a040700190000982c101f00100c503044413100d030345a1200b0030840d40011800d007120f0303c1a00d000d8a46448221156200110304050f03c40900001149900b4600c00c801c2c48131340c011a1000e1000b0354100307540c014490410b95605021001c4d10501818169100100c2040c00ca1121041241207610100b01c51588210001e082c03015400c0c4400c800d880b0364140031b051041b89030183c83d80c0c0034802d88100054411034002903a041030105580d442d54410ba45641581e00c13900303180c541601002410000912075142c203890401d141e400700d03c50662142d4041e005800c5a819941d42110454510014a840000c142d0b403 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 748899757 1250 748898507 748898519
    0x30a0c09090912090e010f06050c0f12032202150345030a0e010f0909150311060a1b1415190204050a0b070309031b031704080d0e0a 58
    0xa1541c01800f500710120666a280c0e001041c42500d03420440031010071030300400c034179688420302e607003140d60500d080c80e214a910a0407500300300d04440c3d0503200b40320740340402c10240e0803072006501807a16240b203000c440900d2449803036804d0500700e010398094291601601d0f042d03203000c01141e00c54003e0105c40c190901c1d0340c801850200150540001c0d4403107201d0f041c1045500340e40b48800c10b0380000c00940c2441a9007a0050698003403990040c10480020702c0102c0180c010350081d0003501c1014001d01c00558040c60428842130540f0041d5510088400041014100381c01142e4659919580761004001000da0810403000c0003d02100e50301514500d803420f0120610449442040251041c3c1007803c100520b007205400b80450b00e6030041c8108010009075071944001c00840f11240c50558565681b0304083c0c0702e40b6050360010740301d10071a402032070712807094007400001d891141c180148a241201100961809107000d05a159401004500d10300e50140003441c14410b80100b0851210b501d41c0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 748901007 1250 748899757 748899761
    0x33e070f0f09230c07030f050906030a0b061309020c07120b071404030f11100e030c0d02370605030103021309050a05101d06040b07050a02120406170615030a0c0909 72
    0x313503081d6540744c021610408140d8441c000707052900c0c961900c54101010880001d01030311010b4071220025580d988100714541341c5109584a4902c0e085103404d14641d22580703c0c02070b40c0001180a07013405119004180c000881b442001341603001001c400645e0b072610416680282102c0f142c0c40681010705c0f00100040f0710100c142c5005119032008503080c4114002d010301100c040403a5130601010411907072036038034006a1b50008003401c4075294042c60580c0041142c00c5c074584a02c8821460012203042007101d1281c411905603000c98501120599a0508032114007007800020360003000da41c0b1601d500e42083c0c0088046500034010340d60402401d03038843d882c0640303015500f000700b9103131040810038101020300d074810f001c6d0540c06801c2d00d2801390340d621801a0024403a9082c09400300d01d42c41c4c090303c00c0100340b070b417103400d00c40e07036591503440c0e4401510003003034014101a40e6220000040031400d011840416404004240909503140d0703107420301c084c1c00c0401d02b4904010000700000350810b01c1d4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 748902257 1250 748901007 748901011
    0x1c06330e0d060e1005010e0a11090a03060b1513090507260a110702030703060905210405040501150206010323070b0403020a080703030804033e070f0f0923 68
    0x1584002464803c090501824058200c0310305900616000041148055800f4240c3d0701002e440b03000a582c08400c01c20605500450400780c2d0400c04030000071040009580c003409020764120345c0031146044094048105101e150402d000c0260140410080060b864200f9134202046040100c0c5045500c40e1107140c1580d001c5024803010f007840248040d1001a00c6190740001d04811080d00c3c010090300483d54403451444020411540c0d09044014024207200c0c10715406128030406141f841c046103500cac0300380c00c18001d16100f2494074000003000c00d180c891000c0c1906064000c1c100c43d0303283d41c0350f0411423a16a250403d070446030341400340c081802032224101400c40b4102154a89003540184401ca0700f0b00d400419090703021040a10109410004d000c2d03200d0b51510b02a62202609101408100c42060034402d074041c4101c5465000700c0c00150707150901150b2002c440c00140c0c0e413110b0020f0398039103200301444160982d4040c03000805642044144140241624842640b00b030b10045a542003 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 748903507 1250 748902257 748902263
    0x61617100902120a05010501030911060a090b03042006030405061612020406080a0e060c0d02030c0702040f0b040e0105062101061509061205070914040608031c06330e0d 74
    0x2100b010000d40800f0361080c51b0152400f840d040103100c00c5aa40c144da844101518a48240008540328250910421801001d003004152603500d0341070030314000556002101e00014214450340b0506014217000d82601c0c42150454010541a12040718001104021542040801014401c0c004018001e0f00040c40188540d56802040d4030340900504200c50300c0814004c6107030030240500902c642404180c582e50702001c240142d4a80b01c1c040000c8d10340c8550103000303401908280400c18000413a604c000c0603d00195401d0041c080480c030400e00321581103c5456104505982c0581c002403d4050910441e49074400001d0740c0c0c0d02d402c0326501100b140f05841d80001c3d0021001c1c06501c0e80f046000121104002c4107000354200302c000030340010140e0203191454502d4070011a107036030315504041c00500da0142038941c1c814480c54002c04214095480910b001e090400000d00b40c081a2001c0c6281100c1c0090503c0382c0240329185c18141d802008004108041d47e0103100050741d403104030041c020b00c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 748904757 1250 748903507 748903537
    0x1b0a0e0102010e030c0c130e2d16031104050c181908060601120c020c1302130e06031e030a0c0203151003123f06090509061617100902 59
    0x60380c1e46c02c00074003141c1031101c0c0b4415400c24a00410504002506009801c00c959010401c000000380198141c040300c4451206d03441480341c02091a203003250442c0c2580e00500d01c04000034980014031080d240261210084140304001e40700e370100303140750403c003140401003402d0710140032801e4401a03c2c0c40c64011583c141c1106040c40604d68008002680c3d010801c6c2c0700340020300c5540b40c0603442d1400c208050f40242c4410118032407108280e4101c0d00c51108a511441450b80c036145055140c000450300180a4407800d03500d000c0e00d4502c0041c0c03900c280c200c40000c500d0b03e075240c54100d0354009030080072038051081d0002c20300c00f500d424180c18852918520011501c40c81d40c146210250720064904051102d01c1c0850b00483d0b8845003a01038621840d010300b02031625800c0b48402d88104a005c5503401460040301085400550300500c0c01004148202d89054882d031183c4801d0944407041140403c4461250504400e40c0514041d803040351040c000022960761000041a07920490040c10854 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 748906007 1250 748904757 748904773
    0x215030108062203200613050c04020922060f091a1807200a030309060509030f4f0f06171306090f0303051b0a0e0102010e030c 56
    0x180c200070150f070051016528201059481e5041d0802008410010b010804003110302030111107030b002d10160300c0d243c100c1111400c0c5000a07070200105070100040306c0c280507600a041061030203000b5182440310003000c2e070502010400c03240d158848648140020244c41d9000042c02509903045d401c002c012041d804110413984120f41d00c00c0080480140e481000c0134090100300c1d002c1e0b00030003a408031450030111661060703100309070f01d40180c1c121542030314444c0d00e0107101003541c0343d0040035003e84501c805000725100c88400303540b01e015010042401400a020b904030f9148403140c201d180b044090412400440c0d01100c0e980e0080151100409040b072040c104418071080c00c10500080c80f4004000300d8041c1400d1008118a07546011000c0803100e40c0c02148001040418075030009505c10300c200044003051a006a24801c501019404246464000390690001c05007590507010900c1055142881c06441030701d40b0040b0401c0d2504542d41c4100003440746408200401d840b00818008102e49 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 748907257 1250 748906007 748906019
    0x2070905090a08030408090415150215090327040501090905101b05070311030c15180307030507050a140c040b0607080d0e03070503040608071103070c05090c040302150301 75
    0x144001610a05055020050b12408550081c1c00d49130815407110078503a5030030220340000c020f40503100682c04101c092550000b00410a2012040824800c1d0240c1f0034070804940030000902c0100c4400032250400c1103090484484819100159001b0b11004000700c41042c01250407a0003d03041035402c580d5909154080c00810080c0055032445400180071076401d6844010403020f000c1e5441d03082c8003001c1030620816004450041c03c541c8464226500c80440c401a0395590030302c0851039015101c10030200d140d00d003001d4a1050351241c0b0400640c035104040e503040713074268001c51013603456000341806800050056803092007810012802004424802300410048840845129218031403c01072140090151f2059a01e9500b45060009500255002450a5103307100700100310340000600442c400350050781d4980202095030391440a030150041d8140d49106113a8041c104800540c1c0800c41d924248401c0781d8007d000d41500350a282da66070215900581543c09020046070100050000c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 748908507 1250 748907257 748907261
    0x70602040906090f0c0e0909010227010f0206010b0f0f1b0714060711060d2c07060f120c0302041d01051c1a040203011103011e0f180f090b07020709 65
    0x2040c000f0030f42000701c0c85c0417a9000c1d02e05c581c00050a402078002e03000003030100310298143d402da44060b48100300004180e43c0002e01682d85a0340d264003046001c1035641e070a0344000303290380c16502809141c41c588504005207100d16044014a001985000c000a03030059110006c1220010314000c01001100d09082c030b5444110314820170640101d030300f4800f034004281c0039804049001c4c0155840d907a268a120314405c0503010628000f00c03034001e6a48400c1c2000c01030344d4403005042da140d00781d40d0281c0d1521021030b4102c82a07104034001076003ccc4610721324001c456111140c81002810018039155560085098504000b01d411078000c558a004001e9420600c0003113124890444400c1400c00141c0c1e81d14540f501800c4044000039004e40000b41151400d45c41403440d620388040194a03585d50317041154050302c46480280d259020420000f0302c070640c03c2c0403c0c0613a6210401c101840600e995036200508001550f81071450312000d00101260504410500600c590350107024680e0030f049020003 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 748909757 1250 748908507 748908521
    0x801020f1615061205060906151e04091407120215031e07050403140d051c06051905120a0b180c0916080c0703050712030b0a060e01020d18120807060204090609 70
    0x2e1f41d801441c20800d54908114001d0750455040b140550100c418400110200c0f4010a909400c2440e0201000a0100e0622840000c0c1154812074003400d880e0344088182004004000b900301c5000000013014200c4c41d4041c5620040102034100c1108084200502c12a01965000082480024103109010b013488080c003407500c540b40141388070004030310001c06070303c91040803c4e00021200f41e081c40604554210600410740104143c0680607000703d204410301e0720b4402ea0b0b00c1750110b52038203501080701040d81c05955800240f03004c0700d6600c1050380103490b44020081d03001805031070300c940b0207030391403800c003500595504205010072407000e072018201440140c039602d891030051020000081e405008c40b00025807005034110301070890321041c6c0203880c41c07625240d44100030140114009500a0152150175000d90071141c052640580a5412008104404e89400c404800034025030014112000c1150b10501d4010711381500c40d11204201e0700182c100d1191039850308401c0281c4003e5004842d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 748911007 1250 748909757 748909771
    0x50f07061817060f04080d090305092b0209070e0306090606090106090315112701120e1e16030506060a05040204080c0d1403040b070c0801020f161506120506 69
    0x560407210701440303503030760039001342507448211841d0000740400c41468280c54140590795002d001e10241460040c145401615080d400b032244a07644143c81c0d180e03000c2c1c0038002d0b0440c094000443d2440d40a01400450040205060214504e0104e42603182040098440e102c4100501400e0901204001e0481410b0340310074104900d4900c144003250042403c810b40f072046060000d4686081e00a0090b28007a424000040c2c030000380a62400044651503400038500036030303032840310400164540c0700f02d4401040d09000d0390b002c82c1080b404101c2000c40c84003507a002c1c030101c0d00c0144105107410010300854008030340b60313007100092000794100308002c00050482120254103003070a001e1607941d142c0799155098841c2d90b8420b00c1006010700030185044902c410130540b65543d45070700d40700d86e140e0700042044501503407003000000e1144040c401c0d40d12445d186c1840c0742c502030011042c4030300800000400d846007100040012007902c2c1c0ca11805005155140e1812240c40c0030381091401c20000804034 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 748912257 1250 748911007 748911029
    0xc050a06050702030619140c07030311160b1308040f0303020f06040b0403030b011206080c0f0315130c0b0703031a040b030d0f020f0d09051311040b07050f070618 71
    0x74000503a030111707080c0e905c0881c0c0040d10f018a45089000c60107841440c115018040003602800a09001c078401040994020340301400051000f00a141581c071074101c50b0640e103c038000b0020001668069480d42000b191174140000440c40e80340c00000354865480710388000302103503017001095010710040d4400104800034106030301d459244e25840042c024802008c0580c3c510f40d2a420782e014690040c424210786004204007070b200c407038003640c42c00c40c8010b081c4299018004605c0510300000e4a01d48100c1d00c1148210300d80b500340801e0f44d807001e6800c1c1190409405031010800450b82c1d000b030f0400c94040d0340c000c111099486841412920b040130558015401c0441c260300a80340000c1ca00540603aa00d40f000391070f0303c03c80c4100d090440414001040740900030904d184698400e2a07441603030402c4517548403041c00754070010100c40518011441520050108001002c114070280c29154003900a88080e450580000ba08051440d0050808030302940e00d0b00d24200c9040c80c440b00900442000c0e = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 748913507 1250 748912257 748912267
    0x160905040213030c0e242e1403250903060f090c170d0e220b01020715080c070f02091014150315030a052b081611010b0303070c050a0605 60
    0x25007105a107604100540c0c01b41000e071020060b8441048004000c4d034540184032444800720340ea4020201c1140041000071400d00d0780e4880c070000b41c81141c0c01009a6000000103807084001070700b00d4032032500400d05201c06d02d10000045a400e0091080e005880b541c0041c1107103651070610012031158005420880c050464400c6046002548044981c11800c10200c2148410000390200080085124001c40250401605454070b070300040c0b503c280907001c0d60078440e1191841c140d030170384121101000501c0300001c105100c5021000f007504074000d5100c00c054007040e8000ca1283c26041e14444490f80d8000380400950548440c03032640b40f04c04a44140d1402c1d0340c21900d4556000280c480d48460050360740e000702c03981d4100015500264403900b0f480074030b801e18034207401404000340c802052952003200d00c100f0520840b038142c4140381100145507a125100002c0b101210540c003a804150350740c940d820116a0b041000d80803c0d88108121400030341040700340a80a00e10b944084103101c01801 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 748914757 1250 748913507 748913521
    0x80a12050606160c0b160b0714120912030103080d0c0302090312090a080114071407030903150f0204290c151b0406110105090a0b160905040213030c0e 66
    0x304603200b034003505030386003e002039500b440c1c070b000c80ca00e03800340b2120400007400302101c1400070881030249004000301210b560b1441003d81c0c00908028000515400c10080b0012494032240031542066140084030b03500843c4101c100900d07827084e042680d01110205c0e003502000c20901412801300304900d015070602c200c2c003011036035440b0400085056a040450900d0080d16001d003103a00030b0001d06c00a00103d14910031081d0b50348001c0e108800041c140d00032541203410a00111880c2541c55075401030b4031031460300c8900c055940350b003601d00126280c090743c032440c602c2400500302411207100104903c0d444401c00c07144800300111b40c0c03c3c10b948107000b0307001034000c0400c050444030300085034212540d03907010003054400b4221620110f01c0b070000c207010500d0381d0710010300ca1501c001840208800e0b211003401d10360305c0c5c00010005017510601800140d80850406805002401e00e09000c10350b90303112130004007a6084460546026500540c0c01c00c14400c0310301c2200001d0180209404850a05403 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 748916007 1250 748914757 748914769
    0x51501050913021f0302090301060b09010f080105090c030c090a0806061926071e0e01080105040f03110705040914060f09030922020a0c1b060c1211030403080a120506 73
    0x4a804d9501044400c03100156001b0780480d49074400003002004100e03100e5401007501e40003000d8113400240c1c0d4507100c0c119540180d070564180c440c01801c1068943d01d5402281032544001c05a006140043c0440740c42c903240c02c00b200014141a00142015103888005d01c27400c0215070b520b80c0240c1c80c40c1e81c000c00041c04c00d51551540d500d4203109021481c0ca031a489075181614961005404828071861800300202588844041c2c1d40c1c0c900b1004002d980c1c44124500361101902d01070a004104940d01d0700190140781d8004141e6107510a907503496a8500005040303800713041e0182c03801c0300ca10b540c1d100840c17014030016902020400e143d110904101d00304964038065041751324007445c0890301c0d0a00e90550707203c2803049130340100c0c0b00307540d50340d0740d5040200140d0004c0d00031120150840342c030301e03440420f42d40c0880a072007240c1e48440000c019520b0b2200003d11841c1e20b10140140355290804004c421300c010005503014006036941c607441541c2c01410740b0061081d10f8107046c542030034044503907104 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 748917257 1250 748916007 748916029
    0x302010f021215150c0303070306090e030a03090c050a09140a022703030d0e03130e01120308061503010308070b07021f0f1b09030b06030309061c060305150105091302 73
    0x3d0014400200809000b04006003066481c1c000003140105902d00818000001544220501d550901109507103800020944204008210140e04140b041e146194425401011410b0080103040001651040032804600980d00b054100c41c1e1250648a025420f00440030b402055020045160807446003004001200030036008032214040e0ba075803c2c060b501042075590382c2c070380400108040704c01800d042d9a00d42c048824090745a4561000051010001c000349049500d1140c1000c03106c00c2070f42e01200c44000c002c2c2000e60200d0b03180001200300d80a4070245001e548900c0c501c9683d0380b400c0c00c00b07514050004081604550080c07034110506031091450341d100310040071300414480d4000c4c0e06180034041c10103c000003c1d0300584214041ca80c03142400301100d001d400010050f8442c84145902e9100b44824240c0140c0208a001440500c03410810310f00d05141c50005400c40c2c0300ea440034100003586200340364541d120070041c02a480c00c42c80f807582203410040c41c1c03609506c076680454540707100 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 748918507 1250 748917257 748917271
    0x90501060f0e0f09010905070f030302060a200a0210020a050301050910080d1b06051006110c0603070e0d06050708040b01270b01030b060705010e070803130911040308030f040302010f0212 82
    0xd400302191350820b00750000480d89030f00a041e201c0e5582c4950007590b0224141c07205400620070000443d0140c40c50340300c0c0c8840c011100b250b40c032215901c0c24a1465652000140300110b1283d88d0104030509403d1000d0b081114156840a581c0d5140000700043d051018103c195100344c0030104000c1010f00045841150380d1a08204030400c61443d542695849951000f40c101c0f420030b02008609111010110b0507100c090701c3e455807203c40d48100584c0c40e440c0c100c84982181040ac00b1510b05401401d600001c591700509030540144a9a107010030386a0070744e0100d001c82e50a03010b05c0b003000306800d03501e80034201004030003007555a813100810780c051944140c000e50503600c2110506c980d209400010680c200038056a640720b055240aa00070501100c900a042c080c44001080302e01c0c1c0441100d01303449202107001402414504034100a1201005401441c4402c0000000284501000e18801c0d40c0100c4814203510b4641000b9080d2407041800d0902548100102100d0b464a0492a0380143d1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 748919757 1250 748918507 748918531
    0x1005100f0507110d15050712021305240a0c060b1f080a02090a060206060405160903080a1e0302180306190510053d0c080d0618090501060f0e 62
    0xd030300d0201e02040c07040c50024002c4804034445c4038400d03416410090081095030b0355980241d001201c440224082c03440b11049140e070080041209190003e007100000700c40d2100d4003034070082c0d1000e00056612503a80400881d16444051003449100d105d044000781e816206001d4000301c0d020480300320000131025109108880020a200d60441d81c140c48103104054412491640c41e82400b03503440000300e81080c82182000002210110300f40c058004040d00380e114059400d05642c0c442c0303516003040b11003104100030f0384200110704900d002d01502c42a0746480040e40c0311900b4111000b0140241c00300d60296116000781300300326a40b03d042d80c041d07a041e0305c0001256100c3d0200741c200d0301c10325403006178801d084480350804101000d03444444008908402240345c402414080825030501c1540000700342548038060101e428000144100b0881c9407000a21540328048001054a21154004016a56480b550403c0400d00c10007000d880301e0541090702c0d0f840c0a02c90b4004400c001c1501180caa = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 748920863 1106 748919757 748919783
    0x311040915090501060e1e13260c0604081207021c030908040e0709150f020d031a1914060403020a03080a1b08070b06011716090e1005100f0507 63
    0x19510503240584000c1d400c42c3c000312452002c01c14818203d00304404001b90b00302f0b0120501c40c51251071080d4035510300da901170501a800810440955101b0000000c2c2640c2e00c41068150072994a004280b84000b468000c4207402140d100c1d1407500c001d40c0a2288494201c4a102c080c0c540025080c05840d4a0302421078031400b01c00d4106000d0b800403600741090910035006900700d80303141c0c0703011280c140f01407010078140c00d0844015655089011820711446d0b041004880440004403000c606060940d00041d6040c9820b00c0006c002d2900010003100d17140c040c080500381e00b1140030041e00b000040341001415680a0b034000c07074440ad100b9000448079800350111038000310303103841e180f6490354443c108030000300203000307030311080c0035100100084c910100c40020307101c1c8c41d1001c0c10319041841d110510000488940c03908040c005150180d002c020761041c29184201c2d00308030090340340 = true := by decide +kernel

theorem cover : BRFrame.Cov 748741007 748920863 := by
  have h0 := BRFrame.cov_init 748741007
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748741007 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 748741007 ≤ n) (h2 : n < 748920863) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
