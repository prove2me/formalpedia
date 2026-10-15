-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5147
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:54:27.795328+00:00
-- url     : https://prove2.me/submissions/09452da6-5779-428f-ae32-28de155f95f6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 925539568 ≤ n < 925719424 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 925540818 1250 925539568 925539577
    0x7020a050d03114b16080f0f0c0111070b030708151210022101080c0102120331020d0614010b0414040b04020f0403030c02030c090906181002 62
    0x25280c0c25a5103403411038180c00d000310980b040c400419210042110303090545000002444004c508481d2031400260395003420701080080040d9200d05540d502c0380d03001581d81007040d20700303a03000d0701c0d911001030440950701e9260043d4003c07146c01603001d00f2442d503c6010b071030416060210481d402143d45040c140c505030b01c1540d1070000200214104402080800441c2c000300509540150f01c890041c9030464940d4441d07840c100c0c183e60001100200007194581c02402e000843c000005c103135a40349407030365540f03515952203400f502407203400c11700c08284082034a1140008401c84a05143c110440604401c1d071800b4503103070f50014211074000b60700c0300d0540703041c030620560000402d80c2d920343d801074809205a12240c0c2180302084180528880c10075850b085d82426135010a0b900c0222000802a004114032440410800316000082c9548066038840181c003d030291044041c04000707225242800b190390960680c055004154017010000708003007143c2d210300a403206442c5c0185414180e0b4130 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 925542068 1250 925540818 925540823
    0xb0603071715070c030c06111903020c0615061209010f05160e0a121e1a01030b01090506150a120c0c050c121515090403030c110a05030f07020a050d 65
    0x48003031070461440d04a240e482d0020824145501408000d560050010841800003840961223003c4c4119901018003640d8002e403224a40940d903035510b8800500942120b05d50300c07010720420012134000b481d660380c2400041030141844c0d19151141c070485011000140c02c4410540d0789400c40703008100b45205890083d800400b4020100c080c130100289400700a015080c4540f8481d841003042c84900030109400c0c0f5400820103130710903c403054100c2d9070030501c100507003c0415a1905848166101e00e0913040e01d11403008000c80740d884801c1070b8200d400840d411074002c03c0700200b5040707603806407001d0f1040003000c0c0f07441c11039171524650110640b50101c1417840030620b0448100c08004040c00f090030183c00c1501d03403e00c0e08100c80c0095698050501602000015002c04180040f0719040b000881c1e4101402400242c1800d1400400900b81c049007000000da90500300b001000c0042914140c2540120045007010301203110b007101c03035200960480c1c0c80f405200b00021aa00c545250002e442d0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 925543318 1250 925542068 925542073
    0x20603010b0304210203030a0e1606201b1513030606150e0303040302040c120501080d080705090f011407060f0c0807090e13030909052517040b06030717 67
    0x1c0a2506081c1c0001c13000c0d00f420003194840d0a6001d0705d60020907a603000e1130301c7c1c20110300000e4031720665050250000030b009100f00381c1000822540c1e0031a20003840703a51031145800300b10f0041d407011600ca4003020b8101a44440102074642c0b5441c10751146440400308800c024680401103210321010b42c1c03c1d41c4201d0342191920020010748504050041c100c50035400d062500341d18801c0065140d10030750000174822a03695010f004002d105854041d081c524141d0200a0780d6110202a48e46111008450340002c40c8580000d251a01c00d01c140c9551074005015001c90305449001503171112035851002c0001030040c800d0201142c0c0a004507070300d400d503c2000149032141440c0040c40a800208840244060100100b204480070b445095010140d401800702080303107841c00316442c040507445075000504000c10f00081c0f950014802c402c00a02848040c0e04941480c42a68448a10700d0b482d0345019541002601241c440201c1c1c2d039000034010140c030804c80e01d0301c030841c0740700114807a0042250b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 925544568 1250 925543318 925543321
    0x5220f09030212040f0504050a020f161e0203032a011113060305010e0a02251109010e1608090a08030f10140904150905010c0e0103053103050403020603010b03 70
    0x254040c440f6524500d40d550903285843d007410304403111107449104040c0110b51701d8000840300d080941c140c466100c40ca0300d0a0769111f00d910510048012100400d44040ea4a00007070f200000f6010f20300320100c0c2d4003401450406228081035002d00e01c0c00c0c15488440c040e6040c0d000071a00c420f02c0b40041c10081100c0071a11404403000b260000001c40c0c0120041c03614000c0103104034024004819031110030f4072809a83c0d040001c00c1d9500819901100383c1340b5041005140042000041d152800c1074010342c0e04941ea0781e41c4294024892809a13080c5c3d031904c506000700f00c074940c403503c52650301501c0c00d411520030310170940d07564040da40221015580e00450406214100c1c1c1c0092541005104494200c101c100034134000822a00c809000180320240350b03a041038010203917401115040d508078000300007690709504064a660001000c15001a1525001a0300c594440c02c40048001c000b035020000804029041d0201d00d07000d200641c10b0100c18080040180d032004000c47c060404019115100d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 925545818 1250 925544568 925544573
    0x1151d010e0105031c17100e0a111b0f16153f05010807171c0e0d140a1406070c1b0b0706020910020d050405220f09 51
    0x20881a040754051801ca503004001c181e4000450817100703610000701100d500c2c4000419560f8000c131450314110717101070314100002d18558039900021103112145040c0c1c01d6446900403402c072a40604101032250301400140c10404501040c284072088000c101c07a1054000a100c0d4940307100120745801d41c00318481c003445214220310b206010b0b00c0c0542800b40400203030483e00b894010640c2d1100c00b2101d0320400c210502d006c181c1c05540616140c240421440d40c43d15143d6450390b0076400b54862139400040074018071803000802d1140c010201c422045200002081201c001d5203403541240d100100b504498041400070030960041c44264000b028491001e14240000c0d1242040300142031304800700b005001900720341c20031105640a211144103490641c0790b08580701e21500201030702c02d000b10302c00c0304211b15503000702080c2000312441c0d203c241c0800d03000c903a03500c0300b10790f00c00c0086d43c02c0c481041103003401c060b0a10f560300d1107641c41410b0044015030307604035015411030042d150740b54501c1c07206 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 925547068 1250 925545818 925545869
    0xa0905030a080d150803030c090604120609030f0518092d04031709060f040318080102090901090902060f07062a110327060403081b190f060b030115 65
    0x26004c06108600118070385882d013500ca01008000d94070300d0100164000141e82e65004440180542c48035005011660382402001480801011408924002e1145241600540039500004600500803a10036412028401c82e408007808030701c0c06084420080d07507601d0400c0303d60b0098100c0080b12040520b40390034024a00da040004140050a41c0f20500c9074400c1c0100d20f00d58040400d084e80303106a00d90389801c803900b240e01000c4081c800710900022803150019001400c0d506812107850a9998031041150219102124001d42c03020040010100503c6403001910245018020002d0a1403172112554040f1031810440c400740c400c091040b14a003030704000c10a6071214054011030074035100c0419070101c518100d000401690201800c1da415555203400c69007c1c681c403503521601c030702a90011009000c41d100800c11240511030705030680d02044500b403c1850340200e03400351448119110b90b0003e02030003112640554a031440310600c0498000298014030f8085d08015014a0307480c205103 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 925548318 1250 925547068 925547081
    0x91103040326060909100f020d0b1c020112060e150915101b060c0903150506010c0206091306030818040509060105040c090f1401080901021204080a0905030a080d 71
    0xb0411200c002c1d001149440303080aa0342c02401036a034107a1300c4c1c170358403150742c944895013155540b418240008198401002d801905843c9990141488440040403c122601905003050852010300351000b0003d1341c800d40c1d182089035035070040001c134140c80355000c22400d40221920f403500101c07816941d10a00740040c496034000c1d0114505131400c2265800564030300203100d0030f1010031028190019031111800c11050010f40d01c04130800c4103210078070300540207000c07510040d125403c070742d140c0b910084024000c0038410081650b50080342d104560030820a500b10004131600b0010a400083c4507200034403c5401450150307410319291020100a42e8072a51100b00d600d000c0d500703160a1062100000600303d046d100211400700701140c0001085407000e4840d4054070803284c00c80030000f0a40c0060041c0101200e00307903145001c0340d0b99100d0903402d034854112031400b6041900005004150050080d105d80e02c1c41d03160421036103540b080024035150100c041900d003480006044850f440503842181c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 925549568 1250 925548318 925548347
    0x1b0d09120f051218120d150b040b040911041d0f01050d1703041e1103070e1513110a08011508060117090a02100807020105090610060e03070911030403 66
    0x5140c0b10700300501d05007501e005012894202c03001c4242c0e4a00160034411303170140745020610b2030307282d41e0102d1526002d013084516481440d5100d210101d8911503070000c850680d90407032a1280b50510304000c02009006449540d60203d2044c0070201c0c1c145003100401d1360071864920660a2070a101014202e1190182e0010f40701c0c07800c03030b441000000c0d2200d010500d241c444045090322a80c0f0740c1403298819100d008440c400c5100140010104008148000707166603050701200c9a44cc0c0b11940d030008103005880504240310410005910b40c5400c0000c654000da102a010030030b03020700140513065401040829021550004c0140050300820803000d070061114078000380c450401e60006003849070340104030035070b801004001030348400c810804200140c0c0e0140c80111907a80d8408005c01051040d100c80e0015420017020441c2d0038000100a402016500103035000146020700941c0c62082e10400103806014004002903640d441c2d104214505040f1b181d1503580e45800d02d0000d086102911783c4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 925550818 1250 925549568 925549577
    0x80415050405131e021305060313060501150f080421111009110301021201170705090106050c2a04090c0909050c01090f03030509120f100615080108061b0d09120f 71
    0x55000f601c0381e40c6c51940c111392050316210383c0c1e80c90300c08001440c1e5407104006042c20f82450000600250701a04c0b000482413140d440450760050003004482060041d100905105002c1203120309110b10b01c6034500504100d030030804003540c2d1160740241040c00550128100030794071410344040c0159042840200c01044008526005042c0c102001c014818083d00e040201e40c10714503a4181020801070002e040010070303120256035100e900500c2944024840c9806008056032060281c10190080d80120045550360000c148940c0c00d000040c518124290340700324007000c000409a002d48078600202c0d00071000b078810074620030005440c0600d140d101c0b00846004a00400c0030aa000b0241d0304040d4084444000843d2840d252a03d040e80c4101070001500a0b02d07100758071041c0c035621400845600c0305c1c1000071205915010f6030040c209100d0b00b00e0f2130304100006802c800300143c0074000503050310050341c18040e0060769035080b61a00c030130445858407401c9124001c1e80d0800c07004180003009140 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 925552068 1250 925550818 925550827
    0x16090803130608040f061a130207050c2211030406050709080304050613180e06090d080613060e0a0501030b0a0b0102100507050f1206090112080415050405131e02 71
    0x445045015940702d600c0400c8604004a810403802c11700380c002c041d801603000e100700054a41d0603240c0c0c00781e144649126110380740da4180805140d0081d00c0120741c0120292525083d10004c2c01000c05551150070440d000b90402c01440c10000d1240c5403034804038460844d16031505140c02c808644000c0d150720280310500c00200f204c950000101c8d412360b80d05072180c5807907a00d0030080d1a8082402d403c101002101c42c0c5e550035414200c2d070b006401504c1c0d120100c4038140c5a4a1302a0744503d520382c054800620344100240040c204590782c1a00c40c5850f031000103507030350f40b0070941000302816510101a9522000104203111000c001079130000d13400340c020000c411040002075030340c0c03680c3c50b2004a450740b90400100924002d1050300d031005200c01da215070322008950182c0c8000000c80741180308100010000c00e03c614040c2a518a0507444095107240a0400c10700c519401800301c008400c0040412000c295a215820740269215a240300400d03188000b0442c0c6850425100c2c0b92903030b4510600 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 925553318 1250 925552068 925552087
    0x11040e0a0b06250203120f180901150c08070b07050a09080105070f110f07180f2309030702180108060601080c04060f050d0e0a0c060504030b01090c0e0916090803 71
    0xf10700c0c0303503401d8081e041060000c2440800c0c10503480728220f007201c4d5000700702c0c4541c6242d008006c001c40c008201c155151503c4020800031800c07420f004860004d000100498815401400c5541401b8060400340741010211791303c64040c80c204a92000000e0310101d003000403107400580520281900000a00842ca40200014450131a1402c02e8081044c0c502040e00c500c3c1060000381280001501a10002c54603690345040802114210303003e481d141801035110503003503100c2c0803440c40b1854201c49840020301014a00d809020702921030f940403c100d280300594415105001d82e00080c0c0d480030380c40d0b15104590b410400018401c3d410b01000c0c40420039100d000d8030481e81074640f5030401100244002008403118061000c41140291502d141481075240c005481c440e084c0c85540603220654480e4412942030103188030050080d242c003001070002900b10b801c62000e0070b403207140400071061914005200fa01c0e054840612100707440740b08000d40c40c7d002071803402802580d0003d516212000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 925554568 1250 925553318 925553347
    0x909060e0d020c0a090b030307030c1401050f070224070c1a04030804140d08160311030901091e030e09040f0605040c0e0903070201020c0d03050702310b010e1311040e0a0b06 76
    0x40340060410001218180402c401a21982840033161008101c50b280a081d110100503050f94100094810188002c1d031035116295003542c044a02030078501e5a4840b200d09646070301c54600c2c01c03035400da8174150004984400130710040c440ca019a6407040b80703050900b406460403100d00018020b50300500620710425400c0b4568503042138000c010480717a0b0700480800c6001b80008012185400c0000060103103c2c40150089070303000307018011400303c0968005140c50808034120000303000c5003054015150710314100c4a0386030701501a4200b16044200341c0d070b65074100da0702110304550f00364400c0c40602c4a07402e50120706034440d481c4801986403003a01c2c1c0020f59201841507803207101744260001c1d0700401d8800d40036540140e602400f079440220781324800000c0401d200842c080b65044a2200c5160800c40e8010b101c0f4440c0e040c1c503081d01440c0d0719030a20841d00c11184003010b0850b240c000a00c10000701100800041c18080858030300c50030012500010355140340c1c0c00601c0b412003880340b80c041c401e00 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 925555818 1250 925554568 925554577
    0xc0e0d030e1201060b090f040506010c06050709050d03020313051009030f08070b07090e0c0f03010303030e0c061804060f05060406050a1407060b09070201050403090909060e0d020c0a090b0303 84
    0x541090700d00c0d030003220000341c039038003609980780710303a5090420004107046104050885908100c0d02540c2000c03010301440b01b142c404a03615800603202c0b680440110703216610807904225a40340c1561042c0c1c031800420b008010203a402c40c0103900c006508004240954105409090111540134003110070000040074030200d4040541101200c03d0a1410000080110303001c069010040501506c2c09200c041c00030800d074458605d19010740340029862044d03200840c0c4106031440344a5082d1390850328114000c0902c00840140c81c031541c58048030650780e0300080c090400072172481c03403400e2001c18144401c1d1240c69203c2c032225a02c03150107101c50364404040d42c0940f0801d00e4001d803240c04000040750010b00d100740c681440100080c074402801200c0c0c112030341d0f4410a41e492402c90700c0d00d4004070300301c2d00700300c0340a00064090070b4203111180e103a41242180900880700801c0009010800e9410415200c100a000d0f9110011320300070303070030458180390017400500420442d01080002080d140e108 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 925557068 1250 925555818 925555823
    0x80c030a0c0207051305100909050a140f0609030c100626070b0310051215070f020a02061201090606020d1e03060902070b01300210300c0e0d 62
    0xc41e09090a4054820440390700100401403142c200001c42c072030420002d16003a64407031078030408441c011400c441207001d0b80c07011a50090080280f804903480d0202401c0d040c0c0c410040034050011000125502003007098050340c00c1c5009180d41e040507116070340c1f824072800d251071032142c100a01001301c1e00000844030756028601c103490412042102805040500907000100d1601010040c480b1081c1407400c41c80a03500b003601c4201d03400070010301c0c15a981410840301c2095000b450700046d9007500c02c91012241042d40e00441c2c03198070350742e400561107421508540380c6409404004000034140c500540e03000708413600181500c45404580208000d603210448403515064500100300c041c4241e21500c02080444000c54454506103070000400c03c0c00c0c4149012140075101a1224500d1600d50143e103805400701420070401035400d000c80c100c18070080c2814401086c40078440c60050698080c9070340240e41140640907030240c8400202c5440300d07c01c104105000c0303080d2101d6190944010040c68 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 925558318 1250 925557068 925557071
    0x20c1809150703020c1b06030615040506070318060905060f031003020d030c0303060603050907141201151e06051606061a0901030e030f070803100801050c030a0c080c030a 75
    0x55819010901d081000322090300074241d58020011590b0b859030151002e204000240c400720364003011101200d2803003a0010794003c00820210341b00d403905125243c030215044010504056681d00000c80f503800c031a80c183d0108000381c001c000c00c05151018800549224100a41d20310b00f400081074050281200d081040000000070032741410502d00080015540145262806007040c40c0042c610294508203c001ca8103000d8081082c500a018051042c6600c1c1e0060050625242e165041c0c2900d45185a811079048046002c03003020071300a06140402961307016084038074050540d0000500d07100300c040d010a100c08280003803035120084441c04441ca02c4203003512245410040d0040410340d1100c83c100044c0222001003095040c05890561402d032010000c100600795550303145d00c034500c80740b1840304c030030400b81c0e001500000103150001e8950a212224989130355070a030859105480d6045d42c1d80001c020011701a0a0340141481c1c40003a161081d0f950801c6245140140000713806910040d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 925559568 1250 925558318 925558321
    0x91842060a03061806140a081c030906020712020609010b010804031d030a0b19021e2107170c0a0e0621010b03010807080a05062d18070501020c18 64
    0x8611a41012025200764003040c02c03200803004404c002443c15100703280ea0807540c3e4601c0070b8503140c1031940c001106c1c0214090540c1014480c2c10b06e8981c520404890181965641d554000c07502520180c2030701031099018803400b000f100404ac1c5045001003540f017450303050094800c41ca0f41d11941a41c3c1256150400e0452a0105800207052403c0d4840580e090f1141c00a03880620048030405801100850380f078400b88240501001b003039200c0d00c06881420000030355114440c0e01900010080111000055030040828400e1400381c054240c13a00c01c002005040c4170b2101c100d44c020002c7e082170b4041c403800d1402d42218805014884c1808125100340c1c1c0120b1701c000c120382910020007003440f604511251940c3c44084081031600b0a02882800d03102c0d10b01d000c40d002a00041106240c4d41282c0145010b036940514002502d090907840d0640d403070134140940190500c6980e40d4090840e401000801403648041035242001c6540454115448507240c2005a103490740076082c429181c0e000200d05 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 925560818 1250 925559568 925559587
    0xc1204080705030c071403030408070b0904061508010311060c0607030b0102010f1d0c03120d0c020703061a01030e0319030b040b100f030615050d0209184206 69
    0x60080e4a006400c43c000000c0c40104060042403580030746483e4032140803180e0001007899568011405812555071180c00b050160b28440c1001e003940c0280108003150240d290455041000352902c0a0b80c0403400c004014401c011075043d450001034010741b8554203202041824956410b005010007052590754010440264401e40144410b0304106d10184040d020424a003108204020216000f84c001e8600901051a0100d104894855031a10050030316a8500481d402444402c841700294030442100000190b0f42d40100a00942415003040741c0e101c0410006d410368060500100e45c13074004024414401880038220a440d101d94900007070025111400b0030010802c0701c0800d03520001d18000c00e201950300040c0710012040e00d990074492550344110101008007840c0d182004240c080c043d0b0643d181050b406064039100c014052880c41c62040d0416803808803d40b02c030740b15000883c61948441e07240810658002c0402c8070710504c0304a24100380d0043e2001030300310324490800040c10001 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 925562068 1250 925560818 925560833
    0x6070206030910061d0f06030c01110703060501141f0516020609030a05070518040b0105091f0608070905010e0906060f0c1504020111010c020c040c14070c0302180c1204 74
    0x40640c00350804001d050b80301d0031701ca01c050028004c889460f040c0580012038141030000310710300a1001500034038040700e45200550313004c07865525105540c800c200001020030154080d9074000c01581c0c100c1c1c00d61842c9801440900c405044441440030a03842540301603684c80300c00c0b60389041c00c3c21000e6501c041c603480010b19a2040401050b8503220381894001801400701d0a102120000c03a0205104000f80003150742c002401c4802510300c4e040c0100401480c1001462543c0c0302c074685e290700c1c6003071419454107090700c84070b5040000091500c44c104000c064104075074201901090810000100340a80007420201c0002c02c0a4001e20020907a50031580300071003030707030181c0380f004040c0ca040308044d9110a4901303500f190160b000588000f01036070010360600c00e003809500f05a0107040c42c07500c2c09040c000030380b5001440000308003a18038004a0010b00c5000340000340d12500f00c09646914600400100040001444c403c5100c40c2d0103008406030b84104550040007004460192644d59042401 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 925563318 1250 925562068 925562083
    0x120b0303072109170d0507030e06132105061503010e151e070f0f23120108010e0601030f020a09060e0412020309010e09090c1f0206060d02060702060309 67
    0x144200e0031440341004074220329064041c00314a80c0c1d1500505a55580c4c6801a0000107100307034001d0300000b501140443c42100100703045801b9080504000503298041083c40d808502243d1014040305d10601400c0e40521220301c0f000500807400d601d241c4c2640300d040c0c90303050290403c000c440b01e60b650072440b030700e082d006801d203001d166054900d25848100304000c580021204c000c18004244001081c1c4540b034245140107003555034440320107c84a1401f55605000d1400320000d00018031152100600a80f070100d03d40c500004d103860300e906104a00c4102d00740c3c1a0081c06c220f0b410500c420841ca50005401811039400901c0801c0c1501d06001203100550a0b8100444841c20520080745103685c00c1c0c0c210313001d2441800c00390803400300000c0898032401103404071800290103c00f04115443d0030000907402c1020b00c41624011500040040c800c000c0c015001c2408140c1d400350a4030840e01800030540c00007017513031646141601640002c030b25205505000f0300c03d42010001c10740401003081000c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 925564568 1250 925563318 925563323
    0x18041d010c080901050907270b03060c07140a050a15020d020a081f0501050301090b030f0a060509100905030d0203040305130807150318081e0d0b100f120b030307 71
    0xc014880e003444004061036003c488079241c41d070070500424a40c40e03000030408100d07007048010034040501407802200e5442c038110503030a500d8803440465400d5034144107043c007510243e40c0182e51101a441c01c940b52101410500a440c0c02c01144100400c102117035443c9013941c0410900d150800450350440207019a0180c000c0040c0f001c9070710b50207650084046401640007201041c44a54102c04441603071402e4081c607400110309100401c100c0d1601e400c03c045480000302650003c1c02200f42c5a490001c081c18144d8040d6201c90610020100520003404440b02d120414480b1440944402da40d0344180204100e41c594000300050600d445502610a00d8106105940109030b0f103001a0b030365101c1c68014640d4201c0f02503418007102c1d0081c4180d03240c11124000c5c454809003162030302d00003508151220040140d10388000c48102421130b009144441042000095840b10f560611881081842040e42801808100950302075000f00c000100d44214200c0860846899000710b8118010910b00 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 925565818 1250 925564568 925564571
    0x2010819060305010b131506120e01020d02030105010801050315040312020403050a0c090c1106011a07020918190b0402090a110c0a0b07051e030402011b0602180618041d01 75
    0x100c00c00406400c940361042049803090541b0600c0746006084540d2110700300220308010104100d202e00401d54005800c00540e0001103121000b00500d00303980c000d540a040f05940040140f09960b0013842c2c060240c03d0a400030580071816007013102d484000075001030b0038000d01203a1074005803005e40445015550210540d4181c1d00c0514120700000380034010008000e01344ac5e08505254480c01e48056070f05502c4006100e541d1800d0102c0e20f131000040741c1c0301d005035000c1110340b0158503204a09809060031039400e4002d0704030a080c0a040041d00300c00d1294503084000840089056030000a8010350100c41d100360a84840d0f440c00000c080110300c03441014004141000520301c0451030301e0b034141c0150311228141d950b03e00c1c129910301c511242c0365401c40080c0d0380041d000001c1005190311a2040c10300369660b00503811141c50700601000119070807030300080c40c240809414503154514a0742650940c1c105140e00410721215010b00111900403607441a081d100706841d0000701d001521074400 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 925567068 1250 925565818 925565831
    0x3030a0506220b0f03010e0c0613080706090303020d031506200d0c060612030801122a0302030f1605040b040f0e0a02031501240507020a0b191103040302010819 70
    0x141c0b80542500d5940b94401c0c240b074440030304c207410103004165034892008050b0608521105c108101500315060424010303003003c1001c41c001d0010004170b006820141c5880139402e145240091a00301061160401c1500b041b00c500e108555440480080d940e40e424404508504014078003c0c80080c90507003540341c4100c4aa0a1849410030000703507805014082c1072040031b84548108280040c2c845005000546072001040142090080005007034400c6c6504a00d0305066005001038512510240c1103c1440c04010030440c541000303562120210071028200c035461441c0c0c140c2801c81030344101400785883d0401c0402a0f591035102400b064020081004540201802e0940e10360050710128000d1240e001a200c48a07a28160241240d205950305400b1a00070800c2901d20002e10100340c0900000340b01c1d500040e503480b2410b6010300700e203103201c0b40c0350301c00944922889079646030110140324640394403c10300c08004c02100c080d240c0a0a000407941c07240703007110101c2d80b40d070480c00445070300c3c040 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 925568318 1250 925567068 925567129
    0x90402040b03072306130905071707020303180129030f0102030a0b0a0e0108031617190e0f0303180a12050105060f01052104020f0d06060e0c0405010203030a0506 71
    0x481c0c4555000020404c02c0f810310040c2c0611900c1d11500810402d1004114801c00c54508241c00095026510380b4090411881c00c144891916400340c13600805a017011042210388414200e141110f8029040240404040743c182084a0440a24141c0c3d061001018210b050f8404000f6601c0c03500c0e81500842d92850503403940c6004000c00455a032060200c1180040c01c0a0494080b40c10ba5903440003541c5024820001c030556804030701c60898001280700c01480c428100d00c0040c140000847c06034000450005a0080c18a100012803500c11040e45480d83c80750f440000540d10020303801d2412401c030031743c6100014034031a080ea00810b6641640410f0001704681034000ca40156000c0e900c043d40c448260006450364000c00d404032881c400350403c0010346d40d140c03000447d007007400075002032050614400415000d0406c140150f884a48694041091110340101c1d1940b042c00700c21081c0c00e15042c070300000d403684005408a16000c0d01c1d90007080d80350360f8411080c020203410000035a521150705 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 925569568 1250 925568318 925568339
    0x1202210d0e0f0a08030d02071a01060e03010c0908150a1401120b07090506031f05040c03140f0403020d0807050d0f0605040c03050408040b16080d090b090d0e090402040b0307 76
    0x2107140d98002c5411000300300c82400c150188805542412018508220919803c64000c0d044020260707101c0717200070b102c0c5400d074100707203011400303040c03541c0d030b103040c200210380c03c0c142911000504042008141034082010071408035460003030b2100030300c5c841c0d1540c9508003104045c1c480c0015100d03298400d01c00024411180385a03039a4680e226541000151ba10850181c070002d03450b2141c0307600000f041001a0380443c444044006804102003030304201c5032a81c012400300c1d0070102002c404290365408a4050340c054800c686d900480d9401c5000070307807516590082d107820b4a01c202c40180245030380071900841c00b840a548252101c220204030b040d0080c698032000c0c100720712030307940a180740c020202e925910a0180307a11a640090005261525111440e4110f900c6003a13112a01948924820001046400102034801110201240303c00090a02e00d913000710160401c0500c1d403100d030f04450100e40044941c9200ca00456490542e9a03490000c24007a000300e003101581802107070f001140c1202e94 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 925570818 1250 925569568 925569587
    0x506070c0e130b07080906040618050d030f0e0a020d020103052a07031413060f09170c010801081b0103050705070b0a05070210020406080a0b0a030804090912091202210d 74
    0xc0d14480c0d11584030044c098030000001d89a043c80f0340c210070001400b01d0900c2d08a410481215040928580d4241e2141814580d050003004002915001c98020001e40f500030301050f00d00c0740c80900041252507001801140a100e40241810344550002d6031360861000102010341801d11a0b10300b094180c10790b883c00364021102200800c0c2d1917400f82c0b0341c00004a080c0c1e084009000c402da2103079820180b043e40c4000900c0680c0c010806a460082028108030700241808007583c0000c000700091140050b022240c16042101c1550200410020090950401482d41f01c401e080000705501d0700041207455125140300a80710f508002c2c10702200304031607808a845854142d090318191280d0341900c0c0c00b42e1003180308203000218400049905803800d0b81c00081008001488040d055a0f203035540da0164101e0f81c07040d8180c2c0d545100040500050f54140341050306a854900c460306d0410046401044410300701074014110101c6042000d83c1c10522048008483c4045030040e0342034200050a0700e00c0c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 925572068 1250 925570818 925570823
    0x1103040311100c0c021306090c0c020f04150b0a031d0d0e061614070915090c090f12030324080c06191b08031e100806010506070c0e13 59
    0x82c6081d4404410280c0c4607002141c2c40c2a622031456510790b40800c52210b0070446152110b6070344141c002001d8500b4411100d511402c0e48414510703158a00412500558080a45004a0034440c00f8902101071007480c0741034900c1c0c001c19039107601140c4800c400400032003008110792001d00034034a152640020f05484046001c1c0d84540010211a0500007030b4083d00700c48061000d0445000800a181030b80710303034810241581200c9801d0394550a90054821001c0b8420550360b81490601c400103540c015040e2410b02410031061082c07900d8090b00300503003180b241c5880002152214010944240c00c01420810740103407110780b500c10100e40c070001c141180b20380750320392103002140200350814505540101400d806100200c840d840c1080e03850710641181c0d03140508035200e0780c1000138121030281d8010450068005000000382c0c0402c0d0721000050710086190310281300400880301c0004400781901ca007961100e499031450300d00f0360310842032a04158130304d47c1382c2400c12855070896010101c0b00390 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 925573318 1250 925572068 925572073
    0xf0e06070624030b16020f060c07121b0201030f0f090804090b030a0803151c0503042d1e050307030b041b12020603060a08010f0606033602041103040311 67
    0x350080b515100c44116440010a2802d849000075080100b034070803050100e0042c0180d40720103001c50070132030504104903008040e4140104070b0100384022140a0030390200f45040070f96001c0c101282d00b00000c440010000e04154a4882c1c0713072900b00c8660001039010824650501224269242c81e02c21a0003d0140e246c819180ca403194402c2c0c40c001070310061140d000480c2d030349184c5500c0185540c1e207101901c6503401200f41000071f90349081c6183e042d5203050148015640340d6060480e5a100d00c00e001104000c605088a04895401010040e40c011603017410190710f1628403030b0059100203025503110f298035000d02c03032000080c03010401800348141d01c03490140203414080501299044100e000704800d482c00c2c202c2c002c0050804a000b07540190008102d010b60ba13a8a00700e2500791000c1c03070400c0783c1d042d48070380040004540500458902040042c5102580e4400082460b0440c0308070300307000c10a4039031200f03003c107648642c0e12810b8801e000302c5920755246000d080c094030005050104074070b02d2 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 925574568 1250 925573318 925573361
    0xe010c09081002160807021224010f06050324360c120a0b04020403031d01031109040b060c030a0f080112020904020f131a090a05060906010f0e060706 66
    0x1042032084603040403203d80c81d00c0d1305007001d41301d04601e6005000220780245521001e00b00c0010100011806d481540b03905c41c6803031000b400514100041a80107d92003070300c5a40030f101c0141c0000a6a90010349400c44590060105410300b00f14000074aa1039000000754403688000d44c00420040c0b01285143c00e4540710650f03000041c81860411521450410301c00c0c890900c0b0074426000e244c3d0054030707070307200490007c40c80300010b41207a2150340110301281d199001004158003210082ca890402420704100404941c200415584510301d9100c0c41795664988030b02c031030741d17440003500c0302a042c00d42102c0d141c0208004c00303032183c0b00d103100e60b00204010100000320011400c14680065a02811071491512150300340011801c882400541c000c090140043c007000707840c80750201c031220301d01d460200f41c00800203114840e80050407821a04c1d0a00e41008125126031b1080741d0002400e00e089032a982520608554680720050176075480b020000e0100d0074443d050700218807a262114061000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 925575818 1250 925574568 925574593
    0xc080307090914090d080709030b01240c2012070b04060207140117070c051c110106031205160c0e0604060e09070612060905090f0c090705070f060e010c0908 69
    0x54070f41c21107194450758041012108954490140c46401031070500b040c2034666200d61790041c03c1d1600345c2209030380e01e0b0b40c810020075455a040a590102c07c243c14000032601685e102d07441403100c015a0107040d4000401000c001d130300c03148400d25142c80c696040c0d03003d541d141c19482e51071f9440361081000604c550000410540009051040c0c00001611500884800311903800c5074144000c000c4000d101da071551240204105125240882880720700c0c3e0500c246800344043d0691481309031101c4107a02d004002e000082150550703406100c590f0030107503245d00c04400c28086160034402c00a110080651002441c254a0b90340d40d03000d41c5c000c46041c4680c6449140c849854241281d69070815070000e4005c02c241401400100008010420085025505c641400741601ca0941d0044000c0e886a4003491328000c0501c540c0180d04801c07680c40c011780c28011030051290142203405000982c100260004001e265800b403c10300c1ca81800070310a40000d06c00240c0000b000d8400e03405035000d00d00c480120b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 925577068 1250 925575818 925575851
    0x20d0b0306011a0307120204170105010302090a1401030b0c09030a0308061503092a04020c06180109210302072120070911120f01080705061c020304030c0803070909 72
    0x103400d5210f1a904643c0d07600070456034005400f149242d201c0d803c1002050031441c1d487c01c685070240e003200119140d49180b040c88000c00000b858062603600d03100c81039605000341810700381120382003030581d441a140c20001504c1482916000d660501c110b401c000201030b0480c1c5200c1c403801017215a0003200c103103481e02020354070007120a4296500040c1991404440071042682c0011050b114084114280d4000c14100c1c0e2003444001215840032040144200e90703165a4040d1901d0b01d40280064000c5a881442207440c0c00b85215000703180e04050020f86100358195480b85412201d0110700481d00741100d200480b44d0072042c0d001480c2d903107500445600c8038501901c4058a00c00400b50103242504139402041e2400200440000420241280340962203106010341c0603c1c009000c4c0b5490188803928002159008a004500600c0b0000305100100115003881c0078803070000d6625610341c40c0403152900e252000400322000402070101031980903034883c0035100d0003442003081401c01d017000d44 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 925578318 1250 925577068 925577099
    0x1923040c08060d030e21160e0402130b10030b0909010e12070f05070602071815060e0f030601062c030c0415080d020d0e1c080306030a0204020d0b030601 67
    0x40c041011000800c0103801e04200c0300c80010f000e460600010940c210014480626440850100302264954203101076803d01c510700360102d00c1551a00f080d840c242c1d41c0c1c2c01265005101030703c00d90303202507050344846d0660044428002c0c014000302201c007407078101400a188400d940740c0111061000504501814424040c008580100400d550007020403604150f601071746003103980c1215004918009070040045030041e05041d0060300305141450302c0c540d0045070005008608900b4000000707034a003541403540003515460f15064407003c1050300401c8050001040c982e4140c86160000541c280d401820402498680e125a920f4254001c80540440d43c1403061258180c0140a002d2400d1609510014454002028800359155035905441c10003031102151405600042491004a580500c9444541c1d078219010702c140110044601c2c03c0d4248a0402402140c0010108840b660308000031250194018000d5542e003422a0805001c0c140c1049168040d02c1058004110720440079100c2 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 925579568 1250 925578318 925578341
    0x207140603060a0302040f1e0c020609072706080307061a040b03070e070e030f03030709300318030c0e070203090907030924140906070e040b192304 65
    0x70f8001403c580811000340011034848001940e1034001c0d8074030381e0a9810381002c5804501c0002030003044544040d0421400500400f07084d00007800a000500c0c000510f41d01d00149560030400003490780c901d000017808a070300100d003030344001f01d51181041040e4010004c0940c1a4034950000e03944001404156481c0b04070f65580364204c010140042e48003901855449280e0b40b8044034440c50701c0001c00c0c200502202c140c403c039040081008003194100007034400410f54010409601032030914403090902e6083d040c2060a002500400285071280d10160209120b0b4600011a1a503078680071002100c00c0c42110f20f030708104400907100c54008020365002420152003504140d0710050220010800030200321040c0c03082041841e5400ea0310990742c2d136200200c080c00a00d1040c192030070201044028444032003503000408000d11036901c0040c801e140302c01078401049091040002851ba01c400442c041c004001250000840c400f0503040c440d04090b0900d00151240020320034070040c0c1d0099581d0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 925580818 1250 925579568 925579579
    0x5010e10170c150706020c0303091216110307080316060b09070207060c0f0c170f07050f041a1507030f17180a0b070206061c050601091d010903020714060306 69
    0x1c400a0781449101007241403209240580341040f07580c5c850040760440700500400340d1000c005c0009000c4100070b03104009003a1040c0d2810300400303602e50f600c1600c0100c80100baa0f48282074080d080e4404001e00009000c90000340d94035501d41d03141c41c00e0300000030304069035000d0600304040c0080c2030010780d0174012506035002e0000d2904010083e6409691400704856060115540c2d4001c60036510201002e49079943d8501061815070031404e01d820034400c1c0004880e00402402c001c1e0b5a600d40c010000e414040e9004140120031480002030000c110700b0a6401054610309000c0165683e001000410311a0315104140314a840c4111103940b41041450010800c19011901540c1c030045a10392100700e107402c44941e1034155403400c1c0210000e480c41d50150744440140207003843e044180a40604c224501001c80344003c1e2030301996840188200c45080380d0f516000c0d000c86130f005a0003010141400000d0005100510780299212824828000c00140c007450b51080342c640031040700d0150b00c00510 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 925582068 1250 925580818 925580833
    0x30d052a040308091005070b0c03010e06031506040f06031b030212190204090212011e0b040e100207171603031107081e09190e07020105040206181305010e1017 70
    0x1407100c40d1190310358170010f114090002500142441180d90705ca090000d111350b0310b039450000121400f50014080501c02d0304200d030354407900c1e0000001550b200c03000f00c4002c203145050324840c0f4001c0132075401c06050040f400d0483c03a075060404035107804030307031095a4010900945280d0305850791038603901c110002014480c1c00016141c150028040107000070880c402001141101038211040c8507500031f01000748003a03075081c1107000d03c01c00e4100141a202484032549540c0340741e4580c00e03d50aa01c1c80190b02103070203001e0040c108511504608188807050b0f0368880307a100d00084050702c1c8002c80c0041c0c103000c0e9040620549505072541c1030f5005055a05116821210503800c14505044140c0030605005441e050354a00e1b03040d13270780d4a0101d0110702e095400c1203a000840900101000150b80c1080300380401601c1d06411a5151304000c11a03540d5029103d00051142c204110700c110328604160020036560b1089058502840c10074049076000b42da2030007280c072511100308021900d50070505 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 925583318 1250 925582068 925582087
    0xd1e020721150c081902030c04060804170c030c071a030c0a020f1b0a050405060f090c0712030b01020118081b0102130b030103050709060509060d05030d052a040308 72
    0x403825280c42440b41c44150100000600110380d05190901c2c0041c02200c24000b60180007421041d26070b240e00030552543c40d00000004840c03240d0301c80c00e410044d800e400a0306015078035860b402c4a0b1141c2ca0030755940c42031000c1c0b2580d80e0308030700003140103800b40b40030000311015401c040c0040c1f00301003201182983d54420783d00c222a0408061601580113031040380191810074484001c01d004a5a1150104d0780a50300307101d01244550001400790b4a0075050216540c0c4650401c020704604448114996540d403400b15203500540d580108840724502800c41c08940581101070003003000e07030003000700019503410a40f014401d584003914a0364100040a645070404410b6644118020009403421490102002003a2030310b61104502520103c018000c016082c44140010002443c041c0300c60b60500c800140c07102000740c42c8a10071800c0321054800c1043c2401a604602000e800c00c02c4107141294810444100080581a0f04c40e6040c1466800e400d1b44000c5e82c1c103880d045910507003003100d41d0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 925584568 1250 925583318 925583369
    0xa11190f090506060c1e0d0e030a0809120d09030605060616060b0f0a03060c2c040506280302010e040e071406040308040602150a140a05180d1e0207 65
    0x42d0105070030043c10440c1c4010411704212200030f030280014940b103c0b08003403803041d0602007034500100801c8075034030404500e0350b400540100e0240d0004c6030702c0d603180a0100014054880040700003118001c1c1c4010204854201707613240122401f604041c00b2607a00c03034080040c14416482c0085c042c0e50640710103400700301250712103224000064140c4144044140010704420401d0744111101e03030b180ca40c071000c41e962009850b403010b04100058845801190104481c0e01c2ca0000ca090095903580002403056070b03903008944059041c103511028901000c640b121210341c650200364041381c61015002c0b414203142c490901400306140c0549982401d02031401400032065445d1680b00206100210100340f01034000d20042800303800800040b01094034801c05408010a849140751030f1203070f2091040148404540c0c80400004002090b998009210517102c80d0020340d40c00c0b902c42c0b0f6220042c0e85070496201103c010486080c00c01000c600301049a40f0019405036103182d528490301d500156805 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 925585818 1250 925584568 925584571
    0x402030c0406090b100f08180102090a090f0606020c01050d091a13060b0609100807021e0102070c0905091c031b03050402101404140604080a11190f0905 67
    0x181610100380905000805480c103540000d84029070f155241c1c000c41ca010444c0e11000c130001e003841d610b0310b0003541028222000007414042801c61429400c040d54078291f04842d42e2004c01030040300600c0e20340c6043d070020210701078030741000e514003840482c000c1c1c000102d4002040c0142d5a451a106852105901800c1010780031954181003c410012042158401900c0b5410301c510141008503181440b4055510521409004003001c20101c006516982d00b140300c06041818614507544a110040b49000d04411812000d030f40b160a45592a14040d0014518a4050ba0248590a0b00c60b11030f902140d4050760701c45c44a90214503200761404c0b44405260a40c0458180000d200610f0030303000b030740708060091000001c0e541d28100411450042003a600000c0e00780303001480c18542211010241c4914021840c083c540020341c1c50b0240c2e00e100458018001c582d0076518040020b24140c10f01c100303040800383c45291040c1c0502c03456000e42241d00b040390528616403a140c0c0c41c002c00d20009103070 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 925587068 1250 925585818 925585823
    0x3030a050a11030301030305130918030e120a03030608011406030d0305100f0e010515180f030a02060403060e19030905040b010306120b0603010e030921070f0602030403170c030a0804 80
    0x10b4614204071241410300245000354040d4075000e544d0040c0440452003200550405400780b860306400c00e0364080b40c101010442a410304160b110130116000061103031601d01d10741d0100b8403442181c20109981900710f04202c507000002400b01e54140d00c0e281c40d2011044402e25007562106045601b078a101e9007003641c10150943e40450703004c0d01d41413800c094003500d41002441c80c207407100400c4103040c850343c1c40500408882e004c1e4204070808044450904030581018031030150102540010340c1c0502030100503e80c0186180e5903160340b0b2800001401101c0c0c2e488425004081d0102c1403600f8048149030481c0d4140d40d10403099040208000080c800d80102c94101555820003085144400300301981c0280501a410761910300a4201820f60382d129040d585141c10a02c0509441d840340c01d0400a40d100003040c1001012030140198500207075035001c03661107921074000217030741600031008209807402820100b18420044621959900c9400400c8000b9031041003464821031143c00b11541292 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 925588318 1250 925587068 925587077
    0xe01050f180a091b1d0f01030e0f0a0501060e0f010611120f09041a0a0308030a09050a0f03021915050402030a02120705090a06060e060d0612140d0e03030a050a 70
    0x40034901103032a000720350300003602c030b04d40da140103903511640c4c20441da90488852070042c01042c0c0311084080414614170106003c0c6c40c0b482a1450640e020ba0480744039200c80004a8044900710b400c502e940304403032403060315594a0a00041a100e98003990140702c0c4132459104000f51f4a007000c1121044441081e600c040d0107800000c0c10300419403c0107050445090040702c1d140c08103603041200325444161241c6031100d45043c0c07046161594100c100071203400095080d20395466168480c00742501800090440c001c3e20403082c1000089406401e02c6030007982242c203c20076a0707001c041d01c4984a1005400a4071070020385990507015004039900501c080c05a40481e24164045105e401c580c0b042200d4503004100e050010b424064400d0398492610b480902000e450708502500308000052441d0240d100000c3c0c803104041c050300144010804100c40315120041d43c01c00842500007a540c900c100d0043d9100c01042034801c0540410315103004029510f0300040c0f10701540c6540c0584884020b10 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 925589568 1250 925588318 925588357
    0x91103220f02031603030e0108011a130b040306090b07181a0d0e01020301140109240c0f050309010e06030f0609060a030501050a02220b0f03060409080304030c120e01050f 75
    0x1070b00c0c144450340e461078801840c1c180c46420341c1b8002c0d1501e00078517406410402814010081c2c40d0003000340c518419114980269103403010b06d14500c1030349846c1c029150402001030300004000d4950b01c000107490013203040810644411504a4403031a000710004003d0440c090240300c0c248000c0000c00c10801c2c403454003480c008252810005641c04021604400d950100041040903000c1d030702c031891101d007460858060741c00d000c0d140c0703402e6000350100b07640d000b104a80100300c280500315105515420001c8510400710300c0c40c1880c3d80b9808155503e00094032483d2078071550030150242c07805606404110001643c8000602c904c00700001c2c1865400034000c880040400c1d801e03c00d5034050300380514056030321f9010030a01c01800200580004d002c0b0b9026808000100810040e1041c40003070006030b507a81d03280e010005010703140805024100d004000103020401da0031108580c0d81c5031285c41015820304040800380c40811a01d100c0f00c0c08508204008419203105000070560801500801e0010 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 925590818 1250 925589568 925589573
    0x50f0106093014120a09030602030601140c0c130603020303031b0d0e072d06300b01110601050f0913051c140f0d09020f03030a09091103220f 62
    0xe10304202c152480700704500c192100f284140500c000d0b1080003010240350000b00c1100500b4103481d803001920300b543c04400b10720b6981c803427040d6064030800700070310a40300c508440300c0903200c2095040e924419140c040d040541c1ca0540d009207002c40780c0040c055401d6980d010190780c000c030504000d0004804040000320720003031303a501c140804c1820000007042c080d41489070340343c100301164400348509000301117203101d0018400403107000d440d43c910b894030038080b00610240d20300800c2036074400a4601804404540700071903215042883d800d9888108010200e18035540b107510a004054100e50103041c40107803824034502c4c9540010380201d40d40c03540d0049403600303810301e4084c0c1321058505496843c09203016501a0442d0801014109124903041c515100c982e41449a0759040c400551107040007810b46d910700f0118901c800300039050301e43e0f074004514014443d929600405160518220f81c9650030441082620301c100554010100000c44102a05884002d124001c90b990030110000500 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 925592068 1250 925590818 925590899
    0x6141801022a0f0312031303020a050628090c090c110109080415050901090e0405030c0106080120071208040c030606060f1b051507170112020103050f010609 69
    0x41800382022190010100c902040081404000c0e0181301e030303104408404519034060112500400014100c01d1007104c685800d03420b0150050300035015020340000c00a0010b01440203803c1c201c800014011140c0b10b92045c04121680224050130003c80c480c424000303d00540c0c88041c2420f01400c210f404250402c402900759441b20104031103443c00402d0401000308042c0d40c030f00d0f513070320541001b5080c14101c000081c050440e03807240510740d444000c00b140074043e041c0201c0b140c03241068000d00c00191182c200a002e42034481a56242da0400c1084000300c04c0010160390206622040c04030316040e681e0401c071000389010f0020f40c0c20148200d400000900c0c0352154200905030360300d41601142542c0b201410007c03807004201e20308840780b844400001c4c8042445550131b5011081c1e0070380c0c2c3d101e03000115070140c4654a1101c030410410700204581100c0c02d11402154802d1f07031305101540e1580185000c0060a01c20480440d11184091250091900070002c07101c00380900086e070f00104191010 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 925593318 1250 925592068 925592113
    0x2210405190302010311030c030c0706020d240501031a0402090a05090f07030b0904050a02130222150f09090b01020c181603201b0708070801060614180102 68
    0x84060071111001c00c02c550301806120170820402d00c0850445c608015078814a05c03000b040f560042c0400103007501002641c2c0e041d1782c140001004204501e00c01d106000c850107440031202c90360300c801032000140a600c6030040360301400f40000d0400080c0c503054148070180d00300c4a80070354400c021a0b40415103440701e5503006c1c0304250150100742c603406e00e02c00140031503502c028944d004108843c200004034200069002c1c180e541540e16400c8030031040d501d80e000f4001c0d01014800f0402c800b1040762414841d1100c4001c3d90108900384803003c000e00303400c0d50a0011004900c02240e40d4403402c02c01c4d90a1076000c1c41001c0341c107005940d600050306000420a82c0b1156510324030f00d1104003070001e03e00c1c08a486081c00d41e40ba0034204000b400700b40791000b8860744c1c10340484111200069074407101c24201c80c441c0c4c0011400040f00c0d41161038008194540340c080c080c080b890361900c0c00018185218410400c2c03074402d109080c034600703001c21a1004901d03102c80d164605604c03c071046101c44030051401d0a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 925594568 1250 925593318 925593349
    0xc071221080f09010204030201050301030201050304020a050405010f030b060a0303080c0a051c1b02061504090507050607050a02130507050d02070812090c1e090f071e0215011502210405 81
    0x30540c6251420b0035030401ca8028001c290140c1c4180b00c14001030741c1000c21641965024201140c482c0e41c3c902c002035a1902c1d540015421508090000620940c00b00f400c1003980d1040800091079900c5009104050003940b001500044240d00814000310b0b00302c000702540700d036515100c2e1400245020106500c5091802a218255600941039880c41d42c0c83c544455100c80c0c1c80540030905041240d903d0107040d060000b4411f654070b006100801400f00824002800701510031521400ba90500a8941129801c26030064082d0580c00100f880e2a03c030303051086205450b5035007000003065000000b9080010211000901008034441803a8203298161007001e00304001c245007024a41400f8195510320030040c040441c181100e1100e80d1001541c0c0d0b8410004401c010180d980e00000b148c034442e045031064a02841c50701c0390030825602241c00c0c424010003542081c091390742c0304130180c5d4442c0c5d14802c90700107800c102c4c02ca2140c22800f0b000700d07010044034216181020345446c006100c070601074005 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 925595818 1250 925594568 925594577
    0xd0203061c050d080105100221041220030f03040311012d0906050a140f0913060f060c0f1202210d0b030616050c010f0e0307030201050105060c071221 66
    0x8200d140da4410300c445c0c054007003641c40500b60340150030060340d100306000015034030500c60203090b5955000c2409850060a840ca540030169649060800c80c1644ca000555044540c0208655080c2000034868240065890056250a1850b00c840d0f41c020244400383c2e04018400e6403070441482e1454044211a850401c21041032015210162110340f00e90701040c00e020041c0140319492b50400592680d01c0e40c0102c50540c0c4070744101700c1d090244288042f4984c424a800211210720607a94802d81c01e980450f4240d0f020180c6034902074850015020b8000c08149126900c0000030b00a205a020349580e13a0041360744031300c0814549a124015a41100f101480128802085000d6400b036228081e00c02c1e0302034030403405c214842d807005901c1e06200800340400090480304070442580300c0c18284641c03c004000a400746100d003a00c941c40a1410b030019070030000041007501e070007002c540400359080001c1c254907180c205a49443c18440b030003a9010200c0c4005080c8021002c00b0040d5011441d41c2d5 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 925597068 1250 925595818 925595833
    0x5060c01050a052202130f051f051807050d2c0c0a050607030f14041418070e040e0c12010c08100b2a0f0f070b030c0d0203061c05 57
    0x212030046036801000b50701100080380b13900c07401d80b00002d190341c4c40780d80503961404650340408048001e0310110002000c1680f906c4104880946a40600c4012003c0241c0c12607589540b60304000030b80c0c1c110f04803113802d80d0850021804090103400100301004240d5404590156034507150100700100201407407002041021401121009001240010b44129a8412118200b10110340c8600850500600380084030810062060046000c03030343c080e402610203a80d443e22500070004052204030001d018107880005905d446010820080c4545440d9036200102c0e030001d01000050a01c4224100103409503d80e4203c6544480c0001c800712a8500000306e1900703200b00c0010030103c00104544418511020b06200c4001340b8030803201c21295400d80340300e04036158919449001780c04003a00069119454040300002d001240548202860409039105103030f4603a00325005101c102ca2100081508001180c03803c5c01035405903070455000740440d0040030040d405071840d1003d10728103690356882103d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 925598318 1250 925597068 925597081
    0x50f0118271b080c040f080d0305070806090a0f02040e040f02030d020d0f03050604060e13050f0a030c0212190804090c050715200a030f1109060708030a0605060c0105 73
    0x644115101d24104040041036400d00c00c9100200c800e400c2c60b000c0040390000714110401d1001524086e00314580024295a6501d0800742d46004280c01800803a0070a0001400b007400ba010382c40c49100040d14a01095994803100c9006081000760700c00829402e0001281030321007110102d20440c4150b07100150300b540c50040602d840c2c11603d41d502194085200c9a46099002c401003060008074180030511b5119071b00014098880d54200c00381221390641041611545003480090081c090010303a010141e0600c406c07070316a111009e0180c0402d5070304032500b006050200c204083c10380c810094920303201d41d504403a1005019404141d400c1c08000c1024054602c1511660703407200360600f840d80c90524503a0b940f4146000c000c01c20342d640ea54607604070f05400c00945604c040d1403071348040c5036551129032002038018414602d101c285245031004014090090204031000840024405400c1010301c1c1d840304100d40c40280129906915030000180030384034100641a02c16021002017007502d00721 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 925599568 1250 925598318 925598369
    0x210050f0c0a020a0f0b0d020306040908071a0906010510050c0c030303040311240a150504051303080f090a140102090d080403020f2e030209060304050d020f06070504050f0118 77
    0x10b0f0058a00c5d00c00d4181c00704000d081103c1250526203201030050b84036651040018001c02c4445c0380504aa080044c26030200083d80010302a10481c4c480c0c0010030380c4a01c0e094a079205000d00800f900f100007000b42e0a44036020350f01800c03280c5082400c0765900003a490200c0c0c295003007654124085400d0f40c1922003412424009200c00214100200c490801880081c110110000c1d0249041d00d0759103035944c844240c00400c03207000e0800500240032a041c020805a42400003c40c2580000c07000e00c0030503c0700364002d8240d8001c82442b0001d040d42100b5858001d14020101c0980b1000c3d9820410400c1030b454021601706414060749980b6180ca10310300500100c5030012080b02e104000e00121900816514000b260544208503001031801c422901e050b8024445c441d50141d00017004020003003007002c00039004100b819940e003620901c0c80c814200559619064429102050052205000d5401d10740c03031503211407105150002100d10300030203001c241003941e0000c0c0700d6080c64600305070029421 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 925600818 1250 925599568 925599589
    0x5031b131d07050f162916020105060609091e040b0a0e010504021f03200706062c060105070f11150a0e06090a03050d03020c10180210050f0c0a02 64
    0x280c1005440c080e0300c40ca41e02d01303510441810714140031149081609010200505540c2510300b44030020150829000000d80100202c80fa00c0079101140d18001a81d44180143e030f0244001401d4141002550400c0111004000306104c0240c860b01085103114024914114021401031900c03900909208007288140c801c0c03004014030580c10b003030a2100588034041079181c0049000d00303410b030b0401151812000f030007076071800e40045040603422826260160004100e9148101020031849642c0d84e500d02d040c0c0059010303a603500070400c0c01321048450b802003c1d030b442101450010b14208442c1c0da8203a94001d00041500ca00200100002e4139042c078034142d48200c240402c9003814480441c0c0010154144219290f0040d003002c9000320081c1c45110042016543c084180c55840d40600b070000c1c001d40020228441c6840381c0010607100354994407800c040c8000c0d807a50b8610340fa1a0b40c0030b009030308800e0701602c3c0800004200e810411150100a005503040c0140030340010b1726540100640d000a = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 925602068 1250 925600818 925600831
    0x3080f1f06050307080a14040b070e0409060b031c090b03060607020d050307110a050d140102070c0e04030f050f0703082509060908070b092101020a030506090f0705031b131d 76
    0x1034000c0403d843e00a01203a1640180d10040c0d50042b40d6400004444068005600980141c00c008a090410070f4a801c41600310360150200c1d10000004100102c100d045090a5000705280e0070080c00103030b840c10000d50b446035002e041c56140040701c1c0c0c003080c03c1e2910918142c1d51908040b541e0820843c054400c0c4022420032100e8440e01c505100c00111407034140c0303100a22000d00c0344814907400c80c0070740691740f03620b07080910154455a11300d569030a265045800301c0c0010f40c01907605c1030481c043c90984001c1e00c0d409000e10b080028903030b0141e481c11005172205c03440000707003002c00c1c0101a0b4440d03a034102522540c2c40d090f0003880c00c0800341800c07034a41c01461086d08680c0f8180b10039400403017903032850201101c40040410b42061044075054420740194620b5000142d004d403010b400d07421950050f031090f1a000e0003503031000002200344406031080310001c0c10810106640f0080e105110130310074144c0802a24048029200390001c41542d40004520139000f00030b100c91540280c0c0d0140e1045 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 925603318 1250 925602068 925602071
    0x9090e0604050d0c0302010603020310050f25031802120c03280f03050f13150201152306040f030302120a0e010c03030e061008010c0c03080f1f06050307080a 69
    0x4265039843d0f140c05990030101c00300041c0312061424940700350840d4004507006000e0307c0d03440a48000803800f81400721094010b0300407440110341c20490320046c680d001d0a030002c4c0304c2c5a490142d1012000f4020341032000210500481c800005691900700c8482c101001c10700800e01000e4100030306080c8490049113421640594068101c6207841e00162599154400c3d01010824800d03c0e05a6150040c80a80b8903070400201d4071110304624150b0300000d60f80c0402181c06142c0510f070040b07080c1c0c4c0c010b18082c502c4010003901000500d110390054860000340031911090700c07072190701140854000f640002c9016a04a13820030038141c05104483c80c1c90007515020340381406103140a010f0070355191b2001d04200718403081c07100b454031070b83c4504c26520b403080590700380b410710f0340d41803400c0011800750a0840d40b90540c0b00c1d4005000304c03492802ca030b03490340398001c050b6129140708840c810002c10b0340d203040c403052003040c0003210000901c00150065845044d12801c00600091401c00300400440d03409 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 925604568 1250 925603318 925603321
    0x30501050c090a140d080c0f01050c0309150a0605060a05030a050f042004090204020d09050706031b050304060b041407030609060b0711011728020a0c1b050a0609090e06 74
    0x20744481144030301382d418140440c0e50142d00100840c05070030b0000310180900c0c201041c42e00e52010040703034000f0344e880c0c104001d00071900c0b0107101c80300324031050351880040e502552060926040740c0704803561110300c0041c001403c0c2ea85002152280d4010031540c00043c3c8004201f1400140601c5080e0700900c8400840605280594650104540c21240ca0007940040300303000340c1960702d603040300c1706041c0d0180055459104200040025111812041b40d06005110380424100c0c40b030301c03079101b1101007200b0040000c0448481501c4503800a84180c601a464604581480d01d07030340204010759260840e825518034040740d0040403140d480c0c0002c28a0342c02e05204100c2d08500105a90095406c510b1201c5280c0710480182d9850840000041c07814003400200402080c2e201240014070040c45041045d801c0e008260740101d1013000ba440d40416005080080800c0001c400c01c0300507412985001d24164031840083c4407850264000d00000b0740300748040c000503649018401c660000003004140a = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 925605818 1250 925604568 925604587
    0x3030c0c071410050706021c0c030f2702060c030c0706140c030306040513050607030c021b100e0a0902041401030b0d050d0e03031b030c071a031306021207020106030501050c 76
    0x2d4964005044100a8003117841418410941e04543d652403002c124000e1403c47c441e04074010b072a0700c0342c004011a14048007601d0010b114000c03a082000b101582c4d50620288041c404400030744600c090341c201c8802d00440040c01e004000400d0500010401081035900d8140002c1c0790000d000c1d802012041c052044840d5042c1c00000c4e281c02c40b00848001c00d140c1d2b201d030f00d00118803500a20141c802e111780700503c403186030554800582a9520750a90f408d808400144100c00c80881003a550050b00040b1707000300041c881c00019005500040481d80d200341e590810200343e1f0040c1c2c0049103030340302d490b070600b400d9038241c844d1020444040e45c108040d2041d540b00c5645030748981c01031070240f02014459105607a0306108640e0460036031680d0502402c50b00d40c243d03613250881c1070803d615108108000c20341e03849801c81e1403140c586110b07034549941d9a64801d00740c0c0b100c0d00007040301d440780c00780060380f11000984e107210b04c150401c0d8000101c1a24608010382501e030042e00c80d4000100c01c01000e200d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 925607068 1250 925605818 925605829
    0x6050406060609121212020a0305070207090605031e1e0c2713170f070b090606031b010c0c080a0b0a021c0902030a020d030c11010302030c1801020f03030c0c0714 71
    0x80d4144c11601a8444d032203c21025201c110040900046c020b00c0060300b1080507070940d00550003465a83d080300c41c0181c417020741e1401c8170540e0090a5056200d865000103541c014030561b0803c450707a07020b80b41c0080c403280c5205070014070300841c0d251641107030810001908001500ca00b030000d10840d9260070702054800c0c4020100058000241003010010035403d0102d040c408121005d2142e410941d283c8100c0344400164200050855052100c00d000c07580300c07003000a5643c050b0400601a200b1062409401c044c00d03181c2c09000c905001e01101d0307100110f402840c8080c000d00c80d61000c1c0103102c080e441c024401c2903004060b90041881400b808001110080c0c0c0d20458090065001400980d10700009142a40d01d80d0000e52100340360a001c410145e101c011030a0080c440c4024800c00380e0042c0044d01640401c542c01c1c030003e1028003d00c1c84201c08901c0300b01441d407060042e2500c2500400800e8116481100c4801000800040c2e08c0f8503440208072140083c00741d200d03c0d00042e001403000a0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 925608318 1250 925607068 925607099
    0xc140d0c090b0a03050d180b0c03040b0307030b0402040f150906080105010e0102010905120c1212040611070605040b150f06040b03072c01080702010504320a06050406060609 76
    0x1001c1d60340c1d000700395200c0d01c604100c0000b6641007001c4407805420401300416240381d9448020341200c02c006c00084086910068070700f5030240d0405503041500b8850040d0325504020103036410035031030382124002034480384000e00203040c40f48082d4280c503040408201058206c001130b68100300102d40100100741d4443c1c0c40a042d01c009182c0708806a00d075900403405000c0303c502c0a8600c0c007402c000d940404403e80c00600030b06500000350350303401140c1e2010100b2401070705141100030303604200140008113103500c00505040d5003810035003480600e8480c081121800c83d8101c906035208018014a1324021490030010301c42100c400d04510400001302e100380c00382c0d20a81142c44804004204018013a0f81c1c0315141d03285940b18080318081d11240c103021a03140080e450702107010100400c41c440d01c1809014403c07030b080388614070301918044605540d94940c0c1d031000d0841480010314540e0307040a001020b40b0134010701000c1414107060900408907074195001a06000e08003008103c2c4220921410 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 925609568 1250 925608318 925608329
    0x8060904121d06120106080618010501081e040b060405010503190609050f160e0106030c08070f020c0a09021c0c020d05031512011401150507080c01090f0c140d0c 71
    0x59000b014400d0420380c1060090000035400100480d503c1405202030705014101c90300c680e6603084031b845501c244031600b440d80085407024a100b00050120394007414840b50884415000c0d0805004400341d43c03084064140d5084075000c201d04140142c0d4905805114090041240500480f1081d084902001461440c00401541e128420642401001d00800894111010039568444102030b03200c0144079081c002e08040c0c007503140011a030f50303100b0301ca080ea07100c4941e00c8035401511070701815502100124401c0045200304180c1c440951103183c8080d0043c15506005a201c01c1991082c011380c0741204541c1c58041e1800f0b0200344103650002c0c44550085403814050b035642c84882070480d100e1170941205400002e1505203203401d0b9815400307002c0100040002d50707240d988810200740340c1d8804514007000220188004004100480c005141c01001580006140d052690360340304000f50b541e900703480d8a881d8080801580b144c07001c0440580d4821070f10405480f4460b0303140d4040301454060f0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 925610818 1250 925609568 925609577
    0x90c040e0a150b121507020109030f180f080d110a030c02130f050f0708070201090206093f0f03030c0301030b0606070530030c041e120c03030806090412 67
    0x1d1071140c0d065035005441d400c00141404c1a100c040c11001e80e910320003071541e101a171608100083da818810302c90460001c0e491b980d0342c08459442041203826401c2c0e455001ca00404024000420310046182040184400000f1f427015156140000e80130681002603814a03410a004150029510154511035294119100503500c02c0c242d100c1c800800c42000c0050390246042c0501050800b08042c05118200c9682d03140340b81d0b43c424004901b80c2d120f000000703402c488107002c508158984108040110360305e20760809504038400d610310600403044032103e800100303a05014407144800f84514241507495000441c5541000f40380e4000c140b00502c40503080140c018040b4049603111021102003d801c84211400031030b81d10030804002d4035a1060340342101c441200300041000c00006d80c1d104000d100916428180b802c00d48560355201c1f41c840d1940c48082441c08109082650750700c0490314003544e01c01209505511780a06002406844207108241d48810000050058500c00400c201c0900e003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 925612068 1250 925610818 925610843
    0x1b0705030a1112030f040c24030e150f1b040b070f020409080a0905040c020106080c0d030e0d060c09061d1318061e09020306072f06090c040e0a 63
    0x42c030b80c02c20408440e54124103d00109104401c40e003541d64500a900480e03202240581c4d86000c2070900d4103048600308030040160480e8100f5000354001e1007004aa00203891a5134031480342c41521400807904070000308150f00a0202000800e0640d0000320f00d10142942f426090540d85c003004d009440c8020702601403000c640c0219101c0c4d421640c102640103841e26240d002202c0080c00b9042c540c080c19010300d2620b07008540041c41405000c3c1210300c04000780403034154040a10645404460b400d4007031002e1401001c001d07031919807580440c0d6008002c0002c1c4008180b10050400c8400d070b100c0700c10080c1ea41c0f90401c1a514a42960b40401c4003151258a00400307841124064a1800c075000405102680c0c03a02c14044244c2100e442d0548104840704c1d000341041050040718501c52001e0342507484440006c0e4014002c106c103601243c0c80c0055031100d9038507000038110142a418150090b03400c0a0b050017035640041140c0f8402c058215002d0003041d00288149035030324030b200c20181c000c006a20 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 925613318 1250 925612068 925612097
    0xb1e09070e07091a0304060e0304050607080c15070f0824060a02150106050c0c0414010b1602060703050c0f060405121c14040510060e06040207020301231b0705030a 72
    0x2101c00090004c042048420100c113039040700c868204507030544045040641c0e200180705c0100859060340c800424060801140345c65135011500480c032882485e00c20140b0001d002c0d6551010a4818403599487c10748903560850b0042c003001018101110314034402414014031180c045200305d0301c220a03a122500c0b081c00b00c1d4120318004501c010b601e1b01c110035500204510381d00c0001804480c00000840d0b038111110014003003140c20410044041e01c0c0108018003050603076000a0620035041a0310352441d01d425000140d00d9800303c00f0460109900041c224103030072043c051001403142c007a001d00310301d00c0e044c0c640503100c070720184c5000703020301c0001824803030400d5410005608000300002045240c4080350100c2d0f1862003550103031028403541d1340c0d501000c2843d001d0842601c0f0042c84000081d260203050001039008180200e0f0700d5500d0344029480400300b01c504613207505c10106441d269042c503c041c0030354000c1c204403120301241c0800414000c24400412181600301c0340c134101000e000d505 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 925614568 1250 925613318 925613327
    0x9041d0d17040c150e18090d08060904020105160516051201020c060c0d15180b090403090501030c03020d0e06041118011a0408030a02070e10060f08040219030b1e09070e07 75
    0x43d103641c014006c21050381d030402a07244036842809030b0011201d11011009068800300c40444020360b105c01000f000400552080c8003404000407440030b000c0c058115a590305c1e081810740c000c02e042004020400300418038001c00d1002c4051703a840d0003103248c10f40030503041d916418010911102110f000900349144c0700d079030340208020040507003c03008050b00c0f00c507240c4640c0e5250103080a902e0405260080b149032041070719010f603070303da116070b40181c1c900801500502000c030b40c0303442495800e0142035148451405060b00c060f0441c00540b403541341615100400c00101042c150040d160208091401d904246059040d1040b000810200b4030184044100c28850354101039801c1c000030415800c400e03000902441076401c94010319549994031f04800c00810400d00c0b8034000580d10f014030700041c60142c461190040d0000e0084e451315140b650b94040401c845070b104884200504041000031990002042d54022081e0000b0409007042d000076030703030b03084107001d59000c40745803101203403015026 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 925615818 1250 925614568 925614587
    0x1b100e0609040b0a090f0516110303010e0c0d0e0d02070603060609052e020f011b12021803030a051c0e0a0803191409060916090209041d0d17040c15 65
    0xf8017000d106040c12081300a02400054403e041e09154216000c620315004035101060510044025410761f0b107082d0015003940b60140170204800410800e04c00e4180850295040b00e81c403840c0184281842c400000307192240650201d02090325200042c00b03203a078440c0c140821108121000300341c010302400341d00319800c000c000601c0c8080c11417000b02c41d1181c02040900e19407440c44020400c4c85421041040055480e0f40900f00007450a050040084140e5014081414100c0c450842c486485008645142e0114050002090000c140662020910b114030346d88464030504c01c4c00020308001101e56101640c2e60000c06200e0b0110010340600300c8035a102c11042c0c0203e01c1481640c031044041c11020006542000d0540a45e500188503070500142c250303a02d40d040d0038107540d401d241c110312400a400c01d01c1d8860b8040c3c0c40382c00c45802c1d8150080b40d0040240c415007d448040c8444101819001e10301c0d6042d5064007001d0100320124801010b40422200051500c000e0200d00b40012541d0102 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 925617068 1250 925615818 925615829
    0x60f090d0e042403150b060702010c03031e0e01150f05010e0303160c051f170c0f07060f18080307030c0e0409030206043e0102030c1b100e0609040b0a 66
    0x1e89040c041c11a18503010010f080364080c0503840d5540c0280006001550700e09003280790410000c110010055210b058148081d901900d00001da03451400c0300344100500c941134004800d610340c141d41c86021401c1c42911100818118030304501d510701400412501c88500c1001e051120211010f19107032801d1045806000206041c4070f05045507103408003488555000d01400f44004035800d01d03006088806901007024a030b00c0c5c1d03c8860051202c000c411850090107016100d00a004c0445a04003d502400c1c5a81c400c130070108034040c1c15010b00b07085511b038005400c1c41001d42c0b8008030101d107030382088a0b00b0103001c3c40e010400100d0b0b0300c0269649040340100070342242c5440005000d05501140c0c19000b103102c2c40c03122240c2c0420202440d040b00c58824204007a03100e07807580809050301081c1c0e50417645c0060054030b0806031504001814013002c0a403955003180389d0304c110203892814088842240c01d0340c0c1840c404402410300400c4040c0656400b060080342c2c0d0b03040880e40c40d82c66498100007001d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 925618318 1250 925617068 925617101
    0x60c1b15061205030d18020f090c16110405060d08030c0307021603051606140414030a06061e09050f0105120a0602031e06090609060d1103120903060f090d0e04 70
    0xa282c2d1800d240e40340d02c0f040c20358141303e1a100d00c0c548191044c183c104c9209030000c000c803d8124801c003c000c10717014007074585052210108005440b0140e80d40c2d040d00c40a008062051841c0300230401c0c0070503207000518041c42142100c00746000a01800c041e00e0f080031801000300d850340c5c0c58560591911034449500d0480b42011503001041120005651601c0455000c101122540d5100103403580d2444a03111042c031003061006002c042803000c00080006402011901c103070780580c0721841100c0b8140c00400035952080348a01c410901c00701d0120040c100c0d54410803140c5400600486c032024103001d080c0c41803d40d440d140d07000d03110820a50300d609400c80002c550f06e041030354660044020200e001c0e03c1d0200000c001462602e0013030076003842030001800d0f00240396692002c008128a03201c03c2240ca2072000102c4001a07281000071041e103010704028503559150304403c0500e401d03001010094184849410000c0180703000c5244920890700d070603c6003039040d0b400009005040300050100700311 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 925619568 1250 925618318 925618349
    0xb0702071e080c03010e071205011d0c0a0b1204120c12080702072108090123040302041413080912060f061206070207030b190203090109060c1b1506 65
    0x220703600d40391804031041581250f00e80e0842609041c01e8030001c0c16641c10b250041481041640c80f0185c11803400d42c07007600005401c0081031205104041000503000c4642d024041880007030030084404e001074a11904010709108407045644d031840b20041c0010800400d803c0e085610303038062602040060790051825480340c2082d40c00038072245086500000500c2620000030340700b039405014102070101d03114090313480c000c5030b21480203592200000034100405000c1c00020a036000301c200010825050403250f80340c1c9940100000d980450f00d01030350040c140e0b400d0004403241200744562113584804840c0c3c07030705121000141902d00540784a40c550281c0c000b000340002041000390300c1518210365034a1161a0200441e64a4800b1520000541d202d01d13414404110040c030341d6a8007100c0d11181031021041d030220a03060742c00598801403243c0d12020343d013003009070034000d40c00d24a11074580a03080d510402d804400030060100040c0905050116107141981c06400c6400078041c0b032070810480303 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 925620818 1250 925619568 925619609
    0x161b03030b03010b01170f0c071e021e03030702220606030501031a1e040203030d0f0212090313060c020f0306070207030302101119030b040f060f0b04030f0b070207 72
    0x50503000007028030039440c040c0380c0756030340d80149003220082c005005c1007101a65090150540c000001d0326224846406000d80000110450b84818020030140886502c541440c030522030503040c010400c8000711900d2481c3e840c80d0b00c7c000103071010a50111000c94a5a90180d0452800b409510135048664203154001c17031030640541029040780e00c0b6810000d406404640035003003020003550f482c0d40660320707090b90711710b500602d10003c2d80160000341620f2a0500da080c1d124101e4003c10b00c13023041c460700810381d01c1c58a110950000d9104000e000a185070202a4020301d20709001801140c0074406403031110300a40d1a068500b01841c980a02107450b00e060120019550f0300302440110700500c6550110300ca401d9950040303003208041c0554007801c010459582090814504040700109680c0e9400154580e546000c1c0000c8955802000585241000035140145007241c001d5110303c50304000400c0040d180c070752064003403500704001038401e03210f4030800c904041003507016800018050300080c61 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 925622068 1250 925620818 925620821
    0x613090e0a03020601080a0b131a04060b030c0301140a180501060b040e07030204051c02030a061122030512071424060405040b0601081009020f04050423161b0303 71
    0xa5000f40c0884040e81e03039407541c1c5550b40c144601c0081020300101c0204e5114100d6100f042103041c4650840644503984601c1d0000c1440c085900740e0b0416150080100c4c24213050000303090500d021b41c02070014041c000032400301e100001d03080289580c0e580e80c4030000340b00381441c01e040130765000000b402000c0d81e4882c5148a5040390084c00980403440001c582c201d80031f0b10131030b021108042c041c0100340c80c40c04100d440c8808254010303a01130098540401c00a0500e11681070140710440400d603c0d4262400f41c484c6003a5501c0880709182d503090002c1c0081040014100800c00c00e80e50b08a6540216103002c4441542140300e110003403154541c0b0600b42c149469109441d2120380f58035103220b039070710170401c81506d5096401070489814580464019441116100e42c042e640701c01c045c0145d41da4900582c100d9100a513064131000e40410284083c0c60701b40190b030300c00e059510b040c90b4402e121504800d0141406800b44139039908909806c09207900901c3d000c0c0404005000203c0e001c091400d0240 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 925623318 1250 925622068 925622083
    0x11e0c140a0c1d10030b01260105041202100221061909052202010f0e04020c2b0f0203030c130306110304050d0f020c011b020307080313080d05090613090e 68
    0x9142194040044c0d9004c000e90410b00c103c940210440d059079191441ea41d1112000d20004006030b003000000007007441007401803074001c0d4480d0030340c00d01d00c3c001d41c900203040407411000305d0007250040180c0c4131b075159851804d85648003a0f031102c151640316240040c8003400b00309a245c0103e061041c00140705013059200911409001c0c018407055041042c0309c2043c8040000000d0102c2e040101e4941080d118041201441c00054030041c80c0000d404c9207180380c051401080310305062400811008000d00d0f24403000003031011700301601c0c00c8082c1d881c007039100c0c04000d2845031641d0703001c40c1c071404548203900c9100c0295081402000f0742000545084000e520440381541c2d44d100311030421070369078480c20340490b403185030383c2c042c0564904680c01150040c00803000c540302c0c3d84810700c510015a4043c088070f4000c3c19004010341c1e0300e80200c21107003010389195114100c540c20600704212425004402c030303240300b80c08031001a954015809e408502200c00d80151580501d444540c030015500040e409 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 925624568 1250 925623318 925623359
    0x308010e010602070515160c0807060e04020c120304030c2f010e0303030a09051f09020a06080c040302221a0411040f0e06011704030e011e0c140a0c 65
    0x800c060380c031940160b0f80d40e20a8070882e908103460005146003000c00f50050b10014020944440074004251140036881185030040055a08000c80810140780c010b80c42400e0307558141d6043d130030040c0c500480c1d5164120040000b004146c00000102054130900542400c2d551050f14207048201d1105246c0f8055105d007500020148140030b596aa0341c00b4048140500c20010011407075075a850081002809880504441c00e114130007410144c90203015071880960300314000010403020a00411600c0c00c82d5074448002c3c02000818010005410811a815a601910924617004505100701c80300024030f1030822a051070000d40d00d006510410700186c14800490301403040d03070401003462600e8032441c422400c042c0c102c0d110400001d24083d6051750301c10814105450503000404141120740001c450840000d00c042828400640c2c1143c29a8401240e80700c0241c107030b82e00c480001d01070300c1740641e000c4c04103090913910f01c0300b9020421800403801c0d0b12008100410755120040540e02d081523a04 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 925625818 1250 925624568 925624589
    0x507110109060b3309031002040320090f0a1802090709051005040b041a1611101e0c020a0f08060a1b0f030b030705041407020105180a0209090f0a030801 67
    0x403407408000e03032070700b211184401d5184c0c1000c9403102c0c040d4002d600440000da00f40c09000164070a144d01440070b030005501941102000020f10f6141079100200c10700154410302110062003203a1005003003055000100c03100004000c0c0f4401003406145000c1c8600950003813500080010490340149480c1c2110300a440b008000b400081003036815000e107024401140382c06102c02c00c054030708280c0b90204809046100361800d081c10700814041c0b801c41130300383c0d05080800ca0340c5941d8180f0304031100325103070301d4503088680c030a4981a280f100c07072000d80040208a45006010b09550b140d080103801040b040913140c020554403e10f898030790000700e500354a1070385046003100b0014055a800250b5002c2c60780c410000c007081c1c4ca02a03008104000c602c2d600751068410220f143d445601c40c07000141c0070b0803070085483c40c158a00030301b92a401081000c1600303800c01019640c02000507102d1981c0d030304070b40300d0b402076075060700c5246030103641410300815218018144040c5074000c1d407a2030607035240081 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 925627068 1250 925625818 925625839
    0x250c020909190803181603030e030118060b030c1e09130c0308030408090603010603020903010f0c1e23030105030d0f050a1b0203010e1b040515040507110109060b 71
    0x3000d52a00a9600c0c1c001c2d24440480d6104002052030004540c000c2150b00542d0780d0441503044289454081c0d440180344c080359007414418150090070110b5900d804900900841c040c0e8a50350074140c1491200500068641828841c02d5030b061041c41142c40c8054084400040001641006000b1052003540680c200b0404500164551201c900c50590850000a4050324680d01d2445581c070040060382e50440c10f01044100d5a6460015030081c071503550050b8849114600300350031910162441a406860203844034403468100e100720080151000d0040b6410f80001e07000c0c1c940d5205240b0902c2d210102d46c1f140d5902c00c0b00c0f03c000c2e42c10781d4025000c0340c0e81c10b4103050003680c1c0d0350400c51014000c1503062120b06501803281810900702c80c4090400d82c4000f43c035a0109003540c0303650310948a40c1d04a420f01400d28480c014803400303000c208440c244120300740f452550501007076542d8184e010700e44400000b40c2c4540103482d182098004032000700000040741c10180018001180e10318815080c407038 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 925628318 1250 925627068 925627081
    0x2030d0c211e0501030209060108060a080a0521090d0303020d020c0709150b1e091c0f1104020f070b07030908031f0e15100917060604061715250c0209 66
    0x3c20300e030590345d016050f5481612141d005580310306000707003d036a00000e4a500401c0501d0b00340241e50714030b40320340020030b8801d0100f8503c1c0c03d0940c40c400c03d03140c82d11080c0480d650558a01c0c0c1c1d000381c01c4d505402d0043c9c1d0f501c003480301c00c006885440d80c15031140c440c08400040c1c050540d8041d418a011142170400d00580320000c0701664840d07620041d0184043c040300050100a000091001c464010301170301c0c0e02030b03c03c2485101045401d03002da4944041c42e94a50a00a0700040d95080c118205d030118507000d40405070f925140568030024000b02054000202c03c1ea010b6807001a6907070b0040d560f0354403494108402c88000c80c4203071100504140d48a40020301141000700c40707000d01600101c00302e8400034201840490449250350b001041191080055416221841e001680244c0c0003c1e00701454501c09120a03980700b64420504000b8030007401c8000c8101082c460b403039104106e40c100c410b0b200d07510340d4241f400500c40740e00c2404094588002d030060b000030384d84203018030a48451082c0d03500c18 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 925629568 1250 925628318 925628321
    0x3d08010e0f0714010804060b0d06060b0909010905060a030f0516120c0f0e06060304060f0e010e1b090708070306150906200c0123070f0b011502030d0c211e 68
    0xc420700e0303020501080104000404c3c54000309007000018060400303455254443d2b005403801c907400549400c500180151f6241080b0341028058043c00000344902e042650100e181031003140f0019154049006c06a01044130a11880c2e25000c0510b8040c0d02d5103032941d41c5901521495281141e00018400e400165a166460300303504845007083d400c0c001d0340d503801c1482595070000f402110301556642001d00d0095040c071440341044242c900000b41d21140440307143c07421207002e8064685450096091401d40d48040c0c20503403014040ca0140c49036151460190b0141c401900700030a040142200000300a50005044007143c20b1691480c102c1044210341400c140c0042e0081d98940d0004103c501842d4084c8130300c44a904a0305400880c0c5241455040a80760041c440455140b10440501c005000d81c111030709014045c80551112600784542000c1e69030700c03c00c86928001d90303d0f200d5041e0300c6409a504210741040b4a07400c0769902441101000040c5442841c00e000002290344d00b0f18002c019 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 925630818 1250 925629568 925629599
    0x50306090d140901021507200c1507030c0f03050d180c060e0d140a02010332040f211d060904110c03070f02093d08010e0f07 55
    0xc0d4491a1091401601c1030380b6540c0040b2202d0b0540c480e984e100c440f83c65081c8809403048910b50340700ea00040318040c00d400050040136990360183e100c0343c07101c01e69541d401c1001e0b03000d0254042484c0d44006910b8241c0d80c00910000117800710000b020400241500710008002d540702c4070104100301ca160000614214a2020f809415110900e80c2813202c1c4c1c1c01904488000c030760040c914101d001080d503c0d100410880130304441e841d08a20314200865800d4003c210b9208066881100242c841040c04003035441e4051640005e0340c1d01c0004607040c445151254500c40b03402c103450818045041003424407000c80c003144280014841481c10308502d49000c1c0010030340034001d008a14003100030b410000a442820a64071a110301000390441002080008200705d61240014040c40d0120740104240148000e01c00301460040f039858182500452103061802119091083c0e012004241407a41300c50303044e00034205039840d101e15144030200000d80d05030000404011120201c2d01d50300c0e8104900c00 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 925632068 1250 925630818 925630843
    0x50709061416050c060a120e070b07330203150901050a29040303020709051b040b0c0a0c081b100e10020109020310060501031401030c12031205010f05030609 69
    0x1050080b50803000d030300925081002d00030002c079458030f019100019081c2e400540c442e0040b03031041403030048521041c090340030f0031230f5000081c00c401c501e400e124032403e100722170780145251a095014030640030707406507010b0004081400c80101000e400b45040007036000750f461069680c1d031011000c1c0980340011442c1d05a80024101d591803529180c4d001240b20b140c551441204d1041859100b2010118805031006502940c0106034062034081e6220480e00003504000404400e003c4000301d1441c2c181c00c94044a02d0364004691f200c90740c0001a0903c0c0c1265030041111300000c000240750b0500250640110200200300c4d41d07014a81c1041082c030340d07403d08145003c0303000f1125807002442e002d460113510039030600000c102071500e940024140a0322040200e801a501c0b8020300040d68144540c00d509a00410700b1089941583c880c60841d545c9841184200490b4035505810540301c2d1800d01c800c4400303a40c090000d942c54a140100a45081c01010701910031400018080c401c0058200200c01 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 925633318 1250 925632068 925632107
    0x170901060b0a030e07050603070819290303070b090c01020d020a110906011209030f0e04090515070905030105010801061d011d1b03090c011d0f0f030a0b0a05070906 72
    0xb6032520058025100a0400507201d01990f18005480d4030382c84011841102039039141074152403c01e0a80103068640d480e603041241c9844c0e42616103c210751113070480030307001c01105000340315070a0010b883c0d4800e50100420a20201050120003a0009400304001c00c00f42c0a0342c1480010402c1282d5489400c0700140c01010b01030700c178034807500f0841c40c800d40081c5e041c50120308030312886400c00156a00b050086001441da100c514100d070341c2c0064103c0300c094003200d060103d0201500c0c1c144d07682c4032031960b0082c0d000c2d4000200f40c2d058054202c0d2401050007034000c0c40325607515036480d0b000b4112841401295540c40d044585c902ca00142c2c0603042e1800400e080344071740d14503914220740410081c0a000500300541171101d0160f80203010307612a03000c01e001001a41c6481c0300041c1102e46207044a20720505034680104207654001c0345032198031069484507a2401100f00181c9000d810007000380410114009201000c0c0554220f10f11134011a00c5d0700407056501c143c12542c82250010010307421 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 925634568 1250 925633318 925633327
    0x60602031309050c04120c0f060f23160804030c09020f030a0207020303091c120815040207050307022d090105060706021c1107061a01051b010f020406170901060b 71
    0x1500b6580c8042e0b0042904043c00b8201521058035694040440c07000381c1d25017444a10810110b9030001e06c1001038840d510709210751140c8804080c00002d01d0100c10380019a8450401d8458143c0c081170740d11503e051303402103550080c241000b42c400e60203804103440c6070307000c0714010983e01d0700c60080303914440d00182900e2840d903608a80c02c00030340001004984c5030200308421a1641e4545100b280c41030480b0402d120110a145811501d01d501e0010210902040c242004428404141c44d0401d0b10003e840c00350766600c8500e03025085200e0040c1c001e40c414140a4201c107044c2030000c0369004551008001c0d110f8007820f10030808151024414250300c8603040207000d000030034603000f034204801004001c214030b91a1050001c1030300c0090000000325000803a002c428040f0034040c0c420002030080d13102d00940c1c100b10000f80381d485100490900c0c0381203481500322001c000d50040c03000d04403001086480d030f80c4959008041c80005410360b20407c03600004240006810b02c2010704888591020f80c0c44c1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 925635818 1250 925634568 925634579
    0x23117010506031c020c0636030d0c0c080f0d14070506043011010b09090c09130506010b0a1d09010e060303040302090103060f060e071b0c080313030203010606020313 73
    0x141e0349001c03c6400710b004084006c03980c4d4032034801074104e080550654844142d860511a10b04071046166043c28050300c010b805041e440100306c545510245141090003020a0304100c0c81140c2350b9444024648075404440e00c8111000c550a0922005a90780c9482024503005040d15070042480c041c000e5009400450b000036030101d20548143c0001e81a4607102144032100d410a50003940b00c4800701e50702d22512020781c107007032150644603c401c450103155800c200d80c3c050350f42c80c042e080480c011900180880c4441c40055115a00180c1c070504980c0c3c2507031608040c1240e50003040b10350011070310b494015800308016003440b180616019150752101c2e03103004a84081c410f800307410309030140004c01010016841d9101a14060740c0110310201d59007201390140c1080360b4440e44034102c2406841d050080c0103500c40c00101c03018984007420080d40c0401d0801c10207000440c3c0c0320791150300c80054801c240b0040c4404100441e4000c42c002c0022950380c0d01d0581e100c0c401c031143c0d00304000418800380039 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 925637068 1250 925635818 925635853
    0x90506031204142b121d0d0219030c0e060a06020303061e030a0303021210060504030b060414070c020103050702060c040504020f0c0607051b070b0d02311701050603 72
    0x28600c000f004005508401500302980c8140c110503108001041803c0d01d00b813003201c5601e80884180e518009804403184084c850001b0040e00300d1911407901b1706545029541c40c0c000403810240288a62195280ea0b850100f12003002481060b6050400c10006404c615160300208221051798000c1d502e959154400c0000b4240e40d4130710300f158801500340544442e281042741c0000c55100b51030069035602d4072061501c5441d0000c140c1d07031401c00d62080a20400d64001d060301c00310fa61140c0070000c0d0f5103400000030068428200501c514891000030050829445405100014001c0e03c0c00c004e6501c0d0314000700c5c9c4844040f180c0401600041004100798201640140844400d40d4200c41c10b00d20810746180c01c1120a80340080001c00101c2c49400c001e0304050b21040c514440d00003000064508400c80402e0f00500002000307490380810000f14138030000042c0e487c407840d42d0902c8500d201c0c0325070540a1080040c065540da080520803101c400220510845004d40001402400156298081e802 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 925638318 1250 925637068 925637099
    0x1504240f0f0f140d0c020708071d07030204080d030b0405091b120307080c0606010212040311132a02150906010302101b030e01030f090209180109020d0c090506031204 73
    0x100304410110fa920302d5501c00d0019015041c00c1d40b501240582007000000d00d800e44903000b244032500b111008000c6100d9110a000c00099840307103c10080e40c0c3c5800036002030046078000304681c064000140f4132640d140d80300700c40b0b114040300d0800c41034036000c410319981d111180b01100000505040041d10b85041641910003400c400c0440f441c3c03100c0350351072803645d4110203081e2000303603c450107000f825038050002201007820b01d0222030070103103141c85101074110404203481c0a0202c0320103250b0140040d8201c407050303d5080d41244281104002e440e05040c4201d00000c0050041d00d06612094480072480b40c01901a00000d0206034219020030040e251590220014000340c444081d5416184000c00c903112400f94440d05d402d0300704000003509131281503582000191900c0f64002c01a540e022081d034101e002242e00da0a260280c043c03541c0141903420004c0d5000303943e28501d07802c0049107101c0009484071540309000c9515440f040c035a4800400c0c01c24200a8410301043c884d0013001341221 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 925639568 1250 925638318 925638347
    0x5010209011704121b1b0807080a050c04050709090e0c040f0b010806040f090b01060c03021606020a0311071a03090c0603040b040f03170106050a09050f060403111504240f0f 76
    0x10660217007036a203681d8242d1400e00303a0400320000507000c103c403000c10310403d03004011006c00341c1041d503082e5955545442c40000f446101d1a642c0001c141420710918413000070b840700308410010060b000750b1f0255198030f0801c5180c42a42440c80095146031070380118603458a0686408480d91903207020440500214055010307016900c0c01650086090380d01f001e8002e161305c1e00c0c0c41c0040c1283d4100203040c45030f020001081302d800c0b0307501004110b90001d19001c000703405d494811039a5508220b840e0030b000d1036a02c0040c4002c0c07150401c03c6000c1c8400000c50069901d2400c90f59451201801d00441d800110b4001c0d0804110600140224070350340f4443c1080361180c50203070300e0304c0e506e5441c00040c0c07402a00200d00040b40403800065044c2c000c1c0c801d001600040780c1380a031a4100d41e00045442c441c40c00f0042c10903803c42807851150b102c0c440c490b2030011101c9622511507444142400041000c11481040782092464605456008444042101c0d80a0340c4110016028000545000003440e040 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 925640818 1250 925639568 925639607
    0x1b060d0b100801150207030c2616052407020105030c04182903030a0f090503060702010e062d04140f010510050114030109150b070501020901170412 65
    0x1220203a41e03603030480d1251904a602c450105506007082507014488440260041d54010b11080c40400c6540040001301c6010130030703071903500d400c0500340380041710501d03100529446140304a1100d0070382c41e1100400d503503055418011504100f520010b81103031001c0030540c900c90411600c2c016511420055922800040c041841c1c00c2e524840b4040011010408501480e551640680c0c05805190a003580012858400904000100c0001d4591180c44542e409112005954a6000c0c8c06644100002c140c02000d0707829034035022078080d0180c00c81c6100c0c01c1c0c05004000000759480c418030300700708031b00307080412003035003107a0100482001c100c0c050000e170b880a01e420040215040200500c1801038640c0e00041090700707025544c846160204d0700300c0d074184400d1060380c45042e040032080d00c2c11104034000103d0685c18091400911f051301e40c0000702800d03c0091580281324054008040b09002070ba28000e00a912030400b11810909132001408034000011403071406104003007500205040007803 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 925642068 1250 925640818 925640831
    0x1002011e202514070305060604230c0306010207091109120613020d1703040c03140706022d0f0d182d0b070605090c060c03040e07021624021b060d 64
    0x40384c07a2071030355401141e42d6407100c81042030030308090040c1c188031403d0200b07240c0310f1025800c0001c1850401402c211510b40b000c07000078600e80c420002c0900070400780c2402c201c49a44e110011400e5401035803c40d0080c6010f11140302c0480c80080c240d8810510f2002c41d0b6201070b150341c2044924019200160741c3d4031400940307009811102c000560003075200312122040c503440c43c43c140342c8004c254103181c0764540000108105c210b402080d84148440c010b00003c0515010150044140c40354400301076142c0310f201608802c41c240041c003d05502c44035122042070750840e06034240b03408030302d010f825408003010f600000c600524005800b404e80c0e00d003000c440d2407a00c2d401c4e0440c0d43e03002442c0980303643d51075006214140c0c00900813041c10000c1965240d1401c803020050315900d2290b445480c0c40f403410b0200103414280f080c46050020350403542e0000720140c1e0317408000748010700c6250305804403070805140d4516900000c1d641d0130300c0d562007c280c0c0c0021003a504000a42e0004249164103d03213541 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 925643318 1250 925642068 925642103
    0x40c0c03090e06211e030307020d200307080a0206060405072f06190b03030940050702060f04150c030b031009031206030b01051002011e2025 62
    0x8131500f0600340c5404c02440810051008084400c00da00302c20030309a003040041c4411150301080c820380316040c80c10160390601b4680c0d10720380d207000b03078041044c0c207408003146e15010003a94000405120031241d00b11049034441707404000c01c4440603070740303200400d900343c0e001402c1d900d6242011072040300b030481001c140401d038184541047c2c0101c0c1c0421740c031880094041d102d0b01d0140b1030710140c0d101c260000c5007850180c4021441307141c4009803d00e100c0040036400d001e049004604100010340d80203060304075804910343c520103001c060310050098040c46001030141845580a9407141d6000542002015910707000c400040584440a0007050344925800c1e19545040040c040450007100340010445e160741401840c800e04011130489050600004101241c43c10341004c0c19036004588800380e000251500b82d005240c005112003001454811003079540781c0c650300c03031207180400c03080001001070030300c280e1070413407264100912104941d68103003200e4660b28294004040d1285584440403000417 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 925644568 1250 925643318 925643359
    0x1181211030f011e110f0703031104230f061e0d240608011a0f0a031425050c100c170f09120c030304020121060311040c0c03090e06 58
    0x40c1c03400e0700700c03000103189101d94004a11176520b034610003240036410191084000c1c46240f20b01c00c4040d0405031143c20000c2e1400d007000480d402010102c01c25003078481e251803680e500b03d0840825500c10903003201100081d003004405c5030034403190346130046a00e0b2a148421081a042000c0b4102e01940d078031450385003110305015081c0f042c3c0141170036041d4145015801800136105801c101102136032121207100c0100da4600741c8010641d02d1910319160520584110000c1040c45103500105035658244500301600440d03040012883c1031038a07855115140c819500c42c850960b154025501c4080780001800b400d9200d030221791000c0c6400d9034410200204101e00a4043d40d04540420100d011304c00d20306800c0044180605d03604070643c0c10030050120080d1a4040100048d040c000541440c1d15014034130345002c240a02294420131200740c9900700308003003010900c0d019000b580352049003065140105e0092a07859456603400380c0060800010701040000079000c1508060f0541c1c0c0c40c040c60010 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 925645818 1250 925644568 925644581
    0x110406030501092907080a0b06180a061b0b0a0906051f0f0b1234170609040807060b0a0909110d080901030903090b0705030901181211030f01 62
    0x2400045a84210f40c20162240801484d00b13250b01440f15901c41510142c041d038256005105003011009690344480da040544032200300b00e503001c06d00040c0700c1000c5030490ba80c41d0b4621000d87e4202c0805407901800e90782d0f05a02000102000d2030742e0140b01c00500d08254550703200c03072001c0e0b000c90f035400c2c665035407020394034103a903050032040341c141a5400383c1c1049181d080050516099617607615180004220030751203507034054400c00c00b403a000201001c5d45405000e1200410400e8203100380940905100c1e40c0540c51100c3d1700095005041428501c2a045424043e075401000c4906c2d03902d07155a1035500ea40f022804483c0d00e07032104200b4920b561800d400304002e00800601140c144120b28042030000015040d4a10440000200c100032580c01c00541c0d2000341c003802c00151482040c103081d150185564042c00002d540050340b4010044080050082c000c02030302e500301d404841c090703a4490101030b0300030600da0b85103000036a00403940f40d511031701c0e122402a090702c400013011005507094a40 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 925647068 1250 925645818 925645823
    0x109050106060809060c09061204030e0909101802280f030b0f010503011a09070c080d0605010915051c27120207051804020105190c020f010804081611040603 69
    0xb468000c0110f0513205024041e4800031a1040514202000703001501d41d006000709100c1d06000e100000341010700900d0300544030003004020b4000d03880c0c4600c00316925001409882c01107810302c00c0c0c807100000491754207a1500d0b4010900c13150704110303800d0b90200c51010362023880b942d280e0319000540300180c151101c0141d805004082030620f8140b481c10107110341a440309010b613143c00c81c403000406019104c20366204080311503030074586880348210f410340094035014003909400210070b207106c11180d00580c200c500a88444048503642c0d11040d00340c0c80c1650019003c1078080140c03a502840300540c60050b41c0350440d0000d03a0050402c402e9000d0b04164840f040030a070840c1c40d0006005006540c441e03240c8051004004160030040410412441d01d01075480000e090400300d0b086a0141013600d44011603031101e80700f12003258400406424440c0000c0c0e000b4406d08100c01c080754868500e461249030450040c0d440d00030050b664402d44d444441c001e6135501414115180156500e004d0b1100660 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 925648318 1250 925647068 925647077
    0x210090b1306170f060d050309030f030c0f06010302101103070c03050607030624032013030c0603061a0c01090606121502030402091306020405031c1101050f1503010905010606 77
    0x10b04000c009818144000d400c1c41004040d03c04024018018900c4c2e298040b10a5482a107200b0325881c013145140a010050740d423500030701030701c0d8104408c004098503004258a00700c3d2001c0c00035400c1179854440c00e001c0a07400140a80c9200b0480d0b0141d2812001000a1400c480c81c3c0704660f2200000b02c84550001c4031117030400801c3c884000d90502071180034040b50344520f07408c594a0307454501c1800020301c041060540300c1c0540c4644c0f58980707001c10240710660389110340d148e1501546c01c0d0032001c5804101c5840ca0b61000205140c2d1103881840143e42c210917848032240d030f0345919a41c041d00507551031010356480320742500000e80f0300d0217800c008003000309010000e03040318603060b44001440c1c10062583d9105008100141e90b90000c40d54003c19811b07803000c2081c090381840703030280c45142c0199805200b10180e00040307002c142502d000401d55661000c01c455140e10040d0b0981c1c0c42511000090100761000c15403484003034030303c6c0d0b81907900180001606030342076480d1800e6508591150380400d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 925649568 1250 925648318 925648357
    0x6120f0507180f0b12101e05130b0108010203060904031b051b01030f09080301030204020304020111030a0f030c020607020a03050c011d0606031e070b180d050a02040f06050604030210090b 82
    0xf2441c50142092600c41101c102c08004100c0100726611111061401c2485803150144082501c00202c0c181c03101c040c1d00001c0c0100e00d007075004052048081c0c8400c6505868403000001c0556044c400d50f0b005443c008d05072262502c841d1000c80d501d45c3c031400d10a08108514400f40e001920800050507807248041541181a01d8000013404482c142e400d0848020f09001384440055801c00031641582e5040b9401030300c07500ca81c00100d403140c1180398441001d10000440112550300818401d00300703003490341c040c010311680710401c98440300c060301c5d0a0b02690003e9030350030020780a480940072041036400001000002403058034251007107842019001d40219041c07103201c1c1020710500041010300c41d40c5056113205c10310303100d0f038441c507500c40c0421300343e00441d020280d01c40c0146142858035008024118484050070310a0f114544940100e10861410030001401483d0f40200800c840d0f0040c411030803d8513540078018151040c030140130802c080c02c103000c9202c04414021f080c80340348401e0585071a = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 925650818 1250 925649568 925649591
    0xa05090a05060118050306190b03030a08090c0609030303131e0c030510110316020106030c0e07080105240c07170a06050f011202191a1c06120f050718 66
    0x25140c00380e0034480b0b94007242040c003550310300040d4190405600d540b8180c0c20203920041c1401030a04292140d2b0600001034242c00b210780c400c001c203000c4d0f1542d4081c0c946920618003040303010320401c1031458140c0c02c01d1000454500040c0c003914541c0380154600032003840488070b1103080d9441c2036412074018050300418020b104040000b104401980a002c118a04845103007007041e0000420f0700755a5103802c241d01e15080e10270b41103e001142e0218803000f040c1c0e01d40c1801440c0358001c550b040002061a400000e040c90309280b2642008604060003840c8001f951400840741c0c000784114a15100f59140002c0301e00138000c820020000400160842d00142c1c0340c103405441002d0070032082c0386580401403041407280e0094111039541107a0040c10400076419141920480d94003c500c40798084a20342c4040d4801070060481b0070761016250107080840c0e4808040301c8003805407581140201107000002140038043c00d4205001d28201d4110643d124545c02e202c00700c49444000c0b8940f14007002a6 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 925652068 1250 925650818 925650827
    0x10c0f02040f0f06050306070504170f01091101230438041806140d23030414301c0f081e0a050a0213090b09010e10140a05090a050601 59
    0x10b0801103020b050203040110000380507010303038041e078064bc07070300d4610a04224004108211030040d092009000801a5091a0b8000808940a00c2c02309d590708000d8240d8250304440d0465041100c032081d41410b052078062411540702d0440704065021007140c0c00c8001140615600c84001c81070f030602c1d503640c2011690000c10b088015480c142e2410b0160a00043c441030b01c1080f001c1c80c0c00d0755080c5010400b42050000030845490080074020300c021001407010000c80148280d0b405e488504445a91080c14000f844d0690440d9406400c95a05c004490011600c542c1c4c440c00c07000411500c45208400c0e00d43d405c43d4040400c400840c3c010f99011038215007140032154003100c0000003810803001c101c10b040c011400140807040392030f903640c00148031510300e9040d10784014801c090350403110b48445100b002001c00d1001c05208144100c000950351940c0c6444620551880b41040001c500d01210725800107c50481940e0040309500b0124403621005001880340a8086000c111428180000340 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 925653318 1250 925652068 925652081
    0x1022e1b2a030f2d1b051c110303070201090b06090601080403080601051909050a0803030c07080a0c060203040f120305160e030c0d050601080d0f0e010c0f02040f0f 72
    0x301c072550424401254094071041403001c10742c0500b000f501481070040111000310758001c0d0280a100501044c138490b9070003e942d10100341c0503440c0e150456000084440413141c441200610603130110140c00b481103d900c2e050340c9042e0480c107102d803d0000f080341d610701799081110a41c0042c1c1d52889141e052042100078503030414001eaa03150780a0030300c00002001010010005418000b41c0808200c45034410001c941059003a9500d685440c4003021000381100180d1240c14480c0f04e462001140d000e002000b2240103025902d0b4103864425195250242d0fa0400e0711044240703c1c01d40034040101c2c0f800c2c00114400d510500000501e0000c03031516102040da100c481204062401d400c01420801423000804a800c00381400d45400100c0c03c0001d00d445a907141c45504000c5064041d070401c200015824181c03025101034851490701210b040f51900d00c032a43c4400007684204104060f94041e452024060b401070408481039800c54022509541d95402584451580ca11440c0076040c11849640b = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 925654568 1250 925653318 925653347
    0x9150504080d05060103090308041b03020a080c01140306030c0d15050a0b040c02161a07050106090207150c0909020705030904060305030c070b0301031505100e040804090506010e01022e1b 82
    0x100512140c2d88c6004051803401000100300c0c1e41c0382c81440036855082c2c0703107243c01580d0082c034240640d5260106d150310b80d005c15201c03070302142140c803002c08900c062a00352481510302400424120202104108141299400544644902c10b4010794181c001d070050b544a44620600854004101c00c04d005c00c460001c2a00c50441d04030440381c80d03554025003844c0049920f01c4110070300c00782d803003c030081040c400c150000303003250b1030600000341038a910340240a20078080c1102c00302051809041009032101090f00a000230801001480300b07455582c00340c0850703809102104e00781411031010404507910b0380c0041e903143d4801301e82c05020305000c012980180042040d56410365145a43d0740100c414001841c0708a135860b5400116081000120389001341612a2501c5580c18503061071003181e4094003030700d010f1608040004503c2c0d4002d01d502501c540b0180d005140d00400d4289071101c54040b05a01403250740602c80c001420400d50280c0e19820582140d00c4400c80018071014101d2401480e14 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 925655818 1250 925654568 925654571
    0x3120e011701060e030f060a151a03040b0a020d0c02160603020406050301171903030501050f0906030a0b1f090218030708030717070b0a0203240a060309150504080d05060103 76
    0x40c84807510120403690450720300d0f080621030384c0c41e2a000a0304001c0003074075a503c184200c604104030031010f43c0015514041a01030400f00c5504c0d903031a144c84000510704c2c8004c007002000801e0001c3d46000380303581d110085203401070a040e000802e03001a9031301480c1400040e03100030008569800c000d02070314020449420110f141c14585030014080d0b00051294540c800c0d8035065000303032507400f84581403241c81500b0031388007220340710b14001c0c000b41020300450307006040000010890f410401000c0e4020040240281806840c59683c0906084001c1015421883c2c1d20310748141250183c5010028007100d00000d0f803190302601000d42d2080403522464440c0c3e0110a0401c5000008402c030ac1d20a500451040b00300c400b601c81d00016449902d0006040c105150104250040554040c5001d224041c00341d416080c00c50300c80c0f681c16041c00e1015940407280072820400307203000342e000c010760320300c01c0c510b0741a80c075824030042046274401c44040da04207500254100104040e48226036101f00242070 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 925657068 1250 925655818 925655837
    0x70b070305060f01200303090318040c0c0615030210030b031005040804030b04051c0c141204090c170f090d02030304050304061202131701061415210103120e01 70
    0x503c01c481988803c40c188001c4402400c00604e0307040000c40e83e60302d0740d800c895903818510b0006030f983e44980f0b000d0851030b01c103200c2d40c0350501c0c240c012003405485503603400c1d9040420361120401807100100758121001444400001038030b03500c107207101161041d02d0002d0b0342d80e91001414200700302c0e8400941160701d0070b000c2000158803d420790b0305681d001414640c155560b45012403400741141e8580c560341031000c3d042000240d0080000c589148140c2181280c0300c10805035590750900f0072003036a10b48200384800d00044585601c405150515407405100c550741e01051100303000800d42e691022282d8480c01c02600000c20045070f40c060700184001c51541c50035480c0c85449005600860040004551480c0d03003545090301503544020300a1180f0203669501c2e500d04030400c504500048445d401c10350002454000e40340c0540740154040c01c40f8907030210107180c24501d45d12105046c465a00d883d543c0c050403440d00f2203001c1c081d6204520010410800d428080e040c1004d100b645030410a030343c0c1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 925658318 1250 925657068 925657081
    0x106081f050a0b0705072d0603020c0d0f020c09040615060512071d0315160c110603060a0e0109020c1005091e0f0a0302031e0403020306070f090f0b070b070305 70
    0x4159011034100f2280c107600c40c0700c6031600c0740c20406664007401c03d400b1130000d41040460050340d010310031030784a940700f00c80c0c9a603150141c0a0740180e402002d0b0a17008407407401c2c50580200e203000d410420620690722501000f00004590300e0094030150348055445024050008110903c03a001c0d221030300f0401c0c10201001c42000600000800c00001c002c0803c0c0c00d46003080480340109802c01009080d03e60256005100351040c3c034080710512012680c845041030003601440091203820b0b003042d010f020408092050100f55400a007030329411841350b000000b4080703101c00d0041c4c040c0c1030460025035262044901189481703860a0300b84200b62800080c0b1048890004400c5404c900c1c0c801c840720081802d070030705800c1550584076080365000784140d4108040d4040b009002203441c851543c0c40d204c0c55040807204600684c000250503500c54008a002c031401480b4440b081030700c07482c02140c59038455584d114402156480304990032004542d64081000d211011070b0f2000091a0400a918144 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 925659568 1250 925658318 925658329
    0x5010b0103090c0303050c0312011701150810200c0d030e0105011d2e170f210c1002030603190b180c0603180d0f080105270106081f05 59
    0x20b100040171b00a0001d25903079108024001c0e03400012804034100701e0356a480c0c00794541d0020b60020120345500e0400c4d110070306c0701c424081c00300b0740f03080703900a2100c2012074458000401410905068060050f6841c0307013118145402085c490b003d26010b081c50000d40803000c2c3c11b0f0342c440d070070505982c0d0515005000081c20860203401022810781d8030305184d156a82c144805541030307544c0d0748095a181d0301c2010f400908003154800c541415000781d0b841d0481d40902e42d00c40e103130003004039040d40141100685445c4030610b02402212a10301c460329105e51310036100e2501918001590179513401104000403440e042c0030100f1005401030f540100040d495a540c820400b00408541c800c0000241c84180c902d005c1008081a12001d01281d03030740d04103590079034410b15003010300c030110344110b035044000103100701001340070625103440f014000d03420f240810210141050440e40c3ca4803034000078030b4010100d60681802400551203010b01da08001d20281c0c002c1d80c180654110b40e0303454a800304401c2c1c1b541c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 925660818 1250 925659568 925659593
    0x9060f1d0609060d0f021803210901021c20010207020f120703060212150607050c04050408070b10062007031e0c0608061e210f031605010b010309 64
    0x21100199540000342c0000e01c14015180541c584500d032032a91580d84445600a068401d4081c0d60203489242c050201070b551134440d400551040069503208003150103035400340c818164140140c5280307038144211001001c03401103d40000420f200d0204204102400d03054400c13440c8440298a4100703640c0124003905911155180070f00340c50526110140414031080d00a07681c0a04250740d140c501e0040d410396084140c0d045503030555026814012841d2800446401541c4140078100011003282000010700b0024000e41e51100100115000100460202c0d8402c8400449800c081428250002d0564410003042040c001e5030085e88190b0740340c00110300084907804280d585101c88548952048101c4502c001040b2490321a00406d415030021241803040a00382ca09001018142050000829484000300e401c00301c200103521403160b20300250074059502204582c03042e50f4070012645107038004a000c1000c51140c10b4101c2c10400280204400350304246001d0006100c0c9031949802401c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 925662068 1250 925660818 925660877
    0x130614030f0712060308090a0504061a090d020d03020a1709130209030109020d050f060f1014010c0b01090b090a410c03040204140c03180a1209060f 65
    0x1005000502e081d03201d008103070880c05101106001c0603a0300e01d0700141c2c1c0d8000001e020300c5040000030100b000d0403d403080e6022241c1400d42902025440c01d40741d000c940c010128550494040704c0a2805612a00d5485291503c41e500078080100c1c682081078115444101140c400d180c02c119801031962950070070010007036204401665a08200c5c0003c0c01082203000003500144c110050034140a400310b2600110303c070b40c6041e41d106943d2059000b1038420111a6100300014024082c01840c22200c00c0c0c1c0d10b03410f4103041510002d2890b407683d940301d040985c0f04501c059260024240c0c1d604000310110303007080c4044014400701c041d60204205251180404881d08020b0b0b080e41d42e81800480c034442d4134101d18071090022420030402e41c0855900495060303028a08041840b28440c281000d1107100309041c0c480039040d03440d080b0604414001c248910013941c030418502e030020032245c84410510800689501c43c06502e00100941072006101300d010900030340c402455a101c0386113640d5210000c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 925663318 1250 925662068 925662091
    0x1407080c09011b0303050106111f09061806061d09100504080f04030c210b060f0604180204050102011415010807110f1f0e03181507050313061403 64
    0x315407004a03018500c80511480c0c00603031424500c2415015800103060b1409035940704048440c40564035036422000b803070301202003e0f01880b0b400c030a84a42c41503000174890701c0040751001c1c0d1034140009008050106807011541d07681d04001500c450304442c3d00e0f00e4a044094801494290401a00d03032890000407100c941c0c903030380050200090803003282c8100400708005600c55407681444800f03511036005110301040707000d510580d0307450a9404044001d034800c3d4503030b120740c0d166020700600c041c4048519810050502000c01c403000c645103043d40ca01558007005880d14a842c00090a503040d90007504241c41e41c1e1014040c2442011204004491080c01d142030562034039442121400200d00f03054409005610b500c1280070004140344102d41c0c0241208121064010b40600440381c02c250550300030b505c104040308003481403907150000b0388030051505101755558980d10455601c0341c8070803140d5410000b11464090403002652014007554508104e00b03040c4c03030a502da000c0c40040c04460030071 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 925664568 1250 925663318 925663327
    0xb06060304060b030303072a12030b010e031519060b04030809180106020618240402040905030c0313090212040f02040b03120903011407020a0f0602070507181407080c 73
    0x102c01908a02c1c12882c010f82100d0740e030300e0034040003030400c02610242050801040a101d80c02807503203480d4040c1d15041b180f0005c5003148868107600074101010903a0500411002e40d0721a56414040c1a40c041254541d010f6549448120800d11415280c0804d250071b152a4061110544a030195030651398040e070707a070f0740d14440c0c1d00c000b6007003003004010149510030050010501581c0400c28602846003400c164a103805a40d4040e43c039000b00e407d40d80042041e00c9603400344502c1442d02281c0140c0040c0000038108103644a0310b0546c5d0100700b40840d03541c0300252800c121410008008020902c8a80450401080c4141d440c5006c0d005007015041907404028030055681d9a88940d12150004007150084504108a01180d801031480a40300b946400e8405504d03140740d440302c9105a15070380c06072800b60607039038505106203102441694115401d20004000a6013000108040d05c0c5442d410084480e1400100007518200d282c40d481d0101940305000d2a2a000136003280c112915a00640d200c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 925665818 1250 925664568 925664573
    0x130303050715060f0509060d021e150f0a09090c0504030b060105130303030b18040203150c0705030d05100b090901140f0604090203040317070819022701021006030b06060304 76
    0x788289003110401c1460200d000480d1010750130940100c0740140d9840800b5039a0348200001c001c000540a90040038400e0441c0815800c2c0860854688004000000a16000104004580048482108041002640b214070f00d400c0f00c0070300000c00907078506104611a0038001000c0340214840203001c5114040841d1860780038400380c40004184241d841041e90ba80d0034010054096508428000c650000d80100d40d0144c0c205c50610031030f00a801800908419454051b03400030080c0148040b4a05010010003e007051000b05014401148040b900c1d051041c0d901c103815080da030258a0211082114090036103803130010741c1c1160030048082c01400c2071a804500ca540c2c0c0d071b005503940301c440083e021955804175806123000d64003030344d80c052650400e15068072038000d0554000000c074450b603000440201c000400d503400b0844021015081012841128001a0100d40005c40440034501c0015a5581c100515816042141c805000e402d2031600d071402220005031105028440000c001020b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 925667068 1250 925665818 925665833
    0x80708071401030e0d08040b0a0b03120c03070525050405090d03090206040506070303090c0518190f1a090f150f0604030203070314010501230105090a0302030613030e061303030507 79
    0x30241000000c0e505c4108941034001c0c41100c0c102d50488080c0382d0000416084551071090a00951000c0c0090020b07403035008a0317500e1500011807502c040d1000f004514009081401400101031600c1140100202100b0804414022940105014901c0d140c1041140c3d44002401b00c80030300e041c140090450000d001186092107181c0282d5004040010908200f40e41640322000b91401091040b4020761180b0401c002c0c80e903641c40408002c401440800c015005c0c00402c0c03110618890000207002030305c140d142d02500c1c030000101258a0520a480c50141881600f0640c02142c0c0c440f40f6125240000c1c04050b16070002041c00d0081044d43e00703440242d03d45504072070180d0340040407181140d40c0c0f85050b0f020218010b240c01407079400c1c0400000d4408100c1c03000c00c0c1c90b402e10b020700b0442d6141480115055003000f040c81c0e5014840840003c00f51314203000b040c0c0144000c0d04006240c10907070901928192107121070364042c104c200080824203180103201000d0703942c0352034110394400660502d0796 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 925668318 1250 925667068 925667081
    0xf04020d1115030108070549050a08040311090601020619021314130c0509010c061e020a0306353306010c0b060f0d060f0f050108070807140103 63
    0x58002c00000081a400310014100c400c4070021681c01c903070840c45001000f50258141ea0200b40c0900e078000f414034540134640c07000160041c03981c103d06071800e103444052034804800070a80381ca450002d018000d103c0415080c0b0700d0000e0580d425001c0e4202040000c1d6030f00d0f00201645039035074005481d4440d4000740e03011544a600218595558242c4a41074813200c07400182a5511640c2d00c154090306030300b803500445000400f10b8a442c1c2c20034040e40019101c0000c65801207501c5940d400701c045810400e9126070b00c5010401c640140c541500201c06021900325811811652503001c08180002c0703004441070300c0007000e0035049800070266043c15440e0803c1101c15200e00f0040740485102c42901166498a10b00c0c540c0a1894a0701c82e9001074510701008000642284450350004069051500e03034034038008005004804043d10740c0e1151380860f015a40c0740c440d06030721125061100701c02401051f0240044d800689180c42c80c04010070340d1040d19104031007510007502190032650380250b006c032 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 925669568 1250 925668318 925668349
    0x117010501050306061204060e06090703080d090f060c090e06060f04350303100e01180b010509030106090b03010c0e0303030a0f0912121401270b0d05060a050f04020d11 74
    0x40c6c1240c00c062a092000e030102c0342d02c0014500c0b81d000000c030720310300008100d000c40f9084a4903500c2e210000751004090305603840192081481c00c1d04820008400e446a02c0541d6541e45c2c44200c0d85003040c030302d40c400b0040509554071811050110f5241000d05204441c12901541095641d08003a8082d00314a03e00b01181103c00780e5205400d10b4100c000480258840d8016854142c000c07a01c2c3e0f440003245000070700078001150100307814016010780941c41614000700504080f030a09104100003801e40c2c034507400c101c1019803100237450300e50a09014007405207000b41001d41e80c0480ba1000300740e59000c028690340f51182c444134191303c1444c1e280d101d40705803a0041d4a02c50020040403001d004503021b1584000e4051400d110f081841d400c403524141a00c410384201c54102c015030070807039151034840700c5c502c0440d95a10041c0c0000da403800d260351146880364019100d02c4c5044003000c42100e0380108002600c99506017044016521400b9241c6402d503c0070080c07550600c0c070800300d0454180702181 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 925670818 1250 925669568 925669597
    0x7051003150506130927110103110301060c02030f031e0304110d0807020946061719172d0d0e0a0c15180e15011701050105030606 57
    0x301c113004030b04101042c0c203451203940c0078403409119210160046460442410f00ca85541d4000c1707001507480c2050f0320f060b1005140202e1218510051401c0991080c0e00000106101002c0301c0c0841c10306100806909006402450600020003400c9800d0307a807a4645404580e4000000b40401802d0f9a0484000001070310b10003a403900b40c503051950750f02046c0700381d10903115440010f8400b40d080803111038210095442c0962a8800c0510740c3d1a82800c0c80846000038810241245c079031064440c101c0200460321042c0420541c8103d100e081c00d000005c0804102d13100035180c00070032010020200310b014140400b070741e10004104070f0390100c4805502c40203141c0030300401ca40c6810406004d860903450789007081210340150f10200f40d83d00742c5480002c04208001c0c20401400040301e03064010f206403810503000c102a0382e110716040c0c0103103030000c06010400105015080c0b25004600d8000c800c2808d0221100c1640c00e800d81d0070304414840d91b4100003000001980f184ca0b00c1066902926840d2417 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 925672068 1250 925670818 925670827
    0x20f031810020a0b010b070c120c140103090f0503040312050301080316061107030c0512040e160219200a031e030e061209060601022802010c0b15100207051003150506 73
    0x180d680150340410710235510b500384150040f0344c030008100907003010f03903010491f45c05941c0350860780c200c0b0102c1030725924181503540d140040440c0640c510001c41ca442607000e182e0311f90651078503400083c1209d0030001002421300c01440325090000407100c1001100070692403441031840c010000e00300c112511041c0743c0000c0b03010410560480000c035a41340c0f080c0c0c16110701403122000d46032503004911400796400012004544448055091828940c0007803041e900d1230303240704a245404500080f8101c60b0f480b080f840c940c0038203101f546400e80084040b200e9071250f034a1a11a0341c0c0b0b40600100c5000d1803503815006a017050301800e8032030030742d0314003070082c980b1403000341d803a141c04440c2210b200207580a01e800017041907102041000965645041892000c60b040c21350447c0d4641042049050210040300305001c600b801e5150303485034100b54000b641d80101c0d00207100071321b01d0041200c0d003507500122041c40f03195114200003c04024a01d40000c0e0b45c91200508440054141d0040703412100025 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 925673318 1250 925672068 925672079
    0x360b030403200304030303020f091c03030b01021f0e0c091503100603020d1203020f16030f1817010b1e03060f06060a031d0d090501020f031810020a0b01 67
    0x10051849640651a801d203202a41c0c0a103003401c4408440003042904100018800030f400707540038088030200ea202641c2013854078400b0440c020500102c656491080b01550070170554103016000b01c1c0c120030b102170404050060b2200348603201d000030324002140c0300c20a801250138108410103605900500b00c45c1b0390b0605411030420f501501408600900a946107110a003605014010840f54081c00c0281d00684640b27454201c002e03000748080405408000170489000c200f80905200e2903480080c0035903031190b24003d04442403c0b4104014000c884002e0103444c110401544100c4240e07004140720600c4146d805801401400709850780100c1414040a0511010700500501c4c8020303800c0710610344890300f002d8907040c8100c8040d54000401c11503054143e03c29084070040da980c207102c00e4090301c0606a0981000415240700002078204601040a0340e8100311000381400100003851403ca00398081c1007102d01d4400241d07008271081521241c501e4802c001d10314003503800c140c00b41110f503102c0c07 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 925674568 1250 925673318 925673339
    0x1d0d030806010311190c020d080310090c02210d0b12010504050105010515040b092e080106052109120309070f0b0a0c03031d01060303030e010f0204050136 68
    0x99841e180080c0c9413220101c0c4000c107002c21100c007914030030520f04040b104c0880c12030381080b40c100e04a8201a507010100d0008034201c01441c080c980d0810b20240450400c82d5a0b0100c034110103400045500ca82d15640c01c10301048144191130840594031665200940d4142016002405406800555417603815000207010340c0114081c2c0d200350002e0000366070354001c00c188202c44010341d88064104000811400c040c820041200e0180580156004918815801070303031000e094110741e0306003048400143c0c01e58441c0000340900901e051007030401505000300750381c1c20b004070f8a00303014050340008a40724000400069941c0340342c04034582da03646070198406403108803510622280d0b01e09000007040710850315090f14002a1181e454146082c0c00e920218040e1140380614860241904103410500c0400e0046401440c040d072408284d04004191103030840e82c0d00d441301d02106105110501443ea4008103c000407041031900c01741031881070034002000a000019910186140100011040100e = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 925675818 1250 925674568 925674571
    0x1809080408030a050c10110a080405010f0f09021323222d0201121d0102181c0f14030903100617010603051903170f041b030201020d1d0d0308 62
    0x403103066506d60a100d50721389068440246003d940700c14140003940041d0310481c0c81c81d0740b2a000b0701c0046142074640644c90b04030345a40d180c099030382e52a00c06250079400c00f4103007807403d105500380030400a951440a11100c4001040c4482d9000d04940440d00c0d500c0c54403408980001d0780f01c01000c1d41d40c45480c18915590140260002e0f00111808013021480201280b9914035010384403d07845850720603000b0018030501020042290301301200000e405000d1028081000d403000d0705840e400307510410082c1ca0900544643d0005010f0340404000030640002201515402000ea2003100300d416007850445c0202044150184140d1420265101c2150002c0003145c0f200700450240b640c0e01c0390114241c0e00c481c0000341160b40045042e4a40805910b01c13610094000c0c604180c9030a0641030b01c01c48181d0035214146040584414042880601080c070341600044003c0218018510380c0044d403a00e890b82456002e2040c551101c0c3d0b100d0000f03aa4030b5005600080401d07030740180600e00506400380 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 925677068 1250 925675818 925675837
    0x70915030b0a0e04050708030301030b040b270303090115140108090312091c030507020c010e03070302041e0b10020c1306090c1e0903030e060903070b030f0103060c05041809080408030a05 82
    0x1b034441c002030000004011a41601c0d040320510341e442c0d40d01d0321240e40c11f00d000303801c0055003103007070700a19038246101c0340310f8600c840c0001c041c55807401c0c01c0e0308841c00d5403042541000040b0041c0c1041000030030701c410b9580028001e007000041a50b0303d0020904500901501c451181000d03010170000c000c0c041540c50030366840900c508100d54250104030201c40d011182d0902681c4070110f101c3d1a58010495a405a180102200c0000f51664040342c01e8824502042d4400e410109100440007540d020b00480c01106446c0002c8801100324025910f901c4d40f80118055840215607102440c42c6810503005003003011001d10507414038460041500314000b19401080a83e0a62008000e1041400b04212501aa51480c5d0405100200105581b0868203540c0c107100d0344100242e881c0c29040036600c00d41036000d008800e0f600d18241036007625030600202c010000f041000b401101800d184448588a030390b040011b243c4064036100c1614461a0407441e894400407508502890b407103c0100800301 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 925678318 1250 925677068 925677073
    0xc131512120503040816260409062c06190303020309041a1509030115120b0c07030f051303080f1b01050426120705120906070915030b0a0e0405 63
    0x180703584200c07403500050b039005043c4d0104204200c041c202002d581e40b0454002c07100350207680032026058581c07220003040301040b040c0c0400d080010402c0b0b481104004d09104841071082031820080f100000c9202c0090040c040800303010031410b40f0f81002d10b81d02d44e4074412507040741da074982c240695240c0248008a109504000c0c1018100190f0b00303000036101c02c013800c65480b080280460300d0300b075002410743c06d401d50340c0c82c10400710345149001c01500902039100780200c40b00300d07402c240811184c02042c4192035041000381900013544051202c090781c440e40f0b00151074504003002c2000c0c480e5a81c1c8007034120000411182c0582d00da40b801040d001c01618001c000808080e03281e182690b4040700c000d480c48450910f40c12342d042c564400381100a0000018074540141240420315000c0b042c3c425400041c2e0104040d00304200c048209074000c10b2500041c012884c00b0000104a00c5150091180c1d0400c1484ad2002c0c0324042c0d0003048022000034091240f8170703103800d00480001c00445050306c1c1803 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 925679568 1250 925678318 925678343
    0x15030907030b0a0e0606010e01050d0b1c0b18060c180118030308070327080306060c06010e070e032b0c051c1b080306010e060d020c0615030d020c131512 67
    0x948c021041030500c1d80b01030311468106a03203115014001e003101c51840c0e03044000c00000b1030040103100b801d03501d40ca10030140084181003541d45074480c52421020b520056024500340700030810a00e06803a00000d015030044030500c03031840102c0d4440d554414590302000062004001c050304240c00c0d500c00c0780d0981d8200040448401d10b00d40e00b0209044014011095480440c0843c8468004503030001001e800c40386080510701e40ca62415000343e1005070701c5032520081c07040f06688440140300c1030f00210000c00035408400a00b1042c003000b011100740c0024043c2000099601807014220780c03503080300540d003200400c0c46416240301400044c210004141c0030300c0401c02d140e042052448207801030340d0141142d45450045d22503080d00e0b081158000c005003c0400c10011a000421040c049038020300711506102140d0100d44900c914002e1080d00030a42c0c1140d07240d40002c0d0b02140c96002c07a2003100d10039440c2c000300002e203410094800301d07034004d000108282d11200101c8007440d1040c2c00c4524827 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 925680818 1250 925679568 925679581
    0x15060a031d06011e181815090209010f0b03310b060a060206041a070912050a1103031603030209040b0904030f1d060418060b27030c15030907030b0a0e06 67
    0x5050140502d0a603174000c02011201001c1c580e01161181c15004629044c029180d10b0345a149070250611048644d100c01d00381c41182404102c180c01400c0c1c0c0b079050003c00d0704000d98030070301d80001440324810000c014403580b8150314018105001d05014000218141100d0030b0901c0702e03a004550f1a4014075030740c440012583d20006400744a01d4000c40403840c0e89815940440007141c014041d80208140150003140d44410031500d032160b2446500105009042c0b0310307140400300401d60000e4070980081c840f044003401e9518050305895030500d030040c1d80f10083c1000030003e2920008241c0c001d14400c1c1000101034005580401c0640692513003110b42d980205085480d02c0d800751000c0d01302a0070f200030401030740d01b046440c04280d200000420010344503241d581154106101c0080340200030180d103582040403080180c00315100743d016020103400c40c3c01180284100100f00180148001b0001f9150101844060b001e5070f40000c061045040003206071016007030599408620380200800301e000c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 925682068 1250 925680818 925680869
    0xb030703060f060302042405101806110d170a0c0311210c070c050f060d0e03040f0503071d060d051f0605030c0904060f02040521010c020615060a031d0601 68
    0x1080c0c58010389110088c0c28007050101001a64001006100c208100300c4000d03070340101490068805544c0740048000121000380c58040000103a0041c00a42d45512455850181d0010b81c015907910b408030302c0c41c5a190040300108560b5624003044600410380b01303941c1002c03600d0070360340418441140e02540c541008a80151040300c0b00180000b542c40b004014a00303140500a405940083c4401d00300403181c0ca01d4800d4807000703415000590400642480f04d40350121050000e82019070052079180d0511400752528806194200a0704030904000b8035941e85001c00c06502c5680181958109021941200c6050248004503909541852008503003402c001808040003080280706104503100e035241c0300e00a1142121406509400704000303d1562240076000c002d10990300c80c50640e10010703d142d282114625815541190095418009031103400b940900c109141290740a0341d41d0049041680100b8500031032107402510301c00c0a003521031010a825040340c41d42410040f031880340544428 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 925683318 1250 925682068 925682111
    0x61d011d010e07030b03010905010e160e0a150308070c09110a021b0a050d14010e01050c04090c032c0c0402030613050406090c03050703050f0a020f01030b030703060f06030204 77
    0x1000003010000410014059044903a0040000d080014a54402c000440e0943d65010015a0b2a079140d0f26040c040e0b200030007003241c25035100b0720200c00250420004880502c00602121111900c401c100030712003201d1840c6000640e8440a2540c0c0c8154510781b1262001c010701c2400c2189140c0030000400c840300d101241c6e0500301aa010341010040c04807064840d4659400c3c2c0c64208040102c04240303074a6801e010700801c0e0142c010420b074110074152950039100c022101078410f90501003408144d03010001902c0990384064004550f0b034010310403c80c01048500e01c0b01ca400e80540405403448642c01c62190b0000c00040c0a030b0f045011040c0601050348020b4801c5030300030701c2c0100803000392505603010a405c035121300d4000c6651256a11541041d2040c2d4006503580c0c1c222000400030064100300018054030044058402d502c0c0036000921034182c1c022215040c0b5840b071748032004503601885220040c5500c8901004410350103100c9000070f000a002c102c5c081e070300d801c0c000f002c1592600c9484 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 925684568 1250 925683318 925683359
    0xc090b06040f060f17010909050f030a020a0201050a02011506080114190b070c0f0b0a0206010f080a060905030c06070504080c0108191e0e010b0f0607050604060e0a06061d01 76
    0x7006550714003c412141005103400080800610042c1c080c071541121690074001c1c240300e1004601042c80d801c1c000e0422070340c8030b41c00b5040d5004002c006400760f00401e001d03c07a103070242031075602c2d040100001e82c05404080701d044901e07074000d04049912500306031132505aa04100c000c04070400d8070001d003c10000c589641a4450081e40d42c01c1101e10b94a05c02080503e120790410310007590f44910301070981d0130a400c1505d408001081805107a503041003a140103000000030074220360b00d0301099580b03910046802074001610707810b2500a108080044030030ba00038807421100f061400da9401172058105001314481c5018448004003107601c60400c2c6406100100c0c020800c04401c00c0c801d00003050403159615400c52440c1207001f515a0912416110700601d90010a0418070001000300070700104400c24481d00c001d22016020590006203d070380140d10070400074a801986020600e0020301c603000038807443c10b00002245102800d201d1361955903028091228691703ca801c04144241048c410 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 925685818 1250 925684568 925684589
    0x120503070e040b0303090307030b0f09061515040e07091a040f12030e0904080706050703060b07060c021c03022a0d05090d2109090e0312040c090203040c090b0604 71
    0x7410542c0340ca5800650f0110b002401c6034500001200030a0030302d8103d5009480c85100d070810048a4103598041380da100e1201400341c8400c0c502004000481d21041c40510f000d500003292140c078091060044901800824031415401e15004a004004500724003600302010600d0b40d24601d090940e90944040c0ca159602480c200c6003448141c4a50101010040e410030a01c94444c080d40e0320b4010b1001c1c0568056a186a078034401400d004050b80c00151001c403c0615004d0100b0011440405a40d178181d4404030215540707403c10070492400107800c1080c02c1d101100c40e0501a1160103500422018042c640314401c80006041d0f007112122a01443c02c02542048180c2d4804600c10002007104050081000045403403a440300950481c500c00d28092141201061010365500030106000030f100c43d09040c81100300701c48420341c580c042c6154072401c0901941c08102009580c1054a002c1c0c0140141152245841e04061002d10360b1442210b42c090b25281104420b0700340441150191f5041c00f61 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 925687068 1250 925685818 925685837
    0x40606020c090c071a071b030f03050402031005190b040b09010b0c031603030c02012004051306030206070305130b0c210715020a030c090e0c0714010e060412050307 72
    0xd01c02201002001c020719a00e0801c00700300000c0090840b0007002007004040d00d138a14202c0720152064145540c1c00100c0c0d814045a0740002740e000d03082c010410001e2802241c1c1e9165803000c00e1400b2000c0c0524015982003508022030941e4a424000080b030035084140b005541c2d110500c011107a004000c00c0d001200d8070018800c5045540c010504041010101e81c81c08014404081c291401c6040460010751600549201250309005e00800301183c1620001e4602014000c0c01c414825442650f014a001d01c908880c0303d075440e840b4800454000d00095030319181c03803178018103c0d4441c101c1034441100344100896044848400d0b518201d20580003407940c190070811102d4081d405d0702500841c070200304000d40c00541c1610113140d6081c9900800350f110015038601a0079191740740385950030000d21000802200e000702e0209038210481c3c894a50341c03400e0230308040f901e4030300150840002d50b003040900150810700142e89881a409070b04010960307166140d00b201c0a11007601c0c003100180180c0c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 925688318 1250 925687068 925687093
    0x10e130f1d1209060d060e061005032517100e070c03020a0206031302060a030614031f0c0323010510030c0e040b1906110c06070302121c020c01020a030b04060602 71
    0xc0104503400000301010308042d40f0710401400d442c07546d04211000001c003802e11009041c02700340c1a006200c40e0034414154544590b9030303100b04031400d411404900c0b20844821013103009200340c2c0b0300c0300366114030106189007140f000b00c4203078490301c06d86440d50700d1080046c8000c0c2c401c17854001d2061381a13001e03140034a0107800700200c0c0e800181c44004805140c0d080000140e41d0300d401801c624481d5100484c0c01c5103040f1109605041c036001883c06a002407a031606d140214004010703420305102400130703e02d19600b00c22030062000d8600c2040144402c081b0207859404807107414100c9004031514180c8015010303084050351255000c4802054000240c0e0390246040d80008041c0700000d08407800d201e0012103d15480340047d8803020105a410000c9545550180f10085041030242c810b50310304102c0c1c0d03030025502d4200c030702c441d505544046030101004900180700c8003c1c26085000351b48401c0d11034036550003035019000410101780b4107004021a82080e0041c1011164a0b0300545542040b06 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 925689568 1250 925688318 925688353
    0x303070804050309040c11060105011409210102070f11010203131503110f04030b010b12040b0705040801020a1e0903080a0c020103150303020106030309060305011a09010e130f1d 78
    0x1d03004450500090041e214140c69621a40c0d036060780960f00c031088408900031460401ca010381145040003c144140c0003c10401000c4030504d6600341e0702c0150148001341c6284502c4012079000e01c0c01d5000040500c103000703d2009203031426014000d40103071607404500580e0b03a0b10408801c1e0040d500919410041d000984a22060f10380d4241004580005070404c074180d198004580214800001710341403017030025501c41c59003d1b041c62102507144c80f03c3d480810882c04030041c0010500000c0c0000a01e68500c10010303200104960002551110103000d030242a4aa501060103081c0c40744500140469105041c80c00c11030345c20403030301403030071203c403a04490703500c105001641859280c000d8030403880c648040102c01107001c0d9000245184c21868000c0c40c0d03020f030f64402c40030141800014002040f40c204d1560f0410410140036960302c60ba83c0060703400c03030205825198400003200c40c40c246120f190300050052103901070b04100e031a842810a56103d19000d01d000c2065106211041034048079 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 925690818 1250 925689568 925689571
    0x10f050715060308180d150c110d0c0b090c2202040b0d02070c0b0a0207060c11030616090b0a05040509041a090102071b030209190e01060b1c0203070203030708 70
    0x2610700851409611030322400b5100700b50b100b115014400200070300c6102164813440c2e6225400c440034040500c0c1601e6420319100e0046000000c0343d5105a90820127006101c9110f6209241003a101003000310704015000e250180415034180e0360800004d01c118a020480444a50004100d008074040481030807541940c14503103410b0042d0301300004241c1d0580d401c041c1c0a100588030025039620303402e00c2d00c0c186012190340b1000400314144101c0751007580124042c0241e8400c0d181940c10300550382411302c120742d61100780d1a0136003e28014010380e5020a03c0c1e0000a60464807031850445c1d4425003c9441e105a00080340062018401407009151a40c1c0c0c0903000b5002c2c12030110012080d185c91032044105a60540041e980090b00004000042e156242a2808000c03041845403940d0081007c0b480010306550b9841030781c164044909000e070303005000c4c4a0320078008128030b0341c41b001c0c8080c0b51341c070002c00c241c4d00214114035800148458022248a0010b41d0702842c110b880303049040d20030345130 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 925692068 1250 925690818 925690823
    0x201050a0b1f110304240203070c120201050702090a050417042d0915151d21011a132304030201060302040f14060909190206090306270705010f0507 65
    0x51250304000f28440400181c4081c15208136400381d12152084140c0c54030399021030840543d0401e00c40e104c04680d440c0c000900319500034507000c0c101e440500c01201c40d4810060000d5200110000340504003805502007071151740305103e2a00b4204030141202141d015501c84c5101002030782e048042131030341c0c00d400480300d43d018210302043d1a07184d44000064906186015100071a00c0c7c03001c11442c004003032100c41e060401d0901c0039413440b00100c0300340803002c000782c0f150050008040703552010700e4403803c040303040034100020041c0c2c130444040d0710188085100301c9846010f0745145108540c00ca445812801101c6103c0d15007000300c903804058020344020005d4007995130f56007000001d6160350007100341d940040c1c100010310500c08040034000c0040507128a004869010030000030400005842a21121000c8802c280c4e111620004070244103e03102c0036094000c0d40d041c02058805043d49030498050650003c00c0d25099101e42c2e580c90120b0b1103140d00048401008001640c000e5005101990 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 925693318 1250 925692068 925692077
    0x110405090727150627031703131403031803091e01051c06180e0a02010e0f04021b250e131e14030702030309040e0c10030c0201050a0b1f 60
    0x10801c58015005841d55801074011a01924075240b6044403865200051880e03200d02404075405c685541200001c0d4104c1f1407215180080440c0300d400044421003051503200e021003084204440c06103480342c100b40e6100010030007240d074800315640c002c0159042c0603409030103074100302145007106103803d00356004a418001c04001d081c1222041d01c00d200b09005004070302180480c54202c08003009240300381074040140c6805140014004081603507071b0841e40900c6c0c40c141704844400026a220f0560000030750003440020340c2540030f89002c221a41941d488002c0c0c43d0801d00f094071030314a40c00f03140103000c1034400b40e00c070601c040c0146102058110310f010110401d18400b6a481101504000503942c015444c0103214404000391004010600c06024000d10308081c01940031950b01c0c041d46810a02c507035110b81c20202c03200820030a10011400082031008101c2402002074010154218100d005500b40400142c0900c06405124503064001c1c0045e244a075121001000000364000c2140802 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 925694568 1250 925693318 925693331
    0x3030323040825050714060a02061f0510020a050106060306080303010b0319141504060b16050114070527060d0c0201090605010f0f090b01020303010b0d140103110405090727 76
    0x1101c043d00841590300c510000c290407418000003081c00c0741400c0d4900c3c42498100982c10a9641c040740a42d0001001c038405c00f2260131854404107034514a4000507089141030094840300369002906a0210f80200c00030030410741c490004a050340e0f03041c003422940d60b008000400010424030011035200a040030710809a0740030031420350644030b280c3c103285204110042842441001e0b4030205407510400c4400f00029842c3c11510b0b070f02da0040413038404010318164298014008290400030030201101c0704940c00780b402a901070441e030001040c2d05e451002243c881e4041c045198160280710b40e000700400c3c00d1884c241d09150180030051b42c0141103540f2580400001145800b43c1806800303110000500681025084021030300c0310f911070b040c0207092038104c0480340d03004005c03681501c0002e001c040d950a5061201c030b000d4042c1c00000c80c4182c25420000040c0012203a50100c5c85030211000e004c16180c030b409160b40c1e45a41d00401b8240b18510200c074602d650080e0315151441451080420313071 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 925695818 1250 925694568 925694617
    0x110f0c0907050f0304060c0e0301270c030b0f010f1a0304060506182d040f0b09030f120132010302090f0621010e0c030a0c0504120309030303230408 65
    0x40d80058508441c0262100c28055103103402690060200c001076000300f145071052040b144103050680440904840500703252f800384500d282c0000080c64200214200170301300800d405018610900c41c1000c80302e403c450105003203070411b0079007000804041d0032500390384960700ea80c8018030010b400e00e0340c0185043c110043d03040350401080c0c03080e038541050441540c0c1200c102040c1c84542d001e100552141c041c00c0100045241807400140f42e0040401c030007a81d03c1c43c0350140b0310321880c10b921709400004070701248003010344e80105040ea0300c40c0160080024000014441110b4404044850010601165400c6511079400340454290007803200c0d01c0d0008500226078298080d41a82640e103002d2000c540549440396000c5006154000f280a5180b8110081c000340f400003400d619826034545070340c0c1604900c100150b07405020b0750a84000650850300d4080d200261038801100420b08180c4540800d0410101589040340c450001341803669903030b0740b030545940c0729091f06a0107207824000701c4034 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 925697068 1250 925695818 925695847
    0x5030f0a0b1201050403080606070c090b060715052212080a1118150c21041a07060f180237090b040204151803080c070303110f0c090705 60
    0xb48001d2400001c0c8608013800c0041984000030701690041204204c100700251074803080c00304407810346070002040f480d190000341b018491400f0107003140c9020811a03000f6506540014019002d545602281d00003a45041101080f0807001511464a41850303038030140c05603a00a902200f100d40c0000c01050300b80003203000c0e0304501d0b000c40b81d82004012121140c24000030301c00206490b001602d09104c000c01d011640d640c0420714426031000045150010703a9030343d5080d20058850759008803540c205580c160306044d00a09800d4640604120500300307024910b01c00c0265040c60140148046a10340c1c080c0500c6403607100f40100700750741521401090030030b01380031101451000d84060300708a1820150b01d054030041580d080c421881000b04221400c5c00200401d440c40d03440c14404840c2084245900f0f038480b44e940084d003c06400030701501650720110f8114140d80c440e8860b005040e213002a066910000303101032011503407120103626040c1ca002003a035940a4842c0c07400e507203040e504514544 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 925698318 1250 925697068 925697089
    0xf04110402040602011e02070b01030f08040504091416060207061107030b070c05070605041d0a021603020606190b040303180f140f0418060b03030909091e07030305030f0a0b 76
    0x280181d41d1640f000181b00c49007904c43e0300d4008015410341c2082696200d21189103018400103000f98040406807041055050540f401804014410401b11030700341403641c42014158401c074203900800c0d106550790f910190a190a0301d803258024030840d810710a06039044e0450900424031845070300f40000c0050fa11801141c45100f0580d101106000d2510305140342640f42e810940078440c090005000c1c0b1480039100e404001c2903003c0001c800d0b158546010004d10441480d80c481c8181d0904110a15400041890003034030255459a9402901055200d140761a030140b25040801003004201203071181004070703106821000c1c000e50307182c0c1c0c5007050821041560b0180029225034a007409032480c4c032800b101c15091090320306010104544240d8200566802d9009055907030b81e0840c6c040301d84080069440101e80504580713400d0422006181c0e60356000c080c0c041d04045000e00300b11103860301255820407641d00da04d41d5030840d2100c1a0046420348014569180f25a80d0014000195203230304403071 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 925699568 1250 925698318 925698329
    0x3060c0e061b0606060301080303070e150309160911070807060e0a03110d0e010e1519030e07150c030c020f0604060521010810200f0d1808030f0411040204 68
    0x10020142d02000c503030030200300501c1644501000c1c401046204030200490784c2c401ea0510300440c0c180c01d003c2c0080d0180c1000071103003580c104044200901c4080c0014800038941044010f811010341d02c080f211709403036005103580080d074014032600d0f001949101c054000244903000c0418009504184c040c9000c000e140241d001a0300703030f095016650070500141410b0380e1a440e02c0b002e01c03101c1e000040c0104a55a01e143d00803404a210510000c680d138042d46c100c0300d00d18462419a103440318009010700340844a601c581e00401e1400200515204028080c02255440f40030000c012500d007614003420030329007a608424000d000c1c1c100765440c0da004001030100d030388903d6111000b0081d64141e03c85d0a1941c00302520399440107100c003083c0002c81045804640102003000203400d15102c1654072003100c80400c007407011400900c07880c480d501070502c414810f40300704400c00100d03861031240c4484e001d002c0c0c109902000800c5108200308201380d48240904400c030012001c1d1000300f070407680144d215 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 925700818 1250 925699568 925699597
    0x22103121602071202061c06090e0f030703020c19081f0b0301060602120d020906130303080f0103020f040f092126070e01021e160b1303060c0e06 64
    0x3000741c0716441c1004909854601d00c01001118205982d9880c9a0400003020f440b0301c401040d440c2081045205518a0900c2110140181c540d10101940600038042c0c1c02600b60140c00d03000c0703181450000a0b03c0c1010380542c02040600704010a02c801421034951000c480705032b500700030070590001c218400714003060031003070000e5040a09894007241c0b070007441e8901c41d174100384040000031b03070005081c03d4040c0506025556621441c0401d00244580b85945400450104462800e09000c259880440c0c3c080d0310b81140680d1807040202c4905000d0000070341c0020a40b40075410350906600408000c40e40c0c000c0080e10b0710098941c14000c500c280000708001c0c0314001160149a4084131200c0c0001691405800007142040706228402c40202913804200820740e2550b41a8401c000c10040c4d104200c440e50041d894002d012a191050001e0030505141c0080d00001c12605850840c0c000110042e0f1111444d4110ba03900c6c1c001c4d000c40c2055a00308110a081452182e842500401d290b08000c0103 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 925702068 1250 925700818 925700821
    0x42a020d170a1e0e07090515012703060e060f090303010e13030c0510090510060605090f031203070c0c21060b130f0b102d051209060f0105040e070302210312 69
    0x50010a440d1f00409503045640010002280ca0b40c000001c4075564890700310302e280600c2008240701c400c0c07665602c080c1c90a070802e40d4000c40541e0103c0c8640c01611034200c40320071a90b9413060560f030ba21082c4122a000a1040e0009000f40004809030032602d2281c0b90501f04541da5854103440c0641c2017050090440e900c400c035108101040044840e52011003c040c440b040c5440000303001401480d200d01d000e560062101d4589517000d0201d4514514070440c0280c9a080102d4010542c0323504c91011034003860005070200e9095456200403e039140d2022840c04d0b6600039660701005000e90f544c4094000042c00103400381040b40d4011180b042e80c60f5100050100c1060007001103c5840324078080510014100b001006141d403040070103070607a6001c0603038800750003660441c0e4912400711103001142890040c402820000304001e030050b01c1640354030741140d885100b000211000001c54990f561f004607410001802e1042803a400d02010300c202c40c07401442080c2503803d55001100d40c80900320b1910 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 925703318 1250 925702068 925702079
    0x4110a08070e030607020c240a020615010306030f031d100509011404060503010b0c070b0703080403020f0d05030a0b04020d06030c0312030e0d080402042a020d170a1e0e07 75
    0x20b2500c0d070071600b140201800c0c1800308001c2d444141c1650f51602940c035014014010a07062105100904200781160740d07070381c45040c0000d445400039100440140c1041c043c400d03141d0711174010350007a280c010074281c03000c4802d030b03605444071044820407070ba052001700d440456030750360032458440481d11b5440c1c50f692052540c000600c4d0b01a400c906024050044c402407010b9944502074134152465805265940d080001c0c0307940c03800b085507005101280c0001a1b0300100340c1d02c0800b081c0107920903021254aa401506410740f1481c00c03100141c0001c03001d00024801640340d0308590807200b009040145002c0c0540c110702c0c182e616940064400310000b0400b00200034280491900ca50074078030381080100000c0c03a10540780c2e00741c4c2d100141088506008681503607190f52054640c0e1920354001c81c200b81f203041c0b810301c0c05a51129500094010081e80004081c0110280b95807a03c9041941441d590f40a02031401043c641c6c44581d941d0550700c030300741030b00f00e124844c400d14803030003400400c4007500e0030 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 925704568 1250 925703318 925703327
    0x907020a1202031c140c0906040902031f0602030a0f0f090305030301081b0105041d10050402071b05060708030a0908040f0b0c0c0402160f03030b1306031707021e04110a0807 76
    0x55403907400d45103407810440f08215441040340c0c22080d1006d10780d40c0c9024220000304580180d8101c0c0b04511310000c144929917480724500e046160102408100380759903404140d88900401e034600f80440d01c00092694110321070f4444184049031424410321a60b100d071102d5195070826000104d09a000000d4002e50b0400340c110796010328000d203400303480c050505240d00c040b0b40343d039002031030380369540801320701001c3d2001150006044007401c110b46507c040d0400c0c2c115482903519031500b0b0050382d40f01207140e007040700c00c40b003502d81c2000080d490350315400a810014001d42c801a01c0d459403d010104100700c05409100080003001d4016880b844411030440c00d0954003c2c2980c4242c0c030403c10784158800c2821040c59280d0083d4075a42d034109641019000340c01604103180e484500704551018030708540d4000300070389000e480151840001e54280e44114442c051020f503024180b807000e0f40c0c0b2209850f40c0d4100300304000d440480c1401d800d403540c0071560054500c40e408034940004015486620 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 925705818 1250 925704568 925704607
    0x15050306010317071a04060b09092107061d030a020d05030f0f0601021e030a031118151207080603060703060312050f040e090d09230907020a120203 65
    0x850260809500d10b036070f215050700400c1c03505040500d000c50101c0500c14840401c603081c420700e200814940c81c02d0f00d09031005041c5204158890300c0c80740301181c1548000695000c45100018000c40c1c0d44500d0380408280f50008003040b00da094584800c03188082d480706008000c41501c01c001d51310340040040180c140f2250303070003202c20040c0500401034012030b0383d2003481e0407041c0c0ca24481d04070744032100108d04008203240554954850008110b808620003c0100341040704c46c1e86c200200940c10b8a04810b910482044030540c1490980c007045a00e05160003c01404400c8680751a242030442d2107050344c90101e60082c0483c1c003034410082c035804d082c411184d01840502d410400d0301e080d0b6844005194010084404010780400c080104510303801c00c0398060440712000d4540da1601803006903642c1c020449440008168400002c0d101001c2d18032000e00b504102151513040ca10001880301d00741e0010465000c44c4175001920000c01c407803000c5110b41003003c1d07000d50740da556414401e2401010f07 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 925707068 1250 925705818 925705829
    0x1b020f152712190e0306040212010e1e01060503010207020607291003031704120f02070515040807060f020703150902060a030c021b090402090601021f090221030a030b121015 76
    0x2075840f401304a65004a4219401341d41150302180c400f41b0441554010940891036080d07a00c948035034428814186094400480700207030091181c00d40307400600d400d0303018081000350041b500307000a2000558040a0302242c030101e01070803500019030203a00744180800d85142c000c2c400103074418414103070b010040071008046642c0280590400741d440c046003d8002010b0070411954540048406109010200003400024000030103081c03103000950690340144241c0d00c40c3c0c4100c0740c002900360f0140d1040c880c0400c0130b401400010b403031034840c01090980f4020981c0d01075640c1c180000103994907405042d1044850b80d002980108845002c2d140c90001010100300c402008107940701383d503886003426030240d41919103100a032103c1006070305d0090040c1c1c141449041d054085082440d041e48012240c0380200c580040f03a54910450580d401e258402100d12034104000c0d141e072960082c0c00c0340c403544078054501859801e60041890401c013051070f4040d400ca13210018008954107100004020700f1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 925708318 1250 925707068 925707077
    0x3050c060114060702040b060d0c02011406100207030803070513080102030702010c1b1e06021b160e0604050403090e070507030905040b0901060807030e011b020f15271219 75
    0x40b18400007a0940103c120091050b030315100d5410302c1d034585030103030303000e400180344207000c51642d541010703010b00382c1030300c0107103088a4440c001082841e1492040403031011a4000d8140076043d07403641e550913400140004180701e020800c00400b209070301c080900511400f400140c5034200401c0c02800d4845c211040010002d46080402803034840c402d0040116500101c1850144180c061891030303407400c18805880e4510200d06400404004542440c0c44404001642c644e040c03802c04408440c00c507405104884280400011080c0c10300380d111a030858080d0400403a46513030350855840b80e00040b00c480000400119a80b020942c100003007102610b8212000d0003080034040101d002068148101420800e5400118000f240260710200c0301306103c1c80244022040088003080c440e4605000c2070062040110091214102203004450150b40c582d404110f602c070780010303c40c00810b14a01a02d180e02103800c0c00c40c50241089894035190000080c55140c805a00740b55160340c0b42c1411140910 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 925709568 1250 925708318 925708349
    0x80a050108120c0705040e070f1211090402061303030909060b04140d0f050a05010b090703090b01050105031f0905070314070516080d02030403120501051c0b0a11030403050c0601 78
    0x112808100d030100103009211450b1a103030001c2c40d9500c0c00c40700d03174041a003151130070100700003610000c18041c050310410201901c20942d074411841400301c40300005002e441c0100c2a241c60ba1410035002600140001d0000307080c00f440345003007182100c0903801203020520389902081450801e0107884020102c225101e41000d141c08400081085a00d40303103442110a269000d081040110004620940240884218980700d24005000746070380c500151284c3d00240004190038881d025180020750701605422050340307000019a0150400b900c0c12007107407440310404040350b884005220060401500200791030800c40d901070100c0f4207104041041003502e04c10070004d160840c003100c0c40c0040f9120481401d40711420f0010321405030381307031a00200d400041484103042e03005100e02003034208000b00308500d0343c0e20380802c190000c0c40544510f840285844c9000450311070040c0c10b80c44100c880300440d01d9540d1241960040d40b0448046001c104082060086400204051400352a41d400c005000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 925710818 1250 925709568 925709579
    0x2030408030318030f0712080a0605130e0309040c08180f1c0c082a0c031e070302030118060f0c081609030b2403010b0906010c14070312080a0501 64
    0x60b03200c000c0001c0380321102c00c2d0703c00038840003c10441d0001d120204065413610b00718078003801c1060642c0700c50000140c00c500030611321030451180314100c40c401030007400320a403e060803034050007004024041600044c00503c1d0b994581d8002c540c9000724542e07503801d142c9088420710481c00c0c060b0341c108420740d000140e071006440c03001138030b030464000303407499042184d021103001c559640001d0401094100c01080500b041c0d450211107110740640388045080e1015444841592030800340b510540c90f601c403480ca0f0b03100c0446007040c040d524220300203941c50300b501d0381c020030309440150b0844402005071000c0c06081c401a40f0510a0300030301403034244038416076035000a08807903001d412409120241c4540502d402e0041030050021903200c0d401c20f09610b801814144c18640d030801403400400203065080d0145418441e10120030780042510322540c03070f498011202d01561050444050b0782c806050a01c2d0201041303900000c0d0b12550071012035041c0c0b65401810b2601c00381c103003182c0c0707420440103120 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 925712068 1250 925710818 925710823
    0x110a0302030a180f030803010e0603150703090609080a08040203392403061509030303041e050f0a0c0806040308010b13050415050f0d030819020706051005010f02030408 74
    0x1080c2c15519190400d149004250107120a003640104814556941d0000c100040200554100d03044448428000c2c0e0f544020700d1340b0350440d2600c0c21180c011101c00601068025031150f0103c50140a00052201c025074400d604d5510502035100860200406c010442c07400300100d940e000001440c001014680794200c10164804a41c625542c001785c4035101c40c3d503166150580c900031300c5000d070010000d80000f40c0e82c1d056441076801c0e9000340d240c03a010303248160509080300c26042d0003400851840d990b03a107070250500000c0c0d040003c0c0701510542d8a0208408002502d01a8142c50240c0803615181c580b142d04031110b540f040003031740c01000400001c00d0308900d0750b90442d03500364000d036070f0343c8298000d919a00300c080d0400344c0e01c10f261040b4032a00c42c01a05400060f10810745020000f40c10303c404100e152612102c0c0180052030300c0340042c0c040c0c40c9040920034941c00f441005824880c565840d441502c0741124201c1c13500c2c001c1d120420056078000300c2c0d03030345002844c0003562038a403c00c1c06180c0c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 925713318 1250 925712068 925712077
    0x4180507090f020d15050901080304210c050a1d10031e050f070b030406051b0a1202091c0c090507020c09060307171c1b061a0a090c110a030203 63
    0x118200d40d90b4400d81c4400310150103c40381c90000200c20000d41030b801400350381e260380900606000c0c01d600c3c000850020000002c0741c007a210300080700f011002e404800d2118111403400200d070110380400700058680c50b554400005401100d04002c0154000704000b402e01e28014828400203030110720810105906407107074005e600c4810b205020300c08176410804d19260310b03060f00f06042d20079084005084d40024000e503026030b201e20070a104030307280c00c007400c802c480b4414101c00743c0003010010032110502403000008036101c01c6402500b13104010000605005081d410710f030012301140c8441d010440001c1a510150080728002c0000d820306040c022355070307000199054003481651010503200d981c104480c100505062100c0c401001c40c2096140e00c45500f1780000380d01c00d0000303100700942ca014003420202c1d4140e91482019614090315510003501c14050341d034a84110075080582162984403004018007407220010500c09040f080c000d040040303c0107101115001b41c003079200001d80c00310488 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 925714568 1250 925713318 925713329
    0x711030a0e040f0b190305010f0e060c03130b011212090e0c09030708030316110a030206070309110306150f0607080426030a0c031403070c031817070504180507 70
    0x1503e16011420340000c040380c4000e02c2d8040800c240c03a0400308080c900c40015640300d0002440440307174081c000810749900c1c40000c0044c0c0c000c400041d5401c0c41a40280d42c1c000409410310000904c1c03502c8078081642e082c1c200d040b11004182c1842c05000780d41c41c180c0c11620a524008105500d000c0d415041004043d00095441d4000646140250340c00c20001c0e000d00071038001e890356800c01c1c003001014a40501c4c100000714500e0f442c11750360250040341c100d80c165050b4014203041d98504000714010300002c10112525000d680c50701c1c4080d10208141881043d1240c45035220244c203504120302100d18401051084d42e0400503030300011b0205007030340c1c01c40340803a400201070300700200c9c9801c0c400c0050711b8242e11807002243e111007566204400f0165640261680907413086a14200c40300c0344801c54032007020920484080e00080d2060b80000b10741e1030000102601b094440301d508400000c04d01503a4102c2d0700861082c01030b490540700c0c4845840d281001041035051076990292510301501c01d4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 925715818 1250 925714568 925714571
    0x31a070f1d13020301240905040c03060e090c131a060901050c030a0c2102060609040c12050f07060207050a0605130302040204032303030601050d09021906080711030a0e04 75
    0xa04010201c04911248030400408440e20710803124000b030001d400902c188034003a886100403000c0ca03040e400180040814907911614041d00300b0007072101510840f2048400c256541c480010701d10b0030009242e0055016034068041020190200840f028544d680b084040317250902810184085412031445044295030741901c1d03000082c0180c54500030601c21600c14000010708807449940a0307038944510744a0883c00c60481c2e4561000e105040844a0b40005603000030041200e9282005689612500c0b5181041c0c0c5141c81e50184280e8a803205821202588030702807003883d050042c0409806401203100601da41b03840c000001d50510003520906091200c00213400ba0401c468110740b0000d1600507000355561a507034500a07030001c0c82107c00800300021002d074200441070102c2200d0060b90f059480c00d0610049004920051516480491388030700c11440c2c00072218a401d011400620321a12168002e240c4940702034000e412040c00c0803419003040044050340754000c3c1180540c4d12040e03a0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 925717068 1250 925715818 925715837
    0xb01110610120c1502060106090909021c05010603120f080f091507030624020c0d1106090111010c05092e030b13090b1603050c0409050903120a06031a070f 68
    0x1000c1202d40703c039070014640c12060a0b0400b81c01d913000035845041740e0840d502d10303045964480d504001c8412210000754081581140554102050f9100151031409440001030580d525590a54002e0303030b41050001040040c100858400c0d04864815446819a20208090314009814544801b80036029034241103d070b01c0442c030750302d2007544504042c15044000903001c400b24458200324951034401c0000601ca40c00b900360032070500141d08070701c040d4008035130400c888001041015640240361024100304094180103240f02c0300b40180c2c3c58041140e10303601d41d1994490240820307800d2014950071885180004940c2c5440c41d0380703ca41c080003c906c0c00040c20000b250005105041070382c440c1c01ca4600300704505040c02440003480307001b0345200901c031040001c80b000030f6040d954100c1d207034245001b05000821031803500d50061640304508406403403501200d2442201c52510075a416000640d0b41c40080c0f00b0803445040041c040e003203071000c02d2003618114400504d60140c8100c003200b00070b511034 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 925718318 1250 925717068 925717073
    0x10e03010218060307050c0703051608031c020d021e030a0b01020327040b090415060816120201200f0c04050c0702150f07030201021305041116030c0807060b0111061012 74
    0x1c061f188002414003c0c1c0c2c01e8180d40b400c14a40e104103001a40110802d0034500041c102d40000440f080b0604810442244943c0000c2600094003c040801071980c1c08000c4501c00e03600003854620b1130001c03142a16240c5c20048013074000c5455804000b030656108110340f09035400102e0140c0c6002c2c603000f4020740d285841a000c00c0203002c1e000500c5030412401001d000030020100c0144204221340c0c10104510395a42103619543c03421982d50340c05441041c00e0a0222f2800c1d00080c1c03480900605024603c10440491410303400c0d1940c80b84c0d0440d80000c3c2d07200041001c140b001c5101d01504076014461030a04074125400c51003410310003407191946503a01c925207010b201c00c0d0380d00601c1002c442910f42d035a6050181c00707584940608200d40c5034499001c20645814840d14985044c0c1c80c185a0400f0139a514080c02405141c20540900c13140907807240016070700d5402480518800c400c00f003a05c0e00000000340c0022003d075285c03921038020b001004150540e16030000304980000c01c1e4880741d0620360 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 925719424 1106 925718318 925718327
    0x140a061202121203040c0303032919090c0908150103121d193321020703030b03070e07020303060d02010e041a010e03010218060307 58
    0xa003903000141c10a08012014101d400046401e0f01c0300e03200c01e5480640040b102120800c2c075140d000d00c20994140039907640301c03038980618218803441e2140303101900c3c50001034a0103500b8924001400410b01e010f92401003007204410094402d0f02200100004c3c0d0601925006200e003840504102d001c9840c0742c0c0c1241c8c1c1040380c0380104ca400c0c0c0b4040361144071071513807164140303c00080300010340c0d100c000c2c01c0c1615003007101740c00d4070501d02501085441a90501c240c0e800d070503031a20500c1d24152080703180c1c42c2216403424520a11148025622001443c08040c501c0c0d48086007070003c054144e070260320344203c22801c8400d42070380e41c050042c404104903803850060708140003098081c288aa06c0640c481c1c414103250701c8580c0c6130f4005c60215020180011505c8895506000360380d604160171101589017078000b980790030203401000d01c54020110296008100000005402e240329 = true := by decide +kernel

theorem cover : BRFrame.Cov 925539568 925719424 := by
  have h0 := BRFrame.cov_init 925539568
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 925539568 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 925539568 ≤ n) (h2 : n < 925719424) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
