-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4230
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:56:18.169732+00:00
-- url     : https://prove2.me/submissions/5a64336c-6d2a-4640-a111-3089763e4889

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 760611510 ≤ n < 760791366 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 760612760 1250 760611510 760611557
    0xd2406140f060a09050a0f030204060918030f052b0b0a0302060f210c1b06090a0308040c031703070f18060302031008011803080105030106050a0b0c19110f03010b01 72
    0x1581082813510002c074464079000109000341101c500140c0c2202d00e14030400003600d01580000c03011a040103002200c500350240080e44050f07044c1000c064a2821510032641802555203030003040180a010382c0c0030b07042c140c4908030b003119189002e00014000c00c041c040c80390103a10009400101c10000d0504035514440500088001504480b80440c13840c2a18541c1c89010b80305408090760008109a04034034158440380032102850280c11585000700001b41c84e401c0f0002c0240601282d200050704003c25100e036500a158800403040010442d030018078807a400880e5602e0200f204005850707141030090103040004058040f0b128450350610320124003030740014003401440b03c44100040340e035440a008940828a40710b484003141301050070002c004d8501030b44032038046e9250403028022a246c080b041c0050780c03a07107104160ba0340b03a103010003803402c0c01400c20204401c460340000c40821034100505601031a085a1544030740e26200c0425089030208901c25020420740ca40e00d64072007031140f205 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 760614010 1250 760612760 760612777
    0x90a140c0406090b0915030601150c063e0405060a0c15051902090f090403170c0901080f060307180908040e040b09030412060b0d2406140f06 62
    0x58844005111001c01c09541e5075810011003503464a5403240c8500341060456070140079406038081118170500401c0d00c0d1070040c01002c41d80001000c2801045011307800d101381e03860b801503040001c520100c08181030a020305d450348603810001c00c002103520440390808806010b0400c503080c6401d15000801400ea07028110010030300c200d440703a8001040580b400038040448000001c50030307242840946035030000c00c88100640a1042c0514002a20b540c2003403d448881940c0d0310009444900b001d40c0c40d8036400c03c0d0783e11500c561204000d10a01404060130103801c2c203803100c010649030380c04001c418010443d08160554004035040060700c00c1440310844404c0750f0500054000074540324044954000c2e000343e0a400d00000c2440200820242c0d4198048007040146003032a0401c0c860000d10341c43c4020180205071100c038185844d503a140c4e2001c1800758007100384201c404052050381106158004403210729450040d000410045488001d200050000c0c071040d4810060010400983c001d10308 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 760615260 1250 760614010 760614013
    0x190e010b0a17061f11010605030d09050d020402070c03030c020f01110c0d0602041a0304020307140319021306120b2a070528050c0301090b0103120e040c03061d090a14 73
    0x4000d0131070070004040e05a800c08580d10740a0510922004601796092079201e00c0c0668841500d80b000700e54460303180c0042d594100c0b0340b280e000310f84d80002070180c0250720002e86202600c0d0400010140c00c072602202c02c41c400e8810010a1203070031b0054600d6403003074200103000d0b004448810310324070b005002060030300d200d5400182410f840d582c054005401c08484694110780000600c020b510701003140d50000c1440c01c3c4103800c18051080482e4480c41c10940d11943c40c0c000412607000c6658100020203a0951b90404210480d511902c44030714110f89141039030080551400320301140074490390f20180030041e4403000d60800c09425855055030180000751094021007142d030a0750100e905849900d401c41c200301004141645c2812424030706d822010501c280c0c5017200120003ea95010031300e04494100d0306a941c01c104000c41a58400001900668454549031383c1c090460381582c015025a00945030441072000030594088080c4002c3d40c0240103603210b040301c10002548290080c021010440 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 760616510 1250 760615260 760615279
    0x70f0b04090c17070207031509050d1d041104090b0312090d030302160c0312031a040e210d180809120a050d020a030e0d0c0b030601090302190e010b0a1706 68
    0x205451070705041d200131006030400da0040084c003e84807000d001009059a0800c01e030441651000e41e02c1d505c0c192841c003030007602e103140d8a0849814002001482d4040d00510003c4000c000600b0f146d4410b0140b00c01d050f2a06002080e141400210b02502804001c00b4502d4107840700d04020804000c08401c0b42016020000303a0441040b9426102e80c0512484403440c103107045d45441d031200040325842ca0101440d0000200c1c074102d90100300c5000300d030196000241c0b041c22107600b906203c00d13040d0840f40ba00300b10000f0f41d605c6032020700400d943d07000000100003000304e070008107451013a00e200242142c6000d200484841c0381c0b42c0c02c03202807080c08001f00e40c41101503503103440c14040718509840c00340e04038a080c1c1d03051540003001100c0710407044480304801d400d0703544d45c480203007014000d08003019004800a42564007400c0704201968006200e00b505460714007400300c2c0c030707815401141100c150400c00011480000c1c0d00ba680b00e552551129280b4123010394101d072140b40020001030303100e5600f4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 760617760 1250 760616510 760616537
    0xa031106072012010e073b070e030d0c38040203010c0f0801090b03010e0a0b060f0d0317040314180a090209062b232a030a0b0a0e0702070f0b04090c 65
    0x10300458101780c1f044104c001680c90240782c06070010403414002c500a400030300c51480401e520100303179017072070368441212102c000c0c00080107210304071419514642c28100300c203040e0400c15484441c07031140b88201c1c02030144145201d82207600031140801c40b00412080c000602401d4030a42250302e2500001d1300001d022511a03881504c4e0031039071030094501500c8082802058200b21101d41c9a502090f0f44007051024a65001000c2d20101c0c088220b1015900020404040c4591804000c0d5803070798030215218068000300066208030b01e60028400c4007090030000700398100b802079407a1024001c20907810040250a1040074100f08100d01c144030031400d070203000200d02c500c40c100f400d11030141c010b01c1e004941d4105a41a9030060114400c003540642c1900c015030900020f80b503508070302c803681c90312a12100c600ca8040d15000304810f034040343c22200800d00460200119200380c0540d8200c41ea59551640044080c414a0003010501103041105001c003c901d50031880c000001e40c40c0a519800d030b11b = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 760619010 1250 760617760 760617839
    0x305130210050a031a090c070c0302092815120302100609022502060a0302070303181208010f030f0f0f060911120105060a031106072012010e07 63
    0x19100c200000c1807001ca4005850fa030b040c0304001030400d041800c1c4005000a0b40010980c00c0001c010842203440011408100150004000b00071580941501d01e1401c0050070804410030500c0c048240300e0600303262160955590140044403030004480381103031800c0540c01881c60382d440700e0a40540c400c03101e103213494105500c41c0c80000c081c85500181c07220500d2440702c0c1c03811401c1c0d0381c0300511702c101c1d200007001da9141c00c111443d0340c40ea820010ba4032251842d0a401824000c405062075000444506082c0882c0811601c1c81030100e0396605641c1ea281c07654204552600d01000c0c1c100c502c000e60180002d45030f00c240910740b6004414000303d00185a5929040e1203000300c0480b000385030390180c1482818012140c0380c054010f807009010600e0000b006c83c058800f540b00103401160032852580b186d8860408865020b5008a0420048003a0074200200e401c0c50b944000e005111070761003141d80000600c9040c1b407115800010303010203850143d2082801c061100800e4038540090041081e4058 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 760620260 1250 760619010 760619029
    0x327090506040b09060f041a04061401180609060c03050d020c0c01020606040c170c04170102070c0605091f0203091801180902090f04050a150b0907050f040603051302 73
    0x14264041030518080d0184000c0c2d40d10920712501030101c89051001c3c40d07a0b0358680c00039404050f100090495001c204c02c02500840351800e54010f4a0034074003080200c014608010300d4002a202c050440008951340b1110390034920a41000441104040c0901803060b183d0b1207100340640ba1042c02c00307009070360a504a80c42860b440c1800d90200d42c41c1c00ba00d58052100c2c9501c03003400c80b410480180c0002015204000081b42c010050100350001803c418004007600d01603e20404901c80300c9180e206024000d41c005201540c00b40311900001031268807031f070700b00c40c28400f02411105801082200015604413030010000a50100f8000040c2644490200c01e044002e260114003095140082845030018003d040f685400d08051422002d41c5031440f249130455005c901c1e8005555850500c1420101d200c88020070340c0078021840c2d8209081908101401401100c04043c1510f42c8002920b1504c03c0e040c0404c0d40300f40c107000410000780a64085603111031308060050344400c0c070f50300140c0b0021 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 760621510 1250 760620260 760620269
    0x3080c0a051b0c041d07051c17040305010b0405060609040b030109080c030a090b070c1502160e090606010f1e0203040b07030503160e060706090807020d0b01090e010b0d0327 76
    0x74410b80c2c02e49003524090144118051980d00b1a070383d17241900310900c0e12a4001d00900340100010032560400042242100c88034907040301c03040011058620384c4441552041c401520150300f000e100321021320382446081d01074040146132603c1d04200d442804054481840c20ba5070655076241d41601242d071400081080e02d000318090356981e0070801001d000c00105401c0000c20710020720805000a541c0701110f025689215443c199011222000b01d2030a608440d00c0030000c4007003440058080d40980c15240101e003810261a0503589000c01150b41107482e03064940081c1e49a00b01d204644407440d8819507507a0148196481c00b41c84280280c095440b480044000903c0081041310303104905c01e5080d040c1030300d440c119421890100014240d4000c40d4005400030740d031421203a040180c07600440c5da40d02d5018050804044107814111965042407140e0740660381008021140c00c40c040c440c400c1c44107001031246c5072544290724100c40e2104200e2110204403005000854502d41c00e0644a0042 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 760622760 1250 760621510 760621513
    0x501231902010f061403060109091401180204051e0a110729010e0907030b1008150a050a0e100b0114040f050102120304050c010806060f04080a0b1303080c0a051b 71
    0x2900f9200200c4042c2e50140c3c04000e202c2201a00d180c0c1e002c10341c141110044000480c2404681c00d043c81101c402903911141c2e9803800c0c071001d4541200050400030b00380202c0741007046507102e01900c40301e45c448408031040b02da89500082c0c2c80303180c00d034170072520f045003e010705044c00920350340e4015032854403440031070300c0e850041070341c403400d808400e4903015110240c00d40311141896800b242c0d6800320f9010080c4140210400514450401d401641c000c0004404507019003c000004c0420380c442540c07440c508a041c0350000303080705024080c842a00040000400c80e249c0781c850498024501e455110b410007007110308080d50030415801902c06010314002d030140452400002a00e000d00d16581d80d004240203004207c08a1808141494040d2080c01c0c01c3c03400703548100000d0030503c02c0306c1c2d50f1000242d0200300442c3d0098001840200644103d41c0c0720421345501060425032410044e0080002c2e0342c80d00007a076030300c20003005080604d402d410240c0c2040002441800205d101070042c0c00759 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 760624010 1250 760622760 760622771
    0x3040608010807090605030607050307032c0c15160c0e0f0702010606020c0109230306090f1207050307030c08040e0c0a120b1c150c2304050123190201 66
    0x2c0c080144012001480c14240401c4484d140c54007181d1200300013045401402000300000380c0442c001e801c681c0188118070700010900f0380c040306e0f40109401c15174504079244903050002416043c06040055200610022241460005850400303d80d112400803940e864151350002140c55042d82058000c401c0d54618461604d09020000d00b11001a4020002c41d4000100c441caa66040000722040d00c01909050706043c0b13281645588180404001c00d03010300c0380d03a04005200d9008201c0f01e04580089040d6540c1d0f5151640d00d220341c1c000d024010303100ea0002c11168001070301540c8607844588c4200c00860405036501d81009085401304c0d400c1c0760004c000a180000c982c0e00c180b0ba821340d0382d00d1942c2007000c4034404001c1089007c54550720340c00702c2c0421046101344034a00c0d42c001424044e0002c2480104c601c054000c003003160803581043d00740648580d600f400d507018000e40703058503410707507403100b14400000a94882401c0d40c1103203c80540708010b0f1300c01030080315518068a00c202d130000f058 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 760625260 1250 760624010 760624019
    0x1412100c021f090b01090b0d1209090b0d080d0b0307081002120703090b01090209032a0a0b0f250516060e03010b030a06020703030e0706020f2a1e030304060801 70
    0x64070145080c80e6005150021100020702e044c41c44030305540b41e02400061404500c07010611900c402400981194007201b489402e0591086040e000d80d00003031403e02c800310400701442a05203581c400102001028000404c0070b507042e0f4404074102c80020300f02c80c440d565410825007400f00f00c0d00e8182c580e07134000441c00c2c06881680c0140e504000c20340360412041d9490f071a005405481030041150b040c2d00029002100d03501084a80c481a00b12040c501400c00c0001072900020002c40300b10b80505000a000600241010145c464000f0000481403800a03d901d0320818414000954051405040034810109104100900c494950b001070f0915031400c0841c05001d0b010008001132207681404801007490b00d003c07443d0300c90079501100158842e071352440d0941c050f01e0b104500e0401845007820005582d50300041d00c0e0100c0d2400b80642c0c44008146440c0c035000142c5a0440083e01075100d07100741103080c141d94031007481d508600001b0011201e00002415030f0300961080d800a11000300600 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 760626510 1250 760625260 760625293
    0x2130f060801030506070c0f0b06041e0506030d030513032304180b1002150a11031e07170c0a03060f09022502030c150f0301150e01091412100c02 64
    0x10b4001c10a1f0500c1d500306032060341e61030300b0f106c4440d02c0100f0886285002c10100c0c1c442c1d4001002c00041082007842c9180040703400002810203c1d078552107031280154180c01c4034081d100707030790188200f2000c0105510280d10269050640c0070b4109010f0706003030712450800382c21500948040c0c8170b00607240141d00d04403562107055850312007081e40b041d2050b0b22101d4216030001f690003100c0000301031341070b4169205030482e0f0040c1a0314225008c2101c00004205811030744400750401c1303905402c8450300325200c0b100c007203072800c001c20900e0402148850100c0c490707406c0c10010f410042554680450303101d46560780b1054091803035100020450300440d030108141201070310092000c0e25070004402c0700c9883e40003e81d0f2000003d508a024010460089603140d00c0c030011240b2501540c1c201c1540c80d40e40700000d1160303819209400c00080c078820410b1160350302c1102d03180e0413900105d00404003014184200040244410304481c803600c5001d0024150024600982800d281150050041003c03a02c034040c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 760627760 1250 760626510 760626523
    0x1215051e150a090b03030c0f0309010807030b0d021e0406090e0f0a0506010504020f0408010203010609061d0a15030f09050304150503090a1b0e150406090603080d02130f0608010305 79
    0xd445825140a840c0c0d403607228a0090742c12124448000700c0c4038040341020a0851041e03058410b070501030b8400d5001d007100e0000c0204848482a0381e0034201d0398890b00101c0c2142e856500555020120040c08005032411146404d02400074258038446c03514410700080441301c81c1c0c1d21941d486a02c80c1060b178030410003030000001c0c240554015007146404c0780c1c0e80d00d0f1101014081c0781e201c3c65010a0b800c80e0000f021081d1406485400c2c000c650340d503140c181c050001e050612402c030006a42c98409003405c080c81e0041c3c604e2403009800400e456042c01c3c54042041d9850f1010010580c0c2c40191200c5c0f034520703006d500302982c000d1002d156107034200300c009071f08000c2c040400e5090120800902421030350000d450f2020940000c030900009020340468a00c00304254050b000c010103402c1400090390001107010f005c9107040300c040044507504d060f0f45c400e87d0060702c0003801415080c48007107502c103c545c000780501108c0c00400d2550949850503262885003a4100c0d8000401890040c0b04001e420880c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 760629010 1250 760627760 760627771
    0x60d1d0f0712050604020d23010f0605040207120c080d090b010e090d0801030f08040312030f0e0c0a0506070213020703050a08010812030406021e04092307091215051e 73
    0xc1c0b040248242d211550755000141000740a1041a8400024820100c8480c6154441c0039003602801804c1c44010b806080700b4040488003d00c0c00c540090240703403500c2103c2c0e01da80d1121a40c43c006080800c1a188151101c0007a50110350403c4521a108042d10803007040034807072b0100310f0265040211800300c1a4000304111210b60001c1c0e807941d10f02c1d81240d001c43c1100c1c0d1107602e24150207014035011645008583c802402400940c0d070403071103a505a003000c003002030000801c000348285c10600d0741c3d0720050500040d4000b1b103440070501c00390401100411031940050f04005013041d030301301920100da00c0041e0590005201040c0c0d603941d294010340c03182c01014480002d11049049021689892201920080c01d2907800141148890708094001c001004e600c8400c580780c65032128000054802112400b8038498048040380460204280303ca000700210399500850a082c2001d074005250301043c20303125420b4490f04025003c1c2c0c24058240319000141424403074a085602112000f03501400 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 760630260 1250 760629010 760629029
    0x61a040f021c2714100603111009091802030f1e03030c0412050a0b0403051e03090304060c0c080a0309030c05090f040201050927040308070c0f02060d1d0f07 69
    0x1c65000c0000780b52500d24495404580c09030410300c0c0030404c00c1c4a841000c4081d018014111801440d10380c4001c1c00c690203102d04a202d00d804c0c104000c000d07260800d81c10046105420148003143c0c49510080488080d0106180700c681c0d107170002441d0008550b1803800640c898210340380c84211081b04000055001c00045045040440340f0345040c1c040c0e800b0305202201820590300a001003041698406500b145075a1468109420018420383c4505204c0c1503404044400240b0365001c0c00031203100b400150051030034182460030440d5a035465003001d80d5100c0c0b40034001328520100f0700020004a01c039489001c40245140f600384000b010f0b40c0d0180b841042c407182048000e4118242c55a4050760900e8015038813640c1d0f1000a200f540f015a40020300700404070000b007460366001d0031034011802034540380741c195200001180d91040f030081c0203000521046005006061100c00303401414051540440c24803000c100080d41c403480c0304014081e642c021050702d10b05c0c0c0b505004c081d0152544a9 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 760631510 1250 760630260 760630271
    0x140310141f0b0a0c03050d0e06090607090e011e1a0d060b0a0203030f1801180b060406031e080421060e0105011a0c12030907030506160804061a040f021c 67
    0x480010031802403e60000520040303100180406200f4802c480545107006020040510551323200da40d20001168950420302c07650011980c018000d200760001c0f17402101c254910f0f42e090200700041d450070400391240e030004000b03020540f0340000d006042d56041c140c500302e03103605c1044590b1040d10305562084036000010802074810540c0402107136070000c0b03580910f02c0c064640100c03110503142000141d20203946402540c100700c0d07116142d4000c287c0e0164041c0c1101f0f80300c130020402124460b220090211005802c130411a1540d200c3c41e03104d8501854546003002e079500740d44503030407078a044140c0307414903010840c60402410b0320075010f032124014000c210750b605004114400c40310000c00001411008140c03140041020084400d480700c06c4c100680d12810f0903216166603146a00044405005181c000341103512032020488503902e2603030340e420040d1160f84411000b403e2007884048002c9220907194403580700e501a4210110041000684d600d124445042a060520510802c01c50515 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 760632760 1250 760631510 760631519
    0xd140a030f09050105130e040507081207030305090c09070f0c02031207151e1509020a030213060f050322020307032103020711010311070605040804030311031201140310141f 76
    0x10704104180c4051407c003030391646a41c00d22603d004556881400742c0c2c42041039000e01240e03864081e20000d0b22a032000d002c0c548410340c6180e1901c07101d000d00c54000100704001440c0300e210340f041d4000007410341061107240d400341d00802d045c41841200c414841e907000408000700032000d040035400703440c1070100700300d01c004044252900342007444e200100107403119500401d40743c0e05800b0304014100e14108640c3c42807001006000b9420000700d103082101c40c00e5002654500502c0300b804c4510301699910724555550181d030403c54a4510584ac608a41001480050300c04010003400f545c020556180f02c0002100d030280c2401074494403104150060200300009151f03070403650000d140034240465603c0800307085050b540900400603009a0400e0184030921858034010429203002e540c1e021010a282c00c0c0a56032440340003550340444003400700401c41c0c109440182601484010150790214070a800780390203035103507504080800c0c1364610074048141c000c00c1c0c0d104d490b101030045003820f442c40c1 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 760634010 1250 760632760 760632787
    0x20f0102030702010f0e060d0509060601030c0f0206011a04030803090a060c020a0803182802130b09131502130e1f1a190c05010b0402090d020d140a030f09050105 71
    0x40c42c2480280001b500348006642c2d40c0c2c0050f509038108815003008180b40c101c1c1d103ea80c0c0c20098882c203000c00c1c9420b0039a081300c0c1c0700b11641207144034150002c207816441c0820111360a078110840d0680d40c1c2d4180300c0440007460040065005981d184014400d40d251741c10540220f030740c18842d010940d0303c60785407440016524020b81c0e42c44540082c5074260071803241d0170b80e814020381c603032005503916161102440b00c20084120185860007598102c03d10070014100c0d600f2202403042c2a944180084005958041d484903105401c0c1d216030001c8032110561007600c070030703038004a031601304054420030240411780b502041035078450a0b04201c5140b0591000084081d0350b02030007200001d920f1071447d41010344840041b0340341301a00800c0d88074185803490005103002c61601084543d942400c40105640c5040e00036190894001042850300903030035070070000c040b649440c003150320081e404000c003007601c0b0034012410780354000c0c1c40300003000304200002080e4400c0c80c1c00040c18018140001e4030041c12 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 760635260 1250 760634010 760634027
    0x6030903030601080a23090106080d0c15060e01121a014a15090f07030c080405030a05070201210b0a0e040510051306051005030c040204080d080712060b07020f010203070201 76
    0x682c854101c40986510a1b802d001d00321540081d030079403007a200c43d22f1019500060919406024001201c215040e1007000003c0c0c801600c074803601d00714420014031902240700640500d540c40f800f030880352640b180c1c8d05046c101e88242e1015080b818100021200f41824200032007990010240a41060340084244020804017101d0b000c01040c0c0c1030001000d4040110107103c54031802032400c009443c00054200080104407200c2001a050420442207140542c00d03031401140d101001d0b60030840030030301c00c880d190040e4804de0b0400601c6881658944604c400c1c11b01e84c0d0300340b0320010683c907007600c0c00d004003440c15174864003a984c51001000003056001c5405010340c042c10002203110744604000b07241003075072404080d00b26882c1c017052158141690806100b00c43c1c0035001d030b403a81038882040108a0090b880b400c04550810380c10a5001445000480c1d4004054102440c4400c0030b8180b10040300c6490700301c0c080c8104009620303829850441c0e82c0c03104401e0309100075442c00c5d000b0380c0020710218 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 760636510 1250 760635260 760635311
    0x303010e0903070b04110a0509090a061e020c01140121120309020402030702010506040608120d150305150601181436060907030207030f050c03040506030903030601080a 74
    0x21609010940c07800040c800c40f03002c69000f02082c030403030803e402c000800e002c2241030030307104200b00000003403e411301520403882040d191004e0080c454180d115000174111404d41b5203c0b00e5203204011080141a10249c1421100b0300700005d04c00c00ea103407002d41c2900040e0401d07810701101410101300f184404901d929450f0b400292022808501e1405030060316500c3c1c0020f600900120070800c0d001d5056105a02c6071030200d40c184405940c40352490b0301d03a1001c40000c41c1480c03040200c0c00d45c282058100c504111160001d940000b9035030780b1110708011b964401e01481c02104002c0c4031b895a4485003440e1240d0048110800c6c01d40713007012404100c02e80d4810355005025250101c1034a2002040480d425400155503500e26010703028085480c5408a54161280b1080e070042482c1c50710034402e8802c4564540c4a0405641c5130500903079050b004104d4180851000708000328494480c44007550103001480011501da00f00000090f100318001413101d41b009280c4003201a240c1d005200d100c0080 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 760637760 1250 760636510 760636529
    0x3030a0905011407110d0e0d030503130c0b0a03060b0f0d09060605061b07120c0614041a04082406040213090e0705030f0316110402130f0501030e0f030301 68
    0x140c0c05180c0203000d82622001c0c0c1149207400b100708a40f25070841500070600d40032400741c80a4200c03914080d1183c404054040d030300482524a820002406030005540140a01c494088000800e5981600801103070b004002804400728420b509150140030300310217042e114080718140381c8560000800c9001305c0800131201c81d101d07100407013440702c1c5030711000203084046c01c82c03039807480c40d4017081c2441c240c8501034500c188100240002c05541030070340c0b02d405603400042c106500d031411008544030b60700104030f4550341078100800030b86001c0740c404a180503000c0d501a991250718042d401400d04907001d6201c4d409461079050044840c0b154104076a02c0001250016100c44051400101807901600030b040707614a08074000051200008041c8201c45080302201e040141d1210016124010103921000440c8201c201100091102000c06084d40d03000d040141032a105184191554000c2da2061401c80d181a0050010f543d160180e60243e100000c0104518030400b03a030690f03240b00502c10365408 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 760639010 1250 760637760 760637771
    0x1081008060406050a1b020309010f0c172503081006021c050c10020c010203010302240906090f0d0b011502011a0f0111030a031a090123010504053c0303030a 69
    0xf1049942c400d0343c0b06c1c000700319184042180c02078065501e90040e0881382c041165003900030340c401d1040309690005a442800401c6000c0306a103102d1103a0401d091003a240c03800909001c51100340e1303600101040740a41d03150040e904010300f58200128040d0000000c54002d40c22850101404120128500f5161301e03060743d440200110311420a1035119030301c4107071400010b413400f8000b030540156040e80e008440110034215007000c1c12900400500051070701090601c5200e00a1a202e405446206005021062807a0300307030000a00c0c81101c4501201c031b0b1400880140a032039503003107651281c400380e40000c0044c1140004078500d030842c4e40480034850042031100605036482000651215020304044a80765041c210b00a4003070042002c1c2c66203a4845080c1e40300d03051502840e0107049441b0560310384440c00d210031008260702c440d482860b0601c4400c000004d51078803942c2c0a0b4180c41240c101c8030142d1140f031090881090000e034084210060b080b030345880e050b6008021250010700d00c0100007003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 760640260 1250 760639010 760639021
    0x236060f09070f020c0604120b090a050703060f06030602040308030403030c02010b010e040b15040834050d1b1d1f05010c0f05010609020301140d230f0a0503090108100806040605 78
    0x10300381117650540c0d0404000710b40095a1000d0350744481041e4410302d922892036499220740740e507a0311103004c064010350112908001044003640702d641d00407081d50700401c8441d01c0391100e4046c0d0307126501c111544203002040000f41645440394001c072200510003400740d6140071000800656030451290b01c140c0c0c5d541e070b4200c5196151000c0115460f0b010203499142da95030807455458030018969414903840c981000d09044031604045c80c40744144800500341e80b0704007810701c42c4600c0610421941442529007a5180041c0700c48008002c00200319183e81888800803002d2a14801400d8684005451007040513203901100c45142502c400703107080d01e04003e50b41403584ca140b4104070040d020794a40640030500000c0340d002981a03d0303640c0500040d8044080c244048141d031564080c0c80b4011400d1103540910188030407140304d00603070040350030100c0782c2c0f1207031424061496804c03900d542c8002541445542c00a0070a9440303d120214009554602182261201d100410092003245e603040040c5 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 760641510 1250 760640260 760640263
    0x80606090103090f05010912050f0d0203070e1e0f01030204080d0c02032404120f08061c021504060806030303010305100507110a0b010303020105010b160f0236060f09070f02 76
    0x100e40f940c1180303961203001e02c40d04106000307140110302a07a44441c40260504540d0203441114000c04107480540e16144250386480002d400140c440010080c2070503000c4120b40e10703c40303801910051940380d000545041c2d001c0004803000e40014606050040c4410000304102042410000e003050030101d1881c4254800039003080c0e40300c00c00c1d01d00e107074010b44101050418039807194031a5105540c0880008000c03901500c0100719200740d0320008030300000280150030140c240c1c0310700141005070340d46500007a40c001403065584121460a4080204080051070703070000b28160045002d4010303518550564490f035445e03400d01000d02900503150307400301e01c00038450688000480315038020796070001281d10b49039031180b90070300c030542c01036003400700204841081c0000c49140041040310010740864550f52103c103e13503200030a030392000c450664045800e2400402c8110702d44821040c40e4080310212202c80c0000c030240c00c05010b046038032549400c0d6290120626001181803e1140b0000f001c410100d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 760642760 1250 760641510 760641521
    0x4030605070c0b0a0905100b090a0b1f1101050105010e010c08161203020702191203120204090c0915050304080a0e030f030a0e04140c040611010b0d210206010303080606090103 77
    0x800f1010031404210701e401481d07000c41c0200c1d01c114152411a01141d000354250b40c5642c07003280e0f110300c50034085800e0541e640d000110400c00a05052440c031001140861210b03004456800403030380070f030100c140d840000c1c810a0301402e000d0a143c180d0600c0310780028500140700300028080407001800c1c0009000e041141c22910b580301c08904020400d06100030041c0d040514101d0003441610850b89254003040300a0040d60f84a01b0794104488490b2030440e0700c00034224111110b90740c01c00c408180004540500d24040b6195203801040529098072800c024203198100400c012003401800000f0340c6030411560640c28038500602e0003a401d00009092004004010103244000200043c50582119008040340822903081015908484a00006040c02c0b51000010035003007009010351409840c1c0201c0c051401400003815000c50300215821544007a0700340c032010003020204907000c81402c09604101c1c40c52000d00041e5165640142c0011070113018188034140120301040241d101c0e5020 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 760644010 1250 760642760 760642763
    0x1111207241e0f063206071b080a12140c101d0a02060922050108070f08030c0c01110f01180209060a120b0720010609150303020304030605070c 63
    0x1000780c03000000d034440e0b072846110045201582400081e0024012521071981142d48500c42032142d8106400c1c0e80d0164820700c0032000301c0e88810017007000c43d51a440003030501c091050343c0c2245004599414007800104039400198640d00c0000007000045d03420281caa00710002d81400c45180c4000702028001d800b030b600e01c003042840340400764103449003150041580854509031080004191a403c1903d0b0300d1304080280d0080d004000d0a000f0b4104520090510f203d000c48c041141c60f09424218160b540aa00651450340190720510100612810400041070990000c0d840c0c03c20000c0030030380b1040c44652060600080c042d02043c03042e4140880d00c207818220008202807080f80d60006203064982100384c0c0580c2840c40050f01c031342080c80c07561080e80e52904403000d04081541d59444040c20081c038580800c2140c802c044404c0a000c01030030b0782d4440309400440c84038200004d010441e8007040001030000034440003040442d4000c403c880c142e07500710201003100d40c0c0381a0103580d4460302d442c0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 760645260 1250 760644010 760644083
    0xe010905061c05070509010215070c1403030403020d0c0321060b04060908010e0c09040b0606071a0402041b12230702031806030709120302010e10090201111207 70
    0x1840c0c070b103040800c5440e034114551800200a280c41d554800c40300b90040030f460a000d84d01020301252101030440c409540034505141080000400740c1d030740d80001c1d020030b4140c1116880072003071004250b018005d00c00a2540c5161a00c04041680c400803d500f680fa0407000010500e0001011800c280d0f41004000c2c5c0348110300076a60710baa801008100c141e5a108100c00d6500c0c050b042c4440d60404035114440075401051140c0c99243c54554048031000070305402e510174420496400081c0c00000c01e00020030607104400154980760050000342c0791104c20345a236270001c50090000e640d4012a03204904241d205001400ca103195000230400101020010560b048400401401650020040c00030713441d20450f411141002c0000c0c8810703030005075040c038080342001e5410311441000c1d03011442468024400810174a480300d405508200540911212082e1662030b24429543c2005140e4401039085008007449100310382c00c240a40140f140c02040003e00008c002d0380142240101c0414014000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 760646510 1250 760645260 760645267
    0x919060c1b0602060f0c090904030c02010e0a150c0501150b0306120c0d080d090f061d0a020607031b05060c0d1415060a03060f09150b13060e01090506 66
    0x44014115509048040340e00c0c0c0c0d0503005211148081c00c50751800c44005400520241e03c13200e40c4007a400e00d004100601246080c080e1032001e40d0756200d13080c00b41e402a11201d5084015000041880d01a0940d050007507612980810281c081c2c02000507503003c0e20700e0061080207081c641a40034000e246103a41740504080f80105900004000a40c0556801c41d42c815424008000315510b4030a01c1d00c00d59404407461150401240c081d4000300112140420300042e900c40581d07401c0701c00040740005841d201d98850b00101d01c0350b0004448015611807400a00500c0b135a0f5002030340501c19210000c0801100b0036401001d14100b0600c5405184d1001c1540c0041c90b04c06003111658100b0444009010304240712200982c02e62140b4500548610081080940014061041341d03404149403004140d40c42400041620321140c01e04043d103c403050104040134070182c403214212803078210099200e420014034180002e881000c2c8120b5a45081c1142940301e5113005a130b072130105520844d00100d000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 760647760 1250 760646510 760646519
    0x1812030b1207090c11060114130507122d0f0908040617010501030c0e011416080705010f020f0706050604020d0509030702040c09080a030516170309060c0f0403080919 73
    0xb0031031000f902e403407403420004044003200071910503480009070b8105400030070040c8406030720761814400200d4060150300070801c01c9024103013182d004a4075600051b107440028210302d455401420f0f03220122480f4000a00089a007900c1e142c1d0301ca103105008955100740040d950300140c1c00c150015034208035102d4132507039101c0d0007802d107242c1804200d032604100300000c1150b6011f07100341c1f039441d00c0c1641c40c6050b1500380030041d50030350021050300f445544140480200702504411041100340b02c3c503c450386860320340c0b0b0700d05d00b503403203007407401041900600001d10405000001d440720b00b6006200070905460788004180244a1440c0541d01d541c2440100202040c0c00001040344910070380d804c00c083e0712040400c841d012070a00848285402034088040841c1c81070014100b0f0010712611584628080d5480040000019802822240d000302c1003103c40c04090001ca54800c0341e3345030840c42d20080068041041c460b5000007880350002054151540e1a400700705008840d64909420310b0940360f = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 760649010 1250 760647760 760647763
    0x50708030a05121003080f0721050a030f0203061c03030209090403030b10030e060a02071704060c0302121e0d0b0d06020d111c09020d15020a0f031812030b12 69
    0x1101996107100083d101141001c1e0684510034100d90b040340030a0b0030550240950646580403500541b85403001c1c4200c103000e00c038400040800c0d04881e0b1038095545c4100791000c5c0a454020925495240c41441007104c5511032614001c0410482405490131101c145825402800340c1160150814102c03002c1108154040d4810700c1001c10848108184040d55402207098030780045d07224000c0c2c0c1102000c1050340055402520110303205843d1101d001e0880300848600d50030640c03003007002580d201d003400c040c145c0612240003901050007095290418458100150034041d504080d4410303030024100380800d1003a4400c60140800802100500c1280d01300000039401c4620b4000d911480c0c60003c8010101c004100c079403908450000e01414020210500020801c0b1801039803c01060f52000c000580c2180760407880c548416401030312110b184c00d000704200310f900991424140342101b20400551000c084c050000d078031000c0006850b511100c21000790070f401c040150003500d4041100d590400 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 760650260 1250 760649010 760649017
    0xf1e0602120601091203090311030304031401140106021204062610060f21050a06150809010c090503032d071118130323030421090b090d050708030a05 66
    0x3099032013244458840c0f0b103600000c040528010007194001d03600300000b9102207401d40742810001d003a20704069503a11107a44001202c9400e20584e5503c2a00c407000e41c00032450355014000500c0200420480b140708240c09209030700031001400a000700300004e4280003603181076810124500e8998508280d800341c0d05074082d070b01440d00070803c0c000ca6030803818407603200d010072840e2000d20850541225042c5a00401e4054880080386461350804103440d00060485050315025503148000341c0340c00c0e00207500310b0703800f500c5402c02c000303440c0c1c410401507500106903030300301120048005455010182c55035986a540040c0a1030300c4011030a141446911074264071000d1003500c0344141c50030b041ca00215203400c01c4400740902038625013000302183c403c0c4c100042c610341031a141f1145103d8945025402d0f041220101c4580282d00d500b040c030030b0340e0450542d500342ca007402e150821034141581c4946c1c0c1e0040600c11030040c0030440c605014031204220070070040101605480e82d0350881840100550b1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 760651510 1250 760650260 760650271
    0x40f06020a0b0106031109130609021201080c0105030f061908190611030621010b09010f03060c020c01021015030215030f101202040b0f10050903190f1e060212 70
    0x1c80d05400010040d0081c000d101200880e4400d0b07510782002c0d0010048c2c140e00c5002e40710641c40d564040400d50025034801040e105508800021403580761804061400c04981d89007410008240140f0020711441c9243c0303500041c0407074885418456800342c10070708540540c06120301d0b1140042180c1d044040001e6520014024141400700015210000c003003071200741c411641112210200c3d070704600310010414481a180d0300081110900c6200080c4600b41c280c2203201015600c0000f0800c00ca110b1080343c101c010a030015124030581040041d44805000c4162401c80d900d496104400980080c002000396034001c0140c1c4010400e499900b461b42c0003203640191302c0001710041003041000c800044120303200d0500c60700140c1c43c031381c3c01e00000e0410780400c84c2e0407140c44210b04c451540c0380410003a0a006541e07506840340842c40805181184c034424100e14543d0f09510400801e4861300c01d1401c058120070501811410070345108420260104094030711480403070702d80001d0208200c4203000300c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 760652760 1250 760651510 760651523
    0x90c0d09240e06010302060f040f090b040c0806010816020705040912031805101a12060a06050d0503030609151c1a0106080604050402190b1309140c0906040f06020a 72
    0x188107a914801201c00303140004680c0d90000d00100010310f0b08400410022a060001c142000d5481100181c420740d0740d000001c034151500385089890030302c3d104608908105203000c07092403c001d000a802202d000d41065064100a440c62a480340204420402403001030410407040d0140d040204d600000c640346800041e0400c2c1e400d000701d11041c62014102c0ea00310000d4130f10406050300700340003040341400d02086c8044107140085a0394401104030344d50700c00d8034054051460711b05620401c4440d03030b07000707a0312425010603040040b4074008180da40c0200c06858201e503d4032000c00c0f03101c51403010300000d94868040c50490038085000d62500b5000340c0b246090090540d000d80d03c140d031100f024006c3d000040d082030000390b56031800750000303034119002801c00d992017070840e4801e0080c02c0d26500a032522510004055580c01c0c601d40401001380080c002c10000f250f80c032014190b40d83d5020701070506100300440c1208840d41c031201120700429400c01014481d60b56584041c2d07d07540318800a4480c0d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 760654010 1250 760652760 760652813
    0x21c060801110306010f0509010e0a0e0405060c0f18060904020c0304090c051c0c0c0c0b09011d180a060506072d02030c060c15151c0c05090c0d09 64
    0x180d400040c2544d000d0705050712070500c480084c08080359103410000c0741904000445100800c01c0d01d0300003101015041d000c841240500c3c0c01d0414900c1c0081c050300c2500c45040800000d94855284c1b030940c1c03000e071071104414481c500a8030009240b806404141503110b813000400b644844000030041085604501c401d11211010f014240c03118090b60034411032200b4900300000032442c1d5070f4400101c804060800c980c80c80e9640d141d0440050440c1c0200100e1711000560840a603004207030380102d1081c2140b40c01e0515483c601180300e00c2440084c403142c1880b10004155004001d8011a002c0c14000d0130707140c0c840034903041003100c1c0c0e82e1740c40c9450180b0080c1c4003640050400101640c02e11030f0060002c0404014001c01d1003401d50000d00d0760003940c0039000c2c0ca40005807800103641d0040c03080700007450244103d0000c2101d000780311980191400110240c8000103040703003480f0011628210b900300300740d40d01e04080c0c800a00c1104500307480c040c6410450790810002030351403a14020b00ca08a00381f03 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 760655260 1250 760654010 760654031
    0x304090e1f0213090f021b011505030307260f070c090b0418150b0306010305072d06030f06030803090d03051303080a0b06070b0c030603162403021c060801 68
    0x40340302d0600c040020f83c243d00c009000e03c0c1e9035900545451400d0050051805205a05030407842401140d0441d1594441003c1100030740b00b04501c0c03000d0801140510700c0d24010381c1d554502902290301c1c0812448255440400114564090700c0c1c02c1042030104e1a0744181d10b01d0107520340c140c60f010340c00e1040c2c0740080319480e80c10540b150443c0e0b440c000315800c03100700094946829448034010202d04190f180c42c500d0f00203841c1032248600075032003000202071650502245000c0a500c421111075001081641d1342c6400e54442488811241d450800003842c20311801e2442c05010136402c054044030000003809100d0100041589000c80b02e03903002c02158031450f08a80340a0301d030b00c03c0540080c942c04089100106241d00401c08204010800351904010b907451414401c02114003200c00800801040306505051080e005603110b2802c2ca412820f081100d0308210b40104c6115035007101640500c00e4619020b80d044404083c409445003410703c0754105c00c440503007024040c00000e9400d2905040 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 760656510 1250 760655260 760655323
    0x602070309060c0510051017210a0f0e0a0b120f0702030a0f1d0405070c14030306011e181403070815010e0406230405060708010506030610020304090e 66
    0x10324140d001025040910b42c40883e20080c0002034030000460340707941d000085182e110007030366109200342805004032098124405a040c02c500275820144c81c404c1110100244c1d000780f900030080f03101c0c10068181c80302c080c0403500c0700016810601d0a07041c000b40b14044c44e0780c968800741c400e012100b00036140759510502241c0300c0c000c40d0221804101d030201c00750f81142c090b500e00981c6070640b00c0c02810340d070603060028091700c4095074000c4c04034a201444d0800d01a0071202500c0e6000100015031950403d100009c00c206090348010541440309500c1440e40c1d031041001a00324030408100d0728106495151442c14000e54042052080c4110b80c0b000800e401c0c0490319030f250503241c40f40300c100e507840c060b40c15020750001401242e002e07903100000590424101d4503000d900051580010322407625207026403810310701400030303814403200900400c001c3d5100000c136039008030140c0d104504007056690980c0703503000340d41141410301d0500190150082c0c0c0003401c602c00e9002c51030f0f030600b14040f04a011 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 760657760 1250 760656510 760656527
    0x5061315090b0d021b1204030515040f020f0d0c060201060617010f12050a050d05070204110c250e010b121b07060209060d020711041506080a0b0307080a060207030906 73
    0x256000c00c180f03c070590b52141139010700010340705102c0494100002c840c01d00c1c144003045003208032042c0c0104040c0f0600900708000031b128144440041c00310b0405450305018084c0280e8024403941e40c1648596880c0c8075800c00324000f80d401034180c120700d619001d004c0e020704446c1c0200d0300050230809811800700480a4154120340c7c840e8203400704d0303a050800c88404c400d0b014400f03588611034020b40d040060300412034031038129010b80c0c40985400107407041000341c031700ea405824500700b03040c0320010b60680c1c04641005800041e1214a0a031511a215121606400d50284d100b0311010350002440c080e1003401009500745c00003418243c0e54a0f0884190f041000d030301040c00c41681400110000340c0c603680204400ac40c02000341c3e0034004181c014100340e80c403001003250301d041090403020103410180981c86031040000e00340c030039160414000a1012400902c02c0004a8955000300050344003400300d200900b0f62441a900403070b40900305440031b54400101100010144080020070501c40c2020 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 760659010 1250 760657760 760657769
    0xb03150609090a0b0a0c03060f0303020c280e0405010506010216290a0c2f0108040828020c010314040305071403030a060306060e040c17070506131509 66
    0x12000035211801408424400101240b1652040455003000320310f550f0b507200d128559010000c121b036800d551700141a40c0307065103c03d0050340008801d00000380c003c601c2d044005010365699081445280882583c600030400b100c04048080d580802c1c00644032036814895400f50009210503240d0400481e60740700c0640c0da1280411300d0017018880e0342d031101422022100304550103c0c80020394690703a525544007080d000e010500e06800c03402002100818007146802068026104040400f4103582c0e0b900c01d0b44030039040040c4500090100807401007070b90125422802c0801010b01014245203412152a0304235015124012954040e50310038059031380390403c0421548940d0f1941d40d020f49d40c070307042500100c0b0b8103032451140c4500135a00f000a036110301c514a03404070b2001c1c51402c2ca0000c84403950442505807840307004002c049403641c00c0c8803048401c00c1040c22201da00300c02d119400c0c414180c011070303030049000461404403666030007030109840700b5000b40d0a034074010881c00e0b24042c215104 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 760660260 1250 760659010 760659043
    0x6090901060f0201020c010c08090c031b060d020d020307020105040b0f060f1219150e0102090a05060a0c050a030507020909010b010e10030b0607050105070e0102070b09060f0d1b02010b03 82
    0x14841e4922071005007905844034000581001c1080309a00d0030744149268441c0002d981c1d40820595080070002445102002d402400d07115600d2605c003030184959004180c0660340000d04861b0b000d8071541100d5080246860454890501841c000d002e844281c0d0281c030120440c00c081542c261180003d68054080104100b81c0840d041d0305201c201e076101804003085004102c844030704040702d128040c81d4980700348000407681800310b02884c210390030504088180d03072040c02030304025181c48510384240d0343d04803200c0d40c550980c0f64040f07070641a1210000c0403400f580c0b4500c001c06800074060300c003a500c00c5440004070f68440c89080e08032a6a101450300080b00d41c04460094280b0411242d0271348160314011558071040c10114509502c102030407106c1381c1d501d1003040070361a445030324918000002d00c0644186841c00306130164078060460517620846c0300044400000f01b184003160810418000184192040920344514007042041c412005d5400c00f4031090031441d003c5542c180d110340c03502 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 760661510 1250 760660260 760660279
    0x506160201081b07032102040f051207170307050721020103051918050f060708010b03150a030501020a0e01020712110d0b0c07051501030201080403081b0f090f0609 72
    0x4004507426000a4000310194005000a451240100f030041444034060744400c006000001e240c2031018410b402807035480c0744180814881d0042d17800800080320703422a075019144484882c0942040550391007228000e141581c4038213102804400b4011842c05241620b40356541c0d80a085e03002d1242c44d915413090200c100d0a0001980694459900443c50700201c24581f2541c00b4140200e80c2104665a01c000c2003102c580c040020400008003e1004072000e4001820072000160000c3c03418014444030310320100005103c0d0000004041e0f8030200100b1101080e9070300e0914078004d6208811040010710341e5405d2401c55400000e1110868403c1d6004920010310703521006044110f141c0c1595108030081e4100b00403c224031401c41c002e81c11003483c03560b10005441d240c0d1601038040d1600c1750042c440c000410150380c108100680c440e406040c045019134607a80881692030481e0215100304001080c131a04444030b00002c1c1070000d500f40e812090000304082000468003500c059217901000a0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 760662760 1250 760661510 760661513
    0x909110a0c03170702030d050109060b090108040f02030114040201080a0c0807030209040b0901240801030b06010e030c180a060b1303083417030601350406050702010501050616 77
    0xa2060740707405030191506a4500c030703d0351030000c0c1c011015100304005030b10108a45001424611425005150080d020042c2e00c5c90060b080d082030080c0c400c0c43e414480324000080500000001c00d80f14aa40280200203041c0c440b140c0ca00e110704260340c2640007802410014000804c58400c1d80f14040c001c0c1caa502132a83c0e82c0e10120043e520460341c0747e0f001a1074102180076901c0300c0e81c009010b00403150092aa0403140c1c40820941801c00c0003400c2004080707801000810503243d5a2038020302d003840c00356010148540480d21b4007903200e040701c0d001480d03122107200f03882c24a15064020002060288030180c2c2c0c03a10300701514000c841c01400e40c1389804c2c90800015100c4d030000c00104905d134800300c0d032009500d204100248030f01c00c0000c440c800b01042000030410186060980314000002281c250705100c00001c0811846211f002071350119402d400700144d9001c0e5082559003520001c001d420b02d441d10340800075003001c1d9214400b540c03d05e00041002d01d02031017500c0030b1900940d00300e843d51100d03 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 760664010 1250 760662760 760662767
    0x3230d050409141e0c0433140306010305060d051c0e0d0c0504381306120b0c160503041a031b180d030c0302060a0b0604180b03010c020d0909110a 64
    0xb4103c440309200070080041e225000074800b00700046110004040344070504242552081f80785110802c00c000071488081d22020103042e0b0707401c1442880c0008144d694040400c406040002000c0c145205d000c4007110003804141810a0040c003c0d07a0b901403c0301400140032201c500110300414906030f111052015092651102d03206180030340b40b100201a81080110941142c034005061181300070300720040c1303814484020315560810203010001d81d0301d0f00c02140c0120b001c2801c000c050b65a00c03404240000242d03019201a24020456400070300711919244c2d903258420700c04c2d00248983d1210b03203010b91181c0e03000d89114184841d01d032205081003500c00603407030b4054030100c80d11002c8080c1c1144652102a05108024403944450000a41d00d0402928116000308450445403c000414500da03d59000f80d07011100007241c3c03400c03410721301700c0d105010740102910650158a070244800710590700103903e009030126034a9620404d501c92400100f40d411010260090300070800c01400349511 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 760665260 1250 760664010 760664071
    0x60406031823071a04060c0203070305060117060a06030201140d0e100507030b10020705010e0301090b0a0204031e02100c0201020f0703060204140d050703230d05040914 74
    0x284550344202041a940d60561421141d440702000010042c2d5985010b070010015a00502071260040030203054508410060b4031990080404001c1d005500900b152070401108014552007002d4420b0756844e0700d18410f40380b664000a100c0c40c0714603008121194082e11446094070303010380d5208000040018219155400303403100c03003002aaa05010041341005225031140506401404038150601481c000d0645000b410000d1068109404960310281c000a0580071150203003048039141c00d03204c000a005001c460b01c080c100030504001c00405d42c070564000c1040d04d21810a1600f0079035510108080d038141c0110003900140e0425006003920702850300031440c02d00c144111000700308410314071400e1905c140c0c0211221a0003207030500c016003644000303800141060315914955100307515219581e44091002601c5940c4000c4a03200b0007542a084010420300711080f15655000b03c1c900810641c0075101c0d0f00307143c03031a0519011880040c07025a03409040700c40507038500700785a02d41009a000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 760666510 1250 760665260 760665281
    0x50709020f130602101a030c090a0609090510140f0c031008010f060e07050a0c120c020604060801080c060408030901141603020615030609100b0303070602030a0c030b060906040603 79
    0x300601c40b12564144609668024112940c0909200a00d8003c66001d03124071212803070f10300118150910440e100028030042c59141100c0030016501c039080d10400408058001d8400c060622680405000000440610840d103c2c0002c22030521402400d0328072a43c1030720510002c050030404640740b800c0810165070003524a2a40306e241d59900c603585421100e84060443c0081c1d1254000c20a0602160006601c0b0a990400c20301c1c01f00c1800c030007000403049080042c452904215070b00141d40c801c0000c410025406400e50395155141c840c0507003998006d1080d02e5481c86001207203c000d081040c207540c12650075000035820140042d00649010b94203489a840340c032001c3c84810410602100e6030f200341c900a80181c401814a444c4010180d0641e41007030340030760701035424400c91200001e0b06200000741594001109140007000a0862003030440161a081c004403d1040300a000d6106162142c0c540e181001b0452014081c40802d0003204c05041c1d120106010821005001c1e0b00410f0040 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 760667760 1250 760666510 760666537
    0x50313050709050114040c02030f0d02071a07021c031104030b0628050307090b0604051212070321090b0a0b040b10211427070602012705070902 63
    0x7203498151110071580264400708903403170a07510344000c074100303403003800b07001c000c0c80c40a54501a1200c003d14050b00c5844500380c00d140e4001038041c1480b070380b00032515224007024bc503000c040c20103500003507036101d05444460908100001743c2c61024007034440c1012107a00c8102e02800c1500d10348520784076500007400650003042d0680c29508044115541c1c02102d10452180b110b4241842d051601d0941140c10150029203819220121680c80a05171000c6032002c5490101000e04c2c0b08010781440d03800d83c522062440045081410117401504d102601c10490704840c0c0d9082c9500d8880e07007503814040002d4221207041c0c010600d1041150428211864080e0000c01e4170f91550b07000c6049208140c460800040c08184000b00038840c06024821035400c64000380072680403000d00c10008900030700030140c2c2c2d038001c0700d984440c5000040c16401210034041900c42441c0c1c0d8a001078082c100f541070388400304102c20b50070810101c10b9104038021a401500a044042c140355941c0300a51181c910990003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 760669010 1250 760667760 760667773
    0xc0a02010f09050d0909020f07080a02120d05060f062115030304150906080103120309141b210601050609031207060212060409030e09040c0f0608040c0f0605031305 72
    0x181d4240c051511224401c2c00240032031180c5402c020300b80c1649412007060540104486080ca2941e6400d65820365009601c0585e500400701050303141801406507010705c00300c046801405850a0341c071443c80303400e0a94107100405500c00c2001414400d5524000c40404120005031858541040f000d0703110300410b010514101d051000070740307150060b03880580d07800305c0004449100c030380c480d2440d0010b02c00c904042116505565881c080c180880180e903041564861002080c05003141c1c0324403580c1d0241043d02c1300c81e002030410318103072003104940d280100103942500e854401e20041814408480002500869080500b0012150300440616526102c0d500c030b0400320541d154020f0a01e40e2049000503a20041c0f40c080c11280756006282d1440360b803404c2c00081c0803d801254603526100f003110240d40700c0d41c551600c0791101c4000c0d007040c00d642904460206540c2c0d0011003890203180542541c1d400503a40b0b407814900c02d15a40500c1001880900c00b1a80c1c00360701001509460f8440d034203940b034 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 760670260 1250 760669010 760669031
    0xc17160806041104200310050303071e0c09020301091a010807050d0513080c060a0b04090b151201020408101b09030311071a03041a01060f180302041d060106170c0a0201 74
    0x10b000840342c5660000c50000083c402d491584c087d45100400d800e9001c1e50502080d03468a052001150000107524a0004183c030100200041480e01804d2401802c54880d61a0400d0b80000c100a0b510750905440f405000d85656006580f0144030380500e90b0b0709032403d40d1069032400640400703071079143c08480410003440020100e00142030341c020707100d0040055280c41068482034a00c00e503d50380c0901d20744006400460140104a030707200725501501030b01c50207081e02140d040c140754000803096501c04107011400700f0020810f6959020741c0030040c4000c140e160580d20080781c3d020107040101d440340710f0800009000d00c928030f15074544041681c90a0341c6d5120032204101d60f528208030716800020400c020001c0ba0080c0ca001e107075003102c3c5c500c1e0944c14001c002c2c110f02c0340c4136940400e0002402c1d01911300c00d1144d5441e000b840d4050814400040c2900184001d00b0341c0c104400d02a0040d440045120b5100715075507070f5480513640001c10161910521503a0603880329801c0f00455488070000103 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 760671510 1250 760670260 760670291
    0x70204090f060c022806020a1209030e10030e0a0b0903070605010f030b010605121803160b01030308091b060d0e160801050c09061909030c17160806041104 68
    0x200301c0d03002d400c0102c2e100a2034000207040580e4040100188040a1500d00c04c090101020840d0700d540328900590f00e440000301500c0c032910700920380740b40700d0a005000003015405503031512144010380d68201141804001607003a2014000941c0c6640e21004d4002c01081481d646990807114a00030b480c500f01c02c5032156020768200760402c24010f1003000b020030800c003200b500c4500401c103030714126040c80038604880c2c80c1050080d004c800d2500c40c0050703600494100b40200d402c00300502e400c080c2e11080900e85000c46240134030080d00418007107000682e100c0000706200c01c0c49144402c541000c0520702d410000c0c40e8010501c42000f069a0304500d95040c001000700391030048820742e28414692038100d42500f07640303000b4070400180b102400180f82c1d07511203606aa4031070800a403007992800c1481000c44840109900c06088515a2100003410002d0780c00e43c1c811445c00c030019102c1c1d0040c400381c1c1c2e54000019100da40d0855000d440054086018034080c0d8034420001803000c12100b51040305203 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 760672760 1250 760671510 760671533
    0x414041107020d1101080f1e07120603061e020a0203120423060a2901121113140906060f03060a050907050a0206090601030515070509060d060e06030703020a0b07020409 74
    0x8a0b10030354080400c40c103945e0411b07402607100a8031403001045150000044501001300c09510303c22480d104040341003a4010b441c0400c400315055420005981da03410100c02500405420032111503000c3d410f0101c0030080d0003200c0700c03a14103030021403402c0c055011892103c88002c2050b01c074804140000e00c140380c1064041c1c4d5400e4100070007001c0e1401c010f052003040740c8542006444440a0950340c00500050300c0d04c03500c102109003000e68500701c0881000307001c1c0c190303000508034141000400781848160010903106884084102c420403004c10030a00030301203000d4500682c4030381c007072080000c01031000004550018024144020840d40d0342e012803030081040d41c0c0303400442ca011035050070a550402c01c03140e102101070024980b5507d161151600e85030f40708002c11500c014040001e245a0042e011640000c40261840740c0d101c0e450705c1604000d08140c0100c007803403030300180407515501c3c0c006400302c19a030700207100d81016442e0004010300b0303622840341203030420348407511074004c01d02d4124034 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 760674010 1250 760672760 760672763
    0xf0a0602150a0917191d0609011701030b0403111f0902010c0b010308031b0f0f03040c0e191b08070f12110405180405031801032d0e030414041107020d 66
    0x459140e1080c5a540902025045c0b1180204442000443c0c20350a030480c10603818030090350801c0e521010040100e03182941b80500300315101c113020001040001c9607407041d100d6800ba5942c070821580012440d40c0f02d450001d001c1c290804101e41d1408425949d602c01401203205040c007007002c030115552040040002da0069a0540d008020040c050706000464040a0401c140c0e0303e14000040300411514018102f10072448100440000c0c20070042600c0703400076140321070721021a49004481d250840d02c403c0440c8180d40d040141d8041c101d85a10321282500031151a05030031581c4860b01141c64650380c103944010403050349030800c1000c41520550b429003030100381c500d641c6c42c144401c0c020031056040d00300b0851000c080030403011450210655446440071784e60210b8030700e040c0740102c1c040c0c00c10254001900c0340080d00b0030341c0920790195032175014038096810b01c118005000c1054583c00b80d442a1280070304000f40f15505480c107a0300c403070342114030b000e802403c000d900c0c3c01040201004910 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 760675260 1250 760674010 760674053
    0x4021c020d140610053307060b1903030206070c23030702040b0306010b03131704080c030f070f0306110c060c0406090e060609060307091703090f0a0602150a09 70
    0x28081e242e2101889400d62105080c00301802d06407809010510700d03070280440840880307004d80c51000c41c492458100101c100c240c2c400c0e507100c0c4820700384032000300300303184140b07109100d8821000d82e0000011510411a40c02d5005081c0e00c0d50b0303805044e10051440c090859814007225400c0d403012900c070100d400c8206400c002191903007024410300c422240e608102da8030944c469401040340703c600508503544040507c4414551144a2030203c84210032640e0703030031801c2008a00400c450500041c1c00414010490403913520f0140625180e4a440d4580904004032400c044240017154a98210030a442071100c4918a007017103502c000750500105984102041e4400a810421580d00c010000b0103081e0040301811641001000900d49205000040d8002c1c3d0012000074204ea00440481c0700a1901d0f4012102949035220a95120f6120000d03241c8280f502601c03185c014140145182d094a4154000b00300301000c50078484c0c41da940007840c040b515511801c10200254940d080c4601e2500c4080 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 760676510 1250 760675260 760675283
    0xe100309030908070305030a0f020703051f0f090b06010309050f060711100b0a1a130303230f093303010e0622020c03040f120506011d04021c020d 64
    0x207001818404039510121182d440b0f19014000701d8408021220b09807124107005000c5201c111040c0d080002e20381c4090202c4c05030044001c45880c0180d613404001d054444100990400101e10004951142002405041d501e10000c0c0d101e5001e640220803450040c822961b0342c01c0400c0081c0c1c64410101c030040002002c1c1011803c000340d04204010001c00702034010302c80040100081001f070354041c401c8220000805e000180442d50060840310180c03d800c3d8182c0c80c1c1c540b01e05010b00810280a0540420410b1803500d2016905420569401c5008080e00c07c0c81c001060042002d41e40304120500c040c550a88000c10020482650b88403511000c51391080d2a58542122058041c03402403203a802080d005401c00e408080b400c84481e01400e2030000143c0300e065123004c5520714016a0042012546100000300e0100e01140700325040741d10a8080300c1c52a0388802c54054088181c420a20100750510042401884c244c450403401011817240d000302180240c0000d0800b000d901030680c0c480c103407035 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 760677760 1250 760676510 760676513
    0x303010f1a04080a0206030a0e0607022a0102062410021c0306050306130c15030605030106050f091305100504080703030606050301380c101413030f0e100309 69
    0x5402407001480445034090400d40b034107862689a18000344001d204020001c00640c408902e50310819500c95002c0c11220340380340103000a541e0740f07490010000e1a151031014040030001070710114204c80b8060340a4004c80d00da081401d9030000582816070709190714040d010709651110a03d003901501d86500171300d40381d010840003002c12443d0a0b4441c0030181401c5090255450020700507411820342c1e459140111b030f16080c12400d00e034040d08124800c485c1c0000714001264560030030016244124002c0008580d80d103300b240c82801d480f40340740c016803500e00103415080480741c40c2d01401e00800c10340c0c144000e41a0000111281150110350040c0f012452006056062040c003016000342e003041855541812400c03019050414003481000340308000c000f0200290200b07011140e034a1880181d29800900b06054036112041500464140b9041d0b030852015400030000e4002c6466418800c140013050b10100ca013884266124001c0c0080c0c981d01000b152500c24030340c0580182a0782c001140040d5 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 760679010 1250 760677760 760677779
    0xf15030b011409150d05060712050f010608010614041508010e090609060c160b09060711010c0f05160f060b0a1d1501090b0403030518010219060f020702030303010f 72
    0x1038011420b002d0045500400d01d440e00440c0640100340c403a241111304003440c0c0001d6868260302d00046c03d600034030b001c1c803280c143c01400854100e2980300c0d05200c1c0d41d0321210f04514444003440342c0700004141a00421160340501050781101080615542c40c00340c85880310758a40b81441c014800040d0202d004100c1c0d07107103124000d600300c07200c41c0140950707052001d02a590b030000940002c04074440040d4003540042a90001c600c400d50005010151b0700d031900e00e594030b500e4100c0e00d80700400c40440a0f81032080040c8204c61000001c0e840380f2480414081e001c842580013015800d148200e0994144003188100214602d2103204038030114421018034103001d41055180e00021200c6219034013070100078080b14a4030b610101150103030382c1d95030700c103030040300d00340d101c0c0d170181344600ca0000d0040149603101c4010501911081001140c10f45e088004981c0c2d440704500c1a40d01200c9203184c032000400700e8000d07410920780f0380c501600303001454000134210340c002e034041e07542e030070b0551010092100c1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 760680260 1250 760679010 760679033
    0xa0b030109050c0f030f07170106050108040309060c1a13020a06020309091306140a02070b16020d03050a1b0215010b1614010213120302120f090d02040f1503 69
    0x41a0000c0c010705000e81d0300e0382da958507006200b61041102c41c070700d000151000c11451400c1c40c610b9081302d030710701e0703a8481e005450341001c01c3e0b5200701e50820b00e0205071540502c1d50b403401150700d99500e00c401c4d49002c80444540880301411a442040074100345d094040c0846c0300381c000c0007001211802e207400c51040114507516035000c141950000d2207501420750764213600d198025901050840c4a0481d803030801c00509400302008002c1c0c840c0418021005010f901411a40e8800d01c1c44540d140c46416000e85405403030522040142d1040c1c1d44090040d2081d00859042a65100045280101402a50061003118036030380010303030080140804a0700744000c5c0c0c074014451410f0640c0790800310800c6a201440000e000303008908801c442c41500c440940c1220469450b400c0814451519020a03203480d82031180140c00501c02d000b8024440c107081d0046034540135030403280c82c3c544038406040c01100e400544042c0d92141c0d0b586001001410b0340d0090501100386400d40051442c00c2d440e00c0401401d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 760681510 1250 760680260 760680281
    0x1e050a060e2d1b0d020f1206100305070f14011101060b0a020d03051602150405070906180f050f01050f06041701050105030709090c05060f07061b0f0320090114040e0a 73
    0x10b8207005083c0c0951140841d100c40c140e01031704d0041182e12188089403610340000e40402c5113104000400c07014042004c005011759100380159210749560304c0c4001802e000310b000d5603100d89404007000300250301890007600262040350010482d80d54418510701c0c40d40040280c04d000d41c006160300c00301c159140c4159507003d4094250f0307003500d0700301d400000c0d035a810759508114881085c4c000b060600808200d4800201071440007400519128202c440d20940c9080040407003608200201114109a015440c402c0c0708549045910340c0c0f80c28200a40402401c44068200604000200d40310008101d0700c02d00001000000c0b4140d45000180741c40d0288991020340003c0c5084060400540c900c6412800c403102101c0c0d150310758000811001062080007c010190342c0303012410140600d4030a545410009507444e500d00800c0301410030b5003590b0f007240c07440c88000312010401001803032620240515140614010326410414034070406591f1180e00300d0052200b4100070800d2564190081f000d101 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 760682760 1250 760681510 760681543
    0x140a14040812090304080316030306140f0f010e03030309030a0e10050717091801081015120807020901090e1009120e041b0306031e050a060e2d 63
    0x1803906848200040c01500701c0d01001c041c2110204820b54400c100342c8011b0240c0e40b050f03950b500e65103400110795003040705003240400d00f02000007440d4050414a0340d10004042d00c50743c0808a4042001110203200e942103040c0400f030304206080c1e0b203040000e035210b8450300c0015540c5400c03500f00905215561158648150240c020302d1140d0b0741c1c00000c4d034211030341c030124070300700e4101e54408408035004101030282c00c0080c4e128032a51524152018604942c0d514064074101c0c3c1d07680da00ca80541d242444d8103111342100807010485000740000d4200b603240940300160401d440c542c0001c020120a0707002c0500355482d4007189115843c240490460341c8240c14040003004210754034004150346d101000d81c01d0050300394201c50b40b0349803a000b900c0160140c0d41e100005600164020f001020030b8082601c8000d11441140c1d20005040460300560350800c000340410041a95000090f140000750440ca5004222a03c00e0002c0003042c0110405060744007103120f0342070640c085180050405603100e14 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 760684010 1250 760682760 760682801
    0x311060c07120c0f0f05011e020c070b070f022e0e09070c03090302030d200a0f02090411130209100201050601230f03090a02120105090d0e030c04140a 66
    0x2c0c54070060118646041e040c0b50510300c0940c181402800c0c12184090f04e403080c1544030808000041d03000f40d034490300c820203800343c0503000d8521904030302440b60020010392201006005403501840074001c0c1d14403034400003203240b003594045414460740c241c4030340c286545880c040007540769071001900c4031b00c5c070382c90006203035018100040d50644025000000f841140d02030103042c14800c845800c041e640143c00c40f00200d0641000820a000c0103002840b010f620440007a500200821880c106075006170502e000c424850f003c0144132603024004071400640700f02100c109071602850030030342d500740c0c810058850505009101c001c1c00907000c000c045924090030052142e03082844810842c20036404800d10b480b0602c8580c41c18407a20b211038460f424044100100b0120004400090314800d0324612442003800604600340c81003601d00540d03d400000920100324820110a00b800e14002c04a90b05200c1450200342241e9107414400f102018041c100f00c64200c4a020300182d00e01d4841e5032501 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 760685260 1250 760684010 760684013
    0x207080d030209090109020a27060f08010e070f110a05030409050a09150c030207140609070b040e01120f0b04151d070306090c0806090a02190506031f120311060c07 72
    0x1342c0605004032035000764041450714185208034201c0000021004900c44000310701c98029041142500c00d01c1300043d0380109821400e84900c0350f450480e407502c0e0010b03e141d2100d690903a450080c00c00f402003000b6040c0a111800c078005c0240600b518000c1c0003856560341054000403d88600030202001d490a02c0030150010707407100700b02140080d800500264076008003404802030303c03518a0103010341100c9148000944401308000e402400c0c3c02c402c4840050b5540c904120b140034070300c500605041e402d00104860b050700300c05a10700fa48039a8000c2d042c03110030b9903107000c808000d031019601c01c0c00c103604172440e0346414030441300544000e030070300c1c441120125a840d9447e00c250100600c419100d201050030004820740600c098030300101075039610302e80000d440fa901c10050702c080e445030784100b0f030075010034071710200e41e4080c6c98016022034690f5440d40e0f140c09071280c00c1d0901c250703245000540054140b000703d4200881d14031981c1c0340400881100c125a1801c10090529054440100304030320 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 760686510 1250 760685260 760685269
    0x3110604060527101121100e07170603070504020705010c0206010503030c07060518030d080a050c0403020d0816051b030f190f08090a090c0f020a0b06040e1c0207080d030209 76
    0x251649850001040b605417101c103500060180040040f042c11006100030b044c400056011481418000c03040034a640c0c0c0c030302c010240700c60f042d00c005010a0001c07501045503c240c01400e503100794081d0403604010356400c0820304030317030180600b680c1c40e941d11881d8aa80903410700c25940107000407002903044c0b13548443c03c0b44e140d008910421b01440700002d201c010050b039000e10081000d030000c0c20f40c0c0c02c0b00c0461b5406005c0740c100b103030299091407820000840d10300f400d8050318140ca4010380380c40ca480c84607642d032120a5200221161090703403c12541c00c0021030800454182c104007000c540c80196104040c14945008401c071701c60035030001307008007040c1c248842480c090a0f401c03174212031015a144c240b080d0780344600c00c6a142c11a00641010480c5026130300711080181c00f03942c9150314815428800c90b158003840000500d07901020002c10301350b20301034200e120021151010b65680300b00802128205001480030040560010482080b00d68014000408035000c20306040d49407910090015 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 760687760 1250 760686510 760686523
    0x70816090321030e070816090204030b220f05160518070f121103040c141e0303040504091103060f090604030f170406090c051c060903110604060527 65
    0x42500d000582c2c00c080824071a401940c070030380c80ca50564004a4480b0320790303034440c01030074000000002c4d07048001030500c3d807070701c221401c89800240741001c54454280712150116101e090400d07170005500000003098210b03041c0490035214100a2200070048840300c03416000660100340f08a20032003170b4520101c000c400c0c1540c0441e680c6440250209440d00682c2d103200c0307546003100b240349002040e41d800ca030448000c50281d070051240011499442c40c034841c91100325042e254100c02110a24140c0154a50b032000101d94010f0070b40707007402c2e290400b10b802c6880d440720039211800300c482d0020f164182400210b80221880c0004041c0d880c0c8820388540e6808041c000804002c8031040710301c0040d10620844801c03000721220b12107207081508103407000e08440401511144c0e10b80714005090316046a0707035100c50070400f800b0300008056840784802080019000d0703091004002840074542e0040c800d10b031260b071103424006140c1c10a030208021f180e04e04000e992854441c002002407018000450b07 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 760689010 1250 760687760 760687793
    0xe130b0f0144031b070801110f1812011517070509070806012606130b01090e0405030f0f1c0504020924030d030b030c1c0807030e06030708160903 64
    0x850200420030301c1d11461131144d00384100a100803641c50809081c00810134600b100c40e070f40c000740b003039007001d04603000c0034814480e030000300c0c00f010820005030341501071848500c020002e00c83e4040c040503201103400d45a0202a01040700144003090008010035a054082006214000d140e44c0d03007003101144a444000d400c6030140300385400040d00c01ea105803070001400d031030514690f840440e4a160368040f4141a40c41030300c21414200d140c0103c503518422804c05680503520705804528145404406039030240090f03402d03000410a00c4030f4504020000c01030408500105940c469483c0319005e0f1040281d203140c4501800d01c81400090f030b0f11802504d410549501c0016083c0003040320f121030646d0071880d643d4050203086405034801e901988007040d0034406a0035294070b054283c040001c0c13000101103441c400344094200c140851450300260180b68807901304603424021140014034580c00840c0d400380005c41c2002042111300740c030816244080140d05240a4180c15a0303070307001c8007400c0501d0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 760690260 1250 760689010 760689119
    0x106210b15210a120c11091b070507030c0f051306030c03110105120f06041d0a060b060f04121a04020907030e071d0106170c040e130b0f01 61
    0x4484a4050b00b80103046000f68013260a6680400249002e00f030110114002c0e2280302e008121040f003402c241e00c2c050700c124083c48112103840940c9900c1c3c1481e8000c800191210b20603984040001001c2201d40f0b409010000041c6410900d003008010b81108080c11a04210341465000c0000030070003e40c7c0025240e01408051107441140c0049805004540704010891340071820303c000c00584070750490254000780c5003030181e03150048080507056818141013416900c51860400892142e600c080b4201c10300402c0c0e140340c010560b18204058100317400030ba004124a40798a41040688241080340c1c1e5503440003910f8902e000d0f00094444a002817000081c141c0b180040709a034141030000b440039048813002041d0702c1c40b000f10443ea4038071007401100007017107010145114020310908810321800c2001007070f0745407508044030420000e002600e0400083c42c40705c080b10000d0308a4040f40c1c81050102c0d0100d48640c07400c0070481e888181c3c0e000c04100545041d800000d00c2c100b00101c40c4541c2d00716072 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 760691510 1250 760690260 760690309
    0x30f0603031c02090d0b04060b030d0f17090a142401060203030f2a1b0105060a03060f020d020c010c0806060a091208040b0304030c050706080124020106210b15 70
    0x24045003459000c04802010500306c0000c0104200555104200c1e40c04154215402050886001d0b2484241000c112001c51030071010094040220500c0c95030041c55035003a10003820450392001da23038540324408200250041c07403d40e0101009400030740d2145180041c50150355140c8480a0f40b01e02c40640f401c035004e14000c00140307078a1801920003001c004174002810305a0044c10080c1d800c2d1b00031284040901c58680d0510054020502616004110041003000440d280d555100c001b80340782035083d60110707001d00580008034501e102500c2c44e0131f603180010031400b01c0300000402101b401030115108000074000c000c803d6034090341c58400d80b207021400008450301c50030402050701507940070010b55000001040101a403004402d21113900c5042107a0140d5214041034506c0c42090080155a41d0b0b800354132030b40010340144d02801940700d8000007070119110642d405111300103030629070903507201200e1102000090707076000383d2080e41006c0d0a5020001c02000504080c03003d00c500d2007074009503 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 760692760 1250 760691510 760691527
    0x10060e0d050705031b0111070807060c11100e011206061d060c161809030e21060718050d112206030614072613050f0102030f0603031c02 60
    0x100000700162400600300c0380c0c5ca28801c0800704640d522500b001e40001c1400213079040c080ca000600100707413981e51f03000c2e103051810301c0000c540310006040d0544004a104203141903684030102031855030410740d59600d004855150001d060101c508004180061920108100701540700b6020381030b41030300b88545028518a10000b903014007d91040454500482902000170714003040c02c1400c03121981c510b950a02071004a0108880305024060041140e03081c55a6640c034004d2007004c1c60b003070704a0510003441481d4605c0380c5030407011608200480d4070180d143e95410800550300004107811920f0148005069031010300f0080ca0400c0c1ca4001e180d4818083d9446448010454560b03928a40400a0302e03a20700340391002c0c0c81c00d036403990081d42203200401d41e0305100c1d181600c0032003e01c0511104010620307549082e0010002c2c41d40074580d06100141c0000340c010312540902240220005da1a410084202100e01402510080c0700341c3c01044046807152508071003007100c0f0b441550040e144e13044c1 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 760694010 1250 760692760 760692763
    0x60e1201020c0a05010b060310030809041d0d0e12030409020d0225060b010f0509120304050d050c0f03030a080411010309150509060f130b1815040b10060e0d05 70
    0x181460a04550010035448080c8400082100d01c940c000d8000340300b49408a801c1c00450302c02581c03400c040580b003020038404211580c00804040401400000d8103a0326081e8600ca18507203800d1a03107075504806246407684d1b90049051501000407940003e0000401b40c106940384518403800d0324090b00402d600052a4141c5e051b202085000d0124460a0005100c003060380440d5210894030745141c0343d494945540700b83e20151050005454030f03460300b16590b08001c1c04010f600d02c96546440104004251030b102d040c40e940c0c07903900c00d600620001c080d003401c002151031074141160280d0b006000d40d402450b400342e40e82750003c0d009480c000304030450500480140072040350141081c243c500c5160107040507540311701d00c50f00711402540c5860701e981034004100042a81d000b10141c40e81c001c0341340410104c60801d9002540c204800144282c1c00c032605042c030341161143d03023103458107a00300300c03c0c0044141c1503a84440c045051407001c504100d07001e030910780e20724503150142440c0c0d100e21040090 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 760695260 1250 760694010 760694029
    0x7241103220c080f1608010b01080a15090f0b150306011b03021c170a0915020a020c0d050715050304020307060311070b160e0a0b1e1c02030403030b0316060e 69
    0x400f402c0e109003400072003095966601c2100003014a10090178000758400b03041c443c00324141c40582d522030342c07925211010401313040801003001d80b4610315100000c080b0660720500c840e81e41045404038011a01c0c10400410000020300750b004034104100700081681d100741402c1d60700d10048072070040d81c7d40c207080803440c1584440d165000e40104281079840c0304d402a400501d02080d00203103d1044d40c9103d4490103582c0a001300406820201ea0403003280e001c160060242c20401e403040714180c4880e03200041000c0800101990385030814a410300a29020b5400340e118000d040c1403503481c5081503404a6a40c56044c03041000300f540e0350030b015040c0f012040498900e580c00c4020000c0d05c1c00d0040c26282e84107000140480840c2c50750f03078549494100f8100102c100c0326a9007103a8103060702800344c5000c0d034402e4004821647c60400840254144401c841d0701c0c404002d00b80161289450b00d00030b0704940c10100420302c00e601c010480c0e5004030400c0b0381e040551302c2610300118000201c501055201c1c0307 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 760696510 1250 760695260 760695269
    0xe0315010317211503010e0703031413090906050c070807080708040b13080606030a0203060406021e0403062909060d050c0604080a020307120308070f020307241103220c 74
    0x200310803005240f42a100e42c200f130140780c1100301c44103014210401c150072101c4440500c07040d81c0003d1f0041001c00d006850341203440c1c2d80e42d42c010340342820351003000304108000d40104400c0c81e581e40c0071000340062481010380c000700e8440c04c680790101d40c3d01c58102a000700e00005110240002d050000c0100150a4400503c0b151103032503140c403103588042c8109020f03805440c00a100383c60000b040e03483d0004514007a2600600504800d442d184c40d0300001c1e511841d003440d0810300004d4408401d11280f4000c00045000d2980052102d00e8800310000e0010350080740c40000c6031200da0030400c3e9649055064009004803122960b415071440e10301c0c141103900300d00e80d90101c400708000580d0b407800b003003103200c19100701c007900d01c942d4450501c015805407441024000401c00000640c40500461b0004224242070049034100840d41e6984014452042542400c42401c001c041505013010b00890920f81440da41240c214501500044c640c0380343e2061100108103414075810510005100c201e0182 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 760697760 1250 760696510 760696537
    0x618150b1206101e0521010303050705160f150c0c080709060504020a0c1b0306020a120b0d171b0a0804150e0a030f051c030c0e0315010317 61
    0x16038103020302a000c14070440301c190180b1000d80303000e4512485032114000070600148000034140048004443e16000304015a40c20841a440c0140400d4001e0b40103008522950360660b540c20146000c900b00340c8007030420306035800c3d04401072050041101c414025103460204080020a24440031503500a51040141001a02c5034010941d42d00c003040034000c0c1ca41c3c0540034040c6943c0c42c0148400ca00c10141688001048480300800207050b0031903910509410044090140351282c48080032a0320034043e19001c2042200d107090701e8000d500a10b201311004580c1d80307003a1440c0d0740303070311344007000754081000000d00014990b550b82c0d2890300381e03c40b6018081e00f00c0f81300503010310b4140700542c440d00401e000380c441400c088070124800c5c0b04920400700c0107440440810710b036a0390920071800d40d580441d01c030f0158107210385007810030071400e00900109503400304520382e8504028003000d1186441c00e0094104d00d01844454852603070031411241d004d14100048003580a0503245030051a4540d03d02 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 760699010 1250 760697760 760697767
    0x90501020d09030306230f21030f030f070203030603070920040e040303060e09070e04030c060e0703021207081902041806090219080c0d0821010906090618150b 70
    0x83c55030580c45a015140d442d1586089a11070782e42d5074030328501c25640c0a45c0071005112110342030902103a80f0281001055014140d03240114074181980c0103c903442490307410100c10001d0f0a031200c0d0078980c200c2010300140d0f00d1401c040020070f403550030f82d00610b004142ca400f0b025001d030009050786003034081906034864899850b07100d13807200d982041d101600040e052960201c1d45070310f050320b05809003074104014014645020518214014018026001e0201040d030034030200790103004280300700360f1200142c00c00c24118810000540701540e07a512040c2c0c0102c030305000710000000c00162524a43c60110344882c0b6a200260103482e141c581c1d0481503140c014000c0c1081103d40010000364402c80b5040314804400b840040c0b03600031446060000d900c9440c070f501c25801d08200e01c02c40940103c044629040f01c448803420b1002e0902c2d0314805c5034000b44010040a895403050001400c50307100c041c071120345032852005000e040503000c0901281e44400090b0035450345890300c4003d000c0c0d072891030703203 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 760700260 1250 760699010 760699013
    0xd0c051e060901050a05060a0911130b0a2007051c050a03050c01050c090a030201031806061d130201172a0304030f3b090a0219030504020d06090501020d09 68
    0x881c0c2406a4506a1543c00d0401280c08200c0b907004140c0b041d00003802c00034400e450b16034114068070b505500b8078000700b0200082c1d901000c050040b81e02502e00c01106517525a14200c1c02013480703113544150b20440d01c007650188040c2c40c001c0b4442c0e0444404031050000c82c040742213001b5000c174107610014400e00c00c2802030400c064102001d880304042640c0200b0466031042d055281503c02e180c1140e03032004102e182440158025800020200f42010f200121081d10b6a11201102e100b41c00c440e05070181e13002d00b0750944000049696201a104412424443d030550018040062840c0da8244403010100041c00691001c4284107950344c0301001401075030020317588450a54015642640010b10792042d4100d40c6011b40c0c0c142c05400201c1c0c5d40701e1015503042000c8420050319000160a040403909401c0c041e66a0060103402004032500059640307185200c03030b42507040000c20060a243c105003c020150742e400c425585401e07001080419042d200c1c2c9000d900910540d00445069443e100ca13150 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 760701510 1250 760700260 760700263
    0x8060a0603170403150c020102070609141b0303030411030a080304030c0308070503160e270f2a030606040518010611010213051e09071706060c0d0c051e 67
    0x20032240a108010003256a00c10108501c1c8074a01015090007a4170050800d40c1c0c456500c00c0001ca101440014100307401951000142d0300c1c0c0f103109030b0300d1324951542a10902c2c0244541040c0041044040c03c6406c903010200b03840380401030020300000c0a64030600110744044c010f010b5161741c40700c915642e030b203003510b40901480290002980000c0441002a50403402070003143c2c0920030b200001c0e01040c0c000c003030481b051003007190542c1e00242c0230209000c2c900e03405a043c11810000b1490740d00203103000485004035000081007105407000070b01514419040325000c440c403502401c850b07250340340d880300080b913941e00c00e9500c07a03034122031841941e024100407254498113a1741c0580e50b5130b03921904584600c2c00c1c1e015480070762514140c030180420081c0341c2580408207900003c1148100b150308080080c804030f200302c03110804107400c91504c1001f0b40354121000c0d80400c0c11100141000110140c02c0e5585101c0f0007403006009a4542000034000104000c0c416400081020b000104822254a = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 760702760 1250 760701510 760701521
    0x330612140c0d05160b07020d14070b040611101404030c020a03140f0f2103100312020a05190c05090406090204020a0203090a0f050114030705120a09030f1805120708060a 74
    0x120751441004e0204640000c0c2c011034000700c0c0c000f4001504d01c442521911452091a065044036100b44500059a100c200001e80001c146035120b030740500c1c1e10202428140060155030001c0140790064400f4a000e00001ca075070030540601d000c008032046440400c83d840b030701e9000070307025075540c400c41d0516000003c2d502200c4000300d025100f056400784010355480d0a16100001e04a0384810344051444c1c1c0d00000d1743e07110307450610416001d0b83c0e940740e1f010f11021440c25040180c20a910100500c0340030000700c0d508100d01640f00040300c0b03441c0c51340005050203024480c426a450008503003405803e811102d03070716400500466903551003071b00180d603036441603103e58040c01c0d0300f2a000a544440701544400c40d072041c0c4485154007000041e600c01548000e101c1820b08c50700f4862084800700d50040c5622032070340400002040403450802812000d41442403000701720844540300080381415000d10102e0380d0940321156104034110040d4103150302c58114002a214260402c00d00031900c0d04078 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 760704010 1250 760702760 760702783
    0x3040503101a010c050709020a0314090703051c170402010e121e0a0804090c020313030b0f280b1513050940330612140c0d05 55
    0xb0710010040318001507602441c3c0050143c0f071900501d104001c64861b60300240204091860b00041c1c0040c11805184040700c1a1003422850303200f00418030800008000200c003c01000401c0c40c6146001c030b0009000b000d540e0815001c0b48913100114046902504029000384401404049004415002d03070750341e14081c01c0c05010301503194000b1244c108012601401c000d4111800d0f034501810201994060700100103c0c408501c0204402e50340c500484a00c880a1071040350030f80a00d0411460401e140340c4042c2404000a200050b0000c1c060100c0402000020300728001140c03240c4420001044102100607000701003d000071120a42c040311108a000c0e100200c0d90310760141c80300c01500d03070807947d43c01009020420310841e40420812501c11050410103042100440301082e582e1035000c480081845100311a01e5203c1c10a01c8401008045c00100c0d021820442c4620302000d08075607988910028103010038405e01800404014032a8030b0783c0040281041e0b58100f0103180141d0740c0c1005104 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 760705260 1250 760704010 760704041
    0x40201300b010f0e1e0a0e07021c0302122701150f090902090a020304061d15070e0d03120b270a0207081b101107020315040c0312020304050310 63
    0x50f2030303480c50040409480034000900700e00a05c030000780d0880e0380a00306954041e8003020258000078070710b030101c544511a4216901070000281408102c004946925500000380341c0107100340780703800503000d11865122140007000381403071b07280d404252240703502d14165401d03075400c00400b64840c811507220401210310800c0500c18199503850a00b04a6550450080d401040d000203e000c00680f500610b41283c040d120001d595007443c2080d200074003207011040c0254202c50f103034101080d403803204076030301c8003090501b681d48030118000a04905041c50000741804420321121240e006964802c810705d02e80a82104c2002c3e40c1c001c0c01c0e82015850114014115040000003542010603001752901180c1c400c034002c2c07c1c07105109801304294111241114144146105155100700743c6c0a1094240d48003490a80d681c1402d0051608281b9000e8030107807141101c00030700c0b00003182030030905c084a0700040c90075010312002404900b10302c0b4643c4900e92500ca0201182041091035001c00702447c90b081 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 760706510 1250 760705260 760705277
    0x6050618310e060f04170705101505040b0f01020d120609050103050f0f01060e2712030613050103020315100b03070207060f0f02070b0307030908030f2d040201300b01 73
    0x40e602d44d640d44212002421200d500c40d002012000000181c02600d2041003a038540012640303182c3d044a0b04001a005542903400c4100024141845550b61002003039038505e40144028001030341d55642809003508000e5450070340e22140f00c19600150180654a20074095940c0d81d0030140d0380d9034103401900c071141c000c05441405843e814880e0004494091801004603502d6035100904442c0c03605845a40d800b0040c0c2c1a401d100c802d00072070344650071414983d501da0509105001401001021001f1290702d44401480580e4001450000c2450311170200c40c00e43d6541e892041b0106100d40c821810404007000b80404d103a00865000b080d20306036640d00103076031070211040342c04104052120700542c01c070400900800240000840d484000c5050121300c04c0000d9503110301951003241d905403110311103004d1202500380b140311943d59810140c035001c1d80301200a0381803001403020304024103000e680025124a0740c00c003c41c56216124001b855011011005000ca01403c2c212002c5800101c401 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 760707760 1250 760706510 760706521
    0xe060d0f0902151e071505100311010f0e040f090b04080c0114060603070c030203090d050f0d0302031e060f1011010b100c030e0d140d0306050618310e06 67
    0x102901c4440f020400482101c94118004d82102d0307000385000c1c5e50100c180c01c4210740290040c010f841c06008150840c2040c1d07840c50412200a241c40010b181c108000292900c004641c0405a00c010903c120360000c0c000807407107403038002130040c0d5400814a00e0004100800d101d45900900f6060038100f0003070021003005201110403510488840d03500c59814804105540e1050f1603a0882c14030a004981c03912200e00000340300f4046d80c00003102e6503400b12240c440214800c4c0f00f4a590304200d03080035401c5041009800c0a910340708100114180e210760000340a84e5541e0540300301c40031010380340315821010100028000c0410040040d06c544c02c001c00c0641c241000070310800c09014940c2c4000d05904d0540c0d0845149080d0552903a02510403202403010601c204118100ca8070100010711a0a2251a0140c1070b510558030130303403040c0024040b004044800c0721901c5e161207000c1340d4182801c04002d19107452451524501e078003210707588142c2c503800c92056000c1c0301f0540b588bc01316456035442 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 760709010 1250 760707760 760707799
    0x120e0f011524050a03050a0603060509030405150a0504050d03050403021908060603060105030c0f010918050403020d030603080d111308070f080c030d0309030512070f140909070e060d0f0902 83
    0x50b0320400c0006800f000300000a030300c658407941e00000403800214100ba80c949403a4161070064490036a19040010108414541112000d51040c594100542810010030b4042c045000c0e0344900b50060940c0c40c50f240800d48035604580207103500500704034861503907030096170b85003d80380106101442081c022440300e2400090580c100e0320000c0081c83c107400c0700380603c6008481d2000c454140b00200c48013042040c4041034080c25103603501000135941c40c1600300280f800441214100a151070b00c201400031400d4981210301805020034040340f48a12800800007911030500044620048254003046884001c500074003101d01580c5845400c0751244103081e00c442005e041c4c650315074000c070707111a5998080c0e000101b1042c00f81c2440e40c100f0091402800fa00181155108005080006d80b180751a80081d00d02118480c10f14940f810880c0c2400410000d650240c01c45c414480481403003146a60b0780411101c813025881c0052040c4c0c8a035020303c1c0003401c02c42c88201d1107102043d042000c02c0b0310 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 760710260 1250 760709010 760709069
    0x1e0f0d06050c30071101060b0c03090306011a0406200d02011a19030b060f030607090602010507080108150a15081c05070c1208090d050d1e120e0f0115 66
    0x40a0f00e120840d5140d4400a40382c0810801c0201c18a5494800004024884001401c0b502c02d51001840d920a00c10041508145050b007001441e00402d2a0580d482905001034400303a85003410010b80e6080301100d0558088400c90009500d445440c042c1601c4d00d50642140388056a07640003885010300500800009541d8411500c0d910b81840c0030030800314100f040c6990b04550094010300d100e0307201310042400c1480c1210001c01140c50000108407403a424403402c0c0c6d000f0301519001d28a541844e104540390540d0314841c00b034040003040403800c0d41c00c050b0b000340030709080900000002656501035a44503000344030503220080c41307800c481038014007640c2140c00b00e660060141480c58100400fa0342d2404198800340c62103c014040f030071443d2194021403015030b0144004140000880070010400490a10f060112001009200a1258001d01c0d500503031840901d020841d00582c00c11145428003402040f885903080002462034400282840002d440548101482c8980a030401c1000ca90 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 760711510 1250 760710260 760710337
    0x910181e0309171b04020903060708040c052e091509210f020909011103040c080f0c0901050d150603110111120706020f07140c01020c1e0f0d06050c 65
    0x30010040c42c111007100310b000c07001c040c1d4010401410f100010008c00c2c509602100c210020418040500060290320100380b80248003c50b000c030800409140d40000b0340c4100b40d030580c25030f01e880e80b00301401d42c011007055028150b124405504d0001040d0010201940351190482c00584d81e01c044000e05100b9811800e415008091031003030b420346501303100035a04001d100b0400740d540c070b440c481d141c01071602c02980264001c0c0b130015480c604100d42141410206241404103501c404032811154660301c2030541194401c581007130451100341400302040034a4951141d400d4900003001c010000c4807242d02d0f052060a903610a003000d1406c10032a035441842d078100509040500c018030006040e60010040011003031003850404c811580d41c1d0170010382d4903450880316081041c40840300d5038100103070007001108480c07140c90800c1610305054504007901c9818042c0008400791070703441d15904246903400b80e0080c0c041019180c001204c1701c56401250070080710560001c407080c04a0704610a601a03034 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 760712760 1250 760711510 760711513
    0x60601090603150b1c091a06030102090f130b2815120b0a1e0839030c030303240405240406080709020409140910181e030917 55
    0x200c1c1484e400748901c1d044048406203419840e9a051800501360081145062050740c1c4849010b07040c0003040101200140342d031340030307130b02c1440103002036504c81904012403003094800c411884d020580090151010510494028a81306144a088102f0300c03110002501010304060000761101610141441c8800c01d000018440240d5051583d80b641d000b402564002030403100d00350352390b03150302d01c088698000c03148003905c44a008204126091011892458103001300c01c45011a008040e943e0401021101f81c4c0c0c1407080018070b103076031010000d42240700001400c903501c0e890624030350031f420304031210010144500e2900680071400d050042d140151101042c036142a840151a400c0c1e5a604c4030400703a115894000c00106220148040c10180c0305403400541d44a080203003c00035601801160080308209400300408014081650681c0000c145000320300071080300c44416040c04107020160104c1c0c10078a521907406c0d0f62850b6030000a201c3c0d00e4040c0d045030356a1410030f00210040112206 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 760714010 1250 760712760 760712801
    0x10207121509020d0602030a0c030b0d030e27070f020a0b04020405130611130b09030c100306030206040605040503150106021906110c030924070204050a090f0302060601090603 77
    0x41c00078580c00341c50a2211000294240e4180c000822500383c07464151041c680c000306100c020103440c05841d8071074415081c06c0c4100190380c404034500e40304c1308601070200000c0f405909150703921200135800410440b500f4042c20b2a240201004070070090702e140000c6440601e820300d010b400818207249032500488010b14560700c035001e01001d04001400c2c101d6620915100b4000116a881401707a036442000d003441d10391440b8525586c6c4403484d42c01c00c960001c402c2c07001c04900d0340d00140d0b1a80b43c84007503501d140382c50910030b826400b80003182c0001b50700c0710002c079002c100d043d80000584203e8900700e0841702a0316000c0301c00c04010702c0c20f005420050304524095030f0680700c100c036145006441a0000503a00d0030041c462a0180c000204040750f81c0c0000450031641d141130404030f801800c6050b03003803c1c45003901035000c500f0f00c101c4400900450312400094034035946680400360094200c8125081d00840c0e15000751a00021078645010034007440d0017203080c074401e120f05c0007210303030b0000c44192 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 760715260 1250 760714010 760714013
    0xe0903131a19110a0302060711060f1b190e0a090b10030b01122f0c0705101e0c0b011e0302040908070c06080403020d1418010e1008060f01020712 64
    0x400c60b404200c003100740044007980040000e810828480410702960150059040986008110001810100c2600d0f486107041c054880082860b01d03811000b1000c0f43c40344030b0400c1540e800b65000b91000d038844202d400014055003034122805501c100310490300001401d440f4aa50002c513030040481035041030070000300c040da05010394440450140705050511011403894031010582e01d001c080307084611034a541d1034545c200c01c01340d80c001604e1023254060502c08a410065601d407014401c007841054a42e0414101c40d000d0101b200101c482080200d038a102c4142d005171005600700011600c1c142004000a19038062000e00c5036040b0051a90540641c619001c20014106c150303025960300400300804000110f8002c034140040c00e56407030304440740c40d080c03c000e03050401003509072050111102c03140000c40d60400c2215442602c00d12584c05c0c035076110004869008074565044d801c20254203e0030111600040c440b48510001c40c2c01c40388401904004988071402881204001203e0801440 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 760716510 1250 760715260 760715287
    0x3070206160e09190906020730080705040b0403030818070b0a03020f25060509010b0a06120906020d090606080a020321120c030414011419060e0903131a 67
    0x50708040600380c03213915030030300440758011540d0b0903400319400f0f40e000640b0703820418003039148003101c1c0c41c07050051180c684c80c2030040e50020200a030841007000f801c00181342c0038001c2c0b013954007800d200c9418640f645e0700c07407a001d07280000550b0000394141c1041c00c40f0540b800d00082400560303812860702403c021000200b80c019400ca07c003400003000041c80305101e034840c0291007031040f1600c03960310419000c0700d04100045540c050a103401e20b904102d4104111703211240400b085414611b0960115032560300390b00020f003003441d00207124a0001405081028580e040310311110f020f81e8041102958802000d0341c0c662404500039015004145845104186809110700c00e08603c00028a040160582c9011144081366a9450110040140018002c40200d01544001c541008104100700303810340400b990740080280200680c84150710300840d8070354100c00c2c000c2031040705040d4241010b1172a50b459401456005080001d00c071800118215900d07280024070030b0003c103280c6007029084248 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 760717760 1250 760716510 760716529
    0x12200a050c0a050a0309030b070c020315090102311e05121501090507090e07090e130506041103060c0a091e12032f1906060302120303070206160e 64
    0x1c1e5030070702032038032580081001032040314620b511a50340c03081450704515126030f50038000b03030100c0e041040d002c180000580700050130981403041030140c0d1000d80d4903000d01c180a4842d64440340c1e550300c846c1080184c1510b140c0d001989a41c000c05803c29015141e403889500e410b200700d2150308010b80240100501d092000046491945610644502542c1e0484a1075000c10a034001403c8541d9441040308666200d00500054034a2951400c40c0d4204540010007800703a80c00740f1152043c0010100c0d8244142014070700d0000e40c0710081d5010b614250608440c0703541c101e10340754064012207000031101d01d0309000f111080c007078903180c0300001c0e410711552040b000031950b0060903001052034040b5803c2840034240704000c2c4250f640c001499112a446081801c800800029551a2020780000048041405440e070076200a51800303400c00e50403c8805454140c0c80039410102c0d0303440102002c58044001c500c030300c410781c00715506600c4080c501240d01c5103261030034000400340300c0700c1d108070b2a046540 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 760719010 1250 760717760 760717777
    0x4090206090a0b040f050f0607111207081f0b03150a20070201020c01050f090103020906040b030f090d0c0f020904050c090c1c050403090e09100c12200a05 68
    0x146401c0000050100d401e00d022508400007103103001c1410490154032941d1000541010349501d4001010a03012950360f004160008044041e2807400b40e4803a01c40032000d44800c0180000c80318116500c1c190b0a4540782c10501450070310000c24200118a49540607040f000c42024000b003800f030301148110210014003400c80c4032125200d401c079240c1c855070b00d1402d4004480303401d030050b52207540d0300c0064540740441c0a02c41c10b2000034000400c03062000341c142e03054140d080c04d0241c1e40721711050006290703104c0c1f81c00805030003a001c07044c008690f100914083c40781c1ca02c4400ca602040392000280c900079900c00c1c0c010183c1c00007000c91401070501010b007640082c426021906075501d102d001607000b80c02295005000b88011500360141600700040c00401203044208121900705514001d1103121a40a409089001200407032181101080112004841d5074010061261000001049140020138050506050000084560301100400403554041c100710510746030004a0644290700011b40 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 760720260 1250 760719010 760719019
    0x1a03040f1506030b0708060a18020d0b030601080601050112020903070b0f0c1c030f0203010b0304021002070305071202040b010314060f01020c03190605070503070c02090c0f0c010e0706020a02030309040902 90
    0x10700c407240d8249000305000386101d0100074000745803000000300300043c000c00c1c0c2c034461441c1810402c005d04000051014001c101d190251756060101c9030380c0c0240129400c0e503601442030100000d038200d808580f980c140e92099807402c04043c1a901058180c3c010804c4259164225440400480300c660300181002081e5122a500b040b000c0303079545085c040581c00b25440c842812104003c0e19074184100000c072110720302c0c210300b19414000000c030540001000280680e540d404101100c3c4e0080040e50015030344403007280c440035124402c804e88005035040c1240a0b03030810b2004102c542c005d0080c540c0103042c0011503421565800100460f44101082c0c076415402000803940c0c21351001e200d0415403c800e40485d412400103031610380300f01c4038010071210400109000b0321060741d510a102140e5590112000000d984a07020312010380d102d07803d501440c0000001e84010b1050044d0031003410b08604000340c4005a07580c8000380d0320b469411000030b506d504100801c44881c87e0540c80300b4140e90001d003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 760721510 1250 760720260 760720283
    0xf06070318080306011211070c140a0e0c030c07240c0504060203070f1e050325020a03120311030405150a0c140c070909030513050a03020904080a270e011a03040f 71
    0x10700010088e4046503096070312074140e1405100c00e13603d0a05500c5645010348482c117250340307850030840c4030600191950119a03000030104510306801d00039900800d030404a00d103440070344544a0701180f000b4075a000c0c0201d003030135842020319000303d0a035021141c4079000340d89455802d507910202014040001c4800d8000c600e003003c04810303002c01189805205100075071b61200070811088418041c1d02440b9105d003070b40c00c0720300700503100c0d2083c000840303611006150000800307401c1600030700750600300e00008800100802c014400000b50040c00c10351007240d0070f401526000d09520550ba0055a9040130a42154207014026440c5005288840c03040c0c003a608c100f51694008015969071201c158001440031610009070342c08242580d00401c002c40381d01120b0b500c2d590204502d198024009402600041800015240a10101e000c1001a030102d040d1042c201d040c54548031100b8054112a080700400210755218100c0d00c0c0d04010041400d59407c5640310398403042000101481100d000701c656 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 760722760 1250 760721510 760721531
    0xa0f051c050d090e100302100c03020a0b070f0305090c0a060c020f060a0309021c1505091c0302040f0902030103051506060d020d0914190201031107050f060703180803060112 76
    0x511468030700107869500d43c1090b41ca004022001aa000f03894800410300b0603200b00b0050b6034020b2483c51401c00c178181840c28030b4040c20161300b440c400300c2010304080171070f000f000071665000400980c0b022480d1410400341d02c03040f001701c2e99610750072089604220304910030310400c0e0003031664486481c801407880c160420703070101103111070f0820094140800c2d1a0300500d0110318025298008800440302000d591000301d807030350001c0030f030721400c0480003036500c4021980080d0184242555a10108885c0843c040e10b1304e00200254480e00c03403d0f280800c6c048010a44400340d000322412240c00c4001054801400d01206c0e500c000041c00f1203038080000c0005040110880c0003800100ca949080050060a942031109009a202c020030a035500020001c003583c5043c100c50000c0c0640a10300050b000f0700c2c03402812418401c498019089104016495190800010780c4912030012030781c045c07011102103070304510201507103000100403900c2807001480e59403041b4444134005008a40205400128 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 760724010 1250 760722760 760722763
    0xf0515151309200c0706080a1d100f0608120a0e1e0102010b01050a20010f240b2803180b0609010f05131d07080d020c0a0f051c05 57
    0x40d80c00700061545400168603510811a031420882c0458030f4140e14008804a545440d129140201c000f4408014041540c2c4115540039004404101700320507046654049010f070789a4070b20750f8000c8051b00304107420340d00ea4040c1c041d040445690400074034407004807110104d81600000b9004081012154400700c0c26990080c0001103900381c00404001502c401d400282522034018081d8140041000034030302d400c0d400304410f031621060784c11003900003040780c010350f01410b148044010071508052400d02c4101000c040308820131064100303500050b0b625014040305001d01441d5003040f8510044440002001c80c0c0d803a0514480b80c90001040015802480d41d003003030b5030f10240c0d4038100480030401c40c0c1c1014003005014206c2001503e4009250400092004150301c1e0b0182025445025104115640e0f544016000c40340c079040c1c9000917101e0807000e5465410821540042c0706001d039414007803c08413114030030381d00030b00c2400401a050030244401c0000d81079445c10f289004072081c5012450 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 760725260 1250 760724010 760724047
    0x1b2404020d0c06090602070f0b18030c03030d0f0b1e060c0a0c0e04030f03200702060f0f030f0c0c060402010e190e01260d0c030c050a0f060f051515 65
    0x2601e07200c2081c4c0700d05085009240541036000b091114509603014407500f40c808082d1843ca0501400d00c00c07440518001003420403032040807081e0544004030310401440c0494000401c051451340040000d40b8005d001c01c980c0c10301502c82c580901088140c0d0101300e00340b80009100f03060406044881012043d5070346092440c080e0301c41c402400015050008260b84104411007a0701549003e0116000800f031f50f11004609400314080d000c030003d501b5086494100555601740050b0140a031202c18100032088241c4c400c039506c14070300c03030264002805801c58005030380400402d20300030070761a5030700e900540780303007540e040e090b42d2008140640b20340740d005041c450000380c94400c5a94600303501d8001f0f018404c810001c078001e0020300c006500c45050800049607a01c441940c500502001050b0034103552550074080e0182c01406080d8800c0140038200203c580400d124131010840c03607101c0001c20080f1070307003030f18a1003110340c1c1e04805440c6860181a6600c40100b0010f80900e0044103441500c240c19 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 760726510 1250 760725260 760725269
    0x1009020c1c0503071b0b0601120e120a030507090b0909070c02090403021509030c060f10080a030801080607030203040818120304030f02030c0102010e2509020403081b2404020d0c 78
    0x10070003c200100c0c507901400007100008030141c40302134100c45075500010400c000b404581044282c03600e003d51700446410414003190745100f80c0e4420f6540c1d8100c0303441a40702801d10300100e030a080204031490f02c68101c0030100ca1101d01128184480002009040c000c00307080202040105044100565143d0700c6240c0214400c1c1c00811002042200c40300000c10001c10410b9a604184410380c5c850302c0104280364481200340d0019400e56816143e003070543c0b140d400200c9a44202c440341020150420304040c1602c0844040f204199241078089090744000c80b0000c0081c0004e201140d40c44a41d4052240f100c10020140b04030303012009003492442e081984255444064940c1e00740540c1014000702c2c850010070700c000d02c0f0f20301a800c4610f03902c509005407a100082c14108040b0341c84002440c140150015480c20b65490b6540d0402c040b00c0d820800001c2100d80c110081c04203240300004444d0011603000e001c0600c1d100400c0040b0410300401001a03030000c41481480001034404000300c0c0107032 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 760727760 1250 760726510 760726517
    0x30204050f091204051507020a1208040920160c030204051e0109111210030609081803070e0604020706060305030a2114040f05160f1701051009020c1c 66
    0x610b84044020715201d0560204500ca060402041c41a41c031803109208160b442c100140fa0ba440e0745101249180c0c90907481170141c07a4070002c4020400c0b0740f0500030021944c1044042c05540361a03200680c089085500030301d07a80d20200300214203410745411a40e00702d8000c4507200d0b81945e80740c001c641664000c403211000c0421482c0480442020000f10a025000c00341d41000b040c2880980323184a44940109074218006038400500b681004c004000040c0d0b900c41014010214107203820056a041010541c0d5024281c14000516080c0040c030030f401c80b01c1c081d8002a085e103c02041c40001d5100303200580b8030585402011021490070402800e00c58036907074030310320489240480204000030300c0c4450305e40d040c14080c202e804120041c002941040d08520b01c220050a40c1c40d05510305201c41810214a86000d50002941600c401c0701504035802d204031101c00c8048040090308071002242c9810440941c1502071002031140d07405000003011110882d0840c50b86221800c00c040c90b9410350f000007 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 760729010 1250 760727760 760727791
    0xf031e020d090b03010e01050616140a03140307140307030f060e0906061f030b0d050a0c031202070b0d02091809010203040309090c0c0201030e160609050307080d140d0603020405 78
    0x2102e60080c030703a00003042c240b030f215400d65043c40c420301610001880740601c030390408240c0c8103030b0104021800c0b51040e84030f03051002188001048a84440c111807066012401840050318440c0f50041241c0c0700307074030540e5000c9264140c0145104030340c1001e4448804c05a5501e50085003d89a100f44000350010030552a802d182241d8254038114000345210b000388030903682c00d80b03041881c0b02c84408a00c0d5504022842c2d504100124444802201e409043c0c2c1c410414058240219105d1401c1138a014040350003010702802000e076038900192054115641d010003a8040c40d400039806840307031220040150b800644503001c0740d18003107020781e4011800d035400020b00040641000c181401000150410710440080c000080c11030001480080d0500d0384800c2190300c01c182c18002403019034420242000c0c09900c0d40d00090808001d80120f03402489011f0b404034034540000707a410001000ea41d102440300610116a507000d0708484410404d80781c40340c45c0440143c0d25801518490040905980030 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 760730260 1250 760729010 760729033
    0xb04030b060a1203120b0a12030306050613030b06030304050607031106061c020402030a0605040c090303020f012a0c0827090415180f110a210f031e02 66
    0x500c4100038052900c9618100320410240340c00356051440160141424646981251040c00141c200c0404d000d5001c102a01c000c2007075144ca01481a425000750380401100b504c0d2002d00116228000d0007103c20b070703420041040010015400d883e48172034090203907424166500c002c40e0480d04810011404140f030380000340481c2404104040d44100100e0310141c9120000141c01c20489030864040e004640000008904c450190044001000080c10801ca21001e602c801064550f10b0700045005006071802402c40c030384140602880c1030010001c240408181491221502c060180c00b0300500031290440c4000c52021305c0a0503004c1d00c88010f00342c2841e420107001c0c0d00d003040040c080307100c2c60780031007440007164022100301700c5040100ba0004030044560222010702d440034600403d0624840301c440d08000c00c10206070400d04040e5440d099041d00c409a03003004048100c00000d02c0064648440b01213032504ca443c034480f41c042d041c07000501c20544082c58203120002c4c4400c2c05688400b900c1034 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 760731510 1250 760730260 760730273
    0xd0608060916090b011b030509040609090c12030c0b0a0b010f030c02120c0c1f03051810050720070515090918030f04060e0907111509160b0403 63
    0x5a000d5029000341840101840b4607980402550040c0d83d01103680e220300c8100d990064015641c80710390b008555403d400d1340e180c0280282c2c04101028055400c0c000c0000d40329125029141c0216130000c01002c041d81800148041003500745000d6040141c0800014007060360054542c1c001d4000403070201c0c4802d907400014102444c12983e85040518101c14019883d901240c102020300100c0b140307940d28684202c08518140c4a103060079841143d00c06a20200e03216840d02103903210071510184016540c180840ea59000300070700d00242e9401c00024070b0b4074078202c0d0b40040e5000c1340e07034103107440f90020a02c41e00c502548200c0294286902018082c8858585500b00f1009110300c0903190f0300d05800a0045040e10700c0192000d4201c0040440320501684181b0a40e0f2002c0360510030303541c96503603654004007481c180b081c03058050305581d000303d19240d103e10b40000302c0000b194002c000101001c6010840355500a0103036a1702d0068960796004541030800d4000102940d00d0482e407118150304044 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 760732760 1250 760731510 760731523
    0x201080612030912070b0f120c0a140307140a0e030124060e0d12020619020a0509010518090c0c190b040f06150605070b1513020a140d0608 61
    0x1070301c2030400038100700c0d44680000c00c56095800c107480910b8801c50340402c00f8945003140d00f003400e840d240030030400f0b82c0095800290107241001540b100e00d9032540e0280c000c40344284040d240000d004822000c94074074807000210707005011407030034410000d83d42106c04030342d422141c0f1500c0069104103010006240074058202030324590300b08154001c814526040700c032102c07489884140b0000c3d486011555442e8156a1522500304503002d544070390403200292180380c00c80c0c00c1c201504000c5000b6500c0a02071081c1c0c0c41c3c0c5511a11518602032601c80103560380d400018404003070300b1481804290a8452211140c002ca514442c05ca460b504004490303400e1089000c412a21b2071040d241c950045404403070f5142d0000d0304807400b1010b040c640c0c101800a0051500803100308045d1240000300c050b03100d00103103e814020288a440341d00c1d121002c4a080000004a550041c440c260b03840070f400b0340c0c6d0300070319520410342442008208041414101c85d00844201e03a102943c84504008518090004 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 760734010 1250 760732760 760732771
    0xf180b0409052401140d0f0504120906050421150c0e0f0d060b0109030512120c090f040e10090602071407080303271509192105130e04020108 62
    0xb008202110041001c0110300c2d0980f10741c10000c60452101030000850100c4212002015080c071024116120341c1c00070303200594080311520034003101c003070405109000c002c06403030f041d5544501d018644925140344070160b90388031844400c1c044a8100140300181ca510302a00f1240c0d010983c42c03130f552405000946030303050140c0683e0a5091003180da03a40d00c00d013900e01542c003480001c1c10280b6440125502030858000074031501c038624a41c41040d0301f00340600070700703007a0089440700740d40c0e030524500300c60144400f8a83c01c00041d80220200b45425008076440c0c0300303080c08560243d1491004503054501000d01960b407503500180381c2050101ca000c001c840c0d000030400405c040d40c50130f440d8940c0e80c84010512080e50035040c0341c101182c02c1d03940782c81080c55001000c0342e030350f00f2a0940d50786891400380da4110342c1d40311b16102e004044144080280b2141e4100c011410300294500b19810184c1d040000c64003049820080c0c00010301c00600c4040180c0914800c8601d01d02e040c0c0300140500901414 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 760735260 1250 760734010 760734031
    0x1104050901060302010c0b07050c0304080c0f0a0302010f0806130227010f1713021002030a03050906070c030804050f0303010b0c010623061309021b070f0b03070f180b040905 76
    0x83c005030741c00240d0b4000741d81d44680c01a0540c4d4034140120303118022900342210310b010000380019445000270f00440c002c03404846140c442c003154010040c2c0051540700017400300d4004044c00b181c40c0d02a00b031107580f10501400004d5880d5000d80c81a0807070b0311002c3c103383c10005060b0808005030600b407140340000800c0c28003503082080c140c009070440c0350b4008508205c200c02d1380028480303070064100380c50481c1c0c040c2002c00900c004002c040d480e6040000c12100180c82c2c000001c625100002d00540940c409407907039144444162406c545050700100107a95522a03820200200e01e01040114001c0580c0341403d03444011200043c0d0a440c0190301036944400e40f152020b106000e40c00e400c42e813101044540e81d69074004100c1b00b03400003046078046a01d040c800300f401c00d080244260700400e1045a10300752031429860b108907480e091128094198002424000115010702540b00315044c0f064504107100302c1241c031203240c0500c10a682049004d03040104041202c05074174003500380c10124801 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 760736510 1250 760735260 760735271
    0x902070b0c0309010b0d150f0b1f021e0f0f031306050a1b030504090b04140c03041b0303030f110304050c040b0a180209032b08061c1104050901 63
    0x121288594280035125501000c40000443c00c102c1c400d43c41059480006401c483c849112400c080c03c07400e0001c140d1740311281c2001c20340300074030007940706602181d10010240d41c260001c1d285050b0000740703010244000e52140001c8095800360324040c21f0f0301005034400600d4070716190078240307090070424058803c556000340040c240b050001c100c0c1906451892a07d00c0d21071400071011540900320900205852902ca03a0f020107040d032202c0103000395144001d05120390302c010b2043c0b204548a000e92241900342103030206820324880700040d0741017400780c24469480700c0c0405003035164200581c002c40110307544e21400343c3d410b040e0380150100c14400c2e6051505501c0c0985450740c8501080540301c1c41959034a0b0268a150354011013400a8124044400c0008512545680095102c0c410061282c4030b1986081421100108520101803d0442801814820782c0301a20b00c58005031083c1c0c0e000344a41c0c0050001244c0e6450650b0752801481286c0c20440c82109010840c0c0014080424990512 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 760737760 1250 760736510 760736513
    0x40905041a1b0f070b07021c09050d060513150c03051506070f081c0207060b03070b07061e05070e0f012316061d012d09060e030406020d09090207 64
    0x41c91011030014034520903960f0f1540f40c900350a480c4610031005105501202c18010341c280d0000d0010502c0c0552241c5c00000c020228040d209140f0390300c51280d22a4032182c00500040030b07030b08000c1d00607200607a030201d404031310307928007030103d0085004211003a51031010188030741e418000c03550084541d448944d00b4990440c0454030500c982d800282040e1a00c200800030043c0c05400c0ba0b2806220402e8440103a4000b0600070203517100c0c28050b28807030700303010003c103080c034001c6151021a100b00c2d246901e0036103d65580e01c06050a10124002d14442040c1c1200081c0c243c00307070901c50a80b980d9192041900002005850210225064104124040c04000c11a0010100c0120a0020a2403501c3c0c0030329000450040c2c3e0040c00080c1903d041c04050109520b156008030005038029009001d1544282c1b10302c65044030355402802d0b820b2401241e01c0f10140d507580b020746080c2c050702011a00840f540708041c5564001e500100061b4004044100c18070b5024104401a00c0600400d61078030005 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 760739010 1250 760737760 760737781
    0x1a1e16080103080c071a040302130e1e01140f1f03171303050a051f0209030c0108040615260c100e0d0b04080909061008040b0c0c0102040905041a 64
    0x5000007030031054002040380d1914810405c5200608400b40910300c06411210032030219081840100e004210301d8542078050186070017420900071106004000d00709200c9480302548200040f084242d550790314200d0320b800d00002100344150f0104241010500b0f100c00040e202c00090024450403e0ba035400910018510b0042042c9900007c01c085464a80c048001e484160f1103a000501c9840b0304c01e801000c002c0042485494246800c0f9407003940500c9080c0501640302d0341170b4550303140e0042807a8414030743c010303000150002d004143c000345803000a0030311420f0108941110b499440c8501f2821403070f03c15212148032072940500902005044040400ca18880a01c1014140700030b09100ca4496210764480f5010207400684540ea41c0c00c0500741a006940012a0b00380a40007844c00202039050800441c0f60713449260751520744568690300c0724415884043c00c541d00c1080304105000c0d00c2c40c0240040c001070005000700041e1400c0c08e207808500d1280c40c00c0203030300c108411007c002ca20291b = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 760740260 1250 760739010 760739027
    0x1090501050c060103030e2b030912030507080d020405040c031e0908090607031716090b190e15120109150e07050a021e0c10050310050103091a1e16 65
    0x240b504203500c90900b100006410b2130b01000e01123514146034006c20703409000512151003158040e84441d0002ca889162100564000716805004a1000c0007030a0003d01400014841412020f40040c102519100010192252020b51400103501e0303504d03254207115001c80c1410501c0c0840300810488a6a40c0c1d00803a0380039050602c0c1c420480800c1d54814540140c100c08007440019018418615118425049180e20f00c0f210780006441a00d0100b140511f40003101c520075520340e881106621030f81f03000c49203002d0182d0040c2d0007481240404120020340b0001e008880e0b2000360f41d00c600c3d03043c4198078040361030750b44407030614007500b003020414810454075441e0820110714003030b6600d0008100c20391400c0c2400c055030400b8911003c20904040010400c4510a03504031050300c028408100e00300ca580c002660401040440c00408100c1903009901100c0c0d4540314450342d03a0110490f440958000404030b40d94003400414007039400720a20040055580b14015040c040419841800e00402180 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 760741510 1250 760740260 760740263
    0xf080f070c080f1629041707050f0f100b03010b10080703091a150d03080a09020a0807080708160b04120f020310060914090a0f0f170901090501050c060103 68
    0x3000240d400140900c40084540100080301d8240011565107401358115070149121456603210035510f0000500c204042402160812407030308000d0020b031f85562103a44030900442e0a44105d02a0b0070541206001d021000c49680000c0d0141d0840f012604054078084507240384240d00d040b4501c03100e036441c40b40001d05035500746030032030385580c61f880160300411302c4010160180031001c0ba4940d001a808071001e05c070310a150a1100070841150600141c08402080100820421303000900107207400d038000b03981d4034001400c948080390784003840d07805c01c441d0707800c05500c0c0d4004210502480008010301ca03040440e070a0501d08903840e00e040585640260300541480c80419041c0358203001c000406003c1c081c0e0003c06031603d5407a0700e031501004090700d10030040140e0030079002ca9404000069003521607968440076000700215651580051303002c5000c1140c1801e03450300a10049000400f200c54031100a606596995008400250205016506c01410000100b040c81000c08004c260a81160b = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 760742760 1250 760741510 760741523
    0x50a0f05030d0504050307150b090604020f07021503041b0b2221050601060c02090f130b040c030203060c03091b040204230a120515060118060f080f070c 67
    0x1900a180140c00c500c1107200c40b0744900c1c200001d100a04c44040000c0400501c220b05200b10007070b611001c80241c6400c0c21845910901e148005081418075030010403010b030700740400713910781205540094038059200c0c10ba640480400700c10002008924500f1a50b80b5441010b168a258070b01511031a0520031040780841800c0c480c616a046980001c01c2a0b010703041800d2040c03050112454200b06668191a050701d041c03140b1400050414080c0202c1d5040680203040580380d81c0d1180030020004001805901d800340e5500100c0c03001c1038814528074001e82c840e00e80444980d1075401050300d0000e0140c1103c800c3c010800901000c4500040c05501101e441c2014111a40305000094024040c2ea800003181490f440801d00c00d40d015400b000007511000c80345442c0c400d40340c441d9208600c8106100401d15030092924102c0c850421103812f900510504d8004045d07580b80d0301c4a80d600d025903100101151460007003803982c1ea080f001e0203610020251810317040d4940f80c0300080c5072050301c501c0603050 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 760744010 1250 760742760 760742783
    0x6050d0b1603060b0307020115140a0e1005061c110a0507061808030c0d0f06060504061202090d06020d2414031203010803040314060411150d061806080109050a 70
    0x90a0190300110f0040100710465600c03442d11840213800f070503c410024031600742505012032801c0b0029803a1040c00d402500c2032036114202000a5500c440c080d00040b444140030703500280c244e803600014000e15068180c0006d14070304101d030032400d88203010010119040305000c0c15240079881f0091365822a04641b022801000f0035100340740180c1c40b1800a81419400010411a010b114000344108860b4001c20426003000f01c0c8034400300ca1142c02024001041003100704275052003000b039a07048580480c3c0c0107152284030780000d220b444214070200ca08540100c0c1000b00301c0040d00c0f075085010040c0f8a0200f41c2082c402490000903200d001c0c94844c5900107480c030b00c85031401c01c6682003940304001444d55950716034205503aa0b400c20b10040ba4440030400c40c4040b80d00e400f1030a140240c0e0320811a0b035030749401c00c042000c03040e168801100360801c00c3c0622088a29507008840003003180e050800314180060360a4070584403140c00c060116810248040700003100021136021894011010240 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 760745260 1250 760744010 760744051
    0xe0402090a3b24060112021215011e03050a0e06040b01140102120f1c09060b01110c011d0f1026072705040207030503040606050d0b 58
    0x18003410482c14503074550340d0603195004450070000d0b840030300b1a0900c035680551504a041c0d56200c078a20030444818103196880407003a41c041034036000101410301c44c600310030150441e012a0001170352a01c01000d02c50a00c9285110a140240e500b18207103030100e08030702850110150000f030040c6560800d652100018a103030a2544807040e141c43e60000e4840d9802c0904020306500030a0195643d081e80b80124035045600014030840018198550b032402c01c5803203113041225400640f20501c19814103610344803802c80a100e00c04040f40f00e0355000404a454000051401649800000e040d80c0314030b411040341e170307000410070ba280554420b021105040c058046050000302c07102d9243c0202c0300900c2200940e4002c862020510b0f529a0b10b03401c581a600d501c144400f5041c0e410b1808941000781c85900e807034808983c43e00ca180706140c450301c6655907102081c126444450194002840402408100b040034002c1900800c01110110140340040d00c2e1840d00c002c0152001aa45284200000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 760746510 1250 760745260 760745281
    0x160c0303022110060206090d111e011a0102010e10050408070f0b0702191106030604150f080f1c2a030e09181c02030405040c0203130608010e040209 65
    0x1401d050705a00070381d4a0660b2070032503406441060710f1400710072103144008101a80b0009840703102d205820020410841c40c040240c1e400c1480102c001402e00030f09064041171180080c49681c05001100001a00c054141102990310500d64a85045904010b00c1c0c2c1101d4200080c444e02900c664070b030015580c2c48038544080385202d031110041c5103007440204001488001f0b0b501603ca078030681c00f517685490074090f0b408079800d020400280508500c8000044a003481c4018683c014009000000c1c1030a8104c0741c6111104160300646072614468018840303640107000d204004a500c400401501c0c1c4048882055000c6101e540c9080012400340b170030340c480609410781ca0300c0015a00d0305100c070403a400c3c01042600c0050225002d000004007140c1100e1f1030021249050300100058800340320081803a0030848807a010036001c6200900000c0340c21366851041400241c0d103500210b07034a01020a101489000c140d00030018019294010880001b444544c940e200341d0450b000c5999541381c40c07101 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 760747760 1250 760746510 760746517
    0x190b0a110415020304080d08010e04030809030702041b26151f020a1106030f060103050c2701110610060509040f0203040f020f061c0b040905062409160c030302 70
    0x4540d60721200c006480d820f03008001001940e500c14103940c10b0040d140c500780c0e05d01d402031003142d0a080300c8100203000301e40301d80700d555000850b110559141c2000e175000034013a034900015615605040001158403260011540490030107a0001c1484903528504079207d64040207022482a0b090811a88030301d0f5642d000044074404800354441c0302c0c0c407038410000c0d650b5030540c004440b000d189a002c19030528062003568401c0004603038001441d6150740046001d014080e101d80b041c1c14060000c0181500d07807a000c0100e4115070751001c0700c88010700c1c2c0010f100101403444600c054004100303102403a035161041c1c00c184e41c01030502d2075a0703c4201c00420028019400342c032510300d02c04002d11040010381141d039603031680205c0320500e0f4011204100005403150300c0800769a800300818002e4450100d4100c515030070b40003400007458202c0c4da21040d0034014100c918550750381d42c5a00c072952060f05d2045c48905990b06945100c2a880c00b20f1001c0c02c40f6280303405400900c601160f6a50800d0322030b0701207 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 760749010 1250 760747760 760747769
    0x9040302070503030c030d060b0903061303030f020403140d09031a0408040312050d06050603070f030f0207050105040b0703050f06010c081c0e0a1502280201020d020a090305190b0a1104 81
    0x4c50f03644042002401d91a50000c03511400c0250415000140c120003a40036103140090060250156403212001c421080c0c1400740c0460170326440b110204200101440074200641c043c40c1c02d014810720803440c0605190082c131080d410703c018150188049001c0c16074a081001c15080400305580b07881c1000940c40c0541c1e0700080c11281c000e4812603885a002c005004a100a030303c0501005454100700802c500040341c1001c0010410030000380321610a80082c2c2e40300542c0340c2c006203070007000d40b1182d00b91402260140c402c1803090b03080c825101d51502c43c050340a015841044e8541c04c081000030001c0c180c21802912110f4081f0b0700c4130309410850048078032405402d070700f0041114462403050321070011440603a010302e6141025651400f0700d000700c41030103094500004071001d6540394403c407800081400d404540d400d0040301c42902d680d10052080c02c0396038852103140791071071034500e182141100e0885d400c5c0021600c03034400540c89000031f64106081c501c000c21001003514400d030650090341e10 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 760750260 1250 760749010 760749013
    0x12071103010c0f020609070e1302010c141608190b07111506040e0f070501111f0b120f0606010f030e101506020a050a03120908070c0f05100e09040302070503 69
    0x20b03089441c1c02c1511488005000d409403034550799441c1e103050f00e0703d001d441415200411840000c2c045008046003e840903c141043c1c0507450fa80e4030340711700c00341c5884240c051591080b00b589020100c10800b540040c24401c2c004d10071240d5070ba03901c9590810098008180c500044046901280074000400c50312444008130780103000403c8682a00382d20558805010318644122503c0e00c22012a80000c0342c030845000b042c083c1e150100458200340c81061091050103950120444103103514140f500310402e0540104c0c100305910700f00310b000080c0e040a411554481d40c580d05100c140030078200c1d44441c00342400031195103141300550291a1120510031103015082d1071a0480d5100d5120900c40014014017240203612054141d0352600c5a010250036079010b0540c41e40001d1060711403c4407c00c0201c408607214005540f43c0000f034011120440d914602404203016045080c10b03000b0040004a80b42441d00200c0305001d400070820659042c0500030300c0c0c0029007454004c0240b42c000f884080d0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 760751510 1250 760750260 760750271
    0xd091502030f070e060702010806091e1609210222020a05070c0f120b0c040f1d0a020307090504050a0209090c03180c10031a190302010206010f081207110301 69
    0x110741e220064012992200418440349503513030f032400c08001359414264180c4444200e0303118401001a20340009106161003441070043c41e400d501c00c1c00010303000e00c1000c0d10712000c400a10801038540e4040e43c0106a02d4014400613000c0203001c8048810a00e8056491544001104210310380c000070300224902c2040c000100d541c50b4aa10800402001e03004140c0222980e071150754030380194019200d400c40c403004103840c9001080d05200425001001c1e074071450319090b500d0792000340c25059170340a40b0184000d4a294000071280e0b5203c0ce9212500180442c80c2d45003940700a00141c4c0c0c14040c180c02a81e45000003250803070141c0c12a500000300800400103840c1124001030107074021584851000043c240d110903200b00020b06030b02210004001000d00200c00200b240104005100038121119054401000f1f40b140180c0401052400f401c5848060950002901d40344040e0f00c201307682c4100060401000c080810071201d03080e00c00c840c60f41d4824003400c044079040c81c000c0344a81d2551030031 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 760752760 1250 760751510 760751521
    0xb09041113090605120703021201151503051503191103030409020715060605030a05070e1906111605010f1205272413170d051602030d09150203 63
    0x4050760300c12208111000e00005407140148882034566203400700c000d1380152406c0c030051414605034210030400c00000140b40354030f100300115041243e4022021101d4445482d241d0300c0c2c1c18041d0b0707a80101c80440036079945281c0c0010030ba03181000d0f020031145407428500fa0080001d04c40c03264490030350080481c0e4507035884030324800c02580150710446410001a98108019645009180c04c803404d60701c800d4219685e40b02c0010282c44001c102c7c100300010460000010343d03a8481e440581d41082a003514650f09140000c1e01c03421047c40300e00b007a5849030b50181d015196002441b8203651007880c044500c0c552020040c1c541c000c400b04910340580c280020000f412044280c20300f61108250070700da071741520103039186841d01d52000d1512440c42d400c00d140480f03480d01015081d0040340d1403410001c81c000d29243e84010180910480324404c20002d44441c2c40b02c000e0160a030060b0b0b44400c0d01600c400382c40d030040c0d40c1e4400c00000c45e8000e40c41e2a490070500081c4060000344480c0d0f20000e640e01d1404 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 760754010 1250 760752760 760752787
    0x1110a080f04030c1b09021b0d09060804020f0609040c020a0507290c031b01141b0d05060105091206010806090d0f111002070f15020903031812030705151605040b090411 74
    0x10f0300b0048c801d1060144a0341074520030080e140840c1c100fa1141074003511282c0902030881e8209841e0b0ba00003000300040b2107030b92a41e2091012940711039010300600c0e0018905281426400d501c03115040d00880c0c103403c42924510b0603c1b41c5a054a45a20768401c00e00da42c3c64114043c0c41c000f4400c801840110b680c5810041d00801e0361041c4140081010f65540e00323403000c1e02ea804c01c150344400c0b1310a0042d40700c40c0c5202e5125540081c01418020704140003000000c004588146e0030308060b07044240104480b807405c0011071380199282015103040b6481c40f030010158142d002020003040008000d4101d0008140414158802410001d5545440b6801c04403070701903c1100441f8040c0a40140d8001070074a842a03808108000b00558600384113880c10450140300c1200e881c0e4441c518803c98101c1c41340070030041c46800d220301c014004540c07014440340c40301c000040c803804002c5501d04140300d51682c0101110b0030740b003140070722a49405903000458006d10134909008016840041c00c1d0302c41c55003 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 760755260 1250 760754010 760754047
    0x1508060a0f15031b0f030209011106070306030c12050303070c1109070527030c01120b09160801090b010c060c0507021206010906140a05101101110a080f04030c1b0902 73
    0x181c0b801c0c06140c49142c101303d0009031148107000043d02c11011a0300051082c0c009140c0303d14145010030b210300c4040c58950400346c00b6101140400d070b41d04c100308100010081600c0c002c203041d00e480e15407801c031521070a4603403000400d07140800c04403500700c600b00700080714034110141c8090038110003440c0030640030300654020041c113414001682502d031405111a4141035030b083c80507001d480b0343e00a00300150340000d42d43d852000c51581b1461b0500c8070351140100d403031140b410b140d1001e9000c0a07034640030340f00c8030068200e2000039007001d8806c81180d0b0480c1c420303040180d02c81750019003a44030202c101c0d040e009903000254030a050310f8514181e06000070301c0c41e040c1c40c030301503003000882d0341c8007002c4224104082801e07405c006403050420243c9071040c0d00e07801c0701c02c2d01d04201c10880340c0c010110b400c4900441490b0301001000c00c0d1151295808640c0e01c1d48404482c1034801541002d860250220703440c281d0041020b10360b80c00800c044400003205e403000301070303000042d5207491101c40555074145 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 760756510 1250 760755260 760755299
    0xf0e1015030f081305030c010f030e070801330f0e13050d030b01080903040501021b031c02060403020d0c021c03121505120a08030f100f0821041508060a0f 68
    0x1900100440c5906c3c012802e00e1014405031036071040920070000035009445105c1d800801e60080560000303001c0420b00512200c05a8149550000781d000450445404120358203d001e6010b643c1c01400b8540088044006840700d10f8040304841c0c0d12814007140c003500c03400d002040c074003585901180154040d0401c0298500c00d1700e40000b02e0341c1e1428031a6403409540b2480c0d00503800710040d40c40f440e080c3c5000000e1150041c054410140c6902d111070712a21b08004e500006034450000c00042c50f07810f000c0307070801d0041450540194200c58000a01021019a50f4070f20040010201410180610407005c10760001c000280400840031000901424a502c1454000c8a07541081c19440e4000300e021044560b00118460958440d00c05883c4019802070801d12414802131000c11800c1c0d00b101244020016032006211030f0300720721105107150b00300312003400305001c0500003480b4011402c0c401114999403494101000e0365a407000500605040e4010040c00e2000d40300402d08001c7c4441c04035014 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 760757760 1250 760756510 760756537
    0x7080a1107050609010c02270f0106030c020601030c140102011401082b17070203090d2a080304051c0f0303061a09010804030e03012d0f0e1015030f08 66
    0x42d907910140005441079501c01c42c00210f06031031a02c0185800e605c0d265404c410341c070a2a00c180d034500c01500044805845450100d8003c100401100c0e40c14020441100818400350007154516502e1000c46003081c040c410403420007040d4014071780d100358402c07030b0020700401040803196500c0120b1915813241e0360110000074a100c8010b801a0b0008903a8100710604d40d880801c401e40c221050302030709001909030821804204400700c0e080d941e403509036910070300a21490050b41030214440d078030b90103490042c030104a1204020001c1c40c01c0802502d084500a46120403403c6540030301520f8541c40c51001001000203480800034580d00d07600c41c2007a80c2c0b44448000196812040d0740485004030484076002480040000e00000e00c41c1d801f114800001800104890071452101407892803229010303480b0121780d0a505504644a00604190200892081004d400c9230550030b512200d00c1030200810a46402c15003200c2c4058a000d500299008859900011014039050850f58402c14904100303 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 760759010 1250 760757760 760757773
    0x4060303050414010503130b06030f06041a01120b040312020705030d0f110c03090d140d02010c0e0a1a0a050c1902041a1e0109050a1e090c051602030307080a11 70
    0xe13940548202c0b406a80d182905007964a1141d6074a0100c0300002c1480781c042c0104010000c8113171f000c000c00b034004c1d486010729104046005200d00e543c030005911909019070307940c0d07200011401e0f4159080c0c00c02c2c0c06160545d81c20019142140191150040003001448005403041c10300d1160f600110342e0214070602801800d0407030070044107a01a0074820f01d8942c2007084149200c4c6441308906180500c29106880318151800f00300742001c0d60215042c0c00340c0d4540000b1200282d01c1501503103950300899440c0042810258248807210704451840b1b000c06002a0704d1300894000c7c829203000e404e02c3c20480d488003c4841c69100c1405540104a0041d41440e40d1161041092034841ca600c05019160f41104060111810601c20342c060a05040c45a50704010680d41c580c1110700340545240400e412080858a801d071244010a0b40034084891070480c10200845d400302c00c4950302e0124244c92440c14045000207425889030308001460b6480025580c203e240d042030b8051021990030381a51030 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 760760260 1250 760759010 760759049
    0x10e19030b040b07091805130609050102090f2b050705090903040e070314040b04020a030b0108010c2705011101060b0d0b030c0a0509013303021c0c120e0c040603030504 74
    0x22114858040d081b40e50b5080700c0c004240c1c8403642d02c4581d102418050360780c0c0d00d985a88900c0c1c100c80c06c10710261400c0e5000542d551301410900001808200145e500c0b003040320300c039001213448407560b10380078030a200605440c4081c01030410840018042c000c0c02ea04071414100044e50f40c036400342c801d00290201e0040001d003490b000744502c444200700d00610300302a40d80c5075141000710030000e100b02c0c3e120303004071004804a0141c01e8503d01910401c400060b40070284d0102034140c0d4680078500760304491264051003420000b81d001c804807182820310b40c200310180c038222805403c0f01e0300721500302813000c1a0480807080d01c1e001502000c40c15415148600600d0b03080c0040988a1f0051682041d1000010041c0c100080341146091501c2010700d80011407210111285110108003103001a1300410070b510340c4a031407001034281100c007400401c54007804c2540a081030703503814000c00c04a0398503842d112060030240015007102c200100b080007195180c0c80c0c040c269030050b01848a003040c99038803880 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 760761510 1250 760760260 760760267
    0x90210080405030f161502030a11040f0b2803060317130b0d0b0402130905060a060804080310090e06040302060a0c0801051002030408100e011118010e19030b040b07 72
    0x140901c0c0c000014515014070a40071581550215803003604151145e00d055010a503505901c102080080801581c0ca05080f500c41d402d440d00e06c01240c4804074100000c101d40130034101403408565100c91a262070f0360184010f2100f41541c1c2c007211402d40c101205000700141d15034854015a88030714100310380007150311243c242a01806076502551105094148400e44000e0003504400880713650100d0700801c002c0101c1e060b42c11084076221008180103060180304202d00030640d0205050f0b41c40c000141c42c05000408a0502600152100d03c0010209042c0807004021001030021108144901400c001d01e49960320000c540c181c0c01030248802044060109004144d03682d85e00340d8400300280d00b00410412500c1c1d0303082c8044158401007200103160742003440b218100d40814080058800c000205650075201003454504294004000501134a5403000300310314003500030310b4111407a4100c10046440c441ca420107292416500100c000200b180d22540749105500c80c001058142e1603102069 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 760762760 1250 760761510 760761527
    0xc091221090102101d0a0b01090501140310150b070822080c0f130e0a03030c08010e0703090f0212101808040302010f0201060510110d082802090310090210 68
    0x42c0143c00c09840c02d110b000d8180c200101040784114401801c480c542000d91400c90780d0601122901d041c1d40c01048060320b0740c400c481c01042507484803904032250030300003500c4d51122071124a032190b40e012100c01740322301441540c000d000c0000e0704690300e4590342000b014a40069294480c1602c0044d1a0900b040c040c29050f001c0340c078414001e04000c0421001c0005c14040100880c0d0424040e1010080b0507000d4000e032010040c01c00090316103403c480c24000c0079503141c0e180a00a00210030010410300414046180c2c2c0500140307000136000f4403a180c44007004070b5081010b076020390100c450841c2c441011030403d1201000c1c10040003010014407103034041c1507450030084c01034607060000b0005540500c08201000b40c591000098880d1141d00043c1210943c610b0600019107140c0c61015211040000070302c10b00301303820440c855203007022203102081081d01021160524000800612500d10b80641c4c3d81c07043c00038195601000b40c2d0070108010101843c0c1a849000d071000c0d41201a80144400c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 760764010 1250 760762760 760762777
    0x30408120a111509011812030b132408030c0619020d050c040f17060a0506030f0114240a061409180603191a130b0403020607020c01050c0a06050c091221 67
    0x40303561f044007420003500140b41c0d038001c8a8012524400200b50482c1d18484c20b201c4041400c1c1c4c0c04004061800c61400e00550303a088008154410040750400c0400015001e41c0020728200d0484e501010642040c0130b402000700405019003081d0a00c852400c060014005a0380d00b85a490400c95640340d09025901d2108420305a80d081720000c103440901c0303500070301e80c411307000390880b000d0b0358203008014212045c400c000c054102c03074030342800514080d000d13051007c0b43d45c00d000c0c000100784100000c0da64907040d20400b018000350019032191a503640e002c0d07070080d080041c52294803588001301810003440c2107620394400d00075040d03804044900f41010340751803078008515044800603401d40750480440504411500320402400b24002051442814401c80c826400342c681401c0401000c0c2c0303450800c911003818810107020403c0d5010f000a110034105411032004140c646440b4000e0260f48180c8580a402c1003000001d01850403001402c9a4600090b000b1034008406400070801240910b069 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 760765260 1250 760764010 760764023
    0xd1d0a05090a0b040b03160302030d0f021c02010623030d0503090d211a0f0f0f090415020a11060f0112020f030718090303050603030408120a1115090118 67
    0x8602d1001c1c1d6039014903d0500701401c005004484440024584804092450740d41c600c0081c060045060602607010000304d01d05100c40700c28a158400b07034031081e403564003018141e002d050110301c451003500b10342c00402951045150355007440c0764907440711a1070325000780244250380c100c42c0140c1c464030440b485414044080c119040307120b14100d40c021042620910110100c80100302041803501c91001ea9a4000e07010070b004400207401d2002c20000350103600d01c1601c071250424410740f6403440303285091704101d640d414695614509800380b00003548001c00507500c042824903146400a05003050459850100d507680c1d900c000c3d00c0305140b0400d0080d200c17109181d140000043c2002c0034044a148402820354030f0b038584031340038208282c80c007501c1c601049468034400c85c245034141c4030b0f1903000700048d8081e51034203040a52113940e9924148040f8500c007000101c400c0c20fa4403070060980f0300c1400388190384805480513544480d0110640710085103500e481011900c854086111104103135200d403 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 760766510 1250 760765260 760765279
    0x170705040b0d060f062001090510090303060915030309090c050915070605101d0408030606071703190606020a0f0201080c121003050d0c0503041e03050d1d0a05 70
    0x1900d8420364028142c2424907075211800400e0b0258440309100c00380020756503001c0070000d43d4070b0360410703528004800c201a914214003000492404a010354100d445440081180344241c41e08800a00b51070340000c0c2d90524002c0d90b0841601c000100d00c040302d019949854540744c0300c441b81021a50a081da00020440410940c1418140744a1003001841e0740d00c0c1d0399050180a0b110f22080d035000b100d88400300000c4400900c0000c82d81001000c0d00240d0007007280311807400e66030700d018610000d86038900c504c4000c18060100541c60400e2410891500c2e07100351a81801400d168a00004c240b6190340070342848404501d41e440003800d0b00415400500304010b00f0780940040d2004840070706101d15400c030030040400c07410b040303502007405401d40c400e00e0708180f4650304000b82058503000009040109114010b0049200003060ba02511460014403164040d1480035038641809503200820354022205084001500055141c85021003e10942e0704180741c002003100558032401690350014141 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 760767760 1250 760766510 760766519
    0x30610021612140d0e1005040f03080c030f0403080d06060f0f111603051c210c091a090f09060d061e1509060915050f040b040606020d17070504 63
    0x704003142c0c809008000703c081140b0710018650900c02e46502090106100501154032410441d00450300c20748035150190410f07040c00b5511216410a11014022020201c0c0281e2400c00a00850310b1445001041545e80da54078940170050342c02240040b00701c20f01c1c092002074918090207224003a10415680c0c9008420a880c040d038020340135001412041c032954512070000034841c03084502450081002b01002801c2c4001000d0714810040d405c01040800c0f00e24012520440e14040380c00f4200950201e40c1d44180c03c01240e0b8bc2c143e59210300c14040607162030010b603041d00170040c1040c06050700e00201d141d10010910106240545049800a042c80c05000116065600c880c0900d40301601100c00b009d90034150006562080b681c950b582c00c01903208122807061445910020921068207000000c007034080c00b014090184220303070044802a4104031290b07101e80c042c0342c0640000300b08202c480e44415009544001c065440008a071250381c0380100395a9410610f4400d000c0780d034400c1d1415013030 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 760769010 1250 760767760 760767779
    0x907050309010605040c0e130b090117010e0601030c030605060f03031602010c050d080709081b041e11090f0108130f0f060501090b042d150503070306020306100216 72
    0x4090100030b558a0700041000c2c0c0c1c846c010613824a0381c650322250078160400400c0b54140e61000c440000714034298038a20652140046581168003585000c3c0c1e40010054081c0d016243c000c626160034000d4000120801810a20759400da9003d42810080350303451b1428800500c2c1e0030017516a06034414040ca000c1c40454030b0100c2140c9206243c80040302c422542c86030f03e0554592196804030f08203030200442c45034400c2560006150b248001c00b40062050001d240c068044881d85010f50748688005490031036489500c4101c0c07150310002c00004400311401d10058016181242c032652400d2544071035507100f120014000c806102010302c01221554640c0034042e5810b40883c2c3c8001000303070b0720001c50080c2c410700c0c2c000c010764540810f10055800400c0111200101444102500c1e08080e40c42c0021029503e41c0811a0b4000090440228401007070b80c60380c43d41c0f1150341403003501c0c800703c00c0001c140c020b14040e0340c0079580800c0000c0c5c1810266100c880490960a0f814000301040241c00d54 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 760770260 1250 760769010 760769017
    0x10f180c0e150618010305101206020f12090c010f0203120f10030212101103040312050702010b030f0714010c3318050c0102160614190909110306090705 67
    0x958400c03070b0003400d10810120f401500240405841d440304112005070395609402050342c00390600e0145403080d818500c40c07861102c40030001800301540466403e0a6403084000c0300d00d4035a40c0010b445142c079000411a65459403034440c0750003d1a281d4a40074404d00000549008600c0745a11812566035200c0002010350006d001e4001c20404c1c10b00040541c49010000c011001c602c4040c02c4005510b4144105552110170801c11224082040001080c1d0103888003420711150703000401c403a214040124090f05c07007145240d40c140102c00c1c1c5080c40440c000b03040c10480b5281262807810100314001076803e44202d241c040c0041081da02d1902c0e14007040c019000b008904242005105081c15003003004a415504400701000d004812031014420200050800b82500b44028440300940b10101d043d200d140b4072138441408502400d00700d190405009549180e00400310040e038015840400900070b26180c4204c00030710340f406011a030b400110f002102d00c540805051030800ba1a002001c0344d03540d0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 760771510 1250 760770260 760770271
    0x70c11030102041a04080601060903080f07020d0510270206041806090203010f03050c0d080a140f0c0102040501200703030f0e090a1a04020309070302011b14010f180c0e 74
    0x15400c00011800110300d42102403000c061044ca10788517410200c00924003507060b001041405906035041001038584000c850500c03450689040d111b00191020901d500d00000f0f00030301a004614201032a900c0c1548000048201a81503241255503030305140e00c0c410600501940091040106100d081d180643c903075090f52003880e00185140d81c0e0b000000480c2c2080e0032001070400c10070b00c100f00740103040000000c004000c64422031890f60980c0c8501842c8076143c10034003803010311181e0201e0441c01c0b0040c4c2d0701001c581c000c09541c400001802c60b00075070203406914080740d211a65054401c0000300f000000b1040d400003000c0990542c0c1f4107892555112000e041004200c02d50110240c0f1136100302401980706100101c0c001591003015108a10b2944083d03028a01c144104200c200000480b4001c890b020f0030008003040f44160744000c2511012005020aa032070708266054100548c414240d50740004420445001d003401041180d0f003a591015002051011082c40405031a0301303030b00e4014 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 760772760 1250 760771510 760771513
    0x20c010315050d150e1b0f0f0f0402070512040f06021f020d06121406060114072009040308071206060e010f050c150a061217030601030227031005070c1103 68
    0x90091002000640e9031054a4030441e800c03150100c20361b11600946451419000c0ba8444c44103e50b072808a404241106101403003009080d2400c01e05880c2caa045844046d081030691301d9120400b02c13a090568028031a503040c5522840001405510100d02c1039030f50035002c1c21000449440382c142001075000401884480d03680e5400c001000024100d0484105101d00ca000b0180c0d401040e10b5814044018829414440d44100b0212000c0c480021110070702d500801d443c40350868041d040c03150b040d100503140e8110a100b8240000d06400540742032244907199500001c0c070208100010a85815200f9080450061003178240998060100284c82007020302c1d0107401c003144400300c1407904914010301d000c201c0e000009d108041d01940a44000341906503080c54201c2d03040c0e500c0d0300c01280f4a480c004280100803020460680c404d0f01181e04030502001e00441000d04184041001101940c11912910401a8605da101498043d20b841103106840e03c880f10300558483d00701c109040302c0184d525 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 760774010 1250 760772760 760772783
    0xc03021203010602100c09060c03050c150108031b010b060d200d0c1107031a071701180515150d060f08030306120f0615030c04050f07020c010315050d 66
    0x440e512800550300030580b5a0081c040c1c1c54030a6800b02c22148072030b1b80759041000c0d90390144001c5802070707154480b059043c500a40d0b0f4100c46071045040c4601d8030741c48040d4803c00340001444039400005000c415041001c403460000ca031080c0c26089805112809400043c01c1c0b015502a003001e5008a1041c0014101c0852001059182c00d400380d2120511641855852400c1c0758120385c020350000303100e1540340c0105001800c585402860b40d00d03004031440d03142420000545180c1c81348010a8011642c4800701c841940c5548840840143d030550a04100f807401c00040c803c0e1800e1174001c220701c0070180982c4e1000300503801e80d070800e5002c1c94400c8022a2249000951741c2c481100100c010244500655102e041003001c008420a286400306042c2d8031010340d09013035038001f140b21341e084001c510f11100c4884401c00402e0130b01414000c03a51744146010708000900c03060400c5284030349020750a50704012095001581101c10416030480e190804020620407800c01148131402c0034040c036420100c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 760775260 1250 760774010 760774033
    0x1b05090a02031509270c0a0e060a0b040602011e1404170c0a2316050f130504110a1e0e070201060f06112103070c08090a0b120a0c0507030c0302 63
    0x2c2079019591502401840f0350a00380d00e48485e5581030b841c2e180c1c01d010705042402080000e142200c54010301c1040701c07088002c51240c1d511220007000a04040200750b0b103807951101d000e40200040043e00c07680d100d480c03450082081c1c00e44140d804091100c2034030803032519151245000f80c0244001d03900d100b40108480815160104003d95000b031040c00814011095003505212140c02c01c541c41c1b2031540b211409644080240380804145c0d00143c40101c0041c0c032000006c1c02c0c0154982e00c440600d441c0100707101c10711002000741c064005081e500340c10300301e541d98031400d46026051000160480c501106103c0702112842d00b03500b05580348000b20b4965250101c0c0b0000240d40e60200d4046100811140040f6506011100e51110087c40b0402a010014031a207510310004280b0f10802070701515440c01c20584400741c1d1003441016043d041c215465036440302c420343c001d25407a14200708110001d9040d11241c010b50801f2107959030307418149902c9550607540b240c480e02c0202c065001d0403c0600 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 760776510 1250 760775260 760775269
    0x3031b0228080106080303070801060c03120f050a11040b0d1104051f030e0105070917010e06100303030f020711090411030a0b04210207050d0501180507031b05090a020315 75
    0x4914400d44810070209282a806a0844810780d108a88541003442080f10700d0790400e07007650455040741040d40e418074540c6012604a0040980700040717900d4001041c404000d82c2c0d06c40303031041d544018104034400e6800b8200789680118410380d04016070822800341034003202d82041c081c0c0c0b40382c0f013a95810705446200180004405111500c182e0503084141103280b5814010203074150600d100030007241c00c000a004100054501030b41d100d144a44080c581000f82c25071100c4800c1d2203006c16144d0034140f000d140c2d824901d0500c0240c000030f09040d090a556100c80c4200d034aaa81d0110405860b4250b0100b4400d90002c018402d4903c0ca0800c080f828064506019010600380300d280c0d804510314052418405507150440c000744424900081d201080e60000f0f03030602a039000325400c3e0f0300303043e00e4500310f8058885c100c14080e11100d0f03800c0c03541c10440c00180040c283c1e1b10690303501c400000d000d0075850808081c0c1c0300e4154065581d0000c03986c190000d90055400c614140810800580200c000c40e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 760777760 1250 760776510 760776559
    0x708091e030c030711090f01050a06030216050a030e1216120c030807060c080c0a2f01240e0f060418020918010f060506070605090118080a0905040603031b02 69
    0x68172045140c656191240c640390049030390002660780d4801e004d505040c00300d444003925000345014503600095650480b251203401c030030140c3e40403044485906062400601081c10382403060f0051204020005400c403020410f211002034240042202e1803030b00055458102c11641e0954840c0b40307803072000c0b001c503422100419005010b0040820402001000241050401046c41c0c1c2c080d0010301c400f228581d03000684003107401ea85000c202d09044040d4001801c090b00440c07a01039503103041c2e004c804092141c100c81c150b48070100c0d1020f96035542e0b008a00d10702c00d421038440c100001104c00241c503a1170a984920803215541281c1c00d40203089502040942c141a2407065005191020011240000340a03221241007040c42c103006580c41c107404104240580000140b20720303200ea0000e90700c101c0035400b99484244103540c400d1944401d091a04440e401310440380f0000388061000f1a0701e0a041c0104000c49925030b803001039a040481c402200f0644903641207a2000c08084040f21038540120341 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 760779010 1250 760777760 760777763
    0xc0905030d08010e011d060f0f0607030207031407120b27010209331b19060c0215010504091a0a02040f050d020108040813030b0a020306090708091e030c0307 69
    0x1140c0d1294113100045400313810580c80b01c0700c03465240d685001c0419030b500030141c000700140c68004c2c07080c40c2d8074001041c2180f202d00103600a440841c075441859400107042c412203004860410f100c18000000c907447d011240900044840340b03001010001e4108a502d41c0d00501101a98020002c842e01001d03010660350f100e601c941e9004613280740245010300d103084040e1000c804651000c01c0b44102501104410752503842c4066021681e00381400131100c10031901c0200070250b031a103c0c010700308039442c4008040c082d44d42628003112550303841c1c000103ca09440522101412641e840c2008000142250440032610050100800b0034a030717016105070340c02000000c5001d40c43e03900700112000f520501c0c0d48038520807101040b420700981d03042502c8940180e00005400e58031700f8000313614503512083d58401000548400e0410683d51401e41c00782d406928200c945907116110004225581c8805651401450300028943c1c41c1107178040030f06007600d0040806507414910003800b000e0560304805030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 760780260 1250 760779010 760779017
    0x10c080d140610020a030f05160602130f080705030a02041a090403050d0f021e07020d0803041a090129010201090206030a05070824010c0201030b090411030c040207150c0905030d 78
    0x280702d014501015a009108034a20080030900344648001380303024011030120f01480400201110001c004101e800071040d0400010743d940c1074140b00400314000785110364101d0172213089020501200124042d0f0407110300074001c0480c07402980030040240307e04c100c954810303546110f040032961151001940f150b4040e03203074a926428001006810b42e6021a12940064410400c2d0142040f1004119070300181041b12940c94080c544041425103100140c00b030300c100c5000c81044200804940003040b00c80080207120718a0301d0b0096a9420b0703070075480d1516211108030085851000e8a080701d00b221101c1440042400f4403c3c0d004105941e2054604001054842c0100710700640c02a02941d08031800203580101d5000074003032080010220800c55040001104000042d603110390409001c4a400400001240c101881c1007881d2050101000b4007a0080001244e502e00c2d00e442510301540c1c118075112040c94080703c2d910003d214144191080c000b40c140082a075407407c02403c48007406684 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 760781510 1250 760780260 760780301
    0x1120c0206070e01030905070b0a05250c05011b0f060605040603060b030f0c0a031b15020c0f04050601300c05041a04030c09050a060812041d15010c080d 67
    0x8401010b00c3c01c49000d1505140c1441d6075280000c0000031900700701c1e62014543d680760b0280c04021101807180c2d035041c5641e00910004080701207040c694420550b88100c005624490b500d100540c0d4103100070341039109504588000c0c1000c50000c4440301d956070b1150030700040c41905e130400078044401ca6003098900c2e40e80c5040c59811803c003004200e20602c0040004d040c2c0da05007a00041040b00b6030b0000404005410805110b07600c0540b040e0b8000d4203205545460307891103074034000d6032100c082140c540300d4044500f030b004c2a03041900c02c8502070003043e540c1814808090300c009440300030010840c052200c1401d09400380b5000d034407820215100554501f6502c41c40e104428007040c9406600510305201003108000088408420004407108031101040903510740b41c100d401024540d000201a0245542c41c10780481c0c414018810fa60f08014011a550f01301406046414801c4904618601c0b01040c0607000350300890541c004035104110561034147c16041040a8a221341c4e07000f0104030164 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 760782760 1250 760781510 760781521
    0x90c0f1409060604170c04060e0f15011b1113090c08010b18070e1306471b010f0c020a0507051e12060108070b0a1d01120c0206 56
    0x20190a81000022184107510707042480c0003483d01d00c102d2003407454070021125486030616040c0014100c0000080080100030b50350822032842600450340506c039072108000217290070008203400c0d1580101a03681c1e04075190445480012010214002d550346000141411810796416030714111440f441580815061130a140c43d02d100115a08036101a0f410708000400b0ba403034040710004031003a61042da800c6a00d5040f001c0d40c80e480c4001c00030360002000100da03c0044a2a0048400c843d00043d02d500100441d010404c04501031486280440d4000780c100a041f0b9201c642c2004550344c224450361800b4820030381b915a001c1300b040c07141030f540d440d50a4843c8000c1d661107000b003000070740d00240400441a42d22991520b0f02800b59034030071008103403000c212103001410003407146030182c4070010740c0078180042c560740c1000f48150310320b80c480c0380f0001c1110075540064030300e5520b607600c40001848455954004040300310a4660400560f8090050f945540e8010700c030660310f107500070300b1150418 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 760784010 1250 760782760 760782779
    0x61207050f071b03061d0604020f060c030c1605010e0f061e0a03060e1332030c0f1204050303450910180504020d0206030126010c0e090a090c0f 63
    0x28840036000050302c6c1d81c1a14050407001c1155507100c0d0341151540c0c84002c9000002d0514001c82c00000140d02c0b02158180c4403a2001504810265441c000c0b2002c0c1e035a9440115070888403c0e20240c0c000e41402040195400d0030005443ca41c10100c211000b43c0d842145407440c1d641020080c0c900080c2c844104004c511490042950450f1070348100003180d0115469000c1500c0707140001d06070348086c0c0800d00e00010800b1302d00e08a01c030203000549a6524510303070340fa0394a4182181d0003a072030240b2440c0d0440c6504242c1241d0032201c0c00f502540c1880c424010130104d0301d010402e00c4400500c03120300003400741031500804265100884046644624120501065210003081d00320340414a01c400d00c124511034611070b01940320342e5030110303459495101140c98803c0c034080080d041180440041289110b00136203008414410b41d0106c036000d0400d036810f083c3e541203000780020030555400c07040c1070b040c118461540100c1c203074002308000d0300a035214003426544c0e030b1003c0980c1c1e05650b8203200d150305 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 760785260 1250 760784010 760784021
    0xf09011214070c3e03070801062c01080607050a1110020414040905071415071a13020105070b0601110708060910060302130b011107060306050f061207050f071b0306 72
    0x52000310100e1100d410713030b5035207020507481811401911003091018043c1e98100401e1015200200091001c95510081c01c020b10505442800b500c039002d0050613040054840c00ca81216181001801141c891005c01daa80c0d41c824080d08041000319420003011030b904001c03950001710700300e100503900d81c6440e01d6040040c4661001e98803403400d1246040105600241030400d603050303200e00c5d201d400c14540c0040d880c04184401d024111002040e84814000014803c1c1c81100c0c140f0f03444042d60f0b40d0314500c80c1c803030740714448000e01013441030040310302180030700c1e004984c0461306051000420901c142002c1c5048000d5028841c83d60082c0100078854a09001c410002126002c00b4407880c3d0869000480a41d05030440102030b0f07030b54041c469442c5c2e00c0340001008061144050b41c06007502c0e1130700200588040d01170103008542403049000503041c408100d4845140000e4601c4058507100d10494881d40b00c0b0000313110401090110402142c0c0000813060090031090b41898283c0c603501d8214162503 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 760786510 1250 760785260 760785293
    0xd1701031106070b13231c03021201030f020f0a1d060609030105151c1a090102070c0902070201080105151b1f0e0c01020106030503041a16061e020f09011214070c 71
    0x400448900d56459002500200d0720884554070001f401411108400078001d088402d017040e43c008000005000c02e043e400c0d0315003402a05c4011040a0013801d110749030b80180b21b0026011108000149200c146004554000350700408030703482d10124100003401e582c0d060f2504404012490034040c49441d01401d4051501901c481d1150700c0b14580d159001740c0408044100c0e0714080c442c001410f601d00039411640019404201c140342c179500c85a450000f501704440c200d0102d0894400480d4918129a04c80c220b80044003c603841e00d00c444614441400840c10462082e2040c00514010321079184901e85409180c0c03080081c0a0304404000d51410800c03030b0490f03040d6407600c08244081a07000c001ca03426500395114084040c65a440c5a2400344a0307546480c681101e01001c3c8402c02c281c0b500314444e1046001c2c1118004c1000340805070491181185155a1003003c00224403217501800000c1200098144002000c0802c26a40010aa412100c51001484200b00e42c2e00300f00501d0020030580 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 760787760 1250 760786510 760786553
    0x40605030c181302090405061006021b0409050a17090a09110301170708060c0a0f030605060313060b1221070f020d2f01020d1701031106070b13 63
    0x40d10018041010840b0581902082440031000a210310006601c101042907002d0032020310b916081c00c01c981c540200ba11b2561b0b030240b491100045c00b510001c1d0a020030520b42c0320210300305248104010040801c0c0e00100c400d03000f02c1c401d110102e07001e0b103602c11081080b030300019030f5503c0010801c4082c0810390000b04c207041c540402d13006007270400e0069906442c10140c10b13031510503606c1460b918103c9241d02458082c07040200300b00c42c4094441c00303804042400d482e480b4480303000d04402e50a44086008850300a80207000142448110010320951980114000140c074003030040031a9440729860580b01040e8024203400084200c0030710709404104e003a10030700c0c1c00c044080c0d41d11140a200001e0207481020503895001c24807003c241c40c03140041a0422150480e00c04800d50318240c08020380070307409402800840401c1c0350192020328601c0c8e4281c2c0c840800c1d40c0c25903944650100000181541210701440300000050b843d90030345004850200000b06814158541005030035040443c04008 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 760789010 1250 760787760 760787773
    0x602011e05010b070230031e091e0402070c0b07020a0e04051b011101090302010b0a0b1e070602090a0b0405090c0a1b140d080a0608061009090305040b071104060503 72
    0x40c460b468241d40c4c0c1d082d07045841200d20054600c0b80b503800740007100140e04906545040c030007003900c000018030010458890303004a544028030601624007811000c039410039403003444004c021030000302c16030009030018401401d1038050f0b203c40c43c40a509400000360000d00084200551419007901c00040401c0d6180d9009442d0079507400b511400a1200b04141c009840346800741a030044556200c3d4030361943c001c005410f11410f0080c00f034440100c0c0c0602900510714085800f003102001c841c442d20902004540301c2007441c083d041c16503c081d0041c0c0b106903003031000c1071040d9038001c1c0e480700901c2c0c0c104025072528100805c00c103c0900207004498064410025900c0c2c064014401c21002141800c600c03c1081803814088201040041205402c0c0240d035800c8190b02c0e0448005030107203840701300030007516132541c4031103584e51070a80c4e0450f40e14100c2c040400a04820341c1141c00e1581c82890158240f82e56040f40c00304640060104858080303a20384010240e003420700c43e0743c0c001c0400b02d006024 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 760790260 1250 760789010 760789019
    0x14250e0a1b08070203072001031a061b070b13080d0c2120030d050906060a0e07020f01050a0c0e091909020402070807050609060f01061b0311070602011e0501 69
    0x10306480001e1900600c040d880004020302e00034000da44540360808030071600d10103500803204100d0001a00c06011030b1501201c0040c602c000d0010310781c90140540032030324222400b142d0030700118518011511a21509201040030000c0c0c0010341280101e80f09006d0f0201c3c01d0002c0c5605002a150040007044000503002000c00d404224402498001246070a46041020000c4030021100220504030000d000300c050801c030b400100a01d40e404c4202c1c020407050f100c03503500c1500c0d404242c43c00c40c0d004a6034140ad02100304444400c0b50090950700441e4604212092100d0944208982d60305006030b480d1a04007165811011000c11800300702d401036605d240210f0b20740a4088001ca807804500d98900c010b4085485e640d046a19180c0c01201d510303110003151038041e076201b904a42c0d04107a8001c03100402c0100010400c0d19050f03d9a585908003070b1003c0c01901e515441d6480d00940400c5814030b440c082821091207194044c00e115400031941c450400004590f4241620790b28884a103080c00400 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 760791366 1106 760790260 760790291
    0xa080d0914130c11010e0d140703080c0306010309050a0506100b040b04091107060525020c0603061302090603100905130f14250e0a 58
    0x9a1988418942040d420700582850700a0106400c8500808480d0032010b40207001d4584460300b1050424080e0035900c03a0010043c4c9034001c59401c240d104c1e0300030450241101545100b901d024000d42d001001e00c02c00506c00d92032030b403021000ca14240c0c440d4204002541e044001c8481424003400d20a80394030040d58940340c03081080900254036403000c0c098074107e9501d03484113070130309107482081805011440f9032010491000c100b05030018200b4813500380202e03407000c40f000c1044000c841003d146401c00d00c120095510107042c01c5007940c1e0b00c0307084a5004400f45c80f50000700381c510100401074003e006280e94002c00100c104a02d003200c04100d02d046400350700041c4126207890106241550088402800d5095882c0e10b11000c142000d40d2032080c8908401192040719142e000e80350000139403001c0440300c00c1140070820070b0b41600901550840c2d04c808040011604140d44607 = true := by decide +kernel

theorem cover : BRFrame.Cov 760611510 760791366 := by
  have h0 := BRFrame.cov_init 760611510
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760611510 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 760611510 ≤ n) (h2 : n < 760791366) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
