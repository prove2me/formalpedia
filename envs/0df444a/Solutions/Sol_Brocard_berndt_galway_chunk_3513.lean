-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3513
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:52:53.227178+00:00
-- url     : https://prove2.me/submissions/4e50784f-f1d2-4108-904f-7df015ee7613

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 631654676 ≤ n < 631834532 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 631655926 1250 631654676 631654697
    0x20604031112070804140109050a090903230705240402010c02030f01050f0121080724090606030b0f100614040314030304030f05120a0203190e010504060506030706080a020a 76
    0x148901400d0f9042c020301c0420340b07550609000038030300d241682205050202e103172010031007036550381c141c00151a482100401c1c039228502c2c040d034041c140c814a064060010001c4660b840c800500036144283c010000c90382140070440c00c506200c03403405007004058040d000040c0155000d03e02c0d02c2e135002d1003c4c0884144c504030414042c2101e07001da40220003418414010081010342c4802000180748a6446201480d402d42e00d9a400c2d10421200401540305c000f0a81d0035021038460030880414800f405000d28040380c6082401404280001c8400d001400c0124060302034103801c0780d100f0b10500d00024002030a00a0541321103522220750b140090381000007200040c01514900000c8015500031f5490341098035000c0d04c1840740654800c00c0140901070181d0b080361220f015604210030780b10059407621400f502604407000810001c1985040c01c40d08482c43c00f0560040b80f08600802c4100b1064446604060b11288140308260004030141c000c2503035000385900605990b1458240b4004a4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 631657176 1250 631655926 631655953
    0x1c0614070509101e020703060c02030a02060a1104030f2a120f170408070f0915060c110d050c010806090603030d02031e10031a0f0c3108100b010206040311 68
    0x1480602044c1c00503000103904000b040040d01598601d0342150007d503042c441141402950703400d000308403121440d1208030050010229804513000755030840e14060030170080d81018102c8802010652002c011070b07400d17541c2018907460704041580c4440c00c9000180c0500e81300e0455904c00c170701007601e140c0404070040402041c001d005000a08040000d41005880c02800400704040d07a403103500c855003003a030010303514501d8401d24401d42e04141003400a803945814100c03204100074070095085409034541c4000c7c0500003a00d6180c2071001d0781c81d10000e030b8941c01804030280040d61307025096031003071100484514064028645c031914840054240d01da4a1456505180b4144c500c9103403006070030020300c02d00468051041d002002c400c0c807003110b4203050f540310ba41c00400030520314a001000c110640045c06902280e071281e0460f00600300d04180c11683c002c48480d031440b80100900c60b40441c3c080f080340c540184811340c40160041d1403a0b40d40ca84050703846441001ca02d2501e40500355512607003 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 631658426 1250 631657176 631657217
    0x601020c0609010305100e01090b0301050105041a01210203010b190216060c0305090306070314071d0904060e06090c0307090b0f01081b030703021b01090b01050613051c061407050910 80
    0x27811032400104513800f0340740a0508403076040e04010302032800d000152038400c951000d00200483d003803814425441120940101d03000b0198442c20318180000000240c01d805080a060011841c1000030b281590594041e651400c045a45520400a03143c0c10010705000d2260102070074080e04106142c91410310000b4200007080b83c528001c0303540c940ca64104d5807055200142d01204505041d20200702481034480f20408901000388142124400541004025006a154071032114102c0c2c0c03040c102a52029250035880100d80d000348100c141c00031344018580a409444100545041518608480111003088004014000380c81c190143c0071a28502d80e0011803003689950340058946250b4030460184c80c4455030341180e07507818210300b0b50101707884d4401c0d68110b600842e81c196843c10b011120b401030091540c41a580068401d1211b1034408003048040f80c90340c072502040142c041c01082c1507200340c00954107400000c00a03c080c00e210700b850020a40022983d081501d040700b0060020310300c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 631659676 1250 631658426 631658429
    0x922020d0506010614070818040b100e120a0c180e0a030215160f0e030f16030203060c1e0c010204050411120f15090402120d050c060601020c0609010305100e01 70
    0x7055888040104500d0b0307030040c540388100300400c15079460640340d030711100d6840c065030b1005503000b044038007010402e685c2c9030301210380c03844040c000c80802c50303112602424100070b607840c450145440072003680403c0710104819aa081d88044003005d600e040c0807c3ca401182d2000c682c03522581d84000c811203481c020040d082090307100e40e0081c1054482e10894003881d030000780251460911110400c00c0c2e0301c0d0411003491890f14a440d02d0789400e1015000203240103854203a50401c2d0084050100308800ca0501040681e4001e070200c51041e2a07850b80d158440c491340304042c0d05d0145c40d003900c43c000c49a800040c000b001546001508254036a40064100d41000b04043d103580390008124440e10cc1300c202650f1b012202d0f40c031090b03261904d20003050755041d00b481d401c0d21620a110000d021981e500080e460a10072000442d80558185c01d0080e0103030f406034400d03c11314440e10300011000c0d0310015030991411800b61100341490602001900a454050404c0a4066820001040880200c4451070 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 631660926 1250 631659676 631659683
    0x1d0a090516030b030c0a0506210108030702030f07150807020a0b0c0910030608030906090a0b0c03031f0f0e0c191d0a031e140d09050406140922020d 65
    0x5801d01d009030405011101036040060080c0c1202c1e040d101217a483c110b4900031101d041c0c03141d50759042c281c05d10600c92201c148850017050345840000c41c80c1e20001029206d42807080c0c0c100c07001c1840c10341c00c9035501c010522542c148a43c242990429480c1b02e640301f260002d0070703401114500d0007280e5071800d040d0402c9075250547c21003c110305565203426000800d0b140181e04080001c1c60400d03081d1030b124803909001c2405050002407134000e54960240e030320001c6c210000c01680710508080c005840b6401035480315030201c021034400f07860001380c2064900315290a107008004620b00004403031030b000000c00400003802c046c4802040034191441000c0302c14072641c2c8990300501d07c01d80441010030801e0074140580100380051002512240c0b030198600c1008502c3c0000486a140c000912440802154100e02075401c0c604130311034101494009440b01114103100701d0f6120510720020390703c8082c1050b40007480c900401c00003143d00f04410b0800324401449a2801e206401113241c40da0704001c100d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 631662176 1250 631660926 631660951
    0x111c050706030c0825051e210912040e060a031a0103021e010c0602070206040b0703030906060605070305090f01090515130e01030221160806060102011b1d0a0905 71
    0x5180c4c1d4421029584800b41814086080d4502442104080503175500b20341440700000c0c0e81191910b0b800d840d001c04541802a80b80e079040b8101d1540382200322001911600301c0141c0118080f400081207035800e1a000c0c6408ad801c041c90f02c6480588000c0140c11a80c1151000802002089208842000000340850350445551540c81071180082d0144244c6048881809402600342c0c0d002204e0b0610170381002026840e01401e000054044c451548128200c3c034000800704205501600700c00200b601681040182ca965840c0035200d82c454204010005903042011390424905541590003c41042c50030344400d0381c8801c042524031401c1c0c6242c422215000ca406030004a0000401024042c52907400c0d6055145038013007600303d2440000603801c0749051952850318174007084040e00e0882401c1c196030089643d22001521a5000c0c0d500340d0043d400e02d51168460036403050780640c0075825076140124458004110340841c800038404139440201800e0002d0b42c0040c601903540500a00001c1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 631663426 1250 631662176 631662191
    0x903020102120703020901022515020607031a280902181903032309100f08090d0801050d032102040501020615060307050f07020d0311010b04050103111c05070603 71
    0x1103220012006040341c041500400c52028aa44d0114131009801010842d82c110780d071440340d0500b26030320242c00480a1443c1d041e0388ac0d01c510303400210280030303992603201040074510140750381d51407039139400040ba04140e800070b414002da1004d00700480c801e90403000c0c42c1040c035100c106580c02e90b8070800c524070900319a90f940003207602c0c04030be00c00001170f82c45031202e10040c5943d901500011112f141c01d60506030b4940d502000d464000121161184001c0c000015042e40641c0500036940e80140b42d000600100001204038000107440e421044a03929012256881c0c9010045a0340b1403020850801411410020200d0841c060038644174201940c05615242010002071900c4030042c4008140c070b519840310f54103600c81d4001c0300e80200b01440e006544444440000b9594031520000035081424010581d0030f050748001604000381c00c0340d00178060f01070080c1c10001034070000e01000d0140e00030300c0b8111601e4070700b15060b0010400c0614690703480f400c2176290035081522951240d40400c1e140c429 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 631664676 1250 631663426 631663447
    0x90d02120703150f0216060b1c080a030c1d060a110304030f02150708340b10120309090b030a1502120a0c0518011b05010e0705030c130207030e040903020102 69
    0x21400070070104e0790110b042000001c1e119006651a403c040c250540d2091204c1858070307a12181c8070b110b50b40f1032a400b02c074400d0f440c14642c180e0080128100280c94042201030700791003008030381d603c0079000940c3e410681c0391408101599021000e000c091100c00709800b42404014006400154051032290050385694010300c0226410a00504900030040000034000385e004130903500c10300316013011400c01d445000d8104124140301000000000400d112901c10403140c94440c9120300200c1065283c010303511001c444c20030600120060100784e20300c80910645000c5c1d80a00c24a403c02000c855540c1a6a11548408010007100f59641038001442c603600c508810400c1d900080f0b403440801c00302426034002046070141c4850442660009481c013074080e031094110031040136090030014a81381151600c10300804543c0b002003c54007407500700081074070f00410044508000030b421036141151000a0718025032040d031045050141e01d14440010380c0b2180300d56000b65100360001a41c0d44007904 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 631665926 1250 631664676 631664681
    0x36090b03010c09032a050a0b180a0815100b130305010c18050918010e0102210402030a0813030c0e0f0a1a01030b0409050d091509060203090d0212070315 67
    0xb40d02d2428403c000324200001191903420b1102c2a448402205804000c141c40440c6036a00354001a48a54210f0000c6440040311000380074180258040511928117601407103001780d07032441091656084100c3d072803c400c20001d11160700c100010358100200d5101c1d0826074140c1c0221024112146c4e42c50700a0041103800d02c07403c2c0409041e400c00c06c1651060a2020056800d1030151501071041c0074042520714603151040046200c203d402070251100d0003052a0013504000c40d0809400004002c000f45a09010fa209001d190007070050005c05000f61102142c076403102c0d10b4506291070b2005d002021a11000700100030b0024261340300c00d076090286851a4424000d0604203c852a0107103a00304c201400d15802c407801b80078240031902d910300070006001442c0c8050068058042c6080c80ca5070180e022098400741d918206140d80783c400480422100601580103a4000d88d00070014a0000d14262403c101c50510040c070108460610401c298104051a80201c4001114801c042a038841c0c60 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 631667176 1250 631665926 631665941
    0x271807060503060904080c0307020301050a0f0b151b0a05060403080a0e011503110d020d060605100516023d08090d08040f03030b10050901080604090336090b0301 71
    0xd107022811401c0c507100180300020007a000810140303000400043c400c2c014802e481303000d50018004c210502e000c1101c100902242428010341a2401984d017809203048521011800e210748810307030800300213806001076a00c0104c100305551041c0810034001460030011507208038402c0c0c2e6040c006040001002042c0d60350a040b000300350f414003096100b1400007945110072280c0051800d9134484910000c0307090000d5003003010f0b41188490200f002403100300d170000006c80c1c10944103102d1065080608441d01d01800c0c2c0395002000c4400020005403a2550b01601c038401d1291019a000020429800c103640d222020407400400c40c2d68107214190700013040550040c8400040d010f03001a039500103000307140051008241d00c008207420024948240c2c403060315000040c2000985100990010b40360303400c4042c3e01c0c2e00003420702d400a11207051501070a200180c2c1500c5076202c1d80b242030000ba1804000d2288008080120850281c0820742c1d00c41c80001015142d00004007200c240e4185401d48040 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 631668426 1250 631667176 631667189
    0x302030d050a02060f130b0a0e0706020f0f06130f08041503051b040623091009030c050604050616020d0b011d01080303040305090d0503091518180105271807 69
    0x1400c0c20050034a640180c0d1120441c1e1002c8552201d41d260210235000b0a9107240c140070314030901102054698001540441c445260b4044442c4c089031000e03119a51141200e208940311100d41c0d00a000522000009005a11800c0424181030321004281e407881180002d840c0040e03245c0b0140203040010038642558000154103243c070b0170f814244060122502c0741110040c1076080f51003058011400016900d8040004001581d07900d15594000c1111405001c00c0e255070000d51000101e5140600846007190401381c202810140a09030040204081c010140c3c2c2002c548601030000641001840340038041d5104100030443c0c0c490440501000141c02c6250f030f540c000c1050102003504201591011798003101c0e460650b68407840d0150440c010a0140c03604500842c1002000f8041c00010740480d80c040d0a542212807080b03800c100905201310a010354490403400184541d09001140c0c00020315180d03681001910107050703051942c082218001c01b011401420498000800e000b0040101074 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 631669676 1250 631668426 631668451
    0xa0b0915010e1002070f24020712020d050a0f210c0c1e0b0a02150919020f01050c0f0609060702060411012001050a0f060b0c030304020603100302030d050a0206 70
    0x5040d002038414000b8015281c4200800441a04024400c20200c13016022803011100301503520302d07220400014004061031000c40c4c0c80c1050b400c0b030384002503100c122a0103d81445080c1607640a024842e07034142015640360141200d00c038003240c05544896007962240d00b0050829540c03031180ca07041d051462a030010084004003104c040361f80c40417410151543c0380e172040c68401e14400000d80382034240d40035403011031000c0303a600700158010071009003200348003002c10810340d80c1d00d04907a00c0e0080061020403d000b082c4403031001d42403619031990500c1040c1080340c45e15a048900d00c1c5450904d0800d40304d40d0307010004010120790144051500060907000404c0c02c6e04066903441440d070341003040700e410802c1d820600b8081041c1c04030307884a205410b100821071406c0c01307100380000d001070741c2e4805036481c24088000381c00e14486046030b42c5603000c03002a5040d51a17a07802c01c2034a43c40600441c4008041e4040440581d40511682c11010482d80303883d03540d402c03070100180c233108008004451000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 631670926 1250 631669676 631669711
    0x309152a050a0905040f200712050405090a150b0408010b030d030501180b030a0807050109170c0c010c080706050f010e130305070602070606081b0103050f1b0d020904050a0b09 77
    0xd40144003c02628030450300814204000b040100c01000c1c1c1200c1c24509003010480f080302e411004009211550041080d2001e4040c0040d050311a4803980c0708207038101d548940041d0982c0010341c0040c00e2906100380c0e6604159450b91740f0151174104e500003852595440105820341d1604000781d0403844001e0400344100e603d020b1101c0303c5141c00760740c4810f138140c4a94441e94030707640c180b1004200591012413a51508000d00780719000384041e034822903d60758054102c070010300f5140d0654800d400340308000c0c125600480011640e02001c0d00d411501440b00388214000240700e4000c0c41e1080c1668400080c4940c034001c007000900602411091840c10070348110404030b07070300c4011610455081040580d84e40744034070340340f001030429a01c494040d0040a2030340300069852064195120000da03170074045521040f0040820480c29252004a007083c41400041008244080c00c04501100d9005003014060340100c1d05036030080f27403a400b0013a0703221a401d085242040d81b46402c404440711540b03005 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 631672176 1250 631670926 631670947
    0xc0207030212011e0c0f030b030d0e010905030a060c08010b070305030c0304020f0405150112020c06063a060e010b030d140408070803090a080604030804030309152a05 73
    0x8014a0001a0048040c0110390306010000d4002d0f01c04410400e9030014200110040345006114003006800014503080300c898a040c03180c015040e10300c0c8000c000e030845c54200c0701d0594a040045207002d047c4540f20500103940c0d581444104030650041b41c012408000d00b8030002c0084205800c80a4042c40602106000c20790000a403a880040301a000743d40e5101c0d40002511484102d103410342c06414002000b100d00c80d040d40ea024820130a880d0b250052030400e0840050740510858600c0c15440080003030035a00e000300740014003102c2850302c000b40801d0308803142000c4100c1e8462444048502e81d406040120a100c5d400407448140000c0040b41d082d04006500d402c2145c01c40820007403c07134010094040a641118024400d00080303c84030f580c0c580400d0f460750441c0b83e1081c460800d03a6000114003201090380c2d4031480d415903401160740d8440d54168018420420140e81c00c541a0072000e0708004203200e09054288004401070000e03030350a00b691000d405205c0c3d16000c0000c14015031861 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 631673426 1250 631672176 631672183
    0x507020712031b02100c0209060a0b0904050a18060e0c06040806060f0310060626010e040602071511090301060603020406051c180b01080c0406060e0616080c030d0f0c02 74
    0x1020750501d003410b0b0f8104100b0351158051181e140280d84003070101d55241a0076007000241c00f401c0e20948000302241d41d900304024103c1c807913116840d43c03603100f0400c11300c081c6000e038030046c3c1c070082c1800d00040700550344a100e041d130502d07204103c80c200c1d035911040d54000002c11400407210b20403115545403c0c1001131160b2100005400c06016138041000191030780c0d001d10821001c1c08004000300101542c2e040000c2c040546040203040b04601c01120f12004480c10006606940710580d03d0901c980340d503550342d0001e60114500743c0b401d40600304103c881c00200d004813410303112046070039902d0340009010582140c0d441e17440078007403620421042101c56000401d4501402e403140400d410003140400c450064a400c1100ba05442542d044400c20459040c0c0405c1c141d035100021125100040803e12045400c940281ca02147c1d02c610414181d01c0c03d08024100d202c0c1d008444045010300380e039070703000075080360643c10302c550130200340310f01e0081e214403884000740d150440034800e41448103006901c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 631674676 1250 631673426 631673459
    0x150609110d09150c021b0f18040c080615010e041514010c14030a180501050403140c1e18061003050403141c0606081b0327030a0305070207 61
    0x7441e41c0c42d00d82c0c400511103460010100c60301400d809003c00c50030000001c1d140c800e01101c00075482422600c0003907e040104035680e542402a1510440c491404403110410f00001c01c01c0707440c0c41001c000440e107200c1c1844030a020f0106100c0c02a00c03a01914005003050785400f0a03207004901c0d000707401c00704400000b01142203d02000f0f121388000c00d00310040380d806010300c0002c0d000d41e020071081c500c50b810000003004410026548c50b040d010b900608800c480c0d601d0712516000440c01d01007440442c88a081404560b49400100e56404520a0104100e00145910392440d01c0d4000d07825185801e19a101d90460051404c2d004218941400061040100f9400c80000c159643d00080d08160044094482a1001a02840c1c68990041250880c010ba4402c0742e0101e5050070800034401c0c0c018042c03140244440c1100b00c04281c1d9601c101c2080e500010b0420090040c1e0241210032600d00c05902d10141c5098005190380e051503c40203000d40340090f04900031944450b804000c441d1548c1c29110 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 631675926 1250 631674676 631674697
    0x90911060a0509060313170a0807050a0521100807120f020102010b1206040c0b250201090f0303090305160305060a1a06030f090705100e010305091915060911 69
    0x40e1501c02403103084a0500030800c03c21340090000050060038413509803c040481c0c81100301040d44007034030051a10714000c5074410004181c030240490180c40c090310150070011040c0c40e01c2820440845020890f105800120100c41109132080c00b411008212103003004d813050b04001c1006525011042c5001910701c031020709400701120030401160300c00e400140c1c0d402001000124030300040420203856050940782100c07040d11800c3c0005d030702c040800544561800c103070112010030380100b00019a0182c5100202d041210001020070410703480c01c45103010710700954805c01c0d00da04501d44140703400c076140f030007400d41c80118608000245001510541c0300c8019603003c05d01c48460070741803050340030821007594054408820420351408250340c25101ea41c1c45d900b1a0f80b00e41d035a400784601040c0104280000031002c40050607554001d4010303a821945240445980520241c0907189001c547c0c4c00480307008080c00c1028004117490301800019080d0540c0c10403240615038102505880383c0c80418 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 631677176 1250 631675926 631675939
    0x1030b030c0427030801080115030201170405150705040f0b07080405130b040903030c12050108060703021b0d030204061e05090405040503070f0b1b120406050c1c020301060801090911 80
    0x1e0303100160040c0c10342402c95503c0701007010a40c0c9442c000d040e44409000f07903481076203462080749102c0c040050080032030b50182c585a03281f01d1107204030b00450354020000d603054420901c003908400e00249a05108207596070310203896500b0440c20704040201a0b10451601c0d600b4030180e0041b0f0b0884040342c04a60342111545212400e005048019021074803401c0c0d482468640c0000078141c15400001000c00203030703903004a42200d034151404030364081c001c082d4683e0091000400c0d040c0607900615200804d0000b0441c0404030007603451a109503010003400082d0046020054260415101c8615104d64010b140c000b07505404018040d0255003445485651140c002c1401e00606108032029260015000444000b1504160360340c0002603540081848298240075026205501620078002117010301d41050b8613240c60b203c0c05088094007001d0141c40030004c7c0846402c0707880c16a082c0ca440071a002d600d84d8034001000e841144142c0c0803259190529007034000281c840509100032001c1119003 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 631678426 1250 631677176 631677191
    0x61e14120603120301090911031c0e06070204111315020d0f090e07080103020f010c02030c0904020a050303040609060210050702030a11011d0109020f01020d05191e050d060501030b030c04 82
    0x40d24000c1503031070f40524404000004254012107401c1609014045e86401c0b200702c1c0810103165480c0795540940b5038002816091016a070300c602c090148182000300b0071400c080c500e40010341154024141e030401150005400c2c200c0c0310000da10305000300b00881180d10312404042000c1e4a0708980b03154441000217a200c0d0180c1c2c54014800d080c09040111140e07140d900d00000701401880082c002a0b21800d804c60b0291180e43c46034006000c07581c0c0c00b5000c7c2001003060030030b21283d644090401c0340e00c042a4000071500e5201000580010021640e4071100d65150050203030a000a8642e61039145092904205546400004480b500403d070714052940e803075482d0b00c0500405076050b6801d10300340d4400c024107001c801500900c000c01c1c02110350410100b10340e8016680d48190b000640301168051200041c030760003040007030303141661030b00b0180b4450381750b00a06074044424008020104101240c09040790040e0700c11000038007402c2c01c003006040341010000c0d90312080074015a1060341c981c0350 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 631679676 1250 631678426 631678429
    0xf0d03090b031b0c010c111f0f0e0102030910050f1b07110301050c090102010e010204031a040611030a0f0c0f022a030d0f17041a1f061e141206 63
    0x4952082c1c0500106181c55403126268503000c6d0011040020000c0d50040d0b1561611501240c5c00c41c1107062110303c084420b1a4800c00b070068601001d80030070075075882000074110a400e0008503c10355600c03014101041c1480c40d040c0484102902d40c81c10708140c501040350b4500c992290020040700c242200f503c6118501d81680122041c16071950117500308030912103204c11100c003401e4810703400d0b0002c0c0541a0501c50305c03400c03030043d444090008411603400c0c900000e001816160050301809000c1030884040003241d030154030584d0300c0d03000300e03584021614940c220b600c128a2500a24901008481e0810700c0007550b401d0401c0503000c0c243d1030540d003004c1e0030b40d800b00c41d240000d001806030b568194016070041e0101c0c540c1030000020400707420a210312484102e103101d102e140c5c010304007070000301400040e880d076440003006610200c4841601080f030074011501403005054503551740c3c1700d03038501c51004050301c240c1c0a00341c0180200001e1b40c5509580320005e9503c14040c80200c031009a88400 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 631680926 1250 631679676 631679701
    0x9020f0f060706110406020106060503100312020f0601030b0406230f070e0d080304050106050d0c0308070f1b080706050a050909090a1a1b041503050604020f12060f0d03090b03 77
    0x160b000f0000f900c2c101d4996031151910010b442242c080340c0003000301580d608020341d018402262407004040280e141400000c02e1030f1188081001c1d40d20403900c03107601110038540740c83c41c01e0b0401e0b1420103440040104121040c0640302c00c07956030b03802d220340006030b1403030640c4505000740171ba08207102503c00040800d8030030b200790016a03000900161042d04941000184c9910545056030705500b054800b056070700b41507200741c50142d40a006d00c0b5200f031170b584602e0b1a6420100f8211186c910003001880801c031000b018880c04001101707007000f01c905e402c000c68a00705550340107405020062240308002904101a59049031050340d80f034081d43c2d50300c410142405035110008220540032414401c1c0000031001444c455000c05034110040c0d282008855014000c0744038101003102403914440500c0c4c841c0c0c0000d504104054800342c2805050390f01da03112600043c107400e07000c0401408110f1705103085004024120303000e41c0e10000c41c0030691801418a1010702412204240001c0400c6444c031440 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 631682176 1250 631680926 631680937
    0x91e0f090a180f1b080a08030a060e04050c10141c0219050a02010606020a080d15230f090c07020d0f0b01030c030b181e03040509070c140109020f0f06 66
    0x251055071446402d4038004003419964001900d443c094203010030403000d842100401951a440d00405400e00c03907035582001e0343d00090101070000c1d12500000ba100888005044c011442a409000c10b09001c1040c41841074802d82100c080001e20f04092240001450490780481e0490124408855040c019100a44107812840c8601c20366000301441c0d4a90100103000340407590360090011551315081281e40d04d1442d0405000d0700b0040081c05540c100c0c80c2e010b160704203411007600d45125502d40c0d41480d640200d0315400c0f03180c8240c803d40c8401c0d00d0700300f000f01e11501c82103494002c0b50420008504540c0160040240201e43d207000c100180f00e035400d8248401903202410903110740e12850f10044514180c40f00311192a8101c02290400344040320307018107940340c88000c203128a04688031726130040c0302c2d82081a450004000129490310342840c4c80c2d00c60300d28ac4c1c40358540009075103040c1c00760020000c8600c0440e40341c45909001030b603c450740c070030f144407088076402005090000000e03258480e0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 631683426 1250 631682176 631682201
    0x90603010b1201090b031032091612030c051e0a120c020123040302040501030b0f01081902091008010e0105090f01180b0406021905091e0f090a 63
    0x88000142519454020050702840c00400c24880c0d90399149034080c1c070100c00d0310a40c140c00003001c0c44003001c09a80942004140041c03d0000c0e55612480c0785002202030005000d804202c904000c0756035420061200c10019034101014800e250823040158254503403c02030400c41d15145840510404108003501c072154000058a4074601480c255962400d84004641c0c0071501c00940d00410301071051002010b40685441102e6104070a044801101c80700c6100d840e000c0030300001c000341e180da1083c140a184940c1c50a0001c2c1000101d0070300b4510140d01015031584201500b101e00142a40f080b80c0b216415900c0c0407440d22540c0368a802002d2542001c4801c2d8030300002e043c04131405421240c0591244410b40780d01c142c4600482d800c0c4e03507811885500c1c407801042080d00194103d405c1d20340c454025003006040c0002c82000d070007000504000070700040c0c80440e850303440e03282c801440c05c0c1611091001c800c50307030f6903880820103141e600345281e44680c420301c0c0081e201c0b1180d0f0700700080b035614 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 631684676 1250 631683426 631683439
    0x403030c1e02190303150f05040606030b0616020102010f11030402030c1507030e06190f0f11070512031917060603011503090609060c050a091a040b1b07030309170105280209 76
    0x440300789441e01c247c0d480c07107200c0c0f00d01c1c00d00340000344083c040e2040d10080840907225904d80b8a0031801440c0c9492001c01c1241150358600e070119042c055846012079204002c66002d40c0d909060040500c0c0150034007456110300030103c040b03840280e110049806490789820654481c5c955480025018051a102c811608401110661165a01c60301a190744c010315120702082d4800d44d40100c409140484250080342d0215030140700a00d800c4110600c90f501e900d00705d034a412840c84604e580502032150b11b4010814801110340041d64000074a81d0000c0f040d2181c03811980350400c21b02058036030441141c1859030360110f0030244202c0340c01000c645900820188141c0d18407800003801580b04882e2500040c80c1608081546c000010b0307540350b2241001e660b182403d040517104d000546c03044155201000a9038120319003840188241c100550080e02c6a8a94628144800043d0003040c40080d285074540410030180301c01d44128140309000346943c400c0030f030f58030192000081c07194030b000b00e038402c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 631685926 1250 631684676 631684679
    0x1221050103060f0509031605030d1406090117060406091104090c0611160506131502031806070309061425020114070506150d0602030403030c1e0219030315 68
    0x40542059048900c1a5000c02c41e4031a0707030700c1c50001c440055030702d80038a820801c49620780c05404c00d22000641d000f0001e90340341004188841045500f83d5581034031904680e81002443d2800d0511b50f070061104200d991004445400c0c125111103008000a08480e600d103503400a00098032030907008014082c00030440d2622a00780416070502c00e12031840028a984102042e43c48045450b00241c21905e100c00384260400701080415000040307000101c50f440203002400c4070070b4095030381d81421a070300034640e05d1041c0d01d540c260301c0e00c0310074001307002d040104416000207500c090072000f00c0d5224a485d503080d401d0885203810030300c41e4041864003201492200d0380204542f100785081d030341c03007602e5580041c1411101992903000720030025000350030150004010983c50b1900d0040b5010051002c150556640d1f12181280c005580641c000b03560744106c019110780020202110650502d00e403a0890981701000390b4030807956480f110400d4076082c41008044c040d410480d00e901113a92000c1649 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 631687176 1250 631685926 631685987
    0xe130b04031214040501051f0311030a021c05010b01170711030d06030302011a0d1221060602010b180108190204060503010903180f0501080402011d100509190602060412 74
    0x1c000684045d5030b554030b00360100b1505040c1d045200001004040003540f105d00d0f50300e40000320054901595011700501c504000140e0312405d07100b11680d02207070561000c5180d030030805c0c00c540c201306d412414010b8000d83e0724442c4555545490b40021185042c2503d640700615190070f60082c640c0400a4a0601101104141e019000340b540d140c9001c00b09010104e0880c204035041d03900200151000305181c001c80c1c03c8504c203517208400204c100404007100d18031100406e007111808c2d840500182d40d1242d01d04118580440364a0100c4008000b00b6015410041029100d15200514481c0340d40103a0b28181103443d40e810140050034014000c00203c081400d01400300b000705500966000c03072400c004540100c0c05c0880c8400c0c3ea0301070355800c855980d43d50045d602810178101c00e20790403078071108541d95590390301c90340081d07103d4a80d110740d20764003c3c0d011700c4804460301514a40500740400180961a40000c61070784c0941c00c181e45030051030b0000002c0e1403145419110030040c0c001003c0e020b010 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 631688426 1250 631687176 631687211
    0x3151409071802090901061b0c030c090e12160c09140f090d02120304031e180f05090a20030103030201020702010908061303031d0f160e130b040312 65
    0x302c42003030740240070364045480780204912403e100d00d07134080c02c40300050040e548148030080c040790140819000d040000c0e241d4440040e120b40c401c03a059000c4507002e2040c1c045502400410684950003411410b20f00040014035016080822418004854a58050180040d918001041c02000800880700203c100d03005542c011907442c1c05840c06140031607545040043d1070b0074074022550290055200640186005a01c0a0130960401002140c3e00289c01a079684404106845890329240c0d034602c04d43c03049490850307500c41245000000000c100a8450000066000110b450f000400c10b440d800090203058090f44200c00088022002004241e0158010244a4000d0300c81505407a50396041940c0d404040700c03c3d4000c4041d01c5000d000090080c1c0180820809060700386214a8240028031302d05142001030500f2580400c003200f000307504108000c0060180304101c140301d803408a0a480b46503410b400d005090464040000d4180340c854a1040400d0040702350501c034102140c20342121 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 631689676 1250 631688426 631688429
    0x110a060e100b150711040b040c0c020f0102010903082e0810060506030c0909070201020d141b03010f0b0d06030c06110c1e0103090507031202030307030e0c0a0315140907 74
    0x4103450b00804080714600008200341181c1c1c124400c6241c2891696040304c600761030490b898005450700316021140c0c5c1c0314003484180c65032070b945240400085004100907803c01c1041c10307040da4135100e070600110754032249440e4003003103100105082803519000009080c000340349001440701d2040002c900054041601c081e0020201024450319880e91b003000300310720007070f1100c200f08a0200501c00103420600c4e107541d44840c0a000050030110107400d0202541c0d9035001c0a031414121108110880b00407242c0c4d0100c00c3e1103108124115810099554101c500c030380901c52800c040401c517145c1301c400c10341001c4081c607481041a0085507030b583c00500902d40003008903240d4007650a151503c0c3c01c00c00b18400c1d807803612408046d0140403400042d802070150796015075180c050401c02001258040510609075140c03503008540e41e241c8140001d044030007101c40142507810021100d459a9501c5900c3d8040d290001c0c00c50b00000c0c07503d0301c28402010f05180350f2250000310340810428080c0440c0080 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 631690926 1250 631689676 631689703
    0x40f0b040807050102030a17040c08120705010f020a0f0c0606090f0902030c0f0f13090836010503040201030c021f0618090c5916110a060e 61
    0x40010f91520b006a80328040c1140300e20002e42c0b22000d01110407001505280c01c2030080408081d80c42d00d48240c0da09015900b00c10002c41400000c024007040782c248180c07851305046080440c180244180e004100c0c40840300c445040202030040d0300c082c40000c4c0e01c0b040c020541044108119038540070b450026003076159059120f4000c0240329845070400e0007602508400003032001c84100b100008100c0d024002a40c6082c115998074140303000100750800034262110722004100c288821034240e8089280a0420900603000e80382445280d031360000c0c196074000b0740c24240483c50554841d000c0389009620401e11540c07003c03010b14851960942e520003425120f1142401d0141c0b90180c001034140c416a4400514142c091a01040300c507581c100d441a0290b807007800c42817610304c4000f800c0c4141140840390310b480c511407a00441c60540c0d00140b40505908100160010f1615052a40000c2030003009030707040c001e0384803445105400920020034a16032013031007000000150081103665030508450117 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 631692176 1250 631690926 631690933
    0x1002071b0806040b0604020d11070c0f05030d090e042f030105010605091f0516030e040f050c070f060b030a0f05070b16060b011407111e01050a0c0503040f0b0408 71
    0x4903407020046005841581c02080d1400191101001e201c0254400c0400e8507840f07545500d10402c0c07400032801400128010390b04401018205a040038885620ba401035200c1da00c61a600390200e600844024200c4084070304004860f52142400c0e50111004a03c3c2c1f250380350040e03a8240811411404403403895020b8000f042281e132214029182440f0706030322554030000f05060202c091200c400303120280020742c070f08170303080441240101110645030003044020841485c500c0303000f810a480340c0c40710344440700d506000c241000c0112840714860303410094980c041da24100010b00c00d01c6e802a40d80c4450150803100c4800705400d002e041e41d1403000f0100e445d8026a603002a21a0741e0b178068454202c40388000706011406075481c94010320401140711b0502403070408000201c0c10010150030464080d0800d040c1c030394402001c004c0d03c030006a240c0004410f032089841c48590b070100a845002c0020b0034001c00d600028180240795002315440000309000d40d0b5004106203035054050000c071030144048 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 631693426 1250 631692176 631692179
    0x61204060f050a06080a0b133305191d0601140f0f0303030f07020708070f0e060d080904020a0306050d060917040503030712030f110a0906050f16051002071b 69
    0xa032013525101d20803444690b01014a54000c240300e28120380d00142c1814807034400720001e5895552200540400500c488810070a00d040383c40020194000a96440d0080000e40f0340710b00c4c56403503c40107100d40f64809940d018135500c540d00416081c05141d8180003262040c3d039540468400e450625502c09008449000341542e0340d0429444000004000502550a5960300715140c000488010035210031842011000111002c0034401c0308041d060484001c91160b00302403850040d0351001d4410350003001c08515842c04102c0c2d000944008100498001d42c0d2084200011000b8000703d41289901202e4400e41078100180e40e808014020301c0350034803070000074508180003103d00840c0314154041c0c008010340700010311298100008410103080c006607182c0c5485500b41107034010500e102e84400001603001405410120440041007940303022450014046100c4407240155408081000004c0110008200c2c5c1840740c80d25540400030219114491400c0007a101d0f8440c111054905160680 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 631694676 1250 631693426 631693441
    0x200604080a0e030601031101030509030d150f1d040201030b0a05032b080103030c06200a02150c0a0e040c02011116020117060303160203160902030105032e020702061204060f05 77
    0x10080c5c1200c0c3c2010306440c02080c44c0c0010742c00f43c01c0040101041c0e010810a9111000c41c610a0550b900000d08923807006505240c081e00710309004d034002c2041c081c91405130030080d421401c840750b80a44d080c40e0120b0000d60000100b410300255400c00c1e541401000780c0c0398265038034981c2007800b042403045101002c050402e41950361071028000940011040d00c0c803207020a00c5174100752920002400f8081d8030b43d44d5484041c0998000c40c2400005801000009004229900300c4d1500803c10203006071a000d0790240c007500f16014024028000c03521240c01d90000e0707000307501241d41d00140c1420039585102d4149031158040c0b00d13102c101d003c103c0f07040b804465000c035413048a1181c80080d009514102401100810340042a801240d041c4601030800c800d402103041410003d02028602617102e504040c10541050b1010034240011001004502c80b0030f070551801c544204418400180c1c3c44140b40041341c6039114030020780d90004c142d40240000c0000319030040350742460144040145803109a0f = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 631695926 1250 631694676 631694683
    0x4172b1b020609100e01030506010305270c061605060901150b0c010605060a0e030118021f0903080406050705010f15090209010201021209010504020a08070e07200604080a0e03 77
    0x482000500a106190420012040445001400209014140a07000300000d00f501130614038040010684640e00502c0d58041c0074854010b10300b402c06100615040142c04a070000700c0000f800030440c21181200521403c1c0200108200c010782015503442e024940d44003400088241101c03e03104410000e0329404042c80703040203d84240c0b130075458a40c600000f40d822500050460251556140e200140036034a200080c40c20311540c4c0c54408a01441e4820542110352140361075003809509032501c001642d80741c20100380d00e00e80300e83ca40740c03a101c1e00720200d80000003900000c162280c0068081040b40d0460043c081c05c5210320001d00c96030340e1045401e41522050024203030300b641d1614081c410180c2c04c0d00a04000c42d01880014100b9042c0e41030308810f0034060f510700d4801c2c5d41d1138040c0415420030200c000080d006100080002602d400230101c10321400400e04010803400ca5852492a903403c00024414100c4004656040c20207060401040d400704203141d001c9600311405240328180032 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 631697176 1250 631695926 631696003
    0x5070605280e040c050c010504061b0207050d020603091603060f050c0a0c11040f050c09040c0f020c040513020603040c0501030b0d081222050c150403260417 69
    0x2d90380c076100c0d44a10003d000c09000348210003010b04c4014072001022650910030544181d01681002c605240c0f00c01001c00a808e08001c44400c640004009000d41d48403c2044500d45506940d05a0307070382c0d500c601160608400803040003a90030400000400c1c42400c1d04042184480d4685c200b05688035050140d00b60700c00c0300c0f410000300b04100303503c07004a24202c02c1a220050060008202c00c52241117031400c50380222000c1050000105003018281441c3c8640d03440f0b60414104580c512a103068042c2da1003200f03038101c074412611900011136018070080254551507028110917100d040500d090703901c0301040d0080c140000d10f4122040c4071440c1c501500d07a403d03900600800c0c82d2520480e007003c640ea0f0020500a0a8100e40048206d090658001c1505680c01100540f0100c40d0117000c11040c02d8a0740034140c252542440709101040c4200036800d10441e1300411030a180d44510600702e42070203580e01c4548800507070b254203589204040707600310301c264040701e09400c0c0000c0f030030303035010071904c1c0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 631698426 1250 631697176 631697257
    0xe010806090f0f0c0c0a030507061104030209010e0402030309040f050f06060310302f10030e0109120c21080f09030d050a1406030d0806130905070605 66
    0x84089003080340c2610007107030020100b184140c5000042c00340c01d1b01c1c4c0103640104800041c40081c440b01403058902c10807605190b48000189014036603000203a00390b006001e0300702000c01640c003080440d5030402c01c603840c40102920501006080f181c201c0000c1804640c0c0381c07801901c070340004107c1c2c6003031000c4900c07554a45403000a224140812000305668034a0002d513050700100e8220710088180b4001c440b114451201d442d140c1c0203030030340401c0c80b000070ba40000126000e10b28400041c0d941051341c40101c0608c0c50001004941072242034050044004041c05c1505078144549140303038400440c4641c203014132912400b074030900c042600c0041e4448440070009030f071040070404c8a604c0781a4681c2140343e03441280d0601d04600f8100c1e00300c90040d42c0c403410f2555134a040711004503c444c41150710000071406403440444008000e0641c641c0240054803c6020b400200101d1380c0c142d0044030b016400000700c0e80310548606028003250b00c039032001d190414154800724911440320340030303000d210700 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 631699676 1250 631698426 631698451
    0xc010f05070f0c0806010315290f130506030f03032406070b091609020c06010e060117090c121c0c24050703060801090320030c0d0e01080609 62
    0x20004454940108000300c0b03586114208000c0403648801d4440040c2607020058021540b41d8a801c40c095040741592007010b90801280c4218075201960403400c10700904141700854001c08002001c940844108681c082803294002c81c40008a6000510648007130f4210761042940c091000e5a03800100e41565402144245e900031030340c942026815406009030500781404801e82e0740b8440d00d5021100080d40341d110b10702c6040d02d19428903241004080c0c66404624000080312040c1c1c84040c140500740303807196003002180c80b0340d205020b50f00c0550902c1215070721a0800d101c4d46030b00e4005070400c0d0385c428082220003e2000c00701040c090000c83c0105c19020340212070810565400300401401c4c0c41c880305600800081c40c14410342c0c503450002250300040c0c9490b00f601e01074110f075000e0f00841c045a14110104c0000794014221000400e00781020510710164000c00908c4c5200c0e0414150f0340d8000c000c40e0342242e40e0440c80150070508240c031000050790b948000c0c440d20000c1102e84815019 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 631700926 1250 631699676 631699697
    0x51512070b19020102191e09080d030507021f0203062403180c04021b0d0807090e0a0f090b19020715021606150f2120040f02090f030c01 60
    0x101c000c1031007484902c0303400054204800c41120803045001c01d075011020407080001c16188501d403e0203c841501e85043c2144180c0c07d086242d680c552080300c1c40c0050607924000301d02454003c01c00050218020f00066031514000001540a9041942c5150289000c100840803001031540c403240c84a500c54580e600b1507540c0f042550644001000c403040900502d84a403280d5101c1e40014003400640d808603405101d1805909403414030300c00c1450741000f8000782404220341d848000c0104071025840c2c5284980c89481301d440050001e1700081d860246480f040a0401c884e5152043c814481005100401d251310704561003030b40300d0341000614140041e480311490440d90703809002d110303a546003402031070310580c2c1d10031088070304103c9900c0c2c1c488240300003000b03a62540240d03100039008a91041c0189002c1e90300c0071400d40e92020000b450859942e8002410030980c000c403164040c0001c100340450b0f1440803031540203503c1408a280248003001d80d122132402c00060070f1811040c10b07990b804070319 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 631702176 1250 631700926 631700947
    0x204051012140103081207080405071205150103060501060206150a0b070f0210020c03102903101118040e0c130207060609050f060a03080a140d051512070b 68
    0x2180d070003140c0e284039603075901608442e02082c5085001e18030902c0c10340c0c1d0341c8084541005280f14001c01400411a1000400c8002100803600c00200d490020341104000b07047c3c030341030b401c1007000e0f480c4a034180180c0740000103114a03034005030b04803100ea0302500c400d41c17650204651007441039202250040041842040651120801003c0280c05034040b0303500c60702242d00084541c1c0224041d03100503802900592090325040c001519145180d170001c0110300d542d52a0001544c624414207101e2688607400409162014044100b00c01c0d443e040402c9184000031605019400103030550a81860742c00481100341410b00c92807070603d1031103000301000c00c0315808010b911f00445100300c0e0701580078414200020824003501000d021070500104541c64004c00d00d90821400529541c072a0072aa1001c0022035560011500c2d0001d661030704030480c0050714011692889240c009448583c03420b41004602d076002000866144401c0328121120b0038000c00056030340d501402110403a250820110880 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 631703426 1250 631702176 631702187
    0x1207060f0e01050f190f03150b1e2808091506040e120306040510050603150402040509160f02010b0616020406080a140f01140a05090f10020409050a02040510 69
    0x1605241082c6050040b8031040c41326041141c294042e4803066000182d81e60300014a041c1d0601c040c94100403000700701e912010a10317024492001c480c440001e0302c030b1040030150b405121100d001a0400c1e43c4146002d1040d107440480a45480d44200040343da41096100d56101805240f00328000c1c40d000501580501c001344003e031819034040e40d54604c902140500317120105075955810b40441d1130389001801c0c801901e0000340207880d4008030307000c2801030742e03030700c4c4185c80d00034041807580c1009084160101e0003c2c800c540140358000c405008114903415600b1012250401c0c6668542c08074410b0300040e8280c4001851082d0302142c1440041d401941040d544441e0600043c0041a960b580d903017520304022442e80705513285001d251580c1c46502e03042101d000c000b05040003c0207560b0003480e012400040c0508590f5402c0d4a89000c1480b44400300004030443d8040c5054030354510801300b00e04001e41c018814254203d00704400100c80004034400e54045450141115203035980036101203c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 631704676 1250 631703426 631703447
    0x306141f0210050a0213080d08040f1103010207140118050d0c0303090818010207140109050f030a1a06040b090609060d0327091107023003070b061207060f 68
    0x4520850300b40c0b0110030850f015690080c01c0742200140e58410304104000da6624940113907600340d000764100603070315a0002d0050f9101d90409170b0050b580c02146000300450501c3c01700c4991560000c9003900a0140220905000d83c0015000b013140c00c2e011400e09a102100c1003001c0d1075a0004036240e4041805001041000b503ca80f500181007401d607074a04519030407221040c0c03000d044024040c0c20a580401004010744a182404500b9540d18030009043d0002c038041c840c000e0b028940008100c2d1010011420941d50280324515041008480d51518a80484000d882141000d0407902039040080c281801060302030400e441e1070fa54401031088080003254101c0400c030450005a40e0b0b2001011090b03410001c1c0c2d140f03442010311307010401043d1000e204038275100c0b00d8204025401a600c200e44042182c0000f8801c0c40322286005401e09086145090005107000019550003084129044c0e58420807085030300745d4194010000c2c040c1c0e40c4502d4003a50703022505983d0103c2106001c0d102444 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 631705926 1250 631704676 631704739
    0xe040c031b122909010e0903090411190201051005100e06071b0602070504050a0203070f0c0201030e031c05010b0a0f180518040b0a11040504090204150312030614 71
    0x7454464030b000b0749081c078410030145080d0145a5a00043ca80b4100d141c0d01d006000400b51510300f8181014007a0702c82c85500511403180e0703a2031540781850f110400a8131039050101040c65000e582c90304001e4040c0104886035110b65041e03042c0070070385144c10f05103151011455660000e44042c1481440030035403042c003080d907121400019100c0410652245e01c0c004d0714440d8050911140341c20140015110060308402d1018010b0081050b82a03010004031009142890030030a80005c03400168028244052048261f00000910203020306559040141c07600d000c0d00204000c0e1f0343c40900f101940120881040007522441404200764410220150706010504550110710340d03030400121101038590a941c1101c00640030481406210711145034070403038000080c030415680020711280d80c891802028400c40c0c5e600551403c1d502e59a000301d00341c01e903400618507032686034104516800b590100b41ca00003800c3c01c0d00400c00c4a1200f6070003c6804d0050906801008103e1400c1c0076400c9404454 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 631707176 1250 631705926 631705931
    0x30a0c0f2a02030102030103050a12030218130603051605010e06040e01331106090a0305030624030a09020310060e01090203042111010c08090a0b0c07050d0e040c031b12 74
    0xa07000350341d0a03c0154000c500c5030005162006c168580b200b4030b840742040000605105003c1740c3d2110f101010255103808084550280e070f02060003514005140541000e06607100303d000c0c282490a17080d480c84281c0710300341c80c0c1450210100701001094481c0e4010700e41684000c0004000d001140c00c00b000c11030301086d810180f40c0c1c240240302e1041103000e40c1c034840002c02c0521901403d503414880581c00210080c060802d030a500e0b00c3c05009484003810480c002c00c850802c1e181141c2c1c407184c045007000403845d100d40d640c2c04d05140e60006021150001ea11a0007810128200c0a03c14800c440403142c2608040346942e01e0020800000d4000600584540369034002001294a890080c040c6444040d1210b030b035110b01c0d55003070b90300b11010140c4d160b05004651050081480703000944ca00c0d941c0d400301d042c00a40d51107a2050345c01d8014800300030250301c1948100c9117040d410412041500009070790030081040c0441048094842d228603035140744161040f2a1050782c0300342161603905240a102 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 631708426 1250 631707176 631707257
    0x1b120a12020102121e220501060b040302330a0309060f150b07020f040b040e0607030203071d0d11031204121a040201051602010e090c030a0c0f 63
    0x14004035030400650080142d5002480b140000201d0600030382000b2211001c3c8a00c41d908030580003445005082e03500c2141c420303014802c5113000015904072081d4041c000340b280c1c0c0e5a941040b900c0350000d0104a02c0b45441c840c031121050b14544240d41061315180344c44103c01e000d029141580d600c02c00010b030030161910445008500300d8020000003071501800010b01421140d81c3c031298030611381281200302e00801c44500543d1b0344c40c12100440f00b08440004070794010400181c001c25451030f50300300c40d00031041001038003901903020b0f510130b4889031500c28500001240d00c0404c080710191460b800f03061198940007040c180140d84444400181c01caa2000301000c1c2d51403901e0700a41d10003d4a04000700c90340040004807030200c2201444440038052a00301940080c040d80542c0208038490112102d40000303581c07040012114000c00505844060700b03100340d801940350302c1107620b114a00c1c1018510592988101c1401149200580e514010140c211120969210081303a5109121044048 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 631709676 1250 631708426 631708433
    0x20403080415022e0f02070209040f030f02060403050403080c16090603020315040c030b1909061a0a0605041502100c02060108250506071a0f090f1b120a 67
    0x500180c4480c031050001c0030980c02c4003c0c9000060b40c102d65104045140790801c1c1820030080100031010b000300840c4c1c803c04551300030020b009010001e0340c40398900c4248800d000207181c21103032290090f61a0b0310011649081070f640c9400c1076400a0014a00308420000b2806410107451004c440c0b10541ea16814291288904603055411000241d075480c4020811031800304820385c41600c035442c080f01ca6150540740d15520f000301b0310000e80080e00410020303003c605228980e18a00c10318241c2042070502608000004084000c0503103e203d040c881900014601220f4007022200940d40c0c030f03864a82840c00b5000f0501ca20740e40c510640c803c07010340b4004000640141c1d43c5105059009200381d41c03404a4251038034480310340440d60000305d407508051300c80a510b400000c0d22810389205986c0c0e1028a407410840d12060300060101d880d001c18051054452115203004116501c22141000c00d42c1c40da00d62103100c0e041e00c032f485541070343e43c0c00105400d00240c500c4031444800103589000c2d20039103 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 631710926 1250 631709676 631709693
    0x2060c0307030b09010f4b0f0321080f0c0c0a08280804110609060706050916170316050a200405130f06051f060210050901140c0904020403 61
    0x204440030b20800c6d0743c3c041c00360740e240b425400b0314440b9440803514105148500b10780030850455507152903204a01700e0000300c440300008000144000c0060b064619900e041003440265202042044402e90081c42c100c2c4c10f10452f0300d1401110302c548405100e885080d07100d0840da2018030040305a00501c0c40c80d4000c107070f40344041d0034606440c50081429010189203082114484501c28081c4802c0a0501022a241011000700c241040d94503590380c850a0000620301d000d6081c0c0103146500b00304c10495521030108400c3c41f00c0c006580382e0410152204081c001d2070070300c13410300c20080d8810f01c6124a20358050050404480c080c4050b0350704029140c6854440028800015071084e00e4500d0028040c1031502c9030f6a80803c6070440030541d880b0305d41e58134034960030307a04001d0003e9441d0340104861f0010403148241c400f0191203848841c60703403000c0180d1a000c8161120041528150000d96020410700131000083d01c40d50311601c0d1942c2e44a48420b064000071f041e5500260300b800080000317400711 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 631712176 1250 631710926 631710929
    0x12011e030506151f020a0b0601140f0304060f11090406050618130207080f04030c050a0308030f07020c031e070512070b1c050703141f05010507110307030308041b030302060c0307030b0901 82
    0x80d805042c07061061f0825000e40600501541d040020701d03951101c8140c1c00f0010b07510007000c2c1c1c032441c641d00c1d1200d0605801600211040c13040051404c1c2c907040881d41088014a44038a007907c052005990710340800c2228059042009071a000c508030001c0c0d2840c001c01d10601f9401c2c8601c0060800103e41c5a07403140d9007100c4e2020013041000a024001e011049082100400d022600151014259542c2c0302ca18003020381031004240c000400b141c00704c0d00038404030b1074038240a01142c041d00c401b41f810f81a1000381ca120b003074980c018400003041508005004503440000d01d4020810640b800340c4898059001c0d100011303025012858462403251723a4003840b0300842d0190341c0403452440b841c00c40815a074004d040041002c1d204184c04404092410411044500c00d09090703444210b00d0610b828588100c0100716894041c01202200b01500075103003078002c40c01481c410b01094110075281d42001068003018026a03c0000024003204484000b194806442e00d00403d40300c4240c80405c151030700071f = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 631713426 1250 631712176 631712239
    0x20d05070314100605250203060403021011090f01140f040f0e160905090712090602340f0305070501090f02011d09040813080312011e03050615 63
    0xb00c1060900100c0d0380810541c00c9a025a1402151407800d1006401e51240f403508200405800319501d18078a424441c1d008025000b40075944545030a141c02902c690011f00355803556807a000080645a2407401950b200200140c506900b1103c200010b4900080e41c10502c854030808002e4901d40360a0f01c80580024055582a50403990074406500d0f0259001058400c2040f0201026041241e0003080c1008490b42562114010389490708215101285281d40750782d25410a901d10b4104803844c1c0c000c100488541810854101c48003003461204500051030f952800042c0d888480070031a1f41e00d10080c010300c241401c078940403455035000d007521081c044c16280384507001c0800d0290f5800c00300d550341c1840c08110705859010f2180001c1c03259000900301034884040030403403040c0901e00030101e201411584040b246c4a011031007901d401c80c03509000307050362a2403506524003401c1e08020314000341c070f40c040c0182400e581c40651013644032440340d4005902101d0810f60b4140c880c409035004d00507110 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 631714676 1250 631713426 631713431
    0x121c02030d1a011d0a0503030c07150203090102060109051003170c0c04050129072f100f0c03090e01060210050105060c1f0b040c0507020415080309060d020d050703 72
    0xa050701503411156200c11040041018485030120b80c0c1c4c1c4500c000d50700e50303600f11803c43c8030320030903001c102644190f40003150103101c0010a41580440042e07103034100c2d09921a2a1818185204103d03100d00841e811940580e0050005010710161a08060750040c02c001a00940f6a9252540101490780c907025840600001600c03030303551003051041701e29880d002c0d182072150354506a58035140d21140a60608134000051038540f102030a102250581030b004460500d40c0071018100c80302003102407004890300380101100101605184143d039011807000d0321182d9000c0c0c482001640e012030305d028101c04000d106107001c100b0000008415003e05000d43c02020004134040c405021110180c0056224100030302030b1101d105030019000a00000c010008402e4200c01d83c00100034152504c00f10364041c0c1801f0001aa055010b00030784a0706000b160140581240c0640840008096000d0a41150801c203d0a1500e0420000410f402160080014035281e00d1409000850300c0070364401c0c1c0001d8 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 631715926 1250 631714676 631714687
    0x2d06040b0d0e0a03021b0105090901241e031a04090c210803070e011103040b030f0604090302120a0c140616080c030601080c09031c020d0c11121c0203 66
    0x20040d1203100031920b403000003000c4008007a00e0180d9140300301944080481403450041c800c503480703201500c800e00c41c050942907113035031a070940111903401c8010306040410315000e00546907100e003403245000303d80100300f00180701c00c9410890241c51040c0c0c14144500002000c400c2075140c0b803103070041041c000c2000011860030103400c029055480308050008040d082004130101d20700104698102c42241420940c046201005039100070088105411600000c1400250300307007040025442107450541c400d125999180800044508421020340180c2c0308440b5401c0d180060030007814982180c0c1050310303010031560740389046003010490003102504024203202d901050600c0022885800c0d0910901c2483d01e42011190b6010090402d410411401c000c1414043c5290840da01144082e00703680380303018003500808100c024482c51000510800e04c049100e24031540c04082d02d50780c040c400d030704507a0320320040020551111031481c0d030a000b4070307081140320124218803094030141034011f5511403 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 631717176 1250 631715926 631715947
    0x1815090d060f11070804140d0f03260c190509060a090806061503070c080d0f0b010e060306030a030302090f09040507030c0b030105010818012d060909022d06040b 71
    0x140e058000c0e40c400043d041c04003a00280040d003c0d10152044201450740d83c04442001a010110b181c0000c0c0c026011150078a0030705611444083e9a0345e011120400c0c450640e00d440b032951041180c075208000c0040c0720000b01c480f41c88500c0d0f60081042c0c500f441c108000b13240025810b13800034040700041a03181204100410003030200f43e500c55405c503904001140d40b01600045071100405180400030030440c16410040d446042c0c074203540c0035290402c03019103480100d400600340341848501040b0151609206458501c04881c0310303010142c0508154507040d5820760180d00000049a400f8100c07070615001ea440300c0d0b40742403196010b0001440641e01d107041c44511007aa41d0080b400b544030800c010b01c49660012805034201444c442c00316040300c000c1e90307150300500c041400c003807001d00a49002e00c4656900ca449d0080c801c0540d200f0070107a60703100840341c11100b028070000e40080040c0480354100045020105420100180100300250100008bd9407540550805c450303284001c500015103 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 631718426 1250 631717176 631717181
    0x901060e0906040503070f0c12030e0f0f0a09091a090102030103120507050619090b0f0105030c040515010e0d141c08190e16080d11031815090d060f 65
    0x80701500010b0b01583c1082d880c0c0c25101d128000001c0c156850303440c0c5520801c40340408281c000c0209922015200b400c07407500802500229030a02e00c2020404100f0340507181080e4590f200e500000c011a40144c40c1c445010041c1c808901c050701c815940c4000d0045203982d00070340707e01c03030b1141c4000103941e0341c1189030802409607255509400c000d0203125a0000840000d01c641d003004043c00f1001c0e103040b04481ca440a4401000e0007071404400d5821700c070142a01fa1041070580340704400b80c0c1c0101a2440c24401110801c036403165203003ca44849070865401350585080201c0c025080b0788100c0000e440311071070080701c58040803807a84002180700c482e0303800181401c1403200c10310b803d40441c1030170800300c0d01e00400400d200c0711540e0384d1004c00c146c490041104182d1120701040c2c801079070b171b80c03866540e8a84209900c60004901400901703506644080121402c00161800200c3c1011301b0b80b06001103001e08800700c039810b42c0e040060b003149030f4403094030401d05072040340041076030070340c0382c80340c10a = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 631719676 1250 631718426 631718431
    0x32004091413170d0f06241202090604080d05040501030b060c0606010e040b04151502010608030304030f02150c0304050708010c1403040c1a030412090f0314070b030901060e 76
    0x221070066205000d018403001085280060300111903865450004180501502c81c0b0603004a91354903004024107412420703000501100c21401ca003410803045181c04e82d0f4460071280807800045c3e00c1e200e000140d0303c041d60181101d941d0103002241015150007515141c00c80f40640c00011840200d400c01003982e00d801a0301140006031946410045007800c52a40c5034009040700741800f1100c5501d40d0581c44681c844c83c00800001e00c14032860140c1c040c00311700c507401e600030041c000260703041c1c0c003d55a005000301e1080b41d0414000314a1607403542c4040780e0031900c0a111204600503010b00c5510b007a422101d039030160642400e080d030303a17080c145841490a05aa80310702940d0f41480f143c249419040f0b011401d58441d51903003150759a81f1440c1001280714140c1102e4500c2c0340b02502d14407610b61100185128a00c00c204041010700c102200307449968081c4111040d002c040d05041c80000d8000041d1418040c0d00421101000d0f241d6400400c03070b4008071000122603543c0c0341c04001080d07030b01282a4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 631720926 1250 631719676 631719701
    0xd140304051008180705060405310204090510050a0e04030504081209010f0809060c0c0f0d030b011b11060d022a0c09060d0210020f0f010f060b13140103200409 70
    0x809103281c00c003c101c7c01c0c0507501c1014421410041034102d040d0407040c201c4440c83c5590400301e000002c018081000f90001d008076444545440000740c0041c9014200c03400341c402c0240b03844101c5251203911034401c0c000400840820105100005030040b041200031040d00450041585a54140d4001414054074001c2c43d01004001307001d1080104000c00c200b034000c8000c0d8100c45c0e94204880005d840c01c0c2c4007000c5580503100792080c002d0000d41c5544001c1d45002c00741d0360030705010802d0341310105d0198031050250040451141a401a00d4150b004105030710750082c000d03007841905c07001000881000881c0e00c99805008a0018400d4414070540101000c1203403c0e6619017815004200030100c2820024001c10058003c4145503008003e040001c0c8004801c54210281485207203001e0701c61101440052820070b01d001c1071101c513542c152034541c00005011001036103401030310f800783c03924041d04c0d60604d80e03913850025850b2401500740b07080e2100d2072461945c6030301d082d41c0041103908101421 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 631722176 1250 631720926 631720933
    0x10909020f09040b06090a0207020a080d0318030806010c0f0f0302060702010c02030c2805070909050106060c020303190e18041403210405070b1809010501020c0d14030405100818 78
    0x800104078595140d0802c000784c0b006d48207941d0302c6040400911074060045d52104084900081100002551a0500c0041c0e50140001c0d1001c02c40f11000043c0c800004000c100310000050003548610646c8800c5802441003c031000f0041c0c42c0d003807042d4803180c8250010b03081001081880d03030f024020501d85042c0c0703100451070a60109010b54039000f071130740503014405c000c4d11072109600c50315400d418282c0c0c110003950002c60343ea80c83c5400520000070116032035400c1c10742c00210140142d005000c41c0e07801901451070406009034568000d108400003009020740000c1c100b00646800f0b820400540c4e007a40c1d403907901d00b018209054040380c100c041400c180e208004c0210580d040f2071180a015810440340c5450307031214a4014180040d40d0040a000e02000ca51070510040c1030802c000343d540b05642d00c3d02c680e40c0391001240c448289101e45a0055481c40b42c860000e180040c2c14000d2601120070b81c0d00381600d4400092181a5a426040000e441c0c401440144094407040484240d40c0c00b004 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 631723426 1250 631722176 631722181
    0x2091216030312150608041401050708010608060411040b09090108011b1d0916030c0f0e0f031e0609191a0c0c0f06010f0608090604081c05010909020f09 67
    0x1010365005040c0801000c010070f9945109a00c0e02d9034000d001013590081182c8401c545405005100389070494094035001c10740b80c42c00041450620a5038020480ea03030303620301d05030b08101c016181014003074112600180e40d40c0e0b02c074501c600704402401c041d01c9176090f0190f880b4124001c021800806821915242c7d00d80740b030b42075400646042c01c9481d5903c074140940103204c510307032010303260a207050318076007001606007000340140c00e50490308030b5036215850800a060820408aa00040c070340d4034200420402c070140321a81c501f0f0f4982480390740b001070440d02c0040e44142e1100000e110342c18045066445030041c03050204081c000080d03103281070643c2e100f0025103602c4035021401602442d030743c2c21804201045407440c6803001c850b2007041490031186104c00080071a0380e075400034030488505007540303603000c2000342c803801c9114001c4000342e0042c1415103958442e15202e40c004140103160080030406802c042e001030145900a00441000144100a0340140011528401c6005218a650608 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 631724676 1250 631723426 631723453
    0x90603040f03051e04090c031401060e13021201080606011115040309030b070207090c0e011d06070f0615090219030e07082a0105090a0b07170a03020912 67
    0x6990340140c000c280c560744920507040503103032407052488440c2100d0078464184800c00d102c0004008581c0030b900204070040c042c80c01201122614805021301014075001004118410700c1c00020f200c4008108c0a107500c1e1701c0100030220f900002e1040d034050b40d007070010401003200380a0694002c50138204507546408480045465001c01807000c0918a240c05c08601410b20540148026590142a912040c03c00040107035031099144180111113003412440d40e8410320071100c80e4040c500c1038545016610901c1c061b0752580c0464040150130150521984020561a074400d8150305c1c02908001540ca0601d1030f00004c0c90030b10b801240344640104684000b407030004510924410f480c1ca000a08a1907010006080c1a4076074051005486080806107003400c081d07441c0902030006014140d516401d200040d20035008003407121b40c1c84405910100300a814038401883c0d12845030192800c03247c1d0048452410b60803c0b50f500d400030f9804140e03407600381010301c0200e010341081c2c40144990070300d000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 631725926 1250 631724676 631724689
    0x6120f03181305040b0a020f040e090c0307090b0303070f050f01110a120b01140a020a06050c1b0a081e04030206040902071a0439060c030206100b0a050c0f100c110309 73
    0x900c0180c0495000501c80e600f0231800055402405141c0b100c8140303401c000e010965a00110655a48a4003a02c0800204014103108650340000041c004c0d60504485444a13030901140100542e96030080c0d98450308004000c0c80781030306180d01e0040060b2103294030310300200b00c004040c45c80c4410a00d8000380c0c1072240e030050401c141a2101340f4200d650342c049404100d04044c0c40800003010f590a2000384140b0b400c0e224003511025121140361204c801c5103103c2544d0f108038504001d000500104501158262071841130612400e0350a0080e00d4255650b022481591155100c82452503000c0780100401c074440e065045100f00c8400681800d0a150300c9050000d215403050140c02c400724095042d104081141c0444000c0180c07581c0f031509a0b90740400b500d11301d1501000c50041c02441e0000e41016000e00c02601941c444001c4c007418200c6c60901912950301034200440144100400f04440d20001c100030040140c0840020842c00c2100303001511020f030781e0004a105401c1032010070b216450384c0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 631727176 1250 631725926 631725931
    0x1080d0509030c15160c21110d02120604060c030e0d170a090f060203041202150a0504021f0905010f030b01050f160b01030507080c1806120f03181305040b 68
    0x41302e15051503407480940d5030141c440d034101e08200f207201226490500250303050754411981743d044c103c2d03801c001184840c0858410040000c20701c074668181848142408510010310520141c41035440c030741000010b0389070031000c071412640c3c0743c2c0300e0758039544069060140d40070b080740b00d800a01c034034040003001030000304c015090402d204045000080441480c0c0d041070344c2c0550400b074401154203860030a54080d40c002c450134bc64091110314a060b5440c070004c3c40044e2115016a6020785841b50103148014000180080ea40803690314070400c0701145c2130000ea456030485869616405160400240511880030a004240b61403e030078851240d8105003225109051200120b0b501d0400d100e070a03126031113500f03003d0a050880382c0040308020001450700141c5000d41c04440440028004104450f14031380049143c010030400461780e01e05151003603152448810f0280d5400041e442c03002403458000d0f803640d80d040c64214a10811508120980030b40c5c4c00d411010034011803919858890024402 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 631728426 1250 631727176 631727179
    0x105010c020d060618150506030606030412171e011406040e0603210a1b020d03050702010309120306030b0105030d0f08150306010609030b06030c011b0302010f0501060801080d0509030c 81
    0x20482d199080107584d901603809410411012a01d44803410500b40041c901d020004040e200c034076101240358034000c401d82e4401d0000070700c240d00e10796035542c6101c8a40c807030b00c0740f140c01e101c085210540e625005602403446094001301c80001040c5107080b40c64a10010b920055846403009200c0c48192100000c84095a4800d001c00046485600100c3d180c440090003c0540d901d000e44195104080e4100802210b003260781c890011034403901c0d21030008400d0050084d13003c2038114108001038090030151000900505002410b50603a13190421100c080046690002c0e030b40300024810130050000481c05000183d00414021001203000750403984c11654440c14440170400103405000c00140c2c14002e0300019041d2580f80d40d40c3c00018155948902046510904040000d038050400149102d180c1c2c205070361b0101c3e440a141d800385141004000305034215501c51404110f00d80460107602e009162035901e90885615040e4a1420806a0328070002045800c00c0101c10790b9500080e0560320910 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 631729676 1250 631728426 631728439
    0x150c03100303320c1b06030621030a0504060206010e06031f090204061701060b03240d0515010e0109020c0a2405190506010801061d041d0a0507050109030b0c03100b0415170105010c02 80
    0xe85d840309c400e41c081074198031058400000c00d44002e5504c4000381044480d140c0031502c0903625071100c40f426400032606180c1580c01840702c00c55104003480c0c0b10707900e4a01c500c40017840700020b4003c64160b87c07980d0418204411204a1068514001d2054400809820710780e00d045003410441184100755000704820355844411b0300c22690340e90701100c1c052007640711080355112a41d41c000c80030643d07400d100300d00740260074600000710a00540200c4100594060241c25058025a07030140c0d17501e1140002d2078000300c10036803000d1003a07161090071301803144802c8403906106a1140d00301610b50040801c0d04020845004001d403c0c0c01640250588803030404606144114402003030080054031034030f90a200c00810580d000d6500811000b1403a4091303825280290380350401035452908904c0000c04c00114500050030604140c4080d541229544006a260b00d540381c006889580190f042050204034140003500e031035030417109511103425101a20740b0550b16290018103654503c01003e4041e02 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 631730926 1250 631729676 631729699
    0x1a090d08061311120403090f030305120c130303033e030c190309030e0303031b0d09050106060f08060a060507060b030a0b010602150c03100303320c1b060306 69
    0x2619600406444212103d80d0303502c88080c2e040541c000398080c5c400b0f40c041500710790007080c4009102000400d403501030f11000e1034442c81c03100440c8044001040d1400030a001e0002800800702ca4040000070f5000e5600480e03e5584245008403000015000040042809000b4514140701150303100710175003050030540e16030b91080c0307400c8454401c80c1c2004001e4030000c42400c0d0501d40503440007070354901a640b04e001e260040c06c180342d41c0303110944543c9106041030088281c0c100001c0c0041c0280c00904501040e801c4455441d2420f42d0055041140414021128098180c1d888070020394809421118240c903d40313016030241c0103100b014405840c2c5034450046850544003002103080c0e07550f200148044540c0c0d5648029100c4a441080c90483c1c0001001b042c8104d0158068034014400208924030141c41e40d0742c20b0b10b14400715004251002c510305c9103a410390826882c044000c000c0c01084075070b140d000000d00c60030714034540c241d08090100c500d42030109440b000706884c0d1001058892a180a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 631732176 1250 631730926 631730959
    0x110307300617100509060a0b0303130803030105011209031d04091a1602060f070f1707020105061813320a02101412040c050d1a090d0806 60
    0x160038460030240d0540c24a140000d101100c071900754400450041941ca00511003250002695016200c004d0b007a4800c01c0403030030404883e4049001d0342d030000c0490386803032203021070b41c10010216032100c006600302000400c89943c1060030003103040c0c4400d0382082900c000307a40c0a130000c0c0009117100d180c65107841d010042030b121b5600031512103801280c1200c614042031009000c5000441d4080c50300c1c45900365101285000007116802802c88115200075a65021406c444028000e403440040050081c918021810f40350748071781c0170b204030f80e0010a0603d025011300241d5404143c030306480b10002005c007c50038207101e1002c048141d2140d10b101d10342c080b021014000009a102d0001c0320701c0f40020700411050b0000d42ea030302c928801c1e0707071104038454100e4098aa080750500002210344003041601400c640303850030310f07600c00d10980060312040d440d6400b2036000744000b941203658207007080303c4035080f4040000b40c0341c2c0040360b10024080e003d95060b00a04101e03028218602940c0705140c016000c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 631733426 1250 631732176 631732247
    0x601090315020f2701020d03060b031504090b01080c030d0f12051b040824010b0301060f05040e0403020d03380a082d0d0509130905030309030c01110307 67
    0xe1480740700610036004c00a0444a5800143c1001c1030141c41000d240d46c3d8560b02a000390001ca60b8520304190466555001055044032001c03a0a84d1240e62504440b0009004080d01c601809520004282a4251805247c5040c1205075074a05110072002400a406e521100c00c05401261820210700c50701c50340300c40d14050507001010010441c011130081602034002072542c404e00702050b0700c1c402c0e1078011080018920350a004005294408100621840d4028000400b0007220707807401514040d9500c4414171821019501100103810503186c40e082e440d03242c003448903403000079005031f41061600206c080468100310280b8441100018840c105903039480c500307800803c480400d0342d019607031002d8190b42081d040b02c0303240012145500c0e00390b0406000510f801050b006c0e51111841c00140704100080d03074403a449c1d400780180c5c6405c40c510006505001860040004000941d1240c00e648945820b480046450844024003401042842540510b606d40030b04540c485c034002851241a01091 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 631734676 1250 631733426 631733437
    0x40b060a272310050304080304081c020304121d010c05031210031407060f030b1f0f030b0d0218073006090216140a05150103020103050601090315020f 66
    0x20700c12140c4001810502c0d112403070021800450140000c46506000c200203204100c1c06200092014400940003501010007980c00501400b096418040f0030341154045134561804010301980200601080000d070140d03c05224080c0e0803c5541100c1520308515840081d0841c2410440a000b01006019041c030444941d10103440800346640f424141111100c51035100803103044000050760302d032002001c07410605a031225a10f085014002000440141001400c003d60203c00c0074103941110741c5a4014850404054544041881c50b010006d4221201d1581e1035008140b00e00078140160384e00102c00380071362081140d1007016211814122003031204038908205464086410400348d160b03491200d007c04d80300100500c14140c85590704001da01840320703a104010a40b03c4143c0000c1d041105401d80d42480d0422110340c02d146481c4c8510740304e44500c0541c010b400b03080040c415075a240c0034103603200c1c20a08085403801c1c50740d500d00421804070f24400548a602054418000445804440 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 631735926 1250 631734676 631734737
    0x60b01260a0e01150f080304030507090c120203310201200c121510060203090d14011503060b0f0d030e041805030d0f060b1c18140c040b060a 62
    0x81071004d8038221031200c1c0d4601800c810010180c000150001000003201c0980e076001c00034040389454800103402401c2001d81400074400c0240c0d4040c11b0030303442c1c405184a034940c01014003c02c0c81d01c084880c191148200c030403010158101c3d6050150f40c200140020040b05400c40c20040079030012114184a00f0044059000c607503ca4403a00c859400220b0824070a000406c14045440b440c2d205ea0010950b1700c11000075030800e0003010118600304000c043c81d2806503403e040c2c1c0c0418210000d08540d440002d2445056840d9000e005000c0f251082ca0201d88088d00c9260321f084034000016119506800e00070200081e02d9440d814603200c503048440a10740141e04120300180502d040d54a0382c000d00c00d54000d692400d030001c3d600e0400c074090178048a4100981600d0424075070f4540a0020341042d070101c0482d1a480c4040d400c1c1130308624808014000d820b4911041e051000795402c003141030030702501c01c03800c20314980b81a543c2d850403260001040e04041c2005041440b1091a0484000410 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 631737176 1250 631735926 631735931
    0xe0c0f1207031406090601030c1e21150c05040b0f04080601150e1005041703130305010605150310050904030c0209041209122328060b01260a0e01 64
    0x42040c0c61002c0e503c00104141600d50a41d100c40405503104024032001e40006c1014004001041310301c0d0700c00c1900c1c0c201c101c01ea1029074a852038010710003140174034054460848040d80081c0150240700c1e1140304950340091003c01941e98008010307010320701481402e0540000d02500c240e8140c0304840042605005580c010740c0d48540400144890401e10701c04141d5000c6070741d125192a41941c1c901740040d03128181014203054070503010080711211199188001c0102011100049028100171403181f400458000c0c1064207001c0c01300510003912000341c40604c240141300540d00060429640155103030701e06580c603424111541c107503150000c0d42190b959800d00c01413083c045120741b00b100d100e465090220395240c100c00581c0092400c0546281c004d0130f1001034041c607520822501201080c112100101c40d1002035075803200c044803405e240d07914230320240104501d034007540b000d1450909142c0348a0940e13043c0d0030f0079034000305510060450035000045066850354028100703000d80030004c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 631738426 1250 631737176 631737179
    0x50307020304030b010f140603070906050d1404140d0503191e020a080a05070903020d14010e1603060b0607020d02040b0105130b07020906090408070b0c161a01090e0c0f1207 76
    0x2034911185147c005d160b54a000190300092078100101240d0290700380da5100b000e40744c60070744100d5442e000340d85003c4500e510390740c0341066031130760300c41c240d0150b8060000c21a100302c000300c1d8503103003001c0c0705110028000b0078010400041138010f40d404900024010205545c804220a40141c1614040c40b2071510300c045682c035026640507074201c3c42501104000c010300d4032492030503208c2d0f031701c24407000f58032000c0205403200280d000d4500c03000c2049600c00100300328504444041c148660703660100c1503407006407000c006014490152002a1000f55000391a04c0400c0d000304000340c2c41240701901581e15036134503a0f00c692140d801c0350340540031881a42411500c41c074151101f6400004103900c140403050209940d45080041680143e5005210078582410350ba0781b243d00c400c004040c603400000520080000800501c511200d9912500c3d0382260111000340c0c041d8042c2068002c00b848070700d402c10007800030900140454145400b02d1b90500710400d0703580020841008284c1090ba40d01400c10f0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 631739676 1250 631738426 631738439
    0xe0601150f0c12031b030e070b0f0c030f03151503130c09060f0503120f12070507021804200a14030c030304090204211a0a020721111507050307020304030b01 69
    0x4800b00a5851004400b80d20325000c0e02141607c8404010100300d0300500c104003d040300e0f40c4010000300303030441043d905295130030502c2821a040707081d502000410010820003c1030000d5207a0381800c10813101034086109030604414280002010590450700403001117041c0115424400e00500d21038805012054a50010701041090b40c030450340a48103441c0010005038110060b60400610714410301c2c10586034002c1e041010b00081c02c150244502000760744050f80300d40301003400c0c40140700200b9200b03041902e00002d2882c6815403162030303841e0004180c0200c1d0745a0829034201e55205650085000d19980001d080c00c02880b1541c0d8503110001c0c0c00280b088090300988211403600310720400035515016180b4003589501c800400342248002d601d900d00440c11086604400e511030014107000d6185d8a50307181584020140059284c41c5900c084010b5128801501041801010301684040c0302d20254501c180034182c101442808000102e8191003082900d0003103411920350840c0d56540c88 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 631740926 1250 631739676 631739681
    0x1240c020909190507090c0206090c0607080c07030317090307031418180403140c0c0103020a0306210c12050a420b1509100e0301090507090e0601150f0c1203 69
    0x104801c440c40c201442c0010b8103001044013440ae8030110054a1043c480e041013048a601c005001c0b55000b030107210858a140003004000c016611940b15010198803600495803200d000500c4190310341d02c01c2000d40002a404030750004022000005540c6038262920020110542004843c1c0c100315404102c04802070b64180f958007541c040c0d2559120240f4404600c851481500d15580081d880741c1c0001c0303c04e5200f47d0040c662031665140001d440c6441c0c02140c2030058040700350881c10034035203501c40107000c00c40c4402001000c03400050220f00c00c055a4142e1102061003001d0f00c19040f0a001407220f401c0840381130f4444070380700e54801500484c00c4078040e074120300c42e0001c50481c5c07500d2001c220908010400710310f0442100306441c1442d04107000c000704d00360b296110504000e00340c3d100d1030385c43d2000d002c0c21016910400141140906001d0310404a0b18140e002401550100c40100206102022680c0482c25a803600043d040c034106000e840400415000418035038002c0030130580642d259 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 631742176 1250 631740926 631740929
    0xd0609060e01150314010b040c03150816170c1c0512090a0e061f0c0201021603170f120a060e1006020706110c0604090501240c020909190507 62
    0x2903104201c60000e1940080c00c95191038004404221203e40901c0411039044007041007078014800030584200030030124043c2d600f960058004682c94404280500b0040c16001003c0c0410300020700103480d0082c03103100d101d0300071300c075004d800c0a852600203002c1d841805842e28021000d0482e8940350010034404414507001c0c1402e865600413106c810495051355030841e02040c0009201c46e02060a01150382c42211018192551024014449000303803900c0804048040f803054540c849114100d000290810285041c40344204507002c0382800000d0380c05030513212200101142c15241c05a19004002e0391103116900c0d12241d140d44200200a000e940102081d95a24000500151140f45032852100307170320301a000158210803800e118451141c1c44c05885410f00c00c0c11200e9104e6214042101a4060741003000d005455100521a180650a407543d01c982440f070320255070640f5000040800c090944002e2003640014007003420714004100300403c07150310b007508098515a07407502d20303a01d4540703 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 631743426 1250 631742176 631742183
    0x10914061302060306131d0f0d0e15090d060915110a0806091509360d0804020d1e0b0a0606090521070902030103031b0f1502090d0609 59
    0x1910002020412024071014140d80e000d0102419a143c035010040032214030764882c4040c039900c035a038021a04480c42004450014940505080c1044130364060030500c500c64680140715542901440580781da150103a40c400380d000b4556140d0810b5400221821080c00024205600f001641000e000f03401d522490200c4070351030200300071a040205d159590003070000c5007001c01c44007000a4200c0c1403011003940c4c0030700d0319108446035074802c00000750400d00070380c0c602c083c40106c084500c038240d403074646c124001c0602e84a440d2060200500f455070752943c5858100400c0078140100d0219155004c206007190750000d0078421030410105441c181080142003035031807541c080701040e100940780c0324210981d400d5940344200f4500f8036090109641e02800411101c680390200100f4004003889904040c002c1084050790320b500d5800d005000103900d11280342c01c41d082c540903000141d050400400c0c00b036030124144407180114081c80c802405510501504200300b01460f0041100c3c0e03500149880e8030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 631744676 1250 631743426 631743433
    0x6030212060901051c05011e020301171219020709090302010b1009080c010302031e070807080106053108070914011d040b0901091709090a0e0303070e01090503010914 73
    0x1d5030010041c800c076080c442d90f0341281c0344440107a200343d820b00420400e103004400102c0c00c505094203041141d8200c4031000c4070b00e130307010005025483c01140403400720201e0000134802c0b000c00b9101c41100f0b108840c8c3d403501e0b9003402c2ca1040115402805010010f001100c0100015074403410301034044c0400034140e910440d0020080ca82c494021800340040e940311200501d001448000150000c0d40b001d003401c40d04081c8400303074110490342503031420b1190031255107821180c1007003840034241420681089092040500402203291a0a032014403203400c500d0b032505100000b030400501c0000303103412003a01401502004a40d480c125084140401e02c01074440d21943e82e2802051040e442210f8268205141e400120340410750310541190414003c900001d000c2516aa079003414000100c2e07203a40c1010041030b040014034040344065842000010140821710f602a496074492100500741001d00003000101c0303400380d226020b108068400500204004112420302076088411032088244170710 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 631745926 1250 631744676 631744681
    0xa05030414060423070e1509010812160206070b0a2c03031501090f080705011713170f1303050106060f0203070828030f1a0901090f11030106030212 65
    0x1040082d1540c4103070b81010300c80951a29040d500e2100200c0402d04502c148210700c07000c00e00c02d283c0c640982c01001d031020140d2a01c51403100740038504005a002c5180e94100b8400c2e2544442c0c0402252030b0100d10303400303480000c5924030005403e40142c000c00b9080d100703a0000c0154881060303110719100042600d01c4d81d0355044403001c1003403c0d449080b0001c1c0700d070028004140141c945090880700f5003414181380411035211307030802c1c0c6088002d41c45190b15074010007042080756000803100400c2e407000b4490048a19000d456001804000e08004100141c00c01c21118440c03c0792081e600c82c0384410903000d603114010200c1e20381400503404107588a52030130100081e494025545102e07a000c00740c003d582003034201c3d1940e0449801542290b42448007001c034607010369284556904901c90305840009c2c90304048a00141100d01400c00c3d140252180c0b07050b445c00c1d40e10003840310304503200040d0201d40032403115082000340c2440840603446400c08000414410340580203058500d82d201c20010846c0d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 631747176 1250 631745926 631745963
    0x4110901051c0b0a09150c031103370629121501030209090109020d0e0c0a0506030a1803050a0f1b140c09010914130b06010c03030b060a050304 63
    0x6142c550b1003228240001401d80014a94401d4039a000b440c002d00010440c801d901e0308982c00100c0c0c5100c6420355507955614240c0c90b0180305004403801140302e881d007145007070150b0500c010842d41c4401d8800c905923420102c500e1800d03031410000b000030b201c103021b45a903401d940140700640f10351424550b51000301001c980c240902c02c1d1450071601100c0328029071181d80e40310940c04030410240b81015000c0101100c1c0b6190300c64514000c1c4414000140c0e202d809072516402c6904040e0800c0d4280c00c0b48601c4000c0d56110f04a06040e62011203170790355a9150380340d03404001c0202d400b45121200d003201e0030784180340c1c02c217028000040050711125209408160210ba60546545084081c004030030180c1c030114000140000740d086405080301d070017803024030006100341401d038070120700643c6407250f0012844e1810029604240541b85402164020340e0b0f80b0003010000401150401c82140c0c80e5005042c07003500111204007010f450140e0342d8507134050061007a40103c5041e0703010241610f00342102c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 631748426 1250 631747176 631747189
    0x50909090c120d11060f070f140307080108010b100e0402090a0819031101050405070314100f02040503010b03070503061b041809140d0c03180e0108031809100b0f0c060411090105 78
    0x580c442c00c2c145042c1307594203e02234450b000035000840801c0960204a01d08442420046020380c826450b812040d40c5000f00c800d080d2820004080c5c050780c02c1c03036168841c0036007050f503e04440004940250302c500a4002041d20000c02d40c3c030550b0719210703c1c040c0c07008111611200035851030280e42c450340741c802002ca506083e1081607a00038221b60001a0070070100346169a0041502d91075030076120307025804120b4106940700c0c080d540329581c0e0700003002c0281c3c1c5001d00c41d02446031000e60141060600d030030300181d1900781c000c0181e2500b4581c04110820300c0c040204540103000214004070b650000640c00300c005001444003196080004e0718580d040c0c4400080702d4511902c160b407801240b41d2540e404642900300c520280c0900305420f000031400098185003075028207205801140c480600c011451002079828400900810040040c000490100b03c14001030b0742100c00e00d141e03260f604901200e0035105810140c1158006c00c4103010801148000b22582c82004440306101c698883e01000316 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 631749676 1250 631748426 631748431
    0xc030201030b0d15020717120f090a0312090602090d050c0f0418110f0a080c090a110d0234120201020319150308040308130e010501050909090c120d1106 67
    0x2001d40c2050b49580080e0051700248106485040790405d0669142907401c0340707800141e1240d001780c104004103d803880740038411541c819105e1001340702021140d1805418100d903540012011a1200e20036400d008454040b62400c01028000b4100c06506007082511605c4240180d88900b0b03c5070078a0b600f80c80c2a010300741d48400c1c042901c030405045680d0b02224200211846034200500c0341030040159103001d090002880c664005d0309012251074100a508100180071141c05898880040d61f840c00300c1b0280c0300c2002c00640010f903110180703e480d114040007900d8400e03041d50294076044e296403a094a40071124411040c0e10340700104184144c5c01e0340001c0f600c2a44640b94102150441c01142d00a06010020650344484058483e200d0440c641d206400c183c400f00c00004801c0d42c820f0580d03001400822122060f81641d50420b03000230194850007108511a10111004c2145040280300e203142c0090010048018081c0c1c8000c5c4988030a440794070356003c10071048041504103000300c4c0151 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 631750926 1250 631749676 631749683
    0xe091c031406011d031603020f0a1d07120f2307050a051c02040b030f01061b022701140406050411030a090305070b1003060b0102030705060f1803070c030201030b0d 72
    0x10720340d288401102c14001d5044520709902c6580844c241c1c0d514140109a4412604d000c101c10560941c014403000c1920b0105041c040c08001c40204000b10a000304441c03103103180c420714000c50b2218402100c5203c40912440005450054442901d00300b0b036000411554002180ca01c5541290b60409040c1008554040100303c1c2004240d074154860320051025119900e10040000050a01c100498025402440500200000b40300d041441140c800e401452140350010400c651102d01740e03c060f0070410001e0040c103d2805201c820460700c1100500d284440d010074045694a5079441890b4410603541801585031130300106050074035000e400c1c0851010f4031761610b9910340c90750b454000c2140c03140c00e03010480e050003c20005145819007502a40c624004c000301d442c21402d100d0300b100d690108041c195481001210300040340825280c0d0301000000c5220102e039941c82c02500b802a070541d44003914000042d40100700324a4a6075a0180c900030b9a0810260846005000d900104514040d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 631752176 1250 631750926 631750961
    0x7080a02071203020f0d051608090d0e040504110d0b010f0b091c02010201022703010c0f0f2a0f050c0409080f0f0405060415080601180608100e091c03 66
    0x2c0c4121402500102002020451003603e48009400c0e5a41100c0080e61a0300c1080d01010181c40b1160f8402d881070b403c610792202070444002404400340c1042201600280280d845800181c00e100728200303409e04400018007a0007815000d890140440442402075642501480d040414450f220406898203080d01074240140e038aa07910045203180041042281159001c101c032030441e642c15245690030400c1108118a90040c0304100b40c29245000091420000e400c001e4036100c40c4e114103091070030020344c204003e040740c507038940d580381848142441c0c10090f50540c92808206501c040c5504890080040d11645034100d4100000d0712241c46000d0000c1c0818004140c1d2200884d00421000b061030720345a140c260b84101140c4550899840300c035092070300358a41001150040d603000d50028003442c0144000c3c021480841c4203021b20700810382080039517400102d8040700c038880c030006030480c01098603681c581841d03421b54840d4484501e1003032001144200c01d10034000d0064142608218041 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 631753426 1250 631752176 631752203
    0x70503150a0207080c0607030b01050f040611010b0303030711011a0120100c09140d0b1621090515060303030708070203130e0105210709051b0307030507080a0207 71
    0x480d022480c0988404492942004000c0000300048010217501e00c11102500d914034000c140035044916501c0d00030305001040051100020301a0210fa0903260380c3c1c2811030200c11282840c5d03005010105c40c60390188000018411032a0b040300030140320681c510003d20041045204c0c0d01c0c2e000041ca035825022480700207005105e2403407100c0b49400b404501048401e4811020007030030607100c1c1e80c1c0c1c00354013207410307035105020900042c021062036140c1519060508100c2c0e03980c4250a11004115248225000e01a094224450341c548503020342e2044800c2408042034071100010140440102d805200b00c440d26100c40b107210181d907206500060155046660b90b10044e0b0391400700030701c43d00c1140810882c4008144102031704501070b20b180040102e442d0704040a203d80000c0b00341e0311082e00310104403545080240041c450080d95800740300405d01c0c1d180c010388180c1c043c0c080d100791005407401104202e101075141d8082c51003003001d82c1d00c2d0a01c54980d41c0d41c1004901c504000a481341420444 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 631754676 1250 631753426 631753453
    0x43306080102040f0b03070c051c1d0a092004090e070f03030c023001060602060a09021c050c0627010512040605040321020c0c0a0815040f060203070c03020609070503 73
    0xb856001f01181048104400c81d41d40f1981410408005400000001c1d12540d464a600101d035460311850380d0040840200d2000000c2c5524181e4414500142c1d29006010f000c21404440c52000c0581c80340c000e6195911540d210018040ac02c03840051440b810320001550705030b540008003207e4042d214901e4120301902442210b0318609003042c10101090000c0f0448840c841e45070900000c503a000040c050f06100c80241050800760110003014100a45c0d00c002d81e4a0020b80d041e1080c03490940c43c88614a0700c1d00c070382000586400710790310001c0880c85050842a510010910080d60360b031441407040f01100640c0e860203070b40c0b40c03840c0e40130110000400040300342e441a0f030014001d0501501c1c04004e4450414010b14500031200c0654012881d0440d042c004c02c9204e144020484502c02940d0070104000e03503e8120310182811000c5201c085414040081540034140f40c02600566503841c02c080b0240000301140000c41c018440d000005a02e00d8020601c1800c0d04c80080142c00d02961048 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 631755926 1250 631754676 631754699
    0x21b100c030513171303030509010909050127060803030c0a0f02030313060c020a0506100e061824030a061b0309051b0111010507020c010f030c1205043306080102040f 73
    0x707410781c44550100840418017403851440b00c019031103661030f241da40d131407140010700c03207500c50f03000801d09400d00c0c0051142a81d803160885280408100403402c0014000106002c3c100c0344e8881c85441c04000706001e0740115060041844050036210240d00ca0240d04e4226a60b12045810b410203520003c9000009141030f008400046040c1c4100c405068580e25a20f09109050790030090100c0401e0701005003a134130f80b056580c0904101c403e441c3d82110300703000a0300d0140017805520000c016415030b240046a171241e500c408200542101c04c40401894920001c102034509903040030349095600705424480d01034240c1440d80400a01441e11038026800075001004600300d052080c1c861021034403002c01d10410340b0607d00c0780d00810301001d40000144c185441e242040d0100b40c10b00314940002500031000d0300440e584ca42c8006502e81e50360800b900d6094190758248150070042c42c4005e21030304880b18001481e03521400810600d81d90f607540d03600300d00c118400c0f212500e065540400c4101c1d80e40 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 631757176 1250 631755926 631755953
    0xe06070302150c030105041103010b180307080a0605070e040509121606050a1505010513050d0f06020307030b040b0303091f09080f0a1217130501021b100c030513 71
    0x900445549030900d000c20428500c00b1511405034a9012004211602d4123025a820203009015101d142d541004880455071294060014109840d400074030070644040144800400c03160045e640d10823081d01c2c00001911094035010005500d07150f410000349802e201301c80c0942c081c8001003020011251040300c1c182c1004221800c2964190500408a05c1c2400f4030b0f4862580b80500081100010f072072065000c1745074001504202c0144003c421040d034903060b00c400da80d812110300003441020700c2c20312030300d05144d40001d010034008400e0100041e05038010ae040399400b145e050118840b6941410350300c0c0184000c141c2d02403484281c00b10401040701c5400c524900500d85900307540d072140c0e4454980140681404150390003840000f050002c0181c41c042070041525100402e14210802000848005051520101c481c0d06507003003004401d6044820142c0d0851444088480500400340c540c1d200e800b80b56012820031440b50051403280c03141921522007950000000d40850303c1c1c41d202203411 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 631758426 1250 631757176 631757183
    0x14120c1005070c06030207080322060c0509011d0112050c0903121c1406120a0c06020106050112050915040c0e0a1e0501052206051503160801060e0607 66
    0x400000a640351115406048a0605a2a4150b40d0409071410b4120812160f01c40c104052050060b8400204110104d80d0000900c41c1043d503000030030903005c0180e400224009040031710f807082641205801c4000741c401d60209881d4130210400181c42c50b65003202c413034100b034000f070a00d011620031605140c2c0720a4100c281d084501d400c0c100003c000c00e140c40d1058494040300324001c03c104074407150b002c00000301809040c10074402011050010201078602400e018424119504040043c410400006055540090420700e0039607031088041e00074022401001c2c000b0b04c000308481003148107400340b24020f94000c0e006003403450041e118001c4290003e8030880701201c454800003503201c130003071800d80a94040b600000c1e04c1403000d103200e0303003064100b00180042c0d81814010019503440c20201c070350050f1806a0203840300b2542251400600c1c5a8018a50048085404880c144070580146200702c40c1014808400c060700c0406a07144502403007400c00060000410b403006081000150035078912 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 631759676 1250 631758426 631758433
    0x14090124030e03220b0a02030a0503060d0209010e0603010e0c1e010210020a0e040e1c030b0402070503040e090f031215010306090e0d09050d151505030f01020a030b0103061412 77
    0x2c1c40310300c040c00c41e80000d00d041c00d1488203903500c05040384a424110010460890041d01e481031044000c3d40f00d0084402840c203100c0080f000900b00c2e12044001381030a540103102c0780d900d41e19144000a03804080e9a0710b40250b1070b01e0401c907181e8a00141101143e080102100c541046401c1519540740021510904500840300c1140c0d4034074840c0040c017009a02521503070354108006060100f150300405d00341005611840303080700300010714405204e001d1441c0c81c02203140c03980c00000c03402a10900700000c02070b01c00000c001400814a60340280100382440c02d030f4004064441c0031070360b280245e003480c090840d011404200c0d403010f0075041d851807100c18100451040d075a07100c03a1085800700c1122681c81c1e006600e24849882c2d1114070380300684003c403441c0e080d421150321001604072002c070401002c03980d591112603620040010210080c10024201e80740403860303800c5903020750844501c08021904101a289c100d41c007034041c5000b0ba03040c07540c0c540e661054410800c401c450441d14034040340d00 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 631760926 1250 631759676 631759691
    0x20901230702220c0f0f180b07050f01050606040e13020f060705010b0f03030406021009020a030219031106090607030e130c0e09010f050303190207090c091409012403 73
    0x85940307841985007000307034030150f0030740c440d0300380300381c20b0761216401d0400b004044040d0410058211402d507079181c009203000068040d6a103025015055603400501880c4001700f81542002000903240c00340e00a103200910003500c0c1c607010b004150040d802854500340201000a10715000007941010141c00284861004800400450303070340c2e070202c1404d41d40f59446403800001030400300f0441070703c8203003a8000d6141900d465030080d1581c83d0301e61007042c0107031100c035403400750342c0c4400406016540084c81e400d6200303806002c00005503861f100440c0c3c0401c100011507102d203891802d440e0000d07005814030349450f0865404035064075625070b41c144d2001c141014040000e506208001c80314a445e1956012214501c00304008c9170816030140c000c0e403010301b4040c801d54401109844912001c2c4400ea40500b2000c182030381001030903040585030780c2c5040c0320704c01c2d15a40001200b0803a82509540b4490103188814868811b0090040c5180c101041000c0f4440c1e2500320441200d0247d181307000650340 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 631762176 1250 631760926 631760929
    0x70c0311070909151404020625440306060f1207031d0106120b0c0d0c39082a060702010e0601030b070c0c090f091104020901230702 58
    0x1c0341120001d543e40d9a0894280d40e140c80ca612403110319514008108030981b40175400600319205030b402c140303400a0b400d081d4140c603ca920260780c444a60004e0014020b10700390307000380040e251541461142140d1411003400c030902120404820010f455111131665440d502480510b0340103054090700300c18108040082c442d00345000b503010b600c003650f01281303000603109005070225542030056500d034501070003042034210700c1003580700d615407002c1107100720341d0707001080701d2503006440100301c0c00c80c00c2039910020b081d4810180d0350201180c410109640b003280316283c6081c0441503440c0d5201140283c100007182c0d2503c06000150f1150f007000c803050559210082200240309040291940b00d181807284e066020f001e804115080007000340b0140d85503480362181c603035000d420501400808a001001d20100c6460040603249401c0c0070701061000075030a2004001c800ca094400100742041c00d60705240c14001c440e650081692003908007802d400103119a0070030003038908410b010410000700107 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 631763426 1250 631762176 631762181
    0x30218030f01060e01300611070b01180c0503070311041206020d06080f07060c02011206030506270c060906070506010b07110609090a05181606090e070c03110709 71
    0xa41c0820400803d00c2440c1c81c0c044038440a0603000422540c5c1c402c0d5501d0031145140c065034582c01c04507078009020090358149000288540010031840c001c00113031100c01d11410254150489482c484d0800d01001c1c015003450490380e80c000c1081c0040d00410224160920039040b0000c10344200c036142e858aa80c0340c2c81d0f0b44400e4070400c800c4074480e40105110031540340502c100c0008190320030291510300034200b103140e01c500744e600901060042c100401c1d0300703591203846038481403203146a00304442500c900b011680c2c1d441c119001460f0711120110010035501003014140240f40c10030040040002c58030403c5100d400c913101503034101400f401000042081080701b60b008161f4410096034a400c9420203030011144450054002c0c1820000698151194924194890340074400054243c0795241d0080300303c98604401a035038031031091240d81488158001d0800c1703c0c040e803203442a0503510114850300001c12554a0007160744000e420340031a000341003502c2054110001d407041c2c1502c1d01c547c0713001c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 631764676 1250 631763426 631763443
    0x4020609010f09182004060c020d080d110309010b0f1012110f0306030d080910091505040803070906030b0303040302040c140c071502010b0a03120908100e12070f0303021803 76
    0x1320588840c0c0d001008448000816501c42402c3c3c00a8506410414003408031ba00400009000d94103598618003400b042d0410360319000d880039024085d1454030b8140c03500b82d0f0000e84216615520384183c0003607d1070108050309011401603c4888100e021030004d6820b50584908003c08688902008000180e410002c10000c0030340c017601c0c0e45a040a6017494500316005034980c040c0304150080c8541250000b07805400c4960f203a1002c2480c1d542d5180c6001d031081d0424080c5241400d15091208019074140951304c900c4855507802d40c0d1a036a01c808a0a4a858420325a0560401c01c024009410039812050110244cc204022040792030500032030b061f8400822030a06070000c10051010000100c619000c603203541c402803010a19007c00190210716920004111499160340c0a2010740a20441d4004008223416148642060003082000e03115022280c01d040c041c2c030035040c1e280d1003240d094070a007e030004c1c2c1c0f03d00c09a46540c3d040e8004e50003140e00d0420104060360381001507408115449 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 631765926 1250 631764676 631764719
    0x5040f020d06090c08010b180d1109090d110325060b0a0e062e030e01110a0302070203100525022d070f06140f0906280804020609010f09 60
    0x758501003c07030010714125047c0c11013454910200448280b00d403e40c14400150001210b0031400c590f02c038509050002c00503000c25411191080421800500101c1c507500310309a95215040c000410030207854403441281040d0008807202c0c5486c40701030400b640460b01031403280000043c5100b580c1c000a00400107544400c40984110041081d80e00f403100740f9140000c501d00c010880c500314641800aa2041c86806200700766603840c0d1032060007000d4001e8404440803504040e134030814000e00030040d42c0b20311000d034028800c3c03528039000b20010f07104540c42060b0b03034030000c2c0040c9185500020310304070381c500c51400c5200d16199000d50040c6110400d103480700c180007581c103e5070f60380350140c1092401c0c0c0c4030343c4600301c070400108642504041200e1010b0180d1001c01d690705c9810014600da4000c49001c540c01c440b01040c840c00c101612820402c0c1100c1c141d00d4030960100c8032504a400684c100c0f4000e4003d04244403203600303540100451411103244d410894205512003640b0f507500c000100401 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 631767176 1250 631765926 631765931
    0x603040b150301090c0608070c080a0302040602070e0f0c0705011e05090c10020304050d05030c071403060a020403080d0207021807030c0f020c0d030e15160303060b070c05040f020d0609 81
    0x5607808281c10760320a408402d038003c0c052510b1603120045036450620444091110f50400904150300c07803280c224925031f00507003060315800300c408003c000b904a4003840b0054440c248010407408907038110140706080404180d8026a24551a001c80c2d4102d08801c071402e640301c00031b190020b140d11034140d12002c00014001765a146c6100c8103442e0644400c2e5150042c04184084800103178080100e4050341c80c156040c03016402c1901d021851849828038405050207083c40100d505407031040c0040c01203008404031001925007403000d404920541c0700041c044032042000c4109450300d5000f5010580c0014100e40326005201c0c905080c0c0c4a080720008000b07035890100e51030407500000510003c560510003012503040d9040407500a0725035140c05001d0040d090307840f40f91036481440b6180c1c901403c1082945031203e100702015407625045040380460b00701500854090f031601c082d544459000903510b240d80d8544011300008044c0c64403540c03800381d0208286400005c0701d014820051840b903200 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 631768426 1250 631767176 631767181
    0x312020c0c150c12090f03010e03070506071704150603051501091514211606020706030c020a0312062c0702030f0d1a0a1e080706020316110603040b 65
    0x1000030000003030b12200010803052020460041d03000411401c1c82904511050340d0320304020008102c40c20480303216500d50308040491000c000040094000307030788101d00321205911201c10036200010803034240700c400101e070340000b0701281159014044d0590aa10300192490b01c035100e0604121102281090000c4444010070813a440344c443c00700000c0c04881800811400c02c2004040461744070400f600c03a4002c0401d03054440088070300036009034140d50031603620707400618403201408000e100d043c01500840c400006e410b8002c2c001d00c8041303007041d8054000c0c41c590350b6080da0070081620341d01501a036501d2000c140c5581140038040a8068800c13084074003600321001440703c41000740030104541040c41107801820945042e10091152004041420907042d0040520013080d24242ca9204210100000d200c1140d40d01c5100003000604500c6855601e40f000c05030b503454188a14070060b84100030400b000d0042a1510781424416a0703903081c068134850000b04540c03c2510107456840c0d0b14000e = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 631769676 1250 631768426 631768429
    0x1e03120f0f1204030212030c0a031505061902010b1509280602011409010603110d06110a050306030d0c030906030b06040b040e09100504020a1a0910112e090312020c0c 73
    0x508504a032a1b00c40c490b2843c85c142d6044821402650001001d15440d829100c507030071302c07012411011b094017502190f140d41e040a620902058001c000c10090352810070f90b050181032540600b009440289580c6141608107014020517400c150a59070071503101080e240e0032480d07007455940c001d1032160300201e102c84071490085d8000002800d4000540e24180d02040001d0720840000c3e80c0700000c0b1040e150901c00e60401c20054070303505090150103003000407d409200d030820082d6016030340c140c003206c0d0721500d490419250000b41030b8000c1e0204441d610100a074604c281c0001100ca0b0010381080c1c04c0035074403401d00800d23411a412001201c07a62000304a903c040030462a2380c40e1201901c10302a60416030003190b4865228051561075164415916802e25103280803200c00036000740c1368101d05041c5040007001d00719400116800c6000c2d4a01184040c84410900d642c1c0103011034054000035020501880105038020080b020301440c10340c148101c41d450f10241400340e03001d074040c1c540601b001d030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 631770926 1250 631769676 631769683
    0x80d1b02010e0c0f1005040b12040b0a0209090a020a030e0f1b0616151d0109052512021f03060e07090b0d0b040f090804051e03120f0f12040302 63
    0x204041c90a512043e6406059034494101060740201551305415040c070214080314075224035004031101d010000761000700d84290008152282e4010001c81d860364954000e1f800580c401c00344019440b1021402003050680c0e03641c000c1c00c01900e1400c0000d0203010b003407030043c00d000e0110011440c64102031080e043d01c803864800300381010381c1201d0083c6049128040d90040c42000c00b8003608000108030342d2003482d0030b0f5920485100c00703500305012561001034507860180c11410401ca486004500c66090b5144881e62441888414007507105105400d00ca1621390010300413606a91201341036140e000d88008460102403d400182d0340441d00c1400c11500c440c035000050107a80c10440442420080d0a80007030075194003000c003940c003003079410790342c1e0026000d400d000900003445860300c07404a003004407280c001c0086440130b584881043e1342c481501d0804202c000c99030354164005803602c0400c445200010802403105103040d504140660b03114440a4101c2031400d05850b4008090009064040 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 631772176 1250 631770926 631770941
    0x130e010f050708190f0e031b160b0904060b3004150c140d06051e15030c0c011406030c040623030312040c0e0c09010801050d080d1b0201 60
    0x146051040e400d140000410440c80141596034410004034010380c61402034000c0d290450195a085c0191000c6c0c403c8a600c0e1f80c010354a09649a15151080030b182d034022502500f520382039109c07484924a00f6201042940c031042075903500668074503000c9501003c400c083d0083d40c003040309181003032001092221506100c04040c2c07100d03a99240030000060415984c609001980da407002c01c88401c04441560340c2185481303168424180800c009070009a56031002048030f20031607034040c901c10062004d40301c04882c1c800c100c0d0440c021100f000080c0d06080d00a5400c0720f02d040d80380303280004401503d0308658010000f160882540e00c02e04c405450100300c0ca40a00d00110750400800d45441440c0308a40051840c1b10061400040d240450340e401344252072800c8002c0d1165801403070b092405488488103400703074111988140d0003050155100f00181d419034901a110401941d083c241040001d8102201c01c440361641040a100c07003001d14098803407110540c0c00080c0000d4800c0c040030f82540c404 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 631773426 1250 631772176 631772201
    0x613030b010f12020103020c1603050609190f110a0902040b07061b0f08091e011b090e0106030f021903060311010c110f01051b070f05040501080c0909010b130e01 71
    0xc00c8043c4000c9499900d985841e41c0e090800580d5a00f107040d280341055018a83c00c0900108000000180000440c80f0b6114804843c1990655818401b00c000c071000c44138805030140c40c00125031f20000341156122400d0304d0008008005036130342c50030518281c0c1c1c0a60410030002c04041801010400d550041c3c281801c60001c603440d0300041068020140340180c42e8a00400c21807030045000034009122411811189151030201c21400c0e84031540608501010861140da8013005a42d40034402c002000940785041000601d59203005c000314050415220300c0c82032141d080050000e080c0710307040e881034103802546001c1070b039524506004419103440b041c1c490522141540410000d00700c0c200380341c17295a0071100c080c0c0400d021700040b43c0901903d00d03466201c01044c24002c140003c001410412145925020000c0ca40c03034005110039200302b8401c8030b246074804189004549002900c040d40012140c000044002c51100040c0316521503806568040340c1d180b0a101c0c80d15020702820869190 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 631774676 1250 631773426 631773449
    0x50a060504030b061323040b13020a0608060312190f030b0a05012d170a020406050a0e0111071d01090c05120903070b1612060b0919050613030b01 64
    0x556143d6503a140030060559100700c0c1040192240d00e8050350151801c010505001c407008103902c60070700032800d0143c1b410b95200c3d0411000984a8411005103c9450350141c004554145040310655010030040d000e140d243c00380d0244454078640c0000900140c00c2c01c00c0000c0041c000b041e40242070020381c8a281400c040c280703503407003000b601d403100300004603802880c0c90070740081d002c542c07600318419014006004800c28800c03030f203c06034808519202d24414440f000c074161216180031089108074131503000070038001d01003592180e010f038101c0c800c204010b04000b0400000d56151500b44611900207407640c180c0940710042e4401e1944070700c0e01400c0906000c1050380e11080c006400c0e8010742c461002a600c00300c000610182c000d1003541c0c1807540c030603400c20080c10881d004a40e068040345861000800d541c60800c0001a1030003200c04460000340c1440ca0000740c3d4091001c840789900742d86958070390a0200180c40e49648006154a4100e92050b00e402d40c250302c0d20111180042e44819110309 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 631775926 1250 631774676 631774679
    0x30806040e030f07060b060408030306210c04050612010609020c1908030f071806080f0a0c1d150c010501141e1c060c0c0201020607020118060c02190c050a060504 71
    0xd00001160002c0f102c0502c02910f90040303141c408040e003004401d850300008042000201158000050f50140e00202c6e8168800d61200c00901000d10480c1c1003110039520000705805142403c1c0d12041d00840050700c0c018280740055003080c2900d00a91100c0c8071940c0c0000c0014103060240150400040c05001d509411142501c80c1000c40c0005017014808440480101d040280145021800803d50b100b20784540c565480c8080c0080307000f110035945682135400090400c1071284600c00740740c262500c5507000ca0500e03010b800b01691098038501d4011510503602c13110b90910102900e05e00f8021400882c1c5907050280440c2d500021214190095424642d03c541110380384801c2d0314104815500b12003204500c0749035031800c00c0d2082c030150a1a00c1c0c01c0411281c140d1040d0b0b0031190a001780c080300c1e075585035000d0880c04c80742e5881c0c081354100c2840c02003000090481d0030260290380c02d881210504002d602507401a030072840c1c8115071405903104100541e0500c04048401090581007650405 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 631777176 1250 631775926 631775951
    0x609070c030915021c08040204050c03093d06050f040c050f2d03040c0b040b0a030b030a020a060c05010f0203060d020d02030a061a0901050f01020307080a1e0c03080604 74
    0x1440500400f400703003a1000c003076001c1500c208032001e00c501801300c00300c0212601c008050008035064805034003da007030000041c9220040302c11240520012001400c040002040030020304103030310f0302000c041140440c01d0311203040c801034058003075038003000010b500c0c3e241104005400c940e0000c0d00cae010701d05111142d0360310703600a4103070381c00d075100901016a28100b10101149a121350a1504482c280150b10000300480407806035100301e1003010019a42611421709450900880c400c1c0040c4940400a4190491003500800a41c1c0b1014040b1460782a050707000809440103074200c0c9000403601c60310704092001c2401f139881c40100240c1d00314910304101001c241c0a881000c0068001c05609007942c00f10b4500700080f44405030444001c003c0d5081c280300c1c4e1003038261341d03000c824440d07400b81c000410546401286882404416001180b40c0941a074a0f900950000d100180c1800354a184004000f102c0196804010a0a80c3c890030102300358500508940c801400f594001d40c0b51000e1803011 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 631778426 1250 631777176 631777187
    0x605041b030b090402100c03171513091106210702250f031e140d1d100c080f040b0910021504080f0913060503011419021303060c080609070c03 63
    0x300c1000f8035007c2103112039402c0503510047c1100c1112900b50018080151058406d220342032404011107d00d910489001e11140950b030750707400d0140801590840350000b51420030001c200b0414030341040d0001412148021024070300032120000540c0010b00e441c0d01190b00c408010a40903030381e0120400050401c26441d514083e280401042840300300c500c3c102101e07400084081c600c4c1e0004228244002d280300103034aa00301107203010302040301c030700104841d4019801126080320001c0c00402c5c6414441000312545407560809070744502c401c0040d0313403820300d422004002401810041c58cc2e54101d40060000036030600400d0300440d0042d52480202e01510303000c80350020b410400351b544407401c002c0b4808141c440c000710f40d40d00078248900b03034040042c40d41069007103a600318002c01400088510107040300004840407106450403c0314850740b03030207640c041c01e2854528081c1d03088030364503039558104071108020128041410002001081e207406898140c1c45861441d14001507035441d41c01600 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 631779676 1250 631778426 631778449
    0x30b0105060a110615090112081e040b0f041a0306060d0e102309030903030301210b0106030203060909030f07082217100c09060f030605041b030b090402 67
    0x452407000861116040c401e0b0f880300c208808503000e131603050400107214a411039400311294080c1800c8400040c5d2049031b00141c400ea203400080040c40c08015000016881d920b00346952410b500070300000c2200004200607014420950003240da0300e074280307010a8600010200300d054400d00070010440c454440e2800d8401002d02c111010500005031803c603800c2011090000d200d851406014014501c4038184984440f0a941c051a49540b14521805d071640301e00c040c46901a0b000700010030888142c402001c0716010310403800400001255a07001d42030a0030ba200d2800250088188603031031a0545489800c0380c4101d00031860f10040c80d140031f29074021400c000c1d10441000c01c050280540c0d07061885e418228a60074a03441c00d46901e8540420003408403c0440d5210b0181c1d01070440e81c9074400d054040e881c070b407242d0b0091440c0400031a408001d400d4444209500c0305030010301502c031805a2040ca07402c01203410450004420018102d40440c1002840745030000180b0015880d10101485c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 631780926 1250 631779676 631779679
    0x1101050a030605040c030b010e040b0307030215190804030f0810141c0b07020f070b09060a2f10051302042a0215090606090114030109020a090e0d09030b0105 69
    0x50300c540c20340a080d0700038103440e88150f410a04003004481001c1e450b078051040c801c0240c03511464420f6140a200841d24103040d00c2d500350f03001400c10700143c5045240d075600481c503100070700e180c501a5803451500242c1501c060000c10411410300c020540c000644031a00b0b9a54a0410200c0ca411643c590020202c2d10420000210b0381810720341c0790f00d60068007886e4110f078050581282d9203c1c9094100c2420448005005005850800d40e00b042c0110f0710301d00312a58043d030103040c070100e081044075550020501c0010700168807044141c450101c607050840007800d10303401c7e01104807042c2041c106400f0039105019203150008004009481d035884004a507010340c2d00003210050468140065a580680c42d070103020214010745c0c00f40d0380042c0058802d45010038404054507044000b654511040e50402d5109003044014060b00d00f1401d0031107032440c4020004950401c082d0085400f819480d04440d8041d40c4642c41070303900070002c01481065000178900544032a255441c1c4018080e8107009a5 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 631782176 1250 631780926 631780937
    0x218090c04080a0807140f03030a0b0d0506090d080711031b030c07230108011d0601020c060a081f0503030a030f09060203011202040608030c1b06070f0c1a071101 71
    0x14002140c640c141c9015001c00012249141d0850501040300d4000c0c80c012603040c001942d00c103641d90004585c009a103044140154290349900c05030802822411040c103800c8071014062001251040120a0086480c40040e21700f001c00180d0040c1464401420b890520001105003408a0400811500e020418802e0100034601c8400e540e4110300c00d5401000715441480408071f0300000d1000c80d1101c2402d010074040340300c40040c00648088009100f0b901a0140d09070308500120b10f48105240d0001e81407054804080b01c210004274641c11404074040021f804008000c03034244031424103c0042ca11520201c0300a2405001a541e4800c0640f85400c00d070300d41c03003000764200c3c0d590012240640d200070195102c2d82c445c4400140781c22040410703031090b8100680007030401008400c880480ca540405003c00611101c49402200030010302c0e43c1e04058100702c0000422018078401203c039206041c00c1144510307042019980310b9a08206034503002041054500103102d8181008030303000c0c04c0c01d00c03 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 631783426 1250 631782176 631782181
    0x20610030f0503071202060106031a090402061309060602030c10050f01030305070c0515070516050603012603030c030f0115200a14030a090902090f0402031803160c0504021809 77
    0x507429801205402445c44010b1315210041c55004148141650030070b5a041042e00880b0400f000ca06141030600d507007101c416004a009801c0840041c400104045640d00b00f042e030328a181400c0310380551288005070004503143c501940140003082402031600805d03c4070303042007030a0b40c4c1da600c0184802000c0c0040000c410b8108400956a440181001046170f10199511074090010380d01c041c504a82c140150780840d540700314800a080d06842e0003810080c01c50382040030200c117084002031005080d414006402d00100402c200441c441c002d4104400d4132410642c60702000d0f450182c00038661540082d40c505510f6500030140c04800610b9000344000b000000e01d103500b001d10700b81d006000e507001641c46006442e4000001c1000440b09c5d55101415640c2e21035001c200e0190140180e40070398005641072482c602900070b5a00400c40f010038010701d44032640d0725461603201d0342101220941c0300d03d0041c01e00904209601c02000300fa01c6c154178000309040c00000c58090002034900c5038800d82c02 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 631784676 1250 631783426 631783433
    0x10b1201050c0a08061801080607111c0e12010f150812070b04020a05130e0d110705040b270403080a0902062b0e0c0a06090602060106050315090a090210020610030f 72
    0x6c10001402844a41495845001490b1603074000c4031102d0204520360800b84d185140010544401c8181e80c07464256210320400440f00c1c040400e1401c4d5000320201d112104941c42032003543d00441140000080380c00070f04250402411091b40301203d02c0e002402141e2502001c501115040d0741e100903e0a0700790707154400281c00c821141c00040c3c001400080303060015403245e100503415401c4008450440001036400c840500b04198180115080918100700d42e09142d001810108002401400003550701c2502407203010520044001d9034071604180000e05411800d0150801d01c030300010300c404405a00425604c1c810001100708604c1000c04460003410b840301c417400d1143c0519014046014004180e980c0d500b8031212082c0718030040500025114028a041030443d0043d801606180e840e025040d120350f00005c1c51840d2680c528003403912607540380d480b00b5104107074480b00001c4609090052000d68960b8814010030b540c0288280112403c9490b80c0e0812a648511034040ea02c0240c074 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 631785926 1250 631784676 631784689
    0x6060319060f09080a120626010b0d08040303031107080304020f0103141003020a05090103030c1203060f0e0a0f140114030a060c1e02061b0307110a05010b1201050c0a0806 75
    0x145614000e45810882c0082141350801000c1d025a2541d8021141249100b844226415031050703018080403203100421840312184000c008034103403000003072120054400b045005040c020308860760380300050700b841095014814401c0c40084100050f04000095860840603c00540003030720450141450700b00c140e100c2d40020411100e060001103031414100c0306110b4a000d1404101d00c9882007440100c1d65040a020580c1226056941c001c60082c0a07282d00c00480ea076888007508140c0c950b440840c0421210300e041008010700c0075010030324a0070f82501c0040340c4000768071000302801c11135001450102ca200d103906403120b12031403100c00d404440009150006440004000604060740400303041d400482c814400700f0817a410002044110508a0b1194811100d41e8401050ba010507440c10b03c4035030117140d20400b54103001070250315081c0401d01d011100c25044032607a4440e0b260701610704100c20130b00b500594040c001d1045081c02d545140f070a00603030004e0000c01c1010800030341d40f581d601 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 631787176 1250 631785926 631785941
    0x30b18011a1216180c14072a0806010e13030c021c0b0f0108060115021005100806041b0f0609090c05120103030806030d1704112b140606031906 63
    0x80b1a004065645440300c0302e80e401084c0e100107aa00d040e00c40103142e80203942800320744e00e01040091516103156282000742980c050038003102e05004903c401c02c41b014864800113400c106e00200130310f41c034040c1c101404410040c1070000140d10030700c40ca800650000400c20b4074540c1100c5680c1f0032104c0c05001410841158000360400c0c00c4c040501c00e054004560300d5042e04c1c3d10030b080c0d0b1030030303a25981c00c207200c0410701d8107500c0140d10140070340c2c12002540e4003850b0424841e541c03480b0210303914842149002001e480955034010100b5800750b05854444002d0014841d800c9011003091400e00042c09503002440313280590340c0c0f1002c0054500d80b18904840552900c0ca0780a09a940c490400a148010840c1c4060003480388034240c0f4509801001151081040411074034200d035926510303803203181c000348001c1d81c000054901d0242e16030340c01c20100780107654281007045001803a0408022a003080324602010b0f4002c18240704003610082201503034081d2485095a92242e546015070003011071 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 631788426 1250 631787176 631787203
    0xc050a0e160e0d0804080111090a0e0a090803040b0f01052d130915050601081009020d0e011d06010e0f0105060a17010605041811030a091b030b18011a12 67
    0x10380f9400003c11200b1000b600585607848000c0112043c0042015518031402a13016448601ca210800c8041c2c0c3e407180b200e40c4100308503004100300e011032756075034a25042038400300d07100c024a404101141e03c00f007090600400c422560701e000200007030004031000f603d640e84180e0301820000344106503190700048000710f100c1040100060b58032411f001d120340061819034002c05041c5004625650303c00c1231624000c0c904100911103440c90400c801009602921000b11074607118030f0001d1302424217100702c01d8089041c64846001120003840c3c1410000160016095403080b00103100c102e0480d0034840c1d0549000b9902203984610410080c0c5209290342c0703d080040450b40b00201340694000003030021104500c610b2120b09070a0344510007601d0038103c40300100e260074400507090b0000f60f0002c0d14014050380e40369008414080c0b0644c10440c1c03d1304291f4080e509030043c0280a142801111007200a1000807c08d882c502c0d89030b401000c82280c1c601d0700c10102300444400030078041c40171841180c038 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 631789676 1250 631788426 631788439
    0xf090b03040602130905091f0b040609060f090e031209160803040e0c190518041503020f0d050706140d02030702010507030b0a060905130e10090c050a0e160e 69
    0x70286081c001940c0b00e040c540b41400401d44000400060600940d4010fa0012002d01009103102d8100000c01ea121030043c64400e1b199007151074151160701c6000060007002402280d16400d02401d40028840da5100300c800c00d10b0400022020b40012040d07a408010071144012144c40300d5007594600180a002e1307070305148010100081ea540300100601c03c03504403900c0c05015a407941c52001c00d901950421826209181c1b0309540500d114170001c1100203811b10a4003010824840880c0440d01040c01c900b12000c498070081c0103510302203480c01550318084a1004195034150345513030300d84a15108013002d10140244202496814509551001c84901030454480c600380a00038041c06099400d0004079113410a041c926003050358105042d0b44245e200c80d80954901014050781165100b11060303034070369910b9250300520303003405010805403442c040800c00000a0610403280c031440e0b4000352103074180901c200403600c5100c8605038407551800724218102030389101a210803c640c040d0550000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 631790926 1250 631789676 631789681
    0x604050f0d12030f1416080711190501110405100e060d09060902090105061806030901060e040812060a030f03120f0e03071b050a030f060905010911100314070f090b03 73
    0x983c16449121080c85010040c0010701070600038403040d038000d407014411031a4684180148034024200181c204202c2d02e01207a08201007035183e4208515840303481c80c02240c3c44003490030301100b405036001d6411000038541c60240382c070001404040f415600c5209100344044071030a07956070001900c01c15450f4820612590846142900c01407000c0c0c80e080b231142190b480082060b00b46181520940c01c00703203014151412502c000c100c00f0341c01c001d2a50750150b4032142d02040e10b031900800b6600030340c03007403103015295158403403c89181d0700001c00c200d005102d00da0b4200045569407509000c2c40341c040c14203600030501241620007424000206c00a01e9080c415040f07030a020000090000e1402200c0b41c010070b0b0b018400d201d81c442098801c26a11188200c2e040c40461003105100360110f2040c03200082b201c517035a44d410b082d120482800e8034250b051070034140090400c884410691500c1d031804200101d00c225881125460240c003410811916400c5501c0c6a4050340030000500f0566108540b01d1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 631792176 1250 631790926 631790963
    0x3006050c040e070c0b06191a091002010b011209020105130305060a270206030601051309021801030b0307140f04020f0903010b1806040c170405070501030e0c0604050f0d 74
    0x1070340203204040241c81d0480000d00020f108003464840103601c0131103410651500f03020424070080e80d01202c0c0d080e400b030840004951500740106410705007100000d503142d00e1028200108154040f5440723040d039041020100d20350380e03c150300741600c861801c00020382504500040341c980c080c143c030070744144589000c04018010001182c900c90803107004140301c4a40050440d112191802c403c121865440504050040c906440034540c40758061402c0303130601d00041288040e4200c580e2140e44203a500003601110550400c00030215400c0c2800d040c454401c030b2201017960340c0d5052186e560400c001500703807015540c030f2b6528540e074400018825919001610803210700b0303034880220903210b9860038018022904081c404102e10581800124a1a9941c00c09204c058003150416030200a4100904102c042103006040e0149001d8001041501d05160014080360310308000b4801c154010164a0207039a00c1000300c0d030681e81b003515070b000c452802ca00415048915604024814140c40b034190220 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 631793426 1250 631792176 631792201
    0x4080f0403052b141b0a0209040f03020601051008161b08130e061315050406030308060907300e0703151107031409030f030a05180901300605 62
    0x3140e2003040c154080305034118050311030282c0c81300d4140110700240041c1c00d6029000886042c034035121030607100f030300b501c1e03500184891100321021100303011194410028158100039180c0906020741e01d01034580d101420180001c10004c2c07101e43c0e1419505201a0614801c0c058015044000085108414003602d042242908200d1a24601d815103020004030b0b0f0f4040c100c1d150040ca0b010b03022040c0341c2c0c5e0300032103130001d0b001c2c0400c922010424030360700144584551146070003d5021b5603030441c403810b02d201000101d6001400040030071911105514010103002280c081e0595540d00c80200619616200c030042c041440020501c1e0207542d100205105040d000b00d5070108007194200560024080521000c0c0a1200041c000903609542c280303074481440f000b0302074400d0090031a5126401e030b111052a590101c048100050380109200941c040c500424842c0250119014003640d8100f4807490000b103c003055800b24000654002d04980407061444100503810620510440c0780010a5060 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 631794676 1250 631793426 631793473
    0x32091e010c0e060a0f05221502240c0c070905071115220602130306240305030706051f0306090309151e090b070c05040c05030108030304080f040305 65
    0x100340c982d5035100d07a52520781c1c1250100d005039264007500800f81c0800722415044100034249600c0508034134050410303100d000ca002401e403843e50480c4010003400013402d1070101419014000424400e02a0b410842074107142d1141c2c85485a9844a2007000d459181c4001c59105032415494001448030f810b0303000b81c0540000401c10b048038400c8440d05041c01542c1000c880d049401c0c00c01d5582e402080d918028400341240c0164809400c082506840703400e402a42c1c0c3c004c035102c0d5582d8045441d1011809603d0f0303d03150f43d484d28044000d1954894135201e10420300010700d007641e074100166208400310201ea101194000008005640b80d00c0c004009010481d01580460003a03e400200c1ea29407114101d0703030001e1681e440841c03440b04101001c494044071a4082446030003007001c14001d1020f0060000700e4061030756002410315110500c42140d541402075400c115003040180054400003003100c2c0c01c95403001d2501d0b0b40740a883c500082c41e00640e040280340c0d01807060b21001551301c0c0010400d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 631795926 1250 631794676 631794701
    0x180303180b1e0c03010308041401050417160506070c030b0a0204030f03090812030603190201090510030b0a05060309120c0114071106070513061202130b0a0332091e01 73
    0x4555498922003d0030f54002440024020907041009108451100200c3d6035046010b041050909846050a041d001d24601d0000301a62001c1c0c0041c20864004007110000e08098400c2494511191600d03400064075000c0540f01c00c50b1034020443c081a01d504079001190464004e03000a42d0f18900103206028030b00c5910220310505050703212009408040701c0c0200e800400030114220811581c40e45c40e511068240c2c103000c0204000112619412507010000c01c2555001803002c038250108110b0361155040240138500510400480010015a0000b5103d621507025158412070003298050140f1010440086100720140003002c0c1d08043d882c2e109200c6241603032100da50312141141e00d8058890610300354140c1800030000d04e0302800040c01d08805804002d46841601c1c0400030000746242c0c00fa10441c00005941c020040d4980325825400c24110080c903d00c1507000282c180c3d090381c1c82d078215440c1c2011000b09824820800c04180c0328000c9001e46900044c802680074001d108404015 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 631797176 1250 631795926 631795981
    0x1504150203042613050904060603060606050405040f0e070315090c0e04030206090a0309091e05180d05030709090f0e06040302060108070501080603030f031b160213180303180b 77
    0x4070f14810070031090b42c01c4d00465441000c1102c0c6000208600110302620035a40d582e5550400b1010840c540141c20141c181c0d83c5496555500d02004d200880d4510f00c000c40b2703a90314140102554901c00b0413004100e0fa0001e03905909852a124028010200004014150503003401b00040c0000c414855038841c0e4029020b6521640d07038000415200c41e040702c03004001540c3e0060600c4110110391081c0310070780c020b0402c05203000280440038222007080d00c90201d140c41c8100c4075030000004010b41100a40107140050450400d100b0151409505000340c4060680b98000311940f40c90300d500200d244400315089840d6800c00d8180a07465a80c02e0050060306e01510034080342c80d5006d500303c03500810000e00118038200c2c2c15210700c4220382000c0c2081844c00300b00300c2e52592105004004d000b040160500b02d24024900340f0400c142304501c3c1280f1083c56040070030026801e881814860300054140c1408146018195143da004603034001700144901d03100c40c2401a0420100003811245a0002c402c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 631798426 1250 631797176 631797233
    0x80304090b13180c1d0a050901230405061f2310031a0307180b030a0c0b120703050106050d0509210705010506010e1f0909020a030203090c010e0102150415020304 71
    0xa08008108082020101514400406c8096000c0d50140794408106000054084841400328080c024480e140c00d02408420040c002849070602c0f800760020303071640074081003d11407411748408207103e114034403000d00641d0720752811920144060181001c01020300900714070605002d0020500d035180b0340c0a10792180a0341c10107081c00941e00d0207440c02c011038031900f90560030189029016000086416000740d00d1602c0008144d02c000d03101800300ca482940e19042c1d900300c04806400001c1441c003c040c01d01004011050704401201c42000e0000d00c003040507134440002c0c52912500c1009224404201c4404d001010002000380c03000350312640c02403059842c1d40c0011030388040c01e071005c958024205c000c550030300e03c50403540a03070ba06c0a40c180040926134403020700d005c98009110440100740c0000070800c01c034009022070014901e090800b50008202c4500003907880384070505048001040c9408141401030403451070010540224055580c0c0c58103284c51701c2000d8000070094400c00c96100b1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 631799676 1250 631798426 631798439
    0x140f1b0c01140c03040f060507060b040506100815120a050609030f030c07060b091005030c01080f0106030b19080a0b0109022706090307090e07050604080304090b13180c 74
    0x800c0c0190080580d01c0b2010025514000d4071150301c40c185010003848100400107a018500414030700030300607600c40ba51031307078000c2c1820030503910546806c500c25460f02d4100b040c140d65140685514021a16040800da40c59a609002d0802042e83c1554401e22809114892100018a10740380d58414001e80b44036454000382140d44e0f00601303007a0106246c003400081c0091650b0320103000d2850141d00c02040c8610a040400c205000035501c82c0b15441c2100b02c24815400c0c06c202c140c1c001c00080c6003101451611103010300028406010301d004042c1c8440c0703200c0b850742d40d505443c0d001d5101c101c00c0d0740c0c0d000d80e514150740e80c401c2812801c4800c08468030000504001030303c00e40e80281540115180d201d00a400680d0281410302d608075804141404940b802e074808118484c09019039490001e512883d80007158501030342640482c5c41008100002d021180d000b1066404440c000d04001c03034080d0035400001d070044c500c1e1924141c100e103404401c1d03c0c02e040d07240d181c40402e0300941032400c04985542 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 631800926 1250 631799676 631799683
    0x4150c0507270b06180a0e070903023d020a290c03011409070c06020c0d030609020a0903062013090c090326040b07050c1e0d12140f1b 59
    0x310295004c20103000c3c9a207072070750000c01c10156503001401c1c0800c06465401c0321100745019100000013400c1c90005204505045004503004c9658500151448268010001901500c00c03035040034583e000c481d0040d0b003802049144011079200300021444524180c100b4002e00c00418100309404204002c00d903034540c5842100d05071803072144600803030540e80c014440032641c09090b010403c40b4401485001c01c005101604d201800c0b44003034900901c0c1002c004058451303d40124020b1441080500e14494022400008880d0f1148001c954900000701c1660301c5e17842c1918810800c03000180300c1142070985221001500c0c5004c400300800d10b10084200e484040e00d00009180c8100c0080c9480d44140042426241c2921740c0a21460103450300c101400607040070710f040390582e0201032094024030b40030180031441d242c164140e160301c10050b0700280c043d000705407000d440c840c50403480c808054400d44104a111a00243d559030303890a680e80b1158540c42813560040e220340c072108241c107110011 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 631802176 1250 631800926 631800941
    0x31207110f010f03020310181a03031602040506040b032508060709030615030804080a112b032d0e01030504050303190b091501200304150c050727 64
    0x1a90343c0f0042c00110781c42540250300141066101940c903180c0050594000040c00c5140e000580300400e460200800e0302e6030038090b82160f14804c0c1c0007403100900d00a07040100c503241035011030340490503071510408507009017103c0400d0741c0c040c021481e04881400240d009140c0319620304200480303c1d0b07500c00e42d8684840d0280c400c400044c041440c1040440c410b500075100e508181d00d03111034402c2d40c03030b5115003580d0f109611a00e03881d00240c88440601c4a540c1d9880d030300c880b09407083c410b80741000d008401c22521921000410a20403440c02d402c2c140700700d142003400c500c1c181c0c0c4070100c1c558460f019125503a0340f180243c00160000c2507400c032075120340556405a0780c400b00660035516035238030450072155032001c0e601d017041d5502c10030b44681e44c840140034010342d070b4048984090780c1490f0004145410500702039401d1070288039080e80741c000000c110780844024044c0100d000721030020440c2c0b17140b22444082c0140c414080081244400403695042061941501e034100500b01003521054607100d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 631803426 1250 631802176 631802179
    0x10020309060a05041e050d09080f030702012303091b0301180303110d0f02040806010f0f030209151906020c0a1d0a1d01050a201c0b031207110f 63
    0x200042940c12285410107034006201c2d050080345d02c284070505e24921601c1c11801da4290f071060300c0d5095901d8108507000301030003c0c00060034032043e8040b0b0855032885552030090402c040903500d04824002d100d41802c220700500d4030942d0302d00340b0092441e0f0380c1540e9490481209907000c10010985014400d0214070750282901d03600300c200c1ca0b1002d400410380100801d19103a01048141c1501f5203034410b002d003820807a08010303213560800d2107180c900b641c142c00c4107007001281030042c01007030307040220300c41100e5040381c080000c2c2c0d4403031401d0740046001c229480d0b00001415000608840216508401d690240e802c95000701204010001c0501c1680308400e00e40c680566103698809019412607840350409102180c007401076115005000e42c004280b05440c0d40d01c0f0144000c080b0340340900504c2000c0c035044080740c840410105c0c1800d10a4000d20f04580394161800006620b1f103411001c0034482c01402d9607a80071800001e2807090380a0481164080448040c800303852500242e00faa00303050 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 631804676 1250 631803426 631803433
    0x813170a110a03030c06050a0e160e01060801081002030601051303030e041a0a0501031a03161503050c040b0304030c080c0a1401020408030f1c1d01140108120708040504020f04030510020309 83
    0x112900d030321b00108009400d2505450301c441502044200070031551010501051000368080d10300f40240c031803450181c101c401042498001040640c500240300c925160380c071880140c0da9156203006130703480d101d031001e03151201c20601700001c1419080111006c0c442010b0b541481a94113079100100c1008000c2c4807d40e200707070720002c14842c65100e580010504032007000001d01c140300100002c1d160028008078656842e000b0b00041c004458240107244d00d0340c9050800b8400c9060591060009000318010121540d101000240616202c0d4294a01441c0c210001c0c642d02c46003050865152241036809662880d0582e4420042c42414400ca0b41200ca121003d1400c018105005990903446031004040490b03101c1080001d1900500c030b000340b1101d060203001032440f0700b070041d607003074804050340c0c0e04202c120000100040c03500811140c011248180346d10340e58056a180c0320302c107030045070810381e00f0902c04141c035620051810000c0050360b004a0480d95410755400304803050384011500340c1071941 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 631805926 1250 631804676 631804697
    0xe0a05040201021b15030a020702120a11121606020303070f020312060f1906020d1b170a0203041e0801060806070e0603060d061a09060d02010c0813170a110a0303 71
    0x601a400c0f000610300905c88200018075a9803188140c105548441c112030b07000030960304615100312082c4c100d01c0c40390003038500221180c072401c0000d0350241c18940910720350f01304020340c008180068007044140300b84c5040c09507150a8029960780045400b10049400000528103180c000015154110040340007107103503a480006015405400b120050782103131801c5404d001142050900d84080c0000b41d004040400410343c00800904141e668502d0440c0c12413012000f081c0c0d40440140c034846d020603200c0c0d440c130440004a1451141d81c0c04507c9440c410001c01000c40110603240040f154401d00070700c0b400380c1791070b203c03602c60409843d2100482c03064002c0202d81d0400d8405154480700040c0b01c48003e40c1c0c9621030360241ca141507200340001c41001800e082a1a10300171164106070161114440344135940d0000c0c000c00c5131102e000d000d04101041902e0072402c041e04c404040d11502003094008100e031036001d5907980c200702e82256007020400c800c88080c14a0102c10b812250156070b4903500c803 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 631807176 1250 631805926 631805953
    0x907080615090a1e0503070e070807050708030402040902060c0109051c02010507051602030304030c0905040303200d090507031703070809120a050d110310050f03210c070305160e0a0504020102 84
    0x3d51080d201044e814001c54001034070f59814070842c4000c002108080c0707400d2501c40c1000b0690080104440b06000050091002258103c002c0e0303175009505613400540c042da1400011154059120884159824402070000704040480c03090302807000728080030310040e40b1030426801e0b280d040f0341d4400010001c1c011106a400030001410034140044c00756440d10f0307143e40b108a168041741e00198044c6032200d01f40030400d9894454403420504011424501d919807594611251281ca072280d03014035119074003002409014460b400c0116408940d40b03070f408040404540035500304460703d00201d104000060120740303000c40c60412405100382010b00c1e00c3c40c074190680c1c854000d6401130b021196200c5450544148070801140168100da8605042c24030b4a0104480000c850307144a00070b8011400c2c0800300d298070032606400c60b01540c036164891045102007442c02c1c00550001e0300e01d224040d41a030b461180c101d0742e041034a55040034651a83d8a1407c0e100a6410903503001380160300508a05120 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 631808426 1250 631807176 631807199
    0x201080c0403061109031029011106071e091203200f0609071202130509240703060e07020705011d1e18100e0c0403020907080615090a 59
    0x410000326003035040039100e80391102114112460409940c40000e031244041c6410866070a618032081c81c00c0c0211024008514151107202000d43c0c070309210032892004603806505280c4130a440d0004a0b505483c14020041c18000390500e500841c4625001d03c0d60b04a114903100415a1300b8050404400030f250b43d011161a4425021001c065501d1505076541d68010b2008205c0800c03500024512801e00c024800c1c01c0940642c4019005004001044010f803a845911900d8284500000030b0390784d1600031060402207941103030040a000c0c0a001406041d1140c0010300a4205a404114031622910f45001010301a01d1260150740312140c10005588500f84201c41840510350783c0501f540030034003081d00790300c1100690010082c01d454886d00e504100741c0300000084554400c1c12039041400030100c040c0c0090040004a55510000070621742044003158000c5901034050100f516008c00c2c014034040c81960414862410384461420302c076000c4098480041e0024038582c0302e0707442d20841400 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 631809676 1250 631808426 631808431
    0x30c0512060123030a11010905060c0601090b04140a06030c0e040f0204050702031b030301030203010c08010f030807080f0d0b04140106050a05030612030c07030b0a0903090e1005040f23070c020108 86
    0x2018a4031034203102540c03414003040100341c6c440c62114000390034800000d4030003441500014081c110500c0700e910341c2d000c00030382981180e09403607000803640e0fa19000304001c1d140c4402c5071100c880c4a842070003003119540d0b210f0801c907030050300501e01135911a0340c44034968401780d40181c01c4245660b00c1c00090320302036010b0350300410140112031428000300361000030400041011a880c1d000480104190b04080c003d89040c2c2e2080c1c94040160340c180280303081155000e000c090310081012510301d040001181c202c8040c240b2280c1041e4803010281c070840f000e405c641000c1d50040c2d0030806c24805001ca40141c25040c1c50181d01d400f41015611001115240c00041065500188500c0300900444c01030004120f01010180500800f0b803c50911403107207440640b040b5800c0745000359443c0840d40c4022040706685045c030f01c1c80519260a50f6881640e00395400443d40300b8034040711048601d040780c0c0b00f0002024175103600649483c5407120308030312400485004008c21098541d00e001584225182503 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 631810926 1250 631809676 631809719
    0x14118060a090f0b060f10020706140901170928020f010905090a02160f0803040201180e060111010b030129060906220801020c070f0b030412120b19030c05120601 71
    0x100203105001510360381f5960031302d10150700315a04c18400b0b90b40c496a942103041d4000c91040c034000c1c02800003042986800054880c00a10002082c140801400441c175106040380414900c0b010400010ba1100141c00c400c9100340c4400901004070f50065910400f1948003d0110009998100316100030b58020034812440702c0c000321240c00000c84060000c010240242c80b060303220318082c800584088071901e0026680c000c03100040000503d00404103500a500707203850100c18040511050150903c07600f4958503508000e11121483d00c0c0c81d2915201140d00c511007022440c00c0340c1449214403a50358080d07009541044000c5140020390000034520450704504c2050035a1800e40c20308a80048101c5003032030b044030904000d51003481d20448082d00900c1039a03403440c02c15030340e4200c2403d407031046d09040c4090040303c08403940607940310000b80c10028040181f513a40c141c1c0b0300c03108440c081c041222074644040000c5068101038600b22401c3e40707120700512440c0d080c020320f042030003980d40460 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 631812176 1250 631810926 631810939
    0x21215120c1e0306040503070638060417060703150f0b0903071806050307050f130f1b170a05070c030318080d020309010608014118060a090f0b06 64
    0xb00940c1c400704404ca100368064030140d92540e0f120714000c0143c408100e10300d02c101e02518014501b0600f0703521000400d0807003055a64041c00e403d404210300b80115030200001c8612000161142040403412520502181d641044400c0c3c0640120b44401c0260050b02d91480000c0d000344503016603000106111034000b401c54050595420b000405040c580074814907807030700c0e030a0400983c102080b894014090450b008141842d0700703800304044101c200090803104e030300d480c800303d02d9800662202c2040300d42c0d0101c0445401882501510382184048038406a0343c040002403214041c503c9500d002d90b040fa60744c01034000240d2000ca002d0214050044800c4c200741e8004e40000b07103524014161044240c1000d62a4500403902c282100e016030b2010300164185a151542c440300b08194220806802c0d080c001c540483e081480b44402d03c0029179407228042400b401117121041d14050301c1c81070007100322a199a0385103408030a466403030800400c01c0d021300c6104000502040c940c0c1e580640c015002 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 631813426 1250 631812176 631812229
    0x10f05010c0510060f06030f0c14070c0b0c150a09050705010c060b03030a031a030a081b030f070c08060c04060903060b01031506121112010e06060d021215120c 70
    0x2141d00300e844c036a025070035605101a041129541502941c07200d507410520811100754a54030103400041c00b0304180304110300c0004d0007010000349460286c050500107900989401c18410500e40d65078808032206000c2d1000b800050b0048003030701031404083e03888400b5250a518190064801410f00401120200e458900000f80e5440400240203d80d00c5558080703404480002400010b21740c0700c45242c080d41102c50701c500445d009a0454900d28160740030103080d561410182c50860007807a0b0a0003036a81d00007407410a0103940220352050726003020a4450f00d4031142c00360582842a842240040b6440100800200320180d00015405106050108501155280074000740001d0342008001c9442100d454140302e845101d44640201803880311443c00050040b04040008144696411150314000168068030b1320340a0381c00c80400160f040d502d82200300c0c541d00618904480d08018200c8800c950300e094501070602c0070380a00d188000d0275401c1c07140c00501c8800c0d03488140d5983e038080d4130702d903 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 631814676 1250 631813426 631813453
    0x1090306090819032d022b0b030a21030b09180f03040602030d0e0a0b0405031e0f07230d090e070c030801211718030105010f05010c05 59
    0x40d807450900c1042d210340d42d0030490004000b075414920300c1104161810b94411a041c1061900603408600c3c40031036041c0c0d81601901c03902a00c100d5404903c0200b00c000201504007901240807510148102d0a0000c291a40181981d514900c0d01c09000d20070901031200030340d03c0742683d4460080013458080742d207645c01808270704c0f030840944880030290140100710f0a40042404034603111400c08018619051074104020351364082c58541000c03442d03984c10480a11502000450000340e44800410140d1915052103500c82d0000642c6182c2c01e41107011281d40e122104c822600c1c000f030b46821a609111240d10b500206a0f184039210301200640e04000800d090700300041a080c00e0a03660b14038030329041c009451301c078800203421101800640040d550000b500604550f05440d843c81404c4d00006a0881c28071030200b4000002d81206100c040400b540b101c4800100040303004040840c440900001c1403600300e640902c10300b05070500741e41c0e091109601c1000030b20111400386044a0003040c4c4e004 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 631815926 1250 631814676 631814681
    0xb0c12070503090103050f07050f1b010c050c06060306042d02041d0106170319020a080409020301030219080601050d0203010b0301181a04110f1c050d11210901090306 73
    0x800c1078440380c1c008180700c07002d507a25000300342d03005181041c02c1089003030036400505140501c40c000060a170003c40d00c0003004811069030404c0010040c001c0c0300b400180c0c00c1c054103607881024000494012100042c5207428005481805180d202c440c3e4000003034a1007400140c10b85500400c234494102c803101c10003507561402034024400c1d040003030005654504589500b100d5207a03000101c54144200040c3c00d100007c03050b1441c0015245c0c2500f0f083d09400012400c018102c80e0042080d00081004140c001c260303030145040e40e10944020007400c04080048209860074400d0603d142c1c880e000502a40c181030020300d29181c8007030004034090b909400003d00b0740703c0911208040c610810b0361601800f03d60102040e81500e2484043c4803400d003501c0b0700783c620092b1040f0a004188103040d91080d91a2403003200101030300c407002d0003803810700c601d071080d02c0e02003940c2c3c01d03400104810100d4181d03100219409200d107070200100046ca001044039101c03550407122903a418803040b410008041903060 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 631817176 1250 631815926 631815937
    0x5061005010f110a0204153209040c080a1b06050c0a1511030901050726040308040206090612071e0207090b041e0203041b05181b1602041103060a0b0c12 67
    0x15580403600303050120030701d215110048281210b0790a040e8500c451194020401a4103234260b4405546503658107124008504c19030010445118281e03e40042c0035070040000b10400c010786154807015510201103c241c05905007246042c0c100100100028aa0421351246000031100101e80014804250881130300200c030a940c1607510340341005031442c0c1c000180c00c20b2a0ba21111045941250410075603070f40f000801c0202801020b40205056564500503a01c00001c020155640e640e440304080500c540e040c1d0f41107001c101501303e42d250060b01869440c0c89200b4a60003088042d02e000c90120103090005210750700640d4803940001107180c0c1a020707070f00081c11200c002d80e40703051610f04004110324200c0004000800ca0344280102d84e603060820b0043c0b04501c11040352a114081c15220b101000540c2800b015000100000380640044804c0e840b02e000303e0381080306a070340418548142c4421960141e0000082c0d0047c00f00d00c9403140504440c02c86101141e5100e00c040c0c1c4d44206580c400c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 631818426 1250 631817176 631817201
    0x30c092e0815030d11211206011209080918011d0a020c0a03181e05010804170307020a03110a051f02040803161514130204090b0705040305061005010f110a0204 70
    0x5030f003107241150404101340c0c4030981500b41d50302070f140c002c6c03221050301c1d028120311038035502c06840c08039420344c0c0306030361903150308426400400401255240904240e401052002c0c007400103504103128292040c8221030403186100c04514203404070445509866100900c01c580e855403c2c468038106000c100a50a0000e01c09d440b848401100011303000166205503001c1c03094080110402c007600001d0781101c10844a003030804060b036171901d103403038804200c076130005052158000c000c01c0342f065400a442030406002c0d0b200c810a40d040d203811151124817044014180d40e0062080404912031a140a0503145004030f006040a40780c203801c41c1154009100414480c880704040d105004070a0000d0600109001003042980b280d04084050890010040480c580d1002c800200b551200d8020341e0300c1c250300480c0440725150450b03001e4495000f901059846210301c200190008050a0814042d5001611901510500d25200b1074a01c0100145040240501c4505000503141e60041600c450030 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 631819676 1250 631818426 631818437
    0x370303060810051005090a2a120e060103140708011a0405060d020f0609040617070303140a0206520c03050412020a0803030c092e0815030d 61
    0x6025965490540d020703001010091510b81405503015a07004c0078000c40d0000c0e210704c41c26035a1031041e0001070040519a411351542140540300014003903802d100c40310355903101e4100c14005104410122480c2c0c251404107540054018800309803560f89900007925180c4c01c490f041900c40480030b003940c0340e041400b0481e0700c050254000e5450305000e15a44020b042e14204440240c03500007070107a090f0500c0060140ca8000346854180d259904054090300c0d104a03090b00100c07000c0b03025917440d48607120640001e40c1e0111058282d0405004548100040758000e0000352070385a5090580e4400803481c401c40480c8002036802c6c8456041c20300e40604084002c506507040814500300f00c5442004208100701080ca808400a45c001040e42c060f541030343d000c08030641c200d00c042490402290415044c602c408410050b00800200c02000d0080c81600c40000d50070b051451880d20381550701e00000b441800700800c072050340c8103861041d804400e81310603000b50313114400401e0402801d842e801c1d000070f0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 631820926 1250 631819676 631819679
    0x60607020d230c0d0201050d0c0e030a0b090c0d02060703050306061b0d02060105220e03220f0b0a0c0809040b04052d010b0403030c080408030a1215060237030306 71
    0x2c814840b61030941c400703603008000b0303d1003903000078080d10480d69500142e940d220f10010300d0328401c4081702d0303401e10050100c4400c2240b40c208102416030480720a8104c6c401c1c0c0e00d2039003445c1014131000140c1d503405084513080c06015030303040c7e82541000300741c00d810040a01c2444120b91240c50007085001c1d524018004803061100c009042400580141d40542c14082285064191506a680d2803808883d4005003140c40c0504c41c0341144101c5104d90f03c1c5840280580621130300e04d400b034500f221940b25a400d2460b03070ba030304020300300e001d11b401c1c010201e0380054640c00800ca007440240740e01000100000703441080580020304440741507a0021490341007512050b41900003820344c0700b2010b03180800406661400001c1c200612132800014200a20800e0789001c21810005490252401c4c4042d2501c1b405a0b420041014910305c3c4c00006c0d4a0419038078004088203c038004c400d4500e82da01400403141c5070700c1d4080b1010010840c50042c040000c000700c2204040c0e91110421512035034001c40d159 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 631822176 1250 631820926 631820993
    0x30f0c0312090c291e0409050106020313120309050904031b0302010218030303150d0c030503270d020307090510090e03070209060306090303040308040303110c011b050a08060607020d 80
    0x1c0f160303110b0f00442c02c900c0d5201260507801800a4601c80d0207003001508001144c5c146008403405541c1c030200c00307242068000b041043c0c0200203002090030b00e0417580202c6030b54414044100110aa025001c41c2090109202e5810406001580f2601a003400b91200700c0824015180140440c41500140d5000c242c02e141c80800818000200c0c408800960440c1013151504010b0042c1c070342c0e803602c66074488a41c40c4c10048901842c41c000d40e0411309403901ca076114600492468041c2c2c600e10b404010922508015281c609603000c17080d0703000303002004884d0031708076008005d0401601d00121014500b0700001c07103a115004d141a16041b00300a562684540d2060102820001d013003d403294011004000e1b400500006880c0c1c020381620b028081c0d034450381020b9004016594809000d0390300000e40d61040441504204030840c45249007404c0d40c1c00b0307007104940900400d01da06000418420108007c0d1034a040904052070000304111038086050340e0750300000201008200b4115004035081c1040c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 631823426 1250 631822176 631822199
    0x1b1d0a05030307030801030c052d011107060206190203010b0a1206080304080a110306070c031407021e100302040501022e02121006020106030b07110f06131509030f0c0312090c 77
    0x10401500c139503070740c00b910f0401c092b000d5401c513070080c3c2022040800103407035a10480f880484400b504040e1100c440e1651002521440200e8600d03052098040359406080c80c1c51007242d04956034417406504048803404c040315642560314200c04d800b611b0300801705801d80300f8001040201345040003031452000500e03202c41490b01c80381115100350004010810b0b05a081084002c00550614141e10080040f01054140b401401c4010390080c00882041c0406003106041141075402150035a030101100d2034110182c0c4900d0140c0d40c0180c0240569046050360203c003d40d41000307240e003003501182d1001c0400c040340c10034280554460701e02c8041c410b0940174800341001a00740c51000340b111030300b184c03990342c600030000e0280c2c0f0400585100c0f1903136080d018030902008041640a841ca0381c01d02d1450740c0c0d040940180195281c005c0c1d4910007446007424071581c00400e40c543ca0709900c5117048103013643c0031410fa500903014402500203410400540c2c0c4102048148142d49641e07103d818040b80f9540c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 631824676 1250 631823426 631823429
    0xa0c090c140c190303020c100603030206100305071401050c0609010518010e030301030803060409050f1c0306080706140c03031014040203040209060402030714070602030105041b1d0a05030307030801030c 89
    0x1204482081204445103012030000f0807151082c0741e0101912071858214020700c104091501c01e40144640144442c0c02500402d04490190342100d00c0d5844000d513108030a0b110b0b120003419988072810401124544040360744609034141411824039501003081428807070103d45940c02a55102c0810290001070415210301c0c0e035030032000300101c0031491001c0b9500d20060101406003800440021140d5880d0f400c040d069039400010384003202c201050b43c940c0d801d5445400303040c0f004007204580310f02e4441d110300d20499449800a005a900d0000e051754000110a0540700c0c9103410411080f2012080001b5030050041c451070410203890211f03840307010345804403102d00c00e42c010828000940d484c910401c2d0008003c40740145d50f034591607000e0719501000d40300124843c0011500030207102580c2c0c051030484600b5181404240d040d1440c0d0358030300190020f40d80100e880841c0d491410f01700c03000440f050303c001600301e008003038854000a155401201088000802201c01030041200001c255030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 631825926 1250 631824676 631824707
    0x4021c0f11040801141021150e011e020f030103021203070b090c0414280b18100501030b06180d08030f090d030c0e0603100306110d2d0c020a0c090c 65
    0x11b070107424500c025480c20200c80e411100100500030a40c140004111020320038003501c10108101450040c8082c06400c001030104403011980c00c4500300ea2886008688110408a035024070316804e42e42003101003220320000086a12007440309100050b1740404160041060000170a16001410304000035589401d040c174024488840c1408a0800c02c0782c0840080d4003824440070810154000400041c0104605642e01688410080f16030000300c07841c01c2e000f107030500e41e56558a070325000107409890042c6020768014808105035940e00604040d42119100b00030900070705120240c8464540d1b030000d48648490501c0c0005204004d01c0c200244442103c0300e04040c1706542c900ca201511036500c4644017806050004002000d40c020114080055a8040020041410ba01e142003401c0c0d0072000350942694036020410700000d90904180b00c225455908001c081300700014094080c28014000301c0640c85441d603203500241103e080c4402401800000080031a501e010013854201c2d50762805 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 631827176 1250 631825926 631825951
    0x1a010b0705011b0c14010e010f02130e16120207020a09020c0f010b060d020d0b03030403050d1b0c090b0d02030d020c040c080606180d0f0b011404021c0f1104080114 72
    0x2142d010380042c61521a9900240e00c2e984403140c0802907805041f4218100607994a48a2011940e441680c05001000200e0320b109825949900f842c255900c003d0740c003002c06160000605441500c20300007440c9074100f048000d1705000c440d07800b141c07040d003180e00700032049500400c40769100802040120742e500d81030701c0240460000072000c14418030544a814040503000141014540003540240c805014041e00f1280e60342e55900304140c4541c40b8420740710020702659552440c1c800440555441300c1d420400c00c0406034030300074442d0010014584040d8000040f00074003030242e03a05214003141d150240d0084c225210080341000103d031a50300141050080300700c14461507071203890540d0302481c48600340219804090300001d003c40c445001c010050902d82c0824002c2001c40c42c2168129214a02c0d60445904104208010780c0150205400d510f581c2c03001e94501c2d13a5041e08141400781905100182951030811050b080d98059001101c427691101e0450485060380301090f0307449030015015 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 631828426 1250 631827176 631827221
    0x41e0803011409040f020105030702071a041a030123041e0609060501260405070816090605091302040506011803230f0a060c0e09010e1b0c07121a010b070501 69
    0x7040714178404083c002c0d04003c030110000700b140c3c2c001c2140c040600382c2c0000702c3e2400a1580c4505801d54003034014000340c01241a0606402100b8509580c10b8510080e0181c080031114801024046113007030301c250b13105490b59412800d0218200b242c1c003084400310408103c0340c1c28022a0010340350150300482c1080b090381d500424100a07090035017082c0c10704051014168940c0c0c20160302e40f0010f41c00c0400a4011200c80003028154030724850220b400c1c0c44002c0c003605a0b103201f003002e205800c403000c030305d0031050300c14900051502c1e81c8030642c0540141050f42262510924410500c280c0741c0045428003050103a689000002c0c1c05a4544010341034014440180c15861503615059054001444507071140f100b052101d0140c0c02c0e2503c0244054040b000c42d6035900d44200707682005030761107110800840e1410f501c0340a130a04550400304000001c2c9502440e2440150030702c20364050980e090302d00e400003110480710005060380200800c00c00309841d40c07100d091940c2101e42c4110680d1001e0a0401d8 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 631829676 1250 631828426 631828433
    0x3061401020a06021308030307021e07120303051f0b0403111005120702430e010b16050f030c060f0405101d0a06061a071505041e080301140904 63
    0x82e0b80e410241d22100240c0c0740c0f40401c0f0880b8060020790822011030001200300f05009600003003500c403d00c0314400750024254007011154490b02e082c010514141100804540070902a4000d650408103010391201c2150304003049003108450b07904480240301000030300300207000d201d0355580001c203070440f41c0c158003480250000c2d01d07a01c28154500c049030f07903a40000d01d610740240088052003c0c904400f600c2c01041c0c2c92411600615110701840c600660085545071801c01c001d80400d4521086029000c3e90a0040c0d10076036401001c1540f0f10412070915000c009001805200d040a04a10095840360124503030541003600041020a0038026042000041240043c43da0700180f0707204800501404041c0e08401c0e5031900701c44101d45840344040c02810000742e03500c0402200c18440036074a80e1000342a0300d50480c0704003d409440084145041c0d0281d66280d808a500076100b01b40d50514030b0589030154200703906110040d6070020010004010003014007118610500049038045002c0c5440e0783d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 631830926 1250 631829676 631829683
    0x2150103030f091d01090902190909060509030c100b0328060b01020f071208070b040f020406090b0f04050c04080703030302090f1002030307140d090507030204140106021506061c0c0306140102 84
    0x45042003203600d4000c401f0a5485003024030f50714002c0e00c1030400340031340c4401c0444050301ca4014120344051a000009621520200c192020404810043d1000d41c0400e0401000760031415030300d41e498098001c42e0601c0030320034070501c042000d1070160804d11511505040c022248200d10311415034000039142d43d50300a0108a41096406004e101000d000322420301c44480d02800c8801462500140c0510042c004403042d00420b6a00c02c1b02c0074400b141e1115030302d200b51102e014025400240b40b03001400c081c40d184e003003103510042811000b8105030f40c0b000b03128508501580b042c0c0c04660300181000c22400c00c4d102440745100e0035180b03021034502c0701038001d50341e11000381088100300c9004400c100031403c1c10201c1e80d060101903000c0c41005420300744592076084071321040744150300d44050f0035403100d80641e82d0740c125061034010b0036410190300954609104014071240e1300c403200b04083c42200034907000b082c2843c00000e4001445030780f400350281c202c0324a60001c040407013540c50b0080e400d80c0d000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 631832176 1250 631830926 631830929
    0x602070905070e100e0a0504200c0102070f150605220c12020c1005060d020f12010b1309050d02120409090804030803150117090303150102150103030f091d01 69
    0x4400c00a90703665101401c0707514251114070160f01160703a200e0303000050341c8106103e10300c01044641000850340c41c0200800c0719a07030446542c00340a1050b2040074510701c000a403003210480400589000c1365542d038510441180d00d130840d4401600c8030f09100800807445254080c0105513102c020f00e08585c1407a01c8900040c411901e001c40d101d054020101c4c0c0720703440c1030946940c3d0007415501c1700841b008840e2203104120141c082c2c1440c1000280d19480e040820074a096005000004009607075401e0007800d01c4030a2100c0e590b03640700d62000100703031205203684004030326031800001d104200c3d240007810320320003036606e10456104500300b1030104403a00890781110002c900c001904c820b1403900501c0c0d4021980040d04d00b03d0040104003e00c0d104506e0135601030003d9880c1810072004101000c279004042c0e62152030b0740d00c1070000500c0e840440085500019050044a031802d03d104c64001910760260070840018041c100c240810f01c4d00144020050706140c10114108504421683c1c4401d005 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 631833426 1250 631832176 631832189
    0x203090c100201020a0f0912020603071b06090b011e0620010e01050603250608070516030917030c061f03150507090f0803030f27060a15060207 63
    0x4041800a441004401484140a08918030390925914064000c0d0006160000855800340400c1a003d20601003030040d64004907092803162041d4081c000b280d08000c041d04c05002400c1c41030b607002490b174040300d1409445841c0200303d1681610b41810b104c001a0300a4a03d5090103c080c20301034010300103603007070701c0c41c6140000003548910244030340c40544200c2c01803294a8041070070440441074110301c0c0715140a03000c070340070a2681d1142680040440781030314600d18404405000c0a8402e415503500030805140c80d0f41449a1070940104203a20260300320049488030104000058803034500c000d19034084d001440c2040d1340500c2583c1c507204003c00c81303224941a080720305400c8403c50501005503400103140c4512800f580703a04401000d040d544d07132001c9603c0d45800034001050401030010703210054080c5082d40c98201400340010340180410401c912402d80e0103105804140301c5110f00043e0000602c081d041226942e800c64928482c9030520325140d030400d00c151600003580404031a00b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 631834532 1106 631833426 631833431
    0x60b0627030321100f1203090b0405182d010e0903041a09040905010e0c0a0e060609092d0103061401060e12030702360118 54
    0x30303c1540600401110309440c643c20a03441c070032a000380841002c158995150f0074007004482254111b4076858003008628010706030310841203801019035900d0704e4a45402e203000301e40d16002151070b00c101c40101c400800c210071a9558201c0707420b51034600c1c0b603000403010740308007806050038880e2040f0007c2c101d000c07030102d100102c01c40c0c003103c0d2546964440f100b03500403048102d410449105a020fa620040d401c0400d00a006206400303007503101409461480c0302c1009841d044a80100103048450002c100301610781008948403040219000403542c1c5d16096074051007280455039008000c07500e1100c1e4400c0f201200090b068900c0360805100c41c90904e440c00c16007030024032403500007480c0c16100c0b071950f0403c00c1d1950950411241500d01c1c07da442d40110b101c0814540002032030071402d180c3c034214241e103100380c00310010750b410b892040342d49080e0a0f000c4160310400c10300400d0340d = true := by decide +kernel

theorem cover : BRFrame.Cov 631654676 631834532 := by
  have h0 := BRFrame.cov_init 631654676
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631654676 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 631654676 ≤ n) (h2 : n < 631834532) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
