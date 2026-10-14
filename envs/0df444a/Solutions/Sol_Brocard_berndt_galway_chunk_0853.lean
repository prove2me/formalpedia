-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0853
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:10:43.740312+00:00
-- url     : https://prove2.me/submissions/09473ef1-8151-4766-8840-34d904086f28

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 153237410 ≤ n < 153417266 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 153238660 1250 153237410 153237419
    0x605040b060d050601050d03050c03030a0219080f0408071a090d0f0504050607060c1b060506010311130e15030609060f0903031e0c2712010c020a020d060b03060718 72
    0x11900d84004000d060f0b503010030010411814402842100140a46403103403070030400c818075600d1a40195050307d100740e030005250039041c81d41c0c60b00c0508041c1910b00302e001130514009038540c103600a000544010300c00a558410006090140055440b84c036103109414580014600d486503d0040404045100403420388019407103101101c3c15240c0c002c00d5a4142002a281c5400911085490105218030001c0741002c10358001000c440e080c1c4180303c0460301745040f10005064440700d00701d5605180085c824060000c01035030000e4241c500061900401d07942c0c403240250b900303c0218615805015000a000208c440407845520941078000c07482d08a44807052041da40f03201c00c41381d14540e50007941030741c007558844a605a1f00700e0a1603900070f0800f101203040c0c1e544001904003100502c0c1030090000c0e070500704214510602000c58008100790503000710b000c0d450b8000858000d12a2008a02020400c0a2070784071104192020702228414502401c02038100d4080303003003640b1944a1110000b9 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 153239910 1250 153238660 153238669
    0x60e0105090c210a02120703050c060406050d092310051b0d09022e021002040605041208040306020a12050a06030c1e03080a03060f05090c030c030907050d0605040b06 73
    0x4020b0401400a000c0b1503600c2014074070f07202a02110705480c0c0036800e00c0c1005607030b0752815200030070096005819070b81c0c43c61030001e14021401440c18050794040c48100702d900c0d008810794080c1226030402140e084103910382001041c0c41454082004001d194406040c4140041c800101740c80f03860040220b619160300e1600c083c540107400c66049002040a184240e1003500034803c40ba1025021044520100142554030035440c000011569540805240ca80d03604004c2c00011601101c4214905070134528020a9417080f03000d10a14401550040320400007000129801181c208204640f0b48030090b07402009010001c0c86207a110341800d010903220655845480200e07544001c007441d4040c81c002c50344c405100e500c15500b284803940c80d00000490074150082c2202603c0d42d80008490f820300e100c1c280c0d6201d42e0742155005140440c10440d00d0303600003003141d8018103d41d0700c2a84940d0754244071490900c0307680040e41c104680c942e00c4010080342c1c0c0c025030f000d9031240700e504480786e84580500 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 153241160 1250 153239910 153239923
    0x60302130504020603160e06270d0b01091e020f0c0d0809190203010212010f050321040608100308040609030b06030c0310050901180b0115050a02030901120f09060e010509 75
    0x1943c0304004001040c4c030b40d0f85801e11b0702544034207410660019a1030170001500f0f40c00084d40c005034035190540791011880943c10249441c1001c5403000d50000300f03619081c001c1a414004c41052603602c5048041c180e00d41c5030310070007020504a0035982e4080000e1607150b1508040100a168030400c1c000c502801c0c01003071100e10400d07100c0c0082a01c00404e00240c801d01c2c1030100180d1301554200075109010b0242c0c0151400303020301c0403030340f05658071b44000d0619180408201c1d45420003004ac2042c4248407402c01c9601300c0e840c0340341040d425115500d810804180d554001044060f00142c00101582c000c1c0161044030300500105010f07540e1a014151921901601c4952640221910040c50365803035024a03000b0300004000101c0851718018810701660a050981d10340da08100100210044815030b4001506145400790400601210203541c030b01640309058180030f50810000c0c81546503031710280007035100e0b46c0e0502041f072090130072400414001004243c19400c11000900708100000c11 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 153242410 1250 153241160 153241163
    0x30c060c051203040c0b030f160c02030604060c02070b0304060506150406020d0f091502010207060507030605010c1101051c02090f0f061e0c2401060e090a050a110409060302130504 79
    0x58211004100c09841c01c0d0761001340200d81d041000c8001260348810340c00690300c10102582d039510142071034201c070002c0041c3c0d111024108074484e8502c400580300031820307135006507006001048414030000141d080100301d8000103c0100f01004000c28012180c010b00c1c001d103000e0f215000302251003410140548964020743e4050703441000c041e01e09030302c5800e40b40303003009452814810941e181c407460182e001e0b025070342c4070040c1e401140c0507003800406c0c860b0a030080d5090900300041860000081c0080c40182c00241001d04250103248159000b082107444041401402c02d0803200141d4898000b90000701115000f0890003440800300e051031501d1040c14040100000d0038280e40740c1c00c500b011b00103005600f0f2084010f00143c0d24a480810200113110011042e44075100041da08074003801c14164001c004026400ac0051041d456006850b600520001c8001c6502c2c4c1e01c1460400140c0804660070924400001e0001a113268541c402001d991080310101c402c541216070400546405990 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 153243660 1250 153242410 153242413
    0xe0105101a0f0f1803030c1b06130501110f1c02160b04150509041103061302030f0615070b1006030c03060e0a090f0b040609020f030a051002090301110310030c060c05 73
    0x1030b091000d1003400351480e44d8036400030042c40d03200800443d0458100342110086588420f0036400880013041d039940b2100400d43d800790402c400004410029006031207030b1414040c006861110010b030034008550000b45450440744500e146502092400e0b01148211006000f10f4001c0c420b4410001102c8003107030341e074207104e07800c0c14280481c1500c1d0324803441c004400d1140812075544141c4481c000c41c02d44040c101d1619440c2c4c9000317424421051610540d0740401e500c10010404080e80c13103044650071440a41758040310507100d10107070544d807040c4036004c0c4c00c807100300c1c0800200d845001c1c41c1d081a180d103550284000707021400e0030750071364030349005e03a8101c0701004000a001c2d02da03a0b80700d16030003400740c40d40030f0a0000f21f4461207281882514280d40c515220317545c203419818101c800303540c014001c0c0c004001054858032166110251015080421500006c010050f030f5002d404c08615481c0b80700d196607480c00d1601710348985050600c8102c5a201c11b240d40042d0407030080c2000118550480b0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 153244910 1250 153243660 153243667
    0x6010206090a0605070e040501080309041d1b01030f050a05010311010201090c05090603150c0403020f010e10030e0106050418200102030403060c031b180b0a1209060e0105101a0f 78
    0x10f607208060b2100400c03503410000742c04640c01003543d8070b004a5000303180c030300d01840c1d840c04414180300031340f000710020310950040c4002c803101010b030005850040d0f00d1040c05034151b01c214840102c001c3d107090300d01220424100b006000301e815055000f50b040320301c42c41c20480c080002000684c241c40031888090140ba0501200300001d04010307440c00d501030401410b41d0a18050020311107255003080c1e44956821001040034030445c100160100c04102c0309080c060503504c4010005008103001c01544000c00d80c0702c90154040c452300b50010310141078000c0c0184180d07401030801c40318040040d42d0075500101940b5410200154450302d071141480d06030f002d18a02411521620b014005a8483c81c00f050394078043c1503a42d40c10300d0f02884e48460b50350346180e200010401141c0f20385946030844a0002001c1003201c1c58203802c0500c00c3c44103001481d0114021505040c848010549107160304020b50a0100308a030081c0a40300d44410b960036441c00038070b03528070fa95902441d8001c2403150011400c041 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 153246160 1250 153244910 153244913
    0x20706030612030e1302040f0f09091e0501060509090114010504020a05070f030504050904080c061b09010c060f02030703090b010e0411040506370806060f010f26060906010206090a 79
    0x1012400e808640c00750180710105c039520480c1d4101da2082c0e1050400e40d0000005103c8400e00c140c10b0300c000d001082d41480b2038450f68413a4201084100030800d00c050a03400d898041003401e4101d03000900e4014100056464206e0465000c0c0002c01d00d14003540380306000124552815200f51010402179545080c101082580c4200c18510950005e401340801404001099aa0b41c2c51a81c41144524035181c0c03999100024030b0315140740a0110840c1c50291881c0c081d6480884041d10349240d82468150782303a2040781000b000406407000d01c20401d0f0b000008000030250140c0015403407a20440c09811542c0e030780d00702d08030394400c1a100204461404511002c0528254003c150400e100821410301c800d181c561220200800300101102e410300c041d090010b00058407882c800908102d405040c2626080000800c01070f458201136040c085046601d068440c42030890003200080e079101000081c1c0e01c6100340c5075140c42110001c0c8940380f43c20005030f007548042110341c01101684010240c03d00d13607 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 153247410 1250 153246160 153246167
    0x60f04080f04030c1401020109031718030d05150907082a07030f030614010c0f030513030f02090a110d270f0b0702060402030706030b210303060102070603061203 71
    0x54000c0d1240003050000d0180c10000c1c9004000440c419142016110318208850310b03200c1d50300700d0540c1564542107050010070340017814039a07044e00102c0d9104080e40e4003030b80d44480c00180313003044015110100d410000019180c0c410750152410121000d185c001060400ca6440003c55010700021402c2001c43d00314448001c0c40b010804030054000c0300034100000c285d209821100094002420515080301900c1c1c06100f80c9028040048a0300d00c80e40c05603001a1424904082c014480300301d4080641c1458814400d403810000600b0303502c00403640c0c0e810403200149810310103030702c24030b0240d0106810071004d10134400c0a41d000900350782000840050b180080116002418030788070070101d0358002010721144a110b50384a035180000200c03a506091300755481c024820400c1d03600002c00c0c000960b9001491804941c039600d00400d829001901044840070010300c00010903040b00c070199407582c4084040d520810083c0d01312000c4d82c0d50790004900741c40d0345100303084516080898910110f8072 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 153248660 1250 153247410 153247441
    0x180e09160b0a0c030e04020a0c02090105030712020f030a0c0b0d0c02010c0c080a030e031b0609030405061903090803190b030c1f0315080c0102100c08070813020d0b101706 75
    0x80c03d1241d10750b00c5150111b4140e902c06100340c000910341d080010110b20306441c80038090481900180a954100040703071100f003c0408000c1c0c0705140c60082c4907000d95041115030110355008503c100340681e203c40081c140d0b0458884094014107000c85500b105205104002d11700b02c456481090040341038440e0078507948a60703009400c06843d909808407007074003040246405a0011407181689400c0403016041110152012110f900104410031580d601c0b64142d03005400b4040c80341c811003076031840980c02840150801070035020040108040c4000ba6582c41d0703010b0144002c1441410003080c20961940030742c2100380e620000c0042210424100c0342e0341c2101091003420300007200c42000001002c641d40d10340c0100da403603000050202055905202c1400060017042060081a00d0210003a2a24200901c0e0380e0801000030700088417070010661580c181500a40316002c3c081440c184260f150204448200116404000004162411420080603044c451014081e02c8e2603840e070143c001d20 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 153249910 1250 153248660 153248663
    0x306040f0606050a0e010c260412080307090603050609010317120411030106050d210e06030a060603060b040302031203101a0306010306060c05061303180e09160b0a0c 73
    0x1503542030440500d01041c8501c0c030251400c2c0d21030700d8585064801c01410181405030050410207a1007100340011116401e250a46c3c0441c441d44542e04c03080f4035101c009002e16408000e5520011303403100b050040e950b009501a440e507941e60b4045a03120f03201a401c1c0c41054920a80001c4000c00400208002403401200300111b14900da01e070116089846040d41010790f0191031400d40e6a0343c5440c01d150034030540d8000c00003501c007844034ad44c0c19280c07186000c002101281110501d034108008040c403030740503000500030041c2100e8503410814202c800401c02e03409031001103860443c02003403e402c1a015141101e500074001c0a10385205a000b1015400c060300301c511460804601141404d03800403110840342e45c13862104e4032840e0280c001006d807221644603078103000000e42151301081d8007003132144c2d01c0f041c030050341007084042c2d250888d02e03040e8503104480c0000302c803440880c00c07500419155004020134000c550004050001503203140445102d0002d009600300103420075207006140321000e5030b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 153251160 1250 153249910 153249919
    0x30d0506040b0d0c050a081f020a020a080f030f010602010e0d181a07050721080a121506030e0102090603010e04081c0b030105070309050303070e0a080a060b0111160b0306 75
    0x2e40880c0450081c0d5003c40d02195402c04401c424881030410035500c500406141004020402c2c25100c0044030001d00c0314000300d0950009120018280204843d9000e594050f8101d0390b0340346444002001500113660a01a00d50060000181c0920501540050880000180079002c510388410b445545204c046031403207509104000440d140384d26040000124480c000c0c075644e69071450021304050b140d401c5000c01d0810f00407000e5002403002d4040410340c0d8001101555141000b109482c1c1018008080d1407050a041031900300702d06140d000c0d070440d41907403010b00002e2124001c02c0d090780180c080c0250480c1040c0010011403140c84000c58100d8040c480041c900700c034040f000f041199203d038011000903214014280c0d46d003424420b1640c4210a0b1808100c588810f0b640c40d9140c0c030000d0503040c2088101c0d030043c202503541007880350040802c5030496080003c00d18054001e0b050034280280441c82829000c0109800440d60601d6039554500000c111414000c09050301d4001501c101d400c0f = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 153252410 1250 153251160 153251171
    0x1119030606090b0a0f1a0d020c060702070503010c08190504020d050f01090b01060e0a06030e12040e070f080f0726040c031104090804120602070503040612061502030d050604 76
    0xc50914031940300030380304410780400c140d07010500b0b21040c114141d0000c0781140c4074000c00c000044042000c21900e90031031180e42d80c1c0c0c0314201c1f0000064000d008a070301c20ba015140500548c0c035000600301080f07500950003803101d540720324015103100c84112603020000518441802c00c2e4511a40800da103e4801044c1d500e201c21039468491070304045444036a01ca0f07645101d200d05001241c07074014010901c6103004515500c105c0b020400701c014900c00c003801d01d521039402d202440350a2140040181d10080c416880eaa6101170380390550700290740e03030800301d02d500c02e43d01c01803845021200e1040080c100c9104441c0c803180d40031681c180103030302d1590301c1210071203801c54207a04500655000340e02801d903914405003541403d440705005145e84c47d108514113020200040c95003003c0d14100d8051003415041410356080c03c0000e8402c000c1c005140780000100070508a42260f070f444884c1911784001c0001c2e54440b8800b4403c03541900321344d000341c1c1c002e0108032210303002e54018035031241000d04040784 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 153253660 1250 153252410 153252413
    0x70302070f03030302091801120f02030c06070302011e060303051917090c09180d03090507030503070b0a111204020f040e01110a082a0a0315121a0103111903 69
    0x40300e501e0b600110002900010307050000d24243c107004d0300c005000300c04e0451b1940340000d0722608100a4900602103406c95085900b9590107000400b04100040d00341c660b90102442c000b030090001c007140030b602d0420400340308140c42c0c0b40e201d40403e8a601d600e4807071a185080b07202502d810012203000d41085607208403440d601d4410910140034900140040903801d10f00000c00c07643c458018413582e2010f1140e42c001601d0240000c0409801026082c005071030318103424068140502600041c0c498407001800c1c20401030302d1501107200360000c079810801d5400c1c450900c0e0701d030f1050088403a000a4083c000c6409441d0002c00d0100d405d4004100140501d02d03039045a0a55007000c0001c0d8006001042e046000d0340c100b43c0b0b035a409060409007a0104055107095801e45014801804208030301080e18090346000c0d9014940c100c89120203405159030b110b020f130581d041c0741d0904032180c050b20411148800d070481ca41d20306031f0703500c03e614920650341e61003400605507940c8400340300e20b816240e0020 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 153254910 1250 153253660 153253679
    0x3060601050708131403010f0b01081f08060411031216060b13060f0503010b0108091203280605010933020c12010b0f0a0f0909030e040e06100f060c060207030207 71
    0x10041c852040025540e0305e09508040c212165452004001d0b810404a008681e0380b00c0700880d071281206007441d04907115508428800c01c00741e001001d00d403240c1c005020a0007801038003410340320001c6048900c04034400c1b402c04128002c401a0040d500014560f510010b0305076000030205280c00b07400303c00a142c00030001d03025680303103030f02081d86680301c42018411820207000d40c10407030100303091015141c14002e17411507a0380901c0034000e001c42307000b101244031801c001060860fa0300310700308400d000100720710124005080500c0390501188540b680060420342c80380607440300c500101108000170446001c110018200c03c0280c4046018502050300c070b41e41c90798181c1750011601400080d007545910144201c00c0f042e04079540c07007010112410010680525100c0701a202104030114041010f40340503100392550101c0150320030b091680520400c1c01c0000c0030391181200b0902d040900e81e60712000300b041c032128000d41d40050102c00c44c00020070582d40041542900c24812220030559464118 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 153256160 1250 153254910 153254947
    0x1602030f0901120908120405160810021317011a090613050405030d1a0f060f030a1806020c0604110604060e0f0a09150303030b19180603291503060601050708 69
    0x3106c052000d8080c0014480104010016102c0041c4c0b612100c9080c4040c06070344052860440755401c1e000151002c0d00484000761000074010205403a000041e003070f59180c0a0f000e405d80301c5000c03812840c0134000516000385440c0c010031028242c01c80030100500e1040182c5802002035440d44010081800150002d1103010356001801d00e0810303110361a6410030000c188400e0352140b1030030007484506a80c00380c3c4002c60703401140310030000540504110014103202e10b40030028110510202c0c07501141440031522034843c03441b91400a03121181642001031034091402a000014501c00c1c94068a04001140502d001001019001588c0d5a0032000040d41c02000c54881410103c0c0d42c100f003015058000c0b240407100442c0c401141c0515515071000c443c13224400c011218182000c14402e031042d50344450b020f19040f0822800340d00700b4207807a0001c0043c19100b0f440003003100002a20800f0000f480710000180200508040d8035041c0c011a0145c20280080d41c030701c00200083c400f10480c5c0c4018 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 153257410 1250 153256160 153256177
    0x506090d02150a020f0304080706081305011404060c09080c15070b01091b03110d0c0309120e1207030f030e01021c020715170103080c030409060b031602030f0901120908 74
    0x55560358a0f80d0300002d003000a41503d022003544280418010400041840320a98000d450409495540c00c0c540350300014886001902d80d5181054540c0d641c540170403100e11440c01000140304030094890220380b40600761141e481c498210125907001071400c50307006e450184032000c140e800d10b113480c0c80701c0005100a07440f00c00c400365596010101c0207c1e024441540b20210309040000700c0e00c00300030f001684151440c0c500302503924800c1c403e0260096024059050700b0104c81d0082040300e100151a1403140c40b81d90b8890741c1c9441c21032044000c0081c0000580b580300d641c203400401c840d58256900390b01f580400e81580920302c801e00600c1402c0d182d0811040082e0300514020303140c601004400404805200300304100030740f60703c1e0012604480541103940c4020102d948616840f00e01e425400b03160400f002e002e0418900050190980d0045d5004907071445841c503150501c0c42c0242d80e81e1054010250404c602405805c00c2913020b0340000803d01865140406c1065440d034070b041190384000c50 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 153258660 1250 153257410 153257449
    0x9090a02130b07110f0109090903030b011e17060a03021807030c050705060f181203010f05040c09090b060d06120b0906060d0b090c09090a050c0d020a0506090d02 71
    0x1140d00c0712481c4910014010000c15940300d2902101d42c0f181140a504818107038080d55845182c004283d00c00c480700401494603003000c11020b1058074008002c2d01141d030030240040c40c1c2c41070100c8008a01030400c540721041c0d40700d2a02d400c44001d42c4120f4294000c000641c0318004200000158440c0e80d44544094940c0071121158642814064222806050324804201c0244001c400050700090b5003030308144028004d00c051758031030340c240f400c044000140000341c2c00303007a64101a114280d006141600d030006e148514854841c1c080c4000c845801921900183c2c020340d081102044e40e40c03001c43d820901500c45842c14200300303006000d540582c3c0c043c1c00252010403040c018042a0510560048003843c0070345101c0c01e200000032900b40300c61304c0c080c248111540104406103420480310f10003c13009000f05410f40b505403189512400d0603a410798203801001500f642c07510707003245440b520a41c020b002134895420841804042e800074610b40e500004864100030142e91210368a400c42d80d00e000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 153259910 1250 153258660 153258667
    0x70e180a05070617010f0303050304061104120c0b0f12150d080703030b04050601210207050109050c090a0522080904110301090e03030906040620040b0a080106050304050d0f0509090a02 81
    0x5002807909000e00042205800c00134010700c0a2070210500e20100c03030301880c00740e841e62031f681841c1e0014030311800090300324040050700156040707850726101101030007481a6081240d480204c25490b00ca00100020300000800a4410041d5a841020303000f008074004402060b11400c0400d04403107481c142600d01a4022803540105640b501901101000c00c0e1001d11260a000c40060321903100d1980c66a0442d4607040075046091a0780c1c1650f500d02c1c1c000c0000d00484006080a90b11444d1408240c0d000d00c1410b00010f5490101c1c0c000c55026407400d0b54441d103000c800790300342907191801c80e0003101d00c1c50042002d4000c076622400f41301b844988804689a5a51405c04004122015444099482e40085c004c10850b690045151540160003002c081681d0070460030b00510f007030010205854040c0042801300318075203540003401000d10a070b00c070aa070598035000150b40d14001110010a40c0c2c2c000c41948411070300c10308940158001070b0600d141040d6418000860280c0c00301e41c0b40300504e6001c07 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 153261160 1250 153259910 153259919
    0xf0605060a0506070c0302040c03090213020307140705060c0a050c010507080a0c0c02060706050c07021008070207051c022103040305011b0e13020a05070803090109050c01050c070e180a0507 83
    0x15a405070040c40200d4a2502c0c2c28511780c1c5d103d0f009029032001a225560340d00c1d24414290003900200401a8000d1242c00100d01d06504103000390016503444002500100c6540803003184001128550380d0000003e080c40e42c2c1e074510444456100c41d800200b042000e100e805040202401903074019403058403031403814506494020101c8242c1c0311064104a480316028000d40c5400c811100e0142e00702002003a85d50b60b40d00445440d10480380000e404c0b401050242d14015400403074903008500c00c0d802d80b0001542d031400c0000c100c00c0101c03001000f40d01c000540c0018a0b01030080c5210000e9038110030744558440140c18103542181e0b20660315651180c03a9908034108165031094000020706158900014600c01b081c1818041c02a4100781a07000942610060142007551241a440703d800e50ba00d18080c0012400380800b860125514450042220410340c000c0e002c0d0f582c185000c5009151192414803480055000602204c941042c00c8440f00c0c010396052107403448842c042c500404990b40341 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 153262410 1250 153261160 153261169
    0x702220c020d1d0103050c1209150a3b060903130807150f020705030a0f05011419090303180c030302250506070809090115030b1807080c070f060506 65
    0x400d04070b02c00c12801c4085076803181c02440408004103c01c2c030b030019280d030790300100f881c26205600c411500c5101c508100209003800148000001440b001c04d40c41c0707611103249030001d489031001500b2040e01c0d1240320f0403815102c10062565000360040030720342402151b0045c2d0070000150b491303a2035600300003101020080700c100094006d110080040050502d400000040c0f2a4045600d1381000400c101030f20200344204003541c0607100040c04d40d04401405d1400c4001e4204e045011602c1f9420b24590295a014030441c3c2da22850741d04010f5114040250300b400700030448403404a0502d55220020f407000038092034084480da2107154990801420340c240a441c01c1545560a00070000603010b460f205000000e500044950175600c0c0c5450f1845494025582d005d103d1140390010104800000e03c1c0c241095103156802103138800b0040e408003403052007449801882c0c49a169020300002c203046904c0383c451035901c000501c00c25410032055644402130104d1180c0191445600d600c1402983e290 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 153263660 1250 153262410 153262423
    0x21306030b21070b1303060c030501051e03070303110f011805072108030403090b0703021b030106030308010b0a090b19081006020a03030c0e06040803040911070f06020702220c02 78
    0x200c210340ca0003102c0c82c1c00340707156550805000700080e402010410714a007000050014000c4c41d40712505200d584529000103008002c2441a14820310000e80281d2000c5e05448440c40300017009400307400e02e10708540f000c1d01c002d03202c1922404148500305542d11010002c1c441c84002e043e008188284110446c1080b070300d41005604241c00c20300311040445040c1c105d000c25000321a600110172038482d070b11414252104440e55101100340700c40054204201036012507541c02c250000c4c2b03041c84d40201c1913424542201e9640c040240440c0c0100018401040d9240181c41c102c1c07030500d03100d0000d54865041400641150f010b2042511200040500c11500000131503800b5540c1000c0340c1800e0300c0c204001f96980d9a12030003034149981e4124040025100f1b0614980c030384006850507949030340d55010300c2d64035401361244c0c000540c90f1212002261000004680d0200d8106503c690301560b00d8540d00000c0d0311145c0200d03444581001400303080074038494010124520000001034404c1c0003103000e400c200 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 153264910 1250 153263660 153263689
    0xa050a060b060306030601090e0c0901080d030609060b0d020d02130611120f0909040c030b070504080124030b100f0e0708070e0618031005251404030305030703021306030b 75
    0x10f004004841d20005180750442c1ca0740400858940300c52021f650800024852464202080400102e1300b0a000683c1110045c0956002c10005946903500421903c150040c1800c13110100042c0354040348540150040c45081c003130061411001c1d480e08151180c013644060003090b0780020320294181d0900c040c861420440d13050a240c074841e410000034910070519501e2054104001103818014000c9a010243da84034243e8506420004005401e9030000d102f144019804e090000d50201410744074611a21030030034203000700c1c3d400c41d5200c1c000c5180c01004039060340d4200300000703a0314010845d010003c01e800c03422141c0b1400c3c1400001c0054400802c500d0030300c5806c034103100b02d82d102d031411948481401c40c2407400c41c0c114940001e0402e51540300c0c4205550401c0b043c00340740c3e1103071100186e03003800c809100e6201c25180070b010f94050080c1c0c1043e201181c1c06010820210b802100156880516807600520b0304010030900e41010030b00d500001d0011750307501020641e5041c059180010302 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 153266160 1250 153264910 153264919
    0x13031205161202070206270909010f0f0905030d110c0a03030c0f170402040f0b0607050106050916122d0e06070e0f0d020f0a0909030e040203071b140a050a060b 70
    0x4c000d503000300d205845000d0a002400541da68078207501400850012200c074001402e001d0300f4240201d0b864041c214050050714400e01e40b0200e10320414482c40354280a40d4020003860424180d2034840000302034080c03409078402d0042048280c1c0030000d1000c1c0071144e209480001d1006582a4020244052903661905008070b610941034007254881c0401d0384183d04442c00f040d07410221340003501621704444807940151000c28aa03080040c1900b115055071416680b110840d074904410150071240301c00f681e00460108841e0702c819402c036070850042415100300e14100d02c0c4a801c250880410111015040303666a0303809502181420f202c080c4d00080a881e005c034190002c000001c4104040765145841520b00038617a408645401d4040c28129078000c0c418001a5030b100310b0755018025031442200000c030102811015440c213442980e000f61400d9451107410054411f88160061090505482014103d524800211810811584a14828002f90116034003e240030400d5989140625106 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 153267410 1250 153266160 153266167
    0xa031a040b18030d1d0703080301080105060609060d0216150f0e0f0c010804020d0218041104050c191103180301060f080c2205070503190c0813031205161202 69
    0x2100302c00002c0c1c80300300c222114001903c4030407105043c907010030b0905e02ca1840c01000f8000082c40101c0010f98100d56281c8024443ca96812081081c1c3d403003008991a03000c0d000740842050300409a024240c00d08600441c40303158070441d21090110400c110390190016280c40340303090350f10141e005014000882400900400c000c494000c2d444000204007541040310720070014040d903890380002410142c01505034401e0b95800400c1003000b00046130142d5003220014103c0c1140c3c2400d00c83e0500c140080d103180d0703051600021181c0390345045a4031000030010039500d00900d21070180001c04040340c507201e03c88603080c04a818103094501039130168030f81250441c010007007814007241c1d1802d0600121030007440c3c2c05440d903036071220304480a41044a030345000104031089070448011800303005140d01c94400c100120010100740c0d0201c440b2040004c482d0310200343d0720183d08111070203681c4039040001c3c034820101010b80445034110703804c0b0749103230030201e8850000d030300003416a9440c8441c2c1d400350700c1c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 153268660 1250 153267410 153267451
    0x4090201021e0106170c01090806250509040507110f06011d0601020304320d15050c0d0926040807180603020d031211090a0b03060a031a040b 62
    0x4071000c9034506085034000348540e062a100d402e5100501500701c00184440e082c20700403074a03650f610b1110161f070105004200c0461082000140300b446031650120000a04000c5081d111003190264488020b0181c14044003049036a03038000d1900c41d01084ea5008215016907210614000c41c03210100002e0b00081c005100d00302004104031041c1c00c0b003c4441942e601c135000104d140d44074961005410f80c400201d03d0100c03c0b0865004081c40c0c61507903007850714058031010804150240d010080a0750030407240024149a5908003580c80102c0c50b108a040c030951810720302c01d40d841c01e0011101c104628800c0c4a1074400d032924500c41342220070240f403c1034144009259680c140b4011300d41070b0041c0004808c5116165009200a035a01420030340d2252800c1c0717006803800b0303800004516941c2c02e114400f03400000c031200360b440403e40104181c200c5440c0982c003503032650010704410703000b002e00740001c07001c80e00d541c1c0c000030b8107007e402510005203001c1c101420003150280068881c8070145a0448 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 153269910 1250 153268660 153268663
    0xa0603090b06040e0f060a0504030e0603010b190504050a0e010312030c09060c150e0f01050c13030b0a020d0e07090e0303011d09070f0602070504060506030f2802030a02090f0409020102 81
    0x241e0000d0241e0300058161006004549805c0707011031904801c0c0315a00c1004419030803038020500851098491a10225500d03040200c0e82c002400389040264050220340e00300c40c0c440840c10007503000340c100686020389a8000c189942c032079411032001880074500420402606501c001c0e1300b05524a810031818101440c0241a0074031840740400b00712180501009120440005980b140045401009030122510074203448159000010300203521300310015014250348012201d01580700711903003280a0031035070703440801c460140103003200035400d000c081c20121091040360f201020000003054842d24080707030788055a4145054010a800c24401005641110030091905181c64010400c07540d071001f031130f1840c0c41410340c4910b401000207103000a5898004c5901000e0300c80a403028002c076501e40003400764600c4299140c4d120802c01000241000503aa980c0d034a00b004034070b1001034040c45840403401a0381050700c03502401d6030700261650f07451401d01c0e030080c5403030002c0e40c06000511716030300040e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 153271160 1250 153269910 153269933
    0xa02040509060907050409020a270f061b050106031a0718030b0702150a060f0f080c0105090319030503071e0e0907030204030609080301050a1e0506070c1d060a060309 73
    0xb14010340d4400007203030420380100255009401c0703040d01107489041c2401c0007000f003041360b1326a040c0da85000c010044c0c0c00c50303155403040030769000000e00240d451500d5001c541c54690b55020b00c4040c1034174a805000144203000302c7c0e000318080c0c0d0483d002c0a5200410a050f66809404002484001c0e45414420b02c3c51800030310450360030062905045d07481481c180e090008070404131200905000401114030800d50081b01a02e0500f80c0c0001080e4841150144c80e500d94007a02156901009008440e03601c13540082c14003e070080d0a5405030009031b54030805000121208801082d404020801c1c44d0364002e1660310100d010b00700c0180c42c01207420018003441030442d080d130b0040035038100040c145406901107800035175000754100520319181c18841c10301d400c00e014291040f02e80310f00010709004002d0b0000740c41c0c0c0000c4032103100140f80c10100f0027a58004501220070591400c00050f0307488400040100182540ca0703201c4991600008204201000382c1140c8241480c041d61840850040180d0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 153272410 1250 153271160 153271171
    0x705180607080d02160b0601020c0d02040b0a0503070e0609060109060c02040b120d0c0b0c0310060c020301110c0307050c010201110a050318010c02030c010b1804082101080706080a02040509 83
    0x560765181030314180b4a0a0f40314140561114a00014800201450300c07541c01d036030140180303650f018039160346004903218214204442c0c5c2c030600c4c0c0788590300946131650000011110080c8240b00880e550001b09080c480e0707950145289204040801407541404d0340010ba00c0035007460f000302c5990400348003904500003000040d02469407110940c2300c0b80c45200c411003103240d15104841d01041c0c8410024500310705050300f161040d4146010450301005101a280242000b2142d0122541040801c0b9400303000ca07242640d0540d00c0701008a20f44040302c00500340c411080001c0d560b518040c0c18903e00e010b0303000114504580c9006240c03c0c1400891041d10551074040c6840baa681e00d59940a04c0482c00f20355210005510300724412810303e40020080115407100070080c04210358140411000032130100600c08004044000107002801c5940188600402000588480c000e83c00100100480c240c00829099006210a1140580144c6015403040c15814294905401c00b03001c51007a00700a0310 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 153273660 1250 153272410 153272419
    0x110c030304030206270a0f050102190b041403070219151d0d03020312010801150807050105040e0c19050406030f06050d030f05041e0f0e0f041506030803040506010806070518 76
    0x242603e10b0341085441150880e4006c05000c080d85d1500790001800e001d41c40b9050151003580341c1c000260340c0c01210b840c900c0d0707040a1180c07503642e11522464001c1c00d000d0803080c1036000c10000e000050391070f240851821019000804002828405080040c1da16030051405100f440e50a090805200c42c00803598240151941c88486060f4641640703180201644c07c1000d00c10540041a940c10540c03086510b4901d000704040d40654a50080e03880300c20600400c0d000650410043c051020140d20319600495810030940c80c0c0300910781070400c480c0b0001178542c009840040e04201482e410f0155004103110210100300c0d9070300d000300058920340119002030501621200d0000400e000b1000c2c2d030000c00c40c074080c40c40741941d0100b052080d10100d000f440d00b580804031001c0380d042c6030154cc45100303529122983c541501e898559000c41d540901d503565010351590400700016006501031405144510020006941040c2e012820b00c00010711800c00c20509101d1924001113040b01050354640aa4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 153274910 1250 153273660 153273697
    0xc0b030f0c180f0f0a0312030606050c0607030b0a030b07080403020606030c0919150602010f0f09050607031d0102040e060405150105030c070512220f0f09180b07110c030304030206 79
    0xf02140156001220440d4802030510000090010082540e00d0004c10380e030b000c00005032584c20076122030080c07180741d8040c2c1e0300400000b07004901a9000c0344544400620001c54195255519106c4601c203d81c880c0000303454406010805070100869a042002107014100c88180f40c00810803984000341120400d5010012901f1508000c6d40a04500300101042120554543c84041d000e000302150034007044d8600444102151154840c0940107680f21024219903140e28800303c0241040040390b00d10701d1a21044032000c8202440140018030106501c0b665a180a070100412520020130f10400480342140e00703c01a80c0c4442201e43c0000d110041e1a26180c0c0b07420040c2c034080d910400c4c80c8010000080a14402002002c24034145040c2d14540402c0c6444190100d40b040d028803c0450800e440c020a110864164000e0b00609a1848000d000c415840c0c480705079040c0c0561300b4001044001802c036108860a0081602c01182500114a030901c3c55020030458451700701845051490072 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 153276160 1250 153274910 153274939
    0x2031209130b19030f030824010804020109051012060b0304030c0b07020f19120207060210020703030b0904030801050312031302010807020a0f1506080a0c0302040207020d0c0b030f0c18 81
    0x4412040d0714a05881c60640345613120301d01261400008003055000c601c0c1c01c0006032001031180200104503d0411141051548580064540820140049040c00440c480c00715280c4c807a480103200c4c111843d500da20f00c1301c0340c4029040440d41e46403c245c0d080d4204104210100390080e01c844445903000813010106d40e41c41c01c04034203212408205c05440e0040d088101302c1004040c3d081100c10b80560300c403a548409001040c0d80d2100c3c03611403e030140e0230442100b042104284d01034000680613003004118541c00fa00000d040500032581140442c05400051202e42010840402504a800161031440c100114191420410100024100100300c400100c0d00392080c001084191341c454020035029801d45031140345400b904031114005450498009032400f40001d600100c1d640000d481200c1c10704640038400a540190405c0e6008299000c149000500b103d040400034040511a26207030b007800c50f451002c051703009d003070205404418448003258502ca0811300180706000c0f00c0c1d04c40c104810 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 153277410 1250 153276160 153276169
    0x31d030c030708070c0306060f170c01210225060c05070302030d110c031611030106030c090e0f030f04090c0914040906061502070e0c190e010212041202031209130b 72
    0x541004103012304001c0001100b0300100301c40c006035007906841c0300508000c606e0f04d65440005522060025100c0702c1612604480c40414002c01c0d5202a00540f412a80c2c88a06501c040c0c0705080d541402390340c4c41c0d80c0c0203100d0b048c070074401c074444140392291404003607072002507990041260740011b0755550170686040300d445074102c4000b44000c2c0c2c1681e07280c3d1705102185005050080c0309071010751485164030450718041c40ba102c1500d07880880b0105081c207000030a80240300544c0c1421140c41040400c01c400c500420241c01c0301c290010005070b8550502c03003020103540c9071208400902641c1101480700c07020071000c01082c41026503000030050950b00b44580a0091307603115450325040d00031100c1c50540c0c08903800090320b05807000c1c0e501079207611516007054411800225103000410800340c40380ba20541191240440510407203219405099481c00a44c0c880c0d400340d10100309980981e003c5090500016080001c02454035091060150108001407d10385500d419280e40301c1078011603a68 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 153278660 1250 153277410 153277433
    0x106142203030c0b06040c021b040f060f062d0e130f0b0a080a05120a02150c19030b060406050d060e0103060b0306090a1a070c05060403031d030c03070807 68
    0x40003140118a5600d0402901042c2100307826a40d03004501c0015103142002c2c0205110b00010b070340102601d0346610703241e0038401d0006210030f0f445521880354118080043c0580e8014294440842d140c0303a24144001d071410340c3ca03408003c00070a04000304c020711518407558808260007401c0c1101422030540010780f45242012034440441d2805007940b001459a81c0305804200d01070b111801c0d00d60300d40544540d100d0803a81c0040a562120810200c05041000a4403040c80d1030300407190740440d1041c080c59025822688881a10b00208a271001c004a141c020904001d13541410420200d50070003081c40342c400d40c050101803150025100c00d07031840d254840c80c01000301201900d90780d40c603454a00301501446008610a11544010441c103070008140e4108895009600072002414048611961103008001e02c09011620100741c0200d0380510144d03105511030b65000607030b8590032584c8850300c2c49601485040354018021550b901400004481c000c5400c01c05250300c034415840c05103485d58 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 153279910 1250 153278660 153278707
    0x60c021e060612010e0601080d09060e100509031c0c0c05120705100905090c0903010506100507261206030f0f06040b090a08040f09050c030f041101050d1401030b090105010614 77
    0x800c1e0300c00060388e181c1c0850a140c1c1c080c41561411070807503403a0002c43c4c90b100441003059201e00044459402c080c0120010102140040c0a84071240c10280609586094086da01d40c046103036030201c5020805040b1000002d4801111040c0c4c1707480e08102c5490b51100346000d81c0c1c0c0228000301c0b4694085000f1081c2c1d80080000030a50003051602c9001c140a035048520b003035010b9800c03e00454030304d260000e4000071401260348c44908020060700d90800650703030f60b81081c401041040c640ca01c65400d130380013068000c0c28502407002d141408014580381c00380140400079550400303855240d62890110f406da82154101400c1012a11031301c18071400d0140c0207000501075540007800007a00101c40c4808000c564040104002941e1450140101c5100494490b0000030400c000a4005014400440b07580762041c9051401e007009206034904441c0419a1081d00c0c0e10720400400400842820060340100008001d101d903514103180504000d280c1d5030448282c21000c6101c480b6910000740068051 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 153281160 1250 153279910 153279913
    0xa08040201180b130e0f04060908120106050c07060918020d0b0306071806020c010e01050a09050402030a02070b01050303120412050d050c0d05090106141c080304060c021e060612010e 80
    0x740d66010982402d038043c590740084084d0700d640000d986030345400e2851103400caa0400e02090742d200d595900003013555a4007101c154509105c0d2003900c1c01d0008119010300b4140d200e45a460012412461505600354480c5c8104181070354140210b1014039040650141d000c8009030b100c401180c8a000500300307203003e0b10340500c038850800c945240d01610850307038038151000c1140200e07103d0b14101e07140e5202e64140c501040b60200141c81c154450002401115004c2c41c000c0e41c4e25072a10b000809a07801aa0141c0000e0703000b0900e14248044200918014182200150b01c0c0c1180d88000c011042d030010f101400024565403400c44090080f402c9896161703d010741042145003c0800204613003000e20107402d09840c2070300003101440144940000c1e922210308569014040c1010030004903408265000e40c180500400c03c001410030b0302070750095100b4600880c003141c02200007031500307010801c507442240345c00c20250101100401c28a0308204143d0300c080030401c001e40c1c22405001c603220510881d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 153282410 1250 153281160 153281207
    0x510050f04450b0103020105030403050c0708030a030c180e0606040b03090a11060a08010e06120a050309010206060d0c030602030a0902090a0e070506040b0d0b030a02030d270b0a08040201 82
    0x82c882c1101c1c0c5410101c041d490900308490850368401042c40340d450010314035038065005201560040020711380c40361180ca8100d00d80f0310300c404400d042015541c0f00166590000c90303c0e1002d0381d010f0262809000c094540b641c1c00710084103408031725044605c1619000444400414101d850303810071a80581501c0003099503a0614040490303881e5820300041e00c5071a0b41d03440602e000d281803811201402c0316946c40300100c0e4240b003240108074001514503680310b282d14204c3c0f16200340c03d122204070070307004502840c0c8070f0b1103030400a070600700014030b070b58850242400c0b81c0340000c2c0b545018609590f00314030f00603126901c1c034900a00901c514140a94820044410071010340269049240d00c582c124042c2c0b03000580e901c0c240320309030149002c2d030700c1ca0715801d11441d03000403841c2e4028060400e008080ba01500e0194020a00b00903c04024000103035040f80200c00c2d001001d40036440c00c05a0b849c0b203422651510aa4080070301415240d0b00800c08401c01041c29a07101d01200312030120242c1c0001c06 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 153283660 1250 153282410 153282461
    0x1e0c0b10050301060b0f09040c02011b030212060105130308220311010909020901230403060c0801090b0102030405010c0209100503010f06061e081303140a0302040305010f0510050f04 80
    0x8039814031805100f5800c010010880c0c0307540c1d40c19034280300070180031507092401403c200009400080e01c14001c640d602c0400691b0440782d85c0d11081101400d4030016a2802000c0c0551700903100204106d060150811003003050003091880d0340112504280c0941c1c03150710015207006181c002c03004110b003e001415001c402d0040c4105140c09081098880d040880d0740d80f4010016805442001408030707000c41c5080d050755001c50f44218191081413003e034549601d07a5180f404480361003040c031001964600c010b0100c00910310030715504d180e09000940c2001c3c40d00000030305c242120341000780190306a20101d0a01200c6c2a040400780c500103009100d003808107070b001001054244540300005100c40883d515900da6100c0c00c000d40c0403542d0b240302d40c0344e5038a1507000280c41034810440411148140303a01c403105180c0c000d000303140100e82d030242e55a440c600b8124292010188190030355460501400f040c1c04030404c0d10000c07104180d40300c0c100c0303400442c0010018181080c4180301c0501c0100c0569 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 153284910 1250 153283660 153283681
    0xf050313090c02060703150b070c030b07020a03080f0910111303030f02010f050c0909090a120c11010809100b0a0b07230706050304020f0a03020301140901050c0a1e0c0b 74
    0x140c40c40b00c0d50308695481d81c03401000c0301034a046c48141050586c003100300f4015840c00d40000c086090113402e14038030b40360703503650350400c5100e0072501c03d00181c00101c21101015805462103030415250f000c0d0081d24240329115903268460440045c0d071441c0e980d4481500b941280065a07074880d4120a1920381d00c2c1ea1b414060049011681c076003005519015017049208030303521900e800b0348a01052142413190100074481540405085a8924800e1400c0440000e48079103d100522005681d800c0345075a5a01c0e03d8403201030328070704440c10302054408004410100051803000710948101c0030a1407540710703001c00d400d07030f00030303009014950400142c404c1440143c5c0c8003104000b035180f101001d15600f24045907140d9480340142c05c00541e082001c1009441c10b00c01c0e070700d1070510061900711699a254002400c403008214442c883c517849a040125000d0284100f40d40b2400031a02c40f03240402c0e00c0002800c84200e0303030041101a000c010382c402803d11501c54000c0e2594030007660007003030800d0000c03403 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 153286160 1250 153284910 153284921
    0x30201060303140a0507060507020309061b211806040504060305011b1b0303020706110705010e0f0f0a0312090501020c1c030b06030402010804020312030106180f0f030f05031309 78
    0x1500420b80c155450790b459510303403044562410031170b640e66003405855a80d01c8041c0c000a45201c00314403052014480c00e0355510018800054101d00007d1505d11490600c1e0400c40c0c1c81500558203070075580c90034000d044c0d440403506110301302114a81c8c0305200324000703000350041340c10048d002880c000b008010002c05501115050b42001c280304040c210f503600886000e41090000880e0701c3c56803000000007030003500680352140c422031000c42d505803004e8603803c40d42c01051050340c039691622100c0c1e40c3e180c010b011041d442c01a00c40076203400858000303060755840386000003c08000c50310b01400c260105a038007103c0704d1070303005009541c1c0300300107840241d1b90002c0f423400204030719207030100c9002d0754000d20038040580000f8001c54115900e0b50019203020400420507070f0140112640d503c2c0c6d4184070f00040d40602100e460304410a00f200c0191100488540c02114500c04646d42c18070004107a540050204d130360002064480f54424a0440d046000340c3c444a21042e401c0a0082003da1554204 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 153287410 1250 153286160 153286163
    0x70302070e090102040f17031902010204031703060112090203030910030e160608010806010e0106140c060a0518010b0901030b060d050d2610031104180c05040c110d08041a040302010603 81
    0x8840c1940e440d074070b0b4a121038805620420b00c41e0700400492710320202c65019155280c141e0b000060406503203032942d9031181c01080000b402c1800c0001049030940c0c1044045215200000c003c01007058140c0c0400e40e2407044440c081c0c4220114000c410794584203400002924900100361040c0e42d141c0c0c91144032071b07402c2e4010600481d09000011619007000104941220f0720480c0460035a482c01c402038482d5844010002201c4038100031802402104010481c05524445030000f0a0b00d4a1044408020341c0c6680c401402d90605150845503580e0b86060f60540303821000c180c0040d25440c0000d890b070000307960010010300940310b4030140c40da0840300d805040e00c0c80960f101e0000482001050000500321019070020b030380c8480c14004144605c020304c1d10781c5000b0707100244014581c040034030034081d001c1c01210000c4c0b000c82c00b4406400c0500030a16000041c0c240745014030501e965040d22070070012886c60420121100050078010201e803402c00402c02c0c50207100240c2070a060080c00f03000107000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 153288660 1250 153287410 153287429
    0x5010501060809060601030506270f07020a0b0402060a0903021203030604050a2927090c010302030702030a030929040332030a0b03031c140705040308070302070e09010204 75
    0x64030703070140c03540a11500a0002900030744e07880b000150001c14029000c01e400c40000840c5000308044003442c2c1c401c031000800b00c102d80b0f10701200005081c0318018000b01c02c642085031010700040035024800d411981c111401070702e81000e01d60803204070310564400303584030810149420100d0004002940951429541884140c3d0341703402c1c1c00c2c1521086070413805105c00b090980b00707000c1165501d41d26001402030078810260411a151039251a41540328001c00d0042c0d0144500b0007810000c102440000782015425440c00b20710280d240e000e103c225509154452100f4001c000d40c0080310748180700e1014681d840e0700f4400101c40c482d1081200d0031008942c24103d40740080c1c2030345c050002e0360719039040c040040c11740791500f1201a070070107056564001c3d2101c80f440e2b400d03a814006000da902011005040030400e1051a60565401c2100020743c04071140c14014641c1c1e1010458054a0300320150301e64500c3d1a160880c50320358203900490040c45c2c11030900c9581f49040d001041280c3e14143d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 153289910 1250 153288660 153288671
    0xc0102040b0432090601170a1e0504030503010b0c070302030102070303020a18150c02030304030203190b07050405010905010309051f02031b0f0d18050a0303050709080613030810210501 81
    0x4414504030400c0c0e08083e08000c081409464443c900100b01c143e110b401071401c000308408001520071100380035900600510344a00b0300350f001c6c04040c8400809850408403e200508098401908a03c01030007a01801c0c400000d100102c03007420407000d0000d50f80070f00215034504080c20000c0c001d4000b514260002400003c000e40a00c2c2050f818a0964001700e10501130404401c00698900d404900c0032601030000b84000400340e541480203c514000003010315505445520349510400383c010001c0080c010248801e20003030f64450301020503034400303003070010310711005080c41c80c90715500b400700022440d16200c0c0c4111140b100d40155000301450719002c02c0c5065040034510050141000d80e0384400700a2050545000340c9401103148414249034900b1268000e4032128188040d091050340030a8030b5005000344e0b203030310440010047c01c000e0b000e0603250801c4401503051512009000d42040385100c042a181082c140b0014010203800903842c1c01004125210103001308071501c256015460003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 153291160 1250 153289910 153289949
    0x2070b0c1501140924040617010b030d08040f080705030d090203120c0a1b0f06030209090f0606071b050303070302150604051003060c0c0b2502030a090e06060c0102040b04 75
    0x882841c0d01c40080203520184d40d600d4540010340b600034106280d0b60b524407501d0301170741c54a201e0040a0060088201c8609a01001c0ca0f8299810b20054602962048064200d041c2e40441065001075101502042800e40c3d81408182800741010140a1f40070000d046182c03c0c0d07999102c00c408910075420781e041c1c0914080b810710309000e15030049286810080c1d0b100c4c00035507803d02c2c0c2d40301c13200000c0d8002801d5486680d42e001e8402d55402040110360700281c45051880d103680300d10380c03002421144440034034080011503414000c100000f007000b0044d1290801e008148101c00300540b002408480d2074420381d04000755503911804640280201c4140440c40a040c1130242c41d00c070341880000241001d142d540c5003401400d0b11541d540800508030b100d03200240d00146400d001d80341a00003145802401184140d1803422090450103542c0104070240c05180c1104544044419030006039102e5a2500c01091880c441c182c2d08440d00d510025001c00e40c0402c0a002d8000d9850098951b0111040b9 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 153292410 1250 153291160 153291179
    0x3010e06010206090708070e042922030903060b0102010605030105070e040e150c130905070c060c08090c0d0618050307050f03031023040509030c0c1c02090702070b0c1501 75
    0x80e000710319054021030302c18030240208078206a00240b00e0804c00062040746158050386805012403120302e6030420050080503c0388107002f6511054040846100099503a801781c00e2902d00d11008105e80d45619401119a00031740c040001410040c00038401440d000c20010300d58850308510354030444c030b0030007a0040035000154407040140c0c0c407100d03255141c4888064100c581c0103101c00e8040c80001090200c1c01c40540e0203524043c41c0310b03413240440300d855850b2540540d4044909030f800c110110007000707000320002413240050041950000071400c15410306c4009030054443e09000520000703d11302c10400d0020040108034007500070b40c1d41c485007210f0103503240e00c02a200c604050024502c107010820200d056034204489007009680c411a1002c041400e8440403203004c11644c0001c41c207110241400e0100750380c100320490346101070403484641000f92010100c0c2c081d000c0c07218080040c24407402002904003405407010001e443c0d48100031820390316652880b034668901c41000000400340c90 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 153293660 1250 153292410 153292423
    0x1f09050706050901181a0310080d090f120f0602030a02070602030c07030201060e0114011416050c041b05070b07021e0c0f010503040f170910020102030402040528020a02100203010e0601020609 84
    0x10030b00c065000000045981b02250308040d009034520b11240000085d0b2000800140c0c0d02080d160b03c441034150302e003002d640550b14281d0f020400060380c2482c1280022100d00a0071a4158001001616611340006600c000d0040f600c0003400325200101380b010340e0984101070039a1901c2035000340030355900d82202c4e03902c07100203104507458015456080760040d8003890142c007529070341040d202d0602d070b4031580711791688405003030a94568010351240502402c083c0035241412005c080e11103180e124620000740117100b444c4018100340d4040c808610858401d02c1580b042c0100070058001e104c90703050741e1035129000c42d41c1d8644610a2889011483d5024030242e0303100c0d9810088075540403480c1d444a03190b95a0b01c40d001d40c0080300030000003000e981d0343c0d03c0c031000d2080d180c1e00050f100d10b40b91050004403100508a081c0203c51290802058030030f00740d01020000400c3c801503211000d509041c1c0c584004c201c0010f030f1150020002017185030581000502c982d100760308a86841c0c0703955100c19181c08 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 153294910 1250 153293660 153293669
    0x304030203120705010906111b0723150a050309060109090b3d031a060d02100504051e100806060313020a030c0306060e070509031f0905070605090118 66
    0x2c001c8141944407541d0a406040300c1405040007141e5000b46030340d01f00485010444d100d10000d0301241510038002403020002400c18072074001c280e054100303103d5400182111410200305015841c4103402522240d941100b484100d501a50b1289250f0744058200c2c0c00031a1403200601c0703980c00000b9080c0140c0079030401d060704581f0022003a21462600069041c401d900200b5165120300d81d600c0480e54244031244802c0d91628456220307080d890300080100740400c4002c2102141c801340f04d603650307403d0001800150304452075a0018403c00040d10b4a0049901580d4440e01420404040801420031200b81100132500900000200541034a100c6000d403500c03600240b05100083d00d1030348240300342d5200d42c002040d04040c1562603440720006251a0402c852184d10303443c040000010703024084c3e42100507410f140341400d000d0b00201b9562400d1940c6015040c0b0541c8040a03600500d80c8682c4c40103402c0720036a10025100e100240880e404443d2040c00034180344c072142c070314040050303a400030b84 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 153296160 1250 153294910 153294913
    0x30c0807031704060e0f03031902061f030809061308060406060e1e16140706020a17090a0320030a0e1504030203030f1b071e05060c03030f070302130e0105040b030304030203 76
    0x840c505c0140110703c80401d42d1190944001c01c039010340d000400920200341a02c6a000381000c1c5410781064512004030341102c15078070003604051000840e1001500c62054043d40c1c0280c449980d12000080f2085d60343c81251640107401c144002e01210750418000d85030201c40300100da0f00c61680c00b2400a00c1f118044001043c0c03d40452116040403988000c040360501c0c11104100d48041502d00303982c04841c1c01c071341c03280e40015030b541c18a40080224500d4a203141c180821458010042c0362200301400004080050760901c0c0d44051035100c1e82c80411150303200849440d03200f03c40014000540c1a1203081c40f840c1040408000a5250402c850940780c0c060055130410501080c001c90940001c42440d20610703002100103411304013002703244d00804040b4550b98442c01468050b807200d03c2290025401540100a9000080030001c00c8a81040304185441c81d07540d41c40304110300a0082e0315031074003100e01041e070000b1880112034001d4143c8008079001c0055030304207030416650340f19610000b50075 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 153297410 1250 153296160 153296177
    0x519020f06011401022a1003091203020a02030d0506190b03040b01140a0302040207080f030c04030b0901050c0405010c05070504020a03060e06032107150501030605040506160206010b090307030c080703170406 91
    0x1341d541000c1a024000040c2250110b640200c6c00610100c9003811a200040c0e9216403410900c0203c05180302c1142440c2403c41c904903903050029201d01c500c4048910b10341d1544041100c40e02d481d8070075a1030710208484810390baa202d81c100704295109a07010355480501500105034a640c10b0400300118500138091080d0510316801e1001941103044180c1d0010400c0c00a0546103103101c1c015849400492081552035007540741082003650090b00c54119a03140004001d45180c84204840c07e03100d090810301c00703400341407070b0640c40e0800c240c00c040e40140c004500e96460300d4158014805a9800a45e41440c0307a1f203806c281a0340f4114110201203400076280d00010654140300104030040c003c00d81040c0c1d44508256181c1580d40a0380125a0b682c1e54408000501100340300d00d5400c10600c10028a0000240100039501c1c481802520050f1500203612540381d07034104400c600850340000411140ca07030795071440d61203459502c07003134962170401c820140007078000c101200c054817101d0310742802 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 153298660 1250 153297410 153297433
    0x1d0604090c020f0303040302070806011401080c07060e0a08030a11030402100f09090204080a420b04091202160b04060f0c061e20040905070519020f0601140102 70
    0x30304a0720640c601503000340c0c0501d190000003803005521581c02500100107142c84e02d0354042c0380040507408101500341512581090340ea00030011030300140c01110701a191000c60821800404007401c40f09041d100b111070081c01c101c041000f4501c01e0340d000c8001c209001c451040d0300c94500c41243c000f940402169408206035000e19070000e1620b19a1400440b000e840f088954102c0e40a900102800c0d806800144204044160681c0d8240c03240e208007142000000052040e101d00040801d03014404868000019441640846158040108203021240c501c0c241400303400301c100c503140014018120102401400c0d1041a81210703402601245400d1518004480d4418100c103590f00b001018010034000c9001d601408030001c024400f80b40018040c1c10240701118000101c40061544818100314038000c0e400549044403440400803989548260f8101c0740d511518011184541000c00c0042d0034030360024190801c075269800721039481e40c8800e00045400c0c840c4502900590050701c1401 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 153299910 1250 153298660 153298679
    0x3060b01050a210605061b011a13110f120105031c090303031e110306100311090d1401021b0d0203040f1202121b0102010b04050106020601030b040f0605161d0604 71
    0x41c3c3c3c200300008000b03000c3e038480340080c0203030303200e1040c101a101381c1c0400d81c2034101c001c0c8074010025001c810055501140880071900c1410f85801040810340c0d1241d881d1400c2c0348000848501004030445203a80b80308803414141c800800307010700c5019201d481ea0080340724441d500b44140325003c81d141c04d806e0f07a00c0c640d401c40180500e001001421400011242d0005549014079140c101d54103041c0c98480c500701060000c1c00720480d6a100405041143d840550319090b03040782d821181c02d841180d216542c9082c181203d4544c0c490307000481d8030001d40d004200103100300504009200d0002d0703c000c3c20758400202da1342c4c01140602042c000502004000f0b00d05102c11041c2c0340340c409040800604900c010517410041c03503644024440614580b0710f20b107036078203110303c031140300040340c0070000380d41003200095845405020040c003010011010a050041c0001e4510a05034001024840c0d440c041c0f001300d03503140a80c0c4088010515613550701c0c4e04216580e2001080302c80161800d800d007860300c40d522 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 153301160 1250 153299910 153299957
    0x20d0b090705060c01020c06100e0f0a111201060806010c03140a02030c0a060203040506011e061d090f06010f170a0b1c0f021305041709040f1409070605040f090b130c0903060b01050a 80
    0x90620b507580e037003107061450802c0c000e4040d1080d1251aa0aa1342c544a4050401040100b00303604103c1350203404c4e8002038002c0e940c042d00160020f286a11400c2c000802ea245114454202071079115200440702005441d4000350f204170301c18021703600c4d80c0e41da079400c0958101011401e00c16480000e00d00b481024071500140c2402684506c1518450804c0700c0441c1c0d56103410364668940d04102da00708145940c2216500401084a29100c00c80e60400141e030004440040d000d130690710f0715807261490650740d030500c0f21000b030711100c540380c070620b00303450600000006408101c1c0605c042c4000204800820720490744110b420095180d00400d072421041c0040d842400819440b13613a562030100104214821010790b04881c00102c826800c0100c5024908806540b02c10100807041105024661032008030300110b80c0c1035040452500c070b001c0c0024990800c00410f1244d06880c110b45612a03c2c2c2c044c00700e004481c0100c0040203901c0e1100011100c0c0c0c422280300a010803100010b00c3d40d07101d00003080 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 153302410 1250 153301160 153301171
    0x2a0f0f0d0e090112060c17040c050109120803011a0705031c0c1d01080604020d0906020d0506060c19050102041a180406141c02031c09060c020d0b090705060c01020c06100e0f 76
    0x21030003900c2c500c82c5804580040c2c1c8c040c2c0c2c5001c43c5903010f0116580040880c0d021b401d80039100e80e02003555540d1140345d44014042d040c081440144180e06079400312007580e08a680c040145c90311452114a56000c2c01c0502d1130000c603ca08008140210a000320f25600001a40b0741082d00c0d401160380064a6511000d4aa00c0e0070680c01c00030918600300301d01c1110907880c404c0201681e01c440100d100c03403d4800181c545423040c0001c00241130050400100191300d86050586031468250f107042142c02030003241d000d10391f018201c02078070400c004201c0051125007018010b1b0340600d5003e0b402e10040300c1c40c50146160908994050f6007251509518200c2480c451607075018801c1002d5010a00305581e00c8001702d07018009548585075a40c019400d040a01058a8130641c400d1140d00010002060b4001c040c0085840340085141820305002b040d001d020050030080d80d9503601d0042c01d00079032090900e20042c0c0907100109500712101c2d14600229503040704c140e0425210b0744821305542001414 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 153303660 1250 153302410 153302417
    0x503070804060e101a0301150e0f040614130210030903050d0b03100606090e0108010902011202030403020f07141005130b1309060905160201022a0f0f0d0e090112060c 73
    0x1624807004c0a039010700d0341e0008080f8048803492021a0900d07007950040301c10b02070050040c902c05d05c01059052900c0c0e030f0102c0542c65200306600c5a00700783e4020109203030441d916231600c8040125092000401c00383c810303c207031740d500040d0200030000c41c01c440080e0f40042c00108100043d0352643d8844c0c0000903840700040030341d80060a90b054017801c44035194071080204403101c00800951407882c413914014407a200c02800a03e110360700081c820351003024001800350380400406e060610811151a1207141e90003150308040e01d611002c0f0b81c0e604000d085c28455590281f10a000750700c11000e403a071600080624255032800e1004955541d08800b0850402c1c034003a0000040242c00d0380150300c0100302c4040e0014140c10b20020000c141030070100500c00703581c0108aa5407024401a0380c0d5014261591660200c3c48a41c41140f0b04204459104c00c28602c120340c2490010b0a003c9034881243c00b05465254141d200b0303400303012017404244500807070540899200300208440b60880b96481e100c1c0d24 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 153304910 1250 153303660 153303673
    0x509070312050405120c0a170d050d0e0607030605030c01170c0c0a12110d03180b09011104060e0901050109080a08030a020f0315132706020c011112070503070804060e 73
    0x10125140086515001c0440c3d07001c506c004620342090160302010700b0202505404004500c4046a918140040b4440c1001000101500b40c4c2034107603c001814000c10307040e200181084e25000340a0702143c018144030380a4807558221643c02a0219a00d0350801c0e0400c0d201903035074500e1020030760400c05240485000720300c0d80100007009042c24450101d21900d8030300402c20710b038020300e1508010700380f0f15043c94a4044005000d621000595000030380c00341c80c140e0140d4407555002d024106150322250251008540810300f0780d00030100210a5100303603101052030780d0721401121210070b10322590485401403850345002c01c021b0401150700c0700000c9000340c5006224900169540d0044540e21400b0382010343c401c2c031b641340007066040e00c4800c421052114000d20050031200a000e1803c602c01030020500d0f5000b000055011340b200c0000002c000c10100d6540940882d80707600107071190b655552030307500140300d26000e2401c0d01e0051403560755258040e41c447e5035000050040420112562090300c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 153306160 1250 153304910 153304919
    0x1b0d1e02030a1202070801050408040e180f0a140a120503090106030507030b040b07141902011112040b010e07021f090b0703020c0d030203010b181c0506040b010905090703120504 78
    0x80200710344142c0700c0e50104601d81e0403e00000e00705403558001d002181d0500c814403002c64808030613582941c0004062a0150f02c54005030035124592002c290b4150045406065000c41c0102c0d0346104039015501400802d00e6040b502038441529010007000c610044880f04810ba101d04040c41d4805d10314000050700f02c0e243e84a040c90404290310072907148802d01d081000b0401141e003180d4019140d0f05051000010203a050350680c000c0c00b0b84ca14151003004901e4015910035004141e950044c140e049035201da08429030590200103c6094070300034010400008d001c000c0c004001e01c50005507000c0d04030305075600c0805035121a030710720761142035498941c0c0c0030229540f0201c40f070244e40c141d00c005940d40c091380d801a00380b120500130f14040c5841400100003e09180017280c0500b4401403944c400201aa80014001e5141001c40a000440900410104040003070500e000b64000d40c4082c806030380c0c603034100741552011985202590441c0c02c04000098403000802207801740c034184a42026180e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 153307410 1250 153306160 153306163
    0xe1902070507140d0b04110a0905010b0d0c09060e04151503050603010524151e0a021005071704051f0b04060b07020d030e0402041203050306031b0d1e0203 68
    0x42042501d0540045004000d00e0000410200b8030f03950607103e01621100d5616806074140000b080605840601c000030f08503590f0709004039010b008151020411541c442d2060011904030071440c0c540300346801550b11881c1d0003400900103c1d1699503a11030046680410712000d0729140c5221014204580390108000c8001c2d03000c04400d58141e42d0000d1540380c184200740c20f65030b010340000c010310601038903107150100040041900c0c0c2415115240b1400540249198900c42c2051006000e2843c5d10201004c1c40c0d0700c0000d101c40119039080365100c1400c644803000f160340994556020859503800285010204030902c1c2d4000e02807001d650380c50b0595031030302c0107000d04000c94105c826512541e018540c03910744542d0300a810751807112400e11150354003003004600c198001405114114502003403942c0c4640484029004042a021000c2d00303900c0c000c1d00c56003003618058401c0c09001401080510f4100400001001c000c118034090f04039501c4000e40308025200d02804484038840010258a0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 153308660 1250 153307410 153307417
    0x10207120201020a1701120303020c0a020907022b0516050a2915180a1803030903030e0c0a1401030221070906020d080a0c020a020301050106020d09050a0b040e1902 72
    0x203503000983e4400316050000c104a0000e4100540c003030703500006108990310524840809030b03050800686d01ca940e45800d925005190500030740c8441444108201070340c0c0801e0f106551403050311560807800c0400070752005044041048000520280090700042603a0070703000143c0c41c0180b0030380c0d03440706141d100d03022818031b40782c4544491109401603400e00180c1030542e580c0400c003941c91025002c00b1400240d0400359a00c05280c40030b50341c0000c94103d20450748040f4000020114040054a0740d00e0040c024145201090f404a40392004101000f035003c00d0303602941c074005041039072036401d01e0718052400c0402d610182c1016400d000c100c110f01c0b880a4403660980042224846a00c2e200d0070007030002c02c040d041401150007469040b01d034240c205410303036008900c0c00404211258642d804906e0b01150307500103541982007000000d01c068010600120885550392003510f211303111400c0c045031158604c6031903c9181c040008000044c2501c01c0035801c6080e04214000701c0810414203001da80 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 153309910 1250 153308660 153308693
    0xc0507080606030f0c0306010e0603100612020f0103150302040507030b040203011e06020304030b06041806050411010906020a08031501020f030408010212010f080d0f020c06040807031b0b040611010207 88
    0x40c0318005000b22031030208144032014a00100600300c41c01c80320701081c2c44042c1840b4801035002da03000800e0607980c080c000911004031414041046a0b61003500c000b0000d400101a03004003100110001254800d0103034a03001c02d800d00c00280d62038078550038000280001402203080603590080707a58180e5560000b51700074191104200d900758080510007215041c980d00800956108105c1080081c00c2e45080a91006003100d000507902039521484800b031404610003819545801d081004000ca1404070441c8681e0a98820443d147c850405a03a50540940d0203410034000348006491103000c424280b0001c481031041da0f8030704000c140076034510b42042c1c010300000d940100340415030354078020529004101550294581c140780000181c0c6401d820619441001851255084028020850180e24420107046595600d45d140c49443e11110a8041103c1440c0540b00d402c03082000e100d040030907074403030341034072880c00e40350100076180300800c00d1540e03465540034402340f40030030b41d40320b01c182000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 153311160 1250 153309910 153309913
    0x1407030804030b01090203100311040b060f130e01210203070305060103080a0e03070609031b0b030a0605040b030312281401080f12030c0d1803030603120309050a0803070c050708 78
    0x241d04616190006000507009040421b206204200025480d14400f004036600403076540410103844000c02c2c080c140030300307449810000004034060340b07400c154010000030304040620820300c0c0d01d070641c1c58084a07081c40761018141d00b450941d00c040c000c3d00000e9800c00c0c8024200c40859903280c0d00c00c0d0400c0000d0b40280c0390403a01051501016030441078002d0582c41c1100a080c0311400e040016007c4201800050000580306542501480c0341004600c0074007918000c082e242e2a00308038450241a032401a14052401c08010351039034200081654440303068400b500615603142000c80036a0640c2c81c0b81c140840d5901200e04800034614442d82c0303a0440d0100c001c05040d0705244800307251441919156660758013804203032710307212104400e4075000244468138543e100038040c003201c05045105c0d010700a015410780c0400401d82c15920820071203100e05404031a00d02212410b5049440d02540584541c212034103040001c0ca0000c0155441510f50070320703071440e4126440d01440c1900310b81050249 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 153312410 1250 153311160 153311167
    0xf030901030e030405042c0607020d0c030e0d05010e0c0306060a0302240d060512030c1b01021e0f06010509130b0415020a03051005030f100b0111060a0204050a051e090414070308 78
    0x3030b031035150702880301840d07017030040080e030808240081d600d400c41082f09040002d01e00301c000806209481b50b01d07641800910105c034050315402d21074001c055a6280700c500d84079501107241c0da42404a86144141002014030039138610b141c00b8000c14030289284a02d42c0040055242c001c1180342000d0f10b800c10010000055480c2040144241803102584120f1558000e101c544450b00700010303600305800508078070300100e07160000140e1400405418039048048080e04010400000058201e07000c040c030381c2220031503640c440038848082c000343c80fa0414192180c1b0440003082203007004d950003d120b09604514104030040c0c030803c980001c00c0e0000081d440c1d50a01a88003880100c240150070120301604005c400c114055944200401c424882c042e107034211080e0741da015060102018441d94140c0b049807401e00440d0000b5445405420b2007030850b2080842c107400c0c80782688a60034810703018407110890003420040c220000900c11911a82d00000502e690802408010015031050750001c0d00c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 153313660 1250 153312410 153312461
    0x40807050106120f06090c0f031a0703020307020a0b061801030501020c06010b0c0309090c0f0f0409200412111c0201020c0402250812010e06120f030901030e03040504 73
    0x1d48103a40c0c461083c414144200b40c0118462030714600103554042c0c0001090011032410a0070103c0d55808105641801c0d2000428420861140b004440407001f17103509070790700c00e01c05030300328041a60114011382c405411000041c00010310903812490007041d01c8440028898080d2404001741c00c101c516075000b01300c401c6e0f266420001c42e401b502e0305003802d0b800d202400b16019a01e003c1c2010642c4102e210301c0201d081454441d04444011000c4c41c60151b8841c1808000c6106a11a1040050300751501c404041ca100058010714a07154964000c0c518162502c055007070044c0d0341c49820303103007100c100e8507800d610341d243d8001203000c4042c10346d1030010062a0001a0170f1082a5015601841c01004a400c141400031f00c8030044410702d80403100032803010f00b0070b42054082c94420100240d0003030004200f01d250202c0f072620580c401c03182801d0000806105c161200c0300101c55585640c01072102d10707a10340c001c1c0c2001e2030819041007180e06003aa1f80c0c00007010f9903401e10800300e800c07403400b21106 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 153314910 1250 153313660 153313663
    0x3030706230411150d020d0b240304121b0308011e0f0512150403030902090601031a0906040908030f010609081b100306082415150702060c0604080705 66
    0x709071500c101c50403042031505450702560ba0003040b403981e1091021442d584e007102c0300003003612441d003d41c030021501d914403440b52200604005013220b1003505605d0924859850701c400740c00048905110352801e60f222955a614070722100464801401240c1d1130004102d0303100c5403c07201c058060342c2c07540d0701545030000314901c001002120326a0554400c800b40064203030000200f08440c01a5605401d8240ad6420b01d402c1407400c001104220390201c2c2400103040d4182c0014907035500840346071515455100064040307448c0720150003501d2404410851030b5150113654160321a1000d800420341141550f58001198411242c08103c00d14040041c030150381e20443d164003a18a540017081003401d054280641d5440c200c0142d4402d90110b90110000361094008000400181084608000c0d601d881c1c401d41c019444485200d04d4425000207501c0b004003960302503144400b50468a0b200251007800c0055885400306036080401005442d144010803c8005c3c0300394011104240c486c4510310340207 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 153316160 1250 153314910 153314951
    0x114060103021315020c130c08060108070c1b0503030c1c0507020312070201030209040603080a0f030b0a140a030b0f070e010305041104090507030818010305090106061407080903030706 81
    0x40e04041c410b00c41401103164034610a800c3d60b010080c50b040c01c10314104200d01c0d11100c1903286400048005012400544641003900d150b5919120070a0540e11240111030a14003220b011001170044500080454041080d00c1c142548058001c18941d464101180ca036900c8060071103c1640010003480b030b28600014982d03500c034281e14048c0d00e480507c3e000265a003080c0e0b501c080d019580011504110780c080e504899841030040c01c280704103a039074140803000b0703005600044003003103103660a54031280c4a80308240d00000000c0148a029080c00424103c0780c01004801d60405080c2c280131000c03c00d002c16203441980d0321503414043c1d2401c940c004205641e0005100e040c5820002400f0018071252440010314400341c42c0021144100c0c11701d40e1520703100b1780c0064042c940000f040c0001032503445e001c044c94142078800380070766210350091608840103407180c1800982d1440b1022a805442d000914805026203010b43c00d01048000090071580035507400c40f1245d6030365040200344001c66221 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 153317410 1250 153316160 153316171
    0x1309050d02030c0715090b180a0306140a05060306070309020609030709060612051e04111201050a140402090f060d1703160e01080601030c0c0b040c0311091320120114 73
    0x1800c0140c13005c888090800031103400313800e1110f240811002c0d081100ba00c8040800c480c014120941d45a981c24110001d1000c60700da00c001d401080d00082501c010b0b809907034001c5002900030096681c0380d00d400c8000381030111049034007603400c00141c05a0313641000180c014007010500024001d02c2d00d4005071200e1083c400300c81109040c01c0c200004508800c1a510300c001035020b0020081e03440e864588048007401d01d0756507008101c0560039010070015400700e0301c2215901d40400c00581d5030b0040180003107007110000d600a600c240010000d8502c00005a00444003400400509180e69140341c21001d11009041600b40d011040009a08900700c21180c101d81500740500c0c91404180020840c24008158905143d12550002800ca1294211f10b02054100d01d180c082410180741503145040a4403081c0c03044202c0301200c0e0301c40d1801c60360319805000c00c0707018984803403065616491011621203164424240170615000e2a2300c0340c610211002c011400000341002500240c0031082c00040c16 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 153318660 1250 153317410 153317429
    0xe010c0807020a030c0201050c0303040b0108070803040302090406090206130e0f060612060d17040611070b1303060b06120405010207230705060705012a0207091104051309050d02030c07 81
    0x34096850b8000c56004040c6415281c00c0224031464001683e070f0388101c00d510f4085110000400040c04030800c0042c1c1614090000d0760904c40e55801071035a01d003e140000b80d40160b121010400140303c0b0361265080c10300c0500610b0a1241c0700c1f16203088503000364000340454525504002502d0b4080758043da002c5012100a13044c18480d100c251118400140a04e02a01d0840b45840501c21038484a02610f00d56000e55581c0d00c2d103401000708a400f0900340e0a402c1d114503c5d02181c0c101b20030050b1511141c0142c0c013041e42500e10348410000d81701c0845003a41090007004614090280103620b203100d68054400565501c44525150504011440e1000394400f44e04000b440c6495001c0b80150803100115000c50300e813a110304010b401400103880e0003501182140c1601100085081710100c0000709030282c500c51139803521100103481c00e000311180592000c010520451900c3c0300280741c4260b0180000034003403815950710740b0b40765070180941e02580c008070301828000410031544015108695 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 153319910 1250 153318660 153318677
    0x120203040f030c0302161e050a030b06150702030304090204060e120607030b0102010605040c0905031605151c09080904060602070e0a1d07150e0405130b070c02130e010c 74
    0x11036009030075456840007800c01100401810a051003003210300c1d4159400583c00744510b030350301d48140c0750020058400d07d0700303405200300146500d402d00310701003283e8002810181c1c5a5070340d01001030070b01c0d11004070701000e86e042c0001805a00d0400240000c1d120312900103035030320305283d0080c115000e4030f041648100001d481461900d840480d0b2700b60000014140800e08180700b00040c0c1c0580381c1ca402031a005840d103082071000340da100c80c3e054101c910540a69094040c151100801d15800d03010700da420a03060a005442d2006038001401441c1c4420710a43d51101e00c003442800b5201ca11005484903900415070a0180c5424171481008010780d0008040d10352500a09034a00000100519440c0c0e69902e1201d0960542000b0060072840ca2000e64900f240c445184071401c00310010103100141c040d048003806820325100e071a0007000140118410b004007a80d0305a000ca00060103c003c0200c819005130050f1111201458055a40840802c050fa40c0350401800c4075005589542000141ca = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 153321160 1250 153319910 153319913
    0xc070b010b181e10110a0c0e0601020d170408071a06191d04060e0319030501090603021c05070f030f0506070201110f09040209060a08061503070527040c020a0312020304 74
    0x10804880901c900341e034a843c1844c848801511900c407007016510a50040200c1170041121824240d4140d650010006006864540c012a61448002c44480200314609103100410720425081d81d03100e03120b0341d81245050400c2c1d036410303618128425400050f4075004140244e5141194520b02ca2071010100c002d0102d207040c2e51625400c4590320400b11405500d00854180315664014004482c2500d048030f9031200d009644401214100e0094400a03207004000f04000e41240201c10440c1d400070450284400400352500009000c00c0e0304440500c13a0410005007130010800400042d4090608080c6060840c14081e0901500918140859141111024081c85c842c2c007590691a07443c0316564030f0780080f8001c180244222103071641e100c080410383c03040140c1d000759032070f108840642d0700035007410b040380b030f0011240000da0b107540101d00188030094814440c011128843c44000010340101c500344004201182c0300f00c043c000058010640c05418180c00045510650201130411031039407610303 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 153322410 1250 153321160 153321199
    0x9061b0405060f160308010303111902130609060b07020a080303061f030207060f0914070302060a03020c072c091b010309021801091a060315090c070b010b18 69
    0x850050758403540d004103441c0c01070a0b046003a18162154980c224900303150340e08000d07090400920040f40011200c0809002c030300804030b01c00c2100494090240d54180c030a03070812000c81c81c112802e42559a4981000910080341d006010081c030402c00c5d0071390f40d5525401804080e94160f00300030f0b0668402c00c24000507440320750b80400500b031860301d060b000000c01c100440284c451050043d0000e401d242c040340440c02154029141c0340d00c11074240070141a2600741d00d031140b24134400654442c506218903005076001e40c004140f03146015040d11a460b0b2110844410340d410b095454001d0180310401d03140300702d816449103801000b8680207100e510344641910b00d0350040614900e0415458503648402c5468081382101c0c45044010074911039030311441078800410f182d00384251145c00d91056140c0d5420f000045a01403090000311102200758a014818000d001800e102601c00341040b04002082c0080c1c001c1e07018041c070701402c03503980f8403402081c0311100c180800644517914000460240c20300 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 153323660 1250 153322410 153322417
    0x150103021011120307050405100305090604060b040902130207060c140403170d0e100f0603080412020a05060f04090b12060f07051e2a03040311150d0509061b 69
    0x140c90b001028404541c030040c141244003491000401012041c084100e411001074000d460003a01c00c081c0b000e40c10601201070300c00a40300f040c0300f07410400201340801e01d150010074040e00c016202090f00100c035408501c081e441980d00c0981958040342d10020440140a02c02000846140c1030703c0f000038a140c00001c40c465440001c041258a081c08100c03060410151003100702c3d80321080000c140c02106c8a0307201c000b000e030140b0400b807407c4071819400303a0b44e200f41400d41c0d821040107410182444608900c1068040060780e01c1109002c0005190792100001c02c4c405c043d030248035865526040d901025070f07030980401d602c16801850394121031030300000c0c11030b80f01d21450610441c5844015040d60039121320080d509038148107e000d4445400c0d07002c01010389810300000070506803008070103201098040c50b1801090b410800c02000402d8640907006005074006114000560014844440d264400d1024448072521041003009091060007a035900103200c8820031145460700e15940030510 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 153324910 1250 153323660 153323689
    0x606030c1303170319060b0f0d0e0d0908101406010513170a05060f07090b0307020c0402030f06100c081b070803041710090b0c0a05120f010815010302 66
    0x268042618060708800000c100001c5030400701100010000340141c54560380115001002e8120940e214411003001e03118200464125040c254100414a000300c02e580d400f2250702d4103519114264900c1c541020720404800c03003555100d0141c013500c0c10000b9400c011a0803141032030f40b494020361105071010305000f46c0c1c0c021000d1030321543d60b41034044841c868054030b0700220140380e4031071042584c070a40081d0300c0343c6a600030012115603a40300034607540c1c468400c480c8800001d0402c88200300244101014540040c1c40b4011380f0001c07101030b4082022600104d429034140030030401030000e42c0c1412039800756522070f9841c00604003c05a15062140c4c480e50050301011070340b4165118486806200000280c5881425a41d88558405540b140190a0407084040e409040031f001c07000d00d1b640c4145203505078807a0000005541e12100043e0310380010000d0301c14464100b004008115541140d0761180080d2070500a8550401e40d4540ca8141c96000c2080030803081d90042c805a900c424000080d070 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 153326160 1250 153324910 153324931
    0x120130b0d1506030509011d0a03181e0609050409110613050d051005070207030312021c0e0106030c0b040506090f0301090507080a03020c0103060e070c03020c0d0b010e0f060603 78
    0x30891801480e0040410b501003036100300b540c0b2404030704558540c100900800e4000c0080c000d901a000210319400000c100d030006a900203401200042d0052164445041c800d418000080380e0ba18074080307080b8080b180c042c111017058002808096003100071040680015103040003880f200c0c7d83c48429076107181031210b1080501148030050b4000100740c907c0588000b5001c3c020507900c1d07180151360b50303190410f0041c44c941490005998503100003043d400301d980551340c4211410000020310025070024800d07000401011310603c0d800c4500e0301030b00d819905100000a500b42c0780d0b0419204200e1150050b03000784108110410030341d501c2000342c884d405002c0300e01891200a450000b4014002c1d41d6004115014246000486d0388011032140c060501940a84054083c1c1c4401101151180d015011140700c566000c81c07000340c401c00200d078095100740100c80c3c0302400174000070b010240d0b01c00210340000d00e00006108005002d00d105810007034150480144d81019000100d440c04010042c7d00301 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 153327410 1250 153326160 153326167
    0x14040e0a0b040608030a050705120901080f04031704120f0e060d021606061503050718091a090a0c09051c0b190c05030702010e0c09131505090120130b 66
    0x3542d0302c0f42c1c0f001d0020a00501141c1e654960f008014000382c0100d4001e80e120301440466004000845089074100c00d8140c1d00d8800955554911507100b02d0090019410080d045440c00c011707069401181d8010b50080300d881440324081e5030000c00d100c0040800710104941324565003000e440740c205039107440c14070400c056181d040042c800000310341c01640c0900321500384000025010030503103040c040c4100580c1c0600c103a0761080410b9034030810303440c50001c0420403a2820400206c5a0740406010300030810b0304400d4401c080c00081c81420151614608e903039a407050707491400e4001895000418080d500040c04114a02e81d221800f81c0980d0b005d00304070714900c00110030501c1d041e288070b40b60313031044800c0107403802200c00200075030421503400c40903620b8030301e0b41c4541c1c000029550b482010000d001d01003641d40d56040c0107513103200180c00c5808010b11980c5914911480c05814401c208120000464802180016860821811046088040c01c2000c05800c1c02c00041d8031082d1040030b045c0356074 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 153328660 1250 153327410 153327431
    0x6290607140d03061e0506031305100e010506030c010c05060103080f070c0303030506100c0f0602090409150e120403050d0c080d0e010c03060f05030a020f0a0518060114040e0a 77
    0xd8110007185454160141c40d11500d000c0b40c043d44044195448044101c2d40a100411034602e4040d0071b0041c00d034005070030700009580d01028820034130f000e441941990b061914402d0720000380c568000d00203441d42d448408010b11801d00300f05001c220082440c100201c05042d81300c03280c4072030f41800040c0020b880000e400741c4201601c000c8034055903201c010941c01e2650303801c00800403d000d4407a540300d10761880c0c4070fa0415200316141000103400c00003e103094003071503861030002c0d07000300c526642007171712034111a002c1740344600e010035080a400e10115052500b04107290410700c1441021210407000d010a01c089400000c0603410300400d13003400100c03c01103040a403403600420341040f4009081c901401445a41900022078441281d10b00344036007901c0320201e2158941c5c0d4000e9540592028070244050300c0e01074a0070700c0c611360140191108c2900c86012a00001740681c540c000c24643c40300b484200c1d41e00c8002c0700c0c601080c0b90f440c14242400c090961441900151054401c1a100c20b40d40e003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 153329910 1250 153328660 153328673
    0x50603070503190b010501050a020d1116031110080f0f060a090c0527060a270807060206060f0a14221505030d0801030b0c041203080406290607 63
    0x1001e424002c00310f82a0360a04a0030002d0031240030701c21504010154000541540507406039400d0788540c2d0060040c070f200d000c00860321400e4500703060795a4410001c40c803c0301e503600f8001c14051800f4588603121095244184107118140034440c0d41040110400c0100d455600c01c841078102151010130100e41c0c031040001040030b101d80d000917403100e1a141081c0c1003140c01c0340003860000c1801e200c05440c400c2c00d42901c8506050703040c201350000c0e010000100340b140720340d5140464030709940106c00c400c20444010400c25403950069038141d4014002402a10f40400c03034194403080c210b49070250141c01a000c6280001c4512486070b5101403441800303030903950a450181400c440811080301940c6c0048510007800d12130390400c14111948501040a040c04982c05007098810380303c1040c40d0340313150307110344401034001d140803400d200a020101d80021418001038410b8000c0e0380d65241400d02d03007040c00031111881c0030040d1f03140115000b41203410303084c4a06e100c5170b4402c68800b03454034014145030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 153331160 1250 153329910 153329923
    0x10c171012031205070e0102190804090b010311120105011209050705040e0309091f120503030f060a0b040308070605012301050a0201060801230115020a020d1a04061b02011e050603 79
    0xb001034504003010005c025a1001203510340503426401c840c0d0200000361117030071002c50b2200240940c202008184000c0b1190b80004240307a40c185800607803989a0b000401e2140c001c82407681c00440440300400071581d00007000e000484010004000c40d2442ea91a140d4580340352180324022900e41c039441058000c02d00c151680d144c800752481e4901c0c81c142c8102c10b49406030540c40403004205500c04a002020101d03907483c200d90041c0150300d192a0804145a1880001c01603580102d01900c04174007c108040036200031803003034445d640c0725003051411805940c0140c110901e0702d658000740441003412070110304460760003800c0141e40c0b0040840101e0142600341c000c0382d56076003010010b4080352190109001110841d0740400c4180c0d032104106844020013039104401a0302800501d009468007080e54a00c3c580300d41d04114100303640d1101310282003070848056940302c0d56818000034800a0a203d080003420a2000708000700178401c10300742000b410b03049610110b40d2503001517034944080044 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 153332410 1250 153331160 153331187
    0x10082b031d0a05060a090c03020d080c1005090d0c020f0103050c210405011104050d0b07051306020109030f02060709030303200301081f0501050f0111011d010c17101203 74
    0x600e052200d00300007240d0b40d02c44080c0c00c503650b200c1c250014a15600a2003100e000e16444004001000d14503005c100001e1030100c01616182410810702c551002c00700b05510202e4007610300441d031458195242c9090002100f0303c0000e0280500381b030310050340c4203541da1030b103030300d09007000030701030711a032200011600134142140c1c1c0c181d403e0442088081c84020429200707622581c002d0106040c3d16031441c24a014501c106600203800050b070800080386800c09540c00030303241ca0320724281a0034842c151700d800b5080d030000c00036075951503110301031560001814965003164001469642442280101038840c1480301404040d521000c0a40d10940c00d880c2d654103134100345489489585840131035444413550b9440092a0040f11003280118840380210b50480e48020701c2c100031405903000554220048514140255694008103460151119142c41ea08510140001b4040b05038120241c0b802e403080f0100e80304000d401c81002000c2005215200a4650940f240d0201f903140307150a4600a260000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 153333660 1250 153332410 153332441
    0x60f1309180309061b290a061d040807080301150f031401170c0306100611060709060c14060705030106030e071401032012061005030417180a0b0310082b03 68
    0x4200700382e2039030203002520f54002007214038183d00c6040e45030080748e0642c4514148051590106c644400002e0882540180110f6000e4074042d1140d45001055000341c0002c06055040c11031107001c0c0e64072076403030656805c1504080180041c0c00018200c0d000381407103480d4402000d141001000c0c2d2061018000f5405c0c0a412100079050000e18112180590300480d40090000c908070ba40070400010305034041c1c0703d6915040000c604207103086032460f26566040d9003400c030b9a100032601000800c2220b200740711554032582c4030750500358001c0540300d42d411010302c144d00900b400c1c000d0f641585071102c0d0000382400d00042c1e0094401403400e1480780e000c0007203450714000ca072100044c503076011060320031001103c10400801d881001070391035000c2550040c0001c000c03202c903011092044002000c00d41d9404000c02d000036103140000700c800c103181d0030002d21341c1004000d001601c4010805c0030090401c0e18060410310785804100110203c00c1c14107504c2001d904184119001e0184d404500442c6400c034 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 153334910 1250 153333660 153333683
    0x4020a0e0f03071806051504060912020f130b041503031b1b0602030408070902030103082a120d06080a080a03020706060f0308070201112a060f1309180309061b 70
    0x541080117024038814503028803400703400ea10304412100110f8080d201f80307458483d105802c01481c00c2c000b80e2070f100102c1c0c0204400341308040e181d54105c14116802c00074480414240060000e201c103548004600342c050a02c03008007440020380210240070910f0101da607546040172a4104030340034045d070319860b00c900300b462400440d403035601200038025500c18100700d443c526a205108400c070b110901c005004c00109100841d020038424413401d00728401c885002c50980208e410f00d80c20f015550280a03e2a20f000a0109a4050900031400148070400140884070300a4440c2d0507184504081d900070184e0000705042041110b510070350184c000d900310048960b8503482c1c109030682c00100142e000c40e050280703a02040b107001a013400e80030590b0b10000c40c08884100e14042c1860301ca01c0c0706510200c11320081c007800c1c18003c045d102c0c4c070107c40c1020040524110700c8004030b9500c40c2550001d4180e030302801c4080303a08000c84504449281c50b09203480984000b55160304500e00900801012254 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 153336160 1250 153334910 153334949
    0x16081c06080a1e2d060204060905011202070812040f060c090305010518100f23190606170612100203010810090203150408070803040c0e0604020a0e0f0307 68
    0x401e0420140300307290034020740f0030a00c40d900015040403401000c0c0720210003440340020324000c90035a01409031628409641e031a45e07802090340c1041d005180041c86c406001c009540c5d00c800d48103100d00001404600e010055284c0e0540703071191021020301c507845100842c0800103030b0381002e40401d0b040007041000310680480100503055521098407150700f0000413920408440c0100b1500381c080344014001100d00c003048602502005420104650307945503421107208500e00b81101c1c90001c889554101c0c40c14002001301d030010304c3c00c60014245000320500a15802141c05070001640c40c0101c0c903280c3c2c94000050240b07030300d645800254041c0243c2c0b07400c0c8202c075401940c1680d40500039208030850f0720a005013100c02203038003c0d605610001c00202c036541301c98072540d04640104111707403800c103590b154420640e109403821034030494269400c100600c0303006080c80d0002302c02c031402d514100480c44000c00b0407080610140c841c2c0501c40491500d641d040000000031302c0340300500501a03120 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 153337410 1250 153336160 153336163
    0x6020c0703030e0303131a0f1617030f0a050a02070222050117071a090604151b080304110a0801180209060108070f2a0f02041116081c0608 61
    0x551008a0105082c83c51466440ca0080b00752203842d005440785038480ca103422000c04014104004000b1406400c1145100860540b802425100a8110320903080d8160b45011200454510702c0407004044c24401e1010420003843d4441d0040c05003c404a481d80b11900c1c604001e104140e0029413221203644803090001982144810402d95004100040c3c0c0e0b82d190025140b40c0c3c13074102c000c00b942003030b40180546a05030400640405030510024240391411022030703601d501503002080c0c100201c5681210b820380c043c500041d280550170200100700d407250340e02107041c00080e0000303001d240b540380c900c225130b12904000001005440c0080c040042100c014450f10030180000364080c400000014015500030285203000d4040c41c2e0712441c044009920460f14140043c07980821442051010b580301da60745980d401000b030088a8083e01130038184104000c681c010203201c802110107100304503140c140707021126002908804960381c0d40e6120710000008440c0c1403283e452a0386441e10210340b9090 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 153338660 1250 153337410 153337423
    0x30504020405012907080909010f08010e03160201050d1e0905060f0f0408070f05072c060310020c070b0304050d020706020a0203100e0c09010803030a0b0105040302090705090d06020c 80
    0xc1e102000140d0302d0390318030300d0792002c0c43e0150940b203000036501014003010a0010300c000c0b80599501e600b0714266400003a20306400ba030199421070b2503c0000d01c030391103080c03240804100700c11005614200c096841c2d01c4a005000e40f01905000000c540c0707559030103894001e0010140141e0001050a140c031252400a00640c4410340e81486400c0000d12400d003103640050103a14403480301d8020796226900c1c00c0c1c55501c40f01085a1010181c1561b000084d020454203010300a80d40084401e00100c200001ea0400b5800705012000360600a01000f40c9000c41e491507849200e91000d03030365031344840f4400d10f050801d910006015000104105c00e120317000c1100b4214481503800d589100f0740e5603001b00e80d9101c441c0030103541908040300403000c03800c456201c959004c40c00307001d60f00c8518a803030000314104026400b54485030000001c0001c404607030b1042100030b01003420014140b03130454022600c503010007825074040c414001071003402c55550b840001410350780200250343d071f10b407e039030296100c48 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 153339910 1250 153338660 153338663
    0x90302030c10110d110f1501030809030a0f03050a2705060309160b04060e030d0e040c1205040510052818080c070905060d08030406050a240e070206100e150907030504 73
    0x92484406e07001140031a0035414965800c81d50a4641d085868465065002003030155040c4039000380100014002d070340009102e4026102c0c2c0392500d42880002d44021121403c542c42017082a07400d144954019458405803601502c82c00c0d165500d0800042c98060307600c4084990801c00c80c40001c4058030440207006481c1290756040401801006241d907a442105140000c10884404000d02c0d040961104441541900c3e1030122070780104444002c4401c103681c01d80e4141c200c00303e8948107000c14003c454000c0c110010b1080d034038204084a07803666122520341800d01e070b140c0c0c4072000100007800c810707010700d0b17000f04c40070ba5240b41ca0040380360340d8440303445403007456400c05c00000c40c50724043d045422810f0b003100c4158915a0307075588089c01400000e050180141d9200c0c940031414402c0138690274028640055a4138150415000300a01c0394024845800c562180041080804900f40341d20210f5549002c24078480d140c1484606840c0b611480490f0000e801c2404c1000740359164110340d000d203 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 153341160 1250 153339910 153339913
    0x3070503012c19150915050a0c0206060f01122d05090a0206040b090a0314010902040509010b1f0203090904061d010c0503190b060d0912090302030c10110d11 69
    0x10001c884240e103900d00040380429480c11210024045031011a2944e00000d0950000806400c60707921001d003c00c1101035000e40c10790715010010607251030b1040002c02a03450000304036030318010002862507028504090304112842490803a00c0409030007508014082003400031104000800e85101c00c2d40c0a071880c00514107060104000120214a0191442c0c014049514190030b09440803020303803020400c1504070880d80400004644a01c0700c9045104100001041400da64010001507a0300a014484a64034000c0d00c011a5a0f4514a100700b400e4034003100e041d201c3d9004016810741c000e90358070a41040903101004100003040d030111045c040d84214220744846c1146202e4200e500d06505000400c10800108101c3d0ba0480e807a4210220688404078418402c000410140c1d040b8940c011039007038070f440d400d40800000c48403250202207649003500a0341d256400196440046030712541c065101084031100f00d6200d86442c19241c100b00007103c80103010a04010000b260310b48240019 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 153342410 1250 153341160 153341231
    0x7031d060c03062e0c03020c09011e05150d0b011101020a030b101106010b03090a080c0f2a09060607020d051e070f090c030219090501080109020702060a0e0307050301 73
    0x52150b00b150804c1e4074807400b0000042c12921050f41c3c10942d540003038040d40701b00403c45030269104883e035030107804281c050f0129019080f10107803003a05a41c1145204201c4d09420b904510380c20800d40d0400d412186000c0390010305000180c6100900b190b00e22580d50000403071800302d94054201c0c00300c0c40070540d4401a2014640000c488240703942c030140c00290010001004004041005590010301d0042070368440b12030ba584034400765000b490840f000d60400400c41982e104180b000c458818410120544140d12034100d0300c9089400404151223441c0c01000304a40d0348984040d10140380e4060003500c0b2034201c40c103007607544201c4200c40c5513111508400ca1102124085219001c442d101c601d490400340c01c10b071490010301108204401055401e004940704260b0302c81e004d030f000c24810740391141e103035060100060443c0416000030100714010840d0074016200c2c030b0308482d540030041c03414031421101040024100381c41d55000540c03540c00d005a0070441c0c000d03280140402070303610854144 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 153343660 1250 153342410 153342439
    0xb190f050d0f02131e05150a06020d0f0c060e03030603060105061602090619030c080d1805040518070602070608090d08011701110d09020f0301110307031d060c0306 72
    0xc86511000010070b899528042031005041444108154091001000c500310703459586043c0e00080e201c1c045d0b60920380302c00620011819060001c901001d050790002c08082c1420000782da28a882c03584481045080388a03524401d00c900340407180b07180e1000061104903c3c03e84101d80ea034006845140c840d015980c00054507240c20012601e0100c04424800c16000365502005500c920040c9251f401ca440503030741c401c80c200c15017098001395128244a096007418a00382c00c2c9044c068000d80d17014841200c1054201100f00355600c4201c410440340800e270341d40c80541c01c1030210711040c40081c083c4a010b0001c00c000740c0101d00141038807910b64549605540d2401919038803440c50101d0340110301c10070014090a0480ca2800c001c001c0c102c4c0001c1050400035203003c680d6440785200c0d01c822a911150803046281c0405403014400b004c90091280e52807220f01c0180710310014091005041c2d4408103081400c210041082d2031305500340690b15a86004da241e0f100d2030b48200d5003e8030480d40c8400056 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 153344910 1250 153343660 153343669
    0x2010e01030b150d09021306060809070803030a0e10110c0c0405060d0210022406130203090c060a030f11040504050609010b1e04240f030b0904150b190f05 68
    0x114a0000300a422030f0072800e00c1456065100c0f6440012140c3c5032026407000d030301d5221207600444c64091002491510b803880c002c0a050b009003065042d604138207020841e803c0c0000560342c109601032b0001481c025800c1100c0e180c120150b0341170b6205410007188211120f0070001a01550101c1010354200035603503c10001211310403039256500845826020015090000c03124078032420070300442d0070395109000c00b046000e050b1004003280c00e00b100d040000f076040c0300c40617a540c511858015030039410911156900d90070301030b900d20b000e81c2c804143ca600f124400d0b04495400d00c2e80e19800c200941649400b5501544a0300409008901300f002042c1a418010000c13030498900f8840c660401c14444806d03204429001350303440229505100129504074151303040600c2140091380b5819900c005030026002c0d8015260f0381c4117040c41d04000804689810390101c4d4030541c094417000540a0302d4005c44000c052a00407150044075000d94812010703d03003448182a0348030340000c4c2020315900e40411 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 153346160 1250 153344910 153344921
    0xf1804060c050a021b0a1214190302030306040b13060902220302090109050c070c0806190b0a030308060310060b0c0f06010302010903200306090a1103060103030503011511060103030c02010e0103 85
    0x30001a0320112113024400820072801da04281700600f200382940d694500c0440d440070750300f429200510440c00b1184000f00c00c000e05012030354464290780c040c84c0a0b440c06516404014011800b41d6241c03900c03d141507803403009002c0786849009041200a440c0c104e000300a4009004101641e1a034554000c510724907641c18404680c1c2c01082000d00303a09040031705016150260080c1c5681200380a031500081d51080c5030409070815000424403450010754091510312090002d0400500d0240e483c0d0a0303407202402e00782a40d4140c244840700d5150800443c1c42c00d41c81c05803942d04d503407134000d02250003442c000c0100803150744581219a41d66683c600030f07031501c20170b01c8001d02040c0007410402c00600285028115207542039003604500e00003401280c188002100c0d1541c0c03030703000070500c0d504002c000b5100b81011001940144507540c19030b076001e8260700c01805150384000708140c00d081c0c101d20800301c250540e83c04001352041c5503500d203809000941d895104901040da00f0b0082d000d594401d1182 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 153347410 1250 153346160 153346177
    0xa09090b03120712121109032b03090515070f110d0e0405070e030703110a14090106050f130b0a030e031218030c070b0304060e07080a110f1804060c05 66
    0x306441d0900540d0344511000c04c1c5403540082c1300ca0103106405940b901c0c800c00640600111415940d01c210b03108040c00c00510100388080703024403c140103010452a880a1030174001400c00060018060074030900c3c4c035111514906441d0b02940400080d02d50003502c075040ca0300b45488800b1226061842076840302c5060040c00006080700c1c2001c5864a0700341c002c0c80e0820000d090140641c01c0d100003181c203154440c1c2040d542102818201c8050b0709182180d0340050528040031311101c80b5001c0012803107041032045004106020401141200003803044410f880c0a01c60030b40711080d6030701c3d00352016810500d000c402203441c002d00100c0960020044845c000d14102c10b980340c03541ca40081c102c40c500c1c007080c070800d01e100900040322802c0c1d01b084410f018051000030151240b4003450590161409403070705c0182900304040801003008005010b04030140d00c4400002c001116402041c030ba0315141400541c00380012200c07403a60070640c900e2502a5001d030300b050094249406c0156158801c500c80c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 153348660 1250 153347410 153347443
    0x5010e03030f0a0c0312150501020601050a1206050c040f090b0414011212120c03090c1202030304090b0609040519051807050d05010216080d0b03060106170a09080a09090b03 76
    0x3004243d9072042444070340c0e840c824180040c4c0e082208103944101e407040c405d80d0401880c081000d00c00341da0104211070040c18210b40700c00756103060243d9000c02050304100104083d0f102c04c04140d039011090141d0780900440415500c165a84801d031780090b004000a1501071840c0c1424038440326a030b41c3c1e41506a41040002c01c1880b1155542e41480000703c060403410003540304106940c1e107000d40a115002180c903503000c0b90442407400c10081c40312555200b072500f404004c030b150340142c5020050364200d6032001000a803208101000c02c0c0f00740725000415520500c4c04080003101c0d5a075030701c404086030030148100100c4e42d4a07008503280c1c1460084491581d800710000f0480740c076240780c0c9001098898000982407a001c840c801942e040b030714030300302e43c441004203189041c2005840703413030414001200100125498420054a000702454020b020300722900c000400400007070b0064104103602418642d605c4890300002411b2500c00c0c01002d0085040c01c40714225840c5c00a100c00c00d1030b03030105 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 153349910 1250 153348660 153348667
    0x5160f0b0415051e091005090c090a0911010503090f0709090b090c0f0d031e0206010e1e010303050c01020c120c0f03030906060d03170108030a030606020102070302100f06050607060605010e03030f 86
    0x4c1c01d072200c00030050401200c2d200c0c001510781404441d020303050141c0346c0a40240280104101003082d1914010501c103d403c2ca4075070401c0c08910200344020701c5803401c5c28999682e454188007181030540c0343c43d0305200c0e0311401c07100080c041c0242d48280b105a00904c00c1c00030585400c0c131301c19103482000b0300e200c1c1d01020300e2813040c52525008090600f080d10a0810002001c1d8440c0d644114042c4400c04c4030140c0c0107080108850085000c1c91a4011790740488500003c540410b000b24039001804094108a004186180d1280095046419a0341140b04854900340c000304034030b0f0f4541c800100c121950148030b060284081c030001c1528010042c0002070121a950301040c40b204070f60443e0281c6c1082508103036000c5031056080024007030008030000d1a51020000700160540f800d6a01c0032046a00c1041a800030981c0420402c000e030007015004144014004152000f902042d00701d15407058000580c4800c00000c1d0f44031004490302038075101c00d070081c1d2508260312401502c8024001e1071040 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 153351160 1250 153349910 153349951
    0x1a0a1d07030b06120f010311030a0f150f020d050709050105090f04020904150303080709060c021f050903030a05040515070c03060209130e0a0c0b0f0a05160f0b041505 73
    0x203401000603840090202418403005400c6513a1024066482d40100c994810051042c0034401c03e681443c45000d0b03000f41101d400c540d41d11410003520f000054600541c2a10702c9a003407a00790031404820300310740030540d01c40d244079038041d0003404243c4441020440031580050554001e03400c1d00c00754400200b1203041080c08405000c007960052442642c0580c0e14501d060030404030650400280d07020356103403ca04e282100c00030340b09a8080d00664140081c017400721005a444112440030382c420582d06051890000206607040c0c01614a451390502000c1510b2410340c1d0f011000d4411104101d031904042503a44a400c0e249101c0e1020141c0034412081c400d0000c541250014803140700c010f011140301d242101010400c4a04891000b8003070741069407440c05001040796440e003c0c141c080d100624102d640b032504074042c03003035021460030b1001c042400e00442e00d03000c2417421960742002d81040781c224545032540d8400c4048904a400d5404c051600d401c1e1903081c0300d05d5201c0d1084803c180040c2001 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 153352410 1250 153351160 153351167
    0x206010e010810051009020a08040303060816050616050f0a02031b061b030705031317010501052808030c01020301290403030804020f130501050123070f0c091a0a1d07 73
    0x1005a21750300f4000c0c80004558400d84003c0c03100c4a81c2e40c2e218441800d091900a06403030480d84000380c154444084800c20311401c86082044a80841d0602e50700c1d0280078000e5100004000c026003c0d0191040c00d611998000c5044c9030404d20841c15600801c200b50b14403440c030020b0110598000f1400c1c880b412103401a41a5480313210740f03c10889003803400940d619440d551054010b1072954034012070421240549078828020500d40380000c0c483c0350304100100d0403c561a402139518005100075114a100d0792281c14000b8001c584156580e4400700101d507400703503000703209a18100c05506141a002e00080750036400c2c0c0f07005545002d142c070386161011910607801400581e0b001c120008110040d60350100c03101e0007411442030104644d0b14040c00901942a0a022040524a0140e141c12620342d441d0441d80e90581c0b0100b4240c035252281840e00703e001c00d540050840360b2070f00e1004083d50b101071003c200548070444008414540354503915032003070030004c0c10841c800d14403804205443d00 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 153353660 1250 153352410 153352421
    0x30b0606090a080609031b01051612090b0405010506010813030804020108190504030915030b0604090f090b040308010906061b0b150a06090509070c080301060809010f0606030c0206010e010810 84
    0x90040c6402c081545445809092640641e502000c40e800080d00d21502040f114000f0205400580200305510748004c0000c00040b1482a0304200241e06100c8081030442c1d6000c0014560407211042c2c040c641850400c0c02807a0a0303c4841c0400c02d500c2c0010210385500c688088616415641e00c0b403180c449900540d46000080c0440844204034494201c0009651145d00d104d940a0703a15604818602000881851901c070100000c2600b07141e80f942c002e4036846e00300c500300c1d21011400950072030604562030041914030801007003401500203000905922400042c16507040440402c8100d5079200182c0d0b80c0b03240f41c1c0c003004501c0c4044402d580450203103000745a01c1111060b091903009200710000d919601250031440204e200928240180e041880c8116403000103410251041c1140d42c44049942c0030500c604070402540000044c0240d80079040004c02030701c000b80601c40c50341c6905024000c4c11124a41c0c20061150700000640c00d9250b9030034074101d0350488003a00c4000b02d242d00001c058031 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 153354910 1250 153353660 153353677
    0x10e0603010203010b0d0b0f0d050c0109060801210f0b0f041703061509121f0b0402030403201011090103290f010509030a05030a091a0d0207060b1e01030b0604030b0606 74
    0x43d08c00091a10945403801c041c0c00c00c03440b92003d003030301941c5000050301005064210200700034001005210141d40e40301c03030444003111582001481d008034940301011009400004000120042c140400c80889112680c0079030700c149550003d0101c030501c3e001080c04111006a0b1207070040d940c1070b0516035004e00500c11008080c1024404600040fa844d2500f1460440c0302d82c0c40080c4581026041018420380303015500c202d80a602d9824161002021203107800142030340c400d036800544400283c01c01c404507000f8450341d4207101780080ca8450303641c1a00800e58003400b007401c0c4042e0441d10f0030200840a4600c1c04607098041e1120340205100c40d00c585148442d0502004018100a0781d40c1000074080311441040155074076689600010302d20616580010059244019214141c1c1c40e0041a81c0481c00806001a00c039171803420544003418007100143c0d0041400d00b026000b440b10316841500301e410a0b00c0c1400103420b4001404024420341c40007611013003248021904a203441402000c03480f = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 153356160 1250 153354910 153354919
    0x50a1710032405040305191b0206030c120405010603140c012a0512030108120c030304150204030206070f1218170c03030c0106060f0f1709190803010e0603010203010b0d0b 75
    0x1400c03004040340c12603100b5138080c0d004c0380300410440301e460780c449462804400c41d8500040500840d0641040ea055060030003481190040001201c050106c01529800300d8010a800c03c507041c40e0804178000d1007280410754646504440b40c250700440080d003c00500b0301039503a40d101440c00c001d0101c0c010030150113151705205040a030300200c1c0b0304000c0780346180502394480755030b545080b0001e440c09151034003200d1861000d116012100c0b07008416250f00640100c0d00e00044401010010001c2c0b0850300000c2d800100403c140c003d00104210b98a1079600c41d4040b51403401071001c2c2500e240c58100100710840079042024052480014030b00c01c000704c540340c1282d010400d00b1001a055400805000d500c1d40e54a80c8100125079010803058882192400d081512950401004002000c0c0301e42c0301c0c400501e0a0003148040608100351030021503801201001040380303160480c0c00303500c203108244200031003902046881c501071084030b048643c01440b0524062641d199040544652413259902 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 153357410 1250 153356160 153356213
    0x10020102040b0f031501030504080d0b0a030f080d0b03010e0304090906110c06070318020612100b0307020d0e040e0604170d02160203101b0e060712050a171003 70
    0x4001d0342c00003510088005200654483c54000e0503012403802c03000d001030425007014240004a0301da6030450b00c10000400000c510095120003240b0000c413039a10080001c04903070700071030070f0045200141403881c803c0902070007000e543c641010700381c46081e0900710b070030b4000300400c002000031342d17100111961103410041001d1984a60a0506801801c4843c1207900800200251942c1c14030a4006064240300c100740040900d402180050141d040d801c10100c035206c0202e500007043c954100000d00c652000e50b81d0700e1404200080d19038204803964008101180080c2a0900e00f60181800801007500107004a503a60f4039010815880d80d1403c44403140b04022800040a040c001405c25601c0c6501701803241480784145441d202c909a290842a071410000d00d03110140d451650400780618a40004542100e200140301807090f40c8004007112010540d120702c140d080800b134410402c941c2c07910b4442140320b001d8490034400417518107590052200c01807002409400820041041c060b100a50 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 153358660 1250 153357410 153357419
    0x406083301030f1b03090312020f0f07030509090702031b030418020a05041502070e06121b060c03071b0e220821040c080705180402010c0210050a02120313021002010204 74
    0x4110407604d0310340010380c8610054041c180c00510442d49000200c4e401c501e1302e500003500100364021b4204400c0b00b00c10000c1c0c8081814420010b841040c1d200900c0100203040005000e556980140300c00704407000c05002c1000c4100001c41917408032000302016591102032019000000e5000480c0c2209002d41444003040c1e81c401c08074131003074000c2550010a01d0320b05000300700c401c0701c00c0108402c1c803070031200c042840c8807403020030015840c041d20703079a8405140c0c0200000b049801000c0c041c1c0b029200124a40c001d1007144889900c580c0c014592108250b40c5492130000360010841d85e4014440d491070106110b0023007643e41d0300b10203001c3c0a1031801d1003130f070a4051441281ca0b264507405c40300c00206000501c029103840304010200f100c000d1801d285040f01282003040c5503400803030705214000008056900502107411616401440b01402500303064001d08942c203e5844600148141048803010410600c1280d0150380c903510b500350301c84015801c118860110300b2031041155001c1c0070028 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 153359910 1250 153358660 153358691
    0x7030218060a1e2102040b12070306050d05101a010207140604030b0106111002041a031506030c04080c010905010c02090402130e0c13050f1803040302060406083301030f 74
    0x800d1658140d5494501811241c9501c0804c83e880b40c1c50320150340704110402c1600c50a00c11908051006a0115002d5450031020340c01000c081d07115a41121000e443c620030003001141c002103001d0301000401842038041001c41645001d4105507026a0001c2c200348031024000c18001e41100c0e004000c14507185c0c5030703503829450031000e07032003840420031304150007141e000d0911050a0300b00c1480e10840c246850000d4400d210b0b460394000001200340040482c0703460700144280010760710080e1240b96a810986003c0500d40d1051154029600440b1340003209176204460a50440e00305940306a50007030240c08002c00400302410803131380204104580c007007052442c0200010004094050300c0d4002004080c0700028030025040c0108030701d000e00300144200c0d0020502d070007100d1590308920b84c0342c3c100341692035803142e5000a507200e58003240006000e907104c440c240c8940c02c400304041c0b03030214200603240e07070040e4060542d43d020700080d401e040c1d81d4802e500046d40b40090351404109400720300a03d1 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 153361160 1250 153359910 153359957
    0x30b060d140d09030605060f09180307060c0f0906050f0901030203180d02011a0a080709020319021305040b03010905061f0306050c0a180f140105070213060e07030218060a 75
    0x100214883c110304000380501485445c1d4482010f0741c0450240b24144006100b42c81d00900c41202642c00d9942c01941403010000d403148103501007000c00861480c298090581410f4401d1100014032401002c43c2e850300c14410340340c461190301d040c282005d55100054029400045c903e0105074a28810080071800401070114900c856800002c1e042031030038018445030060f021418050403610f03004000d402400501c0300304454003904010b0302c1c0c0e2546080d29083c2d807042e441001603180080b03505200c100c100c1c0c09072070440c2d00484081000c4000c030000d042c243d17645403001410b940c010100007008a0ba4807100030f1468400480d910426076100d9880342c08562060701e03010140440030580b140341d036801800792107451400301403800c100c1f45000c0580b042680345000b520b02c42c036210756100d6a0344e406101030301c50040d0b000b0410b17212409200700100045c4114401c0c4c1110701c10304008201407900034422500e100d0000c0000305507084513142400900d0340314045080801c85903003145000005044000c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 153362410 1250 153361160 153361183
    0x30b13031e1205100303021b06030103120908060702030c0c270a0b040c0e03100203010e1501030603210905040209060901031d0712031101051303080a1d0f120301030b060d14 76
    0x4c1045007107080082c600543c0b2602a42c155030400b20112640e42d400d02900d044990000418000ba2481a070031260401c04d94096085441074000307104c8807a0b0044041c01c2c900c1440c004444a05c2d04800030410141e00022807000c0c078521101100c10360880305401164001350003c00401c0c95026240858102d5140c0780e184000148125814100c918040c010b01c00305441c101010b60455042c1401110300720f402900301440d00f05000d1443d00c01d640650006c030015a044050620790654407000420341c0f1005503055400520341a4000c90540b8191080e142d850307001400036400c103010140154001c021800c0c0c0b415011005100c0042d4221040050f4000341002c080381a03c1600300c0e250180032440b00782101c090b981d04100400440c1d00007081061aa02d80520f01501580c13203001d101401008000c1400030421600c0c540007a190380300088204103141c0ca4811500c4030303252858a03800600007808024102c0e0482c00c0070422614000e103901c400381d4010045428004440c641e6203241c40e40341500e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 153363660 1250 153362410 153362431
    0x1209010605030d05180607170a17070908100c0f0c030201140703091b030b0c0f0c01060602030306010f090e18161d09030901120c0201090b040c030b13031e1205 70
    0x2904240d80c06004480380450304107403002d90420915a0b02c0400c66185000040f046031004580098901c0c4030700116050ac4a41000400050a00b41c00050042401d0f0161002c14801e03001c040c00c10007582c1c070811104905603594481e14504000301129886c6140506800b1592552600f2000e4440c10b840c0278080c44040c2c900190700411884d20400900306000701401c0c3c041c0b142c500304082003091015550103002004a80d943d140d060049241c0782c001d001a05c04c0d83e6103031040c04a4496000402075000b50002d88071042e01201102c802c849494560040c0c6401440f800d000c5460001c4800420041d4000002641e100c07217034441031100102c0319a03200e03a120460705d039808807010311607118941d0045502800f5518207405480080c007800000c03110300d442d0b5a80d412000404d0340c03013980302e642c2d2540d00108800c000d0030903041031260b5000b180000e94022103464049001c00710348000011525074503031030312401c0722807480d1900001e034a000e41074414050743c400005055803052040f06c0c4103010401 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 153364910 1250 153363660 153363667
    0x4080102030f0601051201030b181006080613020f060c0f030d02030718150c020609180604050601030606021e03090a0306091b060c080d09060203040f0b0601080c1209010605030d05 79
    0x582c141c0c80c0700540040d041c08000c110310421410580c40150640703420690080c00c80e100d031421712100c440446021241406034a00303010285130036400c800c08032505201200c415481c1d0a52400c000100c580d00258052110f4450043c0c40c108280942001403412082c3c030101005a9403550540d44140309041e1a150700000700b18003250004a0f41c0b0313021b04402e82400d0381070b081c610851541c025800112045c020006c20301401c40d5242012584003d1010307040502400c3c03000316280a01a082d86c43e98440c03810300740003ca055200380729410842c1c41c5030b030041620041e603081500c03054003800a517030001e0004100398086521410f140740021407040c2c100042000c114103000c00000e050f001c003042c88801c000d0b0100985544044d4a11055401841c15030b6694504800c450040c114140000e00f140e0001c410401880812940342100c10b01820700407140f6613440e03004460011040f103240a4101d030500100300110300d508005640204040000245035849500103850140029502000554000f = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 153366160 1250 153364910 153364921
    0x20d0822061101020703080a0902040e010c03020403060e06040f150b0411070203061005060f1804060303110f031603030209010219051b0607020d0b0c0d1a01091509031101140408010203 81
    0x70000c0b88100080001c50802c6100d0303038010709058010b06010308241e10380c4e100c075056680e203500c030942e40c200c1c41000b00180008c61038064040e402a20003511207a140201e008110a400f040062103194011031000301202c4a84c1e40c041d01440310a9400d0070b143d9030780c11105040d11240302c3d802c201d08903200495161300b91031040626046008260038031024004004100380d80303500041d81c3c00c80141c1e000140d211401d026404220a00080e48186d00c03d04000c2c0000602d900810441c002c204a50140c901c44505035200959074401c82d018840000144402e817404284664050010b041051055030107142c050943d107844003400c000300380d48580281d210302c03000030500c03028200c0341c2ca010b0b80c500f42004a0354001134450200000d02400d5400700000160080e007020b000c5400c0701b8029001048906078081c5003007a080a410720160205032081d902044200c00c900700d00342d803040c090f034401e90350364210380d901d403d41d04c02e011042e418000c1e404202d443ca000c1746070280002d0084800016260b1074007 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 153367410 1250 153366160 153366167
    0x60307050a0c08370207030305030702120d0b1c050303040809150a20070806010302060706061205030903010b061c0b1210020306030705120d11030405060a050a020105060a0b07020d082206 82
    0x20039000d14141ca01d01c1d61441303e41c1e03402081d8001101e40501b00f440c0c4a50b2154010b1781800b4450924500924001601c40120144c0c0c0c2d115a41d890420754024404004000c0075811030b04c607000001e40303145d100340001400a2581c900410382c05c04007074417608bd45403141c008107505400c203106003c00710b16102140400d50302c072042043c080300300c4000200011441c2850f10f079181c45040c00b01900400d0001030040503c06d0341e070441e800401c0078140700540c00c071407402c0c02c58483d001008030520035400c1070202c05140c900310003036416000700e64284030888100c142040000740311411045070024180e944600980c8001e00c80141342c071228100242e83c0e03140050815007440503d4100500c0760040d50040700403c0e2000844545060041c203003c400d0500100f2914030b0741c01654001640984001250441c0d0f03030303201004e48400403807074000344441c1e101c01c010840a80c050380100c0001e00f00510405000d85090089400c1c8a4000e403c507a1070600e0040400d502613003400e0309211008142c0e2b4041020960 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 153368660 1250 153367410 153367477
    0x1090f0f05010f0501180503060903030a0c080105010e010f0201320604020a0f081f0b0c010f06150e0a0f0305010504150212010302040b0f0a0608160905060307050a0c08 74
    0xc2444108030960401e000c58242c1c480c1402680e04002e19840e1818030b41c0110346003100500b0004048917140c0c40c04902480c1e4a0b4021164208958280a084101c203030003141c803a4180e0314161603100080740400c1c0111803510741a5104c004564803075680b60000384203011585108403600c0c01080c5040c0b900f404460380d483c00a0515401613204021581c8510342c09124000904020710b00813515456110720007183c0710751442c424092000c0003034002402c07040030000b4a0490008002403000c4e0f400b17880c0e000c2c210f510714825000388020300305100c00c030140710300d22584140d5001040d040c2543d4803198409030180181d04119610b81d50f134030612050206080580e6150903103214103529029800c0b185840885047c840280102d4491003609815070b140100440300300d2000d0490415150b603001c00a1405105864140108c885800741c4017281b071080345c01200f5244080c00c198a1600d402c00111140d0348a4008841007200808681c0000b480e110000d1918031840c0201400031000b125202884c80d0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 153369910 1250 153368660 153368681
    0x1060617060111030c0304090b01080603160611031e0d050f042a08030304050a110109030203060c03090703080c0a050606040b1c1704091b02010504030203030c0c1501090f 75
    0x380c00002040300e200e000010a501810a00e00000c1c581005580145580200005410b81d07000100f004640c001196103c0407454200340c2c0c0340c446c282c4407031050503120034800120544d4500120f0041c041580100100c003044c2034490304036031414840040302120051489128002d2110009100900100d280a100d41041c845603210009050950300e01080355807030b088180000c20030000e01c00c10302980e101c1c003000800c0c0d40c1007569980e14103850030b031b9202d00e4221812108644243d000341041e502c50480c110503a135001c1d009160503180c82d100c050030f17904002c2282038244643c640c0030000a420f20007070700c4040c00b03e40040030407150610742039050a074014035081c010b6140c880814000d644078131642108400d07100c100e42905e0881d081000441c08400030308070002c10001000604c84020340d02503a9180c80c081c90319402c1c0c03010107800b02e0a1720029900039006a20502c00b04048400c41c800600841422104441d6501072400052034002400d900c40040d160341c80080120342401c80c0242c5c00300d603 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 153371160 1250 153369910 153369917
    0x5030706090e010315021201120210080c09091812040f090515040203043002060c07120f020a0b0403030b010e040c121e060b071205032503020723010606 67
    0x10b0074030300e240003400c2c41448003078080307076186410f00031841c40c035030440314919130300b20141c0c5481d84c40c0c81d41c0641d40842c1c118100d00842843c01c040d00744910440c03403203010741c0f07000c2031480c034103100721041041c0460098000c803a0030641112112500c5010407039107020030504480c1ca511103161030484511480c40740d00c0340c030040c1d050dc0200405201046200c107040c841c1110b0049e2a030301e91307041009200f6031070001103c4040310488001607280341ca00e03e0b0310100100d82d01310ba070386944441d10003190b8083e844005105c419005502c0f141c40d4010000280030094034412515456070b2a21680344c4600d0588080e004207540b109282c003c0d590141420625403c01d1307400f4014014406401005462042074500c901e941c1d07920b841103640303040c2130101c0c54600072035009c0c00302e90707101da0604005a11000b0704941741d00c402040a0020790054044e207110b00410036410341640006600540d40145582c0d032881019401c00c062000604010840340c150088041c1d03a03030151240b19045402c440c41c6403c182e050 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 153372410 1250 153371160 153371177
    0x40e041e050309010c081e04090c02030412080f160f0b0105061303030806040b0a08010c080f040b0c0904020c010c08011a042124021804020a0806190504090302060105030706 76
    0x421000022155482d0003031914800341709003400c3c000c0341c5006203000d0074101c503500703410141001c0400019000381c1c0c481c20710421081c0403510382030b80d4a124611403a8140d00c030752006000400c04038400b0307080302d0020212151910b06559000c4030f11040ca55400c07640c001e0300d09140b0043c0265a15102e001d050203581c5c0c10702d003091a40c810f20781c07188035200017010032254000140641d2100e07000190345c660060b12080c03c2586520840e4007804900d80b00f000003524074000100038584c2008072902554205400e200c641d03d40f110039450b203500c030319050f54001390204003d00c0c1e0650244240702d880c407440c0d81c0d0103040754100000c91001394409501560200400c0c4030501c06400002c0420205144034030090010380d507c0c0ca00780200340801600c103080c0502c0190b01180f0500643c00500349000c102c1516001d8240300c40810040f4002c5059440000f17a00c10000340a40c02d00a003182d045c814044584102a59034a00090075a400540100d006800100040001d0b00b4200108005400d450500000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 153373660 1250 153372410 153372413
    0x20c0c01030c0e040903020115030b18070315020708090a09020310091104090902310e1501210b09010b010e0a030519030507120e27011403010e03040e041e 68
    0x11124101c07100300c0c8541d540d4004101014000d41c809d807502120301028070300140d500c1c2440c000c0078508542202021101c0c050400310300a0105400c010340380e02c45100702c400305009036020002d4008480464191108002e400403641c0c0790400786c0d0042c03490389400359a03440e00603a0445140155030100b00214180522050400d49100950b801e45454620001d60200f8900009a1010803042d40d00d140b42e1001c504403428110005e40b50440c0580c00300c0130b000991048030650354030503098540400e542c00b410014010448014516400303500c907000b000302410300395111070000b0711056901c150740340e5403484884080d507013043d066041c0280071144401b0582c40d40e190f1a48907022001d05c00c213038440004680d0300b010701440540d407500d42c1050b02d80c2000b0140c010050194022580320303c0c403030405540c4070300d0600f0703901e9085010b00c1c1d131013a14440f80764a4001503003484d40001203400da042d501c41c0c1d5031845000080004d8402094280303944403003400d0a0510041d00290050800840c401c3c10301d6040 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 153374910 1250 153373660 153373667
    0x219020604050d020d060e030306090c04030c030b1f0b040617090307080307170901060e0115020705100201060b07080421050c01050a030b180601030e0c0306011503020c0a06020c0c01030c 82
    0x80440b04156901ca0b22a0524400192840280000100300c0d81c500400d20340c2c003101c000040e5108050a03a0440301c0b0f621032058100c07050185200c000c0a81a10322401c0c400201015003454204c402c000781c95802c0c43c040d019a029406039031308000030ac2600030408000082e4481d414100c0c4250b606070211a506002248030744a109249025003800c10001c049604c09124200350300030309880f0041c00602c0e00b014028240688514800c4100c0700382000008180d000010006104600040c1c00501107589001c1c00d110800c0c5003220075000359540c6590006141c190000241900c500c06c001560b616420300f041c042890f10b0f100c61801580745141246800544001402d41c006082402c0c550b4030f40218220071006002c806490b45e070040c4030169407440d01c80c860802140980d0090b03c0034442210b11814a940c0e9011185510b940343e4450001001031030240301401d9100155031802500d02040401001d10780682c6010440f80b10342c0c00100c0d81c45001d02400406e10340035007440d09000031900342d44001d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 153376160 1250 153374910 153374917
    0x510050403080928090b0103020a05071106090d06140a0b03030a1d06070305120610021506030115060503040c0806070504091d0d0203070b010509090d0503040305040f0b040602190206 80
    0x500c2d21400058403030165403805480c01e0707070040503004c1d01e41c0d1003840803e00da03444030030f807040c0c0ca461802c20361a0084ca42c001e00a60381842115503400d42401090b88800c0090103002040326002081004080c042c1c0d05c940d403904003814011000400c08603800ac46142d00d880700104002d1a4500e04000184680c0d008401c40d01850707460b2030f0150504514141c0c120b4800c0d034410340164040000592082095003150280c1515561900300c58815582c030130512499105856203280160042ea010500504070b00341800e80000010300006960008000244171050103074205c440402d034080b0402c82005000460400901004d2018020074209400301400c40d010706e0103038000749903e0700e85209101030f1b40a0029101d0303e04808980410000d0702020f500e0380d006900582d100c01c07000b40042500e080400d1400e0140040b00001c1425081600c03040310941c002400890030818200300015091900301a46806060f08180c1309582e1381c941440685844480b050250000b0110801503000d6981d260a5 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 153377410 1250 153376160 153376163
    0x2041802033013050307060807170105090105010c0f02040e0a020307092304080909010b180906090109090c030b0108161409160c020301140906070804172b0905070510050403 76
    0x1550b100d4400c6074090f69103891030b0300715540610403450002a85980259441c1c00f409003a118002e00442801121030240b00c24040c1a800c040b0002c0108100d51040c140c001800303001e4848601115070950000342640c44204400e12194880c0c0c100000f5441d0500c44000182400f000402c01080c024a60142c0d8500c51030b8078140e86000d07100050107212480088420106004100d05c0384e035070b114034800f2440e420020110004c0c3e03030180101d044500380884094041c14000385207120580c6405006e801078051b00704112101e1504500000000b03a100e00d209010f442c4400280072280a8030350181460310750fa900c041e03a02c80e2403c4440050380c5800c5021904900c200c42c1400865880020560700e01940b40b000a400d580307042c43c01d40980c29801c11250141890509642c2c850320307250402c0b00c4107881a103000c0e008406155202c4c420702c4595000717259001540050300d2440820a007031034503180c54540f501c00000d46900400342081014045400075000403102c0c00e50f26400850020009e0056000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 153378660 1250 153377410 153377503
    0x3150a110702031608010c02010905070b070f02060309030904050c07030f110f0f01060513050603070e060a05101101050f0106090603020c210c0610030305030619030204180203 77
    0x201220442655021501c6203900541240c21805204240040e52021841105265440d100803c03884501c18041d244032603030040300510030719003440007492543e8450141111402c1e031110904006882c0e40c1e01035481846000050f684030410401800143c5400030304074a41c600d0100086400a504250140e18041c918645610f1000c0a10751181c60401d9416500c1f5075480340311912802a601504038806543d010754a00600d402c60441810585d03d0a0ba00b031030741030700008814000074080d001502e0340498014100c0c40107a80d01c8004c01c0d00000c0f803000050014003945064015401c090249903000801c00700003039081e6140040c01007800d110ae01a4404241d0006001d6041c400208521302110f00d01c0c0d00131510500804400d030345141c0c42444c1014240c0148000201180a0755402400701c90300b544942c0c0ca99540c210030803800c00c40851a00101c0c0512460100240c2c80e14840c92056020721496001402018010146001002c3d003285078410305003041012221038070100003500203143c02 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 153379910 1250 153378660 153378671
    0x406030c03090503040f0302030f01060608011806030804090501030b090a0c120204141611010c0203180102010e1509010b0a1802090111060c04061106060f06030a0204030c03060203010503070503150a 87
    0x40c0120080d10040c034010b8414840860b020400b8020004460b04691007141220030303401c0d14050290030380b801c2d482147e02041c100001040800c14160075164640d150000c00100c0340c0d2030780d54821440c1c000c0e42041c0038440d660401070041006000f01c40b80c001242e00d00400f08c51200307541d80300100e1028003c41c010050401c100c00d045407a0340d0814082c2d407241c90480d801900d060413074224212209040f020004440380c100c40250301c0107200e035028900581d1301851a0503503940100e2a400841c1d441a411513503518940411030106100504a1004030915110141020450a42524420400188a0107449000b0441800c030b00281080044900b5409611407240c2c00c016940b0100583d00d240a50007180200040da00c40c7c1130050040c0c540985a845650006200041c0c2e2031380c04894894020ba54410040c200f0f24114010795440300841901502d020340703c0e900c20150342c28030350003210130300e4000c0018002c51800b07100020107014154014500c0c4291040001824500985a03210381c0350ba61 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 153381160 1250 153379910 153379931
    0x140c0a080a11011d0603040609050c060310051c080a1206080304050a090e011415180f0a1a060c07140f01140c010b12030c01380f2101060902070206040603 68
    0x1006002006500100886c1c2c03685002d080c200040c00742500c6c00c071014040c4201c004514030313004050b00c2c086c403ca440c889203001d0401083c080c0d04e040407604100c00c0e03441441900300161806e0010081c10072a136460720084481c0c42000019a0200d0f080496150418002805652200d28107101200e40d14440401c1a403040c481050041540340b202c803584403030f544104411541c0d502c120a44640d010381c1c4413034018101d1002c80640361419620600c81032441d001103060b52a544c0c10101442c11203070440481d240d1034400007403181d400107200c8140c0360000f41081110040e2030b0280b001c0354001f41d95a00e1500401c9000070812011003803680c400040214134055014000d41c02a90345c05405010103441e03404c103c0b0440d9494200300c58501840d801d00c0c640300440040d181c411800b119150584c4041180000744248454901822481e00046500d0709000c650752080011010aa10206403500254034070b0810703403d58200d50040702d000c038010851100180c5401c01214111072980c40c0000e010701d80b4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 153382410 1250 153381160 153381197
    0x1505090d02030307030503180106030b010b090a080706020a02011d01020604030c06150b0306042009130e03040e01030c0906030206180d20040b01031503020d050a140c0a080a1101 78
    0x10500e01030b416100214003201015000401113004d0205510303800c1442010311401070986255000040105d040d5100411030b140802000d0010030341c005081044076905d1b8420340d8a88100b96100c0c0c3c0041e401000d09106558110b01e0300c0c6119420600703401c0741404410b00203940ca010150008080000c030005860900c4a42c0d4018501c40b40c681a908881c00da8960419540760010b40d00c0b18401c0303141803000320507083c2033802c0b01714106420345200d05244172107003044145d040f0002c2504403035444207140c0c85203400600081001d045019a050303040c1d41182410a078140c0281c00c80d1210a10309003044c4007590310501920804003010076000c0086400d00d02249081144080050260b4040701c84802d108800249800c1150b1090314104041c42034840110140c884000704c1e060103100298003030016060692130703030300c50b03034069011030304040065038901a4007403c403041800c1d10b03088500d2241e11845c102d016640100000300040141055036120484003080004406040c0841c240605100405 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 153383660 1250 153382410 153382429
    0x203090c120703050105070c0303110c060601050c031b0a03111219030b06070c0501121401090f020f1303061b0203120a06090204060201020c07120c030803040f060c0e0306060a150509 80
    0x84c498020b011030300340958003800c18142d4920443c040381c2040d9400c169003804800f070301c9010103140018604e64461800555455101c4441c00301c1d81e0208000c1c41d40c511001280c03114810640e40010180c250007402c00a1220040c4121145c942c0c001905004100c40c1040964800410f040e07079500452a0403070099004101d43c01089400c100d010802d207040c86441c8401d282211000c0c1c94000000c0c207880540c404658101000325043c0405000500c954040745c0d02c0701560044101d070040c9081c1c8175046540058004441d00200180709410900410415000308407540c0350714031001820407200d8201079101d004049000145000e031000144401e6920b801c01c0300101280c103011035440d40c884c40024040e5019100003142d80c425490006000d00941a00060061b040060000524110350322901d42d40e1029000361045100c4189482c0820b400384a6006002c10940302c4607500000c244c2410304100700106124400d14003210100304924068164014400d4140b5202e0f903a101076000003000c509 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 153384910 1250 153383660 153383663
    0x130e010e01061d220c120b061611010e0d0b060405090d0c03110a0206040b070c050114160303090c1203020705091b030c040e15040b0103050702062d091615050d0f0f0516030e010203090c120703 84
    0x120220a040d0600c00c4c44100c803804fe540540d414080d644e100d010f41d69464141110f10f20000c2c4c0007048801c0440d04c110f040d52451070000c0c040d60f600c4050f5400041940d001a0006140c1120001d101c4082122054020000301400e0074010a03040441803031848902810740c3c0084038100e0502603408051190b40110805503025081d401000e031100c1c0744925030350b041d5a048001d44280140400d00345040c040c0c880c800d280c0002c100d4460703c402d81c031001c0f090704040c060242c0c00c1001e00c0041040080c1074409813040b801580d40b000241030710170401c010f0316400405981414606070610000c03960104500d0b5000800080c095110100000001031080c6c0d00109501e102a0381c1040c0030741c01401013245400c006a0001c0030030142d407290780e5036000c0e502071004440030980030000040d852407603801c00050f1a4100c440050a00e0400c21204160b039012204c215107003400b80c0504015075050700c84c04441c0327210130000718150700c0d150401c2d56685d203070313011130301d1044480d110703054040102004140701a5 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 153386160 1250 153384910 153384919
    0x30b04030e120a1b050f0a0504240602010c0912110603070e030a050c0102010507141c060504090b040b07051611030102130e010e01061d220c120b061611010e 69
    0x7040605201081014214504050802130b4100007041c2c42c0a245103425070000800c0350701e0546c80c0004100c000c04403941e8501c20309000346041daa064202091000c02030005030004904c0d01100040100004041c3d040040f021105086c504007080301380c4180c03101003a0548940c0d030780ba1500103050700c40701d05000e001c5500d032040c1004082005008a02d04111000070b030000e02441d1100341066030284800c6004a5414005000b40c0c1840701c441024110304514a0f400043c4484e25003000c94180c0b1185402501c200051368103100802080d4280b00d07a00000300c0c130300107040a40c140100203400e050914040c240c2c2010700c00f0b2040e80e540070740c1151610540032044031040c517a554a005c0d0110024403a0780049030f40741000040325030060815070036080b0200f103114207038111001007040d00d00b00071044952443c941c1400f03407902c1c0b00c14801d01113040182d1304c8038850503881c1184d00042e42d0202040c18020202402425941c0e4014050504880c5d400081031480c800c0c10801202c4042e81e061503258030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 153387410 1250 153386160 153386173
    0xf030c2806030209090a05070306030209040b0f0703020f0a050d15151119120e0a06020f1b01020607050d0f020a0815040507140a0210060f08070e01030b04030e12 71
    0xc4081018000800e010a600480445607a9800c103400f207000341d51000c0c0d013154180001030042800b55101c190300101904000803141d440b5004a1810301040301d00712040c0003000d0030b2005682101d089183c0c0064585825841c1c43c1d10303d503800c1804c1c080c0039404c209021002c0380c4030000b400b40f9000100704026901817040c18995488568211070000c01170365022078941d000011400c00c0200c1c1004840890040351100705541d07980d248103044050854508200d50130110319156550071201b41300501c0030354010325025850303810309810202d0428846c088a49280c035038441c0750341c011543c079600507140d09103d81c49150690030704014009040e00310408130710003e500030b6a980c1000e01240104102841441c4180c0d552007408100d40381900c0c107034003040d0b6102c5040741c460f00d4000205041c001c0351042d81c20200c40c010205041d504950089000d14050315001d0118502c03c004520081107202d4844100f54950b40701c020000201400240c10042c03111380f01c000070b86038207100b000d100300658200c0300c2 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 153388660 1250 153387410 153387439
    0x60d0b06030903040f090203130b040302030903010c050c15240a030f03020102070614100302130908070507031103070303120c09050d0b060108151807110708071a040806060f030c 78
    0x48130341c41030203182d040401009001c14804894800c2d00c1c420b088101032000c40c101a902d403214180e00c020004c404520041000c1ea10586080c0161100250303182c0310b040d22406030040b0603042c4120441700e070004d5034400040228110700300d18249001c03074180700b0500540c034035100440c44a56140d000542042d000d04056410985c2c158001c02455006850402c24222100e65070f59a007181541c01c590f142150706402c0c009031820141c19080f140e0041d500040c0405540c1d218052a00601e005071110b4000050410038040c07d00645084050100c1c0074101541c29980d0203000e005803244e04c490595965101092201e00903004c0e60058800281003040c00240e6260440c42800c04a4441e40025400700208407c80c80780000c102441c00c005062142c01c0302c034101d614a4407080181800100a840000043c10a1050000a0140a03170030060310019081039408895100c1110700f904002c40c0c104000c02c1140340126025401c1a41159a41076480079030001078640041c1174200d1758040781e041c04100e03 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 153389910 1250 153388660 153388663
    0x1d040b060406180b0301080a060e190506010911070201080703090c03020d050105100b04060c031d0907020f151b13030c082b090512010213030320010b0a05060d0b060309 74
    0x7035080c1c900c18603d10350741d500c50000b20441e000a11808040f544441c00c01c0d000561150805c8101c454280d08039204152a1206010f06984003030703090340c19412000052159810b140030340128600e40900d05890100540c2c0000e10124000b4100c90070182d80b881c004080141c01c0d008071008603001040c8001c1e160352070400600800c4181e81d64230a411921900040300b8041348140d408a0341c403911743d000468402d0310255140c0e01001d07100640210305240d07600c101d03540d94083c0340c01076107154002d00020180c0c84000f882c044404201c000401040b500b04900000101021201d603640b0b1615030f6152040341c040303420f980c642500010500240301e900030030060400508001c070302a41e0903eaa00225080100686110f1045400340001744100c50070b1001f820550320a4150350411400107140c1031900d11040c2002c812504210002803003407070a2089514a04000c001010a0703100030000302c00781c140011502d41c02845102c0c0101c13030100e8250800c0466500c012486040644415070380e01d007210110303 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 153391160 1250 153389910 153389927
    0x10f0c03050609060102070b0a140f03010e100e060f031c110c09090d0503071205150a05041811060c06100302121c0507021201020a1101060b07031d040b060406 70
    0x4a00007458800040d5052800308251801990180c0203401c2190401c4074440c0c06510030300341d10042c00101c03803041e114104032400403c81e44648018440c0c6035414509605404000079154500c03588000c04184005803010710302a030041400c0301d8004002c0146004241024440740440807800b540e075461031000d0f03030403903400070300080300f10103941c1c010a41004000c0403880950308081641c0c080001c84049a001d080150303004a1745080c41171402540301c96020507210122190010f0030606010344d17030682848000c3c040500000c507400c0c0710040e181c10303170401c8500410710042c0640101c400722040540700c1004807800310340030106440c0030b458250b040e007070340070100d1008034061103140d40d107040358003800b141c0401045441e070104580c25900e048121026000010140e80c006141d45421303c2c00d8209100408198409464580d644d0071000516421182070364007000c1403480800c50040020792120b42c1c41d444c0301d402002402540003c1000c9002410100051604a1400100482c0460300f051a2 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 153392410 1250 153391160 153391181
    0x21c150302090703180f0807080a120c110d0c0309050a06020f060c0301050a0e0a290411030c0403231504050f0d05030f07110d0e01030b030c06070b1008010f 69
    0x818090b1600201141222000200e011300310b2070144225002a4050404901d547d000d216011306144181e04e45c0b100c1640418052004100039403400340c09803400d401001c4241800341403803901d4181d1a4491907c44405401c2070042001c25801c2104060141e00325101038171015082042b5541c0703680006c7c0d510300403aa04c80c0003038491030380040e9500c04a841180d050344e50260452040e2480e0001009410001501c9820182d0321800344d41c1560f60322845132584001840503402641c0028010b000858201c8550303446510b0003001082003201340d400403142140d03880101034018428180144103168220405e00d00d46001d000946040410124201800343d40100c0688000e800880c0b0a20759800c080480c0ca00865014000241031186403544664446d803036050010000c0392840e00d85081405078000c4101141d05601000f40950341446541d4800005500030440720b410f0000080081c00f030b407040108250320305000a450762000703005e0303103006240c1d041c02485030b218180e18510140601400 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 153393660 1250 153392410 153392419
    0x606030c0306150d06091d120d0b0d0b061207060f1b050a0f0b161b02030c030f1015080703021203071a04020f0103050601080a180f060905010606020a0510021c150302 73
    0x4600404041f01d10401c40303007588540140801c0e03504c41842d510b41d410200743d072203c1c25600d402c6031303003592512140040520b224034002101440d0007810010340320541150745601e60702460302400b4140e000741e068080d02e581418142d08802180b0305a2030440750b0707a40b00402d140100d220342000c100c058003c6214907881040841200da0340c400b843c1d9404181c01181d07000251460b081c1c600c002d04031b0010440503d0014041e694154038080129103002805200f400455002d5840a4800800c5e803081014441d40360310002e007100d00d4810280d03524102400041e10420440705080341d02e810800c1260748243c1e1007440540c002c00045030400301c3c20001c4030142c1c007410442d8061503c83d07200380300c0c1d18443c0300161a030001c1d58440303004041c014081c030082c00a03a07140f00d98108003c20115044105414484e0300007040e503a404e441c0031400e440c0568082c41c1550310290b03958001070000718150720130f41c1d4481401a00d40e00b110500741d041d42c130310a141d52850303072501101c4c04400351115141c0c02641c0c020345 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 153394910 1250 153393660 153393671
    0x222050102030a0e060f0d090c05040c0c02090606090a0f1e0b030903070b0405030f0c030903010b030616030c17010603090203010b010e010512060d020603090a0c0e0606030c0306150d0609 82
    0x80040e41c50348241c0d20032400084501d02074180d11304d0804090035042002c0c00f191410005c0d101034010440310392403001d5491640f411802c0020307203003d00070304454040324500710800c08429070100e141c4c1803000c3c040c14440d07e030104888140f41ca98001600091407840302105400e0b50ba0711411940c2d96052a07032406400c600b0310042140094142164000d40c81c050085180c485992038000304548042c10440702c9000c20003450786101d039900080c0812115050240d40c0c3c40380c1400805007102c0c0c145100078002d0300301d0000c0007016108142d4841c2400124100440c0d000c00240c0300721542c8000e01c102141d1900c0384400414030503815031010110500c00d4000b007051044801c01982c2c4c640da2a14210700085c000c004403000031459501c0a0780265003e00061054542d40d800500350b030f00201d4010b02c6036400844a0f200344021a90315000078242009161624185000401c0f00745c400103241034542071000010130225100d1242d030a40040c11040d1007922803015026040250809110304116241082c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 153396160 1250 153394910 153394919
    0x61d130b012907030f050901030603080a0e12061003080f0d140105180c04050f04020c030301030b100b04060518010216091e05100504050717091f020a0206010501140c010222 76
    0x443e0081501a00c50103c0028001000c590b0340c2e01082400d4109500c1c0c1c5800400250750700080c0440700030544800600e5041a000e01a281c0190f014007201981b164080c400c0ba421407251003000e980d0000d09250350f070b5907000c035001058800c3c2c151030000c10b0320b070072030b4aa6503405003a1404d041e5581220380400646c0c028400325800c0006480c080e4561104110420140c0760a010f40c12981c00c020b040942410711004445017140c000341e01c10740d00be000302c40c1080701060014150300e024101034a801070505042002c024094040c69030000000d400300c2c8a424a13981c000c0040c402c082c40045d01400005031a81e00300c07006810780c10551b1b800684504200e000703003003541c001c01d841044094000050903140804200c09814080c1900c000d012240303000b07200900000b2806445140101c00412080c0d80c01001ca00c00c0500321205284070138070502c900000c540e40860301a045035070918021131704844c800407a41c032601c1191050011903200103428010032403498801d1450350003400d40c101c0d01650302c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 153397410 1250 153396160 153396239
    0xf0405040c060e030a0b0a02040f0602070803040504020d0b060703020a11030706120f0b0a1d0615070f2307050a05060c15070c0c091e061d130b01 64
    0x1560010304a8038103280078002c851295240003034500c0700a0440b501e110311501d440761b10000913a10040020340000b01449620b00d842e010380020501031000300000f51500060f02c0c2c480c05203020700e038421034000039080302c09412a001400c1031580148003c0d500c00844c60040d54513138021310211a220400da0b1a450300b49008210310f0200e854540f1000c034000049256000141641404c0003090395441c5d03802005500c546217000e01404581000400c2c4850929070120350590003405203100d611000c042499040d809000c0c0d80d01541e2012044d182110b040ca4060030752205000c0351401038507000421807a03100c0c0052003008450098510b48401d60710360b4180b040a10230641c0119a07a030080750030b00100d0071000d0450303174080460324105a0140f116079990080010b20ba01c190707550380d1901103840d580c0110005d50045a01d5001007044118038042c100d40e0f4a02d42c1844ca10302100008000881200301d1001031500154070010720002982c40340c900f81446508810201042e040141041122110 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 153398660 1250 153397410 153397421
    0x1020903121b0703230102030606070f020d200a0b030919050c0a0608190b1c0204020f161505190905100608010605030d03021309020a18080c0f04 64
    0x1006005000c1c110a0641c07500682d9000504140d8071030805088000416003c0c0042c0015520464900c014820a0b0703d000030711021840000c1c410303902c10010b00043c1c1d0307a44400c07142e14a0b8003010028000c0700034000281555100c07000640008101b6049465003141c0035211925003200701c0d00811015110500c5101c903000888960020360300a9501842d81e00740d444ca1400140e00c82c200f2100114900c401042401c42150700003400304130603c050050100e030360000040040c000d100d0070050420154009002d034505400388904443c0ca14419806540f101c0c2c0488401c48a664180d40e910103a5000300c0610081c03000044d101400201e1030700c8500e0403103008003405810305d130440d00719020600114400401d201c0034103c03518802c100161700703103080900542c0010003040c00009042440d28080c581807400288110081610411070740b07441c4050b00030500103652045000684580300000240c403515540d85030092081c00000c000034a000000414080320407007590840b035008074400522007a9103 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 153399910 1250 153398660 153398677
    0x370c08011e050a03020114250201120e06040312020408060c040f0501090b03010902030a1410090b010e0a090b030703050307061b09080a02090a0f02160519030801090504080702040c1d030102 83
    0x1c3c40316082016600c9402000c0205858a51031b42c6040e0807038014210b030904500710b0300480d06000c3c0200c0150f41c0c000c01201c0e0159002c1400380902079204d0400e80d180d8400500c010140301c04400b81110701005581030b5005031020343c04841e03541c140aa010044ca4005124005041000c00c0d8080344d203500c1407548600301d40102142a09590030b111440029400c000d206405960b5211629801401e49a080e10701411015801e5042caa0920040e403003500c0007407038494103100152002011540b2422000011114089030014185880d030700020b0a01030a82d00280203480041000703414840958001c203c50100525800007000b9003090542e518407a030301c00d0802c0380d042018036001504205249683c448100800000e1460244180c04103c0c1c2002000d0002c100f01101d0400c00c010042041141455096250fa1134410003a64010b02560701402a04642601c602c04241005141e00545840b25070061041c0840c0c00c1c8500002c1140f040609031300f0321a0b040348046806401e044c4221030025 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 153401160 1250 153399910 153399919
    0x10c0903050616080c090612190e0c100c0f051614030106060e010507111903020901050f0a05100c12080708100b030a0b0109050607030201060302090f370c08011e05 72
    0x717950342d500c0b50015420900001d500136408100d8403505140707880c0d840d440b0340040200d5000d104c1780d260280c4120303903031021111920ba0180342400701c00c1c0e0755041d082050603006c0c6044821002e40345030415000511070002001072140c0614003502c0000000e1314001e0b110101134500a02c681601014242c5013980b00c0c40300440c61040014080394414001810b9003401a070718225607010341d4011031240c050110040c0e082010324581801140351443c1240d006200031240003141c40151070000d031001c0058841d05100d000c4400c100d104982c02002d4401e14070740c100d4180c1c6c1c04510051000b0f0300b00107048408500003010100056083c03a450381d4107030150782105604904643e10713907000f01c000708648141c0c0d82c14000d40c0b000000d00da545480080029038843d41c0049225451441800104400a0446140009103030100412008144028031401c000711000c0d168103200c0103441c0800c8281e02101c4440a810076142100072500105814101d41d1003201a4500c605010355400d8803035050b01480fa8030 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 153402410 1250 153401160 153401177
    0xc091008010e0406051e0a0b030f030304080d0e2a010905010c030206040305090a170102040306140f0c07110303220603090b060f0414090c150313060c0201020c010c0903050616 77
    0x804c440780c1c44594803022031003c410280040100404144408541140040b503e40b020000320f41000d0080036a100f20f584021820341c01c150383c0d00200740c00b69030035806445580d2510082803c104202440700e804040e01c4580511665810041c840313003030b0401c8039000c81c100540c005134551180980042454060340603103120744480c1c0d0b045405602220740182d0081d0340f00e101048500507070307000c0032203114030000042c0c1d9203140d0f00c2e0020a461140342c1210312a6030420800c84100703035542c070b5a0392040341c426590f42c1e52051880c01928045807c4603641d0544004a100c1a888001e80b103529551100c001e14141c0381c0380d45400031002d8a4203404000c010070042008103443c0e0408410864400c00020070200f0000d1862030441003002007140c0c5100140d00420a03044030707052603805008a040d100809603d5460044030130080c9071040c0c18000c28842d99508001e104070b02c00e50540e20180a20470003404000880c0c98010030400c00b1740001d80311405600042502520b01103004002e10600d034840846 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 153403660 1250 153402410 153402413
    0xf0907050a0810050a080303041a010b0d0905070902040b0309010e030903070501030b0a03080a09180c050909040c0b03010b0c0606091003080c01200d0e06070206060f040b090c091008010e04 83
    0x1142e03200030785a803040c11410180899550745010300107015007000030007140c4900e01400d1400700c841c0e45071103a207a00d84c03107140140450340420b000c940381c0042081021135520340d01d29040d4600b4840358090720160780301040c0401e9400d80c200042d40074403003050083c00500817600320b60b03882c0d00c00c90000e00d0f13040d0b0084404001e036501a4208400301d940081c18996060f960344c07a1660154800e07140c90002401450040c0803600007842c0c032541d4400500b600b081440a802006030292040050f001e105040040000b000c0040c030542d0b42c40a8860591080d890b03595617107095003150801601c5501c40e000306000101142000e103c228407a100b070b810041203ca25503222225241c0c1b00310031000255407200c410342444180000d00001c49418003002540d42c400703950750041225001c5600081e240c0008081c8034003564001401030304068100c03000442c070540d0760f000a000340038180e0882d0b00b0884d14410800129041d402900c0b003410705980c1020940d036441011035980009000f010328086a07200401d0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 153404910 1250 153403660 153403667
    0x90609180c03010c0513082d01020c0708010c02010c11030a050a050d06060f0e01030507020c091009050f060901081c0c0204020706050f0103210c12020c0a03110f0907050a 75
    0x1500212a103041e10782407000d00000c20f0030344241c0c004000c0812000102e10303400303c2203100c1080007054844d02a000121090a0000010300b1030110350341412907004007030001036420b40c1192702c07064117942240d881540c0d4043c0366010300440055400075510b00850010290300850107504880c4036180503616105041009a8080e0400c00c0ca0f8420000705125600342c40b8810311905002e86200c1d100c606a030308000360700811840810034070f94109820071040c0071103e60005101210359400b240c40500e59a101440c0e002203688662204c50010700309030034003040701d80c502513460241c18180c81601d100d03030301d03012110b6858140c20001d4400520034111b49100c0c6204510110703156100510140c60b00c3d1168481500b95a000d40d60b11181100c08001001000100b80b02c1e0410f08090721a0304040d050000006400f0816005001e810504110318032a00c0e980b09200410190f4030052002c0b14a9889081c4082004050f82e81180a0000c1416012540c0f41000c80380340b045a444e81c070140340c0161a4000c4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 153406160 1250 153404910 153404941
    0x3052e050d03020c060304080d0b040905062a07060204050a080a0804060302070804050a03140d031b0e06120c0315010e0901030201030f06171b0409111e03160e06090609 74
    0x2e07030031406010225031065999100850149019144041d02c60024140e02d400b101e90185030130340315074500551840081d1022484030340c090103101d060025a05414411440014030b114880012400020710078204000c680c080c205549040e0b902d1307403040da29440613965078625104080c00c40c42080c40f041020900c079130000d00d00342d13104da14800c1c2001c5e80e450126104102c0c907002207450100c0352011200b082c00c01c00c40060a0990341c6014050050282c00c00090018030344590001c220001e0380d00e44041c0c88200440d00c1e075002c8901400c01c00d1600f5083c2c210950000e551a8008040a06044003d5817042403940903030b107802803080c0042d034a907600540c02080d50105002f4603546542002070f60710410450100450b030b0940203482c00c03004211800032000413440c2c415201b2890240c840000c1861021070301d49400040e208270082c204941581510390003900032081d803602c52401c0121100794414034a004654488001140030344860741085407907002242c4458100259000090000440d0f8034107 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 153407410 1250 153406160 153406163
    0x31203020d020f0a0e1e062b0b100309030e0603091504030e01030e07030b040605070507050703031701090b150d09080301140a0b12071d030d03052e050d 67
    0x40c9000008001c03542030780c110384107044005502040310b18a10707400c030024081050003121003a1401c0050000404104506103046002c0e4102240c503419941c15201040140700e00b44036040c00a44810f60180d01400c01900c0d035500404e240b031141300c42a030003400f51555003503158480c0700c0359103026402d006481c4c02c000c00041e481e1050b84461070603825400c510b640218060360714030b9580040301c4000b6040d00e074204000e50403680710000c2000070805840b65240c2055000c64041100d4607000c0040321240602c000c05051800b03803100000405420184c8903035800d050040d01c8400b6031383c408016003121f0090504a4000310450942140703ea0f20754010b0020300302c5444001052251515a0031468000340c0100c6e6132140d10042c0091189002a0048020610601c419140200c10440ba4240040285c03d000900c844000c1c00c901d124205690b807280134030041c0458800d500602c0300200a80000e44400c226285a402c0144031110420515511820b030b441401041501d81024000c9010040301d0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 153408660 1250 153407410 153407417
    0x302010c0807120f021207020312090a0305030301080705010e100804030c0303020f0a0e04060504020c0d0c0510020f09100305010605040e0a0f0c0903140601061b020103092307050315010312 83
    0xb441001440c88100590311070055034828204d513a0300c0c1c401a152111000d80106c02c40b4007806410010307038001031000c0d503000c1002d80341500e5260035808a091144c0c0c503007008005001c040004200741070b0000d000012984240d0741c04014110031410300030040c030f0f034440c040002074818000501090148080d0000d4030320030320700103262609034860a515604543c8c5550002214410480c2e140d142034012140600400c5070118541103149401c1c0d0f54a03e1180d0680081c06241300803103080c040c0c14049000b0443d15044255030740c0040800001c0a80d102210076881141f060140fa0409072003445507030f050360202c0e10791500c0d041c103200041d02002c2000304010b4065440d411110000141070041f00c400380020f440302d00b8003030704603d840500c44446260f483c0d82680003000400c242640440ad40a40306c0005228580310300c403c2c00120042e004120000d4802c458090110200500b05088180d104240c1c0007540c00c07450303c900c101034507100000000c416070400c100060002c00c80c0004e02542c804008e00707 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 153409910 1250 153408660 153408667
    0xc11041a030105150102070e01060e011b0c0b0306010305090a0209062b080702121605130b0a0605130603020301080c060c2514030a02130c031d0d090509040305040302010c08 76
    0xc0000782900c0c400c40c1e0002611051050f1024503580401001007d00302d00350f10440d0940c1004d100030050141c2101c514100301c040c400028030b062034088808201900007000c2881c291b1140003040312580182c4400c1c5c0041d20301320015101c02d41c0441e4488119034010030110080c0c54030340030040901c2e0182d02a05840c42e4011500c0000c14200d000b003061584aa10042d4588600740100521410400d0174450250806064145004650022181590300495209100010702c1045200510001d45020b8118102c040041000c0307410002400c21525440900400c02e92990380072003d0703000a11481c1c01507400030701107034124584540a0030301030070440100c80000c120154489071242d465507401e402c0080c149414803e20305100c110402c281c00540040040d1400c0e5808281c811914400702c0d0900eaa840348400c0109109800200780d075055070b0001c094040e403156007151074244400c10000410610000020182000c002a520442e05600c0705400c080c1b45070015180e102800d00110780717008040 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 153411160 1250 153409910 153409961
    0xf29031005181b040506090f060603070c05010c08180102040602030d1a10030203070206070306050d03030504080d0207032106030201050d050c07080a03051f12110402040b0403050604120c1104 84
    0x20451400010f001100082c0030503102c0c2c061208171040544014020300c0c00e2020051500166042c1c207422007016580c0c2680c075991100704403945450390900074000d50800699403212035100301b000340602d0340030080e031002c1c80c0d06900300c03400c03440f0b0752003040090b801c248081c1c480e411090340072400006000c02803a5420507140b00040030345405510074404030754007000f8420340d184c1c1040304a6010310035050410600e0305080000b032a031a40404004c040648a100140400c01d90780180c07040340e15240402e540383c003110703e400b4041451041c0d910341440b0011620605030b030828003d11b01120b4060711132610b40030700803c144000d070a0003006408451001c0000d5000642500010041040d10382c2d800106030800c2c4911040c0101030506003205078840150a00111080090309a0100c0d4822140d0f403030b503001e42010901034012603004034024a40841c000080c0302c1c011860300c0c0b14510840c1d8010101c0307140785044c3e030161000c07000605020fc1200c601c0680c2e0030182d114400600d0000f0a039003c85100 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 153412410 1250 153411160 153411163
    0x51902130b040e0a0b100e10020a1211060a061406130308030408042402030a051e04090c08070807051209030d0603081b2a010504090f2903100518 64
    0x1030391020a404600f04208118004184910101150202c84d100d00c0703000f2409000f000f020051039060700ca6191a0040f05d980303030081204840980d40300c10111051008210f024210210400d0034845a00944002400034000d82c85807109580c480c494841c901c07091003040c01101e40045042906240e0303040030100100d01a0005180b00d00d21424000d65510f04200740301d032001d089101440540e00041e15000c0c10b20b5008025a00700540b20316105446014901504c40500010b035090485240c0014010410b400d594100e24200840340e2110b0809440300d6004440b0080700315002c000140f03040c404040e070b218003080f2064001050340201c0307040c4000000c4402c200d60300f5a2048a14480c00101414800c40c0100041600c0c02c088014021441070b0103032440381f0030400460704041c690f0401181d110381c3c1c0202d040d40d01404c1c2817038040104d400c2d0720304840c006202c103d80c0e01200c101041540c203000410310304a002e4510300503000c2d20b48400c21861200c06400c01401c1b012102d0131250300b44008000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 153413660 1250 153412410 153412417
    0x50103020d241514040b03070501031e110a09122f030d0216064b0c02010318030f0305071b030509130608031603050714061801051902130b 61
    0x10039410341241c0c80c40c24110044c400d0700080c51a000e0740c00c1028862441c0d4020400c98221039081c2000b00b8800000030310309504120700a80300c80e4030781c500900005800b210710054080f481c00f0740c5800381410303241c8110382401d100d1903000a214140159200d0780c200e52a40480031007080810700307041601e001d000000e0401d0b1a400d040d80043c0d001c86441c0c4090368080c814800100062308002550345030407012072842a6949550388404c407000004c0742e401c2403e64180c85015181081072843c1c00c146d171a80109040c0964405900003400e009a88417a404007801e0400820340c1519041e07110142c03400164058a001044031701406007401d00d03010364080110007032a00d03512a60b00e43da80d82e10000200440901030000680c255403601900340118200081100c401a20401c4112102190340c41c048860340301d11100203181d10410824040c0e40c040000f80f2500a501d5541c8807068908480d08403403c0715401c50704200302c2d2030903000391000003041741d004001401c062901070207883d4881c21200c1e52980b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 153414910 1250 153413660 153413681
    0x20103020d0903230a0c021e101d030606090f060f06220801020408151f0e01140301110a0c0c051f09090207021f110703051f050103020d24 61
    0x8a01403080b44d0707803220802a8502841084c4002401e00e880b50f18003c08401c500d01c802401080221841c6240030103802c080c1d010031200901e40300460204480007081040303d50000050144c001d10200034030700e40491000d100b000e0103040d90100d6a1070300b0251210310005000ba5070000c1401c803280b80720791540002003500000c40c14044440f440440f9650b1480e100c240e100d444640d09c144014490380300003080640c0d610140c98040d20080d101e180f07080480881d8504685c8042e42c1500d070001d909181081c12604070b403039102c401c503103049414092500b40e890491400e05d04200400602c1c800c0c4c1c0c054000e00c0d4040d03008005050345140c4810200d2168100703444841c5018061400e4041c1300c581c484e0641d0302a0444030720a40c100525030f404070b004140004030401c0c04248448400e0b103128820746a40c1d40303804104003200c03c5d840e6242007443d116140302248809900c084220002c5a07012400f5540c102e0fa03014105c49841c058035210075441c000c040d4059400102038001100300010036015180c0801d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 153416160 1250 153414910 153414917
    0xc0729160b1f09050103080406050703050d050106021509011806050702071d0a050606070803010306020904090f1a011406040b030a020c0f0105010f15050a12060504020a05040f0f0302060a0c020103020d0903 90
    0x300c4400040d407261016030f0010301100e00703241c018030004100030255070072500e8074100305845202d2442c1c2076403103000f1074900799502840d0100014107160f000070458510aa081c094104540b0f402c60b8842c241c603c000803640c040b000d014400c0b000109a54009907206841d0320540c2c20f180d0301d030703a14901c0e0001c291040e0352012015100344043c01c06c81c0e2089541104044800515011007a61803c00901051001424056000c1900e04007501e858005044041e401031501c200d580b107a00d0001c4020075200000c1c4200d84804001056603c84850304801c41600180301e1800d061030003c080d21568030080000e00f50a07003e105c0c81d60309d00da04008082a10708154008146581800c0c500b40c0b0010302075000ea0200780800254000c01d80c1c1100885140003400c0c5011149241c0044552020300202d80c020f9800c1741c0300080c0244500d0f40032001c0d00a0310526900050302580e40c2c4041c0d000a8000d02010758410410040308102c0c03402240000c030414810305016003881400c6410000302c0c2e51014055011 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 153417266 1106 153416160 153416191
    0x1109131404260301080303090d050310090b0310020f040602011a0d020108090a0503180103180201270b071101170f07110102120c0c0729160b 62
    0x8034003a0901e02c95a075655003640c0345da05c1c3c0c0200c13140080d9001d011001005a8400c1045900500100c00c40d218200e051510980080181c464515070500c152142002e01c1036550002e01030340719450a01c01e0b02d40d49042c60180c00d480d00d01000e41d61010014044003006e584145204000e1034081c60f00d540f603a03590068940c9045400703240904244008158084e01031108a1000501c800aa034141b14600e00071782004007040c0744180c0280031032440c038101016406542081500076403000a803004856440320310303107e594800c450503a11029800702c45490395070001040e140003040c3e40075580312803408843c0c0c0290780d90042c0460042044004862b1205282501514440f605540020f038503400c2032054522264403001803140d0741e000791807000070048240210920354003d40700000703030078035541035040140b5400a01c1150711010760003170078000f1401d800e012a02c0303050920122081f = true := by decide +kernel

theorem cover : BRFrame.Cov 153237410 153417266 := by
  have h0 := BRFrame.cov_init 153237410
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153237410 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 153237410 ≤ n) (h2 : n < 153417266) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
