-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3599
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:07:34.925979+00:00
-- url     : https://prove2.me/submissions/93a25567-2597-411d-ac10-5fa8c73b2cbd

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 647122302 ≤ n < 647302158 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 647123552 1250 647122302 647122309
    0xf240f0c02120d0f1407051c0b0904021c0b07050301050a060819020f0715050f0a182409051b091302270a050402031b0604090f1512020f010e 62
    0x850560310012008507164459803c4d11004c0c014018005801c46003c50501c444182c011003d401081c14940c400c0d20940c50071000312090703170901c1c4080c0303802041c508040303405402d041d0a041b444014986084540312042c4d6901020b00b1130440702c001c006a004001405549052504840207121501c1c06580300d041505025030780c1030310b5041d80305095500003002458805204150780000350010249024000401c289501a000c1102d11100c1c0051000004035150490301c940c1a5900103034007120a0640955141e0041075401c01541e00500b185000201c8031150b00e00412540c24400d070050b0020340c07040c62041ca80f040b2500c075280d120b001840104608818203514547c003071034045a040400000000c2c0103c0000440152149500f031610300308500c0d80c403140c1195004601c01d4045036040c60401821080040d0303070039615a40314504007c10048170b0f469802c0b00d0140c6004000004560003105004a0340265580c41103040c00f1040540c0829482d240903c1c02d024207003820001c22151030140007 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 647124802 1250 647123552 647123557
    0x207090e0c0d0611070602031b03130b0705130f08011a01021002160602070602070c0902090f2107120b01050109060c082d041a0c07030f240f0c0212 65
    0x400c1c0600005042c0100b0300c6650381102c0c02c1c3c1610348075000d43d5071a00313041c81800703544111403042e603400c5003090940308841d840e0700312032080000010411241c1541e0303880c0e00d1022800f41909040100600003035030b800b80010b42003c003c0c954400c82420a0b841d2842142c2540c404212002c0c0030759090002d201166000b01e10846600441c2c80d0060b07a59010041203003030490090300c007500325840807400300e0030041d490303006050381401410a03090207540c42c2000400d9208691009070042080c260101d5141082c02c1c050030601c02d200e401c40c0042d000c00303141c03030314148440d03100e00040b1004080610502603d8180c0c140985800e01e09144010705094010703220b44c40e002001407000c0000141080300b201020410130040600000001c0d11621042c1c0094640c0c010740a0940c1d00c0081c0800070209820f80c204490300300500c0e40190a0281c515201d045a104201d407060722007103404103c9840604200700142c060141e141c60004804540807421003c0741c00c4151500d00f903600208041114102980a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 647126052 1250 647124802 647124823
    0x7080c1905190f1203020c03070803090103150b03090a03090e01060207030807050f06070207141e040b0105190315060e090a0e160315050601080112080304080c0a0609030207090e 78
    0x12204510141ea420980c0d40040303c3c0e1151400620302c20012619100114200708102d01030790885201560305420552101050f102d6045241e0081240180c1d40d4000d8101c425020540202641010781e16118244142e1086850605640102d1141c400705074100c034004c405000500c00e54000c0c4c4d810280088d40e03035a1640400f40450901040600400a040124003a4144020152341c03c80c108440003a581c1e00e10790140796802a414a008501802c1c9100309041d95903100340c24148501c022000d0200509400130701d1410010208800d0700215043c00034001486226540000c10180c00070b00c0950303040d80d903084441000280c00800758161390700c000303440d0401a400c0317001440c8291910410300d8002c2c06900f0789824040c00d4000410f12504c0c607010100510541c0003448145d46000044441c007109000b001c00e45084809802c020419440c081c0d54881c2c4210502468030040020161400415081c12140b054440300e0110406605201000041032031030001d0040303912045d00c0135169030101c407 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 647127302 1250 647126052 647126059
    0x1d0405070902280c0b1b03060f0a0305071215050108060f0a180f0507060c050d0804020604050402030c0c070602060606071b0b120702120901050306090a1103070207080c1905 76
    0x2003407007101941d60a01c3d400c201d010900407040940c800e4019200040e129819034000c0d4015002807111280c102844030304499208000b85140c0e58282085a4440c940215036080f654900011000680400108018011150000b046102103140030b1708102c1915002500781d604100040051160010714030343c00c1181109072088030f9841c00c0601000f000d00c0200d00c0c2c100b1201e000ea50050100910031215240c0c0a0020790700400c0c1c441c502564a140703415001072065200140c0c20b0840c1c1d120740600c5803ca48010001c900d003039610320000d402d81c0c0003515000034482c000200310800d91020080c6400405450010b8030040c40d0181c00507080703000f102c102401d940d0845c00905803191124043c81302070041110a5031f11a1030303683e124070014008940400252103014030896207284903405841c22100c7c16521180b640d5a19000d001c0750307a00c003030000700082c3d4690704000030b00824400958072802c82a03000301641e902c0c1c10a000e2602d21410782c198007450403806009411103414414074140d40054 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 647128552 1250 647127302 647127307
    0x130b07080f28020d05180f10110f0c01050a08070207051e01030b032e0b10050a08011d16180b090a1a09040b150a0c02010801150801060f050909101d0405070902 70
    0x41002c00d49141ca087c0b807180d1f100c14003821511600d9004015004c02140f0081224501c0e01c00d0144240c1e41c200c0790b4541c6003c40c4084c080a02054807a40d00c0a6026000b40305507600319a650300402c074241c0c0701602d50040715a4811008202d541c1c584948014000d00310b0050400c2191020b03946141022081c00706545042200c40c49001005c1d40c10404501c00040c082096080761900010b268ac0c001050000010310414000102c000241800f07243c201511807031400c0c3e03501c80c02c00058a030440744c06020b09200a01d01071b07030583c4030b5030702000005001e04058140d913003010700104071203e0b003160003103c0c11103030803080d81100080c00300544148040c10350b000904110080001005046110b201c89012030000403000c4030280e01c4850062410710030f881740200340c1d803259070ba5080b44030100a0b0340d00150604c0c004010b51841500e0946055500b410450314010040303000c503039030542c01c41d000540395004203010494544100c0101d001d2000b102c0071242c03141070564906850b00c050b0311070300580301c0d000b = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 647129802 1250 647128552 647128597
    0x18080a29011503060b12060f09070f08130b070c03080a020406020a080705010b06180f04020702030c0d02060f04171902011d1804060e0c06130b07080f28020d05 70
    0x240e00100140c640b803401c1c41e4641541070400342901d1007c1b10054001c541d2540004002d0034802d05040c0140002c0c0c94a03500d5001190f411521043d0040c4403001d2807140441c4080031030340f5030000030300950300c03541c804034a0300d0682801390090391301802080f1118410001080015804100b000910390b000c60fa16a0700c8041e410902c2c0500000c44049030700c800d0002d03c0080140c1803525949440505039280c640d0705001c601004101c1c0607400f006500340c2c010401c03000303803807402c1015606210310081c1031604200f01e100c0804c00c240c0241d0054200700a82c2c0d01d00129241042110b185403000d02640040b0071106a80020000d080c2030801f001c84456043c0301c1c860b203a548503010041c075080b00e0780044c0549000d050201c0a0007071420820040d00a0801e0a2140c0c10100708a811100030051054a842c0c03401c3e1300101c0f10351240d40c0c140d54209c0240684100600100700821110308407100f18080780c0070b0807002d0540544401c452400b95401034402c02d1030180c1200a0381c40c82005588040c503034440 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 647131052 1250 647129802 647129807
    0x10209030f061302091005210d080c25080309030a0905060412030f051e03010e060109030c05130209030307050a05120408060106030506030102070507080d1103040e010e0718080a290115 81
    0x2c64012541c020340e8044602100b828811b030040c1c40084403009c0318191410400155000c41058400702004c0d6020003c400003e9051140484491408002d0482c10511610307000c0380c070741040c0c905100d0b0f03400c00165410020350080403540600012102d1a01d413034508115000135040b035410080902c03280500c1c00080c503004405075610020203282c00d080c08904499200e048da030007401411415507680f00840d40552041242c00c003644d034800804402681060200941c6524030205101255020010b0400300d49050000e82583e0384510002c0031041c105103003560500e01c10400e01c2410000c01d010411440000061a5044500508001404c0d80710329011030702911030560042d2543c441d5007000100303100002251a042070065030f80c2001c20382c190644c00d899108600c51b402014151a00502414452030811a0452114180038045281c1099103c008140310b911201303141e00f000c10342c20280099428400c0704000311415606020b15200c014862129042c0a0911001051701104c14801e0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 647132302 1250 647131052 647131081
    0xb0603011a10181e0f0b1e0f09120d02010c0c0c050906010e0301090c0501110309030a02040b040b030f010609110a360f0f0803030403080403030e0a0c08010209030f06130209 76
    0x4c014162640412920920f940340a4643d201d482c00420f164040000c801c101e03402514450100070480411940040e60b030001160000c407803042c0760a104001111240d070f544072034000c14007940b1025201029200c6d4020f800c440c41021004240202d52001c0e80014030282038010944500b15503c038420303100c500040300d5003803500520750f405602e8482098240041300c4c2c0c417001126401d036111907148201000a9440e03002d400c004c1500743d400320801000626068010340100b07000504005071100c1888002031034100b0031a601009659070303000078020180e03d802801c07003003640c4400c0e803071a25100e590018000344c92020361901160741249201c042001804050346030b000b020364902d540390b0311072009081c08000b51058140b008103a03400060740e194080103981c401c1d038040d101c204003591075841c01d9004c2d03c0510040c900700d002d52404040004e444001400140c1170182c001600d0b460100141031420800e103140c00d246078042000c00c00c80c000b1988a0214a40d81504c440480d40c454174138214420 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 647133552 1250 647132302 647132309
    0xf0c05041a031e09060a0c05040f0e060d0501110a1d0901060f110d0908060112030813050a0b0103080403020415140f0109092d050c04030f02060706090b0603011a1018 73
    0xe0f10018060000d40c00107403c0d005000e400340811040d00385840035251403140d449440b0184020000412035040309200e065400322014101d8107402071680d851908490031428000b070341c0c40006c16423018581d40603203a018811080c0000004407941200050310341c803014490b0300108060a80604e009a21070841405540e02e201e048444130b00501f0b00103004003025003e880c1c503d00c41c4c080005130821104200f08000c83e013684aa43c01d682340c4400d6503061510841c030644480c881e10040314002101c4070400d5000351b0150792140d4031142544100700c203070390008205014040c846003040c0005c078440c041c00e1150390b80881c2c03040f00881410340142e41040720355101548851510600c4407106841c43c541c1c3c14401e520103900140c00d0300f214000301c22140d080c1c0b15401d255206210900000d68944d6803c41a0785c00140901c0c1000d21a65841058031014a0201c1e070f8018940c0c01d0110a00b02401052084820504c00c103019110000c0802c040d5009807184104008480300313400004440f103408603025 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 647134802 1250 647133552 647133601
    0xf18050c090d050606040c080c120603160603021215010f03150b040807050906030d0c0201050313140706110c010203030c0f040302120105060307091a0118090e010f0c05041a03 77
    0x2e1074a6410003030313110581110f141d800303607080c5280c2401c0d85d0f01c00c42c1c17080d203e0782c9001002030034110480710000d1050001031103142c1510400046c0700f0645111400f00000b040e26540250380c60000601190035000e000d4401c0c000d07100c500001001503038022401d21640d51507460006100c3c1c5e5006000d52031034400364009460880001404125000041031340d80c2624000e850300480f87c0c8500b07080c150b4a8004148400c0002d03203102c00e14006611950045410032018022000034443c07540b162400201c100340703002c038607600802e410810540c01c840c2c4100c1141c0200c0141104400c2c0b030300040e4691100034405000c00700d001030b03032220007590003040d50055500a010940b81c1e086500c00e650003802d05540c024401e2043c01c4001481e03002a008048851300001408400300c00f042c2d0064500d440d094403803c00000001102241d402000d1045a851807404400840d01c41104181c0e24201e40d400b844a00800c14100402c0c01415000c8654070340340f207104101140d4a5462540c280d0885100240d0b0014 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 647136052 1250 647134802 647134819
    0x209040903020102121b0307030f111911010c120203090f0f160909031209050a02100905130c09061d030a03030e011811040b03010912180f18050c09 65
    0x74168158060007854440d80e44039141c648821030701450752601d408014a00d00e0301000011501446a0082500f00d03e103103002265400001a0100701d54100c0c48002c9420f0720004e07510484a5407104209041c21080002008080f039000f1004001d16660a4116892600000400c400e10300400c0208034054541050b2001c0150786120700381c50701650701e610b5440c94000307500070072000701d6031007200180d5078507480d10029482000c2600e405818182001c4c1c1d9280141410f2001580b25440d20000c03ea500d60380300e40c05117081004010b546610310341e0b0360400600d02100800b030303250440400d200b0f039161418003203440c24007840c0c458620092140c0440d01401840301e107130704254041e00176000313260703211000b032164640f24100c1195402c3e03072401c0034280035000062135509092a074081001a50060004540d0901d240c84114000d03411191450001d0420b0480a15144030300038440301500814100001c0c1d5403504501507141140d00301f19000050795070010481072090b41c01101c0700c44802600310711 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 647137302 1250 647136052 647136071
    0xc0c090c0313141c11032104020d020a09050603010c050c06280e030304060e0307050706050f090a0305030a0207080f0c01120609090606030311031c0b04060506031609050607081804020904 82
    0x40341d100f41c00061078003254104845d20006007000c0107a41c00798482d410f5101c0002621142078040d108040e2042e44c0088101c0d40142c0542c840c426040090200ca107000308031403d000c014542152080c095040800c101802004041c80d400314070150071200394180c03030815104444513104810b0a403a00c2d03c03070b01450861414101280840a1031156000b248200120004420115101e02c04c032807000b0101d400031803041c48214082c801510920b9202d11016052110348000329040c0285504159032640c0081803510602d0b0741006400301410854001e80000c6e42d992001c140c0d5010715442d190b0500c02071681c10001b03282294000310003062441014000002141401002086103002c00c4c0c0014855848030100c0034000400c407006000e40710005411020030400d0f09005290642a0f0369100742c4426001649940d1000654024840c05c48105202103213840007a01c0100e25034030090040301d040c00351a01103484201a680010b01525080304103800050008000384107902032964407502c4c00e10540d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 647138552 1250 647137302 647137333
    0x723030f03040507051507111002031c06051c0503070b0408210a0c020d050a0302300907050f010f0813050f03040305190c0501050703091a0c0c090c031314 68
    0x450032260309071911b8060342c00c030403901030b810b200310a80a042c5115100500d44a4100704103040c2c0302c20410f20659060070700d021306990b001c0c591001c0a9003126100c8909008a25180d950001940b54035181c4140c90b16040e0f440c103860780100d42e005042c00107c40700041c03c0c400a070040301c00358680341ca00b09103002100200c41c60181c03015100d0744481481c050134807050a00000310502250600d490303450030942611403c801070b600c004440a404200804520f103521001c01c24038003044100c5843c4042e13441c080311980e02e40b80d0719510a92081d0790f214001c4030243d0300040d04a12817100391a05040c655590720481c144000c0c40480240688507520800a4003003010016100380da21800c1a00e509052100c90080c10700703982c1e00040c00d201b00041c2c04200f00e6000350000c0401c01c0c440c0c1083c421181d65086c0882e680c2c00c07800720000346018002402e8403000c5d010702400e450b800b011500115a030804441c0307a5000d000062929020300b0311040e1440c20b01c80c5400c02c0184510406084494034202d0b40c120 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 647139802 1250 647138552 647138563
    0x311070914060301060807050d02032a1005190e0f0a06030c0e0a080304090c02070b0d0f05010605071703151509040b01020a030c030e010e06131401050723030f030405 73
    0x120344a00c200708011034554981030213461308840004000b40107076400c2508004810403283d0089925108910302e04850104040d159815455041d401c400803511031401d01407200450f5500354200201089035030b4401041c84581001071102d403a1045102c2c00304004529004d50300300074194048a0103800141c0300340d258000d002d50a06650781c0446004101d02030050380d81c158000c1c0804e0350400e100a0008856561210900c2040c0744100c60b0000d81d14188980e003580080c01c111045620390440440c8201c090080c3c0740144864030b0681d181140c0c5413600080c41d064003654140449001000c2040c060328110700103c800d100500722000303070f1000b103201c40c0280c0c001d404040c0550308108040c03c1702e43c0042005040759405441d00b0301000d4aa5901300c8054080860720382c144a9007900c40d0503d515004080c2c00c502d43e80030941c074095402c007060360b459428a50700342410058104901000122261880038013800c180110003550a240928541103010303111442c140c2c0d69002c1304000900c01c00094 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 647141052 1250 647139802 647139821
    0xa0914060a090e1c02070f0f240f0e0406050402210601140d09061b120f0c05090607080f0c030a09091109210714010801090c080402010c03110709 64
    0x7800d00001c0e940303201c0ea4003034854070104501d15400280c3e00481c0401c0202e181480042288199804107403a820003090181e4960858481d4005000c070078441c0782139401d06041c004854503001c03c0744400240d00109003016148074001049a055030011480e03e031504400082c01e401003095486030040d46440c03c000001c04a05240b003090312000c104c041d4050760001d502814160026850203005000003c00751040420468045a03540ca060444201c4e03280c01406501180c1d5403840c115030340b01c500ba816110300c600b00380101c03403030b051a0b811040e030400704855a51b0340c20307100c40307464403007501304546a8066526540c102240000e0300868010010000741000641340c0c4034044029150041e080c204c071003441819510300f0303040011030828a080107051a05014008203e9803e0807142c0760241880e0050388603000116003030342d07004400c0d84c0000c203007800b50894600403c4004200780000f01440700160000e81408482c0741700c0c0c1c05051092515801c1c4003104001c640040780e40b031207004010010f500 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 647142302 1250 647141052 647141059
    0xf03080912012f0a091a1e0720060a03090503040b0f0901090b04060c02040203090c13020c0c0f06040306021c06030b0105042306040e0a0c03060509070602060f150a091406 75
    0x10040c3d007484240b4403c0d0f4506004903501e00300040d00307018000f151603119981c0025080024012052900c04075100f05d4105405140100d407203401900d000d400d1a4004405200034884610f800420754403140144d4016990524000c1030104003428098150b100d02d4000082842001505a09414220006111115003a03880c1c40e90242e844c1008002c4d030086001d9007000901010480c40945800e40140da0031014113010b9500d141c2260700000d4107035010100d03480c0e10a8011515078400102484000e9100e101030b2407500103014002c0c00030301c41e40300303500001744115804a0900302c01c03020b60b07001000c118040c01040011603168144441114024071800348202d0810605d080d41600c006200d52024110815124060310746c002084080c12006000d0b0100d1f10031403800001051180403404000e5001e003000141c0c50071b2020807141070401c69000b280941d400f8005000e454407400a58682c0101d8003400c41c00c0c100750400000d03590301d007950f0003900d545040071541ca401d5103c400455001d06002c5 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 647143552 1250 647142302 647142371
    0xf0a0309080601080606131407030603060e0706080613091211120708090904080d02040b0408060a050c070b060102070312031a1e0d080702030a03111002040f0308091201 74
    0x100e5041c1daa40c9001d020b0701c1d0340b81c1c0003000844c4042c1001042d01161104010000c2100300105201c829000411500e00000949a00c000c00c1480b80a1081c660004011805403d0440c1070480150240c6000f40211303014000c00c3e108080e00c22055401040b4031603100301c84070300e0400c054070b00070150300301c0d0302d03111050303005400242d0022060101100d60003540100042d007410380050401c203501800410540d9511740800900c040c4000c24401000600024020103071035905046890b0300d840002411260310f81d00d00760510003411101001e41c1c103010b5000d0024206555880c004138104555540014843e10400709845240d41c0c0540005031580c03442211035031070050281c10820300d1485841350600c111411401140c040c00c02411800c102d5000700046d91a103001c9a0110f854080705d18400d070000f60700549801d0300188203016441e0320303d114100c103508113401c10302082034180f5a407100405030103001821502035200d2003800102c8180f05c2c0001c20900711807144c100c010905110740210040802c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 647144802 1250 647143552 647143559
    0x21160b070b0a2724061a030402010516060b03060a05010602060f0c030c090307081e060c0f041203110a060c0905090f061c06090807020a170607080a020405030f0a0309 73
    0x6881000040240030091249070764030980000ea00100c4000280e40107261041013102c1c101c00b00701c00e0011120710440c00504503240401800501040010094580380d0030070034840586e91043c03c2d6420005422003141c502c8a0b20716000b0001c1c140c02e8007198042c080c0310100003e904c0b2700c0d405141201c480e5000e0300c009545010580102c40c1084503402c024840503c00314400720f4494000d40b00240d00503040711141a00c483c80702c2d00d001c81c00c4200e14240c0c0c60203c655000302d04240660f039001403c40c21198100b00180400000502650243c01a1072140590740c070181407040f03403590542442402a0b1303107141c05508040d0040d0901c0d02076000864002040000c0904005a0b41e5100c5c900c29160750101c2d856000401c03650350110846000b01800c0c00d03001d40d021405620400401901c200c0c005662a081c501c140a80e405c1103a00009445620f229181030b075890200c0c4866100d50989800041755039020701450083c0100c2c0c0200c1d8051240c200d8807640c000c40010b54000d501d001e42c4441134035596 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 647146052 1250 647144802 647144821
    0x160f0e0c0a020d26010312020d0906091413020c060a050105060f09040b0105040f1d0a18020f01180b040504050a091e0609080313170921160b070b 64
    0x1c0e00001c0c00050340300f01d03162846103100702e01109010f041c035804814041015008242000b400fa00251803850603050350f140070741e030104840a40420706041034250030303280c60006000603201f44034074103a0006ca203600800c0c0d96529030396440e54500e491000c54480c0c0c04102c0da00d50741c1d01c040343c0c2490362514140c00810680b8004e802d0307960010701c60801e5440c0c840d40c641400040c1440d000c1041c18000305200104000200080d81d03005000b5104c20500026025a0000071842c0b01506034072000f40362545102c0045600e400800030f107a0181c1d60590640038840040740d2604118455455041030580d001c02c44045d0900244101c503011182409103845411f841c80c100e9041e404001d041100c0a0000840050706031102554140601000074902c0f079640c8401c80650710880e403c00030304104146200070400c0060f2040c0c0e00d00c8440c88014104202180840c05a20308503085a00d02d5407507241070049030004001001c0403800100140124559458101945400500341104c0d940081400640d0000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 647147302 1250 647146052 647146057
    0x603030c031416020402071703090d170f0103060c020705040e25050616050c06030f04030807030e03040b1b0703030905150903070e06030c0904050c040c081009020c160f0e0c 76
    0x5001c0c110503183d07030440d400c01000398098903040f1040c00b81b00c1440e1181031500c0e806584996090750203030034907440300070700244200c01a0402400509204040c412880102003030b403030542e41d000c1b50011322805200c20591500b8021b6200d079920a042044007000f0301d6010031604080d102d0011031028030f103080316102c4c00380b035810b005440d0000070a0001102c030400c841a110300980c02103080d10f6000d4240ea0101d503c40e401110035803030040e124002d210400d40e0100c04643e00c00d4032803404000745603814044075202c0c8a0f40c86213030106c10010425000352400c000181c104807019404981041d0390700d01c1c0c00f44c440c00062045500c07814410f01d80071000080003048400c2140e00401410055041c00040d4444043c0646160b4161084103509001c0b03480b80c00c0007601540c001c4008207802000202048151075404c08548100000c1e00c041c408505800d402c00e0061310201d00000d40c070f0380c500d4590140f50030703041021052603502050001440494400c0b501061b44c00c2580000603640d590141c810051 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 647148552 1250 647147302 647147317
    0x191e06061b050a08250b1801090b06100216030b0f060d0b0c07030507050a0605090d02150c030402030a050303241c020f06040503030c011d0c0901060807120603030c0314 74
    0x58120703418980000324014010312161a40705c094050b401c0311041c40035000a010b00003141c1030a05c881c144051002c0c01030b40c0142a0b01100000d100b0500b5560300c0c40401400980900d004d030b4440c4100418103802402041c01040b91824140707c00c41ea03034104203607180d03010b80d01102007458a0011a50360b041035800340c600303e07400014100b11603c403405040740903801464103408200c0103202500024100740125011580201c00202d02800d144c0180d50030b142c0d501d90101e0640d07001c030681d1800710f00c0c13520419501260103103503503482e41c1e07403400881d0810070348000040c0f45000020810003884400611000b01d0490340a60302c101e0244d100500c044c4583c003071081000d80015007e04401842c0030740504800701c90244c00c06042507515008680380d500103400301141651140041c07040c4400c41100681c4030442403005102031241d94001c2010040107000d0801049400ca00282280303004245043c0f4100210904021482c3c0d2814000d003178880503081100001c4030300b00580589812400cc1d070b10f54 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 647149802 1250 647148552 647148563
    0x61c09020f030a03021e0f1510030210080402040b040e101d030703091e0e06040902010320090f0307050d0b07110d08070305090106060207090209010c0209040809030609010e06191e06061b 82
    0x111a80340d8143c50643c00400d4440c10204488000c001600c2d0011030702000141516903375524180ba1041200f13a03407564440c5801185048520403062200042231400030781800c41c00036171002007400d084414140f0080d241141e03c4002503c0c41050390002074102180d03010744003208034012801504800d0081c52240032040354240d00454064a01a030101080510505001444410b02c010740c00b00c0b15001c0180700c80c0c1c080d0118036036103582001903240300c0b40601180509145400d0000084c0c0d817418915014050000680016840034014020b85070845603c0f001c941e540e1100810007459460201d031401d00003401d04003c109203070380c1402141309840c09500604403d909160024001f0340069014074100520120510007507101c840300385010f20700690000395103602c4602414640344029000d008540e14120101c0602803001c5409900403048000d00c2441020018011000d00500c0c54101c03801c038245c4403600107a0301d895126004458440d21040f0391814400260700c0b5040c44140003a05 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 647151052 1250 647149802 647149813
    0x70212010e0303270f0610050a05100503040305070c1401120203090d1206260c0d15110403150c0f090803030109020a030e1f0b061c09020f030a03021e0f 67
    0x390050071030898108a01300000641d400109401e140e03c0c1c00f00401d00342440d0382200041c01060200c44190002402d0265900c183c0c0703038a02808150514003140c8502c0801401001240404d80f05000301e1f40f9082e080410312000c06c2d1507190802d5a403200d008998046041c8421020301a0068000c1d27070311400c0a03001070090303d02103680c103407960b0403501c000740711140d034907040400c1f800c4110f156428040f00030084400c01c029082071991420b030300d20f070b03007248100d51000c55400003820020703414400b88040a4042101c45241601c450796001e0b07908000c10380320300c40c0307591404801540e00840c180403050f510002c58803800d01c0252241d449a0052004a13001000103201c25401a0000c051012292800003140728800b40d4503410080b103070289003407103980004a284138680c240100002c0107011221035140400f5095400d030319544411050203840d0b25030b00c0d00300035544c84d0100d20040000c06410b03503298080d2403070002c1d2283c41d80020142072640712070104006820014690124125410003801c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 647152302 1250 647151052 647151061
    0x50f06010309081303050105060909011506030c05040911071b050a090b030a020301060605040e0f13111302040605130905090c0909010e0d0503070f020c060924040b070212010e0303 79
    0x401414403070030183d40c004070811004440802241c021801540502d00009103418a0700400030540302c00f40181e40c6580c1807944440b480726035400c0c0c0354101c80b068140020001110394041e14140100c0c0e04c00388426241010b50078480e40780d4001454030920030111004a583c4903130884e00002140d0050a8002c01039460510040c81785038404124003a004040b41d100c0300007a400a803d440603a00650001000030900708801c040799111207070081152902c40c02186401550f8289a00c4522400303812a40e0510f0008805c0d21368001c065040c00e0041025540d4903145d0101400740e078806074007680500d40e201030004120540c0e1103245d000c0c48400c0c0c0a000e003104810204600c1400182c6070400e195614107403032070041403c10482c005a64207850b040d840385442c2d0405491002c207820380b0001e64111000003220341d540e440440d5040348040301c074216036201100000c0603c80c44003c5846102d17400080c04100415400c01130502c031442102c01c07149282d0403843c40c9080e80c03400c0201060541c014408903 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 647153552 1250 647152302 647152307
    0x601090807061b0503130e0901141504151e06050c100506060408061302040b010c170a12021b0606030a0b150114071a010819080313051e0d03050f0601 66
    0x6681003c4041c60103c0c1c1600c1c0c0d07190340e811548441a031041e0411049020041c1142c002d03261540807114500820000540d030440301e00c00600141200c488240c0500f01c65015920755000d250301d1002504100d000c262a001d0b80c14002c2070812102c01030707c06101c800102c0d5440341c8229484246600c01800c0f441c050b49600da00500350245c0005c0d4400d07014840840c080408206551103170480462901c908119801800221000354007030b1030410807492181000300319515007220ba11400d66500d02d903150b50b0315504943c810300402c8400e01c840d0000a116a04d86104c801039510303030003004291112921188209544d980f1075180040050307000034002031141a0003021741c0186441810006450040030121101a80c40007a0441e4440d541c00441255036030880042405000740704028030150548281014040d031001d54001c0c11081c0010021382e8a0300424507629415a02074121941030b076284003503181800c01013409903c1c6106100701d00c00c0e010310a004150082400c00c00d61f80c1f06407280c8004 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 647154802 1250 647153552 647153567
    0xa08012003101508010303170106020316030219051e0105011a09060403060203040609170c0c04020c071509060e15090103050702280309140307050108040f0215090405060109080706 79
    0x9107005003802c0c0e50001400480240c401c0e01c22801952150055030452601501400d88021503060003488900140541600002142c58482c43d01c09a00010203c6140032840c0200d181e490b00700c2e5142c500c6012081023000244242c100030001e481145521080807410b080300d000b44121401005042445041003442e00010101500040c00c09807030651241c80f035070140c0e030054408031a0395560b010814240300c54034a0540610b120350b514685001810700302d0075550907141070194400da1b0300051680050780304000d18030080c400554030b80192840d024000c6e08040c42071003460003155034410f12580c00d160560804012039401c4800a0805c12450011401031000a1800c415442881c0c80c0c0b840d0200300d680d92980c41c2c00c0880d01405101d4542c03030300030200d29050f032041203000c0041c141b440050342c010421001780c0c0d01c01c1c40d1401e001c1d6614205046941c8486a01a400c40741b00b42443c5000551040141347c100c005071820300c0309490304001120190b209200d007003a00d4100300070a0003a2403280c4003 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 647156052 1250 647154802 647154811
    0xa030806060c2409151b13050a0605070521030103030302030a18051b03011e0b18130605010510090911090a1814090d0818100b0a08012003 61
    0x843d802c2021143c101c018080e4543c42c1c1c503214412500401c0500300041003400000c2d9800d80402015060072055940e50403100d050140d9034080110fa0020303c2c1d01c401c50f80b00002c090081c13011700b40607607420000e01154420b50301981c0328001d180c00080480c039140d10f0540d02420094000385945e10790b0310100c000f900040c0800000507141d004110190051504c1c51440500490203000b087c0d0340c1810101d8821043c030107032802641001d940703c00e036280080d0003188103050b030080482c3c805001c0000905180c0001300b1442c00c0c24284061108001c2c540b81c07000c441c50f01c1044204856600c8400300407410303824501d1880010030811040c4000d18094010041141a9140c10350411001c03200040751f98031240c10024008550440c0600880744500441e590170003404ca400c0700300c0c20300d540b070b07a40c0f213071140d400c180107100c800c80200c2c0e2880d0102035814603241442e010f642141400481142c0074001c2210f8280c0f10310003051000c50032000610901410090103040445030203c04207018041d87c20040 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 647157302 1250 647156052 647156077
    0x6180d0201110a0c05010206100e04140f10050f070305040b27251406040306020a170a0507391401060f0819030509011d040608030702030f0a03080606 66
    0x94180d0070000301040007100c0f403407040141e03000650504000900d8480018071050f032040030f50f0b030200052010a400c1a8016030000d441d24510580c001c6101d1a01099040e07100d45803282ca071701040303103071769a40c4203502416181c0c0c1110100d8a503010120f007992810395015020a4083d00807840d14402015400300444020f900045009082808107050540d03e070f2840742905c03801d241c66075080c0381d0140d030360b00a01058810701c04103401c800d0204a4901039400010002c0d40e0002e100b81646014191b610b503440030b45c001c40801c5203001508440030700f04c141c400e1404224886502060b40822401c0e0b144041350411185c0ca0b911101c0050785d03004043c921080d6610b02500034001c507110028000d00d0007401660b052a04020310b005d40701807802002c10140d62022110303071219030010ba441412942c50391170910380030654070805480701c2d81315486000000e610514186000411b040044094400e85d4000ca0070749400303203050f110395a20303511440c10003000203248000041c0345261480182c49810100d0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 647158552 1250 647157302 647157317
    0x50603040c09020f07060f0614130b0409030f020d1d0d06090204050f1819030e04020d140709060e0d0210120c0206331005121603050606180d0201 64
    0x4414190480e130111900c900584000160340c0103200701c6c0d000d5410030440c034120800ca0f491401c810100402e000045082c418058441ba00f40034488a4100701040e54001300f0401c4191b0103881c024000c0c4c551502101c0140c0600104605e465004d03050100c441c05241410081045c640000c01050000501c0125a030558441564001d40c96510400d40b154204c403103503400506051102500410680401207110344c42030070080c00d09140307007040381507042d4182000944c03040880c0005019000c0c00403861003140c90a01d20840403803807403103070900034603581c0c5400700040c0d04c1c1d2904844c0780c1082d02d02203400020302e01141c001401c2c420707001d080039400791412280004656403840196004601c48100681c88502804800d0000080c107100e541441401c0340701d00d544803c0c540c51829124140244219401c10981e501680500d045908020154ac00c20955140000082c1c00c0c00c0012001e800010346003000107446810500f08884000001c42c08860305403a4850410180c0300c0e02c0d1a08a0402c0140b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 647159802 1250 647158552 647158559
    0x1e0201020c16050a05030703050a200d120f0e0d020d0501140405010603021302181908030c1c02011e090c0b0307030e060f01061d0411040b04090c02010213050603040c 73
    0x240300258030240200c005081403883d21041203c1e80e00c0b2070304410320940040fa000c10009400244211225a000b41d5484500101200400d40d40400003011038204042284030420400703032002c01e14540802e82c555240c440e901241c02c661000c403664a0a8000400040403c0585407074091840380c10322550010411440201804c01104015141250f585c1c0d10f4480600c214904400c4108007820038100031420082c03642d944040c00703c0c10740311480c001c00340341d0641141004005086c0d0050104c000031079541c2c128014019585e1180c1c06004400204d204081c030001501c180243c1c011504205c1102c40c403131844004084c02827030001c500301c0c0c64041441000801706107a2001d948035184036240040c0e44503e400c1403505148004210f8a0421000001805034540004280036400814000c81c04800100d60105004120146003082c0c01e0300302003800203401d28200b0080c000e840700c04005000c5600c1e100020380c240e00070009070303000d84000e5031b409200303a041c0440039542c480e00640c5280c0c0c10554 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 647161052 1250 647159802 647159827
    0x150108070501122f13140d0f0f0219030201140405030307080a090f0603090203190b070507030302071a01080d030603080a030509161811040810020f07140303190b011e020102 76
    0x1100c01804c500c0c000840c2d268151000e804800c001040e030640d900f58082d2a6000050300842c05030001042080e00580e850248081181c032a10310541c0685030780440800c0341d1500c1120354851208900081e040f030029118416040140c50840700060002c0d030030b00c00d80d5515900140c02c50102e030300030010300c10b000048080d440c1010034010170803518009002e95070b45c014182441444018584c20080b04403402c400164040c90a0342c0c03150140c41c3c6070f038541d52280390440280c81039070340280400030b0360415503480352105290031b8122150b500445038001c1e5020b000360103649941c032002d030542c4070501c601d41030a030198104075803121091b010f0315400300c000320150700c4078101034015034030095070a0b02140c1c43c08860b00c41c0783d0700710716000541ca0900b80350000300341e0307103c08640004401d26004a2468034882480301078500d0254004005003a0b0f43c0e21202445c1c1d02e400403240103503984000480010300c80e000c0d110315130130b86006960391380c0722500342d16a9441001200c071072903003159420441c4112380b40 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 647162302 1250 647161052 647161121
    0x110a0b04030f030513050703081602040501030b15031b0904020109051837180b150102120313031107270f05061309080d020c15010807050112 62
    0x240309071581d030a10000d40b8002800c80d03100a180c14030f00c240ba14100b40108500003021011264000312890340c0c2d91200d40b007184a00c0101400a41103400c0a00104c01c000f00d0300c9125114000c079403079040c5003414445c10541d6840e050040e4101341080e100180e8111f0a01c4019594064010b041110f429542d0344045110000c3d4414802d007504800801e101200c8254201c2c50a256030440b290440c80b80a560480000d15072140103440c8036641c0c000002c00c604103402e000300481d400ca0f0003132910b45480c0e03585440c8040318012082c01401583c182c02e410360314420603207020b520100c940f80d042081c6941d061ba400c01100a0076040f82c4518a000103010070002032030f4940c01d00c3d13082080b01100356070701480240c4030300014003601c842c03e10080041a403129010f1407064005114082000d803280d050901c85803056044c0414840d000051072103500000154401c0c00458105155441d40e0341c85c0541174890816000e9140000c1014104a01c420240c1d0812420001c084481d0310b640404a441750b21400c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 647163552 1250 647162302 647162311
    0x4090b090c01080903031e09010b04090b100902120703051509011202150415080c07020a121401110912100501080c0102150c030115031509020d0f110a110a0b 69
    0x20740c04508071040c00c1d40e01081003500302400b034009608506200340c40d21030454581545201ca0145100094042c41094009000490010f041040340022070704000084102c12100140f81e821400400151142d480c422100744030400c072035100c069118507008030040d01d80548001d0080801110080340b950b1542e2078140245132103034101e18071910501c14003a805200b07a00d00840d008092004001c0c2010200700490715890500e0107028650740c0401c290800d02030341c000650000c82081c000319403c098540400b0519014402400320429010111420f0310298a040d4040705130a100110081c14444e4001c0b00202041003a074102c800c20308008400c85500360700855441e404a001a12a56010300c0300c072042040052403210a842c1103c94940284010311403d0000d0346c0f00400c401c44584179a12030064004502c00e00c01e86c40782e4400717500700a5007200050003141d0b460944a100400454411b80d0750115500141a007411406002603c1000c110003003a01180503050401000890300d81040340701c4c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 647164802 1250 647163552 647163571
    0xb010507020a081e0606060922020f04090b0613091d01050c0a0f080921070b09010605012c06090307030f1a06010903030e040c0e1528091404090b 64
    0x1c54005008070791040135012070250203034200702c0903c1001e0704c0710701c00c4601c1c0a0013074520100c1c0d44c19681190344d031004d8054060b1100740c404200c045020080800a1003210000350043c0040170127141040021702c10400300d00b244480041082050122a4110200d0186047c001502000011a10a00307440f000c854044145900050070f03030941d90001d080d1126901c0b1854000f80b10710700401401e5941000a154410308a4044204400025440201d6000701d1780f24100708014144102180d000e01458001c0601046001c2041640c001c0c00c0f00b14001c0d5126a070103102256031a07201441055071041000136014003d8060100103e038440010103140e501c2046041040800119410100140540a94104100503600300080b0717a02845418440504480018082240b100c046d0b03000303210b20f10340b1a0415441c2100c801c0640400d405800c943c401800444558202810034090002c1104e80c81e1340400c00300c903030502c203d400e0900404000700001d030000403490003507228600140c804a0340c0000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 647166052 1250 647164802 647164813
    0x319050109061112010b09041119091a0f070203070308030705070b0c09010c02130f0c0f09150203040b0a0c051f0c020a0203100b0a210b090a0203100b010507020a08 72
    0x2c0111500c100e94442c01502d10307081c1803810005001000e030806201d01c0409403404903000c00d0303996540e40020060032034900d1690317440030031a2159550034101756400021419000000514400c2402d60300070f400d20a2034041c1c940f103480c400e05001354201c3e80c4107a80500c0750b141c000c00081c5402d40110b0044007030340c035001d44803401c40c13070f01c02003040300202400042c050900400300c041c1d80000800c513030135a049500403410340c40d0303801000082c0005070410703c0b21800c180003c0a00e80e04070350360000b0828a81e9500250b603803a8080a42003041c1d400c3c402c00103a004103c1040812107003000381c0045410303450010244044e81d2906440c0100c2d8881700361481e0024107000440002c43e11031071603100c0050002e0300c01030490b80c00087c0c507400103003101541d554485d84101f071079940d69007108014102d01d4a120220b0340714081c01d5441c02c00b442a08560030007910010408038200050703565042c66005000b4070681c003140c14514054480100032905000c41409800f0040e03031070326103a0300074042d084000c10 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 647167302 1250 647166052 647166071
    0x91353040905180319030908070b010303030b01020111030411010c0c0b0f033301030b030a0b15010305060114091e090403120b150906210f0106020d0f050a030b03190501 74
    0x80e10068440d01d06103540200b181c1402d450524917130412450003810000f805d00520304007440548100c640c002d020303804000002c8100340e055400294410070a900800482c0390704440302c0624031082d0340281101c0201a0054440e6115850303144030203104e50008044a0350ba841800c0013034000042500800d01d0110800094000008004070180310449200028090094902c070b410b004511542e410540c03184141400741d10200189070110303038003000c00c000500e4102ca18070900800d0019544c0001d0034000801d640f50b22a004c0b40801c4450140141e1401101d103003048125005000000e94600c103801001860369144d40f107043c421030080d05d0340341c0700b941c001503c80c048842202c0007a1190540b280e40000301e250700807d03201c0c00700701692455034030800c0b50110300003107429003da5402644514100100c1d403510715011812610550202c40316043c881000b902c850001c207140c140020000c0c820220110307c01e41000310415800f9041e0344049900540000c0301d80c104203810f490a070344512076038 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 647168552 1250 647167302 647167321
    0x30309030715080c0a270503030a0302031803030103020a12230f060a150b07020d120c050c0103020405100c02011e0201090b01090507090e0405030405091353040905 72
    0x3541310520302200313031a105c0c0404000d0620740010044040340f0a03850070381c0c8049035010a6060140c02c00600312038403030122810040207580115040d51040107005a81035691034000f007030301c3c141d035401844110103505240f09c20b01e45024a0500b40c64401e4909882042140c428045201c010320b150041c100062440300850301e0480050302d0b1040086c9040060084000e0700300304030b015160b0200c0516a984164000600007a0700c058028040f041c8818020407203680002c0c00c03240b000c1c400c0096840b0903100e04019400c070300540c800c041d0000a0702d400c82504a11844042482e544141131603201c2414032204100c502032401078410246c0c0d59191400e042c010251202801001107200c1800309140102d0000e11002061180d084102000404a0200101801a50081e006c040d1080c507183c81c0031081841c00703a02400003030305d80300400c40c00113440708654190740002d044540f14030361412807090b44109104000c0d4100085002c0250005410400c3c030300000c10007400e032120301041c582810304d144c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 647169802 1250 647168552 647168567
    0x403030e030c03060105061b15010807090603020d0305070203150403050c070f0f2723130209011e0803030f010602011d060f2e03030e22020702030309030715 69
    0x196200382d001d512200819070340064090b0540e28256072481d11206028492000101c0c5030000102078050411070344c10303280300700038454100d51910085409055652a540b81200c0580c00040d40280c12000d0100219001300f00510020703102074215100c0c050801c03401e150518094034203c000500018540d41d450208101003006000b01c03000e0414003030300c0d240090b14290618847c01c000703041c00a04807204a100025509201404c03150103002042058050703080c03d111110000c0c601c03a00301004103102d2440c50f4404800c5d60760140c51400303a81d0901720302e4038a40110807000103811502100206184500780051401132220000c4401c47e9418628045d0a5030001d820241c2c0183c40c021801c00b41c40700014007190410510b00700c248071a140c0810903402a003d20300200300c090074801000301440268102402140d000f80c3d21507848260b40c6003081202c0d18460f0116019039180038442501c000766900030040704d480202120f140422802c08641001038a9012130581d08007100c054a005801845 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 647171052 1250 647169802 647169827
    0xa020c06030c0f071a0108120d0c0513080c0109170613020f1005030a0605061e070516080a050d11070306021602210613030f080910020c030c010b0a0305210d060308040303 75
    0x348c81e44c10015004984140100b03844801d401e84c4807201e0b040c4003070090003256410702c2800380d4070b901d19448204160740e131452014405c0c0000c81c0e03080b0004040741c900ca07401c3c3c400551480504881e4540d07040482e8000790b041000d982c07090074402809051398940300c0711400e0034455143c5649a00e001558030341200c143d07520250085108000c09a08080410503c04405919080b0f042d1a101c084c2007091a29585001d4680480850782020645100c0054000392152192085612604c107840d4102c41c0b80b244030500c0400c44d03019080510000b00340350064001544032035a4504200c00c0b507000038102c01c042110180174140d140700f400342030200604c0f41940c01094400c1000d5040703541e680044c40208041c401c001042808008140e071032900b809005541000510f05544441c034000545459a02c40e1441c484a51318201356001c240c1000000035003200d4205001c0d200501c18517444045d52003607948000c4035000100a8a44025628400d00026601507080140c9403400c514029108040085 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 647172302 1250 647171052 647171069
    0xc050111040501050a11010b09150f040e0d050705030c100212090105040b0406050903071703010510080408030c0f04030c0602030711220b030313030501200a020c06030c0f071a01 78
    0x2052120f660000c0407159402102d15001c00881d100302c8416005003000010b1940c8111010148142403d131221001e03000c550456140c01442f5a8504210486500722289241c9412803400c0751840741c081c101402030140100c054910741280401d200e401d00114461410326103a010a030645074400906c41c0e070383e1048200c5c000300b00609083e292407107410b01c0244014079a03078440b4000f4640f82030610a54100301e0f4000c5040100c41030000d4245540c0d0400d0140380e018500100c0801c20039032103903c3c424021904512002d00d19110342803148603541c803503148034200401c00c10002000880d01d040d5080108a0f40c1d000d540c0308d50141c5007181011102d0a40c05200720b01d8410509000c40c80301c900010b0198402c5e00000e1380e80c840c1c0c00840c2c01c5004215452540034401c040001c180b10040d007100d810300700704002c0103441580d6a1341141d058003647c0c105a0050303024000040b11410b1180c021600000b907940b146d4209200c05440030f00c1c0d076010800c00c45102d024200c1e03024075121542c0069014140c0b11 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 647173552 1250 647172302 647172307
    0x306210a062304080d06120f02030f0d17061203040305011a06181207180b150a0203030708191a03010e0325080d05160e010e09010e19020301060c050111 67
    0x80b20034054084000c0d002500380c4200140301c0311801c94540c0180010100350343c4200014441f070a0100034039071358031801d80c001e020315009405a4180413172580d84160007a20354140c125060b0440d502440002041541c100401d802803100070841007001d000150311400c008140480d0303009026400c1d001203000c0300d00410046c042c2200c2c029070350380301451280f0141c40240b0b104514820b071b00c2c58101c0a034011031135140b909040c0c1041c0c150302d8208034542101034840c05002800200704806030700c60901c8541c01600107102083d410761044403226000704140081c481e80c0326040c2c8502c4122184500f55800e012500340384180b26050a008485c0308144640c0a94240022000741b002d00c1466403202ca5010492217400d101007201400c252000c13503400344410807080c0340616440d4003072181200d03010702144010040442d1907114100444c25840080c1ca100056480e000d084500883c004d03029140544000c4c0380300d80c689115202540c02486195545030400c0d0007400c005003107604c201550034500c2c808 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 647174802 1250 647173552 647173601
    0x7080a0206071b1e060e03061e0405011e050121150b012001060e0a0603080703210f1b2309010c050106060e01032306060306210a06 58
    0x403030003034844054101490f1003140c02041c55030300401e080d541042c102c0310380205049003481e4118a015090720420703210700f80702400c6403040556a07007040f1480c1814101050b1240d01e444141c1c444035800c60300c80c00001c9202441419045002081280d01200d95540e4200411030841c0c01c0c11038581d903106500b02c03010b0401e841c1d119400381d20040020b030038005480300e40d000080d034458044186019442090b030b100584600401c280a084644510f13180414201c000c1540340c08a4032507d42205d0303128005a2070044030703030b4050769001400a0482c00e20058180304c4111080e0318040d418042e4442d034800900c94411101c01070868043c41400b000308404199079110442002c40b0442c040c4400e81f4100e07032180006c000488a04692030001012075091800008119400240010019000740c07400d000c10b00582401200c40300c1e0f0165034a031209407110114a481c24540002c640110001e08221503101d030616481902c0100d0b074002d07880d25405504003c0520505c0c2c45100d07414646101c0901d4580d04 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 647176052 1250 647174802 647174809
    0x201020607050a090e010305030304112e0516060606080c07020102031b030903120c1207022d180103120c0b0c0c0102121302011d0d110f03061807080a02 67
    0x300034a420300344800010b059a032a8041e00891008002d011900c2c5071941e12494015140e0b007040c0d408030380701038185c13028580e41e281840501011180c814031814a0b1440c1540e0f0581c1080d6070403080007409001c000400107503441c645401401400380704081a0b0528054004016034001060710728128400d00440d80180e9000c811644202c89030301c07958001d01071402034541140300d40112142e042c8242c0301303003070750a400380005810b07204040d03410755101c441400b605002c64030803100b009511960080b507000b14011011040703c0412007100c2112000500c6501143d007100c805060f060032f5003c58001041000300340d03d0215a00240780c03030182c0c203d0318039949141d81450b001c3c1039031a01c20404130300c812091100354190307030781422600c2d00c070202401c0489080300e00422500c01030340056100001c8c100382e010410b641440d14034014100390340100081d220413480c0c8020740740050340165410700212940c0d4081002300d00603500b210740501c00c4000d0340105072900440f58001ca00ea43c10200b4001d01594 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 647177302 1250 647176052 647176063
    0xc0f030310090207111002060a051f090f11181e06030103140a021003050405060a11041406040b030a0606091202030c10110105090f010e0303060d080f0c07140a060309020102 76
    0xb00c0410016896091902e801001000348510103600304034141d0011001550002c5d4403405031929500400c01c80c1c8441c40813002c0003000541c0060744582031b000070001804290321055150354488030004031400d00840c2410706901405c5e0360340d40c8040c1c4001c680014545061007000e0802041c1c0301e400003c0480300400d1181c041488050424003014901c010020010701940010300d5004103103c1a0440c0e086015001748410f9800350391921403040000c4605003030780314803855200c400c0521420300d40f404110000300d0700300d500d840c4c1e08503c051000003082c0803904065401044001000324001e800d00c08024012059644444800d00400880700096200810b1684004500791100440e03000200f00a8407580180007070320031250300e014204613069001281000c080b4840c06d00a01a000d4403401841d6240000c6e64120b40c004020080f810001720f1503001071031020a0030031050f08091104500c3c9040850300d6015900b444903100c180602880c2c080780c4600a0091424100083e22094000035501c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 647178552 1250 647177302 647177309
    0x50a020c19061112120a0506060a0c110310060e0610050715090611031015050405030606091305070f0303020c0a140f031906020c010b041b081f0602030c0f030310 71
    0x40407016114444084c000f01d8003441d80c0300303100f0b5660345940c019440d0034a4100c442005a03840c20300450440d1070a002100c452590075502c4503944d188a45609041c114540e82c4a649840f81c0781074032144410074001c0000500c05625120114500b80f003e01c00040f00d00c080c44001c10804200c203800090420841c1c80300681040030000c2c03a282c0c01e140003401082960052408040003104000300751a403002c2d03000540d011840a10322240b1249410740382802a1b02449a254102000140803407c1c0349022680c00040c000c5c40102440007501e400d1709008050300280083c40c580001402403540400c24885005416a401041546050350b0300c011403003040012403154042081062103030b0303070030404411070300c816280410004a65141110007583301701c07205880f0303509064000701e0500c2c0a1058100310b07000c250020409600c4140212000a00209100c0092a015880f03000421903407014001a01c0181c004651301c4440610315481d00403d1003402010340e000b0003c00000501484416044 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 647179802 1250 647178552 647178557
    0x1120c0314060a03030c11130e0109020f0a080d050f0f03041412071203051b22120302030702010c0f1205040914090309150705060703060f17120d1b050a020c1906 71
    0x112400800096234a05a6004482d41d03a040c810903009546066115000b03492088a524001103004024044400c00d584140c681c0c03500440a403e000e580903034010110b030310090441c18a0008102c0348050130740c005403425640100c0610f00110b942900300a180710305115859000c1c04c011059440c2c01e019200030a4140401d52600e0100703450320300924200c0139144808242c9900c40d142900c400c02119004680d440007005541c00c0014800f007607050818000d42c056010f985407160640054440c5058501e084a404c0f52015045000c55002c1c0c1c1a12603040c0983d40313440e601c0f4900318840054460882c200007030b00b0325841c10301c520581c0000403070318a044155001d8100c4d56180390410142d00612501800c0e9020b02420040142c1d4154040402c2d40d10380b8a26032507003512110741041110103882d60b10750950201c409002e1030403d401c0a03281c80000c22001048145604108000031861030110300c012407030101c0ca00070003540601054407282e009892190099443c103510121036012032040b43c00303 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 647181052 1250 647179802 647179823
    0x903070506180c0a090b01180509041e0f0503091e031c020708030c0309120d080a15030f0506040c091107060c030b0303130f090b061801120c0314060a03030c 69
    0x40b070342020300c014000100010038018040381e95142c008085c0c802e002000c0e001501c110300c11510300075145240030544602901040305aa180e03560203207440e111000707401c5003403001c0301302600207550703415201105172066010b1921240200c060101510303192001c2e56203a401200ba00e0b840c0c1d1000a00800031000c480f07a8000c1161a00034180d0410810b508200001e0000180d0360710048800402050036070700943e80010750500300c2212644580341d006849000421200100d440003506400030f4030f01e24509070f0b601d082d0503905d56413015510172180080355150030107010001480b0601c0341840050581d08001e000810040c292110b5600c2107500050000d50f071803903450112482075201205482e0050201c0307580346000420015444018450ac5100ca200c2d0100404c00b01d80c180180003914001811250820310540c40341240469078824190410600c40c100c000b18414500444800701e00d10740700001e0b81d0081402c14941c84c80014581402815074107400c000103980242d00d01c0c5600c0d0801310044 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 647182302 1250 647181052 647181091
    0xe060d050a11060f0c0a0b07141b07050a060c1103060c040b1b0a0c0306060f0501050f070528021903050a0f1b1502060603060403050405100e040f050106080903070506 73
    0x140f1500500c00d841080420104a461455400103895441039014460700121039480aa003112195540c1641140c0302c40144011925408071105496180705c050055483d21901ca0012980301c11503584001c2c0042d00346840a81440a0704000c07481c1444143c014220601d00161400404d218500c01d184503e40002401070300e4001c1b8007401c1401c3c14400090340d203044507034200645038005134041500e403107190950016180a800625500722181a1249810b0130070f02ea00c5e034a61074000c11000d480740c1c080e0100401c406100a002e01040c4410281da141e99100c5500500205440e80450704048001c6050284007144000583c0d0ba5001d40c4105010006840c51401010b405480742e50503202c121200c60110b4a0081c0307070100c2d0100341c000e5007111096500c0f0303802c040d60303040107403070103008110108000d00040c1031104a61004031190f00301100c001d44590301090071211840300b800c0f645555032006025a5038080743c20358221402500450810240b5129540c455001502d0205001516218103 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 647183552 1250 647182302 647182309
    0x20307051b070e22050601080f0f19121e03050712060e1b210a0524060f1c02070b0601230a030b131505010512150102030705030705070e060d050a11 65
    0x51381d4a03030000955201d5607650005035920000701180d1001800b5484141c113210b1400035404000e1011951106411111911404042842e640f20340040040e8048903151740c10b07d14a000c000d80c461540d0019981c9440072008140c0785801800060f0681046c00411120444c1107a59402014003070442c031840303540182c2e01c0b000c0e01c00c128103074118030200c2d1040c1203080500e2903040c0c840c1c0c4030b0711020701180d91481281d0140756a4031201101b1460b01d840c0880c1c9a0800704064184c040d40c8036001c82c0360031503a203480c1201400c0191005003040d000540c20040100004a02d81c205d042030902c101110143e000d00124510b5010061071185c4012950b024000d12907044180300c480040c20701c0c1c21001c04003617210701404224260311440c0000b0540000c0552080c01221200700c03010700105440d4441d4800c40308400460025141107100070300c030500110300144005d0000d64410300c014000945040c07401851000000c0c1180e2060f5040c2c0070040100d0346c00314000200585c82001c4c0007814075086d001 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 647184802 1250 647183552 647183611
    0x7031706031905060a060b07050a031404050411030109110309060712061802071209050f01050309150c04060206090c0a060e0d0c181407092601020307051b070e 70
    0x700e0025410040c003002c14082d0110b03c036400788401180601c5090f440b445004a44d1203400350061059100c600608080fa100740d5000a400f20700680e62403030f00c1e07503640c00107040c0c0f0904600c2c04180c2c1c00000040200124500c00c0c0d850500080c0091403e510700b0081c007913100e20005140000340f20300b5456030200d0418903400400500303406070101c024001c982c403862009400072082140c0642e1104a450f420780c0c01503607181d00322100184000c1261052000441e06504042d10980031031040d80281d0303608105003460141b080c000481890f480e5481d082c0001d00d0060060300300c1d003a40d0440b86180c0703481d03200d159142056542c82c5c01c1044050408101151014124140140020311ba411005c280c1c410403183c99425655403a600348042e05c80700c04003115004007a2659004100340c40002c000344407111054944607140b004513459081c5201c002c282c00e9a0040707402c400060000208610280e141081e100c1b80c2d14a518001c03c90300d81800d00740640030750301611030040c010441e0302c014007050301d1020 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 647186052 1250 647184802 647184823
    0x308070c0f060203161d0a051207090608010c0f1701121e030e04061e03170408060c120108060402010903110616060f0b18060f0103020f2704020703170603 68
    0x115940d1038903850045da603030740800c3d42034006041004e0f851451889200440c1c2103c00040620303203510310342400c12003d41d00e417a101620500900000003904507852195070010980070b000401c40c45c1c2c80e681e00070320768002c80c3c2000c0240019550181e07480300c8110a136a05640c12881c07141c41c150700c0d0b810106200f03a00000c80b4203144091044180030141c1c001c4d080c00c1071680130384043c09450380b521440107030030032058601050442400010408180c0100e062035035801a01112803619465a0003541818030855000c0304440b80001d40702d0308142c2c4038013210300524000018003818102640000d000304941d100c00f03441d100440389440d12a54600040b900800101c0d58410740404403072420101074a000b800e41003d0f41e00d04044d515160030aa2240740c4404200b4442d56010754448041002d08040100110704041e82440b9036240019604002c0026000c5000a0f141c10f00e9495004c203481c0d801110424003075401844002d002030b4100d11402c218030740300401404a580c800000c01c1c82e00c41c0112 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 647187302 1250 647186052 647186063
    0x318060a090e34080a140c0703140a03020304110d081206150a02010608151e10030b09370b06030a02041416020d050a180503030307120f05040308070c0f 67
    0x2012800f480b80c841040400e02454a440385250b64207420542159a0074552600c14001c803000034280030b8920380280103603032182c141075074051010420380929800280c1a50003095000003448240107901850349001c4a0440f00d170f0b0f2080b000f980d0380c101c0e14001c00c208904e01d00355040104400303a031021240c2c983e15840d010403d44900d94094000c0c0a4038051090000b81d02605902090405101140302d102e81031860f46900c14190000d441c1091600c000c20107010038482030404030002710803100703043c0142100780c000c01110441c0e01c601c200490000e041c0b500305122000304180d0710780c0904105800180c00c0604180f1070f41d511030100341002c02d01c0070020762080c0f0309510900180a1403c0f40d80c02045201c41e01c5c42402400b010583c0d691094190302c10101d80f05006c00e01c4450f2085a0f00070701310042005503020a65a0170100c4e1640e0002e580c1030002c1158602c01d900320300d189100c1c04440f640c4101090182d41455200640b40c46000b50000f0100300310340c12500b091042e001303229400540d022 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 647188552 1250 647187302 647187361
    0xa150902031c030f180c0513020d0903270e0c07030c02150a141c0f09060e0d0311040e0402060a0c0b0702071706070f03050a090203010504050318060a090e 68
    0x2101c00400504c40425400105071030072121100300344a4440c070110403a441038440303036494100340400102d503540041c41c3d00345507020026442100c03030902580d41c42034440d0700d41605040241c1c42004190f4000411a071030f441e50400100441d8080a42082c0c11501c1020155a5034036103050444010a05120203500600a9000031400d1101c000c028906941c0da5a241c2c981034109614010300e03403040c1040140007003503980ca0708070414602ea00c0800721000d0b00300c1c002114040f46e41d4040680700461104ac034586c000c01c0400c51041c0d0503015040480c00c9003410035240504240460070001000b400203401500082030880c900c5020b21003903d61950400405485480c0c005002952480c45008218506000d4840c0401d0002c00080003405102d464031103001005041070124000c1034024040c00e5800d4030b6950110140e1021b118441c000d0780580041e59641c0101000707076041d03403600c00d080c60240c081042101c144690105000f415a01d101d8021801525000410f041d0028000101c81100d0300c032 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 647189802 1250 647188552 647188603
    0x1020709060e0a0e030a080412031d060115030902060d050703022203020f10050d11090a030309050901170a06150902030c0a0f021606080c0408010606120e0a15090203 73
    0x1002c00c00c030f01c5a000071205100050200d00e9081d10380c0103114412005c02c0d690408180007030406010901c01010a00c0c001600021400028141820b6494103140707a0f008034005201300d00400b00620442ca0650500340041c0040754042036261181c034401c040410380e14400300e2111071080c0c044810051003039002606003109a00c2c84100c01000744000c92080c41990741501203420004c4200070148241d45482c1c1c1001c3c01c040e800005400200000c40d41c0300801c000d01841d90b40c80f103001030040c6000e9034400c01c0c40e60400050119059040e00401001c2c8801300c0d180f4080d280018608092036402000440ca40811440c0b440c8030316800c4e0014000e0303d001004001e0781d020070340081c207041400c3d41d480303035240c0c00107807420307611000c0e4030107490521401c600c810b000c2d241c000d1422941040c4440c50f50f034070b410740d06c581c15821280540c04c030000040310001040407210b080d005807030350804005d0140118100580c2c81c5206520341c8056094825160301d800700541d6000d02c24620711040001880c0c3c480d014 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 647191052 1250 647189802 647189819
    0xb0d0311010b090f061201060e09010606031a030a12030b040f140f2505090901140a080f1c0302070b040302100e030306090601030506190e010609060806030c0f0102070906 75
    0x204a814088907601e0180c4095107860700c610f00c280100f01c140920100d546402c2c00740072040b401d860060320103648807080000c3c51001550560300c00e011a400008106003041c40040175035650345516030f4002d20000680c00b0b240e901160001c00305900c5030f00c091041c03000103010307800b80c030346040d4040d44280f038101c48103444010f0b0740204111020b0300f03d042d550340e5078145040203940c109071581e115103800700c9403010716030b641c2c00c0c0882809100d83c00c1543c10403088000040c5184000d801804100d0801200e02100b810080c03600c1000c0d20600c00034004985141420325580c02c81c5810350fa40d00000c544003281c1c1180039030304689e5441d401806070903040c581070501965441c5901525100c0c140b41c010b03440024000841640e01070f8900520b403102c10344030100114040d000c040c00321984640c0c5003040e05090b035946071943d030003000404541196507240503406030a00015601203c01d00c0459004c0084a950100d24081002d8040f01e030358a036000c2c00e2004034074007041030b0040c10105240007004512a607 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 647192302 1250 647191052 647191067
    0x30203070801170703031407060e071a07030512130f050c0108010801060605030c0a110607030b091501020d080a0f06090e010605060705060a0f11070605060a050102010c0f120b0d03 79
    0x1030360780c585812990380c0c2d80929890021010b048030807900f0003101800001e100d07500d80104002140e944500b0f207426511000300704ca0113001070104c0c0b503002e500c081024000182d950380622100151103410728240da10050120b11451b0a13406001134640d0002d033389801303142604000750740c104002d90450005850100d680e805880d451a0100c1c0349000001203104050050109031050f9503226802c540351004440660740001c887c0506011110901040001c0100001445402180d4008c10b0040c10401806420400601180b550b401c0d190411100f0f0790700003440441412040c5450181030381c3d000c0c8100c000b004c8403074030001e015090807000129600c554104600002c1900000c01c220f99851082040910411000503e160003078000144a076213203620250a00100000109060300319640c521031562143d00222801623030349040c041d01d4202008010302811007070008021100710050003800540c00164040c04111240141041414440d0040012000080e048100308041e5160161420 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 647193552 1250 647192302 647192311
    0x5010e1f020a06020c01230147122202100e040c030b0906040501080d0c050a020d08040311030111030114031e07081c050d0b041410050a2c0709080607030203 69
    0x40740030840c0d8840b54078000c150904070303040d0814141e8408080758940e01d085007a2031000f8180d0031015080489249409002914041d03005c9c030403580c400707000d600001100000b4040343c401c0300f601c28820644004520483c844180c04580c014140b003000c031001c860603000c090107941c0250515450104858250b005082e460741d04503000101c9541d00c20500007290b9003480f800c03a040c6e10445240310054051030807490064002c200f694031030003594020075a2100d00389411198240b00107010030038058220041c0404503002c4000b800340e040d80c1000c07000d00340818007985005000700020825266400c1241e1107214604010404801403001d06072503c6070078504ca40601801004c09040040b6000080070801003a29210103040007100082c030002080ca058081c3e0f0081e03036590390f031450180c241c85090b03c5000005102c05109042c43c0034056040b00c15440100300da0b680001030612074513075401c0c2040640e5000c02c2c807809541c41c1d0100b00c8690305568085481802440c041c404c41d00d0380b42d001035208 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 647194802 1250 647193552 647193581
    0x1090204150216091122062c040c02070905040b06132d0609052a16080310030b13140a05060a020f130927081204050708011802030705010e1f020a06020c01 68
    0x15140d07610424000308c482850b00c00190341050000c0d0b80380d0b19080e0301000310032030644100c424058403603544034115181540d0503070b1001d00540410580d45494900c052542c1000c0c4c0303082c051121606480c40200340500388003400d2011801c0d00003440d0742075501440050650510030310007410304244040401102c0d1038210640900c1c0484000030307604000c111250615034010014442041d03884560b038540001e07211070706e04640c48500001003448068500d00604044543c001c2000452800c80e0504040d654922400c0d003204140a011480101d4400e40c40026241c000d80d5070350820007181a584182801c1a5400300308080200b90900c4030382c40300f404041c584121401d80750031808414100c050f000d800500b00001048030060b04240e4080b1503800910880c00c5890300d0742caa0b00c0c11825070742140080a102000001140c041d03140400c0840024103080c2809054002c060b404200440803500c04008145120b000c1203c00910801880503010380226046407920521000f05001c0d0003940c0d4101c00 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 647196052 1250 647194802 647194817
    0x181902180306150307180f05160801081c03020d0908040b030415020313020609040f060612150b19020f12031608010b090111070e0109020415021609112206 68
    0x124110011009420f18000800070b10b070180c60200c0040a010101c41d04040303440d01c510410889644901455014445040c07241843c051104002415032005911800e0b55030b001c840d542c164101c03100b120300340350140c1c5d24015940c0ca500710304c01c80c00303040402c20042c00321200140000f12004202d020f1400355110300c9100c14068091068102a40030541d0170910340049010203000600c4c10b08002c1c0b54183c005040442e880142101c0f540440b0079603441100850b01c40014451500034510070700382111080c0c458442003e08203005003a040c0901c1d00c03001c00c041d404041481c0c0b10340c000c208500341c3c1182c0e2001c90300e805000c20100ca02a4109441d6140d84982d11207205501500130580c46050f034980c0c90456040c11408001100c240355414070420060103080c402080e1071031100d124501030800780c1000f43e43c480c94641456034026000c01d04e2001c40d08280d10228540c18110310400c00c488518001103a1890819403c0d01c07588250800b2030755200d00c01010302000340a883c28a0200e4085856030103 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 647197302 1250 647196052 647196061
    0xd0e13020702030309040207141f0b0a030f020f130203010b0703261b07200922020d110405090a0201020c030d080f040309080a030e0405070e181902180306 68
    0x4141c0c02141c900950580003404541442e04007540940075090040441076001c10580c4043c500340400c10790640b0381070400c42040a00c00e1040e018100c413800e0156040300801d451502c50414610511000a100e40c1c0c440c443c00b241907440c40d0081170240001c0204550303d50751845060020f521240b001c03408968071f188a0100d01d24001c1d080060845400c114221503500c520105008181e01200030030081c80a12030f078808208020341c0501c0c12404204910301c21403010041192082c0000d1124547c000c40c040b0701c25295000781440d03400e0507070503100301070440f4032850b0404242020304503843c0c00c503240c441086000800098180324180c002e80a4440708010750f0305041d00d410102d00c1190108403018045603400000355000c030b900501a14090789919101e012041c02c003038031004183c0c0040c0302a01090035500d454814070b9084851403c0484800200c0c50205020808084d010005003440000103001c0d02c5a07048002000402c0f0b0008566581002c240312040e4041c2c0710700c40b40240700d0600080c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 647198552 1250 647197302 647197339
    0x2b0b090615031503070b0d060f09050403090608071715130e0a03140c070308031803030f0402060a03110d0e100608071206230a0c0c080a0c030c050d0e 66
    0x24541098050410b0319507550100411985100580d215030588074900c0c0008840c0e05100140100c00b44090001c01e4040c9030031440020a0303034903048505014074001c1030100003504050900220b0300b1f0760600c010117a41385c02082d140352140c00c5502e00c02680600420a9015200341500c40d0050220b40c01410460020740038021109000c6640301c4662020001401083c0200055808003240d440c0462a01884070b2546041400c545d01c122810304c0081309002c01403884402c521100d803126401181107103070001e40c41c84175101c00340010b40580300020368182454440d07008079000e00501024207036120002c0c0840e800810059500402c24060000b900c0022030040c010710b4212440c85005051150520012200c0c03c1e9484400300e42103035460760314034082c00700305030b01144046445c0c96075a002c2c586003e50380151019490440d0402403120844000240c12005480c001c0901e850120300c0d0310b00a1505070303a06180d15070081e05500c03401508140480d445004660520300c252040703500d02110319500f = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 647199802 1250 647198552 647198569
    0x90b091501080601142503020f010504030f140d0e0d27090e1905031e030712020c071205061f030c0e101d070e0109030f082b0b0906 58
    0x11400555168081103d40d8070402404070b0b03201800c000d075450100741e840994240c03004034940702560101c4080c11014543c050203444503100c031031700007408185490b95008242c0121511210b0030b22580031156815030020400b9101e04203080c9508100c070341038136409030341e5940d03200440754005890701e00c040c400201507038118031100d50140d070101600c2d400c011816028041150902182e4800d0340000381f50041d000f14102d03c1c2500803005142c3e50101c0e031034607420410041c0f003021441c3d01c0030000d01c000c03a607100000342c6000c07641020040e00c1c1d80120b58500d0500c2e07040c0c0e100220311000010780200b88070000c0355640c0a0313010305111128600c079403002000008074610001c1c0103400c0310142007001203500b01c40542d120f5018213500d400981c0391000d8840c1d0112040c180b0120b44403010400416a8008000a04003c1c09013020a42c442c5140d03110094906964002010003101042540c588580007268462020f00e0b44200c50a12181c009501c0040c01454005441075112501241060804158 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 647201052 1250 647199802 647199841
    0x25050711040f1e0f06080d0215090f0d05120a0c02030a03110405031501090e0a1502070314030c03040512131e050607080d0609050c120612100b0103060815070f0513090b09 75
    0x39054031844c1034450b03203004100400031822b0307000b80707038042540c071030103005150300841c060b12040d440b00d007882d280ca801c1c80401070441581900c3c16040e4108281c002003915840c1c009403501046030368240d803241c003140c02641e000070341520810b54440f0141c220300c4003443c10398080c0d11040106042006d400c50740d0301030441000d0721420141c4144105640070350000e01c030050103030905040c8010ba44003090030960088a002440040100c01c2c40100301e0240580c0c941d0782415400c1c98181150311000c811034115611070070400101141e141100107401261090040a0040c01e03191242e40030700700001c20b640b02d50320500b001480d0800110d02a001b038441d00d4010100d00040e603003080d009103414000003070064241c0d40d10002d0300c00d1501e01c01c40c0c1040015021004904081000003030f100c00035056a0f202c3c1c204031705542103044650012801d000203142d0103e01403400a02c1d02020590658440c4a40030f02c510f00c1480114021407159030903000f803044500141c40213175141e07031032050b0102100000403 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 647202302 1250 647201052 647201057
    0x80c0607030e090c090d060507031505010210020a1205011706010609060e150903010e010204050f2d0111032b050402090c09031525050711040f1e0f06080d 68
    0x50b014219040c161119644500b00f6120140761240c21400180200e812a000b00e500640301c00420078000d038140a040760140e11544500480c9040400113919081441d0a2982055010450b0031007070340b143e0b00000f03400040610410855031202d507252680c100b0702d81815440e1240b60000154103101e104442d0032185159281c1203000341d100b0402c056003200f044003d5074080140b100c481c0303030782c1c0a11510165000800005079107619160501c4091002c00b019607101e079212100314021240722204e11002c0c0c2a41c1ea040b10160090080107a40003042040000100c0c8004036503410116040d041204444070210700850341003481d0102001a52402c0b01e0082d0001d005401007001428080c01400d050200101aa41d4600d040410800001c0d412540f24155140d030011121000d081c07540c0d00000d0303100ba032810901c1d080c002d440706208000b0082d4000d000d0b40e940e03045c085040c40c43d44e100780c0700d59804405044204904103000c002500c18800e090406a1421100286c0300b0000100850000c1913078 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 647203552 1250 647202302 647202317
    0x50307050f0f0705030a09030501292419030b0f030a0f03030b130b090601020a0209040f051e010e0f1903051612050307020111180d150e010204080c060703 68
    0x29410191182c0100441c18001801070201d00001441403000e420111a1907860804852031400c1c041c1c25039101c1c001090489407446441e04554601c1040e240c40075200f91013695042c805890b490380b410160131410300301e260011400090740701da1070b03443e2042c4e44030554003440b40003003840c02c119407054100c554a40c5640a02c00c86000030f1b0203543c0b8401c03190f00a0800007640109500859060501c0c10a5084100d5841c0406a8145031200c28070350084000e100070103c8110b15404152402e00180c8080c00e40c0c2840700946003048820060b44945040610142a002424072225400307810581000e203034501682451001d100e200094014000c58203c940c05044103075038906039403d901c603015401c2c090881ea0302943c0400c2c04080031644100030340d55a642d40b840c0070f11000303084414541c004030940204000031858024039507107a00005070b044801050f0440700c0d14108032000120019841001d00300204c600c2c1024040d805807040720b4411050740e01e502c0a81741000b0142c0b02e4100b0060114151 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 647204802 1250 647203552 647203567
    0xa09080c2808030a090906120308270114040506090616031d0f0313060305060d021323010f0602010207051902011b050606041a0d080a0e0d05071505030705 68
    0x74203010740740d00c118440011015611101840d080d940082521000f28a080038100001c0003d0b100b06001051001a02c05c0c08040582e0014150030000e840002203600d4803030101c8400349030320615001032280c1e030700810101e200041140c8281300c080f20144c0301070190340000b0341e14100209074a40715540d80d14074509603d00e0b210040c4c005200240540030032102020014400b038408014842d03290f801c2600560715a041d102c10901c4401700c0741c004508241c00d100521100351a0001201d140750750488601d041002e020800000a0100001c42c004000280440040080e1403417140c80c1601ca11005030080716883d800168240d10460300700428503801091380c629001d00d550795000348bc40c414500046c41961700c12004491280109040e2640d4100800b803103410b18280c0300d82481c505da80c403040241107410100103640a501110040d1000c0000900c0c2c0c2d855511441501e090f441c4000c013440c41821803410480c1e900c500a000d600d00541091540e0640e00f0300403410b89224040e980d40d100d150009 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 647206052 1250 647204802 647204839
    0x105120f0c0103050717015d021903200604090b030f0a060b010f0c0206030f180d020303010504050609040c03080708040f0608090d0813020913060606050a09080c 71
    0xc0180400c0400c44500c41c00d07040004c120400600a0028200c1100c200307100045084030f018588414000040f11110071040020407000713506086440e4003166030300210042300d541c400341d88400c4001d602c540c000c451441b82c010303031203209402d5074099400c000390301318401070345c400040704416515481003050004012240c041e40043d0a280806415500c0740c0840440052910000000440324a500c5062466035542e002c100c009030610507244c0050609200c0e00030440c0c07440b010f0720140c01448400300103080c0503880c0a080b0700c6c1a80f1107040754110240c4034802902c0350000e0052900c91030600380424181c0c640721a00314069904581e00303140c803c6ca541d0310f0740c00ba80e0010300e0031201484240000546401c092602d10028039964440401610b03000268604240301d6140100c1404144000d1204421141c6c40d1840d0540e415142218503440e000b03010070100c1c0416100502080c1006802314070140d05c0000303001c280f8865200d903590140c4410301c090b200e51455000e036411411081c2501c65560 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 647207302 1250 647206052 647206061
    0x80118020f061e180102070b0d020a030e0304060c0203120702060f07033b010306031101270b041e0614070303021911070f0b1b07120303050105120f0c0103 68
    0x1c00b01d510f810450102907090124091030003580450118001c0b603000107070440c541007200244003420245003060420013007401100f2000a2403640400c14654050107540602e044501c0074085a48139561941c008160082018040b4028002c1080302025040740f00140c0e0b070120750041c02503082c03090905803410550800513058040201c40740307504d101e40d500c00d00100107440c503c0d00e84400030500e80b0904d800c00300361078014a0426203040002c10104940c0c0800400c410401d2030f10f1700500d104030304101040b011248000a074403140c50740010326030038480e0040085485440024016098048010402c075603d88903030408120519507025405a074200106009442401c005041c004000e0b040941c0c00c8426000c10085104418103140084040181030010a05414521042070506000ca6014002c45060308181c0300000409070003541c09000c1304001e046501105000130005080040180c007082c0700300e5001c0c0440081c0038981110109480202808000003040c040401800460040 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 647208552 1250 647207302 647207329
    0x12030c020a0e0c0a032405040b15030c0306030d020718020a0507051e012f0705032b0b010c030c23010c0305040507050f0a03140c060c0a03030608011802 67
    0x59240d0080340100152900b6400f882030707000080d0300e03000011005821100c09940302ca40c444080440c200241d041c40789014152901901c002c1519142e0340f000c5041c2948036030705043c1802000c41003000d1130320320101440c8070f00d03000c0381100c1000c0c001540583c2c507402d20b40128006406a40c00c0090341c007005400910159002c0e15140d89416070a80700c1c00e00b408500b4105a903d408014414100c100003406484c025460004030811780c4e001103500c1c81c40e444c1c0944280e210343c40c03001c180c01c401c0c00018020f139070100706828090307071110080f000c26000c40d94581400c56489460030302007040a522031054040311592544400d07003510314a44500080c50011440070141d0b030805840100380c02002e0050711070030300442d1004141802c182c984070b420400c00c0c0d00094014114401410101d5485080301e004030b0303411814440243e402410842c3c107251842441580014001803003040d005000511041c0941c02a035007000070b2610303410201c0c20383c0c10745803611540071040c005410141c80c09c44a0745000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 647209802 1250 647208552 647208559
    0x623060a091505060c06100501090f06030506130e0a1a040320010f0e0705041a0303120712091118151023030f01060c020102030703030e0f06040506090f010612030c02 73
    0x240f07030360300c001406076401100c00848035005401440305000040420801804090030702c03603035103800c04815001000d8107102e1b4104150b02c900100e00709843d01c0034801c5070b87e81307046414001201c0310b540f035564030f10050f2002c807030f41d4035500400c00b100c01d01000c2c8103008a0b0b140d5156403041030039181d080700b40100b00207000015540c0f460210300000c01c0e4411042a1800c0a02070a2410328040070481140c0010503140c094002c01d0704100d8195402000311068000c01c0101503d4507201c80d54210781540518605c0c0c045c89144c0031252080c4000420b2081c60540120b40051074148542803c110044040d1030034549865006032100081c5044082c0c440390b903989140c4035041013060504402070b00c03a0542c05049408002052241d60200d0f04242805450a4109503418521a600003541c80c03007162070290826503210344400f0008803d0111811441e00402191420700301800c100f91200c6060b113003042248224408445090010b000e100100d0310340b504404100c0d100d58405588982034010200d0f407 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 647211052 1250 647209802 647209841
    0x120b150105030a2d060503010b0109031104090c0812070b071704170f03270a0c060c1e032708070320030616020105060f1f03180623060a09 61
    0x3c26100c0100c400c806940c1e40c0d0001710302c0e146010185801c4400400c00c1c1030401c10203044c1071022401c03c0c0f50711150142c00b6580091064120700f00b9203c83c80454001f9440c0d8012030de07600c00801000e4010340105401203e90f984070743ca40b032100303503420344008030680402c03491540014003049840c04a03a400300c520000140c036250781803690010700d90088485d03403441081d00040b50a22414a001c0d46000040c03900104500d840380d80b100150003a4134450001044058014401041036603000a56507004008080c100307034003e441d000d0040e41d5850904030495003101d0a803800e800700ca01c2544220380c4184090312203d820341c0c070b03980b014081000c21120a03503150101c4840544042040a1191100388118010107000403402802d440c00070701624400d08480192074241e54811141101f8207200441c07444c1c0c0d1142c0041c00f903000c0d0102d40d50031000b0305840300e8144140680c6410448503100c1583d170644044000720324940903503009907940c03504418500c4062144200c80c3e4013424110410029a06 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 647212302 1250 647211052 647211101
    0x5030f0f06121005011806061d0a05040e1f0204051c11030708030304051510051903021504030c12170c0f03070c0303110c010e011b0804120b150105030a 67
    0x189010b200c1d0b80c503c00380503501ea004202c0c0302100c1803a19019414107401344103452030910001c08005918411445c1c070100020000c005540300c0352071070010f00c4003500500101d203a40032050f850350811100c0c1002140c04803c400c00e000da0340e100b11307000d440e00140740040d544415480074680e040000d10889900c072581460704015641001240300828580000359520f02d040e151170b83c01d000394071091240c80c4a400b010b1003442044002040c05488040d01c418842c841d110344030070703920703d0580e1010f500082c2d651083c1c03244107450001002130f280100e060302143c5a960220352152180c0c50741c00380c10b81082014507012041c254004180d10340b09031044980c0660070504103030669020074821250200140c03802c02c00c141c1c00c0b0f25807001101204000d80f160a5500300041c03d00c0c800a980306041060f0650101844482205034040558000981c2501c0e6616502601c1d42161201010b440b0004820000342649205d40144d0b803034000184d4030b950940d00c030b201c0c1100c080d021141015410704801c44990 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 647213552 1250 647212302 647212339
    0x3010b0a0f260307050601030314040501080402010e031e0c0f0d08042106110306010f021b150d0204031109280b18041b0f030503030103080c0102040b0a0206010305060705030f0f06 79
    0x52a085001704060901c40d45585006400c0441280c15028103080501040201d681c000c2000f40d070054081c02d1900803803050000203802d00c070b108024161155284100c050854000080c510000da005446d64078807426660300300000002044d03001840e50100700130a028101c451558030380c0302001880381c00d4000519a88a10a80300c0102e41c4140d00040403040140300d40c2e0012410300100c1541c005486030519010014211200c422180b60040c41c0a07144226804684401c4882c80461750b1000c54480d40c4038500304181d0962108014840d05804001c590b02158903400302c1c502d2207850000920140700030343da42e030240c0448505140e100d4201d6a125000c3d40171440c1c3c0520951040340c11004100d881200310080c83d0a5030002c1c076550039170040c01e00025100000300ca0540b90011011900d959088205030302a01c03e540110501043c08500c0180d11a0001074040c180d910560a13208140e9036003004680130b0001b181c03000d4602d5510400703e07402021070072803036401a0024124000510002114 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 647214802 1250 647213552 647213557
    0xb0c0d1b0804060b1807030b240304150509190804030b040809031506030a060e2b0206070509010e010e0a0b0f1e03070203040e19110903010b0a0f2603 66
    0x40a0201c0c03010340401003000503902c10451a0102121100d92001604a0100c165500104003100b8595200005105551002c0d5415458148411007250130030030000101c40f20b0f001601c0440c1c1020220200074005141406414840c5090340002c1c05a8440300c54081c405010070305c0156510942000040007145010020901c140e0217461500e5842e41e812061600e0100340b00b000c4d4201000a07024084213580115403114034507000035004c640b04800203d01401c280c0760128615010418030101c10050500030901e09103001d145d002c0c0c4525030340b03003a01510140300c1c4403001400500800740c201e02e20740c002c43c615003240101508148880f034407031010340b0003980120788a80305040c5c0400c10a50319006503418021402a1041441c2141800e08010359030f0b021300e00806001401d4000020104140c0340340e4602c51080002d401d00066400244003c442c1e4000c82a0714000c0d400c0c03841b001d03281c0c14101c49603011102e03265060f101c8146012003c89044046808c80c00000b4a18000001c5e9103004001 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 647216052 1250 647214802 647214851
    0x10503041502162112020903011e0b030f19080a0318110a05030304051c17031005040615170903070215090103060609080606100e030318010e0a030b0c0d 67
    0x2c0d41c2e40341000074100411844e0b14104410f110440860f818140194070010303a00c8041e00d440c1c405a2680038560020340900301c48000000c07130400c2c12000c0180c4042d1030b00480c070394200903015200c0c80a944140540c580f403e02c131440f504a424802104000b4100e000149041600b43c03600096503519000c1c5074140c008806401c2d150b000100301c01f00d84600d054051080249030440c02503207011715000c041076609c0c001c1d035003035414100c1ca0810b0701c0502a43d132001c0785003040c6858140f9500d01c0c0c9502c00f15000201e5000341400b0368901140070034007102c440341800b491500c40d15494950382c10000440d01c100710042c100c2e8610b0200b80b18502c0181c50349010300a8180b2070b88401600c1d544010001401c444541e40418100515500c0401c0050400316620381c01c01026100c502c0380748482002660481c040c040f9a98142c0710004a18a0103846100c3d0301c186044240c2c0da0401d496280d1040001420746d03400090030560a61000c42c0d000030182000b4000642143c00110f6007103242034030341155902080 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 647217302 1250 647216052 647216077
    0x14010318050604170c06060d0f02060a090932090c0a090504050f12040b0f130b07060b030c03070501030e1203040309090509010207080403080a0c06050106030903110a11010503041502 80
    0x80030b01c8100204c141340c00142e4840640b685090806600c0010f0f6981c0c40030304400d008005d503490b003000b44503601c580b0503038451700503025035900d48540c000101500d4051040c1c0404515110403083c1d131041103600b48002c801d10341c48003060900311000500021001510031a001d01c07030348600040c3c50b140c1550030401000b00d42d000060500c0d281c01d00c182000034000042d00f080d040900114005000c5805070b9042d40c40c506081610341150701009040391003010360306008141d1140c000545500850000d00446115079414031800103080b0038035607540762841c291641608620418400d5500c280d02c030000da5142c20302160b8402403602d03882042a442524180e002480a100500801c107103402a103400000002c000c516091894407100410300450200a1080c1d03030020b80385c926141f041d41032031152a000001040103507911078000d0010803407954220b000c034001c080d80030544500443c402610b140c019071013924458014004440b2540020411500c000340c0c030300c1d07a140e03803201c510150450b143e044 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 647218552 1250 647217302 647217313
    0x6050f0120011e09030806030a0b0c0a030605040204121203111c091211060f0f010e0a1b020106061d0a0b0702030a080c07030c0902180105030a111c11040f1401031805 73
    0xa04000b0304640b801421f05010798421190540001c00704001194001c48004800761515071021080300508010750000343d00c140082030102c2e80d140c3e500d580c01f07415403181c3d1071501c10440c040010780c181c44a081010844d09003d111090b181c81030034040340340070310a958000a007071105984000c4262000c82c0c03a90002000da19040c0f00d00101005800c0c3c0102c0304907081500da2030a890544000b45050003180040303003c220203d00c0c0ca10003030b009089104907500311070701800c4100e500207000303101911504000413009258201d5440440e645601003180181040707060030f0809408a01c154003c190498251081502181c04110107e0140030301124a10103801d1007807440c1807120084429401000c0046d10400030848040344604c0080f6400c0d60a00300745440365250032001d0018051003140140b003000010310740c0d40492a07144403155245040300308010503c00542c0202d09030085001d14034040030482001d0141c0c000d02c0d540c15001120514010a2440e10119102c0c840c00120404030f0791980032 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 647219802 1250 647218552 647218571
    0x1c1808070914090a12050a030608190c1202010e0904021c1407060509010816110102120a0f020901050f25030806030c030309281d0a06050f0120011e 65
    0x403800b5064002d008080240310403049626200340e8440d58042d54014000001941890700d406074010701d0003810284142d0381100c0c142140611004400b40381190312203503040001c250089010118003000c4d4040c2d40760000c50100c82c0c1813100e07848000d001640d0115002141039480d806924908801c3c51040100402ca80e03e0054083d10b44200b079044801030140500440b500d0340d174020300d43c079808203403c00310503150701000400391159802603001104035400060740c5007000d00b98511550203003002c6941041074042e9011203001f00e02034a01c603203000130420408807420110460291500301c105610480321042d51280d2258520811310b0201c002c10700d5681005664507060020340020720040c0c0c051443c088020002442d401c2014294150380c1120340c2c100318000c11000710b0107000e000801524604440044a200415a4110355071500c281c20400041024102108142c040b4801a114a5002d151100b245c034000c035407840303c102c00c940da6840c28840a5404280c8408401c0c010b2200103075079a40c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 647221052 1250 647219802 647219831
    0x120f0f09030a1a2d06041b0c29010b03150307090501090f06053109030c0b01060201020c0303010504050c0c0d03062d0e0402030a0609080d0e1c18080709 67
    0x20210702c601d03d61440910304c40a8000b01c0021000802400c03c0e05540c1c0e0000006c00620b000240503403816030700141008140c0e0000c46c0802c04500510030150b090442784526420030a40300c0f0010001c2d10302c03400410680c0d007494003558000d04130308282c01c03a085511010074070303003040c5038001d22089071a003004000107201403049500c50b01801030300b07106150421020904c25080352148015104404000c020102840c91017482800c4000c002400040441e04004200c00c080380c0060340c800d8180340002131a140144203c80d42221130740007443c00d40e0300e402c04000c0205001420580000000c10825035620400e221800d200480e039140040d085003000d050301c41d8255a5080c852a0800031080070283e8040e07840410100c84484650340416982c034400b1905010080e20014130003400d1100342410810180b0203800c002d10100c00030031141690342034003603407401d040b85010080e08141d40440c0780e0600c920b030035014a901522010200b00c0d5145100c51400d03995902401039181d0760014604800d0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 647222302 1250 647221052 647221103
    0xc03020a1205030f060603070c0b0601030902040e0d110a1e0c051f030e03121906030206030a091725020a080d0909060504110a05030901090f15060503120f0f09030a 72
    0x40082c6d40490441c80c09102c003501301008010301911086845000400b5a84030703400a0310031603406081845588400c801d06a510400c015a54011030402101070300d004900042c2090703400d0b00403448075000f000800c0b5810024003c604107441a0310a0000810291226442c14030035070b081000346070071213590510040455000201003c01d130f80040003155420301100b141c141d00a41d136400030030408080811074400a1080e54002900801d0120400848d82015480210840e001d600e60440302821a100c00000748076403151003007011114000c40490000701d040c1c1d10f020038400b505100c0d09640b00c1180c04d00c1d1034400080d800006504034001e01c5840e60600807070004005c00d50341032088104550385005103005140c21441000b030f000c00000c03010300e000d40214032165000070f2134455032500e9042140194152040c428456414218000b90302d0034006045ca8108140c80500360501e604800030ba00e056209000700d400a100501089a20344c0d014400303d2540352244060b440440302da4120b00305100d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 647223552 1250 647222302 647222311
    0xa05060907050d0303110d090c0810051905330f0a0303021507020c091e1b04180603020411120106080601050306060f1303060b0301060b03160c03020a1205030f 70
    0x79009840100030903290031042d1010b40e0b500d800c001c6621740140c10140c0c81030142c0700c0394009003410070030f46c0f8081c04441c440d0340050312441c0083c1d03425070034803088010a0f601c050328101c041702c0303100814071034114091b44445d410018142400c1e071107558003c420b421042c0c01017100d01d03034613244003448034403407800c0080f04c07a1454055a401d61614070b580c901944964118144000700100740d800503120034802d00044075040c0d0000c01a003040c0c1480440301c11140b080d170180010001100340802e055604c1842140c500c402c041401514050a11581004500e40c03d90703018103454945001100580d10750080c40700105c85807110584130543d46030707004e05130075041e407184040c80004414000300d640d00c08100ca500040aa861079507d5105100603a02445203220b05c00400106120120402286420a03641c0010440085c4003940e110300004040d8842900c00d114841084210f80190798050404003054500900684041d50320944a0f603418000f40c40c072500000d01c0001c00c02c44030054104007907401 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 647224802 1250 647223552 647223571
    0x70306050d050730080418021303080a050f030108030904050f04050a12050f0a0207090e12030105120f0a0b0402101d12190503070b0a050402130504021503090a0506 72
    0x201c5040d521040d0b1100d10a02510703400ea2001004414264000610440c000380040c0d00c2d00d074068001d0600300d48907001801410480e09840d600702c10103001c0d50080c3c0308461004440701c43e50626643d2190025408030002400b40003040c0f01c621070ba201c03410040c5000f00401e50140d960350302004c08100485400805144005180e0814040460400140c640703e950340304000f140448224001524640a01e0655040786440002e102d0f100f40c1d400305040c1c3c12544440024040c40c212207903460341b51313418540d041035400d909000410541c41c1c010b0130044032010306015660032114458540342040b02c01c135003d5400c501e4070360a000447c00c00307825a041c440100d1405e540070702d1010351444500d080001420b0300c94002c03006000c50f00b4500f4000d2103100f0fa003c00b84180068441e20780302e03450f500103c500386d40d050703590000902d9600040c041c2c0c0740b040b54000c3c403012035403100e4034420004060150050b81c110107484100c1494280d40d200660144062400804241c0c145180c4181782c401c0c020580c0c00b8 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 647226052 1250 647224802 647224819
    0x4060602060415061a071e03020a03170702030f1b03040b130504050106090506280c0318060207150210020f09040b04090803191b17010602030316030203090102160b07030605 76
    0xc801007080c0d5a42c0300f07580c1d0070341465640b20382d400c000491901c070b07007c0000d100000e80000c000701500042c101d40b480307220351282c814503030500503204440e5201b1202c8001580041011814022049000707000603020380c58000303051103c1076035482c076503005500252000540001d0304480e040d2207a0011004081c201e50506ca41d41c103045000b07003003601900c24a030241c500413800f81440c03204c422801d8103400e00b03141c06102c0f80030b83c00c0000f4048030107007a065012039076000f0b403a01c40412200b0004240e4200e900207007015440c03c414114040c0442c4031100440c00b9450410f41d50440d1400108081c041c0841da0716140c26580c2c00304000c40e00f120142c544601c1c6000e01c10000140e003e42900d9110040f64070441003003a000da03501000e4508405d5803c50044000314008000742c106103980e400400040c120b20b0790340c0c0c0300c1005030f80d00d1000351548820024004080d8100a110750010765100d4540f90016052030240d909001300710f08048000c0354400407d40c1000180c41e8180714140c010007088400c00f0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 647227302 1250 647226052 647226059
    0x12250e0a140c1602090a0b0405190b01020a0f023a0c080109020d15090203060903031012080d0903090b0d0b01030e0106030c030b090a050d050705150717150406060206041506 76
    0x40f000a190300138001c0e04031600044c1400c8042d4031011b40b02002400510940c6000c000318840e524101e900d55000750300c0d103030011903103500c00200a0b0f14694080b80c41c48941081c0e8003003010010182c10400c04500c528840b101a4002c45661160140e9541604504506041c54601e00e10880c0e5000700748541e24141500000d0707134614076140c80c80c640010b03442c0310084031355401e0750240c0030f80d4002a42602c10207080c020308180000040d48a200003903c40c01c0100d88454240004000d0480040c04400d0180503c0302a10129408404d0700c4c1d100b030900c00b00c06540d40c10712041507040750a504100070fa4620070350040c2d513054050080f56018040003004650705685e29088884071b1404052300c90350f4008005030072030400300301c220041750b0410112506230070803200003405a0300001086402e801802803440000054904442c0035140d01d0700c0f003070652804801e5403224124004e00d0850140750030440229a92107038450800980281d0340644a00c0c50b1504028540c1c1c4604408110741c1c03440e20700c040 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 647228552 1250 647227302 647227327
    0xa03020708060f070f0c03050c0a050703061406060409020d060f0e040b010b16060e03040902070b0a0e0a0b070f21090606050d02100c06060902040e0f0612250e0a140c 73
    0x90f40328503e00701026040c4140c07c0031a418000d04c00c0c41031140c41000c8812003803100010362102107904c030f520248182c42d00300700c412000e80410b49500d50000d1082c0814402000150058161644100c10000700140d5030180880307441c4240c1d0080380d855400d01d003404240b1640c0c0c00000d01412040780454980384c040c031512051080ea02801400095940a0703050144000b401180c00501c0400000e40d15203100381403502c00c01d5400c1e100040c0c501c0c0340840c1c00d03000c0103000ca56070b841030b0f40020545820f6604e00109854840600240d1401c201c407260f0026507450170076078407000200820b03100082840640c98048101c4c0c0362504054404c030303551034031a8010380c0c52112040b048000b500c0c00201c040e5543c98404090110b513005221090b0000c680880c00350460f00d20a440361140203112885500e80c6418040900940b0b0036140707160300607040c3c1c07490ba4449401000700010840d40000c0c015683c1d02c080303c0b5140030640320700e007103161103183c11b5110000310031610341c00c42049403125150080d0107140 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 647229802 1250 647228552 647228567
    0x61b05071203021c230f0a090807060807090b0d2a02100902130221090a061a0904143c032803020904020a030e100b032d0a03020708060f07 61
    0x4121105c800d0650200307210b0021401c1d62400700d09034260503203c004042c4050500171980c01110301a205007440060f20522480d4414001c0009481c1d00b0609414840c951106501c48808c03485080c0d181ea000441d0100480050b020030070084d50886180d90311040d0007410050344401954841e03041c01a9200580d9031951a807110800040006a039500d2000000580084401100c0c505403000c008100c0c0940f400304034001c01c1449960204043d600c00801c5440c100a5491815000400c1c1400940011380407494124440342a80445881681000300c103140301004040b80103201d00d451002e00580c0d0007407020440c0000400b00034600704250303000e410910340805c0f50741590b00c0403120710003500a80698121843d40c04058010b40d035550074220080c0c0139250444031000c070341c803800d030728241500075501c90300000d1200200500011042002000e100204030400da1400d1000c5089000449104000013020288a0b030041d0001130f1034000142d0420314014051000c08106030708001038503511144 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 647231052 1250 647229802 647229827
    0x609043c06091b030c0509040c0509070504150302040b03040f060b04060605180102010b0108040305130b0408030c0607081303050309100510080d03090c0603051305030a20030901050301061b05071203021c 89
    0xc0b1444595910f04007010503803041c0cad21894100c1c03c020140400254014014400d580714a45800d602540301941107089204501c98807001103801d1011400182c070504100003040c3c001ca0010500b440f0000002e001c55002d46d1000000c1440010300010320100719004001145c0240000c108500c401b40010305120750003003009040100018030011414042a500800b0740304211a5070b0301d858407030034901d40c3ca0740302c01d10350526442104005902e061290b20800d1003054a080d4050848409035000c2d681c0d608060321102080c0605901d82a5200062141d03a100d040d0000d9200c0e5854901000142080f07422840b0104140c1804500307004600742507080703800c58070a490001950ba0b0340c0c1c426181c0d041400b41c0020b04a000001d42d29001c2503002d4280c0d04030403004084801103540f122030841c4d9030310030360900d40c1c0800c80a000400ca41405080c100e03420b40090400c04500840c80d9644600b0a8100d0b0002401c4030410380e048814141d040103148081e000d24601100400c1c404a00072300711209000d03 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 647232302 1250 647231052 647231059
    0x2d0a08010212061c150b0108091c030f0605120d091a040b071110031a010c150b030316080a0905010e0a0e060f030f150609043c06091b030c05 62
    0x100d99140640c40078802c98560485c20f00c16003158008820409000b5041c40307240010100c20220301000e0380865003a5145201079041c2c030140d044010160080c103c0b243c54080419540e034000200ca8580e0303110714110780c408201510703010129090140407240b07a40c20140c0c8202d400030802d00d0019044040307400741c0da494a105601d410b05840c00003112184400c40b00d42007010502ca0340f500030b8041d080300c0107088003000807042c49140c107401121662440e45028103803046c003c5d40303801d68010070ba1222140c1000581581d160100414814640d1040b084c01140c00703540029641c07e13003903400351019020300800d19041810f408114000740344003525001e40b01e000003c0601088803a034420340704070144c00014090310328a56040384440e40382c0010520461400f031000000540900c1c21808252040768000c250a200c1c8610340891035040c002c0c076015141031a42c001080c014030000510002c1081d102d02400300e104512880c2405010890341000701030704120385020700010744880f09440a540e03056 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 647233552 1250 647232302 647232319
    0x40e1603150b061c051503030d090606030507080706020d03022b2d0e0a1509020105040e040605061905060a030209060d020a051e07202d0a0801021206 66
    0x7803040180302e811081503000c8400200c03038000d1620801010403a549010341003065640700c5006a03c0b01e40e14200140c2d0580082210003406141c0c0c0c0d000341c40207402903d001440c0703034913643c82c1840d0400c40d4100380c4a41d03101d100d040103078a50401060380c511015140c00d50a00c0d0301000340300000b03540000180c1c85402d002e42c103600000c401e40e001908940b00c1180000704030941c000c00180c0721780c64049480b6041c1c00c2000b140710744100021000703141980140b401540c1101c240c1c29178010080280300300c6c100302c0f04020020310502840310581c0543d015590000b00c60030000c04001440710307103510121124099a404101669901050f10501c8209040250340c480e1040009416481600c01c90400030b803010945c541e0035070744940507240034040c810824500704203502d03c00c0c443e4001c0c100c0040002424184040740c6030701005400d4114a405000d034800c51522110b8044400000c0c03100514aaa0000340204031307103490441e00e4002e14408008518141c00c1c0c40c5810705446008100601031800c0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 647234802 1250 647233552 647233583
    0xf16090905011e02070c0806070806060f07061103090f0715050913142e06110a0b0106081e0c0301050103050712141b09010c031404030c080606040e1603 67
    0xf0b4120903c102c4a04480a03211120012004002e41040d82c040c0d0b001e860008000c80c40e4070f07000030080d014440ba9182c0072265518002002680d500c04001400d407801c0c140031940004009014124240c6002d0942c50740364504003001a180c8a011085005d0707640c0001c100300400c030001c000c4c0407a280550b00d0320b030341d075009001c02003202003a0441c0a20882c0d40b07003c00c01d01e1001c51949142e030040104048540b10440d08070071030140c00240342403000ca00d03203c4030700400c8894055445114ad90b4101b03000c2e511000240d440c0c10004681c00d90003640881c1c8294104a8003000001c010a104401d400048000381044102c01e4000e000500900d03040c1a601e001048080e401103100c44510b591200052060080c10a26031610500a9031800016540144041e4100c40038601340c42c81040184e41f84406410b41d03440817206602034003814a8042400c1101000bc40c01a035841406003c8140042600f403e01c1310501003143c030405241c41907071f001a2811005034003c03000d031200300c07034000460000f140304 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 647236052 1250 647234802 647234813
    0x2010605120105010305120f0f09130513020111030f070f020f06190e04020c0606040b04060515070209100305190302010213080606040b01020610092f0c0f160909 71
    0x4a90300025401121124428101d6005401443c142e078429402e81c0c100840c441054141405243d1114016400900c07020a41005500152031541c0c001421145800c2c204003c602c02c03103009507800300700b80001008400c2503580010281c4000f000e21802145070818091040d6203c0c001c840c001050165021b98030700555841c0c148100c441d1500406080e652149110241d9032405500036400101d0812003640e4128500388c0700395010000d0601c09001244e1360001004000c1c0640c80c1d0b0320741c3c4035035181d03030220b1940c84500070b14041074040300140e40d44e820140108506050024150500311144032403d2000410120341d621003240c607010369040000d0395280507406801243c070b0f0102e003a1001c507800220220002901c501808068500700551b0a005004989450049035070f01110500b8400410000f15690b2154809000c611041c140c4c10620513541d884078001103034040c0c0e101c2e8000c01e076401d040300103000c861400014440103203949a0360088580040c0c04610408100d540e403003886030f06020 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 647237302 1250 647236052 647236061
    0xa0509060c2e050c09010c080a350a050108070e0417070309140904051c0c0606060f080c03191a04060b040f14030c150f0307051c051302100201 63
    0x540c2c416aa41440700010103501d1900d48000102080740c20704010803101941d060403102c0c8218181c3d10704500c8a01502c44009039031041204004000641c414029030409940101100a0390758155a078540d0b943d0056441000c2c0c0505480c1c1c102d4503200041102500000340c00301147c03082d40418446581d2824111410458810003590f080000500c10040580c000300260540f44001c1c07000c28540741a10600503a10f6040354004c00c1039108400e1183c2503009080d00100d10082490030703030b540070059611082520140c3d445000410a0180441042600100441c5d070020901040501f0741c03401580d940921000d810b94030701303256a18000300c0000d188241d10b1441c8c18401a006000095891203140c0060f40148941c10355000380d007102081030020501038113281702e4010002c7c060b015024081211a50900c4204007000c501005840070700210700d000fa40c85002642c88080d21500d81c41d010b002001c0300800d1020f0050f107008104030b0f00b0400400b80c1500136805449000c0c0d0070f60400f50590040 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 647238552 1250 647237302 647237323
    0x915090408070b0405070329010302010e0d08040b09030f030a05040303030209121501050906040c200304180c0e150d0f0f091b06140417100905010207050706050a0509060c 75
    0x4a0f4076070100028070200041d02400c40c1e120707501d40035503441d1500442040c0c10b10402c030030890803204001040590b00c18008401890001082c8401a83c2c0b03603034a41019a0240c3d1200307a0070b141c046581002803a0501a10702c0031241c0c400994600303403803294000c1440c82036000040c103041d030205411b203158a84000d02c40d00801400200d84003080381c241008001d00c002d02c203542c8240c17030a000141e954149030081118100c5142c0352200d44402400c011004458150100e0180744001d1100050b00a400202c1400c180f45040000038445030260300101045c400c0c81307205000d96000401d860081407039000300c0710342c80795644001071a56030174542840540902c051540519081922800501045441e070b815007101c0092034851082d80c4090030f9881c903042204a5207200003d0008008a00309080b01d84580c418044c1540e041c2c10030607680d102100d1031141d09440c180c0d4003080300010040708010780d102074001824151b090400c0104000e0061091451b4540100f5000c5000e1440d01400c0180d200d00 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 647239802 1250 647238552 647238563
    0x1a010207050a060f02160e0a0f060506070f0512031003110103050f07030203090a0c0603150e0106020d111501060804060f0b210703050a06090b010605042301110d0f030b091509040807 80
    0xb841e47c0d903900301004c643e041c2c2d14200700925045405004c0740140c0b06600c111a40580100c1c00c2400c5078898140000d55018252040c1c01034118909108004000440c400c1e00c2c010b140541c1641542440890183d01d42c0c07800341810702e083e080c403141030003481a43e50301c41d640345405a07880c0d0305c000f02d41b420400c3d00e0314010607006480c0e401199464240d0080705c00b8400260003c40e5442e540c440c0010541703401c0c850f00340903070024600601c486114100318907140a101c400c6585605070007582d602c201400343e0007480001c2d041d500b440704014540c0541c0301c83c1124a40240403110f42c10b8009507203810b02c01702d80b054624003100745603074a51052003000019034104d0240c40214109041901c064980030400719035503142c07440040344150194003a40c0c2074540d42136941d000d80c001c005508030039100e042c0e035680c140050722004986c0700c07600300a1180c040320969644e1054002864000c0c05907030300142c1070392042000300304118041070200302580c81504215043ca2036603c4030f060048140c825a6005480c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 647241052 1250 647239802 647239843
    0x4020102160f080c040b090f0c0705030706021c15140a0906090f060f1206020906040b18040605030d02100903030605030a12090e07080f09070909061a010207050a060f02 74
    0x86041c21039800b1802c5902503019590394507004c008110444201012036640055010042480240d0103c1000e900c03a5002c0500c524048180c0c0701d42d403440c1c01020f03048407180c0d000600410300c1422803900b0480050199001d000441d40b072004609009454000c5080d4400f003000303801100c0c2d50741880480103107140700701007114541b15410000175000030904040c0407414080b000410000804484040b00e611000c01c00c1c81c024a50741e800b0181d4803462402e94081000e000214001c109800100000c215241a070070704150040d0038001500d0302640154440d03008115000940d913004a1040350500c1031060000d44140185030650049c01140c01498241c810602210100079224640392003600c17880d1904031000e503403502c131030511510458501000940500101344c8034103090300503c0c0c0084001060b10015625040d03050110742d440c8105544180d1a0392004601004045240840740004c1c40a0091075040001040c2c5000542c0f03d031104000c9504080b200040c405d001130921958410210309 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 647242302 1250 647241052 647241059
    0xc1005160f0b09070312080702010902060309060a0e0d050906030405010e0d0528090603020a0c02330a0503040f0512071218050a0501050a0302040e090f07090911090402010216 77
    0x1101080014421660b480040c000301e0090600003810000326030380b14031a0048048101c1c0c040300d040002501500a540d29400d00d40b005940c3c0ba0041e40c8104031031401010589001103c00003a0344000c002600c10f50040020f001400b580b0004881e5801016291565a91207a14040b4018001080e00000074020040204c0140781d200d001055002d1009907403a9402020303418520580e400507244001149070190200322441c00798001d41040c02250510604a0110b500818020140c01c0115802d020000043c000c1c03480c40581451882d50071094540d0401c26003003000341042c400030384090002e000303510032401005000c001e00c890360030107913880d40d4172001a441c000445800751002c0300b01140c123450b04403061510342c0304158210341000305071441091401c801510140d00040400c0205902000082410790f580480640980c8046000b45189298640b0b06030410300c5540144403110305140d4840041038a944e4601071040c400c03990000c054072248010b03803400c4c00c0064049448120480b000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 647243552 1250 647242302 647242313
    0x3b03010e0706080a18030c05030d050109020c0f010b0d020103110f0a0503060405180a140114100317040f1a09090703090605060f01021222090b040606030204080c100516 74
    0x72030803030740305031640340c03841c0c8513080c0003000e540002400710506401102ca040c0402e00c944414007800c5d0059094034507216000c50740c081a9034090304010070080e0001068405202d0406c410008000c948008014002101000a142c0d520050000c1e04050303c41c40c400c80311000950440f101f0310286482540d13105a140e10140081d0002c4070528803891030040041c000c40741ca07040b03001c6580b910001510355800f0a968400813140c010780741d040a0743d650450080c1c1240d4544c0c40a010704407c021209034289549402100700000340c10540080c5002d0000b040b6200350150a0410744110103038151b80d4015103500685a401610b4503242e010f1440d0707003031020322901540075134280c0380241401c1c80345036200e03000d001548481005aa0040e4820071010314115450300c09483d0840100000741d40e04c42c00007405103c5059980c03c4000001d80c0ca24841c2d12a2406100b18802400036090070341c102864804516140c1803001c0d030160003800d4200f80c2c2400300d8803490841d00c400c224000140c40b081c5c454180f1 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 647244802 1250 647243552 647243563
    0x708070324050112060e031b0601030c140303040b090102151905070f020d050d09080304120810030f020609012706030609090206252306073b03010e 65
    0x41c021092255000c0700d12200c040c054075058512007024004e8a15141d40c0d003000900300180644594003051000202036076030340b8040c40440007010014981035045041007010000c0070780c4242c1c001c00007a505c0500f0b90f240131065400b200d844040c100c0c3c48000300c0300149d0404030350a0009103218011010042c6c000c407180040a0303240c0c2400c104100a0781d4010040d9400c0c21250450300150b4414210044068801c000174840ca203400c50010540b82070588d00c1d00d1045d041610120f032a8814651070011540e031081c1d555600032500c541d40150280344d45c5541c1126558640080c0c0200070005415403280d0040212000545007020a1b001d6410015039003040240c142c0900c00020381001800580031055000e4200394580082c0164640002034020802e445207070380501c2920603400c060040821031180034400c4c0e00b03603c4500c0d010038103a504411424004010403c40511180c4003002000b0050365a0070100c0c030032064408103490050158004812001241d550b50542c00d110b02e401141001281 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 647246052 1250 647244802 647244833
    0x8030a14180d030605010509040b12031605160f050d051e071d060906120a06090303090308010b13140303161a1806040f06020904020d0605010f03021305060a0207080703 74
    0x141c03102114a02c8089041d82ea4502c60701e4001502407101e4809454030b13074406001100000d00c141003030045000501d0841d04116284140c1344606490031061040a1160f1644600c1244182d12810300300401544003151501415004004200c1804104903040040c8140c9228407025108440100340450f5501c109501a507144911034007080d41d01000e0a0b484240a0800103022040d070342c0c0d03254288225100300e201e100e5005d11540c0142d10115040f44a9a24a41d010fa64045a14806420042e0026034180e000c0070700305008100b100c00000143c00c8039400d82d0712001444000d0301203000002e1641c02501030600c1140340e0341c058102001044618040e25005035085008269203c0d078ad00e80030f000c01085858450780143e40040c002482c1d101e8036844451090310b0040c10600ca440106007241c214210307074205035985500900072582c11842c0000c060302035282c25494820b42ea00e940d01045800d1066600806010601200250081c8021009842c00c0011103444594a06002041002114 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 647247302 1250 647246052 647246101
    0x302070e04080706240b120604230f011d04051c02251d04050a0303050a1409060f0a1107062f0a111501061805030d020f0c040203090a08030a14 63
    0x242e0001d02042c0b4101507604001049180c11b8071543d030230050001401902c00300062003006c00d43e001d810900646c4c0b4603405842c406038090455070400d00b002403148911074500b1000034107a810000020800540707104140d140025a1045c618203000c240e1030001e100400c948030180c01c1c1c11082092691492a0040300c81800400d5070341c1c0f10a040710035150380d0039203025100303410030600100030034001e410050b040111500009550b05801100b00d00b440010790301d840a6400a00507c8000f00601440c603411110b8200200701c594071029842605120707030140103004035106c200b4260320103003940c4900c8450800e1813803000002e48031000c030b04840d4064228200801d80411900c00c94000010340c800051142e503220012507428008241c8007400354500c02841d0503401c1c040815035032818800d1040201d850340040113400d10540c5074034205014102c1c0ea60103940b0520030000d2182000030000038103a0403144c400e650b51140880c040181400106246017024800207100001014817a544406880d20 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 647248552 1250 647247302 647247371
    0xf0c15180106150c021207080a0c030b090114060f0a030204050c0918091e1f060501020d050909060607021903030c110301051e07090504060308041a04030302070e04080706 75
    0x1e0f0382c074180038081d02403440300003910009010b00505058003000d41c228030120889030b0060351034003450b16045907250215000e5030031001c1017040101e084200c075080940b1a0080c0241210003103c000441d00c007c14032403160b09034400d6483e803916403010840186402030418030480c54181510035040d40a8001d5500481840b40728001c0c240b81c059001d4047d2032240b010b401c181c50340c68000881e40320420b8801c180d901401c000c06c40b40080c060300c4403081028050300410024035180002e4140900024a207007030150820072805035039214a589903110904440403601d54803540080f07081c00403807840303c181040c81c2501c007006068201c0781c25010a445a003c0320140c455000505007612416104041d00400001c0494100100c100000f6405041d0380380104110360b54000090139a00c46030700c160348004000406001d00e02081d134540d9107088100783c456141034510b41e00207503204c0880c403598090000080c08075040129680484000d603400030402d201801c0340690a045a010038120a10b103503d10 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 647249802 1250 647248552 647248559
    0x6010905100506271206040c150e010e121e01060e0c0712030507111203061504030b01090b0607020d150e010501080c060c100612060b0103050105060f0c15180106 71
    0x89040b03d00d05800244030162404d0000040000f8480c005003450707000c0c40060100c4c0c80c100c41000440c1c4a103000d082602003c1d460100c0c55500e0394042e403040700400030b40b481c0ca01c07400e03604440700e0814858159580411340070081030b803904007103101c01c0798000031000c240c5260310000f0540145050380c411030986a40c548600590410358454000000c00c2c10704030421100c400c078000d40c400d6a12060901304414180700c00380d261410503aa00411003c0c1500c08028001181040320310b800306c420442c402c07146030500b1902c6110782001c0511600b0422038135020624400d46810b41074034400c541c09010340802d8222031400d8004008081c40400c0c18501e03144006101d4401400340364125140c4001030080c186060f0b00b070180715804002e211689100390502800c40f414584a01c400401c036004541003589500e01c0c1c0401034400303080d58241010304080041c0400c2d510041182d540b030b0f4403001c145503619100300765903040c40e407803016041c1c1c0035081c0070030424524840c41c5c001c189040d10b503008002240c1c5 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 647251052 1250 647249802 647249809
    0x231e12130c120201090504020304031413091409030717070804090f0b01090b03160309020918060a0203070f0c06090611090f0301090f080c16080a061109031b040e060109051005 77
    0x2d002c003034009002c5010400007400c040c1c0c02190001c0c0203142c00b0036070391004c06200c0a181c0c0191401003072403001100c01c10806402c1d200d243c000500c0c0796065005400c1010645540f402200c5024204c8940c1c0c0310390400c03c2180380c003100d0050740d110035496111592107e08000070644030550542d070600b02100b060b59036204160002c192013012842c107056440700713000d4401100c0111010014980e4490400b000345e07885001c1c25204445c00070085282c0358016034400c0c00d01001030556030616005106103d0600c0d0024051400d9000e1481e05001d98000c500386180070340a030500c054289880c0240c60340c202080c50004064004042d0740240c0640400e400b814200c41d00d0110107440e560740c140315940007032a02c1004201111140702120038080d008400303207898085540c0000d013a03600640d0884100901d80c003a103040d06840728801c5041c00c00010101e03484071952501c1803000460210031502c2599a980070903400e404000c110390b1558cc591046400070300c4155022401c0115100c0000741074603 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 647252302 1250 647251052 647251079
    0x3120e04091502030a06030204020705010203070927050c0417010b01021e2113061101110909070c170f220308040608090a0212010c231e12130c 63
    0x394000720340b02c02002c4410818000b500041d25520201d40c48210000c003507950303030018000303041c004d030001a500c0c01d04540c050140c540d194841407580c0040310304001c00c410102031082280d0903203500450141d5441e10b168207940310f15081102d800840c08040c4c48180015440614500070a800b109c6c8a0040500c01052403c0201e0480040780d00c4440403885090ba2402e000303108000402200e418100d1060203035400e07610303035080301c800142803400c1114950001d018801104010b0f0013124580044040800c2c04403600900c64418440c80758256010802e203001d01c054110740703071703035205480d44900a581c11641d80030007550404003d4903515000500b40c0c004e01c10007200c2d4400903603481d04c0c0c5452019940b40c0002440300c5074074006c840f881300240c9c40d486000800d401c0c88400002c2c543c0f2042c0c0d400352094008150410708000413054010426407401e04542004c41402c2d0840c540340900b50b85c400301481000c00c00401081040f05204074101c0d51500180407911610700b4500d895151101002500e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 647253552 1250 647252302 647252321
    0xb0a05030a030302160821011208070f020112180203070e01060e10020f0109120315052407061a01120c0f0f0c051e0c0d080307030b01090f03120e04 65
    0x1500180720140010b402a4000c0500310100711303854004811944074000303181c0080e040c801c580800341002180e55581e4424403070141c8009409110614030030b40303c1100b50b014114008018a4442134140c05681c050040310319882a40e04090000c4044c1e5011650720206a4034200c0c000d2107243c00c00306a5482d0000031605941003a40e4070a60900b4440c1080108a03202c0148002d42c0903c809600d0690380a015012080c0d004081007105a404c2800c01000c880099054410004206c03000380b05030303560f1000880c0d0500c2c01035083c0380c0700340c4410314070785045c483c6c3c901c01481e0524117842c400c0ca44012000320300034801c3c01d803540c82d03d00790209200c2c01514480c000c0e0400040d4000c070a460386a004c2c0b4404c88007111a8940201c00d10342c0741e59078500d031181045030001d0742d207d03528062840d900c08214907110b440c0300340c4513242d4402d030329540c019044c00b01400303102c10705450ba103c410701c0c1d0b4810100700b0014030070301d807110980b41d40c2c0e824103100d82818120540002002c45a04034401d003402d0082040c003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 647254802 1250 647253552 647253559
    0xf0b07031e1a090c09151b01021c2d02040f1d060901120b07090e0906010f060906120209030102280f0c02030c01140c03070302010e060f060a0902030405070b07060f0b0a05 75
    0x90600c40e6040106e01410f200c818006400144013140f4944c0b030140d440310039448840b000680e201190203c21521100d440482c240e07581c145000b409860f404444208040000c0030603007011411200c0311f900281c084c0d40c0102ea49920a00c000003100130038060034000c480d422400d4025142c803550300380691040c00740035400e010f940554004000070984014550b10a00504e407485010791100e08070f0518040503940a4400d9111000511640d240852590000d00c034a007084560310746010000381c980d09102c500d4484072980850000043e0f00e0039012a50410b442c010b592000a4590030b1030060440144040e034005541200c41c0c440c003c1c02134040403040c540040040120b00c10107801190070002c0710469401e0802c2c140500f0030303410000c002615016100360000710704058050300ca00c0c68a20001c0007601c080c6501c2c0207218a50f10f0b45c0c1b46074025156009405aa66600c03130800d241b0f000c4095001440007000040c0000c00c1c06002c1e8007800600003021800e000c1c214040c03040203030320f400e5405003a60 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 647256052 1250 647254802 647254807
    0x909010e270a0c080f0c0109140409080d0606021516050409020904090c060e0102060f1302130b060304150b1509010c1406010602010c18030f0b07031e1a090c 69
    0x1400e40800c080c034190341c5015000c0380c0401240360b036039121008084d0301580c41c903031140117245e202e6030060041e6910160f0a00e403400344a0f25101298082040442c54940115954040041888080c500700e5112040e192424400c00b651004001c1d9159814500044070702c1c5402e001c03600b1222421001d6107a8007283d40c4e0541070a003030207400c0c002940311039400c41e8025a50010f80b0005400a0f290b4001401c440c0c40d4107081c2d01102001a04118000b0100400640248200100904801c00000c510b9406030740005903c00c0201c80300c03008040c1d03004202ea101c840030007040100900100036180f29051f04000b40b2400308907006001005030011466a841c4100340306103074003940714404031401640159031202c00e8600440740c4a0a004d420707000000183d440385101c04c0700640060401c4900c00301d198081902900e1521403205009041100514035101400800e0b41a48683c000c10b51821307102e0454103818000c01040c1c4010880c1041030203a03500d82420804003850100c4032144a003900c909060f2 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 647257302 1250 647256052 647256091
    0x306011212080a18150b0910120305280e030a050606091e130b16021c09090507020703060e0712020607170304060207050106050d02010c0605071b05030909010e 70
    0x550812004041c41c41190352600c02c0541e0122207488040014042c20700404401042c000175402c1e260700c180c03814090b41100c0c00740000b149009061200b1550402c42002004410b407030100d544e4402ea0a080080300c280c0e07a80c010301805d801524541c106043c2d25202c0071620081b050644130700c1d501d00c029003503400c1940010014180121810f51220102000070b4140140c1c80d0142c1444000740e85c05204000d00c28140002c011403428000d801401c101246203a1041000000355201c2c0c07404a0380e05003100c9079005005c41400350030518082c00007540e050000c0e00d400d000c001d540d080b03280702c240e13a6142030002890209501145410a50b4862074440f10a601d0b9134081c00860307804803070216071881d005c184443d0320700c2c4400301841c0524813506025075100c0160a145084d07d2040d00a90320503600c15081c400141e800540314880c1c294441008602c90740c551009496806819810640440c2140b202408001c0088001e040140f02200c003070001380d80f10001d00188a80072170b00c107025000c5128200707 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 647258552 1250 647257302 647257307
    0x1b081e01030b160318030210110c03030408070c030f050a0203070e01050a0603020c0c09040f1b0b070b0a152c090309060711060d060602010b090601051b070e040305090306011212 78
    0x203d03403800d100d05000c160f070300512209081e407000241058006070040049440d2402841c050700f50807984040e111414070307030a40f841c1c03600c0e03201c0504000e00007400050100704101c0144c08980085030000c0c280260318070700b0304007503880d48000901280700f4050070402059181d000000c1c0f074182c4c0d01c094241461241414404d900941c0080107003c0c040c400d02c850008150f1b00e00031a284114424200c40c0300c2440d2502e882030302507000c50305c884e601820170002800354600180c281c444d22034104080d1469502c681007458020484644400e2120441c03003004640d107004809460668401e00743c5580580046480b5500546029103074030701d0395041000014010b14114020308052405030b44100c8040911070700140322a80000d01100c3c0070f80e25120b08102036902845100000340d01a00da034441480e008000070414443d00c0086040d1000e82c49498002020800605000d8030100469050070b0801c0d09000d4401d4000000e0b042c464828840041420b001c0410700d91101640950045051108040107 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 647259802 1250 647258552 647258581
    0x910030b0712090501110705121204230105010602060610080f04081e190305090c18090f0102030c130f030804060f1b0b01080d0c0c181b081e01030b 65
    0x140360b5001e45511075080030580030300c107a00f40402c00102c907d94400462500e182006044503032208603682c1440682c0380845640c140c1c80c3d01030f62249416401050a040401034000d031720382d01c1e0025602e000f0001c103070300341c00141081c05490203c40100d02c032003004004458242003154071984d01030190b00468001070350400506003110700040d402100040104040c00b168210710111800e41d07003280340c55000c4a13018490a40c0150745000501005085c0b07201085c58148280c903602c40d0243e46200003418082c003800b00c00011aa41c230000d540d01d007840d072004581c6400c0802110443c1d0720006c00002e54211050300e003000c50358071204450501e4509002502c3c54004010030000b4043d003042c640c00c2075601c01103074030700d194850000e0150b90350500624502d00301d0407501d8170080c1318100010b1800304140f00d0b8060201c1c0d180c07a00044250f044806200c0103407030794080c80e03641e0702c41d5071340c120b40690341000030300d4070650361200a88030b50720a40d144202c0f014401e03c000b404080c7c121000c9615004012b04 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 647261052 1250 647259802 647259827
    0x2030912010605030a081c02090d020d0303020f0a031a06030906181f05090601050301021314030712140d020c0f010e0f10091e0f15030e0313050910030b07 68
    0x242c031641d1040420309000480b44211381c042000a0381e030850b58450000c96105c0341c1c6808003103051040d0000814034460781c01c0001381c80355a035a181d00e01090310a404448100c21040c0003e03485000039007025015041e1404585940c0b000e00001500500b8590196441420000003e240310b8486001c0c3c0c00b481c03603000d03558803594011100700d24103c0085241410f5106520034000070f0034a803501d6614144141030304540d20a134010001c6c440d46070701c922000710075250003100c40c034020091240000d20f0044035501c031010042481c4c0000d0f0a0101103083c400488418100b95102c120041c0341c126181c005141140780d00c1503001400700e4003548280301041d0807140252501c5204a014400200e400000d03032030400003c2d0400c0d6042c00600d0403259610100700c45204403007101401c0030206009400325006803407030790103c2200e10100a200c1e0b00504078440035141a6945c5100480e8070f80d2004407070307015490184041c2808aa210f0003040364807000c0329080b61003101e072921450b1045814055280c07 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 647262302 1250 647261052 647261089
    0x24050304050c030a0b06130507020c12100507020d02060a06030b150105120c0a0e0906090c0a09030f051c050909060f01030f2306150f09010309140d091401020309 71
    0x50b0749261502d00700805003505000e4191780016140850401c01407011003091110a41d00702130074840706580000f1038000a075000c450000814110031565482c00048440c000c5186041006000c8610303004100c641490f5500d50030355407107542e801900e4007580c03403510000f00031480c4503001441c036640100c641205698145000c602d402c1611490004144040e58034460030301001585800c07203500722004683e040e5003500c52031b203980f40401c00281d104500804850020000103000d2074002c0c417541540000e0b642c022007011034407000e403c0641c1c1d580c00082181d11131001c8a0399594400c0e008801b51840820000d00310102c1d0761307031380051002c0402001e01c49818540c4a10021a50130300710700807440e8404100d508a03229158010075924901c1011701a240079080111211a400810100721684140c504d01115502c0355542d004900402c030200010740306480074000d14811010100d00e1100a0510b584c40d0b0b040142c8810200b14210340724101140564410000c0c03c6044c1001450142c0542018 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 647263552 1250 647262302 647262313
    0x1810050706020703170a11090607050c060408150a11180102030904090f060b040903090909050a0c090f060501030204050d0204050c1207020a03180302010e1216080f01062405030405 79
    0x181e80d4002660052542280031400c5030003508400c02c0d0350081360b035110761940400d11100300d080d004000280710b03d0038000d0081c0320026007c400d010041141005540014043c55034442d5606889510f41035103040302500d5001074004605600100d0240302071400962a02e00e240a04600300303240903140542c0e48a066020501c4036102070b03500c9101da02806405440d0080c0b1440c3c00b881e102042b42e241c8460244501c0c98141c501012a03030209080e0706492038101c0024101440307007440c0d460240c2755900100010341202c3d020505801c0f940020700321a906000c188600c030b46903001507050f40103502071141c00142c4020304401520702900945d4005100b80400c2d40313041c8210195107031142003203075880003585c44065210109a40120b179041546050001e03410b006003103034002485180310f51105407040c154210b000611231414419030418224145c40340600f80d6a850401d600c0b03586140040c00365500c2c5c00d500240c186188021440710b0001d050b04019013008001c01600c0c540c0000e4010344d00c600ca80d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 647264802 1250 647263552 647263567
    0x140318040b220e07170c04061d1005040207060605090907270e0118030f030b1f050c0d030c09090e070509040c0f030804031103010219080a0e0729181005 67
    0x24050480a00085e03451094402824a4442d00d011603c40c82d03580034514000080000354004d284600b00e0041d01e0305510025221403035512001061500100c2c2c1c07181c400141c14082010681c00041285d4043d0360312105551401e078817640300c82852090140e01140e0380d1703000f00320103a2114044800f0f00c01003400500d188410950301e00711100d0208106888685030031900c00e050300407101107662180d61a052000d00d5203040800c0d0000304107118031600c001d106c1701001c01140250306640a10364401d040320012503294174001c0162599000e00000b003943d01001064048140c040c0e0061040d8801c0101101f0b440c2809001c407612005009440f14003020001240640404402000440c000c2c00542c0d111800e500301010040c9000c41d005200761f20400590755000d0aa08180b100e114290402240c281e55441c840c0000e000401c062062500880303001003140d41c5240220300040d0700d5016950560810951034419500c10049814075078030105a0030710ba0340c03400390700b54843c6900d07518000d81403086 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 647266052 1250 647264802 647264831
    0xe150306240109080a060e120a0c110a0306051024091203020c120c0a0605041206051503031b0114100b030a090606150e0102030405130203090703140318040b22 70
    0x221000200e40807030700c7d070300c1001400100308041d1101c07201d42207180740f4195002c0005030030228081001004000c4010401a580d0388000c41b43c0700558000106000c4c03440c00075000c1c0c0d4980c00714000c80100c4103840b044c0441041c0080d00a1758050060b4854481241c10b00705000d232101c2c11410100c086114201110f20161074407000c501e02d050164000300300c202080c90401101d8074060300074108004040c07100700080c00ba03a121a014041c5c02203030000755601e41032000c0001d42d2040452542600c00000da14032452201c0d100701d01d42d2145c410007000451280d07064010181c41c255911a104644020180100f010940040d6000b5403488000200e098aa40c0c0d01e0f4183c0b200c40e0320210b10303903501c00b50002540340c02444401002409101440c42c2034100000184445200380146481a9012000600e21101049218042c1d034102c1100401022108a855560f901901202003da42d899110410f2810030f409480c1d1820303170040041080703000b440340203100c0307403080f44655170900e81320a50b0854005 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 647267302 1250 647266052 647266063
    0x403141c02151303090303030506030f0f0304050f040204050904080d021315020c01090e01120302030c0f0706110a0b0c0d0209040504080c010608120301062006010e15030624010908 79
    0x120640160003000884041405003010003010303d51008815060080000c0d400358a1100703880e0b2506000540d51208408281303000d4011001b00000c0c42081c1c64140e1403100000548119041190000700140d808814001a4001c0f442101e4021740501c020400141009014128032600440010b0030140246c0000701085500c0d8801c00c107943c0c01c000704628066040c4441c00104000b0300b000864285811002e9180074014070900d0040e0302c0265421b0100f510a20840c0c8481030200704451106c580501240e8032404948604d00c041140960740e8840d4000100d00a10031a400002c1205107954000908074a9400012031300d07105035003003041c445143ea603131190f40d00480c0920702240d01c40c03000f0070003682103600d550450503d69100c060350303d10103240384023141e066414900d00645010303580c00d5015891190b104107070215018010011403544014603c151299040050720328440407000140354803040250303001d01100c3c900440410700a4240905c60f5200481850988041555030440c01d0402c0c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 647268552 1250 647267302 647267353
    0xa08030408030a1b23120a02040905061801050904020619030b03011505210f0f0307060b060f030a1a0d1103060105030d170a061208090123040314 64
    0x10348010041c440981140d00c01c000304240403440707904e040c1031940c0001d014880d03c29940122010003800d5843d4842550f000e445524901c10510849810594288006500580501180c003450180010041c0c6041c025034100700c1450b11000500703034203203014806d125a0003031090307070050350400002075820201e81e180070320341e0915600001c1003401001010300392468005400400c0418400511813540d48003100e03000450323010500102010302c2c040842c101000c415520201d03015000040300e00c0c05002c00200f42d214820a0300f00100324842e41000800e01450755000003008041c07002038160b0009a21200c00003c8000420103041800400503803070285071201181d9001404141b46a142030410450b80508002c9010300802201144028900107056102c003880c0080c0d40040b80074505a5070162018040e594021700038038605040c64038041e841a0a298002b074030030805460341042140507828805c9040ca100d918062075074850611044101000d04458098403001c24081c5a00e40c90b0002d02 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 647269802 1250 647268552 647268563
    0x615020102070c0e09030d0f0f0627061512060305010f020904050c090f060a0909090819020c030316060e0307111e0114030a0b09010b1b0705100f020a080304 69
    0x48100b2440d0000c0a40699801505400381040c240135940c2d02c0031003582ca80415804000907501c403e00d03480f90190520f140c80310000c51405201150800b40d00c8002c04498128a500c1e13030668110034515001c9844074802c0c080818004903c00300c0c5981300d26450b5080300f040368800304160343c40e5202d071821111140f40010f00f00e9030000d8070300201d040074020103511449003050241488100d00104500a10110b42d051282400144410005000304584000b4100c2c0301c4041141c5001c80c540a5995440700380d068100d0254091008821403000070020b140c40c0005d40a1030034040015100150382c00c0222040f17403110f46407610350103031803410005040310602660100b030141e0000c03020b00061420700605d035000820402c0700c03c11640d8003c03005c02a040c1e9101c02495403651811508001080c902d006603520140c1480006040b0304040080d0400700180705443c07100b5490b4410301540c0e61001d00c5513940103140000303010509800390076030694000140c015241c03084002d81ea90245580200c5040341c1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 647271052 1250 647269802 647269807
    0x9050408090a060f0906030902030706050310170307030e03030c120a050c0114070e1e06071104020a0c02030d11250806010303090e0c030606121005100309020907090e0a0e010615020102 81
    0x1081d0b001c51164006c001030f0a0411052100e50040703510351a05001e500c05020000020450f15402c0080c5080240302c40341240c070a20f50340200e52912039000000607000100102d07c0080140b501100f290f07200b5404d4001041034101001c40214540c0142c40580c0511806003c651480301d801e0090b1120041400d0403000d451400c103402906480c109814180244582c40d51082c400e0740e42e410041002c0c0d0225519520340425191120070405580c2c5031a82190011503021801d90b005050700000314800c409455821100c68404c8480d003a90702000d510300d501c4141e180c81d0350f40008204850184546481c3e0701d00310385900304c851400d5030a910031000038000c0d0201700041c80c00f0107146030300180b56106152441c102140092041c5c000d540e0100c03112444100424070740b02038200d49000400014001e400701b1030719400098010440e803001070740144001c4000410301485050360f03005455100e401c0008680700c40e000f05009100c0fa004000d046c0d03584980100300b0102d000400640c4048550000d81e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 647272302 1250 647271052 647271077
    0x70e011505030702210d020c06040c0b090604050d0510140106091d01051003140a0b12010203040803162307110f03120f1201080c0a1a0409050408090a06 67
    0x3850210341250910401c40c0a009200003140e010031074004e980c12400c4a041c1c800c0b00a9902c86461040c4003091030b0481c0300044020030f129000c10068400d50080310a900d03101c2c1d60782c54080c414410749540551100c802c20040c8960700d86440050300c0d4030300441c01c82c0c040440162424045075080300b15401d0401180700100000c5902440c0319025004440350f60b0400a801c0720621580d20043c01054850b0080464030b0312800c0c802d074009100605c01c452800726904100120b08020407405682c80c0c050001c400c160310040a05000303c0740034644c446581ca00d16900d080541211100d002045001c01800350b84c01c0c03212081141c1041c0203c0001d42c0040d070b4882c01441c0005042c0c2e00c20320814021070719410301c400c0d5950089002d040c0c0384002915140d41c2ea0002c000d010300ca200e00501c444507041d45000104860500003003803420b2820588003428820703103d00c92991034000e541648043d03050204420f100c0c071031a40d040716030014840c0103002e0a1005440000b01e06140d540c02c54070002d1703079900e00710 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 647273552 1250 647272302 647272319
    0x6050d080c2434090609050906030309010e031207051b010305060306041b050303040308090306090304231c03030c080c0901080103080906070f11240a0f11070e01 71
    0x3500750410041401a111007400c40702e001440006102d10b0720161445001654480c0c4256040095141404200c8244000000150142940b400b8680008104c2c000c041500d0604c24001802510020011400e000740f50740112143c2d070450510b2600f60044020440541c05d07500041c1103100e105030003410b1503401c9a0181d40480c40c102c4816070425040c1001e11015450109a6a0700b143e00800000c43c602d00c144c000080c100c5e1540e0142d0381610002400105010040001d05415502201500c0103502e4102c05903540c1c1c06240141d0504070003000300e041c4c020020713202c04102ea10018110026803820762440488189400d00b00b940881e486071403854130b03503911250480c0c0c00241102003030b081154000000348500e505000080c400342000034030f900c1680c0d8000c00d4580160b8010b0354a082150913250540100c2009841540250340d0800800c0e4801d20040000c820320080c0c0c0c1c0002d04240c0d888404070f4005841860440500c98013100403603181800303100d0400602080707074200c607855241c00c114 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 647274802 1250 647273552 647273563
    0x604050109150b1309020a05031f0509070b0d020a0306050d11040c050a020d0c1103070821030105130f060323060604050c30161b03140d06050d080c 65
    0x4094070b03a807809950f100165640390a00443d10540c80000419413086d00c0811000c4401e0b8000740c0c0d06200391f40c0f044e4101291a412012a080c5254003405285c86103c07015a42d01c17054001c407480b0403000d1000850740c80d0240c0c041d00780b0448504c4c011501c20b035200e0101301040610300041d01c040c1c6d80701c0142c1c0c6080c04d1078003a00d076062000307140091421078282d10094803000f4008115007041040c401c42c034140201c0c50001c80300304000800340e0303c100d640c9502d17040da81c2a20501400c031590a040c03000e41c078002e81e0f4050740c2c101c0e480075102c13101204189031403800072f1030003401c40701110360382e14004000314000030103150594410010500780d44046000030791401400900242c45035040000304550003860703074240c0d03181c0c1c60700c0c203820520b134a031484181c039004425400102140b0181020002d588402215070f5a0020343d50721003a240710354080b11070340d080749621005404582d200b491906021003e200520781c10b080007200044551303c9100103000c00f404010140d130102c1d4041201001c44406014 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 647276052 1250 647274802 647274833
    0x80409050126030307180b041215110904020703030e010504080a4805120a080601080420030a02060d02090306010f0e0411010c0f030906080c0c0709021b0604050109 72
    0xe801d1010400c00c0e00c070b103035a0710005000074100071901462152114442e00e01e100030304100c01480f070b00d4035141c50b9000b20030303c007500c000e030b81000482821048a210320b1154541c00525a8034545c41c003190001808003035440b1003401c8040540d00c0d40340349000b81081c401c5501552054040603078070400c1000082651042d00500c0c45404007540701c0311043c0c03170203040c15040f203000070f4042c10542030b9280413500c212840075400384ca94050b0a84204a9504d080c005001a40c010348400016441e03040c01129084001c54005190301c0401400c605510302140004074901002000c9400d44040ea6011414507004002c51691040e004180031140b4070b000d2002501524440035803600f0b10345005100103014001410182115107444000403c1d64828130260248903005001155000414640189070360312921070070000035005400b040502d003c0000712200240a08020142d250400785414000c6d48070b0400143c0c0b14801101d4042c8200091040c03500ca00e0058000180c004914200301d1000c012000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 647277302 1250 647276052 647276099
    0x6090d0f2a050d111c030c0c0b09031b22020c07120c0603091b0b13090506010f081306140702070f0b0a05070c23011b050601051302070804090501 64
    0x50741071103140c0b40c80310543c42c00d035003180601d6401c0100704042820351820050445282202c54035030410700d41c01c5400c0e1401c451080c2e5201c01c0c6680d843c60411480c2c05296290342e23154210b40000d2400c4144910503130900c0c00000c1440c5070484461611402d614449030301d03c01d0300394010514421961062184d40000d20764140190b070b00d12800e5603030b901d007001280207400030725a890101d9410b00c80d0001e014040e0201001d044d4003240d84070603140701c080d0484200028203603620000460f0815140c042c0760302906041c0c613a10b403003000b42c0d401039440701401404003c100290250705000300f1003d000e0340b9140f0b485038401c9055414401002402c0c80f071030f80c02c20300c0900720916041107101c841208541d8108110300e4856151503080c644500500b003503500c00291484084445030164000c845822041c0c142602e84656814202c881c003156100001809041e5400400040040741454502500742c43c0010100516242a55560001e540c10940090342801d0340c600051000e1000031001c0c9419156aa = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 647278552 1250 647277302 647277383
    0x203150909121e090d060603051009031d03010b030d051b0307020102100209040b03070e150f03120304020d1a150306100911040b0c0607140a090506090d0f 68
    0x5402c00040c0e01c2003d01010161580411000004840e00b040d55a00340300100450f092882a040003809001d040c00203540760b0040c1001070034070260911a10400b9585512035070001780400b031009400f4001156160307015501c495407945207a4040c07021043d91500342e00c4140e1103096414039074540302c2400e03084500c258010072100300542e8000600110710741c4410070159881d1164004200603000501041d500f5118401003c03500708883c0c40014455440500c0700200c5d00042420000040f01410106130150044072181c1084a1800000e50b4424009170030881080020f80c0ca1200486c554880c000d0384103d80000c0c0051000d544044c41240c1a0842c010100c6003403103800046601c07803511600c41101e41d20340c1d60074501c654420980d27009000d03400d1480c2c0c0360460310391181c1c0c40f501d0881b070000002d24002940c0e11080442825110081801c5c1e0760fa610305030806083c044242e000d00f040b031780d0002d504601900092070a54580c484c25108002c08881100d00d101e0700f030200c2030b00c060070808041c600c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 647279802 1250 647278552 647278573
    0x50d0504080c09060a080d21090c121b0e0411010e210708012a02010603051b1503090a060c09050f0d080c03271f05030a0b040203150909 60
    0x1045a4030120031141d02d0840d80721240000d1a07085c0c240c1c050b403010702502d01125051034011407032410901c54a1004404001303400c8146c4216210507000801e000224036007030001c0c101c20321200c546076100c0e81291449541c0b0180040b503e405c0d9030701080007500708030100410040e40d0001034002c15420709200c40030000340c40005911aa11801d1403a0061100c1c600c08000801001904002c00609008002c07005512824031200100c42c13000404a0b03002c40d07514003500e481442080201c03070b000805401032401c09001d440350161501d1403664424903038088e0100c6680f50000660044007500c00030b1442101070728001003030302d140c40c404000340002c8610820241c0c071170145a14080301e0031101581b11010504e0f11100d50300441d042050140700118505004000c807040c202050030146258000c1d1200c0b501c10088141428101840e16091081c1184152805040510b8100c0f21700400801c43c2c24040300801c040740c208071510406900c0c159008101410801d0300a03400180340806000003204 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 647281052 1250 647279802 647279819
    0x807050301060e04060b0a15030209040b09040c031b180608100e06161b05010c110d020316110d061e05090c060702011205070512010605280306050402040e04050d0504 73
    0x400500c082c040703e07203c01201001f9035904c01c010780035094600d5003d04108110b0340040003034000c645031500403458111420494640707149114842c2c2c1e0b004100040712411580ca070403400c801b9506650b408d803015000819000d02c0a000150380501d00600050760a180401441c41d0042d4588900003052070b007a2100445c580101d0855400f81d10000025510700940100315152002c002e1070074403480b2005214401c000c01908804800301c0e10f6034804608800891440703440720000c41e500e50241e8800c0001120087c0d040201d48501c40c00b60046201c0241000081848808454003c54485944242c10100040745860241810700555401c00031407504100880c2e565a0700e8107610700ca01d801190a004684c410000d8904019540ca800c2c4514100f44101070180d03007008400f4240e4805901c000b0070400e10403419546141094610f1400807041030018202e0400b250440100700354a4040208031602c89000170001000c8500c0311250070b180030b0608509000116a0398400c000040104111100 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 647282302 1250 647281052 647281079
    0xf0b100506181e0607050a0605010e090706081008030d0506030f0c030705060708070f0311010c0c020d150f021c0e0705090103200d0b0a0f1e0509160f080705030106 72
    0x110700740c0340d000c03503440809981d018418030741216644c003060001e91002049404a48501d810340709200902c096621071446094603481102d023500c0640c0802010000030f885260300d160442680c403400f020440d1645241405e55106011508800b0380302e030248081414200322500210500f680500704c0f40801d00d00180d222407803407090314403480010580c1c006102c07103202250701c0315030300101a8507007025a00d009002240c804111400e65441c0c4a0720b2984140150442080300340d0080c0b0400300302e1070300e40d07440c00c10080c50340c400f403200e0380d4811819480000c1c5200038148140c0310300400442e02e401200510607100031904901460b000207404007c640c842c9040207056940c003010080e070b2151740b1504241920400600c2560228229200d0400c3c040d407440c01c10b0040a202d032301071008400c0f1500031800c0e0f400141c940d51a0120103004081482e1155000a8224405030142c8062039018410342070021b00c1c9800c041e6480b85141b90421003141c040000c08024070f400e4009000c0140380046001445 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 647283552 1250 647282302 647282347
    0x1a0c070602031e340506070302030f0402040218040e1f06272913090305160c171c0305090309040e030c060f010f060201060803030a0b030a0f0b100506 66
    0x400000c2095500111365803d02030740040900000301e11098041d100c2c0344842039101007956030340a58404101c859100c1c0c000c891107000d000c030f852107964a880e070910000750702c1140c207400d01e00c407014502500c90340c0b6402108441c3c3c0d1410000c101410100c903a5556a42518103401030b500e107020810031100200c01d000e1024001070150001c111203141a904002d0404040612203280780d000764040314a0584116410f80074040c0c1d41419000030107000340d4100c0b4104903014020440522810403118810110341c910540700c1d1808250035a600d07019080c01100c0ca03101040203801c9111403450460041d890001041c3c3d042c40c0a022500f481c4941c25103910030340f5101801a038942c2c0c00913201507801c000b140c2c3c0071200e1608450140c40d00300354039201d518080c080d40148452180000468510500900040d41c0521010758a541c03203800707011004040e065075282e09070080c2d0000c43c020070f905a4100c01030360700074003080d2190f180005041c01c0d051a0b5402545c030440050041c0e0307020171400c18480120 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 647284802 1250 647283552 647283607
    0x4030c0c140307094b0621030c17040906031217070c020f0406170d110f07210b0906041a09060403030507020708032106101b0602041a0c07060203 64
    0x1100c1e45c1186044d00000180441d4a060a02c075000002401d02c6030702401c103c400b04031140c07000c1c040740c003a08040c818810340042c0008616400441c04240c0c00040001d444100c0c40100346025554000d01c410340b005984292070401c1e909040b10825600207050b28890140b0a0000031180741c5014058841c19100d14007a000d003940c0040301da1291a10350040010f0114130001c031400b841c064185590b16105030f540701c3c002880b40e901c40d494040300010041c05154010004d00041307403c0442c11070310b800801c417582c225014a50100b10114854420b12806098070101408a40c50182007541d0108180320407941684501010030803034110104444e80c019906247c040f8443c1c403284012460050143c001207414040094000c0365450340c45900b9171220003403182c41895550f61810803040701e081e81d0751a404142e00114501c1080009a441a00d4610a1000605054440208181450074000d0051120030001080084800104114001044180b005618004e40354001211108103219100b08 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 647286052 1250 647284802 647284871
    0xf0403030e010210090b06010212031b0d02160317010b0412030503070c0b162d120603150212060405190f0608030a020706080f01050a030b04030c0c14030709 69
    0x300b60300c00e1001030410590503a040c44810340c24200009922816900d15015104540c3c2d0304041d501c1003010340781301c1d01d402c03200200c00300051003550403954494480038a60070340c00c00c0742e220780803d089801c0380003034080c0e0313580001071390301500050f8200010381210204000500007081040804a4000f001a03814600180c9940301c0300b80030754030702c812448010a40da500d00300300090342220b902e540004c410f0729514800c0d0b906644400003005060741d0b50940d00e000a00c0f500c0d9035003038040c111700010074066283c0051a19545d40b00d203108401038a030031100c90f0f9000101401c1501c0e00b00304450704001d0883d010031060500d20792030740381402c006600020150300c8503004080c1c0c2c0142c1d48484024003880d8140c0382e650140700002920740e145801201d02084000f0042581a07400040082c140c078406882e00950704e04581700c0c481859001803041301008903010b01180062800c101e100300900b4141d01e081c0c0b003281944209418000d0a40120780d82901c0d180501060b104002d41380741036840002122503 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 647287302 1250 647286052 647286077
    0x12060609040f05010603241223010216061a010c0204050c070503030a0e01060f0312030906060b270301090323040b070b100b07030503150307080f070e060103020f040303 74
    0x3805890910b0003505003624150001500c03c1c0c058001c0e4503400412501016448000b071751010546185000b401c14143e07000207240c001904c48801c0c1d0300c0058454000c000074140b0b0102040c03d81e4060310203010129081480d060410085028034150f0343d11440c0e0b08a44405803c00081c0595280c2030040e102d00d8944000c2145a951b0004507004503405c241070766505c0c036211002001501725020440d041d07620b405000210303074800b42c61000c00e072544601d41204054800034124040d2202c220140c5413581d03100800519203959200802c02c50f040500d212801403550b0401c1c5144806842c02e0301e000764189075500d0300003a4040743c00500040a1001161000c00d980d418401e03d0080d50000303190b40340000b5146080c0801c001c5240d1180355a210b15404454907a00c8150306401607540040200b40140045041042070300f00f02820f460307000d821101d090740d0f20f20403113160000c41c86105d803640e08030800502c145403a021203907500c003c083c00d040d0320f403070103101c0c2c01811889103101c0035041080003034041e0b = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 647288552 1250 647287302 647287309
    0x150207020f3601082a06040f0e0c0301211b080c090f090d140702301b0d0528110f06040611030d06140906040b060a0c02030a060c0305160512060609 65
    0x105c0f0300d107401924854681c0e85500e0724111403452805100c1c82c8000300c50001c1d00c10100300007124180c481000c03480640d840d01540510f1000d50005d4111800c0c01c050a0304c02100380703030001c2103005060360401000d4010314102485030640307002d004100c040e0040b000b048008440010f85075418000e914124403800d5820460641038082c1090003988182e10300309960480503030843e1000c1e406a90751031140302d084941e6100b55500040701c0c103050880e010302c641c00480d00d03259a0001100c3e008805403001e4185800a6903034407440301d800201840910101030040c84000070720240c3c0031002703481c00c82d1282c4103080056414001c9204140070010304000c18405c007001482910080701c0c103000b060201d030b0344450803c0340090a2043c803d000e070000138000740652410707004221000d207026002516250b80080308460503044518207a800d40309140f0041d0010301c0d640310b0a010780303000741e40018070783c140b042040c2d00d0fa070176961980040003400e2102080303203884000c1d0107401410860f0075603610340303071600070 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 647289802 1250 647288552 647288623
    0x21061306060b0c010203220201090608040218071115060603040b07020f0d02030a080a050f0406111213020a0b2b0e011505100903150207020f360108 65
    0x111400d0804100a0710b503c20540141d03000e00d44c50028070f005034412501045014a0480010380002c021030000c010150040e140c45800c540081c040c0321142101140d10031945000f07a030024000360f2030044504400409000811200e00200a20135160074040c0001e220740c0009000600007124120110b241c550080007181d0b851100f400079a407680c0e016010207034880c0c02524141c00403039070280008854210b1131080d1031041c01c130f0802e402c1d05900c0d039458070002421010b02a03a442c0a04100c0840e81e5042080c215200703c55400c540126002c1620610802103441da0210725002c4050000c80c201c804541c00d11100f031003001c4450060020700740c100c00d014001c022182d220b19480c0100c222303441c0598000d0b040550f00c003521140300205001c04110350401185c030000c0d24064446440b0890400d4580051042c1030004084000e80c0000e10002071071900d403011407810544c1e00300340d01800d1504910b030f0301020031449903001c1c1c140c1d8074000c103085d2640156041440d5000022450022070b45d0b0001c02d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 647291052 1250 647289802 647289809
    0x203090405060d020d03020606090106050306010f110102090303120105030708012702030c090a0c0906111203042604060201060801020a05040621050c040e010503070b07120504051e2106130606 84
    0x17241078425400d00700039440c1c00c000c4d07034594000c4001c01c001041140c007400489004143c181c4d640b4281c4801500308594401d03940d1360320a0695001c200418480e40c0800240226004a10080919515000405280c0716a991011149904080844900404860010b03140c181f80c184003211450391840001e0512a01c944044d0703014000c7d009000704c4108650000042c0034150f1112122292104020754492014611101c046d80c0080144a52044014007a50300b2900c1080f000c1c0764224046545880c107039602040d01005c030380c04202042481e509006100c01020700c04e00031450004000f000034024401d501640081c000b81c00c40115941c2131000c002100d04008100820581c01c111401008580c00b074414141e149030040008129440c0100b2800c0480d001483c0f9585003141d50742c0c401d00e105070003400c200e0500c02c06100c0001d071600c8800759041c85040001405c00c5c40911001000950702c0364070f80355001001e4400c5800c08811000680c150840508822002c9569440c0b90903000ba081070f40 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 647292302 1250 647291052 647291059
    0x105010b070203010b0f0307270911010210090308060609061b0d09061701170a060f23060d060e031b0f0c1e01050d0e010c0c030e100203090405060d02 66
    0x1400000c0032100480507110300da10850091000d5040c480070445c02103d1811007e0381501702180800028054240f02c440ea0400d070f07101010300b00e03100c1c0c0c030100403500b000200f900c106070945804180d960741417107e206a10040b000c02c10110740e00380c400520102005158501904000410503915035070302003a40d8030000f0710b02c82041d000c010000d6107a103032158402000b0100703041783c07808180c45009429840f41c011510b0003110303003a8030b850703c11184071201d88220900c1c0e0203030661070004900c00340a101030000c9683d5000c1000aa08410041502000141d00c0d2032852848140409941d030a9002d040c1c10b60800c80200791035a80c0c19005066204620110031288514641c0b0001541d0201e00d2800740003c600540e1100200d58083c84903040341e035603d20196000c1c50030410800d600030b10103040510b58040b0300059100364401801c3c2180c2c0346011401c04118402d804004040e4030100c000450742013a910013018803100305000c3d58034090410081c1c0718070340300c400103041916004140c480c242d4005 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 647293552 1250 647292302 647292311
    0x702010f090308180f0102010209132a031a040b011205041514090d020a0c1a040510120b0307080706031d07030b04140a0f1b0b0a05090a05030c03071703040801 70
    0x9500e11000d640360551800e0007491400174103040c1b9030040c82603400a0340040c18810380d0104850892005007460004200040070b0012039021a00d03111410700d64400080e02d0024644c0d510040f1485003006507c0c1041c8200c3c00e0013404a03d99034840e02d580a20b00e0600404506901c540ca044180100c52600801d0304901c0d080040c0380c8402d24180c0035010355200b13401c1c0c07801d41440303800032070711801209400380c0f4002c04441c00304890f15041039103110301d0001c00d800038109501d40c0000346410080410721400100e0649015020040c18450b9084084003100240316562401c1c2c1303500d84401c101c0c0300d450241661340020250f0000301c644c0c0ca0410002000560b4001500c03850034075a07400040c4e0301a106809000203c039286e000008000c2d0490340c10100311400305090740d807034026004803142412803d1010b080002680d1002d100903100c211100d1b180c980d152402031042c409508500d034000e5120350b222601540c141d40300401d420080da207a4440c11005041a402241c1c0b542c4100e90211400750300c2c2 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 647294802 1250 647293552 647293567
    0xe060d110307030204140f061c0603061404060c0801030203062206020705010507090608100302060a02010b1206090d090b090405280b1e0916020a0204060308040e0108030a050702010f090308 83
    0x158001d001762100010700354046900310040c01f11741030788910b1081e0440401c12984090746a00c6d81151a1309039a802c02041e119160395460055605000101200480010612080107224000c03903075075a050b0f1524a0f4150300d10b0b00043e642d000040c080800b1041144042c071050704130000d00000f1103030031131815540c1e0309030f030320f0003600820048401000082c550700d40802c8a51003081d04500070030350b200300300352054215000c02034664841038440b81951b5941140e005540c896220340c0b0341215540d40981400e1a08445041c1412641c880301030410032010410320405010100352001c031a029207000403582d6036040490428241c08104404041b0f0300010844001810f0700204085101955004d20106040701117805101a00b82019030252003040040c4081003091040458a481441281d4031054903401141c01c0380e120b0703002600c01201c006000d10040a101035003038014144400103602d000c0e1003e00043c00350151802c002c1c100107000b594085401d200c0c512620145800101e00e03030382d0f18034 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 647296052 1250 647294802 647294807
    0x609060d0b131e12080106020706050f0d0f0b0405060d030207141c11240319060f0303090510090609140d0c06020f010b1507060b03030708030103030f1805010e060d110307 75
    0x5403150846060010840c0c4d44105841a040c950403140650000c0070f6585c100315080e075940e0030010721451718800c10311014003600d44034014400080c0b803010f0002181c0c0703140300c00e100a50380010010b07406135250094000020b50300203648001c0f50340c0043e48022458031000022a040c1c504e2005905c01407040501e00188918034119000d0084100c2d0b404038580e0051822814084408080010054083c0001840e00b600c80c03140d0301400240c6000015600e840307148100c64034581c0d41064000074081d82040c03020782881c04940e400f294003418a00612407a04400900019940c007850240d240300303a0400c607643d114405540c02c12a80a152050140c1c1c884000030f55440302c0010050480d802c0c11005030250500e0159211100d42401000381b0f040190749030f02c000b03882040d40c001e03094402000a5408a031200d00554042c0d44070f40d481e05601c680b10100100446500844c41070b5416154108001580e08402ea030410110151812902c52000c102414014844900500f141900001c1000005507 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 647297302 1250 647296052 647296103
    0x2030307030525020d0b0a09061122030c0510020a02031005190905060703150905070e1908030d09030e030f03041d130f020a0f0609030b0609060d0b13 66
    0x1000e2080c404810f800340700c0500401c030009803003c0d400c60000d13542e95000c41c401c804803640c041214040440c01c0042030f612001140c01801c0d54040e0b020020510420f52031302038501c4519080c100d0003041c101030646c1c03122881009544a1907228861450801210134000d10040f20000c0d00102a02d502c0c501c1610107502412040b210301d500c4030103456600000900314032403500503640000040025a40d428001e84c01041c0408013042111001e040004400516010f5103100e00c650340d94810920500302d05120441c04000c01e440d02000c05860240120760b0000103403015000969408a5262440c1c24103640c4c211812003056014001d07150300c1d2202e480700100600440d02d00d40d0259008444900c5000c040c0c1c0b009490042d61403069070342250114071010300c1ca00040303000405544c510360b0745030404020341415500c250040341547c5002c20078000c041724910f0b0712400544020350b144c80d02500081d542940600300400c0c9c0400326000c565000c00703030645000704a91007580510180300300c0d04c1e41300104 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 647298552 1250 647297302 647297317
    0x3010801090b0726060d0b0a0209010206011a0a0c0f0218060f010302040303090e1b0c06060315130308041e05010504060b0121051e04060c020c0103020319020313020303070305 77
    0x8010b200400d084511031004c803003142c60804c01180d0805544900c0e0304207407030081c02455124407440814004680c0140066004a4440b200140d50f8600b40d400a0300f0f04005a104900c00c04ad1425501002104d400440d03101d04070a15101000c400c080c907005030264803810f00139410030210f180c0342e100c006000c07507070364044c142c101d038000000d04070040110b0991040380801000696076280402807241003090280e00f04a51911894111240000c408607a40148210b510554420014405281000c1c0604504420264000541840d0958610195200135000282006000c2d0300190500c0594100320400b0300d403c1044501c2c5443c24108203029110644080d00c00a01c0c0c4081414a036000d1280c400c082032070118850f803271100d80340d0284020100200012103440605038940f0840400c02003241c032844c402c50000030a402d40c0c400c004e14040302c3c00707105414544104140312045110254017469a4034401d00940e5907900d4407a141543d200d1864002d4240c032010503603c0400d9085405013001 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 647299802 1250 647298552 647298563
    0x3010e030a17070c0c08060f06120d08150d030c0b07050f22090f150816050d060f09030c0b0a05061e0102031623071d2706010911030103110103020304170301080109 72
    0x20f52180b404000ac07140400d4100c02003030b4081c100f82011a030042c84035960000d00110113110a40c0c0300350200d8205060300ca801c60000c0e07000e4a83d1820046000e4510b90008240d1901608240340096030220501c00d410280d644560468007c0034681d044500c1403000d0600300c10300b4005c2c1c0802d085032001800e4144c01c00c0c204402d008002090410002aaa0700600c5007501003046051805013400800200c444c4199003654490b80c3d00e03004d4136014040e1034803541c40f0f9074407241900b01508102c0c0b00c100024000c601c159041ca8103204080e5030342c00308148503e040c2e40342103241c0d5617000010f0345144140034603c0681d503003005414061100521000342590000100c1040c0c0d400e058840549904550091400109503401c0780301e101d1440000141e4007440f94129144000c00302180c007c01d98483d0380c1000d400b64031800c014071201240d23000d18281e000909035644d00355410356551004604d5840c0401c0d04140e40400080d044c013014112404007580ca03042040d0390395846400d0107012382a0711405856 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 647301052 1250 647299802 647299831
    0x9050c1621050c031213060c020d030e0604021018030c12030306060809030a1404270b0301060b0702040c0314070207050411091309080c010e010b03010e030a17070c0c0806 75
    0x1ca081c024802c645032800030801840c0f519034611000c1c00510130103000744040c20f0783d0380007010009070076101d040d0b80814150018807414095003802000e544800d00a445950084414040180c5400c0c0524055030010b09115000b03003225140d0181a030b800394400f07802c0704060003000505558040410192602a0781c05000310307078507004203a442c0d0f00b0584031900158810051703150010300c0381c10a580003604204585182075510000390f00b001540c1070404452085504100c0221040c2d03104000c900142a4024002d0910b0500741000501444102030b02640e113030707003019005900c04c1d409501d181c815440301e14124108000e00035070305c1002e4007565003d1031600d4060009005400c090300c0030b80b100248032400f400190405074000e8000fa070f80c21602c0700801e10261849200070300500d6550440f020000904c180424209401d4800308001c10300c1c00d400420514507031a9001c840f2114100804a203000280ca440c1411038040402450242c4070b88120702c00401c0004004c00d41038004c20a50130f0074035 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 647302158 1106 647301052 647301113
    0xf091f0f0e03090f100c03111507090806070207050a091e180507051e0d05150a02030711060903090f0409170a170403050409050c16 58
    0x65950070110f000700c3c8a06011000001404084800c040c00e0a40d42c0809801801500c0c0054104140780245e401080c008005000e10000c003002c0e116110b03c0c081d0801480e4540c940900f40041c080e880116200030701c001040025640c0042c02c3d0b40b560f9182c0000900241000c0700b500c0304100c590a03054031604900c0c433901110250380070045c01d20300307160300d03113942004074540000f40700e2680101d980b4802c105010401d00d40800c00e903100d54081702d60f400c2036450f1038802402880000d1400003001126074180d0003540c0100000d132121022700301141038864850b0800ca401d205154010300c901c0d0301ca4074000f2060801035002400000e00c20107281c070794682d00e01c100054025060400109070b602c07242e100c0d1017a8a1030703200301f890321441d09150742e0082a03407240b03109aa1036241c460001c505201d541d00110f0310304010506000d02006141d24050317608016581110701e020000c00c40c030a = true := by decide +kernel

theorem cover : BRFrame.Cov 647122302 647302158 := by
  have h0 := BRFrame.cov_init 647122302
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647122302 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 647122302 ≤ n) (h2 : n < 647302158) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
