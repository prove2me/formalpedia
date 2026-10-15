-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4889
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:03:55.614983+00:00
-- url     : https://prove2.me/submissions/db5ba66c-a5ad-4a00-9925-02469c1738ef

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 879136690 ≤ n < 879316546 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 879137940 1250 879136690 879136771
    0x1080106060806030f060117011e020318010603231f020c101814190503091003090b01031b090e1005011e031713080607020d050403051203 61
    0xc00704211078201c5582038001c40240c01030541c03107035402e282c1542d81d501071181c42c600301420704220342a07000a6000c01c0503a5920088072016888140d80b03c2c1c013941051310711940f01100000b44c03103c118030500c01c10301101c4c2d000604440320107466501e00d4550081121380d00c2207000c0e0500c2140441e2144064030031000148031b0050321410405202da1406200c00866003020345031449a20000350822020b42c41c2580c072645c0241111540c0548a04042c01160204040c040121980c030812101002515070010151100d00b280d0300b20b080203d003030301ea0211010b451f980b0844018800729030a01c00c2206001d000d8040c07110103544c2c2d541c0c1d0104441596040140035040b4040c02c01d010a194000c65004042017203088490ba0711f496150091260f1f2484000e2040c81c104c031040305410700d40c6044d03c3c0300c11503140032280d4285e034030445580c40e2001103071684c006001d0814400c08460140060390242c0740c0004c0217104076079003c038203854a540040c2600d0b030102103014010f100400300c0380c42c91400c42103510 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 879139190 1250 879137940 879137951
    0x10e031618020c073003021c0306030210080f10060914061606291f210e2808090303070f08091228080702030105090f1002040f051e0405010801 63
    0x5d0b601d0720f414005804104020041d40000da010135800a00003544a42c2042c0c000e0580da40807000b078004004a90000350444046000d10b14003941040186208050352030804e250382e40d0782a400125a4514040d002c0425580001802006101c80c0c0c2402c600c400a491607280440c90104030358030001c0c0c074400b100d1407500e41c80c17401c0d01307101020340c0c5980c0154041d01c10381c050201040028944030300040342ca860000302c1080003c1c031600c0380c00000c0484ca0143c0c8020980e6654411010280c08003200303044552280c04c41581c40d00001c4807942e4402c0c824024119252000340d070340e2688d11350000c08080d9161005210070f0002c24844080d000540380f04c0c00313480303540b02c0c3d1000030f05c0715880310a5082e400c2038200d94035003a0808104442c103c040022a600585441c1c4d5900d49003400e406200c0307010b03405601c1c1000300244000300150085090300c4640c103c8560f813809a001400340d1045001d621308c2d40720514420003090412001d0300c100b550244a074442d42c10071305808201103503426030000400d40e46a8 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 879140440 1250 879139190 879139229
    0x40305010c02062710050c0a1e02030a181a0a0f09030308160210112101050d2d03050327071502030c0604050c010e031618020c07 57
    0x1d114074081e511541c00907000a2070802e40c3d5810008480c901000d04610b41c2e405010002401d00500e058001d0660302048103080036184210b094000c5c80c0060081140c052550000700c002803034120160b5801d9000b5880c00c4a80e038001c8655144000c400c1c0d40c0030f03020714030100386441c00d160781d1000ca000311420503449284500c0c2c0100342c612411941e1040c019020002c0c07012030303401005141e00038800d00780003000d038081503001c92070038014044406d1403a1804802000204088004006120203408485010400c3c1e0000c005001402e10450390702144040254002816a105148124447d198820200c140c030155041c08420020b1003200001c0000080050160320310b004103022118061000710240f00071503000d5911105070080780d100840c60b202861205200300304941548031100156440c1741881d152207a03030f8440140c265404103096109080c00fa04000681e4010580300c40c00c0035000074549604140c029442c140751184d10b0f40c00700800d1013440020060b540080c0b0350344c00c4401040301c20 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 879141690 1250 879140440 879140443
    0x62e0e1003050f0103060b220617070602032d0a02070602061b1b0a02130506040b150a030b0f0307080709180804060f2d08090303220807050f03040305 66
    0x1400d8040a062505040c08880e0745240f05941c1900d80c40b0700c00203074501e000000102c20b0f0300c20380c041d0a01440c0700d20154108000c01d8001c0c5048801e20030031404030607450280c051b1902018020311005034010b000480d4040034a00d04601041d64200c0c03010b2806080d041c0c1d003031141d030009183d100542e012030020010164100009940010707042c0c0c031320000e12219411080030384103540340c05070a41d40101c501c1d2040c0704240701c508d00803a8000e12561210600740d0b0820060076007110100c2c400c0380340c0300000307025040c90b0b40314030100c180030500035142c81003a10007640100084802c00390445c0d001640b0151070f072810800761010b4611200104009803410030b486081e45e107010020740b40d0b206d40c62403003c001241003003501e0a48082c1e041003600c044906108444074a66403146480801c89000c0c000d40c071809045442c00750b450b0759503841000d43d0301d60740b00c0c5079284400c1d1070403181d140d000100300101c0c000c55440c2011007031142016070b00e00500d54070381a00e013216003510403446420010302002080b80 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 879142940 1250 879141690 879141709
    0x7030c050d0305060112051803040f083c101a09010b040b0403080f190503040b070804051009022e090e0415091110091a030f062e0e 58
    0x40349428081842c1401c0004d1040700d0400c2661480d607112000f08051548c414659804040100112038480e0380e113020301c00700144280714209440c0500c8555001011a49190f0040f81520b240d039405841d202400c0418203000070084100346008851070241e070f10b440c0f405240c1803652500103412600c200e0004006031030b00180c3c4100106a0100400c0224a400c1c130f041c1c40840740c2101206032a034081008200c03003407240c2d14254980000d841d850a41035030304580918011400341c1d11750b486664034000305549400b81610082c0036903000d5000303031515140d0364100c00041c0b88054200c030842c03041546401c071030b1050b03400d5510106101e003100802081d400382080004000054088955007041e403a0941c02c41d00c43c0c10100442610b07045408140405100c04e0314036514007030040300e01c03c0806540141340b03c00c3c600880d840802d44168408406000406681c05405030198030305803501c802c800c110b078003550403005150700100c4000c0e01140300013a1554407541c031040e03120f000780070401400304045d464 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 879144190 1250 879142940 879142963
    0x219050a200f0f090a090201090e0108061005030c01020c040c020a06020c060615030712150b030a0f0510030c1e051003091b06080403120e0f0109141f020310050607030c05 75
    0xe03c40980500b01e55908401e40e0300114022000922010180012915900380750400c9124a0700440005603d48002034014491085640c04800441d192020907407261b404560482c01a4003030f25643c9106d02d0664401074041203180120b4019142547d40e0200fa60400c5c08503103c241c0110f0204400c50030020490b06483c42051b014906d185040100906010320700d0b0b41c400f440507500c4c6015591040303410b80100290981c44956170b10780c540720034002c0c040e002d5203c0c2840c0660804020600c40f2070885004010740741e209654440d51803d0109484000b14121010a02c0031000c40d4009265100c00d203c000c1d9880300c550b008201c09559080c034036081540c014440100c20031011081103200c0c0c0c454615a00180d05d0b180246a0a14006c0020098000c00c1c2580c0b025000b8460000018001580b01c080f10300e00c101c000079000268000565150000208405204900f100c80341244c9141a40150b80c4140c0070419042d006480302c0c042004c540145008401103400001440140841080580f03c1030 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 879145440 1250 879144190 879144199
    0x180103062102010e1507020f09011505090307050a060518011b24020c0d12091703041a0f0f062407060e010c081e070219050a200f 57
    0xea180040103001c400c501060034200309512090788003107a104205450402c50000c00e0f0f9440d403804146054060350200740205c0c401c09001504a45a00703000110380c0c121850543c0c41d40800c00070607000c4d82c0580c01030345415854000e142e00070400d5501c480d0100041c00710f0b561039036141c0a0500b07081c01c2183c4240d003401d05008203003090126400030ba402e2090510380c03060303003051001d241550180120180341120b82d502400811100d88141000421050304109540c131803c00740340000b4502d0440f071030303008040c210b0203190045000c098000c200543e0054450040000d1000d100440d04c0f04071901942d00f03a1b40c1da02c081d414080e04170703400030896800075002c8030621b9096020302914000d20400701746c0841c3d0781901041c3d503818000a540202c21000d0540003d010301c5504a500802070314003103a080002074030300031100d04d00040000c9214802c881ca90010040000004022050380c010340d50300701e80f43e00c1100703030f000d002606460030503040e0390107083c518640308280d0702081622800004614004d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 879146690 1250 879145440 879145451
    0x61e24100314090d020f0a021011012c10050606160201020a080a1d010201020c0c09150306040c080607020303040507060c020625032705060c030f0c0a031719050901060f0803180103 79
    0x240e9910200d001c01d000c5076080021102b0080d809460140c2a04050268000b001060a0f84c04540300304005102d100210195008001da942e0388900f20390f400e88400f50000303814460428012540303d403000743d8600500450b02c0c865101c0d80d03401601da00190840d0f00103180c1c40c0d40d80b4581d4281002d40709400e8002d000075070600c40040c000c0c83d40d4200002c17a003807140701c202c0e01040341d54545c411841100900a01a106180742c60306004402140d144200b81c420310070704000404072403010003038a00071544400940300c01450884100d500c44104141684c4c041020496510b481480c08010302c100261902c452510310344074200074080c0d05224083c015540440020040c0032440665a481070f581d00b150616150a08103082078954010b00c0e1544040d0349001400745210803002401c144011712a070341d0164801c1650090b8049642c054480c5503140c550845001407811407034005a40c810f81b007800004d00c180d940e003080312868000754000f903041c0e00009a403552401001080c402d44660a0906101 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 879147940 1250 879146690 879146693
    0x50d0510050d1101030b04060e09070b032404020f1225021203040f0624050607020108040204020730032412060b03061e24100314090d020f0a 62
    0x8411408040083c40340d41000900c1c1c60581c002c1d88480c402d070744003800410100c4c0d1070b9484100c41440540300030748030303204090002581c0c405c1e09044074818800740405c1d00070300203400d649000850b130414205620507020b0042c252400040c1c8040c002a409101c640c0c0640e04000700140b0070386a1003001e0601c000d103007140d02d0701c401d0b80019000c010020b2540115940f50b480d0b04080340c02040e500d2005100720f00307142c00100b034018002403c41d141e4495001d00d40d01103030344004020030740c484c4980c000d0115208000180c090b260641c042c1003210b000795034144e8804000030a4a050080006014529454000d404407400d5494803580c2c00418070281031f00d4866089510110902c14503116076644002444c4100c002c010b8950418581c001000d01108c40f20b0428803550012102c03040704008030703e02a078000960b44203989c0c03030030300341c001c2c441901ca04108810018000203406c940d80b184141a2100300300300c54000510401c46c411503d95001e404d8415003814004d04140030350b04c800499a002040410 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 879149190 1250 879147940 879147949
    0x10306050a0c08010627030b010f1e030b06130903020607030b010839030903030403270308090301020708040e06180c030703020a090b0d0b03010f111803011b050d051005 74
    0x130b041d5a0715003050101c8036251040e05041d06103101c000c0403e400c0d446000030030800807900e1203041e96500700701c11483d40c0d103400443c0059903d00c1e04807110011260010400700340404075487d046007000c0c015108151250110300107550018100324010b03031102c0d0800002c80d91510032210000c44c00d01e04a08607041800401003007182c00400c00303004507070005105090844514000329040c4e601c1460325203a203420b982e499102d03001100c0c01c1d030100b02c6c520824001c0c10010060b03a141712002d07100107001c2500395120741c030803600a1842103800d5035003084a4000b003503101004d4001861420041c04052401005114042d50916117010042841d01c0c14064104545c80507203902071002e00d001600c45c1b444003030031180100154000c0340c4a940028540a0696407900300d440007020030742c0240720140a04811004840c0003490700d411808003840f98020200000c41010701208000300086a200840d0710300c00d1210441450800c049000040c0fa0700014009018041d40702d9a801ca0850403240b401000c01c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 879150440 1250 879149190 879149207
    0x18120604200a05040e190311070504060b0d1d01060909061b021506061b06100e070203090d050715050d0501050103020301150309020117090a051515060a030908070803010306050a0c 79
    0x2d04c03ea480d0201c02e07440d10010443ca90000d45200e016071038140050130040c100c0030500c840c000031030003400340c040380500b000c3c001c940450303e0502c821840d240b03200e00c844000b009100c1511001b0713400c0c0318030150840024000c003c082c01481d20b0003d4003d10a00d441ca0440b242144414606000c400341421580d8012031030b0210703002402c07000712856440400103819480380c46a0760303e0b038070702100388001c48510000311144601c1c00d0203800c0c41e110b61604014040070504540b241c0050b4804c01c0800280d0a10303e08800d4044d204100b120742054442001605481d07070a480003001643c040f50408040c01c1c00d008040c01000d00703090071403440d4100f6800003209070f0102521014144c0f1046104116440b55450303a103441c03048042c021450034818090f6031034604120080d10503100d80818003c2c039080304505030340140d041080c0804146410400c0c401c654000c1c01d4000e05056480d0305400100e0918401804c0317080c407517500c00384d0720340c154500001220701c058014810b540c9080d03600d82501c2c2d00303c082e8 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 879151690 1250 879150440 879150449
    0x11a04050114090f07170408190935120a1b0302060c0702060c060405030901090501081608220302031e12311101090510050a030218120604200a 63
    0x20f040c0566501c10141d41511b0002c44550110360307001308000500c40907101505200d0b11090240c180181801021940340c81c540c050100c882e00c4103001804401c81319035407a552419080d440d03100003500c10040a081000c0341c0c1490807804000258819855880450030720590b113840c0c84203680540341d45000751b88410040070400904400500030301036680b95000d0303800f80c41d6030004031035081c64189803464484d0402155140810f1032490007040541c00b50303c1081c410b41400d94604804000800f0840e6039000c0070b800d43c1c9068a03c01740904405021301210781005009400950f47c07142c80840c120481801d81d40b0f403030086041071007544a615810005550422040c80780c984410302e000c0c0300c00040003846886810114090880e5030108500503001c2075107440c090700d402c4c10b41569541400001041c02d41107900084c4c04020000000380680e000e00114007480c0c020441d120908004645492501640306041c0e520080420003000031512150303003a01c46100070006000a09000304605000c1382c0075 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 879152940 1250 879151690 879151711
    0x12030a050108061f140619030f050603190611070c030c08160608130203030415030f0c02030a0203030a090c05060c060912090a0501030203090307081306110a02012708011a0405011409 80
    0x17030340c92165100740c1a100700d100754038200030130a5140080940108107038412504040c0c1804000340d16440d0104d1000d0010044501c0750024201030b41c1e82034003c101984425403030420521804011820046040f00654401c0d00700d14403190800201e545401c18042513804440c00380c46090281c03d600c03107c4a9000301820340301e803980380120b20000782140150740041e1000d0036028004814158107410018881c007a0610402c804011a40100d0b20380c4148144107000d6441003001c130700c11011755485216024005e80004a101d600c500001d50380d030b4005a107403100756001d142840100d4105000a0030800d0b95030017460301d0400c00001140c130a1096119080c10b259011000400c013120034403c40e10215440307041c031384d9520780b106146480e1621600560f40010f4201c0b000d00b160324000a2107900c0b46030141c60f941c00c10890030050880412000c000b02002d100c03402c40008140809002e0180c042e41e050440c000039200140c207010845d20b050b4090380b10401c2e41d408040389078480302d0880b41c10440040 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 879154190 1250 879152940 879152969
    0x4180f06080136020a181b03021c0902010504030b13050d050306010e03150c070809060f04061202040b04030605091e0c030d02060f04110a15030605040c0521060312030a050108061f 79
    0x100c06ca001031901c1010500e03904003004030314444d2941342d40103125201440180003c00f090b011400c0045038480c020003404148200710500210b2020341344154003012080e1500001305c415500d860504000d140d8140100d40e000c42400219070704550003200000c070076401030694450080c002c1a50801c080c000004603a00000c01c5014001e03864100d80e201e41001d0881565203d95a0b01d00352968000c3c400c1c20700185080b034a04d00036040d18001c030303411250600394460070942980c40d0480200800360090390700d40304a4404d007a101d070307020b07400704602c00800700940440404101030500f0003003d0403910045410010070021032107144650700d40c005400c20305401240894501144407844107400a1071200c88a0248034003040e803540244081c1e50060300c05001310311403004241ca040c01028021100f180380d01040e44a080380d000029580702c0801001c94100903000d80d1010301d5940305885192200b0b44540041c070003078404200c800c1d040702d042641c88001050000600c1c1c1070300143c2c021950a4100e07034 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 879155440 1250 879154190 879154229
    0x2106010f18050a030c05031e06060f040b0415090507050906071e020310020705071527090204120501060611150403020a17090f030304180f06080136020a 67
    0x9441d4805440302400e076581c00b80e164204007541001d54402c0074440d20489181c85254840311081180c4686040020015900c8100400404c2c81c800980c880e04650f17075120070b400d295500d01922441d9510354074513410301e41c10700c0c101d441981c20041c01070041c00000c11140c019511610300b2919220f0b0007508035002d05100d0b54003130b45e0740300c0c05500c0030354103125040f101e0741190a15402001d000d03200340115040340f545c0d8401c02164000c25140003000c03442402d910011456450343d108400302c40c0101c5103501a454071080401c03600250015914200c251103203008100c400d1003120050000b034200106214400380312981e903942d80807410a9600301d45030109041600800680c0c807241d41c80255145559281c1e80d01c3c12998001000e01e62040204401d400c0740c0741004000c444c251036030b050800c2400b01041c225040601100a40410540d0783c0d00e9000070701400c00c2c801c581c1d02020140a0800034881a00501c03c25180000c80c000884660918000113a031000c000c00e0071240401520540d10002 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 879156690 1250 879155440 879155477
    0x16050a05041206022818061407110a12031403010b0304080a020106081005040506071103040902090a03060c02070305100209060702150d0606030c02121201090e100f022106010f 77
    0x1c9042482c41c00403010040c611885417000207548500341550348903540c801d20b040449191829100340b101050721860010003030b4031140c0003440c0c0c8600500f081d400c402081c402003100000d41d13621041c400c00d082a080340170568020001c01d00c2e40300184085080d0350412002d807209100140c0010075600c1c1c001600540c01d4000e4000000600c5c03128143c80138400050303c00d41c060401107808030b13141d010311000200340500601180c041032100c200118141414400050029407142000c1907201d10120780010004055005254000b849035000e40505861403805c01d14109921135000c810b030740141f1800c07119860740c100b0740381050340444150724a00c04d10600074940740b04402640307040a080c488081560f07601130304040e04001c4142e0880c6c0110001100c1c00c5020b01882c0011107409240400400c0744c1c8284c2d420058803030031402c041d1404000005003400449900f4511008080e0b004141d2503444201c49074580c10f214100301400c1241e2a000c0300082103125042d100c601401f01103507000410504 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 879157940 1250 879156690 879156697
    0x31b09050c25050a1b0905090c130e071203080f090c090604020d020c0d080108011416050405060a02010b131b0804140a1a0601050703140f07120816050a0504120602 72
    0xf004400d07903400290500313104a00c85d0070f84805031458500940300040d0000b0600c1540c0c402c2c85450041e24840d142c42c0c08002205c030030020720000c4070303032140e4034483d403002e003440201d00401034142200701022075440e01030030b881c000030064410070030306104001e180d5802003801490381d03100320384590150703584400040003406101c0980040ba41302240780c0c010302000040d110203100e1944c940c41c0c2c8aa03078595850b800d0315624418446440000700104140104030302a017102d260060400b40e00f01b98903030012030b64a070070601c00301c00140e4440460f4801030070440c1e9100f001c4442844d0500c800000d001c00f0348481c000300d1800408200c601c0b00080e05102b46400758150484200081d11890201e606080b405507412510041d20306d49002c0200c0c02c2d0f507000324100c0e0a03050389525185940c88928115090703a4001012620740c4c40002c001e0710f000203400310000c035412a030725101c1000a0605004040c82e152260f030300d603024410200f00d01d508441c0c0ac501034a044602c5500002c5c441ca8407882c14602900 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 879159190 1250 879157940 879157943
    0x5040b0904060c02161409010806060d0b060f09040f06060f0e16110f1f060815040f02030601060f020c030114010b0a03020c070308041a040b0405061b07031b09050c25 73
    0x905c03000041030f031144004101c031446d074040f10301d4812a6207403112280c590038141c408a90004101882c800091020800c4c0d56000038000c01081d001400c1801003190a00e048400f200c4048048070700d0810080b00388180d0001d058020400369031a8100f1000b14a8071070090850717941e1074482e02c060310b1200e200310700d040c0c2c601c4000c03000da9600d13400c2c0c903c1669441d010713550a4100c0650140701011090000e00c114000c5448550087c0381c0140c51854200c58200043c10641e06687c0748454031005d40c80c100000341c024103056a40741c450251307031000241040180c09810b407103641400d1200041078003116440b41900c01568200d60b131152980d500364001e11418070803455a00500000006014403440034000301c803105003641c0c09104089030480340a206a02030807002231000d010a0003103042c075034040d15014980840d011180005808407500d4540e031648200c0b806400d0001e4640e41a0807540210020314025000b07200034285500d40b10b10a0080440c0c0c0b000b405150300640107003000302500c07134412a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 879160440 1250 879159190 879159223
    0x80c03132307050405130605041a150103110304050709051806040c05030601080304350a0b0108120403050a08031015091401090302091b0f0c010f0605040b0904060c02 73
    0x1c00503560000391400c6181141c5859018071207000845040c14020030b44296455221344880303102a5490b400248405401031b141c0800d4141440c0082c001400007074018485850a0120b006d5000001402d03191107244c6545140801c2c420700c00020400141401a60240703500840d02e03945a43d0403009012004104044502c5403100707002c184241000080c064030b80c1942602c14a030389607152036a4900c0359100e03000c035050280c002d000c0349166a4595184034100000e43c550310b149441052031038640307a01c200f0303200545082c0040205110030041604070302d1420618509084c5151039245d2030b003500002c041c020800010005003494031401414020f8403840803c00c803061000000203003106e080d40034020441443c2150807040398060340c0035034200c90f4020b005a0890369040c5110350030389101441144441e10510107040742c11241000780c2000402800000f8100c48400e02030000ea62240d80206c0c01580341c643c1c1d40389980c0305c180f800d980c001d0300031078046446240322030101d20342452003010f500d40 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 879161690 1250 879160440 879160463
    0xa06050d050a02190c0b0147041806060908100f27050d0924030902040c030f060b0c07030201050c0c100e10090503030414040219030e0607020607080c0313 68
    0x8054005c10b00004582c001c0c42e0483d4560b0300c4540c81840441000781c0318601d483e500200b940345d2041400c440d641d02c0e8080400090342055207102c5045600030760050f02c50030608089035000c402c254441d0700d00410b018540720549501c0c00060035100c82229030151403660b22080c0340980b1103490b07000304220800051070210310300110341c04413a0103040e0820446050280420381c1480328884d201c60020f440c9040c060710b500e4003064031050301d840c20354100c000c03d1585070180c000250b0f9540c0720b0101c001005440c0401c1e4640407001207000c4a8881e0081c1c140da10044c0004034540500103860703000d695087c240300e903403507500003111440c2c0000b0f1b51545500c0030f400c030103c50415a2106182e60060070075960300841901d00300b4241c420808601031160154024001004162040d00007940d40143c0074000510340643e0403400309410480c0090100440c0d143c408040c03000c40e00b001410341c0800b0500c00380456003440800104204000f800380145544040049039201d443c0303200c070001c0d07240d000c50202203 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 879162940 1250 879161690 879161737
    0xf12021c0203010501020613020303180d05060103060501050307050a031e1b0303020a0618030804030f1412181c050904140a09060b03010902030a2009010609090b0a06050d050a02 78
    0x82d52090151328014001c08000c65008403501e00c0281c40c0d2640100a582085804104244003400000016a1100813804410f010440034403859010f1802288041515818a000c0c1403500819500c041d016000512041020501c00d01e0050300040c6100d00c0c0549d00c07603035820044040c0c1c5444001084403405401c00000701500003920116041c42540d0074003083c45901048a0b80c0c00403558094003180000c1c0004000900c680c1049a402c2c100d414101c0503e2100300e025901c035000421031100074082d910511190402d13640301c0e000d1008060005140c0b991a14000c40300400c0309002a1060040100312501160f61340c4e0000e00702d40c48040080b0040345050b1541c0301c041c0a01070801d8880c0b074506036940340e19080600880c0803454024005041c0729000f6907540080e80001004a22000c040c6030399030940e6525445090b0082215a40350740d055401c00c4800c0044030a104c6015101e1a03440d2000c105a03900300b4280d8039002594400040c0650b1210030a1020784034400c01000e40c01c4040e0010710 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 879164190 1250 879162940 879162997
    0x60901050d0218030319021e060a24030308010513020a090927121d030a02011b0203060705120a061a070309030219030605010801050705030c130f0b070605070c030f1202 74
    0x1c241000a03801c0308e0705100c01c1e44503203100c0b142d14411a98503402580004010761010313040380c801030100310020300900c2d1203940d09a600c6180ea801c11000561447c004100034580b90643c0c11507910100b804510f80b02c034002000e4059001c2d8491412129120320241402c030002e90700c240e65014890f0f85441984540d45044018808401c0650020031100280d0710081c100b000e100b9084481e002e001803101a840c1d4005458001740c0000198000d42d00480c1d030401a00c0901145010b0380c09929810780b501290410003100f60710041802c8001c5140c014204a41480c01140d8081e040d46000c0055440c01d590508444044050300007a401440468109818007114030404044034002d2400304007990b00c84006500741c40e81500c68500149041c00860600c081c1e10000340b100c1200b05035025500d80d66032107101102580760344002a40280403900400780700b01c500032a80d2110003454003c11030496641e0241c15030b0070700c503100d0080081d404100780014109904552004280c428603c021140305114034 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 879165440 1250 879164190 879164227
    0xc0301120819110f1f0911041b080703020315010e0103090c1412032a03300601080402090711072409061409040203060d06090c05030c060901050d02180303 68
    0x501c0b1074820480c3d803482e132450220f030348544440203008860700c0d884002e446801030310540c3d4003030f00c03503445d820844040c03542d0764480d40049084107041905070110950014240c290020291350504d4010820002e0317043c140c01408003c52002d0030181080072017500120010040d52000a000f040b40b1070000c50f10582074200d00605080071543c0712808018003040d0751316800f50030841402c01c91030038803d0030310b41101610794110768064400c4030305010004030802051400904086281000f640354480c0317140384009280d50001c42800d002d08141401e07804600d04020041c100801c011440c2c0c908058030754248030480040002d00076042d96103c04480400360b400408503840b011234586103001407541d00906c0c0d140c1032240114101c6080c140ca40b02800040e510061034142d0102810440b000000e8003031113404107240c00b41280700007481c100310501d4981a03c42407203a21510050158000741c3c3e90100448401d8502c4120240c0c40d0f540d46141212540701015095a041c00045586400c1c0c101c0c0e84000c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 879166690 1250 879165440 879165467
    0x7031b05010e0615100e040f090c0b03060901150e01030c20070f06030b010503010605160c0605090a0f211704151704080a08070c080d0b01170c0301120819 68
    0x1300c0040c0f011110030811000c030303082d07500b02c0030889001c5210740b245071551112140c9240d9040201e118049a0f031032000d2821160804041c1c404080180002360130408031103400740810f1119104070000c5580080e05031041c65403442d0402d9198990080e40c2031140e10703103003455440c88216441b10903100ca5600d480301014090b90715032019440001800c80c0c400c0c09901842d51068407487d246074200720085625501c001e03406040b06100308648400a200a8408801000541d079000e4903102802d08222454003e03a02503a100c0115030401d2080008582450940d8040c2620059210320700e4030b000e00e0200e162507003122403404c001c80d0005402e00d42c034070201070760131441d0354400002040010381482d000c030503103000c1c00c446028010804098001c00c91142c01400508092503891070694480d802544555042c4221603200c42d41070314a960807e0174100000030100800d41c15203003140700507289000510030f84d0039511012503081c0c2404104801c54480f1450080c034100345e1580004050000300b0320005 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 879167940 1250 879166690 879166711
    0x18041a01081509010c1e020703051b030d0201050f0109150b071b06022407050909040615050d15090215070b0601170709030b060a0801150f120807031b05010e06 70
    0x141c0c041c241840f0f0307407035110748070f440b0303078211061a00305142080f030f401607a0380075442107008c00b10116804002c050818580101441c8a9054000901d42804451013004055a040c0000d000c8502407410255041d1400d1441c0050310401e415012240480340c0d034403442449c0c4000840170180900001e08290305600c034020010401d54802c0308a9688000d0070003508100321000d50807426407144ca03071140c0c1011880c5030081c1440c4000b030005032051710542c1c084a65694503412444d03148603a048440040a04807a8030f6101c09482d1200c1c9075407d0803058010302d8950b02d10303415046548443c203201c0440e880407070382c80d210141454903c0c1490303c00e565a0b404140e816003140c0c101703201c039020345215003030540c0e950301e00314075569075541000d4000d030029a10803400c03040800c42810034032810303000c0d180c62003990062501e812103003405d2014540043c0718040d4840d02c2580400d8110b0121a0030075450703c0d00003000f0075410048004000c0c0650010f15030b50a20801600c80400050054040e004844 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 879169190 1250 879167940 879167983
    0x305070f18050a1d010b0705031c0204051002070504200904020c0723041b020a020906151215010503040206180a0b19120507120b030a080c1609060518041a0108 70
    0x2c41c06c05942c003810000400c1503204018101e80e48007000043c01d24902000740c090305060311140054651004500c3e01401640541001c210518103801228195004c02c030002a00390045052040b46205200d0715a02603070300015251403294040100000401001c0d10325001d64801248603485002102120740c429401c2845516010104a070400c11a00307094000780030b481c001e582400042000103049a074400ca01c483c00084610030140240480b01c41c450103200c0714030385003110075186280581c3c0541002020320801c03005844501c2210103c000880c41002d88405090018080c1505034020b445180404601e028210f81040030514480c90300e5251548100c8040c6244021154111000070014a0080c2c450820300140e6001d402000342c00b40940e8074004154a0f01403469000d48044003d541c45951314000304044014960042c02e00444240040c92400300043d2002d001c1020301005490090046010050756400c44c1c03601c00c1440c1d00681d4a0740e95000c1458494104d204000071009034030 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 879170440 1250 879169190 879169199
    0x4031e0c1508040b1f17160b03010308031902040b12070e0f040c03020d0203131208040c06121e0204080c01090f030303020705030c06090705100305070f18050a1d01 72
    0x1d0080608089041e500c1094a9503191900802084040d000341c1d009256045c0201150b0f200d400820302074082e02502d60102c803140144d079840c041000b003c0b020007143c1d5000034001e2500c1801105c2c1129000f098250300c0391211420324403100700420302105118800680003800240d408050503285c1b45400d107000d283d984801c01030b914000018071095000a000a09188900d0705030311000a0424074030700103027804905490300c000c0f03a100313032158140268548156810400120303c42e401104040c6451119420913907141c405581c5540640c8092041540e40c0605000c0554442010084141c0c406d05c00b06401103c2c030402580305004040c40c034000e10620001c2940200710b1042241d40c0b40007070b8103000f0301d95101103000f5008070382c0c04c0f0394500080205030b101141c10841103001e455104003500080c2d14290411494a0138000f885d0300f0306007094104640280c1059030000c0d40740c584d0401c481501c0360b048120750070044a4114075030027003100e44040b035228904101541100c0d03080c8105030490740c94 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 879171690 1250 879170440 879170459
    0x2a0103050a0e0705010f12050a0b0f120a0f02010c0b1602010e0a031d0109050603010b0a1b120c03110706120c020a120e041503060209010305150f1504031e0c 69
    0x4400b07214050380c800c0300c0402040d44182000c943d0383c0010316000310207003540480d030029124103a401031a10750b00c6034901c20f000e00d481c1c03c45400710306044544d480c0c0d0041c00d42c0030701d03200d500c180006041103140d80c11181c10769025120000740c0942c0702c1c82812151901140510440540c4600340005600c0c0001164a040c40058030302c20302ca40603103988848243d610011788410b111003030028104510007070005a2602c031480a0740c06089070710403075510740c450000000e00c0c500c035034403044816071200d500b01c0002ca2200f2036100c84074031291911801c04202403d00361a010042427000000b4402c030b5000040080e8414000500140402001d11802004010803a0b0311040b9250150100c6000980d491010f80207030701c000f1100102800114140618120400100d00d40d9402560020740020314908150390501c5100c2d44501c00401c00c910001001011460603040a00c00314059200513012080d426032400507a40110b078407100f1065068202404a14640c6e014071003120030000d081c1d03021446058 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 879172940 1250 879171690 879171701
    0x703120c081308031b0301080f06060102071d070908060c07050c030a0c260304060507050d0914060c0f0a06060f060804051c032a090527092a0103050a 66
    0x3030303a0421403142d030403900c0d64481c6500251500021166540f0807104603402a00a14020b01e8804050000c0f058107118803070038032100808690440d04040e405000e0860800d0051007031a0080710606074659a108045d102e800c11608001100d03c0369404000c580500080104040c1e80714005451501c100182450381d2807000340c41c02031110b00e4511041c014110710b81c0c907807200040301e4143c8d4001812150070b200d0175644a82c211000044c1c000503c04180202041003110503171643c0b42c04840d4501e40a078000d81c034a10b40340c00900c035010015072403614207400c20140c6050008002611000000740c0ba044008180303e200321249500c0c2c0c03c500103a141d0007005118811504003010313254076282c2c1100b614a440080c01014145942c0b41c20345d1041016003011910684228040701d40c002036128030192410042d6070096200b8071204c120340100c0c0d5644445c1450001480d000e43c040350315500806400c03c0d0554540120701038520501c00c0c04041048a5035902c05400c1e2020841d585400000c074003500d1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 879174190 1250 879172940 879172951
    0x10020306090c091f0314160f08060607060e061803210c0f120108060a0608030f0912060c031f0e0711070f08010e010b060c0a0818060703120c08 63
    0x32510000101c1e03010181c40100501d520043c0f1300210712010700f04030a5401003a00320343d00020340d03600e11410746821169107181c01000c40b5003024003040c00428004d0100070103100610400c0b10a5010800310b403150030548001d207078818418084214240f0640b50780348000c4480031000560095011b000d0140807013200e034540b500802100c40411100003081d084000a4012043c844040002903861810380d00500401161960b02200552510307901c680340c03000103003d4050b2245446000c1003c40c4000044401a500d00000540c880c0750580020703500c50f100201c0b540a038020f0008000d160b035980c1000f54401c0000040d011a124140110399100d075082d801a6040d032091540440e03030181c0078181c0556500130310001c8440c2d407a218442800c040c800f50f41f2007402d5a444118030401244203004003644541d00381c420a04150010720301c5541d82011000c041c01001001685d404144001e2010f07058a880140c045591582c02703240c014a4580d603d203540050b07070710700381a80310460700c0303902c0850182d07 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 879175440 1250 879174190 879174199
    0x11010e01090e090715030b0103110c0d0e13090c030b070302030c16020d2a08010903020c09040c0305190b10030201021209030c030d0521100306020c0f010501031410020306 75
    0x90820a030710000c2e500103000c1e2002c0303100f903c00c006016054411058000c0c2007550300451032811980024042d1515180304e08070010040c424007001407030020f1400e4441200d0710f8000306491801000c1104898910104c500650038413051000b80100e0b0b0618104491003a8100d1220340c0c0c500c2000c600301e020503030f0030f81010740d0208280300750048402458421103000800140381c050b81691581c070410200c40044282c00c984803028680b61043c1c3c11200000c3c11814020b101c0c01403195802074a420b40855824400d010b45000b0606100300c605450015540c0041100c0705040a0001842d000160b91b0b01144c0f00e01c503190000e4200d00c042c1c00404101c0740d043c0c0081804511114040c581c40c3c00c10b04405825124090241400e9901000051401c2c0110b0301d81695a2000b031401040f00e08890000004406039201840694401410070f4412250441c00040e00d800710011983e0070034801c041c900c10651309103000170043c05014055510b000d10414220b400503004c0b00513810580c0030881d176032a0b00 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 879176690 1250 879175440 879175457
    0x810202d0424170103140d05090303071b121b050402090f130f050c0403021504080607140c030c0622050a14241e04050606010c05032511010e01 63
    0x4a440842d0a680150103814260f034208200481450180800d03030003503d01040705c4c500d01e44103c2c0180180c103444191443d14516104906001c40e0b030300d110300f0310b004168081c00d042d03a03940d400c081540c00300500a031745100000c507030650034040c60020b24600161903940c8455400034140ca0036200321118450b015007e0b2603051080010800908404420b481d40503450329600c04a4003054031440c4c1c4580b000f402d0043d01c55065006000c0d40c08040b19030007062420411060049600009615910034030740c3c500401e0402100e4400304c110301a14441e490148000701310100784800204245200381809070301030710501c528140f9440440e8001d2030141064009410030300202e4130b008040c8072000e021a044a03400418000b40c54800b15800e200c0d02c0c2c111100c1c1c4180400b0442c4010030900c0085405080f06d17403400c0035214036845880c00b5200a0601a59400060030490144282c50740c01044a481c0340c100081070b911003090703858191003251050680c8450214560050710703074240d140410794a00d0030 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 879177940 1250 879176690 879176729
    0x4151d0a031a090c1008010f0902030f040605042102060411010306180213170a060b030a1101050702040b1e090a1104150302070501020f220810202d04 66
    0x2c4551001c1c22600c128003c0b03010303150300c0d07494510382070174000000e9981503160b40c5040441300840420ba04651802e0b80108203000341e16841c09000f5400c2078200c0310001d0146c64074605402c29503100b03504090b1095400f400003261540200d0b182d0700c12405288091814180c87c001102100c20740d0103400500c000ea840040210440303540034204201c1880840c40ca9180c684001e00b0b0749901ca02455171b8141d01c042ea202080120900030080361000542c0181000c000507075825410002d103009407030400c240402d5040035542c0715081103002e050003030170880a102120172000300100100444a000c1c034800008a15840250b1107840702c07150107402001c2c180b44c01d1003468000c628100c41d16104150f000c2c001c03000415400e10082610b82d9151a800365110144a030a01880c0142c019450111500705802c111084001c690b940300c000e4492000541246520505c8510f99125544a11206808100070041243c131000300d51079141c440c036030304040d110701045006691099006650310030254400524 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 879179190 1250 879177940 879177983
    0x1a130b0a090c0210111b0d0503160c17190801030b0606070f08030a02070c08030a09060e1908011a1c0602030c0412030e090c0a0c0206030a0204151d0a03 67
    0x251510aa105036203141811103d404d050b41c40725100002c04113000210b00d0f07140500d6080d203050440c980000380c0102c0501d50b00c09010390200400c902d224036850b1400d003550034032444080ca2082d50080b89441002d04102034418250401e454008900d81c1c68501100818040d920360382c120790f171000c035412a541c0e074002400b2080e00690703c00c82e018049000c00c0d030000b41c1400b0166106800320080142c40e8031031400d2603000c0c0300e2281e1200e4600e410030480c0040080d8481076543c01d581c0d260600c0403400d0b05c1d21001c0f601c8841808840b034001c034204000442c10540c19000402040c0182e5540e02158040c031341004060316100032008a000c0d41c20312003500103820307030700a180d001081d070840c54241680e40402d80d42c0d01038022411800511044040342c118175010380c036180c015605803041c40c00c00d04654800b41042c44000400381c070031000400082c000404940444000e88500c10b00c402820390490005130450080d2605425060140031401c0d00500b8281c008074122070300030080394101d4081a0001 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 879180440 1250 879179190 879179201
    0x60912110d020307091a10021c021002070b0a05101d130b1608010602030405060915090415080106140f010305070e03030307050d0540061a130b0a09 65
    0x1034004803815800307000350754203101c00340c0104080740c40418000c0a100d20000c1c060b21544003244204a4420f0b0010400e0780042d52040d0380000814015401050042c1a45040410010750000c4e1340006034010400440450a6003c1c080e10f584c14000d135112018541e80c00c03802c80c0204890301c200b507000012134201c0b83c994143c00c1404154062610a01a11203425610048528100320b80c0e80210100c2055404540310340182000c1c80610b05084c1800d000a00720f21031140c00610032160400c07030909603a850001c9500f1000010420020201c54140e0007030b481d030b00391081040c20b5180c4507000800c14112454401e6021000708603c2c80442104011340040001401d1041001a03204a84a141c2c074108011130049020b0349074182c44001148007201540c0000303027071301446200c003d000041d08042070020701013070200503011460b2600013481581c2c42d8a024102174007540c204850845c03107072540c0781c0e4001d010806617103a0159800000e1444180d40c55010501d0300b044200c002088910401d5021 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 879181690 1250 879180440 879180473
    0x8090607060e1614090402102001140618060931060b030c01020a120c08220905060306101806031b1e0602030f030a0f0e0a0c060912 58
    0x20341041490b5100d45401c1c00116039800c20000400c0501610620310340850136800210740000c002d1405030f01050300c2d500440c07030310f40a0244070880210401a01501c0b0405d58000000800c44660345642104403103400344c842500030280900b41108003119140304500c110000f1700440055210520070600174a800b002201d44180b541407124114403002d20300d224120700843c0d002c102c080d0303040201030600800500590555205020050001f4a1914440691030705c508104192841904200701d0342d2040342080400090f03962000342300000e4001000c016603a40e20340411160b9104d80c14141d0341c00054884280e40188503200300b00555000b44010304040c55034002191b52a902d6951315520742c107150940461800552090204481108000d41c1034210345e031004000c40d00d0204065100e00c9000361504485c40000009140014a9000403607800440394003049801c201c1c0b0380c80d45d14bd141e6040229907041c11030b080010542c4c41103203160103880c0e92020075000541c0c0c1e556049002e0281102 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 879182940 1250 879181690 879181703
    0x10f0527040605131d01061406070201052203030f030e1e0f0109080304051002040e040f0c0b030403021b01030c0929070c0303111902040b0d05030a0f0905040908090607 74
    0x2d002c40c041c0c5401c1c0c01d4110500e441c07140892443d00a001700d40031001600c1090360380d03078508030041110464040104410070415240700d0741d160300350700040743c07240b02e4070002c0e4003a614a180f51801e20070180f10030b001101c1c0a6600e640c034444203c14100c00365855005a01801d80c4100040f0340d94401c0008030342604441c0c14112190040404076031070035200209411b40b01e160004c804c0006110b010301c0158041d0140100840c81c16052a0b4204640703040900003804074215421030705d003001000d064140140c6001311445403246403d280007550f4a07096030301c0401075180c000049a06500070700403101400101e807181500c8a0a09071045c5407424981030a400c2103002811903400c481c1010300a0000d20b000d103945500c1c090460078054800f0700401c45128842c0c1c4030184292400000f0b0382c56054040e811100840d20502a1000900c456031841015100d8000000c81c480c002e600b110a00b000c40c1c071251150006155104104800c072610a000901200b00c100800d040511300031008281c160b01c90003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 879184190 1250 879182940 879182951
    0x1b08071707020721030f050705030409290906130248070e0f181506010e0f0307212f040525030b0d11010f052704 50
    0x5044a11840940d041009038000d110144403101201c084c0c1e90450086142d074040c000d4060794001e0000d403005100500304800841d4032410042d080c42101d0080001c0d03074007801105078080280020030446a402170444200480f071890f2805d0900840b80b06401c01018402d8403030902034508041d41c0300c055020044405d404407500c2103c0c01c2c003088980a0f16001c031501c48568501e070441d0b1107501d1071590b81940d41c482502001003110403c2d240e64880100a80301d0b025440b0130f01801c1911100c0100c000c610f0181c2040804601c0c640a070081c0b048109030b8803800700c0000c40b018000400030174001580c054100700c009100001020f034045422201c0302003001718416090b02c2e02007038a900307007281c41c0d258503074003c803199840b140611000104008403410026410702d0395900761200002d220442e485840c0c101d11000d0f650090f032065a0141c0007811509800d990752500a4400118500341da01095038101150b560500c01c2c0300b6264410483e007902100070b4900070302249192040a0520343c0b00b615078 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 879185440 1250 879184190 879184217
    0x51b0303040504060b07061401120201051305091302210a20030a050a0b010504060620010f2a0503070f030e0a020a09021e0a090308031f0f06030c031b0807 68
    0xa224440003045c0c1c4004454907010305260070f40668072140004459050518010300181c00032400c0040d0050b424201159108800c9079909869170305640090341c425198410015103001c60407031115400e10071915600c555009d0700703c66288c103812503454800c41d8020520f2070001800a20313400300e0360300c5c00c0290360501c0c0d41090010f80b44c80340c82c85044620340c02c0480010100101304901501501d4103c605101186c10300500400001e442c040c49280c50510b00c00c030740760411003075010500d40310783c202091040c01c00c60007010409c81451725808290402c00060000d0301e61180081c0c07400780c1e12954540e6030b1540e00030000c80203008403175035428140c001c501c1c03801e0041e950400903800401075048050b844914100c1c11800788607007070f0341c0c004100404004403040746038404900c80c02e40780e2000f1200e84940b50004c5150b00c1411611351400410091040820070024200d0090215000c0da50144080c8040000c100d084d91f02c01c0880540110300c64403a4207147e4004c81c0c00e00e500030454900740d91150f044 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 879186690 1250 879185440 879185449
    0x18050d0503280e07270c17070e1e010e0d020f130209130507022e0e03090d030e190e06041e051f08030c0304090510080a030f0905030a051b03030405 65
    0x41e034011600c40c003083d85c1c8001c00c0d031003d0784014281042030710204511000d10602034400f18444100440301c524460001e2a060301070141446100c5000d06008568020342142070b080d420031503542808102d800100042e81e181a51001c0707802a8042d01e80d22151303143c04113102c0c060b4605107041ca00a43c0034000381035070f0b465884044026602440b00400d0a007055000a81000784c0f03e403c01841141005458112580303011041602000d4804002030ba421a00503e46c29401480e8901354403143c5a940c400a160344007941c2e6020240489181c500103041c20340e0002d0341501031241030914610302001801600d090303071004260700040300c0d4030001c603200d500c410700403200f084170800080381c050003007d4880e50030844500b025100000045141200b600c4001d6603074040c52041e00b090703a4440000800355076400c1c5010006090150131114090780529015210702d401c60b01d09000640d140c50001024500001e181130540c1d00310001d0690034054140700c62a0f410500203107600340c03004001c0020542c44 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 879187940 1250 879186690 879186703
    0x50a05061e1b130b070f020a0602010e0a020f0d0c0b030f0105010c0309030209040f060513061b0215060105071b08190206030412300c05030603060c070309030618050d0503280e 77
    0xc103100200106c60f0344c1c8104a003c0f030042e00300c1c0086a00d03066140583c2d0800049400c02150100d8a1119242c81b18000682400c1d04c408024101c04e5200c900140494201029600402d8031460120381c0382c5c0ca5400440300155070041c094001480414200b000d8106560155007087c0581c0301c80e11012559101d007800c3d80c50907102f550040e4a20b043c14028003005100f20f090f8004140c41c9030101d046460002551445880f103081000603602000c648940c1c0100c04649146500540c00080300800049840241c80c0c9807140c80b001d40034a00e4501403038180203400c1a0745079401000a82141c503503844490388c003503009840b4400e0100d0000c80e60703030200441302c2e10300a0311140845035405601e001c1d56102030f621480720000602c00b0030f200380203031607a0120305143d210410003000e9403180f07990704048509800c1c603440500003914000f07480c0e825007250300f2010b24590040f0b007115640c02d000142180c451200b1500224a00788200801407801411081680c03800d0540d00c010034401402c900b0381e810001c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 879189190 1250 879187940 879187943
    0x50711240a050f1804240b0306040f09080d0c050a05120901060503030c070801150e0f0c1201031a06090c1603110f010504021503010803090d020d050a05061e1b130b07 73
    0x10080d01120846152600844144182181c00032054685400001c69207544a0186102c0303447c0201c00620240c9460b4440c41103010645030a0000c00540e08052070789902a4035011002800c085500340b1040c0184121083c142c80b9540d03640c070f41320144101c08450038019000c81e80079500c0340c038002603995007000900350140e40140548860f62410414900712501c050b88811038586007a41040740080246030300754040e03030080008090b503854841c1d00020384147d001050b0110281000402404503450000c0c0384500b01680c3e443c401d0319039000300180c42c4000c485000c440d1000304101544010b002d002c60426611030f0821a44a01c1c100107010300f40142a07003a060356a5603001040194a07128040707000d0810f0b508400c51a650410045a440c0e104604100d0b005450041179039086440c4c143c90182d2541d00b0800752400001c480ca0301075120201550308826848442c08a008500031811220b4040c4c40e48803841c00e605280c41500c1c100541003950101e1121070320710400100e0702d000100528055 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 879190440 1250 879189190 879189217
    0x12090d0209071206051e1c0b090c270a0b060403020901090b01081f15200706110313030f1403160c0f05060315040f0c050711240a050f 59
    0x59003500200104c5038035900072441055204110f81c4100040201200400300a807130b0040c4101c1c0040c90089030142d0345000a0062140310200511750402007103094120000300c3d07001e4039405881c103641b10000d000c3c0c0d480565404101010071840140c5600100c034610300682854181590398002a81042d4240e114003001170710344441c14000d69001b14010382c443c000703c0c0340d1300d22418a046171030502002e9019400944150750040b24080703004015410f002c60301040c0080111520400c19a01c440b041d20903c4041154101c11484281c004010fa540c3c1c4240c05480c105000e02c0d58440143d2820102e40547c0c05c01d40104000034600414001000d01d010b1000c10380c02d00700d81d02d243c41038000b40309a022501456030302c8070030b0189ea940c04044070340208040900810354410280003600400116035410052468800e0091415400c2070190503010300510724121900e01c0c00e002c1c08013182080c00c80d40d40300c8469040710805c500102001d0422480d662a1807030601ca0603c8103a40f247c0c3c01402d6007481c9 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 879191690 1250 879190440 879190457
    0xd0b0105030f071802030606090d0f030e150a032c1b03061501030b0a0f060c021f020a080d02091011012f070f0203100b10020c010212090d020907 64
    0x300d0504200c2060104080720040000d249014541041d07076000010f41c481098000020a4841da03802050304c40c450801000c01035044028a404881c54184101c120003051025031034060307900d40401c1780c1d02026102003040c0c0c41d0112082048000f4450211002002a40382c400000301e0410744181202540003000108001d2181040280000303042040300346c030940c8880100403000b0070300c99000215000a00b40811600d00e20000100b0b101600e40019902140071000002c04590005000469030b000303840914616031072200300d144c444024200d90b40540d202c24111400034003804010404005000001801c0079020400520301ca00c40202c074200282c0c138007291821060f02031240da100103402c91b216800360185031038206407a4621100c0c1c10140c44000c10041d01f84496800c1d18049a90f000f003daa003405ca0b080300d0b01f0020415050224015044074104105140c00043c1041031848141c0082451850044100300e140e4400da1125402011541d0a83e005032120440c190040da01a140c1c51f12 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 879192940 1250 879191690 879191699
    0x150803040503100e030706051302031f0c02030f0306060f04030c0e04030e1c031809061205010e0706022e0e010e0610050901170304080f0a0302070e010b03180c0d0b01 73
    0x5003550042068103404e00d0300121024800c1d000045036401c95118801060300e590b050040000066107040294150003004030a070900b100e807104c011081a6210400c01010502c180220f0356030050b800c0441c5407010400c0403640c4c0c0d15000c005001a5003980b1212803902d601c907902c0c0c00243c034441d030005030100521000d120405030042241c95801c0302c107446958540e9a2101314040c101c401340c00103400e01100a401618950320307828458080d1400080501005a585c0d0015052800200c41a07426520b0211410700000d0041b07031410407510640d00400007110122941c03071803400c150100101d05902d450f9201110403060055501c1d03071007000000600c584001150340c0c204900141900a0026000c805200031b90315400c490b81900c8924030380084940c3e9400584c3d10f10b12554000034414820301c440c2c0e0308429800100d44810724400da0a56014a030f03107215000144800380501c041461091001440810014640340036044060b41241c01000056002c10302c4031800041c1500d440819100520 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 879194190 1250 879192940 879192943
    0x11b020309100c02031902060906220914240a26030a02100203090312010305030703090803040e060f01021f1a09040f030f0e061201030302010506010c0c140103150803040503 76
    0x100700c8030b030074180300e0300c000c0305940006d4641c0b000700000d04903030500c0e5400c103040d5100c00301654090100500000d565004001b0b0601c0d0b0868814030703100100c501c140b0007080c0302d00c4078080c0c1401c0802c948038a44040d01d603c11300e12040004a00d16003844801600880702c00c0c0c2e10b03039503514020034440d1036200e18070411078103520a000400e164000f01e0b0b03104202c00308016a000555110142c0005401612500d507071b20500d0441c429400b41b0701c41c0d24600400441030100c08402081881c0c42600c502e520300782c8d82d510181e03d90203144151000b89100e000010120f042c81c0c3c030f01d0581c405051050710010140b1014801c040a2455071410360580d4601c01c640c1c0346d44604040b100c42c0f15040780c03864820710b0300b0703030326250000a0024018100720302103640745402c2e402203006000d01d040040c42951984140325a01451820900c0103400542c240004101554044c0340c0344611280c1000701022321700e00b4200300658103407000d0320441c105a075600c000340c42e440d09a6040005002004003644c0e64074a443e0415 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 879195440 1250 879194190 879194209
    0x1b06120105151c060602190c061d03100b031e06040f1506240513031b080316020907030e06010302101404030c090615080a09020d060e06060103050705090105040e0603011b020309 78
    0x47c2c400640303403200280814412060362003181d1440c6010380720310340301030a40c0b5640241d5100c0c3c6c1360188204180401081407581090024060680c21a524a0600764001f0f8480d05019010605a001180450042070240f081100201c2c01504080d01c1c12412a55440032103106502c51f04401003146400c0404024400000f00c805a9914101d0304081940742d10351034000c080e00c030051850722041a0305030914a5108420000c01480c8243d0340c6822002d011003204858064080348a20700359400900e005010b0303c80e1034045901c10004100d44c5e03003180e0911406040b040305d000e051081650043c0e100441d807900800195201d00009400d0601e0803940405907151034026a0044501c100784074031240d4404141c5520a1800300045100086400480c04071240c17a00c020b0000d6050096007018401c00091f16070042d8400e0342c00304490340d50008115032901882e8501800030b0f80421080101d0369503041070a400900c024000110003805240740408044c1c0d0700d00c600b002d070b08003013558002440d040005 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 879196690 1250 879195440 879195463
    0x31305011101110415031401083307030507030b0a0311180708070c030c0f030e18071d030f0f060108010b010507020f040207051e1b06120105151c060602 67
    0x2407082c454003070811011401a03000d28604410a185d00c0040e484c483e410001252007002ca04c0001ca58689016644401070403010004880234840c0403400c2d12601c0e0039440e00e803d00c03941c500400f030700c480d10301714013402029200354101a02c400c00c0c2e130100c3d41d40b0f180d84d9000358411402500040749480c2402020b2001600c1c000c480d042942c100300c10143c0008541307a0040d01e510f4500c08441d000c1c41c055903c450035810150030010101c18600825400145004c60f0701070858038a4424a5001e424944548080391079030000740180360f481c1e5001c03d1611980c1e400b102c004007658401c00c1d054012a103071060b024045c18050b40b149004111906c1c0030702c15000e22030400e00e04945030002c84c0d004510f2030300c280f1008a0203654001811010b0010600c00c0b89418101100002a84250700d014591384a0760356030210307550000100740710380e140b8084084454011440403100c01981c03800c42080910a00758810045400040141c40d01503000d03007040181a07140100700185090420900900d04110070702c4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 879197940 1250 879196690 879196693
    0x1120605030a150e030a0804020f0405100504022d07030f03050105060a052115041a0d060c0c061e0605010216140a030830040f0b07030b030313050111 66
    0x400344080c0e180401d44002c0349800c03810b0203441d40c0341d038000e50f4010101041c8030f180c1404041460b2800b01e5110400c0c07030007075000301d5440101d00340d09010001291070070740322140d03a48070b0501c0400090500390090494024505e0300040141680c29000c4110041d1000710305041c0c3d80000c0c0d0104050b0080608600004035142c104080c0d0704107000f0030f0340d9200350201e00041c80382c08078010901c6903045040c40c1e5080f100c01e040b0304803410042c110205122002c00058440d506090880c0c03035515103811a04420748004025a800e880540c03680002000300103841c074104006a000b0f0408112107010700601440c8100a50f000001380e040e10004442c000d809c25411900b040110307a0b914080d140402e03003603642c042016000f43c541030001580100d03d80e8030080c9078641c040b651034441d401d00541c03a00e01d0194180c008a004600c20000c5800240072140106440185500d11001c104400c40040d404030300c505000030207640d0f000000745150803c1c0010041800300807024405ca50384622840da004d000d0b42d0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 879199190 1250 879197940 879197951
    0x9020304032d181205060a050a1a15130e160f020d030b0a050a12050609013c1803090501021c260f100b0f0904050a0e100b0112 56
    0x182c0750400c840800d4140b0200b0482003041d040b007810010f40d0700010902150a0814000245000d40e1135090440c5c026000720b1900c80011407205080c090107a43c043d0541c4041e0080041c8420042c0d0141038002c1c15100c003205001c117090001c400030107140500940800806146001c406034021308010819020030408180c004d1488540c000491000b416614100828882d154002003007006866501480e84204402000071700405d151080e54007041c0540d0542d8216a2240340b82c900313980d035020301c4040290130400302800b00c1e030503014400e40e03400d006480240f44014403040720040e00c2071441101c45007400380c0c80d0b0400f0150400c220400906080c00a0616100314003030034415520030070a81414054410b000081011002219006a10fa40c20002003182071901d00040b000e00112110250015020400b24040054000303840300c2c00c44400e40c15161210040c240005401c020300207660041d16180e01c51b107007074000e115034060007582d010005003074118a00010302060006c02070101c01032811 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 879200440 1250 879199190 879199247
    0x30304110609100e151603021006080309091504050a0209090f0705030115020a0f050c01080c0f071509060c1d06040f050d0312090317060105120a0c05090a0902030403 73
    0x503e1111200041c9080802d010640c4001090030351300040380424182d800041d101160760390000704038100a00a40c00c07160f550400d1880b01d01280c0503806107810345e60041c09900381c2c51401d84074190780040320880c40b000e00b00c006404281030f1a8160743d070145481e0041002c0c5242d0612208903075001c40d40e000707002c80034140410050031921040c040c018819840c00408a0301c80d008001c110f00a540c0000e0b101031074040390400c203450300040c0c0c00250000f5000700204954061130002e40361903411545016281810a0352003410f03810303891a0600485071244407075070109107a44510012201c15484103000c6a8000d102c0c180707055070b01900c1e5441b828052005104221420200c00e003554006d80310034501800c5420705032841105981c0207840c240c14481c25030101079210203200304d080c42000424905458090054516005a03500d1529004c080d000080b044900e0f03030001e41a84006051207442e06003040301082030760074250082c1c0041d030b07000400e20042603442580d44203000340b420881814042c03807 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 879201690 1250 879200440 879200449
    0x50f01060f050702212407050d1b03090c05101d0a030b04212622110a0504060b0a0e1909090204110c071a070501050702030304110609 59
    0x6000c0c400810119a0604044034000c1045450781d94006044801008050030084405911281d45183c5401941e991001c03034a00e0904011545081c400d54400c281e40c0e401c02201c954009841c0d0009951b2510002c0142e01c00e07407043d58901c1405558040742c0c1003030347d041a00084082e5804640103180c61150030204690202c00039403155564031ba40da440f0800c0c480051010040c0360406040f04000406100400040c250382d54030385100c050082c0f40140009000343c03007041603c00c00c0b81490303504e141c44001c4440c0d803441c1e450b03101c3c4401c04e4a80d0242a400d05864481e0780810301294079801030320b000181450500b00e000c0003004105e406022081c10101004074034060b402c140c5041c008400448451541c982001c00c0d1000344510101005a59407060100070f403c50344803e078043e62422940f44030020381c44086400c4a0029402002201e14103011103404480304030350031009803401d0080c680015428011180a039071320754000d41d10703030030603050603100f41303613000401441307100300b00a03a0005455 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 879202940 1250 879201690 879201721
    0x16050f1f050417160308010815041b031b0f050303190f1101110319090209130204022205010f020d080106050c0f010903020706090905010503030315190303020606090a05 74
    0x8180205482d242d0345090072440e1618080304100810101e04c0100d44940004015001e03802541c8901d4a0b0341d81340c1d03419032038a54040c21681243c82500004010560100b0100c0c030028485060280b02566902c4641c52202c004030590180c0101140402038900d800112030050310f402c402452906c021808526402e204070049042031041c501d14407201319004159500d155500320000744005044091a100070740e108440c55928609901903107800c100c00f5205102900394058a941040c0c0c031804c2c17001092050020080f0781c0280c0800164045d400e000c51000000c070a20a45e200d2100c0c24840007400c0304881c000c5903421075000f865417143c001d034090002030454000c1d042c03840d40c3d41001071020341002c01e0b84070700f20450742c2020800e804040d40050f03c00c00702c846607501c1c0300c109600e038000e81c3c003580ca0038410700b0340c198824004156400303214030840190140080505001d2200324220319034110083d4420380260300302c03004111b080d0401d0f090444d400056100d0401040c0340a1a0344500600e = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 879204190 1250 879202940 879202993
    0x10503060d110a17030a1d0a090f020d0905030306090105010c0c03020d0807080c07050307060e01141308060a0b030c0108090a11270603010b0a1a0904020f16050f 71
    0xd8462103940c1c607031240d50341407011301650421414507540329a1101d5503980070080742c3d0700180d4145282d6102d500d024228014107200141066111490503485101030004102c00d2010103900308501c1030ba030001d80c424140201e11602c0034548034900407040011030f8070164411070520040d40e01903400106100d800d50203883d412941c51585400c641420349070742c040d00b032000303217200c00014540c3e45028000900300d0807500214219961952200b00440d40f99218011250100ba101710244c0301155500b0003500541040d0b90640200a0341c070010b0341e00e000001d0310390a600b950380d4100714406041c180304d0320901e21070078200b49415042c4800c00d50343d0b848a036174018240e61000500c081680c0c6d07864052000041c0c004441c459100c2807210550403501c02940c0c40e52180d031038080211b12600f803075004c140494100440d0030300015000907082100d6400591017a0740f080d403c01c11440040b91840141c2088020208500d200390003600d022480c19061104900066114524000d0304d0101200c9103d03044 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 879205440 1250 879204190 879204203
    0x80c0405040c1a0910110724030e0307120f0201060603091101050a18060324080309060f12070e010e0909030318010207210906050a05030a0902010509091f05010503060d 74
    0x481030140d00e00c2c1c0b66101c05e4002d0301a41460303000154500c00001d9805940110383e682203514202d00500f0f802c0d502404459420058160280e402102c02c8514013040e84d181061545e16681030f0f95840040c8000705418001020b28a40e0910405000c0d1101c0e081c10844200551a103030320150318640039a040150010306441114410b0301403441d0442540d44405007681c5030b0401602404002d03014290300490071403581480b511844210048413104009180b07013441c0402407040c594003802010b901c4840c00c110703030000079420560151180442341e940038040101c040005054500480440f84178403007000901c007030081b000c011240c001d001c402d24880400d0042c103050b40607000342d46002e03210008080b000c08542c0c140842d101e4400213560740300032040c1d86801e800c1d036041c02003104010004900703000047d8600c8403035218440741401410554140640c0c8000036031440d404941d000c050768018000040c40e445003c1c0035030040c0000342032403411841d0072800301e08070380383c6408081c040 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 879206690 1250 879205440 879205469
    0x50d0b0601022505100e09070c02030f0d030507110c130b040906090605060f03071a03060a0e160315030b0f040f0b04060203060109090b010f081008070807080c0405040c 74
    0x4a81c020421003840c00300f1070442d00e100001d40390411110003a0740c400d05000385001080e010305c00384288644950740900815031b0140780c075a020300b11421011607400303d8151058003149014400100500324651410707039804611407524400c01800302001240c01e41c4190701403801403000d40d550841007075545c00c409000007500481e0700c000801406013240e028240500c3d0202e01810320915030802032080307034240c0352a10442008018075555004070310442001c40c08000d014a1244800720041d900208001e0002e056141c0b40c0d280600d01070400c1c2c85c031b0080408801d2840e99640d4043c014000101894008911114a140c46071640108010420420300c81079070001000c10624965210720a604188804980e04d4145084402540151851404101804130006d1010161301031008444010b139150b50400b6001ca40c195090100940703600f43d64030b0640b8000c240c010042244400529925008004003880e22840c54140600340110724001c0707040c202003002050302440341c0300440754246c0840c1103 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 879207940 1250 879206690 879206701
    0xc01080606072604080a060506060f030c07051e060f0903030129040902211003150c020a171b0304080a0f051903031a0414070516020d0308010f0f050d0b 67
    0x1540300b43d129402508030010401280c0f00000040002c00c081c4540f904200b240c03509030420909024440c480c07035600404000040d00030014901814803d44030f0f40490760000001422680351514000c00803000340e0101e410424203200315403140340c02c80c4011019500d9541810410695009010300203209055a00130241170b0464101c225002419040380c21521003070ec410281c034070f88014510f110790004c400e00201d10f4001254030741d1421203a110700c1e452041c16002c1003900c050b18015a4150541c01840ba006010402400c49440000d607202e01d035503505c0d01c0f0110001452600507000110310fa000384030a214400c800130301540959000001d140c6250760074604189415070001c0f45010094498800004060709508458041080401c81c217545500780b5092204a42800907056080020000484e40144c001c400400300d480f0807444503216800c598012880605103050101c001030045001040b001c4550701094014040b503003042c1c080140b800c1c00007039900d44284400303030005103560301080 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 879209190 1250 879207940 879207983
    0xa063905090420040e09061609050f060909180d050c071e08011406010f0507110112090b132d0b0c0405040905100e0d120c0201140c0c0c0108060607 65
    0x900c014002c06104d5607551540130f00d81450b038090300c0b450024443c0e100454201a042110192000c149686801025103024200402c10500003240368011204002035609030312144c4040d44189071420388603659411130f0344400c3c94959100f8010040050030f002416544001054100480308061082c0c001d51080c1c0041258195003640030031942d61030107018022804003002094825a0262504515200910400c2d191445034441c001c0801851440b400360302c3d8001c0c0f403881c40c0c4004011001034000c61595601f41d2025040c1c803104d00210201c60a0010030811000758486010070002c290130b007100701200d41c5502035425000a1901c8000400100003602d02d4045c2c40080c00005c105000412150030119264240109a60740325030510951034161031000030f40040e004c00541c0c50310f40d213000302d400d0755004049203c0341030115500d03404005c0300046070000c035034026254a000b042d550680e40b0051460445c2d10b03403986040c00b80d501c04100c55651a9800d80c0c0320f90b608080852000b120144814 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 879210440 1250 879209190 879209231
    0x6012109021207090c0905090c2b02122e09050a18030513230f0418080d0b150702060a02070302090106030c02060c07080406050c0a0639050904 63
    0x880b5620546000180d2403045405c50f8011032050784079a840301c0c0d01c6030180101c017601199280220f420400140380559080005d50440c110b00c01200d01040d2602e03001e0000b40e0740410003d07505220950184662400000e081c88a0310f80c0c1c800c400f042c100b5001648032080b44882c81040b203590f03078400002d440045150080205004003440e5001444410b00c0c001c5e1154015200c2402c2800c5942008076404040c040c54506005010a01110f800c040c00100140729080055807a003003606c0d41610000000601642503080303100302c0c502501d401c01c0d0002c54007140c0340d00700414440c2d055038946c0c03100c0b40051011510f0198040d0740d9590344040c0309409038503084440e40001e40017000500001104c0360b140c3e220109080f043e0342601c003d5210820105900c0c082e9240150100340c0070002008041e00510003406055600402e07076000c07180e59212181158070240d007210808403889844902c07100c40d80348030f0b4000b4072003c1d5544062600010000d00d24060510303040c0c041c50341d0b582c6141400c66060f120 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 879211690 1250 879210440 879210469
    0x308060d08040302041b110c0108130c0b161a0402090c09060705060c03071701030b0601031e0c020a0c21020402030a0209280602070602061f0315140601210902 70
    0x5200114100d03034003206c0780c1c17524500c0f5000a2407180008180c624080388005000e0300584d0b6022143d00c5251101502620074201151b200d901c18400007114400c05018100001406008805406d15814948560340414401442d240040402c100040e83c41c80c8410780c00c038510307410741d03500c84c030846001c2042403055040150051003400100074001c0b00760300046200b82015500da00a420450240d503030005803e0000411000303c00740042d66552003a404001d0160304030b2028002c1d041c50014040031620501507020058001405650921441e9400d88000f0140b441b1580d81c5480802100c0403100152140242b1898002010402460090b0181c4c0e00c50300d0000c00d40d20300f040b00104042d03021401581e10441222402c4000154a030000c2110f808907041500901559602c3c0a0350850841d0210b1010046102005010021522100d0454071032001041c00043c0384594414100104072300134407282c100306c1091914040c00010740024000e4039000b40000c1007001c0280b0010b50b40307424502c030 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 879212940 1250 879211690 879211699
    0x102280804031505220804090506040213080a051b01020a020d050c030313091107150504051912020106080c0f0d0501110c0a0614070912140d050a110a0308060d08040302 74
    0x16034100c01501c0d0703400503004020103002d545e100d03168803010155600741144041c04c0e0000500c0100601d00c4241c0204d58407541c001c200602d054000d0f100c40304503070b065400c800784a5001040d0b490400804105aa014912001c4000e407105000d400013941c1d0110720100902403010064000204030017004000a01040141a41c0d1035a02c01c0c02503840280c114811030007454101640032310000010021105115080143c0020070340041c103500010700000b078011140c600c510090701c07081e04291492004a82c0c1306203840ca80400181c20000e09541a0790002886600848400021613665552010310b0301c405a8110101c0c806500b0550b00418240c00c1e80c00c2542c0000950244030745002c40c60108840c0b145070200f08040d494102641c16280444045000c100c00120510a12104284902070a4442c80c4030903222612035003442e081c240403641d001e000c1034000c11441103a6404c90f01d8940c0d040c0d00305000340050041610020008080900128040d06603043c00805004060086801441e000352 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 879214190 1250 879212940 879212963
    0x102091f1707030b0a0914070525150f06061b081303050a0c06020303130212010b13020406090b09090a050601050d02160c092c03071b14010228080403 66
    0x103024020b44110248244103072003d5601241b040090f101d1406201c542042c180f5244c1c2d40c044065905d54006940c1681c903c1078850002c00303d002c41c042150080e40f01d0804900500c01501d118001e070b401da440c041140d203040c06010702442e0b61003c2011020900301e01d60190841841c10820703994458028004a080c40048020042c020001014504944589085d500072582e40d54120703101d01003540c8505a200c00c0c0079204015140c1380c1c91300f4000d00c441200004801c0b03201c0f40064031982079070328000525a00030038104422034104032a500284007034544070307250040030710001d401e00340018151b01c00d446d03681e0007040007644038100b500c107a4160342e18115070350400d440c0e002241c04034000b800c44042200c1000820745060601500150704e45504140c0f030b18080e800d494050408203100d501902d03200901803031000c00e041169030807503000703442d800d9040d142c10164000c0c5110091201c2c14195407241c010f003006442c1d05141c00c0c10403448011410388880403490310340014411640040e25a80000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 879215440 1250 879214190 879214201
    0x60509040605122817040807270c0908031303020a050a03030804020d1106270402070f020d06020904110720060301060309080403061d101b0e1f0f020f0102091f17 71
    0x882c011b005072100c440803218066503a00410a94401000c0744404803980340e910aa00409190006145120386007400c200c0142c96031b82c200e103141c100c0e004202800d02c04020410a50410042d0740018001c29501c8401807170850320301514605000e00001d02850320b41045000f80407280c5ca0707002405d50000c004036a5a14440040e0008101c040681c030042900d07080c0884140c40c0503c21282d420760701001900d0b1040c05038080102c100d0510700c1c00c0c0d600d25000c025114556450344185a20b00c841b48070700545500d168245107030329003200c02036440000305860b00548145da03001d0540341100c05514001c1010600b80c90019070078040c036400240001d003001202c0c0c2040c0001810400602e0b0410211180c141c8900c1c01d01c016910600d5001f4000c000c4081d0240d0118030030803a0354180e1102520003840301c47d00b83c908404112040751444000703280c0c1d1221038121039041c48004007204c000002941090741500c0021040e051842c040d480b0010b0440d54452458055107091166444000541c0b5140c0f502 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 879216690 1250 879215440 879215483
    0x16030e0a0f080a051902010806130f05070306030c210b0705070f0624060503070e040b060a05040e0f09100c0c060e0607020f0703170c0a06060605090406051228 70
    0x1d103e42210a4010809078510101c40c6048014030a40c05035030b0b140b1141c48200500034404c0b280002000c07880e480300c502d2458079505d40116400340d4295600024202e155091400c561191504407030500010503c000c0800c480c41c00300e40b010a40c100c196048142c8038a034054501d03214101004210754a0a80c0120902c150b40e4001910075001504002100c0c107004d40310340c0031450501890b00400c2003400030075907162140c924000240c002030000240114400c0004c0e645170070a410601c001280094188070010a042c480ca420140d5000391340b4003828000c85070760701c459140d24101b602c01da60f4a000681c85208446021846400140c03c05c2101251007405481d100211105e6025200e07401d601d00c48042d00040041c1107a0304a0384207021041d40801c1404a41c2c04500440c074184205000c14000c41d101e84034038002402103485280d0f454400c0418402a00d00981c84503201c0c91414140d8a507224000ca01d82d44007060881c9101c9890100b40c181420030100790402411450f11400c049012a24 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 879217940 1250 879216690 879216703
    0x90b0a03020c0a051015061115090f071806060206100b071e0b0907060c1e020303091005030a050105010c11150d06080a170712230a030203150616030e0a0f08 69
    0x2411000203154544443c4143c0c0c0c00069240070b23500560204450030000300c24006411f40105415090300c0007031212004081c5803050540144a40c9007650480c2d00194040c1d01ca82c00c0140840e0002d484c0c2032034480001c2c40c1002091148901c000000030349002001913094198070381c0b500c8600043c00324100c0e4140910010421102003116200303900d0045241030140c41e80781c00e10b5a000c5440404460400070768041e14465030130490b0144400d0040c0700d4035945110742020800c4540d0b07038203902c1c1d02d00903801e00145d64041e4801750600043d044080d0208081c0700720460b10107410399603070098a281c0c0200da03042e44280c80c450380920b807400742e0211380c00f500492403c0340300d8012985a985c00700c0c0f8840101c1da0748200351000703100201d034003e9a00d50714040d44011102c80b05900000c0c000140d1455102e0035503006a60000010b58000100514000000003800040d4016180c0c130741001007500215a40c0520000302409100100340302900541d61000c0c96030183c075201c1c40080099507641001541c401 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 879219190 1250 879217940 879217961
    0x70912080c1006050a0506090a090c050c0705061c0c0c0501061203090902160f0302010207050615010813050d03020d06090f0c0801150801050d050c0d110a06090b0a03020c0a0510 78
    0x2034014004002e8565000300401d0350801484004098501810440f950b4084c80daa690030100c0c5140001d54004c1512500000300c0b070742e4890302d0340d41c2c502070560b60074410160409403103414103011807a2441e41350b03403010981c600d070003000003040700034401d090300d015081c041c0080942d0b0070304d0b4020400d11144112260000e220351101c002a80d240c071080c10503401041c45403008414010359410101e200340c20791041050203800018a040d00e140c644904015045690a80b076003845030211200d9640910b8040e4040c000115146030500320759201070b01c9103122200f08040580104850f41903070302070303800240185112a000c1204801d501d403504041c0c903c880c260404905000300001d2001c111100000341c0340742a607201301d03c0d682000100600d00a15070410340300c5100340d004101c12504c90154111060b8000e140041d00704064004004240841d134000c20108441d0400400042000c01c00344d52a900d0381e402c0158683d024600101c0c68006036490240240c85085032a4030b203603480350f1008010b00b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 879220440 1250 879219190 879219193
    0x6030605030a410105070e0108160e0f0409060b0102070b07050303160302070b090f10090b0c030703150b0310060c0f032d030e0d030e030f03070912080c 67
    0x1903959040540b42c01c0d2010001d403640f121a9001540c2c079403091508510881d00c1c0e00a60344000d044030160440030100100c00955a40d2441400845604001007003840c20091901c031280d2701d04007940b5501e9000e23000c0c614041c04003404a0713075615550104001d0070040e003d041004959001c0c01c05001802c05840c1041c0540509030020440301404802c1f90b19042d04200203510715201c180a88070901c80c960600010940e091001000045100c80070f1805404000020807200c0300040946040c10030111010001ca442d2090403000505e0a070b044552121781100f0154581e0b60b0840d0030340141c00e004010131215442c2c3c00022811910341d0001d50b0007420307810501a9030a44414050314486599800034140d030004c4000c5100180c4030720141a001d03500003101e4000007007441000d1550341c2c0c421520002181e10b80449e494500b0f420040d03001d03c00b01c0d5203000d224000341c40162036241d10a0301501e07241c8000000018031300c14081c40e00c0e040103003071418143c00c56160740d00305241c1da0b0300300304040740300b9 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 879221690 1250 879220440 879220451
    0xa1112043305130503030414011104030f060b1917030c030307090609080607080609040501140a02070201081b072009040c030210020601080d051608030406060e0a020f0313020f190603 80
    0x142099220340c803c450b4804000c515540b03403621000703045403a0000d031650643d00c83d8075800b000320064020b80000c501c0307101d419400d40c8040ca03000c02a5030307241c4000c601030782174040391421503003020684800300c85407084901642d8104400903411440b0f001c00e41381c0c441c03000005118110340e000211a08484c500c1e52901704503500c0c1c11109841750300540301c1c4e6001450304008182c4514042d04850f402c54030800c0005a40c9900c00c000710f4645c0c00885107402c14680c0450858150358103c406c1e1030740108aa200c13141c2c2d10031540d10810a9003d1a4406488141c1401d00066030a10344040c803613500384010b00c10062483c161812181c0b5007070501040380604030503102000d4040c0000b0b801e6058421700805450048511541100c2e180c12110240f481800d42c840144042079080000f107008a0280002003902d5080c0220070f14140d10140c15101400d01c10030413003001d040214182c0741c2007030400c00300101c0c0c25214000909041e00d002a980d43c890281078101c3da0030a490a21a401c690b06a10706025 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 879222940 1250 879221690 879221701
    0x304050d08031e0c250c0305061b0408060103240905010b011412010b0a02010f14061f050d051803180a0515040504200a0302040801050a1112043305 65
    0xc41134402040e400000d0140c0c828001400704200d20000c00110b14034054005620b652503c000710b5441aa21908840207000d1944d46a41c0800c55240b441c7c250b8920340ba00e0140710039036403001444094205140e41c0500100d020302c40c00d40002d01e284d11003080c0050040c5041980c002c24001c0301d0580854040072405500c81081c00c20741c0c0e09404500c185681581c0781c25103000e582e034410342d2681c046550368030503031907018164460400340440004088407580760100511903840d151003240060850403440d45c0f85429800000c8843e2602c0566000ca120385600a200035159110542c0baaa03502021555a9860307802900b100c617030080480d01c008440c7e5541007417002107000c20b1881c1d43e8045041001748894201508640309403403100c1d000c50442e5000c0009000315130480d554400019400080400c1629802d0052075040115951708011040c09900200300600c500044255526110000074081c80f20f501c0c5150a014000303042d5508207144110007401c0541e01180c1441c1c203902d40300c04101d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 879224190 1250 879222940 879222991
    0x224060f0a140409061e05040506010b0304050d0f090e040302060403270b07020a030c1707060509010c150e060c120f040206160c0302062115030d030b030304050d0803 73
    0x219a810061440a20003902c00d00c0b015020201055401c1070300e032001d9007203c02030050710140c01582e5044c00107840c00c2c0b515025061440690150140309024001e01c80443e5002c030f180c0d006103406003821145044520000d403107905d82c40d807155811000e0033040105042c0c001c00c280c0c2c409d6209031360700d0280c01c04a07035100360b07200800005407440403e1420244040c0742c0b41402492004c0c001400c032a50300740d8030b596074030074050140c008415a15103440309c03400360703601001071901a200030305019003800d844600090403810814800b40c04036409640420000c05540e1010705003c0e82e003c143d81c03c5181040603584140d01c1320f500c500710303a001c180024100000d103a004900844d80207020b149454481c11400c02a86015807043d92050780c0940000010b170349403401014204808003a40308c1c3d407804d507543d00c40240c90051095606c0411541034024559000c40d02e08200d040c1810002400350002c404a403035802140c201e180c0050b60240840140010f03000654418811164032802d0000d801c402c50 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 879225440 1250 879224190 879224209
    0xf06030106081009030e0411091306080606060f1c0b1003060e04080c030c031c06080c03121c020310031b030314092233030605070224060f 61
    0x10b40950400c0400c050b169000c0d41007009858040c0c500000c01d030949400080c00c4800b40b10b00122181000142c0c2d011a0900028401e0061190482000b00350710700044982c03152002005240b08810001d50b100b04408000e0684010082c0700540c040701244e00302062004103418030b000341c400c4007000703103c1c6003440c0b103030080700107449008040035010340311542e031104142c110600140a500051110401d8001c003003001d01a40c00003000e0f0031442100c607104907030480d055074100d244e054222a0900100752000900c2c0302c45404881d8402e5541c2c4072820b051803081c0401c4000307a80d00c2d0700003c180020445140203082c00c0c2c9010364002e55007501c1c1c281e06c0050204462000901054407103403000010999640075011150028006600824040301a040340d404c442c1000002d03d036850b80345500940c112000241008c0d220103811540c4c04841c080d03c4c0700b62501744401029036807107100180b140c900c00d01c54100b007800d0049000032400305e44107a03111406000c6480724010040303040e80720110314060b00389 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 879226690 1250 879225440 879225449
    0x91e0b040c1e0b0f1b010209130204080309010e03010b031227090a0207170721020c01050f031b030709090c020105011841060409020603060d030e03030d050f06030106 73
    0x4a1661624049843c2c42c9504200e1500c1c4200000b40101c0e10030f898800c0c420203d40c49400001030344c0d800c21104000c01c64645481c5000d915105000070300400c68004121610b581090800d16076805800001034007500303122140b01d030140034034000303070f04410007003006080000171a081d0000c0704581003d850214140c5401d03600e501102c18404103425910030303401446654040e509208882c1c0d13202d00441d8071a4050758048030341e00c8290ba07043c0110f07000d59001503210342e1280b001c1c2c0351001c0460700080c030b94003800c04494018680080414000d080d1a1000080c96408984c1d01d0703180d01e403400700030340008024031590288030300f4036411310959032061148070b043e00e0078002c18012440030318200f200200240c0301d4682098507005d43e031812280c00e94001c0070121081211444a80941c0301141071a0140036013003034000c5081004010059807008181d9034442e40c1519400002203450034100c5e0031942c03002265406010004045c0f19500258210328821002d480818550361201400c0c98205e4036984503 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 879227940 1250 879226690 879226739
    0x403030305130b010b0d0908040b0405031b130e0a02040e010e06072a052a0f010206040c0918080a0c0204111204030e060408120c0c010c0c09091e0b040c 67
    0x501017000018054045194000740c0042c0c10704840d40e51151640c0942c11100700c1c02c80c003040400040c6010407140c5d0540790161888400c41d40ca54000c5070f0758a40c0300f50301d03610090b00d50010340c241c0007080260002c3c0ca80c0013001882902c10702d019007402020041180c804500806002401c01802100c1c9a41412040062010841040d20414241a2011200b2905c44c02040e550613040d02c10b00d200c21200101709407105288110300c1d003c004880109044041c1550007500421003c5050900c092040700d0400ca0081101d61041c02d0588021001c40700040c443c50b03000c034052400795840415845114800e4a04109018105030054894001d406510401e01100380015000034401c003181200100046c1c200340c1803946941002e401c4c065003402003e20100c000c00d00241070304017008011003c44003824540400d0b012910b030340c0c00c5500140203421106880e061200104000c0d074042c40319208038901d201c05540001d15107507141850541d0140c1e555003001c1c0c00030601144000714a18005030322070 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 879229190 1250 879227940 879227963
    0x303030b182d10060315081e01090f0b090c0405041218050a080f060708060a1e030212060f09031309091a0103030f021606050711040e1002040303030513 67
    0x52000051000e02c042400081840001852181280349046000d5544880e64400050030a1001002c40e000410a28804414a001000801808201050024140c0c0c410406010307048240d81d02401040d00300819a0b004452410148070010041038007940c00102620f503151035090400081d51000e56029000608010100c01d02d14043c5510103400c9504840b280240c5944100054000d242540481419005006000318802d028002654041d800e410808910b007002c5000c102c0007a00c60040c2c0340c05a210a21214201510141500080d54018050b0821a01d064000340d00c0c0c00c1e064440c09000e0780030501044a44001000b1389103501c01c011425010a403a00c1c1500340074004407501620388911070010003550214800545004e107000741c41e140c583d988071900085c0b8103500452039940d2804000c809210850b40702003107981494000d1141a41071740b8008c0080c000b4a04008848181d1084050550850700ca40e00500201d0303000c0c0e1000c02c200c2d0f981241072212050782c2c0c10700420703110194 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 879230440 1250 879229190 879229201
    0x302010f08090106080714040b0409080307051305040c0905120d08151507050a030207211212150609050a0f09050c0f12010f120b0f060105071a010303030b18 69
    0xe880142d8001510300001c0340b1260f54031616400d0003a0f0380c128181900d40304401401d581003e002e4500c0300c440a0f6000c005000701070700c0d4450030380405000d4a042002c0025405c50b0724010202c0200980320081007001648040315028018501522a2a00845100710f4801c800c041c04036135103221501329180e01c0510780d140d09003d035010408a8543d540485040d00c03440706844c01d040940301083c4940c3c02041c0003120340c24040d1400300c1692080b000c90402c07a10055010408500b1045042d40c0700e00d1588451418640c1517900c0e0020514a411a6280c5441582c1c0d4028a0450328200c607400e84031624210b8483d028041403611a0150b06002c0043c5041086200c216901c03c40d4004d6010141030704056580003c43c0441c3e204039134452003000c5a200601c914094903c1d0080101460400400c482c04d4943e100b0000c043c0041151181000d030500043c00d9902480071510761503804010138500040400c4403030383d6240b003030005400180c500100d140080c1010007201c16645002d150380005039448 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 879231690 1250 879230440 879230447
    0x1090504020c01021e0306030c06160807030e06070b010906050a03020a030b040f02060f0406120c021c021606050c0f031309050a02070f1a1005010f05090303120907031101090302010f 80
    0x5101c92682c15035007081034401c0080703041940c0000040281d0072559a0a000d0101480c0442140140d4400c0b041040194041a0101c0c80c0c0c184040d48400c0351a01d848543c20141d0b2009072040c8040c0e0031940001d220400c200b140c8000a0584003d854100201c8e034413141440b42501c503a000082d0041140e120910104c0d22000845510912032010010384d2240e50b030208006404c003401c40c0070460000706052180075001040d990304c0840c80101000980180300d4000d591b080001400d00e0b544018210621900e80f00740305580c102e03040007944000007039403008002c00e0383d4092240a18079000d489409844603a01000b2a01180e407100100c0c182c030740c01c1c0b00311000285006042480300c0ea508000d21000217084401112560380640018005551103002070281007e00a0020000341c406400600844c0e80100c4103200484043c81d2081e01e85400c00042441d40c82a010649501100c103810000b42c02030004143d015244240701550b8a04540c900644030958240070090100e00074107568100c1c11312 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 879232940 1250 879231690 879231697
    0x1060e090c01120605060412062004090b010c050616030b060702090417090d061a010c1e150f0618050f01060507050118030f1b23030c061608010e060109050402 70
    0x103450f0001281c640c0c540000319990721a9210401082403032000c2e13400c0c0000c500c43c0c0b840700041d103520050036141d0310b408020188140e0203000c039060380d00c0d4031032030059100383d07130b550302c80c5a001c0116070080c00c1420030404014641448080083d040103099011414620265101c465003d44111110b4649964841c03403280401d00001c052001846110100c0e502c0c44009030388903020b001e0000d604400580b00c100c11403084041c2d5414070120818040c0090b5580791070000c0c0062402011b031004045182c0041d600f9600c648400c411400c20440b08064122a1300400450300b26800740c11005441420300002d03600202c03043c40e04582890010002c0314002c90080070284d01c245c0000440f01c030018503c2e110705921450940000e59000640041d207a08401d21740c000d44103a12600030126207554812181c604503140501f5020a029450389040e50f0800c20b5421550449040e1445480c180e2450003080c0303540c900050005030003a000041e81c04c40c070341c4040e0041d081030350340020035810041404043d50 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 879234190 1250 879232940 879232967
    0x1c1401061d0423070c0c0303030219020d02120c0a0206031e0708070219080c03030403020114011e0308130512151e043002010b0a0e0108031e120106080901060e090c01 73
    0x141103185280044d00c6c0001400165100b80c80040c1c85200400c1c541492040860382d6005550020241c40b480640004401e0400340d4000f95540d5541d0810014900701450348000071b400c480b001c0180000d99215211001c0100090304401480d66140c40003141c0e045000d603450009608050345e24040802001c1c1c0c07002c50f00d40100c400b5480c100208040c0c0380383d03a002300d0301035005075568034000032403c0d01c600e211401040801600c0d6141841c11108075119912031100030440f2000041442480360481c003402c0007040010107902209a40c5d031002c075240c1c0c0c0e4080e10124141d0440c1d000a15007905040083d0360082c510b07400078180d03921961070020151110030b10080303075181c420700b580010080040e0b00a005000d43e001041d503403520414010700902641001d04074440d1140140300402c00002912003501c000b1010840320341071001c0c0700f41036209036040f540500307140a001044081d002000301340203200c940c00820103544d032040042d800000a075642111500034401240480d0302c03400e4150f0541 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 879235440 1250 879234190 879234197
    0x16090f1514030c1f0207050303090102070603050921180603010e13061d010b0901051e13020412060501051801030b0106050f0c07080a050d090b1c1401061d042307 71
    0x1c0740c220005409010954800407818111304102041d0b59040c4202070091100f60010743c2012030540010b0745601c0c0782d004000c201644e44000039130704002000032150411507a02c241190301164501e000303d42e484100002040020100c4c40c1c680fa090020490b8100c8101c00c14401050300c03050101e03800501c000c034050b203905440d0300102ea0201815a819081c0d410200c2c000540945980700707021035000143d200c14892600b4014581c8094045103554000c0e2000b100c0c0b102c03035103400100d03400007401143c014403040d85005000328100505684424103a6200b00d4503000418100402c03545108000d000c0107190854440042000b88c0c00740024101c444d0107807070640c0c10200c0c41c1014502c5e0205907400540c4550100c2d01000901800740000840010146407038040c460130100c801241340300310b412034404001440c2411001c1109603005450881e1444410442941d40c0c2d0401011004810085144494000280202860a4403644100d03052109040c0c0c220500e0f030005040c041001008001030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 879236690 1250 879235440 879235453
    0x15070201090605090f0c01110604110a030b090d09120201140f071407060f021c080a0e160504060501030207051b0315280506131d16090f151403 63
    0x55043d00400f8810354800b001424003e000120152074240c40c0c03049503050159014002c88400380c0811491342c02504010030200c115500300c0495064504e60780b028000255074010700c4004007002c81e160121015962317890411340d484101c80c0f10408103521009003c60036800c007140701c510044001d002e0380038051980303505001040c2c40706640003c1d68120400c4c107400c40c14091007030701c0e0800d1002001c07030001d2000340340300200d485940d18951091941c05c42030008880c0084c4004903607030000e031050003240d4262142210b00405814080c1183d0064500c1141011000300d0994800d1080d200140c3e001001001c0c1c61248103d50f03e000c0c0c20b9464015054000c003002c0c1e101c04142e40c1205801601510350034101070283e003c1c2c02010b2140c030f51a5800141c1000188105540c0d90038040c08807901d180400141d02c1c0b02c401000000c410007078840d403020f0044004510f40b0302c1280840700112403400c0d1092041104040114044481158111010b120411414030819102000001712100080c2c1242e90 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 879237940 1250 879236690 879236693
    0x906042a0305010b191d090313122303040e041e0506040b1f050118031205040509151c1514041109010b03060d0c0b03040f1a07021507020109 62
    0x440611604180d4142c2e454002c2c00700207003440600250b045d42d400030303a0030209040440482c040342408800f2103100d036000c800714682daa410b004650700f1440e4580d8801c01e290f135a100822005488800c280d50b00032594050138019000703001a0160903003844040c52038a400c20600007003480b80500290b582e54200440d0040305014003145521050107032000b01603502d494a80b021440744020906211808400389408414810140c85004e07100f00342441d2551201c0003a59030310720181c03a1310280110302104840b0b0035503900040103106584041d100c0d840c0c1541d0303041000740000000c1038a950045640b03c0e02c1d586040407050b010382c085114800c0d0400103a40740c00780c3c40a40d65070ba00343d200255074400611041010112003489591070030366081c685076152010302e1540c0c5c000104501c0c040c5103140d981074108801c0301c8a08000d0008010220b4590a083c03c0c030303081400c0074170001c0b181001504001008480c50b9110244210025070040100003020041c8140c0780c2c134090908402d540d2a030180a0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 879239190 1250 879237940 879238013
    0xc050301141909140a05070e010b09060d02220603291f21050a1a010c0206030a18050d180e01061227050105070314180c15030f0f090604 60
    0x1185c881c00b030f5004050503400c01c02d0310941c91006900401c8883d50400c40707880d0a4680001791502c202119600503202c202140c901c40300c00e0300307061a01c080b0804984002c1001e41d0183d100b8070142134111301e1100070202440003d6030701e405204001e03500407001e80c0a00b41c030190607109503200b804240742400d00c0e004900215545090074000490801c5d40f901d003044a40d07407a5104d4007000f040040107154a039455031001070010b429504002c1d010701c80020000c5e0b05060755401c4092801d061034a180d902600c40d082a0740c44240703c803440b000080010742550200c80040600c04103450200c190307070142e40d1030303c0d00c1510010381c10000e20803d80c0e1107403e00c883c08001c84103291081c4032841400c080c996020710702503084680041c040e030141803515074901904040180d10950010310210042241e00c603c910561074030f0f2078881196880b010403146c0650002407003000d180203200300c40d4080300c180c0f209403044450b110111044403580c2d01c10000039001ca10325802000002c001c48002030b0a5084488001 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 879240440 1250 879239190 879239203
    0x13020c0a030c030f090b220b0a0206150603281805060a112502031005010b0c060f010311102d020601090e07030201080915040c05030114190914 63
    0x58000c81c00464501c028944c1000c1c0c1480b14492900e480e01c010b42c1171070411810390141180c580340c5440740340c00200d1580039208800001c0d003401181c903034035090154402581e0704c2e0103d40c545000003181013070840c1400c1c954103482c000c1c141448205c80d0043c0b142008258840c0305019690515150001140301c0344d100403e0181d41402036014121501d04903c032030098582c2d011065000603030070421612043e900090340003409400030100c0402c8070f00ea00000e49048003045001c049945418000981c074070002008180c51b200407000c3d6800e650b01c8910072180500244005402071500000c0c0d900a4076145044a123100c4840c2020200c03003180004925035064060700d201800680103c3c030b9103011360100200360050040403010300070040441091501c0350302c4c3e44402414008104040b540000c002d2007144681625112a065145883d0400000f42801032080d01e029510f01035050030010710649895200d402c03080c916810400382e0890400c0181b49a60085e644400e04038003980e40400c1c03e0011 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 879241690 1250 879240440 879240443
    0x2703030813020d030e011b11241605100603050c01050d0f0c110c0301060b0f07050709090f0204111305100306030204090812010e24131e050a020906040513020c0a 71
    0x1903c444200140026003841c000340404521f01ca55a0303405400100702401c2050f00f0a000d444c0c403a0380554078207610b81d820f410400d40b002050350204064001401c111200e07030900d03019070221219040211001c00441d20103001c0541982c000d41c2100800c4d50055000345120300301944000740410510540700111051003480e100080c0b28a848141c01c0c49040125101e042d100301c000f0032500e4607090410075148a104003000e0402d6002c00e040040c0b10003400aa001424001c00a000b9440ca501c1d00700340a11202030120303c9185000003000d00d08250340d068030b0410f05030781075030340c00541004208100d13400803503240c908040d02c4100100040e02c4a024000046100d0444a92201a401220400c404058128800307180da000c0400008040d0380d0b000d80e15070600380031610089041030000c00d071494885100d01e5121401c3c85400d2483c0c0502a8030b00d0003c2c1c03514841000282c9a00002c50240e1051404490f8060b8003808103000701e00e0000d11824240d81d030010300603d007005000c0401d04180a10a0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 879242940 1250 879241690 879241697
    0xc020c090115140c03070f11150d090c0302090414150906040303150f09020403060e0a05030d0f0615051306051c02090d1703090f0604020a140a051306062703030813020d03 75
    0xc0200103182d0080801140100e039200c0c1c991000074009000c41c05200ac00c0b02c42e090321038810200707005829504501960b00607040100501d01814000e4410910580090f0300380301d4002081d08180c0742c00c0d00c140c041c0310008040c0002da141c0e0f803011800b5202c10000c031140708042980010303800411580b0480140720380c2c9000360b290752850a102040300c608025071911904407030350060004034040b08542c80414003031388c0042c00b900c00004c000c000340b901c0e0300f12801d960031125603911a9030300072010b00a845c880e070900b2512940c803028115407071702424641100a0302c0c0d4104d42c10b5503440c150080c00c1805005040b215070710030580c441d6040c00e440306071040300c80540082485001401400042e904d0704440b00107141c00c3c20b0a0f8007007141102584110100c01c002c050b4202890740e507040c0c07054018000100755407aa81008103080c0000c009034030030315000c1000c050020100038001c580800c2080b880b000541c4900b450b54070161000d65009191401d021103403504d2000580c1c842c1c8603d00c1c0d042c025034 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 879244190 1250 879242940 879242963
    0xc09030102132103140a02011e0c1205060901051c02060703030203150a350d050a0206070e01120b040209130203060103060f080a0303021e043b0114130f0c020c090115140c0307 77
    0x4ac2e000c1c1040114807204142141070008011068441215450449100342d8a004200049032500b40d92280c480b00000d42c0301e100000c0035001d1642c1a000380d80182c0041c00d480e0703484142402000a10b561030705c00c104403600e0b030354180348407032600122180010840c450120900d6500c0306025040c82400c05080000c904007203101001030340c1c10019582d214005003400d0704440b421b03c0c0040d1015030b21a512061007900c0e0710104407640c48a4054541c0a20003924050840742402c8418019410450b042800240f0b008000201c501c40d000c07040341128031890183c000c1e0015500c08070069802007070491060b180c07403001e050160048d0300041000b40703080c01414500710500164007400f10541c240b241d5081141c03a80c0d040a0303600b120180c50440303100381c4a142c10700d02d0000110740d0114901c003042c2c00c41480c0c03003041b4040c50b003c0e42003d00e1040b816429074a05034414010818181028001c101c103034030081c40c3d08a00540508100d4041c8495031100c142415200c6204918542c0451000c854000b0400b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 879245440 1250 879244190 879244211
    0x80a020a1e030222031a090307061d10090203010c0314040b060a050607050114012c1b0403051e010c0903060b010c0210021f0c0f080c09030102132103140a02011e 71
    0x39100e80e40c441092800a0010306002074900e23541d0184007009062036070b40d800001c07405410460080c401810100076200741c1814644c01c174000b48400314050340a9400c05c2a5944000d1080c410103035a041c21445072409511039440318072072010700402e0203070080500d40003c0344d15a0764002900303020703102310000b0a9400005074040201201a801861682443e14032100103504549101500f104031301c0118a03140e03940300e0f41008623000c210020040890010300401800710200351074201d400e4100500340e17082a40001c060888040340301c6640081e01c500c0e01800010f4041e0800c0c400e19005140001c04220b054002400d96601080c5550141c0d00407031001d01c22102d266210400b042e64608100302c04c140507003000e809000451000c000708404900007400002c5d404091f5003802101400842d101c41c24181c0e40d00c680c1d6028051103130078800896422116440c3c407040e00504039410744e0f40c0c003044086004605803503004090020b082d55282c100602891011040c02007440ca4406004102c0d0340f804d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 879246690 1250 879245440 879245453
    0xb041511030a0c02210a030f0203011701050114090f0a0605100815150417012a1b0c05060c010e0f2503052d0709020703080a020a1e03022203 62
    0x741e88030502590410913407400d620090507080410491740c891190b5407070000d800c01700c1c000d048190713206029603c040008980c1ca00d030300d04030401c00003099000700b01c10b0b44c80d50025a043c00181d11659484200180064185030b41140e1107070700b0005201011405507200e000240012014000003400284407034100145461420404000010242e40b10107650450b000260514031442c007400e0040c1c040e49141d240501c03025400700c080c01090031780ba000701d40856000c0006d0b0003800c00003c40022011034240411010451081041e9036100f013038500c12034600f509108903900840d94500780303950703600221501c0040601c8a90030a9403d0303c09000e61443c03841c2500c0d121031141c80c0920045443c0d100500c00100c0010700545d0780706900c00b10f00d0700d0681c00e01c001d5506c1d42c002a10515280281a00000d0401e00b61300507100c007030720a8542c4003040ea540f01e5040220b026400e18a0005140c10664220000d449040701e03881c040b0320715000d0714045040d112440a0113500f50900e02c0c4d510081e4040051046 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 879247940 1250 879246690 879246701
    0x207060b0a06050a0806012012070c0e2a0f0c160902181c050a0804080c010f052a01020f09040b090709031223070507060305070c0b041511030a 63
    0xc1030f04046060004680000b8542c400c0145003a05200c418110000d0791005140414024000281191507042d20716280044a4000c0b40c400c80b03055891440118801c90040e2181d03205901142e8810541c0039017a22040c034030000d0312030540d070400303040040841c1c02c8404001003081502da807000b00021740c00301d021900140016070280c4051807051080d035142804039001f024000c1c000b11003010031401000300c11800100628401002da102d040d0000c01001601c00241040780d88a20035103401407040c00055030220329102c000000602c04000d04032021000907051122201c1600040e0724181640807940e00b20303030100d0641e070b0b81c15002080f810303d10302d86402203408099059640811034284071030050240c0700f640c04000c3c06280c6107000580c0040c0704688102d2900070034580d01050000034180142183e000d60380541d107500070014040b8045000c0d005090003200550784002c00d40e21113440700c0c0350f401c1c4007400c00c070b03502c00142c80780855120080c02102d100b400082000c40d90303801d1a030a110110f40 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 879249190 1250 879247940 879247949
    0x2c120106050d0206030402040f09050703030e0108010b071b030c08010f0f0608031209030f070f15060f0512011407090e10030b0a0b0301140408190e03071e090207060b0a 74
    0xa06280d818401500c880c40b2404840d541510300382e8881d05d607440058040c019110303107021164507290540c030500038000788030022240241c0b01c01d00701051f24401120310f4242405200f010f03034001c1000300002246c5182c038140e0100028144070310300e601da503100d4010040c41d0740111203c0c0c0d10740e20810b6020480f07206140003817100e0300c8c00700001850600c8403a01d9004001200d104245400e00003190b40c2d174141f085408601c07813500000c2c2d5403181843c1943c690700c045001590f0284404d40c45440342e8040e842604261105600703009010b504d00000c0150b0400d003085228090f54858000140821220f041c0d01d000341046e48416515904000785958008070081c81c0e00900f0010744020804188000166a045603429102043c9850442c000c2405040d40b001d214036030074440d0042209210a55015040305280a840311080c60601441112034001c0d401080360726402c10b0008202a80c61110b182110380b4041c607410041d659254030751003ca0708200380a4401c1612010303003940e2480c0c401201000391 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 879250440 1250 879249190 879249193
    0xe0c040902030c090408072a0501020c0d1b0314070503120a050301030305071e050a0b070c0b150301090c06030b0a06050c030a200d050702030105060102060609040605072c12 76
    0x44803540c00281d5500d058080041c05465100081030034012000110341219402042c0300213400c100d0011401039010340007040c01c1c01c111502011510f50300c080b070a2010094000c1c9004050100c948074802c007210080409450f06049000c000300140c030851684070390011050207806903a2411060600b8840300b000a00f003012000c2080c410801d4100c2c4c05d90303042d00e40503c1c2c043c0e151641894064044184554004c4042003a00440d10410100040341907030300740711b91000d141a4482d4070301500d00020b4a9401031280c01080000340038080d100c190600f403003100400100c0d03094042d41b500c025098040e00081d0020fa1184505100d40c2441650040204000c1c940f151911481031030564490064101d20020400d06032109020901040d500b0758070700004400b501c00801c82c0d0303100548242c3c04280b04034065405c00c00000c07800e6002142c40d52107480094810b01d11540c2f03590740d45005100040209040c01400c0142001c416509580070080200185501010807896010802292880c0e503221409 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 879251690 1250 879250440 879250451
    0xc0e090c040f0306020c0309040204080c150301050a05120a02090112110109060504140d02030613060b04020301030b13030522080f0f030d15091107170304031d010c14010e0c04 77
    0x40705034180d40812213402c048010b86070b241c2d109455045120301541190300500101c1c010612100c0490490005101101c2e10900186207a4820401e40001d101e45980005644010002800e080d0051030001c82000255034580b000c0d5400140c2c005420380046401801c0c8018090400152000609480c0000d080042620789412002030440c465800380c331440b4000140100d21945441143e480300c168024140c1707007249030203496003161a41149040d41c04c10b0400c03035500d031346040a1080343d05032504449503101d1980d905807004403115504104508001d01004210a0000780a22000b010000310200201c800d02c0e2040d81458190007a1503001c580d04007091024412100000301c52186810382c102082580c0d1400d00f44200c19081e0344001c00700da04141342107040340c03081d00c01807207010b100d8a885101101e0115541c6118007080700c005001c981c446800d0317404000b008010f101c1c1850705140014003003107035a94280c41d1846400d09440e00760f441d0107414900c00350500c00c000414000340c4d02000b8 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 879252940 1250 879251690 879251699
    0x602060903132706080c15090f010509011806030507031b0815031f0507140a05070f0606030204020a030b120d0e04050a06080a0c030203150403050304140708010c0e090c04 75
    0x40003580300d000340010008000d1019815405603c0c055044014000c10102d070f43c4032045504c4980c821036091180c840072020090125400041c7e031410f41c00074104480d0303c43c0160055801d40d2000c1070320750501c0321071842602400d1000e85c000010b000a03a60106140c14000b001405841c503c01c08203005000442252039040c0e030040040740e100c0d450050001c0300d41d40322400b2030f00340320702c01c0c1410106180c0b003151403204241c40d820050140361700f5a40d00041c2280307000301031028065404010000752003080b4110104916200901e00c0781d01444c00010213650303e030b00040880c3c0c003429190002c2038030b4014070041842c09401405442d41e02001500c200500c08000910308907481c03080b6441990382d14045415002e1550205003d41103040c01ca50001a150400550310900d600c0101d200b071040d120462242c0b20410192401035030702d03403a00c0d0f084d601c540e030303c3c0060500c0d101c080083e01c0c4511800040e49103070902071030440300000e07100c80ba00c40341c0413002d01c1034038000140300108182c1304000400 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 879254190 1250 879252940 879252967
    0x20c0d06021e0711130b03070f0f0608010623040509280b0d06050a02130b0418020913331a0c0307080a111f0b030708210405190602060903 61
    0x40703032994204ca00c00c050304454103507200108940704125400d23109900b008a40c0c024002010405e039244c004c40700d5044c0340d8600040302c0f00c00b0300740030f1480000d041404c0401d50150002139860000c80c28000a4241a100c1020a441e4203088a91141c0c2c54404403001c0c00050400c600070b44000141c0e003007440032010031804281c04010038072005100648d02e400141c81182603506072071103014154000751105275240c2c000b45076500540200c0c3c01ca40040095441d0052581c800c444041c03102070a00c5542c604003e00203002410341c5103890742416080004001120071009186224640b1003000028242c200110b40745016100c0183c190103460070000c0c420304403000815141c4142d0300401c4140e90300d2002104032107440020000460a01c40d050040300c11040b00d44e12403465021061013004440e0100c020960344180301e02c240e0034940c04c080745403110103804031558180c6003449500280b80c683d5400101d0b1818001c000c0410300729424220521a00754144041c5403c00a041c0045007810310851071803 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 879255440 1250 879254190 879254213
    0x3030e0d0c09050a020304050616200a0b090105180a02030a081c0e031b01090b0a0c03060b0f070201110d0e0d060e010e0a03020705030703170901020c0d06021e07 71
    0x40c420000181624100100d941075140904640c03a002c1c0300b203080004401c00070350415501150740e4003c90000a07002440c41221404400325a640c4095620a40c0d890300300c00749040300c0c080d800e800fa0414000c045030b03048684500641e424000003401e441d0004050140c181240c102d04895000308074208050380c1d001440041da6904200c200d5920000c98842d01030000070464a4070840307040c05080c000c02d090100143c00e2807000000c9c1d204900d116030781214204e820026000b0110f40c00000440c400c825241d108000c0c110290500180b880e8440740340c2030054002901903000d5560020300c0000b1540e01c6010f0302c0d100c06045004100728401190301034000a0180740700c0707001c1d07040131540c4014401d940d0020502e200d51240200611140c0038100d40c1c03104000081940035124003040018582000a05d540489030031080a000403103082c1601e503650343c0800c0304241140b240c0000140309a503400142c80d2140c0c4120300042c1d8454124044031340410901041010140d02807250401050154980 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 879256690 1250 879255440 879255467
    0x504050f0301020903060106030c030b0d12080603010b15030a11040b1903021c02030610050406020307080c150c030910110703032c03091c0305040e071b080a0f02070303 74
    0x150400320000102082c020f0060081241c0d051107810300004803582c01d0750110402d8903c940c2c0501c55104900c06009600ca14000020002840c064030110000c0c869100160800401400450040a1540003802054408019600c0c2110010900641901a00c03c0502e0014850103290411b840c1460101250148e40b080c0d0624074503c002c0020301c0c1c1e1003541200e04c03a00059005189a10740603422034000c0d0411214540164002c5800540850148042d107048802d00d41c000d5250500c150b0700c1c0d08440d0802c07034122090313100744001200d403544035495891140300324003840d90300e0745456003a05180035103d03400c00452130f07d41528580000c407040200c4086070703010b0802040303401142020014040c100c2082c0d0203c11130100c0d04010304003001c03004100001c02141c04001c045007140803002421800280100425410401000b4440c810b000d20742d0320400d42d0800030782114011032500c04c0d100c1000130454003280c00040c0b4080d43c6400001080750221a48018128103080d542d000e4101007030b0815 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 879257940 1250 879256690 879256699
    0x70e0610080c0c0a0605010f06030c0e060a030b0d1205130f0806070305180f030a0905032a0a030803100501110f15090109080d06060801060809070608190504030809120406050405 78
    0x60454440004111364001598025010041907035500c420000940c4035004401c0003d00b01800209460310580100c11841d6008004600d4a0600789083d0010210703001415080b4444101000100e540f040b507014603150507031960303a5103551400b0020144400c0c3e400c040740074410f140742480300602c0040d8465001e44d150600191a440b402c804940d40c000401818960b407151050200c04500048041d000040e81900c459041c50b8444040545403007a034181d4000400c109440c400041c43c1102d44054041000380a24141a880e9154590158130449824080c2000c81101f00110b5030300c03010414440c1280130291001c00084081c482d11009511088000c40803000e000c1081c0e5402948040c05155000c8142a5100980b13040c9401038016071080300007064140000062088c0240045071180b00d540010709291800c20030255003640020b48903100d051304140307410401021a206460146c1d0198a40a92a141408019150041e040580880100207000c05c2080c41d400109481c02e41f40c0445 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 879259190 1250 879257940 879257947
    0x3031c0c110a1202061501050f0918010e1b0901080406050709180501180b0607080a1803050a060b03010209131a0a03080c010e0d0e06070311010509070e0610080c 71
    0x1039085404201610380080035010b404100002c000d00d0342c43c0344404203a550242c1700c51b6603601d00c1d110300c110b1070500e10303502149040060301124101741000385101c02c0c1c01014224152044550054514800d812148001035040f0500020140041c8099950801c0c4a01c0b030f4a0200400c00007055210050030044c00310340c8480c04180002c3c0140300c04030244c04a0309131003805804201b01c240160034203100d80320211300044401d0400c0640342c09044901038020307064a01d4100d0703640c0c0d0300d4091303482034501c0420400d140400a0601d91090780f808021402240104005141c0e814804211216190503501c00d130704c10482d0305140d85a1105810044c805070f0000205070307040c01e00c0483c1020348101000d40c0b16000d01c501004100403400038003c0251940000c1007407007804c0e2034550f514442910b00d0404078050087d4241285484802130030080d01c24034028902c618100780c080d00f50765040d1030a00f000c0c0c008050a00054500e00d060319070040040381ea070369240024281c050100d42020700040c1039050000f = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 879260440 1250 879259190 879259211
    0xb04080601091a1c0f052d060628080303011206140f01050d0302010f020c151b071106070c0f091410091d0f0c1008162307060609060503031c 62
    0x11790900340e1341d40020643c0c14903961000240300c180402241030404040c0e95803a50310604e0009000c91080901414003541c0801c2095034400a01e041e060000c2c107030010180118410005002031030082c0706444561100301042d15104042d80d210303240801c03c01c00d4110800189a400c1888181180c1b0207503601040010103080407400361600c0c41c00040c0d01400000c001d0002800003c1a03400000039980d041c1e080d4940e06894203444000711310844001a0030b001c0d00d0b02281849810340d0120300018150791804c043d0780e41c0d4a034a01c400b980207010b84111058100803501c0c0a000d8000d040c104002e0a50813440d0a0351010b5900055008480c0d005907211600300c50051102c01c000c0c181c07842c403011180f1040c3c030840d140c5d9503107213581c91090161814ad458400000d0083d000c143c054494a10b844004012072402210383d01e0903240320422220400346480445020b41c030040100300d0080001085e00d038103005210007950790581c000c600a078810041090381c45600070040480d40b090200101c1d040811 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 879261690 1250 879260440 879260453
    0x9060703110f040b181c0b071b06060e0a0e07031209030b0108030408010f1a012d0206060406050a0803070305030606040b1810020304060c080906040b04080601091a1c 73
    0x440102d0035411200203808560707404000054510385004000c0b01804192150503c8540c0459290201828204403542c00004010300f01281c0d00011610344400c11604281e924440c40c0c001c030105440282d81d03500e041c083d01c1040f4046a500050030714041c00889074070b400f01a40c030b4006101c0500407290403484003c00900c0788003618001c54011856008a584441c0c80940781da1003442500c401c0d40c078050400285485d107020300100369440800c50002503c00000642e03a0b081e424040d601d00c19481440c08071500a010034408030070b0890b86c01041d01c0c2c0b41100500c030459280b038200600c6003000c20000c103c0240c2c004100c0d007820b03915180140d1280c03120341c040f86d9203001c0e9030841c1503040380c003041c21030364068041c0f0f0381c005000c1e0407685210070400c80841030340c42e171185001e49000100311000c640c0114140e00e004141c05c21024096620f85540d0700c8072000950465000500350381c0120004000c0d0240c1801240000310b12602c40f210401075840c0015048500300e441d803001d6100c10f42d000303014481ca = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 879262940 1250 879261690 879261697
    0x6090106050a091517030a030606030c050f160803130c14030d050f07020d350306210f0c120105010b09010c0213062d030b040f0c150e01090603050906070311 69
    0xc2c2c81031705500d0300703440355142038498012107a6480001c0c60700c1c0001a03040c4c0300b40a244558492070301e4051031b01450420001407507109003103207280c4040b4560448000340f0220300941c407889515444264a070036903d80415041e2182d4000807010801c13031b42c1ca10050f030f004507180e90600240c1c10b00e00d5a4550096000103280504e0364080d40c040120f022040510114502e582000c21001e8040142d02106620540500d02c4218050620310002d20006400341440c00b1130a04414203c1418100e80307000402c05032810850625108854004408400041c2828000c041c01211844000d20a40d07040c840d156025004030202c150402010601032802c2d9203803074200c403584202202c818040c0d0ba46034118a6000c0e210217825800b0040300d171301d40d03445002d8102201403e9035805040844503440301d4448034a111a15070702035400041e216000036a800c81421410b1a5080daa160b4910070040e400000d02500207560000c8145030501d410041c034000c010035401d82c408000c0c1000181d807000c242a58803e0300 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 879264190 1250 879262940 879262949
    0x1503051e0103030c0606081617070513020a020601060c030509040b0111010207050c010e010207051c2a061403010e04020919020409060f0b040602060703021804110c06090106050a0915 80
    0x1403042001000b4940c4c040a0900c805000c0c51040c86030603034480c40300c5e540ea140700c1c25240ca0501d04010500208420000c010b90040c1071504480c00b440d1594001203440c82402280b81c0201e40c0020a03c04154045c401d0364010035280c14190b000c94800d8401400c2841101140da00c101e9403081481d0345a030180e040d405002071440000c40d15242a4500b65541d0840341a00e03502281040f5a800207a40c800a10f000035548090320318550594121411035804441c407008403000d9540c00844522543c60031500c0452203504c00c81031015600e0081c010700014aa1844010080300800044c480c020501402c44c3e000751f4140e6280d1481d5032101040c01e09407040c0410014a2400010000b0346446160444820f036480c0c03c60404d96155181d201c02101c0c45588280c002503002000001c0905000b80c0c040d00151031b0b24a06411000440d60029080b156072480645c580100415082c00f208410881d49a00020060080207080e0808000130103203035952080c50b44080d200c0e0108510500c40c00031007401032 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 879265440 1250 879264190 879264241
    0x304030503041e0b15152a0123040b01050117070c0f020915011202190c030e03011e0b0a0302030c041a0d050718051510110709020c16150305 62
    0x20304040b141740b13540c900040f00380e07031181a030b00c1d84500411060700200c4006000c82e82e55054610351700c149141080300750703c42c02c410556999111009805d00c00d442c00c0101248010851514905860259000401038006c14104101305640403140c82d082c034804ca4100444d814502c501294925000b403490b140c000d0004e4100c1d0b0303514248030328074800081094512109888240034540c1c0303181c42c04200c0c041c400c025402515900084410103015092041c4950b01074540b00c00c0e041e4070000440e0945a0400d80d86c00c20301f207280e6840810b000c00d8400c04542d04010be0702d20040ca840c42d00009d5860a041030094411640c4030300c2200d140340502044010004054000700d82600642446070712035100b88102043c5d07d41c20403c1d105105003c1c444c2c4e0b44180444002d400000c1c44071010b00101d00d02a4480409010010481c00350262040101c1002441014405030741c8000c904211030a10f01c009481c80c0314540d4900d02800203d01c01c200d20790f05a6203034980051a41d0310001c034555456141d62021020 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 879266690 1250 879265440 879265463
    0x1407020d060b0103140c040909051011190203090a05040c090806040f11090421141803070501051305090a0209060301181407050a080703150b0913020304030503041e 72
    0x1001059001a802d600b42601e040010b20168159102d1015085484250000e0f04101c14801d0410a0b405403000070701440440d000c0240e1001e0700c0d0106c8091001c3c07108a51070215000120010720211380180c0710107403025506080c50030001c1414084203004140c0705545510300716115903c1041414000c1c00c48001f00c0e406800c01d0704240141d050900c0d01520b58400f25800a105424070076070450040390310034042615495804003001c0c580ca16190341c101008500816a141071354401e001d845002401c80384109107840e188109440c101803603000e40d051003018400700a0380da0070310b42858110740301601c40c1c0d0341580d211414140248102c6c801154002008030002c2042889044000c3c281d80d440d000c2040b04050603039071803804105c01c0340d021001035800c002100d9180e11545507950031400505000ca009400b480d043c0c0c80b0042260400e8888110204110b00d142c5000801269202c411141c03c43c61410705440090030b074800284040c10300e040303407540c040105c40da01c0341c10061790f40c00c070980e00c40c03 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 879267940 1250 879266690 879266693
    0x150604081e0c04090303021c021201030602210412080109050702100b03210a1413050f0f0a181103011a1606020319290d03180602150108010507020703031407020d 71
    0x94111070001e0881c2400380d8074104005200e8400c468ad004d401d6446600740740e1030340c0d0702e00700a580030103c086411a01004003586491118001c035002d00d00c50700f400c400e03256444078000d00d170000503480350014a007404180600c031600420b602011403035208010030303500741c1d0001183c51f2140780d441038a289440d45609584c0c0542000c06055802c82c40e94940d050390709000c6001d107140c0140088021000b5810000300914500140b040c280350f000034118061150740b0000086203a019a4030291541c040307009802d025402d2840b034146049400c0b0034460031541072011018802e01412501507003c81d0000740f482038404148488100b080c1d2000041d0f5403464480d002c1d8002c20201000c038911a070508400040100400c80001c01c01140000e14030b040310304410801c844002ca0401c03d80601c10681e00080e030144400c4070000107044550014095002d00041d43c594203003050f03100600c035034501828400f030642d0100f41881200e030507182c01c0071a224941403241203889803900080d404070f40c9a14420 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 879269190 1250 879267940 879267947
    0xb060412050c13020a02300a03090b0f16050301030b011203090e07020703060b01020c010c0b0604020708030109091406091c050d050702010606080c1602040504030912050303150604081e0c040903 85
    0x51700c1556425502010700c0854800140c4030038180d81c2004401c00c201c20f04c2041600c20181043d54194034000c60200c82c0b03901c070107052074010317a100c114010520040040640b85079080c45854092440c21a255601d19103501d032000340c06000781104c0d000c1034135120342407502c00c0d00c011000e00008100c4040300e08000c10040d58440c001d101c1201d0075410991100882d41c004560403540030300603101c02082c0542039860004001d802000d643d481a400e1081c6e4010505040296000e84200da10020301c8014504129024884958841c506035201d80108070b50040b0103c0d0310300d030a01d442d00d40b101d030300c0080e42ca00360340b940100186903c1c1180340030208041d06078150020812a2419111080c00b500c038201c25200510650410030103540c00180140c005060690002d40c1c0701c1e00a24110b0380340350b207800c40c044501081c0d02d8251340c41c1e40003000707010401c1005410204201422920213107494900781c10760348c07640349098140521880c0a0082c0e50035810611010b002c075140100204540c010030301e000f4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 879270440 1250 879269190 879269197
    0xc080c0a03090b070506060d0c080106120212030712080907030b070c150b0d0305091503010b0408060708160c0302011b0c0b010f3b010b0c0f010b060412050c1302 71
    0x503800540c1c074000c0081c032041d5407411504802d402c440031b000030b903440b01f041c450781c8041d9903000c032204403010385c000803606000e21401d80500710391002e0b450424000e0041001d03811881510005503001007001000007156184d001202c14180c0c10175140795501c001120307040440b81d44c070241044808400300807000740d00c80c00c103e00d03681c480c45c1c1c00010740b810300d40031310119000c0c0c40b074080d0403e4074104000d01290003080035100c1c01900905000d61503d450a0540e01500281d00c5544030000214040c0607021301403010325404030561408401760314240807080710b5054071041000a2010010482c01410700c00c2d00402c01c040243c07100c07041c0b60803001200400440031075209a9440c4005000890704012214071034045038288a40e1005840ea4103d02844981608006140c000c0e20b00030740740c0c5603610514040d80245a002d42c030765200c000c0e01c90b0503030801c0000c4220488692514413a20266580e01050310700b42c4514605042900c0118034100386040601c1000c260720002010058120180c41d8005 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 879271690 1250 879270440 879270443
    0x40e040308040b0f0906130503070c06030b030d02010209010c061d0d0806100201050412051b0a0804060305090a2a081c0207050904030903110d080d050901060b04030209040f030c080c0a 81
    0x100c80a0740d49020760a450500c3c00d4505d2506900900d022620f60b400f00c1001a150601035000d803490250103655801c1455030907406003002c81d40ba020215110301c1e040c0304154103451a40000e40c034041a0b0700c00200700d20b4680b00002c04a0342d90b440390745158030b03089a1596500b180d0000702c035200101400080e2515400b01d80d0f0b148100210300c0210919072040c00f40728021175000d1040c65080f6048201500e51303400013620514000786045040074a840c0130000800100c2c003c0b00515503c0d0b0400304001c0a41e00010b1070000c855000f0540354001482e0210b202510003940060342c0c03504002d4141040801016501800240c4110b078001d8850f48515004181003134126000c440c0c03090b43d6642880450081100c000d00402c04c1084100007054400301a09009c0030020300e00144810955100e4070203821001c03c090312207a6950400031309002c00d10410340640f5498050504051a503070000f40311110050004110011050901e402c06008482c001740070760740b02c101c030b580390395101c1c0708075070303280d009650 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 879272940 1250 879271690 879271703
    0x1d060112111309051609031401150608040510020a021f02040b1810030e061f120b100e13060b31140c19090302061902011b0203030417040e04030804 65
    0x1c40c90710032050750f4484641217583c075211a09803540d02ca400083c1e400c1c902ca80e04039500c64040704891030714a010140030703110300d45500e01c031403c2a080c118075103170702b0855414070f42d07204000b115841a000160040c0c00b4294180001e0042e1680301418042e0103698006507851401080c01c0d030132001e00c0708190000d008151030f106441085010102e003030b1b40c00c070128041103800070004103600c2c0c14510007980c003280d40c144800b1010341d5038450010b0080000d55040c0c825100c0a0b0a00003001c500440a030300401039041b41701c01500f0000d13512210040003450040c089580d0f807841801036211091800100c10000144807220043c1207480c1614202013039400141c1c0c0d00d0020301490302c14141e0303500ca0054034040c0c0d100f800c000040381600003000e41312400f602440404100080180d440380b000307114100180031901000c1c410134201071b003134031480403030b804008005243d400030241e40001a81d40c0a030308110507000b0340701700d0104541148181d030003082c11450108200024140c20048240c010340c810300 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 879274190 1250 879272940 879272951
    0xf0f0a0201030b0303040501050405130615080403110a1106071401051303020d08010f050d05100908040f170607050a050c070608150d0c050907030b040f151d060112111309 75
    0x404c00d5180c0c0700d40e000e11808a841800f040c0002c0c140250402d12400d03d0360030000b802c41d11143d01c1070100c070385141280d000034481c0b0308100030550302c03003610805121135038000c101804095032a0409244400754032401203002003182400d02c0303034070086245081c4212000308001d0a14440d40e035861148140d0030b50140c41000d0824511a11841c20343c1c4c1207036050070500c24428140001c1122003010f9500540f205c1c8102241d011002e1084d10400c1d030403500c00c40829a40300d207050031405400c1d0190b80314440c0d060009801d800604004500503074810a149001561400c210406071142e00401c8185c1c80f09120307074800840d0964000e8a920300811503130311801480d5103410100481c4006000004081809805040143e070038200d402c580c00c014a800c001c00c007581d03c100401c1c2200d5590384d922007800d803207400e61018101420180c00180c0500c01702d0b030807400c080c4941030200b280c3c0980308604101004d45000903c1c4007070f520100000c149100490368031508851245a0b2618500a09405900c4d01 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 879275440 1250 879274190 879274211
    0x1d13021623011b0c110d060c090509150607140a0f080403150203012102060f1206040e0c10230a051c020c070b130b03011706150108011401020f0f0a020103 68
    0x410410425000f44e03540c15903c81081e940f0700d1881052060001d8110740182403580c0010268080c0c0450000d0b181d6415450078500010402c178460094244140210743c49208121a22008222041d140d00052610000440503281c203191514501c0f019200c2d1715402900310130001818010011130b801154112a00c04900b003000e000c9200c00e21541501070100144c410b5000045000a050140002d2115040c0440905070301d056a00202c4c004416501400030000d6510301031050b0b07101590204001c0022580483c0420703800c0c0d2004c920340e401d002e43d00020302e05801c481403000105040705580c0380d40382c00e008200500550080002540064580065150440031070b10903200b0844480e0001c151692410703401800c65800b51075039400515005d80041213860000e80110300030409108035000182d0007402145c200000903208551512844412640d10303a4090100d0741901d8010308500b00044c1c8150060340f4105408102001038041c00c5194240004c0101c4d043c04001d0003038030148425003a1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 879276690 1250 879275440 879275471
    0xd020f1c0509040e1005011d0f0f06130905010c050d180507140109080106120309090b030c120a06050403020f0d08090316020d17030103031d1302162301 67
    0x25441540c0041c0d018824642185426048410502007601c05e0322850851510743c002541c00907000205005070815490905080d400c0b01680d20481c6c20b1089403550a0128026003400f40103003085200b9249444100c601800340d0b4002d258050748000200040700c0e1000c0060410b8002600c0050b10515001050415401c085501e0030a00d5221016021050401c20b00980e007400080b241810024010b4010500d942c00744140c0c00a00030072517008804051611307009100038465004001c200381000002c03062500c00003924240303094200d0304450482c0e054000b0900c0d250403184042d10b009d050000b0701c424180c020604c40c48400b0300e00d041d21306500d1883c00c00c0e10785803070548254000351300c2005002410000070155a241600c001c0034000c5500d03054441403800040240d1420000300e00100400c00c141e04042d00196001010418007294081840000ca10055a1400d03041054000a10b08501030800144c2c1e81a41e901c203070514000c040c80b00100034951034200d107840540d8070300304640150104 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 879277940 1250 879276690 879276733
    0x40b15030c0907120905030403060212160f0c06180b071b0809151c1a0f090a1a1c05060702011b0f020304150201051512070e10080d020f 60
    0x1d0160404100da100c1240484020a50320080e018150761403450b030001810600c0100004c0d4094007015031511101d4141070380019014010f02581c400112008110300d07001140d00c024440103080050049a8608200c40030748189400c5282104005036401c04020410750094041c0d6020365404a01d461700b1400c003540c0d920b1400b4040e0102405003d00945841e00c0e11b2035202d20b0f00c40d800800e06014400e81c036006827000c4e0340040320305c45850300e4401d404141200b45034840c4d01c1044681d07201c40b460090106240c410040c1c03184007521b441d1810740c140849005444007007a040a46656401d4002140c0002e25070a904022203c0e40100c0b80400c90f0139105019809500c5032454074011440881801518980d4880003050194041030100042d54400c0450b8400d29048580020235145005d4444c140c0b0b044030001c00c40e00c00d40303103d04c1c81e1440c0b0301c0c000345003800e850b81c0e030381007101641b1401d20440e5010566070258415100f0b20003e105084d40c0800c440c40d040f440c0306c045403680f00344094032861480 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 879279190 1250 879277940 879277963
    0x1f0f0e0c060f210709030308090703150b0a0503100c08010504021e03040311062d090d0e010e031006030b01121709010c050124140f0f0612040b1503 65
    0x210900150340c2d450395410080c025030700c050703007500050902007880c2003e55908036120f5021a00b100c1d410000d16400940746a070000300c003006041411309560300c00241c42c140c1c00c82c0000c400d942e1451a0400d0f280c107007004001e0310340181140d01c1210069035940180c041d03c0d008100161031500002514241b60003600d01c520754603082040784188609000005820003072080d810000443d492403140601802150301982e1081c0215810690040c1118042002c2d030456002c2d00602408001c0500b4005c0b4104410011030b107440060300c1c9035031004035146140c60401c168140074891404038a914154044030032203105141d002443d80e40d62403100741240b00040058050b00c1900a00c01d000e0394494006e02c0d80100c1414402019441526614212800f00e5090101d003003200004128484615502d0750003841145c040c44080c2c2506000b2420b00000c44414502518108205441035601c040c00d4070b2005c900400d04c0c1c1454901801c0c608180e00041d5030f40810902c40008414860901191010418 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 879280440 1250 879279190 879279199
    0x10206130303020304030203120901090c052d06070213240b04031b0b0304030c06050604020c0c060f12071d0405070e120c04060311031902030a080304051f0f0e0c 71
    0x101401c0c1c030190003a510040c0100c0841c042000714034a071307442002c2c0d114090034062000241400240c94045112a5540c110360f00c240f0716a018405a04180b142c2c201d0400040a80301c1708190008001c100b02c1d00800c1c1d002548904107001250441d4041d60120034515000c2c2d40d0214003903450303c07610340c11100038000c0c407010800421092000c58401d91919480711100303292409034950b96416091306070005d840880c0000c041c0d442d4201400043c1c0501c1c2c0e00850101c030110b1038680f29680d011381e65152460203e01918001c07c0d003204804a050584003040800c41410019190007000107181c20311040301d9489005c0c6d142c8541c407040c1428400c261003061540c840f540340320800300c01c0014445004080000611811604a1458980740200c10040d84180078407a03c107206841094145030203003402095080142034070502581d400901786c0404d581200da81981c036140ca04040c2e081116800f1341030540c441c2c49c09541c031503c5443c0d20101c0d1403580020100892528400815204c0d182451001d030f10 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 879281690 1250 879280440 879280471
    0x20339010e06190e040204150e0f13051f030321201c020d0902040605030d02120708040906060903030f08010f0b09040b0a1716080d0f03090b24010206 66
    0x204440d000100120b485541080710581366014001010790344650082c161444240c1c56181c3c0d060740014600d0700314142150044600304100010444580c50621201e400d50340341da012a814a10521040c1d6074180090b070062001da8490a01410f24180306420075180d107603450540260341c25038803809013017100f81518480c0d10814411030209613000013000d140c20706030300d0096a41580c954402028042c64001d00070504201a004005c1101c442d41d110a029800047c4a205441d03400b08030041318690603000152206c0701400d1001ca5400b03550481d140303180c603101000c202c0541180026086074482d035030b0182c03c0d0409020450360361a082c03003152500c003100d2500307200441c0604094060342202420004d104100d42c00043d130295400e0380028010904130034a10075180d0700703000c2100c00036100746d45000403030700d00304545070f55480c0c80618030200b00e0110000c0e99010700c00d4003d211100d07042056003d1600707144004088036018007190f41942603449800720382550003c01c4180c4900b011681c503204 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 879282940 1250 879281690 879281707
    0x120c030304030f022505040c020c0901031e0c0801020415021b0f042304061d101a091603061a0d050411030f0d020d050f16020339010e06 60
    0x44009200741400c095003c0c01c171324289030030350b4030690520840140d500c40c0303986881e1030148400c58180100f0b5404540011124201c203882d4010860b04480d03000b03000d01107250340d4841500700d03004034550040050485020020b1072000540141080e601c0031840150500d0500d90140d80d0f0760300c0f43c1300c250b49000308401e41c1c0701103140200c140503070405d0203840420512f540c40c060301c1000d0205000c000d0800c000805120500c2030904c50885402180c002d26a50345064040b110768821a801510036415140c2581044603204510200950200a001d006440c00c0c030480d5042401071034400d010000b40741910000c1e860013000d07200b1100f81c44c1d0715019483d11461351104009810b0041098600d5900c614184085403410400450b1068108010340000202d00c43d00030308100300d04070903904000b030038864414074040e600704032040c000041c04500045c80307480c80444c0c184607030761001045800d10741d0301d511300505807641e65100c10445880140c1040c4005c8006460340780100240a4104000344404c46 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 879284190 1250 879282940 879282947
    0x10506010e030a02091f090516080c03011512020706090b0f0c07020103050c07050a0318350709020a0e09130b040f0c050607080a0f030608031909170d02120c03030403 73
    0x1600886e040044824116003900004800714031503008190040c0e44004001005000c024603110a1101d45010180c50401d03000805c8540418020850f805107401c0b0340d03202460052900518100c03000c241951101100d06041c0002c1c1091a02078401592280c00181801446a4080e1051001c40040c50525a054004400401000b0039680c40c45d24100304071804507900704005110b4510030703030310740002d10302800220044413020350101c0c0340c03000c50445081403003429440412070f4140071035020305902c0300c184a071460300b8066480034886510001e034620415901c156901e583c0c1e06c0035285881192610041d40f00040403515014084031800741c082000106021030031440a4012352880030368584400002c1e010790700580c0115001940051030380d0b030460300854001c0c1c40c4540b0b8181084460314020045841e48686200030f45040748070101900190f0144d02d28101419036407851012014521528654680000700d805025110b1803942040200a0700226200d0700c0c0118091411501d071941c0c20b4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 879285440 1250 879284190 879284209
    0x110d090f0503070c05120106050d350a111539122406030712020d020702151303060b0607020904030305060f0307060206190b061b010506010e030a02 65
    0x11a581200031902001050303080000c0c1c9086400f034030000c5401480d02c0104140c0ca180304c521680940d0600d0720030441682ca41c09407210a03508003103498409640300c412603042c0c0f5803c095103070440d0985200b09481c10303c070303030064032824560352200f1b0600410a9a40b0756a0720304074203103140c005a004005200299850410440e101c0a800f0034041e4020401da2100114100e01046600c0c10000ca880103200113820005500701030010140c08403e00a00403000c1e100106a90b01070042900001007460548038100f144403091604500b10b4031003040501c4007000c6d50000700103030310502480700c0e018143c103080b408507042c0b0803040801002c44c9185071f807480c0160002003101d9a102d00184480350150b1075099261340f21b01c2c0b00eaa000101440e0000c1002a03c00f40d08500d1070007075100b07100501c0000e07000142160080e0ba645010010340000c082184043d1042e038036110f070001004100c048002040d40440440d0800c44d4000b488130383e8515004685914210210541c5984110004400342c01e111502 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 879286690 1250 879285440 879285443
    0x20c070b0d09051902011404030b04021905030a08031906150309080403150e010507020622050a0215040303080c0304021c0203010603081617090d170705060106080a0c03110d09 77
    0x10580c1030b820348a031030401554020300702410506182e60011580d001c0000b00420070040c0406081505503180d840800c1d1008000034007800000012017408860044002c00501d8000d0441c7c1c2d03203040030301d010409900700b56100700040b400260490201603c1d40141c50949483c40b50300049000d110000720050300c0c0003802507440541c2004044042600c40240c84c44182ca1060301003120211006910b007102e10050200c0b0454100c0ba013800b80d807000100442002e0220050000703400400385c00c10a090003c2c420009500c41c81da0003071803103030022000182c41201d0203a103c3c109651794030400c03203280c0e22080350000d500c20703a10341901d441040c80701c00007a000e900180002514586981ea81c034840d90040c0c0c503c04800c0251a0a101000400180c803101c2004010306241000d65070343c0415040180b01400074a0800b4880e110560101c0550644040b20b0708803040b5125940d4500c1d020700521070580304802c5180c240780c10754414a000e0301a00e40e80c0c0c828003c0551070064107180e604010554440c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 879287940 1250 879286690 879286717
    0xe0d08040c0e0c0703020d0905031b060c1507020708010c08341d0103090c0e0402222003040f031b05030c060a18080f0928060e0301020c070b 62
    0xa002c03480070792030318a541c420394942c4030b0305a9400a80c00c01074500012040349030200804000144087c1e24041403008107401c8101e8085081304080c070001c0d005004064070007c5510540701c0e141c804150448100740551059025500b45c5e0b511017034014203940c1294801c1c0302041202c0c003c50405042c4a00e004001d00140f01c08446010321740d182c03a10030164820140d1f0020b0041c441111140c242e20801c41d046110034201040f44c2103655403000a400c81610801543c441802c0004040d07480b582c09030080e000d0500d5419500550700c100420040600c49440d4000320310800f40744120b51a9807080b03900807034010154554884807503500721210300e5543d88803403001c0211004540062010406421307204401c20180c21685040003960017159100d800080340318050140c1900451070100032586c68503403405500796035848100100380080315122050252140007a186008110300c0840d40c41a206c00daa150410030522004041c01c0c1e0042101009494018400810505c020900145540411180d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 879289190 1250 879287940 879287963
    0x1710060503060127080123130203120d1a10020a1202010e0f010914070303090603050a11030405060901112a0c15040608250305060120030403060e010e0d0804 69
    0x1803039040780788415000c00f03001008840c0031700211078203001c0c3c2180d541d00e207800c004480108024003006000302030100c0324016111b40000c000d54a090007400340d1443c0031500d8036a9440c0c1c0c3c1e8035010040011500300300c500f28a07000824103900c0d110341c1b07100c00c0c520f065004001c5e08115844a03203a80d010f9003810b0096650b03130b25101c202c580c0c041c046001c0304200040009141c0d400303403c09511036444024254100c0e0008101480040e8018100d003050b0762043c640040c10b40e4668020f07400a1076405140e81410901000b08000c2101c0041c0942c4101c034600e000b840351601c0ea40075080c06002d07185a000400035aa111000c80440d41214212590a01d904135070051340c8a1011408000e007001040014a41c00141808100d4008440380c0d000025201040c001d0a940c0c0300a0203c801004e111500b0075480f0303004210f99a21039001750490300450074065941015040105a49a00a04c41100e80d0790500f031000100d040b0612440c0e02903021500508a0a01c640c0001c44150000074400c40303240350321a = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 879290440 1250 879289190 879289217
    0x2120406090905151509130c0512090102130308180a0612180807050c12030a0c0611071202010e0c0603040203060a09031202030906040b0109051b0d02040503030d0c17100605030601 79
    0x81d045210202c0816140780d9105004010b110030050480d003d2087c1a0500c21f01400c081d512030200c030950101e11035198078580b030340c007101d501911036800901d042c01050b41c1c0100511442400800d848040310204541a0340140107001f00c401891180034045815840c0400c501001038100800480c001c102144500c1c405540e9a5800d4104500507038041d4000040041ca6040001c0c448002c900900020f50810640c2200140100d03004c0d00300819554071041c1c4107040543c10000d07610321961004229240b04c1002e00028000c00c00d0942004052217000040b8855042c00c4c41240e010300d0300580901106d5980f11a2103000e081d21030012002c001c80c8203014000e0307e160b44065801440840042c012030f0600342007101d041d0b001a04510500d40c51300b81800208200007500c203030020350710030546499040c03440d0020000d0050350b0100d6054000003904014442c020b0303020f051180156107405003aa140c0460b29038288108417041c01e28518038040c2170200e42e001c2d0b0040d56100380145010541d90307050 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 879291690 1250 879290440 879290449
    0x1050f0d0908030a0e030724090210030c02070906030201120509071d0f071b060e030c0a0b010e0a090201050a030f150305010203070201140907060c020d0c150212040609090515 77
    0x541003074900301c070040140260f40c04c0350700443c002e0070f0b00000154200a20703600c455181a10002c05c0c0d14400501104c0080e17662499006080c5540e0000c2444988070040c01018000d00030080e08403005014004000c15071301c000744101002d176034040e0b540009900c000d50f140b0004013030240c40408284542100000c0c0407660428488242911001c0440241482c00140e4000c04010b0041e82c148040c440444c2480941003c01c92012a000032000c02c0b0704200440690452060b0020958140500e400007810301c4201011a4101d84850082c041c5507524104e80c03c0448400040c0240092800c0001c004070758441d801001c2404225440080c04c0d880d0000e450040b5442c0c1c1d0b0045545075008410020700e580c0a10454030340d2014119400300910303204003204d0300c0b808103011342c070140045811703400107544800c10b45c0c40346254048910792085444400d10441420f440000500500c582e03080a580101844180c0d412115551940f52440e0309242c1c20301c000c1d1000410942c41d80001441009a5649 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 879292940 1250 879291690 879291701
    0x507061d0d1404120b040f08160515040804261b030c0a0506040b0c0f030a032007030e090c1204111e0a050d020a090c08070305070f02070501050f0d 65
    0x320040140340e200701800000e0034203120a0312001c58410140410001e032a81211284210b503071020300150a42e5075450301c0751a034214030f00041c10b008004038252a064400c54907070700816028004079003180e035101c080480e41200c00c070f80c000c1a203d4240810400d43c01120340c06000f80e2911209000840468a4150b01d40102c0c1d001541d0301c0c80440c0340c040040e007010310100c00f50b48002e40302c1000d95424003011502074441c82c03003a83e08000000614403500319082c040301002e04141c800380caa0351080308034024090641340b1104c4121150313500e0100050341743c032012a001d5544c0b540300c120281c2c10100410400700f00003000c00c68425800c2001f501c010340d0394400140302e280f154940111a10001007880294280720300d0300150110201c400c0e200c25038a42070341c0800c031001185e8000114000c0c0c0b02041302d0040030343c0b141ca0403508140080300300640280c50700e44260016031303003002540d440703400456084040c04e41c28009078001640521449d445100100705515442042506c0e22001c3c1000c01c04445 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 879294190 1250 879292940 879292991
    0xf0204050f1020030703080c03060a0e0703180c14120606041d010e15150913020d02060310050f0108070e0120030a03020d060906031a06030c060c06150909030a050706 73
    0x800001701141003503000b5151a42181d081c0c407096085103070940c046640003001e03005129082e03a100300001e429038441d0700712000031900a1b21380d0031910003d241c03081c00f440c0207000700f0b1f0f4100b6039580c078003500f800c09810003103c2400c641c0080c00035031501000c0c80010f2480184000b10b0034080e01c84a00c00f01000d000780c19101c1d001c100140919101511004005200500f080d8007100d1403a110b1106591b8003420707550840040c106e05c00450015200180381c001164400941156007c010000900a070031100e10840308190fa1400f1104070300030045503503c100b11030761404140044030600065105096840380e0034410b600100700890f5080c021455500801141c4000980000d2141e074240000d020381d50003418035410a01141c2e05503640e00b00417240c0e078141c050207496880c0010300155010441c5044201c0301506540c0e5402007010000e4a4400441da1402008003134400030302a41007100c3e2281c8564000c50146060043d1014210f442c0e620500080e6101500d83e0f1030f0104010702004540d5080 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 879295440 1250 879294190 879294193
    0x321080f0a11071103010615120209030c03011104080c190b0903120c07030c0f060e27010905074d070609081002030705070204090203010f05010b0903010f0204050f1020 74
    0x1304d520f404060a45410f034115a0811001000300801e042d0020400060030851078409a10f0309a0302001c289848001103010341e0541c2455980082d0b03039070340d20090060352042c0c81501c1c20050940144110035020301804810050b20020800a00b03100300301a0043e1107004060b00c84500901c06020060741008104c450300c2d0300100e0081013000f000280380c0c001044040680400a454454003030120b442299003a0b02403440b90300c4891400d44800b045200348415407924481c95612081c07824010300b01224158045807000681c40c102040e207005513408105016080e00c1000503c042d10b40d9002070001046901402200d42454018020b110442c0540030f40e607074000b12903140898040c40d12190601c402c00c0c1070f2040083c4081507502400300c0c0e0007960142d4020962103c1c61000c80e00400f480c0300d10031103c1d440d000000ca4022642001440004e604600038481ca0f0346560b07020080384520310407558803c16040740b80391142001c0d4016200b5141d60304007954070404001c51440400034980000505 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 879296690 1250 879295440 879295463
    0x30442060f06030b0a03060509030c0607120f0b100318230606180606160506190617100906060b0708070209070e03060604240f0321080f0a1107 63
    0x1804809036030300103000b01e1406010340007512000c00e40050080c003010b41503e443e4400201e41840820403200340d00d0b4144102e8089207400071005004c010142c1e880700c91603042003156900d1500600404009603001411100318200010342a4014000006042c20f5601031680c05804a0101e100400b4440c0c5100f0f2018090910304041d141000c1004010501c12034078000c80450001c650741c043e9500a81c2031306c420750780e0888a40610b0b9104551507000705144220301c1040300079050b0110303d9142d1032512505100070354580440e8070300350380020035018582e40b1502c00091188129006642c120b4002c1e00002801c07506c2d056090525885080182c3e406c0500003048411410200c2c0501d0740b1855915141c42c84c14400b10010b43c4455003d068035106a0312200d1103046401e20b035009043d01d028510840030025a44c1000b952460035511007526201540d030741d00319220044040d80341d1910440ea0700d1800c40e694070138040f82d100f1405030084490656880c10440000030020003030120718010342c81c4084 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 879297940 1250 879296690 879296699
    0x201020309152202030c0402040311090702010509100f02071406040309241107050a08070501200c010c0c0305070e0a0c0f05090105070f15060e0c03044206 68
    0x2d80b0000c80d540c056141940c4040080b0303c00c182c40074618002a41c50036042070006030002903d0690200b0600e644648000380c0001040762156030001c00c4034055801140550722410203a080310350884400c0f601c0e411503590400340e0300e0341e603110004508901d040142003180740d8599035000800f610b4815015405407040c041415048040c0780f00500d03000da46451004540107080c40c2402100f0490030620100c0e001044149809020070b00c0a400040c090b0003003590340e01b0041b42d44486610803540419440d448001c1c01210340041c02d01d401e1026030040040094503001141c0004025805841c0382c00d4040002c000110144640300040c1000400080c841c201501c031002110000d15590003842480d0714a400380070341000075520800d0b42401c08070344550950401c1820078020fa64010310302440302c20a800e0049195203c20b0580b40483e0b140c031215a03030340c244080c0e180b000307a4020f4200303c810901c0010a14207003a80146ca42140c000c8514041140a11008091410030b440070580751510802d20 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 879299190 1250 879297940 879297943
    0xa0c060306170c010504120f0f0606051810030219090c050414090403020a020405150409210c030504030b22060b0f030c0f090903090904030e030705060a1710080a030201020309 77
    0x800b1000458090800521030b038002030841d105603c910f40403901c0001c0540140068820742d6031010b6008803c41452540341e1402500500950248521550054900c00c14070040c81000c41c0c81254010300c0300500500315020400c0d078014404001e40343c0b0088030303c0130030014510b0007003810703042190701c4098a45007024401610300b18a032030541e0003013082004110210344d00240f035071600385c1c0507180020652526108a014010451451500182010410b20420074010171503904844501c4104005100c281d200f140e604000400240000744107210a001203070043c56029040f204480c5102c00880310012410103070a0890f0043d01c0740d03643c40303505034441e05015580b902e8410086000e0f191a48044002074101801140e5003401030071240005038148038100100c0b640c1070070040081c09149414580240080700784244a80a401360000016071030800340c00f5115450050f8072032590304a6118003442c94020003c00c080d4024400c0100064580d01c00d102c8141114025030016039a4076003011800e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 879300440 1250 879299190 879299219
    0xc0a02180708250806030c1002071403060f041202210901021005100315111201090f11030a020d111308060c0405030304050d032309040c08040b070f020a0c060306 71
    0xf801c40f92800e40800e2602c05420141c0010441e03041c20b00154640c40b01103072500c3c450380c1005401c880c15168502500360001246821280c150100ea0100d0110505140d00c410050b60104c400200840100300010120903051804008920440b5610820700303030040d00c842403812050b0075040300041c040e4a1568180080c0c054510100e40612282c145000e02c00c0c03110041d131002078110410102d0001040085030890001042d03140703044d5845a400783d0820603050828824020a14544003030801c00001d54007500c0812000c420884e406e6079601072031440031b50300009200a0f02550340341c526420840a00c0a0000e0310300481d03008605038208a021803410001a192400100c42400100501d030341c00004c84050311001c0d110000b03101c90918007070301c0d88194210404c00c8015144619117610380002c016124184007210300f4004c80c0c0c00007070140c410f26030a80e40905480c0320040081c07041400f40742c001d5076001440c03040b00c2c419800c6482d00554038809800540004e0340702c141c100030305100403100b03 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 879301690 1250 879300440 879300451
    0x6061e0306131a1012031103030a0501061205040b040f050c0a03060b030d110601030210230703120b0114160b0405030a03050108030f031f0308070b0423070b0c0a02180708 75
    0x901c450901001c100c4e40c0c16240d105800d000300c10042040300b0544100070700103d03101d500703040340c1c1c07a810082105c002900f802d000301c0f40003416266443c910958640295406144c1111b403c841c140c645450b0003941114030103054a1901c1130070301441e07240c1c0700c8041c004011030140400003840c00b034102c10541400b0007001c440007002a51f0b400d1401c862030108880d030440b0343c11285011040d02c2d2007415650084814603c03c400c00700c222032209000e00110060203884e100395503900504260000250032100311003e41400a4071115060724100c0d0001c004107404c0d480070b004202620000d545100d0125400c407421039140e040440d081c0d84031a01401503901410101e800745040080044056500c6d00000300007440c030b1080074103030b2003076449040040300155030848841d5a0301c0d2654105200000800e490445841c038a280c000807044e062042d414081440e010081d21846150262603032098100ca860481d547c000d000f40c007001a501c00c1000100d100d000100e80341c0a16241e0409002100700818 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 879302940 1250 879301690 879301733
    0x20d030b1008060d031b110301050f22020a15050c0706030618090f020904080a0e010207060504060513050405012918090702120315090105040c0206061e030613 70
    0x40041503180c000079502d03440f030001d85841144004a050455a80d0300029114010700305801c408801d00041c1d00e04065418010b500a014540368180349082d0014211012421007c1071300041131184d052681111800f40001e144080360b80e02c0b0a220041014910b03140004510002a28101d4100c2446000002d0500e410108145440c019014039040600c000c0c000c401d81d6180c10b040208140551110205032700500099000d180500d08290315074401c5100c40041003841640b01c820350720001c0c01c41c1c03d41c0c0095070b5103401c0c503250000a0380d940e00030340c000301c0f0f1200d8a0b15020803551181c0c4605802403204000b140d02e21100c0001c2001d45820b1422400e03410f0404100c1d4111028100326058000202074580d04003d035203000c0101d0800075280c1200c50b01050000501000d940d07807031000720322540304555218031a44d072581080111a00504210096000343c40001c0c070a207070095042c01c1d00746001c04100d001c111058000ba0038a902101d814155000500452003445400300713106607584100e14 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 879304190 1250 879302940 879302959
    0xb04170607080c070501060b0a030504030e030607210b04091a0f04200619020717070e0103060e030f130f050405040b01050f04020c19020306070822081603020d030b 72
    0x201c024080d000003042004072020005001e0104802548484000c1c81015003d1b074440d248180300030054982034509500041070040d500d411482e000c00c8142c0201c4017070b25860280444812204034042d40e01262030034a80da81e0352910f905840394021559507501c107420725100308000007050141010050400e00e150100721003000001488820b5200707050b01094900042c0c91100340000f0310610030078070204003150b1075109000304940c00080c14000c1c0d41c80c00712142c0c200c0003c21040b83c0e0320310341485282c02c0980104010008100740d0380c014088138900c141907920382080c603460440190302510304103c5d120300f034510801c280f046408030500a468120b81c28802c9040646540ca00f510040c00781c24400c0202c00b04401d03a980d2030354121002e0103039a4041d81d00d4000100b10180c03400c40c290a003030f400703070248400007a081c9108441300c91160700858082c4800c4c1b11003075544118410f003c0320440300c8240802194800601c51090305008521130750041600c2e8410040003416100e41004007400b038a01d00 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 879305440 1250 879304190 879304201
    0x4050a0608090303010603113c0c0312070306050907020322270605041109030705030303040c120206091e03070801020a0e04050c0f030108060717040f12180b041706 72
    0x3c01240e045800030700c0d0118100c4100c80f141000c910541010380011244080641800504401710b044a00c9a24515085400900d08826075038450710098113031a4004000d42c00901180c03070240e41c0c01807018940029042d44800102e2480e160640764400540d002040d030f10354080345800382020790780d4201c0480072b001d807500041a07035016810780c3c6002e096070343c000d000403107024503400b481c0200801007041c44102c600b02140c94080c0e0154030230b54003d0180003404101401c00004480c002c40d4041d1400c1034441ca81181048100d1615100b207078881820000141c580c1e65400c0608010b410540b5600100e600320802c151134034000d07610440341d590041c003894000e00c0d00700d00000c805a070b0645000c6195030314005015418450102c0d4081401004400419400320001f48030303101c4d0701c4544410070070404049a900d00c0d420f04640040a0f88070000704840010058009034808207030504080b03020092a1745501440642c0d82c211031804140401e0802444407038601d150000f0a882c805410303d130030903 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 879306690 1250 879305440 879305443
    0x190c1407020d030e04020313031706090103080307050f0310060305090a030f030b0a080703110108010f0e0c090105210712021c090812010906050a240f030212090304050a060809 77
    0x444101a10914142c0451414580125081548000c00500841d0b407444d086002e0f00c114020400300b540003a500900e1264500318190310140100300c010042311181e840e6540f40c0401d03500050445080000030300040d100d10144001560195110f8000b818045040c0035008044a030300070600032083d8842422038020135000214a0f03a8a0010700d0003040228048020648000450307208200e11f101d0071030300005002610b0180380d0b103100241d882c40c0c035503640c9100f5140b5004032809419201800713400417030f40c00010800100020981070400c40d013404001081c18040e040d00010b5419038040d5442040340c41076014042c40927039031140ca0118104084420050100030706da0360240c00c0c2595999501040c45082d01c140c404005020500d540c02d9038540c40024040d0981c1c1c400c09018007085c0724045041920a600d091007115001c18107d90000c900074101d030140696129441032682c00c0084800701030380c1c01003842c4192114001159920300d000c0610091610651028003008891410300644020 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 879307940 1250 879306690 879306697
    0x314010516080601230301030b070924030906021b0f0d020c121207080409062301200d0504140402211e0f100828060f05190c14 56
    0x180381040c000c0c3d541c80c00503218900c802140d0300d015030444030806182c02402c0002d6058901c980c0c90360b886916424815240c00c1c8090180e0b041007003280100805401000c6031815001d0082e00d0301180140e01500e551003283c0c850001d12042c1e0244440e40d10320042c04002d0009000e44000080802d0782c0300260007921010782c3c01009124111030908089216810800003504131040e9581c1a0b032103075985018400f0358802d10451182c5d900740040000c6050080107854402c1c3c80c0d0380c1d141a076001640e401100e40003240d082c1c40952a9401c49041d10785841082210031004d000c0d00c40c1640c0d103003051a42444061305010b107911890040008460081500100d6400501405207001c0c160702e03000e0302c030b03100c0d840d070700d40600411a07203617080040701610038101038001c2c44140d0021822581390b620b03a41d100c1c205102a501c0901100c00344044184a1801e440c5485024000c00110b0030304888000c0c0503140c05490300c060b010100e0340c2c1203918944500c95142c2003245400e1910100f489956598818003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 879309190 1250 879307940 879307981
    0xf0b090609152205090408071202100c11011103010311060304060f05040309180501060e1c060203010e040b16091809020a060f110c061912060e0103140105 68
    0xca0104046485072608100911008401c040c4540c80d12403101141054401910682d000c40e040c58000003682e050184503107000b0303500310708003e160010a4a88003c8000d2801c03400c01103110f466002514103141d40f00e4142086503a550b554010000c40c903c1d9401d488007400000041c07001040100300051940100168804040d03502035100e41e0345060800c01441c00c6403440b1403242c10304082104041d0300c90140c0d42920101c00000d030510b41d0b10110881210307002d0007070201150800303217482000d14258640c0d900f01d4080239003020f403c031400c4d62450260380080c0c0c440c500b01d1a03220b09000030170069520b007d0b0300034404520a510409000002450640c0703070f20a100846115244061a44103030741c21940d5103030340240501280c541c1e02d001c0140401a031140c4140040c601c040c00c01002c01c804101040100c40043c8120300b032135070f00030055092040c5940d0b50b806004606c41e80a00d200024050320b001882c0e60b0f0b100062940c074608080e0054030840f002241c65915000400489c0c8041614020364030 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 879310440 1250 879309190 879309199
    0x302010e030313090501180e07090e071208090a0816030b040f020301090b04050606060412080318070801090c05010306060f320711040902281502010209010201060f0b09 74
    0x344045000300c2e080d44140407007185100100840841c074100d0302d4001c50b04840440540d4120341c070b00402210308483d040040091650403021040180b030b250740c1c00882c0428400030a4803401a901d680f01c032002d2050031000c850b164400b08469145242c084d0170f00c2c008068035030240000c8285194055000a440c0c000200320701c0c0b1400c0071a00784040020880119070340503008000c1d001150600380e0b210041224115040d201e6400001d0b02030905400350380c12a02c90000704803250641707a440e2441900b00a111022242c9000400b1040340d100300808001000030702c00020b14039200382005110105150019414503041c11301c01c01020360300801d08019081c45d0715005419254000700c0b100c146c02c1501d15200d1596000035164000e401704401005418030480d04001c0c20030791042400140c03011040c006c3c0d8045031203410b001180b8484c17124541c46100020303010445584600344600140c1c161200213006079408a004030b42560248141800352a511101400310b42c074200140400303218480d400ba009 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 879311690 1250 879310440 879310457
    0x10c030807181a0d0b0103020f0909060402090303130f0f03110f0f06040b1c0506030d0f020703120507030305100806010b1803121903020c0604080729090124030201 72
    0x815118120a801030018035480646200d0f1941200710319801450000001904e4400703c640703290301038030840781d180034540c10307807418540c00c01c040105080d0b0007010320342c0254081001800e50b66090004095122091017a0410b107800c00c2e8000350244100d410241c003c001040d0284041400c9640c105e02c1c955007119010070700c20a40001c10040c1118050080d08004046008205078242c03402414400c0b035a02c03034505507040c030307204240c0954400762030702e6030103401c00c0740740304a9144149070000d402ea0f0782c1d0046500700350762682d41602818504800000085d008a004030030164180150382c5c0104403c6a2075103045e0801e40c6460b181d14062090910601000a0b100d500c2d08105030400042c12004013502c81c48180c120146a00750b20a0b50524030104001a280c5510360080c42900c10082c00c1600402d1035580300c2d40e985526500130442900e040300c0c0b8180070645400030711b14681c0380d50380040c1c0c145039904080307131000e00359441081c0e0102201505620805801c2c07190030f9100860341c0910f0035806 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 879312940 1250 879311690 879311717
    0x711060c1209150f33240d091a040201020d0e030a0b1009140c030606090d050a1a1303080f0a062103020c0405130b06120d0e040b010c030807 62
    0x35041158000e1000c010858040110809131104058030030700c0b020300f40344a4801080020601e0384103a00312094035110040724407150741080300000f0240d5000d081d050112040030382c41c044094200c4100a100a521040c6020810602d02e442d0b0980c00300b201d910302518101540003035280e58204020000300901c1700c40d031030b00b03070ba4040103040041c80c0c1008186102d42403d5018805c44c01582c011818003038201a4045400020010050306c80c224201b111800c545403542007110a5220162095001d0881811040407800510007095001e1281c0ca0f0085500200c0e80c4080c500342005149183c0c5818001c040341c04241c10800c00c56102074101e050340119600d4107181401020550008010b84507103428900b10346801c501850b03c1d05009030219039452440074100001d8810866030702a8001c04140c403900014058982950030000040141c2c40b4080d801a03510720344003035100c01c440014000644000c046c02c11703202c0c103c80c9180130320340740c162020b01d510064081d8002620300e03010850304510003071 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 879314190 1250 879312940 879312943
    0xc0a0b03180c0a030b060a0503030a0f08190609140c09132c100608031612030b090c0405090c03250e030a0803070807031b1107030212060711060c1209 66
    0x10b00512004104642039622410701010450046410b1806820790b64004115850004140d9510708d0860761040350907000351030300b240d1450700641055400c0345050507000400c92a03005040207444610380018201030400d1410503170f8000502900b0070903004001d21400c98a8550101c00c1d8070708800702c00300d40c4000b90f031420f460812100c0c0080f9001141a040c40340c0b00c50012510389004030340010203000c655101ca14842d00d030310031101c061410300d4071790503200001f6464202030740703544036903041c00100c104400c0042403030f00703004650441e0070600000d424000f6203428003001d60403d0400c80403d09616107110301070100b0310704201301c2c1c140e00328039010014080d20510550341410b5000d0705071414a64585000340d141d03001034865801080101000407e032034801c2c420001034254109001c6801d0000700340070b41e00c0c0c10741a06544503038050800040050b81b100030303d01101d004200d0041c1454500a00c000300308402003141c13024150420014028210b00060685088400110246134a51181030181e03 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 879315440 1250 879314190 879314203
    0xb190b1203040b2b0617030405090612150c03070f0804080f07050a05010608030306090a0c0c060f14090a0507050d1a0a0608060a06030308090a0213051b1603020c0a0b0318 75
    0xd04070b803442e2046480b2403020a40000086581b014520303800440350100d115128084c0340a4140c204013541300188003440d0600d04442641414006d80d83c2e140c81400428440a100f01c628001e100400001d0001541c3d000c00d40e540400510319081026040681e41d48569203d000c120215802d000705005080c03002c00d100c01a44240d104008001103540c40c145c1c96101c0e041110503501c10641080002d07581d9a01340900c0c041c820299407811041e80c00c80e0b03105d50050450321481c0014564a401100821442202860040710010000c0602e48150b1030075034075000c1d5541101d40198105d0905e41e00141d42c007a41c11600810408240155a84403074011008091543c4520030744e2141c90140400c4900550100045d00d000383e03a00d52a5070f42d0b03c180035a44100c01c0000a4100500b09040005081035501440e0884144140c4040751945000032048903041a03403070b8114014004100d0003013540411620040f1541a0340c4840d1061a1003914245400f008119000804000307400c0025001c0c140b1a8 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 879316546 1106 879315440 879315487
    0xe0c0304030e3708010c09060518031204060503040516080d030905070519140a0501050a0309050a02040f0b0405010915210b190b1203040b 61
    0x188101000050300080e9021070040c00c0745504804a03c818200056900144222504040300d10f821101c09044440900050340c500700b20440c0c014003a01c02c100040d5061444603000800032034100051710f0b40310011920009004a2419089400741d03000e073707003d0400c840c8550310140340d00e140f00c5118041c0c81d40c01d44c000e8145500191203500203240307191151013650022039645000c119010303a00b400e00e140e00c1452030300034440b40000c600012032503202202c3c043d5099182100182c481e2084038070f14800c00d6101d06000e070130710800b0030446038900d41c0a84200b0400d04640d880d000107010003034a40344503e04080002842101c1400356203000ca000b8a01c01034900d2030061031b10031130084107455480801d03004c207029021864403910244942401d15001c51200f1645010404507205000134030b1150010303101d0200e41c1080081a24151000000c131140c2d210011480790103500080d030380f07 = true := by decide +kernel

theorem cover : BRFrame.Cov 879136690 879316546 := by
  have h0 := BRFrame.cov_init 879136690
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879136690 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 879136690 ≤ n) (h2 : n < 879316546) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
