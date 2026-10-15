-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4352
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:20:48.330289+00:00
-- url     : https://prove2.me/submissions/adaeb328-4f4d-4e5e-96a8-830d828d3828

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 782553956 ≤ n < 782733812 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 782555206 1250 782553956 782553971
    0x3080411040b0d11150c100e073311030f0d0b040e071d010b0a0806180c0a120509030a111c080a0f06060228051b270c0d 53
    0x540c1d140c04200c3e01801010042412010300781404048260401080b601d07200070400b6284c0303c01c00060200380600701c0040003d00e00901221070b07081200c540d0280d100c102600c0103803051101410b043c1072000320300d0401d5491038403070100c081d2900303040c00400c50000e4201744001d05008603203100403c841500c529000401140420001d0100c0e640714480540e00e40c0421801c0c031001c0c04050b8603401c0c04070403400c0c0121561400380144c03400d01c102c000c0d4001300862040441c10b00d0315450a07030091420440555141d80c030305030010401582021050030006601d41e400000c0c080002d01c6503130b000e01d8408001d10324041802e1000d8a1446007041f0b02d00d043d01c5032103121039204c2031586403c00780841e1643c91a06a0a12103890001c5c0e8003100c00c3c1448151510b203040100d0f540004030390070407020141da01c1400c0000090881640002c035440503190b40201e03419001404c80c1c89054034000c0300200e40c1344030000268284030041055181d40103000490240100744600c0310b001c040c00c20755003454000702d90003 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 782556456 1250 782555206 782555209
    0xe0a140103021c151a070609240c1803020a0522020c0606120c0d12020109050f0609010e03030c0906031918151806090804050a1409070c03080411040b 66
    0x360016502907080310390303504400d80401340c032141d04002031003880314020300311915a02080c00e620420038002c0600781c0d078656420801000b40b03868003903c51400e554416100c02d141089010b41050b0f0b02e80350004404040000300c4080152149040d681c0290600c04032a00382818450703490344050089000e402c4802e50a55940c8042c00101409030b058000b030100740c05c10106001c0000300302c20464400c2d41207001d500e200713030726078606920100d600303d40b02408505000c00140e00410003000050030034001c41d20030b50582c100019031039010b2003080d0020400d20000c6100c10381c6900040d540c4040344071003004205d515140c8007010319003159003a03502e880003400104241701100c1c41140d110100d94295442e90003480700105544600306201d090500080144005000c0d5060800b000200003030381c0c424086003801806819113010300000f5000955964442a5400d0703151070034101140301c0c905003c002140580308501460380c455060320b460041341c8455590300c5401441c0400c030303a00543d4400c00031119 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 782557706 1250 782556456 782556487
    0x10032a08030a031b0e1003090809030a03020a140102030f070c020105040e0f07031b020316060b0405010b040e2401030e010905010216061a10050c07030210031b0e0a14010302 76
    0xb1100306440c0001c010711041c1c01349000208281152041c03101160702802d082c6c41e81091586400d1991074002203000183c5403800c660302038014203a03050703c1600010f204049d0000b0b0407400d85405491310150320001ca880705400d0b0302c0304640400941c1c4044002c00d60301070181c60718032203084c41410003600b02074551740305414554003118010f4150741110b050240765901031103035690340020000c076407a5644401e54065520b10940e2420402d45100303920000500c44607034070660100c08001c0060005595032100359029030040d0281d440d1100178500400c001c50107114542d01108102e003a2040d569880d00d0042d002820361005224140d52107a400300c00049083c40107145c501c54800e0071105103402410b0610440f64614156100410307100300c0c144c1941ea44000541c501045803405560740c00540038014100201680001e420103c150f0402d186650590007030503200c010030314040c135600d000c200201ca603407415180098004890072828400110b2500100030760300ca040c14054945070640011408 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 782558956 1250 782557706 782557717
    0x10f090e04060507030f0603022202070204020a05040608070207080601060f170c0c100e0a140a05030c060a240302120f07291e07060e010f05090610032a0803 69
    0x10b00b56910000c200601d0780505c0307145840310880d4402c003d02c0b070565010030f40035001c07803880c085007004400c2c90903402c851a40450350b10550180055403a408226006130154206000e8140818294000100203610000ea00070480e00035400801081e443c2c803205a64000b0005108020004440250124103424115181c0282c1400044c144e4441c08203140341d0410b00001d041d07010041c01c21036002e80c0d0450014101540756041152004004440c80c0100d01c1c18440013401002c2c0d000218000e14160400f090051041c04051403d00c16010042c400200b140542484148001076100c020710240c1080c0c006420894031403412910580742c145041481e00701594810310110800c9089a84030518034060b02d1030038907086032712a090034030780740c0c8940b41200a20700300e01d42108082031038402d202280e0800404604c13000e00800000d03011a4482014040444444807180300e000045111010305d01002d004172a000a501d02c1c04c500c40004903140390350300b0301c4030403144181000f0204a01c0001e200804 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 782560206 1250 782558956 782558963
    0x30403020f060a0c170c190e01080c03040506070c081611100203040b070311010b1804061a03120c0c0907050a080a0207080418060306020c0a060f02031005010f090e04 73
    0x5000c80c44419071450320b10020305284030035060110160f0410b8010b00160070705034855400f41220b50b0350484c0d42c1e4140c003c00c00c10801c8411140c12880905030022401c41000c08203980301902560b992106488500c41614002e06a52016000400d03952040840d06c9005200d50306403841c05103050700701c2a00c00c1208009542488000103220b40500c1c0c01aa0700c4d40c480c400e4005541040c0c641400381c0b40da80500000170f07007485840010303001102000e501900742d070f04009010031104145045151440300080b40e040702c5e154540780d4600c400004540c0d403800c004d84010002c1c01c903d954800003a50a4021221003000c900c5500001d9180350707180c500203131190120350784031601c4d1007403200c000b0981000070700b1307640d031191040041001003812501140e061b1030082c151100e041c00404041d05c010201c1d0390014240903c0812003115085000c00e80e02e44d101c0c020781080c0190404440f6030002c034030040e02c4144486a10100070840c5501881c5904490303041e40c240351840310340c0c49409080705c01c4100c900702c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 782561456 1250 782560206 782560213
    0x70807030e040c170609040f080d0f0623031204060318021002060f2a181f11010b0a05040b130c180803030601170606070203010f32040201030b1503040302 68
    0x1045513864604185520200458098a890500e03485d40140c08100802c0544054000568040014480e8101d500c180810030b00400000d0342e2160040000c03c003100862407200b0b20000d0803c440d107000211510402c420b413960302e00d0a841c10030180c0003801500c00e845403612803465400d0242e900d509483c0420f01b0241c014180718a441004480b58010041c4448480d444000c50113400000c40340d40c6040600c0507a00c40350303450204a9442d600c6110b001011a0301603e04002461080d1100114074003241c496100c08403070100c486c1904c4d080c1c66444901c60307048482c5400c100800d2400381c00220200202504c00603200080000b00c01c2a10100010180440c20a010341c500320341b2403142c6040140b0b108405903003581400e6000808008080520024841c038440100c0c03041d5072101c04507403855034020020461440303603010420182000341c5440c0101a02c424050000b22000d0150f00409040d240c00001c03a66a01d60054004018070480035411079508404018480412801180124000e8004 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 782562706 1250 782561456 782561477
    0x907030503040320030a0f021504031b05040e0f0a1e020d03050705060105040c020d0e0406080f06010e0604060f0308071506080309090109021306030e0f0601030b070906020111070807030e040c 84
    0x303002078030325900615001b9442005424082000306810880e22903046604080f0601c0f00d1185250502482d080039160103034001c0801d0003407542254a40c12150243d0f400e010300810320894035121040004000c085400000240700050744000341e2414034085444030411804854021030050701a424045000c2000019448140312081010b2070040c04c0403038062201070301840c402521050010b00550a100b100703085a02580d07034640141c809409440201d42030301900890942c0c0e100740c20311410712581345d43c2f00404c2e12410207008034002d46841c43c1041c03207240d00e1a601ca0f485548010750a9841d40140441002c034911135000780002040003e00030342d144d002210404c00a0081030780a980c030f2920400c18036000500302c1114800701e13400c034200010407801181c003083c10005803181182d030718015840040304120390440d000b030042c481942d0301480d09840ea4010f034200d0303c26200a20204d0020710140d07000800000092910340e04c2490003000103001d00b00410141c0302039062050103d01c40b45035 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 782563956 1250 782562706 782562743
    0x2030c03041e080406030f060305240f1605070606050a0f050f03150a0c020a02060316090e131103100c020303160e1008090a1202060f0c0304170309070305030403 71
    0x100300040750b84420101c2464951550342003004d205910420061503124110030711040400d80c8640700030f5401505490440700d03010644032000c49089800001da004103030200e030069940c40c41d4030744540350380d91049840b080401000d69580d00304481c1290010b40340c0c03a001c50f00380c45488030354004041540e17a132102c0c00d007080b041190325071116008a000750312842c0c60002407030819550036040f42c0800000260207025400403800c0119001c40a0741210001082c0b04404a0074107410103203403182c0e55940300507a103c00b24119516426101060590004824440414031992403242d84000040071100d046d0004d01544c01034404594807040942c10100402140c0e8542c5c0c08a034020401c1e0b4546458622118400141c40300b0010003072004014145000584400080003d9030070550070261b031a8204a5406001756124001c8408404021a18000c14002c41400c020b80340990b9010361900c1d101c10142a00d088907030401030140c0d071603200700c1130004003148090000b04069402800100410f510400 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 782565206 1250 782563956 782563973
    0xd1b0b040501120b0a060f1202030f0a0507090303080c0a0c140601150e0148111c0b061c060203160906020d03021c020a050a1106060a210602030c0304 66
    0x2c419100f40c106110880c03250744514000d0103813003090170018041c1411403400c8512022101c0d02c48915803001040c40090020b5900161240414443c140015500c2840440d0760310301ca4440200030900c40408190820f55001c0642400403241c42d2250140000c2c0d122501207d5075114442465001040140020f0001c1072007600301d1052802c0107016800744c1000200b900041d00100030408e0f12002e540c0000040c116070007880c0c24901104055041e104145800b0041c0440c20100c07494520000c60a5407401c2506000405207a4100c1d61103002e00c0c1134603070f46c0020200801c40c50f40000d10078070203c49141c124502c0058140180b00c010b03102e281004450100c01385045140c42170025041082148650004003129106860704d40540c83d0411032220400d0314011900c03034400c00d800410401030280c0e1083c00f415081040307586540826540941c0d6030380728101502e820380c2110002005000c1d90211050f10417605084d4501d0520a070f80b242c50320b004a0300140c0d80c050010000000317000a004402 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 782566456 1250 782565206 782565227
    0x20f12070e1f0e0d060e0a080406080105040c050d0903200c03011808032a12071b0c26070609030c0e0f160e091f0b070804050d1b0b040501 61
    0xc22094045240703024020304440f076802c520900c03a2a0b05000c59040050343d411000075a1500740495041040e94500000781d0f401500424000480e00c600024452401d401800c01e003507900c2d10381c0c07840c01640d0507040f000780a14035401d030180b0038111600000703014440444806107020101a081d00100d101c01c05003510310007402e4401e00d003540c1000c80085145d03c1c0407a0b41104440301d02a0750f120b981280107500e2111030303041880485001c60000b001c10084d41805110b050300b83d80d940b000c1a80c00140b00c0c4500d035680c07000f900d010b240d020113004102000700c0c00c404c00d0360030f02c09110301100c6c08440c86107816207603000f2500041d8030410403c00c1100446940010b4060748000c0c03038941c682007040c00c11080005000214200350500e0200016003d00d0601001500c09084140c1c2d0740b41215401031359446a2042080600000344000781044949003510b0748075500c90b0166151a280000700406400004c109442070202005c1559581c0c818030080001040e02d601001c5e00c45150400241814196 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 782567706 1250 782566456 782566489
    0x120314250201110a08131a0f071b1202010902090a020403212304050303030916060c11061b060f041502070f0b04080f0412060c1e03020f12070e 63
    0x140310410300000403050980f000d446140c17030115180c2e503c018010a8004038950041c200d14401b0340b0b4200382c124040a480d104050b00031396a42151510242102c8011b0100c0e010042c2016003e20300c800500c4140032601c2800c503a100201d0803012540004000300015215508032a0340003d08004015124107100e03011000b0349204101001407880180010381c040030444451503280003044020f00085050b940a000050102e0b610381c6000c1690171b03900c0040c5c1c6800d1180707003807040000403d148245144030b00c4943c0b000401c0c100442010500210382c00484107444040010700e0703900100c0c0d90801440f4451451203040c81142c0c2094280081c044803003507944014240100030700c4010400c10b83d058058181d00000b00805039483e404c220700b07a40603084030f90b4202140080c0000342000300c6200042110700607042008001c1410380d0070f6400f03100c8104070b40c485064545648902d10f0003036000e002e682c203224400781d03d80100e121a400800d54119500c9011030700361000500b881c02c2c045200f1148480 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 782568956 1250 782567706 782567711
    0x101113061e0c020d1401060e09100632040f09030503070909090209060d02010e060a0c11060703020c010c05010b06040308070b0f060f0f01020a1a011502060c07120314250201 76
    0x445030080313052400d5040000d050030a020710100704e409801d500c02c200030000c4070784040090a0507010161100480503901041a0600e0030110318440300b0011b030780100c0344a500f4211155400702140c050030a244002550240d500c13281070290900e10b01411140314400d54031160b0303a2a0851002d09040c801b90000c040d814500080c240c0142c80740020140c01270f10868005460708190300c0101c0ba06518220801d401401c00b007400d542c0c540d0048250119148550f540c203040b1100c0c54148505070107050300240060f8851040c11449501511404148602880012452101600100c1d0195005501c01c840c4e83d000040c58605004400403015000407500b000032800781014070003e86060303007400c9014445c418007203185000da070003000ba803170075940d101c111742252001002c2403801200c000d200384040507610640c1d0300d124510200301c1074032a1410480e5a800c0c02803030b0300c554202c0206440180c2c140755542d280590203000301c000d00d81c494450220b82c3c84066079924000e40d1141b030710302158001c0d6030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 782570206 1250 782568956 782568977
    0x20d0804020a050d020d14030c15040803011505040b19030506060c0c220609050402010201050f10060503040f060203090f010e2a0303040b0c030306030601120302101113061e 76
    0x380d030982c140003201ea00310740f401091900340c00005c1d6100c81d0064014802c01c880da2100c0c1c440b220100142002c03524a805582032070319040f41204040c03004a030000c003c031004200621100740c00860041080006140c01801d0580710404a003440e84070620050500e0380c1051a0350010b5803501034198030550a0740d80358102030141c0019996a00d10548041c4140c1c1c042c4240341080c000e59010904031a41c4910034000d46603100c0c0200000c10080d83c0c10303801035081c54001000c8142c15103940380990391585441c04d0041c43d140c001c5071a5000640200c0e0020844800349001c2001c80c00658051011400078100c039218510742c9030700311070900341440c805421241d040501c10010702c688920000b40104170703182411281c0c001070304600c1140c004001680300482d000c000b00d00008061032180b40240d045441a0342c884240c03288241d02180001e005900441c01d0318403000c11038200e0305d100300003c01e2403800d15035441b0102c44c0842c00c980009000680000305512011a40b507070410304c2e81341608051a400 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 782571456 1250 782570206 782570209
    0x70c1a0a05130b3d090606090b040e0604110a0e121605060c01060504020712120605100c03020f1903080f0f0c071a070503160206150d02030c0d060c020d080402 70
    0x43c24000e000b01041800c103c03242101601036410542e1002c20303c8289142683c440d122284014140d010f00001545404404101240a6084002074510508180f820203240840c900303e8a507000f0003c40e042901c0b95200c8505182c03e10207800988059151039801108400c14403202980178044103040341c0c8059180407100045000c2d5a01342c030003c0d10390a07664042c4030400e50150110394041038101d403001601c8030038045080201c9418440170340e14500c1c0c03a42c00041480c2074410740e01410384e002441000c0c08410038050000340c600c80c1d2080c01a44e18050030440c2160808052180c80348014010280300300401d43c1c841036a5034840c031481c807179150b207080c00c440001000350002c268507148c01c0c0c0000c4031028801c500e00600c001540c01c54244025242400c401400343c0c0060f55401d401800a2350001c401c54000b2640030301c41c54940031140503680100081080c2d034484032000386c0c0c15003d000d012110503100c80ca41c08200c5405000042917040d0034002c0240b4108500018001300301070f500901c03005 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 782572706 1250 782571456 782571473
    0xc0c0f010f0f0c0b0a140109020a080601030c03090b0c030612010207200a09052406071a0a0b04020324030d020d031a0d050a0201030e2103070c1a0a0513 67
    0x1022940c60041441d084503607050703860302d001980113016031040400b00807003d05550408a08101a4943c0441590340d8908840c02e9010340050000031504000000e18a540b2076800250119032510b004601e08040f07440300c030349070002034404807043c050000400c0604d050100c04007940700600130003103207400300944032000311400803240381100c0c1c5d8800c105401e03070799103c918040250448180410407402e00d00c051704841591480001030003103020407034808501d040e20035182c0303481d04500700f045400d40d4100c024641d020002d05a008081e40c42500d1810b64a491000e103105034845102c80310800c17000006201800340c100306580c4250b0091800c028501c2c2e01250038403c1d031010f0305000c150902c010000c401000e6210351030581102048080b04148140021110805030007a01c0030002501d0001066488200e41600b910341d900e540318200300c8104030b0030000d541c4405649403240f48050340c0e540320400d1008401e6000e003110082001e03c0500241c03441190b41013030341d104040e48004007603662443c5 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 782573956 1250 782572706 782572727
    0x134b0807030519020114060a080c01030902131802040501051c0305030709231503070e010e0604120308090d0503040f08030402040902190305060109180b0a0f110c0c0f01 74
    0x829400880d84004050268040e5142c840114082c440900700c1c01d10000d00a203280811890003942c800c0110f40c9600340b04103030400343c80e0210302408046020300e0042d80a0703c00864201d81020407007440005107501c81c4034a1540501120824103841d01c54010081550410381050340708510032442106100208201c15510640c1414496100d45c0c0d594800e407000912540810200040001c1020f94401c1d401c000f8101d901d030499007241c4001448280c00000c1c00129440400b00301d219010108640c020300f00140c5518000f400303d0b00e880e4407001c00509800307460200301c02190760300041c04000041400f44002c03e01184c90310b141507103019103540742600727844600a40b1003200080800e0a40d00d170354010404013500500010070441004585c1e80e6100458030040d6140e0080300004120705440c0d000b00c44030124092408200c10701552500d10740004064519117455540d40943c00100502d4010a9540f0181f8000715449080500346c841c2031100310424980305603c4070506030440d07a040200c005 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 782575206 1250 782573956 782573963
    0x90807150c030f0302130308040e0a0c0f0e19090c0f05090a05042c03180a08060610170907050a0603022701030b090a0b0a0614070308134b 61
    0x42c03c000144400d40c02803165800c100599101c266011060002c114020011100341d0450480310b0741c2d4083c81c150880d1085020080002d00b541e12210109100b85031320441c1c0c000080403000d04031841012055024040c0e4000e80307041e0303142c0401802d4039402809061001e511802c0c00342c90f1aa102c00082d40d2102180141c5200b20b568080014001c1903944440302030081075081100c8c803e0790201c1d4aa80d035080030300040b031441c3c3c500940401c00d040007618901114060401001303151240000c2001c0e0314481840002001010b407a0441d1505140b0407031070081080300701501c01541040144100010b481e005041414010890812803220b80340030044100e10540383d880808400400407030183c504403c403213030300050708018030070340307110640c0004d03041013040320316100d2160b0300c8006441e248440e10f43d151030910140032401c08a40550109a403140c184d4070080000003a85d07548100e00b15640d011842618104001c130141181042554880d9400c550304102e814200b618403a0020060f441005 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 782576456 1250 782575206 782575217
    0x16060504061211160209060d0302030f090f091915051c080c0a08090a09061511071511010c0908030d020d06030618030207050f01201606090807150c03 66
    0x4414244a83c00742007910712a404180e50303070000c10021104100c904e0320507841103000402060360781c5071440d101c1d20b50541c903802850508042d40d824000b01d0700943d02d04c0b41c01c5a02c02781c1800281d5076148d2003520991007064188440f10100401e001107954049209003c04d031a100c1c103020544e14038003c21011840303a8804961141c1500d0b0040160140f281900400d21400d007803903080110030405440f041905440c90507603541d4503086601920303600d1040d50007440c0c2c410010f080062061140c0003007403c540b0115100301d0341d5039070902d9802c01d1503100900010b85d44d24a03010b1100081c0246440c07442c091400208081c2000c070f159480e44034158280086507400070b500506111035810030b50007160040c40800c0000780320340340c0c02ca1010086004600602035010041031a04d01b284102c5110780d010ba4030300100b003903043e01481e00b00818905852481c0b01e40d600d80030102601d4042000545515903810750014a0a03000c1c91501221380c2107281702c0c002401c41003a2141c0c3c840001c82801d601032403c2c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 782577706 1250 782576456 782576477
    0x141504030c080c15010906090f020301261603060b270115020c1005090a121106070816260415140d06030b04021e0306010504050c0d05130201021606050406 68
    0x14500d41044d440c100400d040b070380d2000040310002940200210381d042d003014000400802c8040c0200e2000b402050b0281d060105030910a903040d42c0300c200e1550703405c1d0071104590103041e01c000c240c4086a0049410313545400f0640151700701030361425458050320a43d004404618941d4100c828014080c10707083d90903c1c41c1d40c0358814070810800b02c034400050a03080044505182c01090b0340e009080640c000c40f0701020008001004040c0c1d581c200350054264049c2035100002c120003039020387c00541e004141880060f4a529099600d91905485165009400c2e00040040a03a03020704200020350440c0621080104004140b840c0540d20b210780b60034055a00d100030000b04c54011048018542403500d000841000640e0f60703071502450084410420344103881c0455525040c100360915090b030000700040080d4109a004035421070640c0035207030704040000c1c180c0f40455a040f40d036458860140e02000302036507010f02250400b0028281c1c274050650030203001600c40c1c8150f206180c2042246981c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 782578956 1250 782577706 782577727
    0xd0b09060a06120314032226040602030f0702040204050306100e010b0a080604020703031103012310020a110f1305151801170a080a020d0f0201180b0a0e0307141504030c08 75
    0xe640c17215811f06c02c02440100d107681401212500c80c0c081031900c4054850304e05040d03000710000c1e20125503559005528012800c0e41c40940394201400c00c9070055000d01c400720380d60740d050101c80d04c0303140c1e81242c1641c0070740350454908084006a000704002d0f1410492008042c0e401412243d00c03000580e80966036140d2440c04034000c10030b14042400c1404003000124100380c16400c4c240102d030200311a0940c14031175074108100c0c10305420b50030015900c180f2a40c2c00192141d42110120071004064101ca15041f5021071140300d40c484210022542d10010400385060b005812003a406c0e05940d0328450004600244940f5a4180189085a80e1a0a2951400008110001c01c19501401075925034008200103541d429900e05540f000c40d00110f2046800340c4148192000c48603010120007440c2c03c00c1d01c510410000180c048064651150101445110100010000103100d000d20007440c070307041d4540345e090418004144904108090900c40460b80c170054221189030418140b40d42c1340c00468 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 782580206 1250 782578956 782578981
    0x50d08040b041203020609160512011e0213080105040305161e0606050f15030a1820210c0f1906020c0a0905011d060d0b09060a0612031403 61
    0x40c0031040c0c0c40740000e00410889205410340001d41d110340c080300d4180d1a1000810f84942c840880b901030100c04607410030040c0303490f21800d6011403e034000011450040712401c2c02114142c000e9854280e000141c220652200c1501d000042c16500b000f040241400d541c000c0c03007441801c01115540e007914070714005000c2e00d078405404103000c003914244284a10314041c0040e007182d2040512030080c0c4c04800480d400e0030480c02d4031009031407800c0381ca0f6a03141c222050040030714203188003512100b403150000080e00b11680ea081d614418100b181700440100410039501c1c3d08070410801484050032400c5031384d100094031244610111540c40011000f6404141e1403440d20107130403101040070000003445600862512545441641d0711072003151a41000b0050b544207220f81605100326607506510801e2105000c1d0b0030107401081c9008550013600c0b80030003240191a180011707000007003400402582c0b84100c40c014001c00e000230311118502d440290000500fa110702e40c41b1103000000074003480095 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 782581456 1250 782580206 782580209
    0x120c061f0f030609021203030421030b0d150606051309090206090d06050115021504120e090108060f060a270b0310140c1312030507060509010507020d090f050d0804 72
    0x60100001d07559a4100280a0442140c007030b4082c20000d402403110f40b9010003100e20568010200000820040c12040100107800c000c910406075951404071642c1c0d200c504a403551402080400c03d40d1880e9401d0104840c0a03602440521008110b00341000c00394040407402c807040301c0d800080c0084207001240a500c03501001c9a40080f0146010040003126030006050310f0003d07101c004000c015500c01d07a5203140c40e40340b61070f8102881d000903002809a28118103403489a10b000c0481000c03000126072030f41c0c1c00b86c00900031030300701070200036062407202c13600d0ba400a02120a10030152900300d410320f0340307818142820300b0001e0000003110303080582e40003200482005000c4548412044488800a14070818042c0c41e00d1035040214500318080c0c410303981d2403a03a4080d01e40207a8901304004203484600c541c110188801401000e02003291481140d02ca00081c4c0e00203d42c61400c1e0f10300904001c4411038800c1800084035042c01a410030180800036194282e455450421450030401d0f41805503 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 782582706 1250 782581456 782581469
    0x170c030a0204210c0803091c05030c060408031b270f12030403060f0b06160623150907021e3d02090310050604021201030c0602120c061f 60
    0x1c460f41c90042800b100700e02c0c107059000359600c900113611044007985901c144000d0507480b451403220341600707662140c0e80804083c405c40c00c0382d2801d4002a0810704007401140c05841400c3c01108001e4001c2c4201d103900e4031440b0340368a4034603200e0400e2100520840700e6020b012a03501408100c0d80d42c1e1202100707180b400ca0014080c0f0b036003d459058440d5690310501046503020b0600641c1100036a0a02903400c3d81c09004041c10304111004040010400ca4a4410365000e9103c502000220b0042243c00203495614485c2840601d018417240c0040c4420700e4505020707400034401c001c00554040f07401c441d4520108900d5907840b20191038035161010039481e18005015880c07440408240b040c006070703800362a07000340c580194805007008040340503400d02d058150300882c12310b54582d0000e90046c0d9002e98001c10050514105248031503803080c0c00d800455010f20714070b409201e000e40411440b411441d1400115107413407040200f40743c5420000c0c10182d403140030007510124242e44030b8000005000c4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 782583956 1250 782582706 782582729
    0xa0308070e0a030501050a0b0406050d02061e0c01060f0b090a1703040305010609271101050a050715050901180519080403050610050a0b190806030708030a030b03010b01170c030a0204 80
    0x499044c101e0007050103444d10b800d00c42c541200741181c2c3c10705d030150030100c070300040c0f40c04514800781e020b002d019400079100642800901c0485072b10440088090b0884100c4480006501803c0022003090b01e0202e800c00704904405001c01d03042581c80011500507541c104000300c02590401d04502e141d4016908010300650070200d0100d6090365950040c4000401980b440c1c50158080c1c01c140140c0950382c0020b0300185200d80003e9695000d20000c003e11030311490898586180d94031903d260004040f1040d41c440d80758818044d182000340072342e40100341420f015480c01d21709562807540d2103060311500100f44415400070f1301401140c0007520b000307641040c19280145001681d4400e60400342c00340d28482c2003c5d140c04140030000f0300a0307910380b40b0000b49150002104680c00c1e55407201c01009a03078180b10345880800c03604000d1018041400d107584020482c0101c035020542551400302c0d0070380c104201c016248000300c001000ea20380201d99003001658030780707c18040c40040d00c03641c1c21460040e01c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 782585206 1250 782583956 782583959
    0x24031b1905130501081b030c09060414010f050c07030f082104030807092d080f01020912060601090317070218190c050919031709150c0a0308070e0a 65
    0x41d0004000c0405500700388800c0c005a440c3e40042d603410200340c5450301003402c8112500c0542d007504000f180c11010320702c0f1280c2060305400000340564015040b856550002d002c81c4107865030001d00041c200c2815040c15418000d882c86480da850390b0740d21020f424500b10540384030034803000008490000952807001626143e80e5074030116000400e403400c030005280440000d04641c4a944001c05403401c5040c03040030718201403000303200d03092040000820341a03070700800120310804002d05000e03889d12000250700c0d0f80d5804200050f0f02e070310022214040e0421030801c45540c1c1e01c40081002d40b5401890080188608040b0607014062040000d400c4084208551410111009000e00c15070300038908600003410441850140c8800340d2081011070780c03d00880002e4a0300410310342c85500664181c1e801036503070703480b8000c0004811040034521040001d00e0089418282c681c8035400f5074561700b591801030840b401c540d8401944001404125404000c00c2c0c01c03900c103036000425410000c000280f80c5 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 782586456 1250 782585206 782585257
    0x6020705030a1e0806220e07260309010309140109030c121b1707170d0c0207030507141807080a0b0a0f03170408030a030b24031b 57
    0x25840b0110140104400c01c82c040100700c4072101e460000d482d140e85600345500c64a05004582950b00e6900e00a206218010042c440c0203201d481880200800100107081c6010705c031103100280200100f03075140c0c04401c812644200001102c0b035a034000c3c80c0003d10560b980c14140d82603111040440240e50800d5284803d141c0d000014002d11802030503040d0038042584010345003001040141d040d400d611100c03600c08030f18000400f042c1c030038400003058035144940c1c0d00d411000b01a00181d0b0f62040e800b01d2030512415035449401407100d220f00040242600f5030715120742e0b525451144001ca01e1385003550401e0b6845820320151401c8941d0500c403181d0402c40d1014110400c11550480a540781914031000e0785000560a000c03681c2d8580801400c03802c503111080144000c0101189044c0e04100c00540d9182c00c20040803400803d54000803203d11000420031405c80b0f443d0701e14441c580495645150140c0e03107003141d802415100b001704c81002c041c0d4025407940507025001c84c10b02e8551461080701c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 782587706 1250 782586456 782586463
    0x307080606090c0304050c0d02120f07031209030519020a05091302012312090f070f031a01150e12160503010f0e0a0807060b0603010612050708070e130906020705 71
    0x2901c003100d505001d566054590b14042c00100c90240c8240d104104e400d85504203001c1d6101c40c6d40c0094040940b03048400c80d480d01c0c000300300e68075400c02d6100440400611406041090b040c40d00d40c60800c520720718603194155680f071001e541c1e500d0b0440001c0211704569441c0089001880302900c1d10403a0310302a480740d41c10180c003040c103a000c0340411a60660400b40c40b00c0758100d00b02148041c2c1c0c2022468118004002801007001407070784034010141e440400100814001400a907100c02c11003419890203d444100250280e054040c2d541e005201001c19194031007010b41107480d000c072146c1e0b603440c00501104045800301010380a188061440540203030003503c01d9400c203074000d02002040140600498869080490640c0c0000707584da00091380c4000200440c902030100481d010858200141c0e25178400e920000102d09110445940404103004440d40030360380d410712002030702c0c00442c082d1482283c154218803034114600c6140040026a00450810b60401402c5440340160301d085981d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 782588956 1250 782587706 782587711
    0xa0803010608092802060409020426070f0b030a091505091b0607060509120a0e01090602010c0c1415150a08160504050c19020705091303090b0d0b03070806 68
    0x90042c00000c1c10350000025132440c1d80c5042004060180304500c200780d48006910380899100c1b00401002174182564000740000d01038925020092000c24180d2500708a0820704901d500d0304150001c0003003101402400c2c040b80d0b07140041c13554950360080100002e01c01000c00900e110902d640f1441d10b01e03401d50140e48140100b000302c1c0c90045100c035030f43c06521011044242d03c071404106501c0000e019800c4190400500e108980e084050222420706a07041001d00c10000b980b00c25880f916580d2150340382006040c2c0c3d0000b00251420048010441c84401e140601441400684c4154286041000000c81100c81c15030207064240390b10704011114030481d881e0301c580009031011640300004180082032a02c46910070480b00d01d444240400340a004000001460080c042100448104201a080d440c101c0e03001c1e2007103e09000c200181140c02400740d07510680d1510341240082e0f0401c110030141c61156a00c0d5483d4010811940003501c170b81d0030407a4060040d0440000d07407100005280c0d0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 782590206 1250 782588956 782588969
    0x90f0b0108122701090f031b0e010b032809030e030114060a060c06020d050403050304051605060a030b030c1503040309080a020a050f04141003050123070f0509030a080301 75
    0x151a903056102c041003c3c0201ca0020082400f90f8090300c2041200000f5200001d0043c1496070203699101c59154000078180e0096980c0c8000091582441404008d010090f02c504c1c554510294180a01464507020003412440c0c22098220440000301114025050001c14140b007844241031070718006200307085a0246500035030a101c1c1440b241e0b90380c905c0303051068101503c0150513a14040003100d80e40d85824043e900143c1c204018440714103035000d0ba600c95402038503502d540b41440d107001454201c100460fa940c0282c0c0590900c1255a0042181c4050b000e030b24010500c40303c80c05c0041d061080d00c4001d2a80800400c580721a404c0792031001e0743c401c43c000d84400080c0c0b80d4480069840f02c3c07141400a50103681400e0034420307440e0580c5e0486580d9400b03000050f00659203020031080701c0003030750011000038081804000308202402548038504450045241c071344003c214103c4202d1000d00500248114801c0d02000c0d035104800795180d0080003821105141e1080c202401c59074020f02455 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 782591456 1250 782590206 782590213
    0xd0506010f030b061014030a060906090207110102120301050d080c0a03031b0804020a090e0c0a03111c020a0b090d050303040f0b0609100e09030d02040b0903160815060103090f0b0108 80
    0x7504d54a064491858207421988507003e114500e03012a60103548002c191032002c0c0c1c1d03640008140d14099100b2003024190605d001a502c45003820119070280c000411541154412400460000244400d0340d0450b5410f4600b015150382e82d1034007040b03c1c000c020040b031861040a001009040d0306800040c20410a407428030403c0a1009080b10701c44000c03980690000c00301301d82041030020381d034070401c0c1105110b425102c18010400024520480c1c5502c159418200c0d401e4004030343c548590034210030181c4000310400318000d5400b050703210760305228a40d1100e01c0410b50074441c0c0c88004417440103507840381c20381c1c2c1c1e28501031422140780c8503103400581e40c140c50500041c6135820000c160f640182c3c03e00d082160601e280601c014004000101f0103c40307070200380140303a01401280054406040201c40c00c0d0780f201050bc1c145480d1002210000107410f18610040240c0c0001280c007910b081c00b010344482c4aa500e00005801402c040b040041401011820b0132044c080e4040c070060507105081c040c0c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 782592706 1250 782591456 782591461
    0x2030a1416050415030b0306040f140304050d140109150905060106030b2227050d05032811040b0a0906030e151f06020312060d0f03030b0d0506010f030b 67
    0x4070800c0108030700303a1020540c100020300c034200703d108032420079810300d240100d01d554201c0003281c10440165001c40355020043c04040401211102c900094805071000b542001d15240010301e0f00205520080d00030107041700410502142900600b0030503800c20b4520900401184031803008041c000070075201c40c0581030011071070070b220740903520101000a050751224600708407800c401305000b400f1503011503038070350b18250010709607500507550702080040f0144003103042c1806400d250903042c500080103010420001002684252142042c40301084032a13203818802c0660014115045100114000420300181000c1d0300300040008841030356440e07245681c0c40f4819419901840070460700d5400c04400b413080c042d401c0d42015400300341070046140106480c40c60190311680340d000200140c2000941030440d01d5807020b9560040e0050360380c070014070300d51744882d80c40c560503240080c2016150801c910f841d61b90064a4094035400805070b58282d44d4450488001c0070003844111540d17501c0000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 782593956 1250 782592706 782592721
    0x30f011503060f1103061e041b0210090c121502040b270a0b180d0305041d010b030109020c0309041b0e011134033f2102030a14 56
    0x148001a81142802811601c80c5030401401f00d408001e10300707220900d4668082c80d40d803540030360192582c0c11502081c0840115000909208001c400a22603506011001e00041c840f80780f410111030210b007000403c5240b914115803e807100c0109070003441d00200e400300384044840c0052503404410340782c999031010b44400c6111900d8010710510f50104004c10100310760120324008210b21410750f07081c2042e8102ca10005005084060b0b02603000550100342441400d8900c0402500400020040d00741307503142c640050030600c814010501d2003900400c1d02c1e440c1c00002c00a80da1212001402440441c4461000d400f102c030300b000380c0e40009030001560f42040d5010b940601301d0340002c0c5001d0b00382102110a9a04242000144401c3e031100b0703100b442000050408081019621510310250052242d021007165030900d10b079100030381500700c08940c850100008090240c1005070415142004410890610040c1401e141e060624000800c1007840c400907031081c0340c000d00c1e0414061072901c8004 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 782595206 1250 782593956 782593961
    0x3041502060f01170615150d0603110306040f021c050d081906140409020a050d0602030708180312190e06100f080607080604111917060307050f030f011503060f 70
    0x100c2d40a5401a1000ca5400606c0e011786006862010f8011101c40d0714010055110b07910461036100a15903d00c01032080050300501803001080480c0100100d0419407250780d0b0062040000034415a5903100c07860801300b8107030f40790302030507040800c0d00c3da51b1213088000b92100130101c6200000001d041000c20380c4009c07910075142500c10203840340381201c0c24081488020040401c090f6848010f0441c00112540e030382c41ca15031010300c141130241e180d0900c140054a1000090104141045100009000c80c1c0c00003003a9a002d02c4000c040c0700540e1180c1f24124004905d1503039aa40c0e250a184103010360100001e0b41c0c0d80034007410300c25a202103641e407101c000d000c0014042e050694002201042440b03106142141e0400002040081c40707240c40311800308030f640130007a416040409402500450380d00642c0d18241c040c0d000c231800c2d030a46800b8001075181d0b0308034001c481c801c241005009900342c070b040140c80b034900e01c124000c204a9a2040500c0b070800318510003140c00506020f141180351082e070 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 782596456 1250 782595206 782595239
    0xa08010212010f0b1b010e06071e02190204090c0e150a0b070506010623310b04090c03110a09031401090804090c11011103073002090303041502060f01 66
    0x1204e0702420122100900003e40c103a200304921550740729100519411018002a03010f1180b6807524008198524040c00c3c2103900c0300c0900c01950000700d510301c100c40b807103000d002c2c0c459811900042e03100e10394905800810007580212100c0c0301d041040094070301c200300201440074004c440c0c0c90303030880d5240d0340311145100304030300204150401c000402c00d50780507540c0d190b130700070910b010b03010f554110f031a0368241d907040404440302c1c845482c0c2c1c010f8000d0702d0340412805000c8423007840d02c4450b03040a211105500c0f440c4505010181d484404400da540f10340d12007aa100c0a44490582e9040c45800041080ea041e0000b510a40d4000c800c41c801c0c0c2d070b0148604502c5070b0340202c0c0942003a01d0101100300502c03680004105026011500206140003842125407a0031405540c98072030500d07481c02040075445400c114100c1d40518040056003c0c02c42319141101d03c15500960340311240390101c0c0c2540202e034440e8060f2040700c207150304560b40226031184920110003014520f0b0b80d90382c02280c12010741 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 782597706 1250 782596456 782596469
    0x42706020421120503070c0f0b010e06040903020d050a120203150102061f030201230307020f0f01020a08060f0616050106030302010c030911190b0427140703020304060b0a08010212010f 81
    0xa246001c900840c041d643c030071204d0600782c410000f1a258480300a501c40d03009c44031004640b00512201c000c401c2490b422420170395040000020701c0d6006507a034409280c0b01c8060103004111004501e1043c0c5c00c440020a03130040540d120b00780f05038a03001c0007440b550b019002d8003400d000120124101c000301c00c004614008810600c600d540c0066a0010301041100c0c40782070801016851008401c008500522450303000f0200b02c0032603040c1905041c118440300785243d0040041c0321005038000803a6400000854010103a1141c62000a0a62080c94040d800c000e5030f080340407081c0700c0194060340c2228000d4000b40079502d02034400310201c070108040105070005004600b042824541009015000c0030612a1445505d40c15002000d0308594440d06a0500d000403040d82880c44d58ac0c01184a5040d900c2030003002c23200300e880c030305082c03000b00008100350f07003c0001018444281c202c80100380e03014003201807913901c030712009000c4d5100014070100104981c00001e004400b030301c103420480c2c48 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 782598956 1250 782597706 782597723
    0xf080f010209060d0e070e0405100c050319050a09021207140f090114010309060f0603140d0e06071a1509061e0f06130f030b1501020c042706020421 65
    0xa002001c2c1c0b0043c428803451013a01e106d14100800c000c4644400280500d0145004101042c560920300c0140c455140f042c004114091040c05104501900c1d8580c01428001020544e41c1c1e6140240c03004045650002e903001e5050940c0210750840442c00c1c2c8150307005030602070824045ca405101010130000c0d4590b8204501c0c0d0300400001e00845411107a42c10705250104011449407515025658ad0080d41010207588240420422020b1184481c6000c4490050419038a20703030406440c2c000307121041405808000703050f808000c542c0c00c40346042d90249150088600b044900050445103900c3d1081c007440080020403441e18000381c020044001c84403400341c1000c101018080440c1d16158490340104d01072054205d41c0310700380744000c040c00f03d01c000040c0207840e500303101c0c10030306c0054990a29961441398109050340e0101d40c0200140d010b4402140b402c1c0500d00c800802c8060220b16000818007020319000c1080701c2d00100700b2140d0740802c43c1c0a01182c902104151048060024140301 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 782600206 1250 782598956 782598967
    0x90d050a05071e0c090b1f0c0311060c03010608061c02100c02030303130627020f010c080a020f010b0418060e15011d01060c11012003040f080f01020906 67
    0x80c45600100344451042000110900000602c1c40b010803490000f244c003029101c0b828420b0002d079100c3d000030703440c00700c4080101300404d07078444580c0500c052820b03003040300c025030745824540503c5011020307680740702c1140d01900d000c10031505903400c28051600001c080c207020400c28a0070072060031801d0610305046c5241a410343c04c0080242a0154000030720910650354000b507601031010398400c24002281c4a01140c191171f105048070b02e0728030000c0d43d6002c0b80b080d4000f070400035507541a00a078152000301c040002d400058444503074010005000c03410024400f3380c840e502258007802079010b100203101c0c24580b4402c0105481c0130f00750304076603061440041e402280c8107070401c0b801e04201100b0f64100030840c071403c0710012805d81019419003107500102d1700b000b5424400900502c0c0c949000c440100d080e50301e08200d074003060b00e8281000f0180b2501941070710180d10618185000e041143c2e5103a82d16119400c405585206500c2c00380592607034041180418002c41d002ea41d001440203150a = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 782601456 1250 782600206 782600227
    0x20112051902040305030408150f07030b180103032f120f121f0e010b0423030601150809030a0e0616051b030c0a0302100c1403030c03010608090d05 65
    0x100320007081600741190a903009080307100c1a1000f40042c0d40940081d60b583c1e41425845481c0034251040f549103001028200540104140d2200790400e02601e4041410a8100c00181c001d0a5a400310060f110301c0800000405030042410071018070012103070700443d028209080725406c18203038004241e0b00441d25031200b40f44858010202108000081410a000061655188041240c140424030110550030403038001d0410400010311030310001c441705604100c0c10a596000307601c110000e9028020601e0720b8840344110902e620800501251101d6950369000480710b0180018803004c0380400c4045640c20201108070b4903411050784950400078498810b011140c1c1c4411001c185410a0440e69000a401805240c004514844a4000c0000c6140405041001d661942071246214800420041e241c10f09144400c8259052070b03a0812070a0400700083c0302c0300007245410b40000001c010001030072070043c60584129580740101c1e076484c040c2e003903034442c82042140d01081003446075030042e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 782602706 1250 782601456 782601461
    0x916110c06030121170a02060c070f060507030212092a10050309100e640807030305060109030c030204020a210f1503031202030a06030b0c19050403020112 68
    0x201441c0300c04100d0858454803081c218400b1445c16030b0282c900000d4004409030704000b0180c2102c84a59180d16145e2190703a404000e0714421801017045d91284000380300030f0700941c19171703800024020900f02e0520303111010540f10380300e41644032039108210010100012040100f003d8210303029005031548942030201b40c034039420007004500b40d4070901756118038441030350003040c1000030a00020004002d07900714840d0292007400f40030f01e03003a681c214008004000c035158062401185403200c00c0320141011041c1050710f540303403100c240030107480b9075400b0800400000d0800c030703005ea5000c00c01500c40d200111041b80d0030744805004c40030702410030b101601d803940c0140300e000041d0400b01250380304086038441d20510321601c4407030075a440c498030281c0c0b8000d00032800401174143d80045028155170f005410041d80580c1442c035190301000041168032140e200201864100003041d40600d09982c03100140d52110341c140c404128058070401001e4043c00c02c1d075064075416120203000b01c5070074101100 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 782603956 1250 782602706 782602739
    0x706050f030f041e05060708070c05060a0e0c0303040f182a0c06060e040302010f0e0307061a04110c07060302070b0c030406090b01170c1906050310050916110c060301 73
    0x10f5070780d1444d4031104000d005051010109120310040c2501e4603290001802c80d4500405110a00482c569120f00040003c10341903170000c41c09400040c8038a0303000665241482081c0705c40d030140710018002c109042c3c4100e9078001c5607a40c0351071500d000c0001c01036400341c1d4003c85862803080418400002c81c126069950015121585020911038180d83c0700d50040d0303041a80b00340d4080c0c02c40300070710080c503a081c010f081c00c00a5846061146c96070b13070591903035a8030910001428007a60f48039400c00c3d01032101032314501024014030520885032154803a6015901800c02d00000d4031070a07100190329402030081d284000e0300703c100140640d40350341030100c860340010021118580d65000c0c0310b00140c60000894044c00064410349180300f010507001c0e00d0b20b00206000c91068404a10340321001c558000450140d50390303031500640b40d80703a8a0351041420a240c1120380d04c08003202c00c00c80208421062440041c103e035650b4042d440050a441c0d80310341084e1701741c0da08184100700601c003000c2d0071002c220 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 782605206 1250 782603956 782603963
    0x102071113180602030103031d0312091906030c020d090f050906030102120c03062d1002030409050415050115140a0239062d040503031306020706050f030f04 69
    0x42c0b029204203400c4080b24101000b01c4083d54040f0040c0203050380640100f00d60140b07070700140c4c0d9a00c04400020303179a07040c3c507084040200002500e080386480c0d0b042c40981d1441045590020107440380c10281c0900080d240d40001482840c0302a1203a510a1300000c080301d400709a48507000d1309080620504c0710b0010443e80d0559020802c3d92680007950380780502c2000007602c1c8a8503400c0c10420896a480100c0c0412205410100e0b22040c6070101494013401c0d5004072003401c44801d044a0a9043d400b642c0d1000344524904070401c000d01c01c00540000070f003a07200030204981d82e00c0d05c0b60403601c42580c440c1c00340002d00b00b4080c82c1440c13032020018100039105004032038500705070040001e804002d0344102421184501d4014002510b028042c489105084a90508102d200c3c4000e0010004041800140c8940341140600340b04e051000c1384c000d0034000c0c2c2aaa55110548004003a00c400d0f845840014841d680300000c0044c480c0f01a2901d10268020443c0396480f551040248500c02800a5 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 782606456 1250 782605206 782605211
    0xd2a14040608180a060b0406170c0402090307120c0609061d040b0a0b0a0504051002030c1002090415171501060f0c063201050103140a18021518030102071113 69
    0x103d044804119401c1500e01c01c200103d40e1807a8801031105071461039010390610800708208000c8101c010581030404101a07800584840c83d8100107803804038554800b510300030540d85401c007031000d450b070300c9001d039036160301c6003410342b036450f001142c0e1302c03070000007800740740f20f5020400200c1e140c250461592000020800240240c503120403449560140858802144000030b08000300c0c2040e003440c1791070a41c41d001442c18800d08501564482400802c0c901589900058a00c000d40d299840388100060a94804480644604079441e01070b042e00c0000702540309401d1b214110f8564400094107948840e07881c103941440502083c0c40c640540e10085840a072208500300240900340503007203283c0882013900f104170807800d03110100d00340180c001c11b0405013888852007405418038604c2d27401c60b20b05200000c20900c800c0c01d1f20070f8206840c10080d84012030081f148994200710010b401365000780b50400c054050703030f03104150807482500b40040003041c42200810544ca003e5400110700e84106401 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 782607706 1250 782606456 782606491
    0x301050f0d14070602030a030614090c0d061a0a020c030703080a030903092d060f0c1403190201020315010206130b1801090606140108040510110d2a14040608 69
    0x140c20010f042e0001c100691002c0b40304410a5418082c01c4004c10090428600c1951600f001c5615440c0c0100042da90030b0000407040c000740010f0f0b000700000d081c6440b07020030340c04a8510081e0240c3c069181c4000600c101c0c01c6c000440d14010480c1802c89070b01605c0b0514140c0800c070154043c0154003000e03014025112070005030381650140e140b10314180c4035090100080d00d60002580c00003160404c800308059040300c8000d00e034102d00d181d4409030300480c0c060741300492402068550721412100f01d40e2000508140106160150003840c0215060020341c044070183c20012a9501c1085922400b00c208245c06100460000c4007606e80020b51213183c1040c0d0350151103141d0035a41a2202110712941d114801c01001c00c10003160f0469403024640380c00306042a444403981c8030b8a480207043c400d59541b050390800002e030401c98124050400c2c052100d101504490602405018003036038860170445a400b841c82e11031242c042c840303980500705030306007400d04004031680c500c01003686803240c803440c60 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 782608956 1250 782607706 782607743
    0x140f0c011d0a08060711160306110d0222050103020a021203061807080709050f010f08070509180412030b0a030b060d080403080a024e12040b07050301050f0d 69
    0x99800c00fa0010702c004041074200000f00a204541c1c900050b415504500c0b00510b84d01e044602803802c80ba040400460103810314102d03d41e0310712801b40c4107201c00388002070840d4690302d0281c008403071003800c00303960710031507500c00040d401d170b01c070b03c61044005820000c10400d40d6503104010f107030406000303001c060013a226601070b180111815143e1101085400f0b0030444125402842c0202602e001c0d280300400110100018000f00c040c22101c20500099500017620f40e03205400385d0740e04120023000c0d11001d150321110032540440649007501d0807521001c125650900038051100c803400f02a09410300035107503440710300404030094040e60b4800444c08400010a8025016001a50042c00c1069440018041c0a072508000c442c400449103054840d0004158030780c500d12403001503c2c55500d0100e150340e81c5000183c4954103a924000e1000b00351544480d01d8482141d1085100c0c410111141e01c8600c07003664640400d00c9100da01100d002500c3c8800c3c100b210599507d144280c0b060203507ea11041d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 782610206 1250 782608956 782608969
    0xa080705030a14070b0f0c4b030301060c03110c0a030f03020a080a0302090301050f040507060f03020c150423100207050c130b0a05150d02070302100c020a140f0c011d 73
    0x50340c102c541008905540c4181c070600000119008001900300c84000c8203401d8180403000c2d8009800a052817040d00d04000c800c200311238989150882501d907290b031900c0300034104000070001a0001045c00c50000c1102c18002206116050014102c0840340e00d159200c20303000c00d03030003c12021801001c80c02c03800a078910f0007400303c0c000fa03502c0150712891004141130031128001c0040c900310486005201c042000881ca0005444c110700d400714103140400c2c000c1d40648283d483c505007510520441c100c0000321005250301482c13140190020190040e00a00807240c8010b80d890420f0b00303d17602048950711340d82d004080052065044c0e440020b0004001a201c51709104094007840e1144400310b407074541145020040c1c4021500102c9625140c0700c8034000c0c2c0503000c071064000b940003814100381030003009012190080d840c418801c58041d484025281c10004804a90340895000c44004c030450205981402410060040100c01d070780000450764442c0003480e80a00343c61842448820380c4074103 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 782611456 1250 782610206 782610217
    0x3050304180f05130210030b0d051605030a12080417071109010501110318030a02191e05010c1b090e060115090303020703030831020a080705030a14070b 67
    0x1d2811403032403201c845800c0940301c0310442c840040307141c0000c00c2010404094021300c0142c05541d009015442c0c10003d400600072200110303070100410306443c0c2004400101010b118421040a0080660741c80515540f694000c03001401c1810b4002c818036506e02c1038010307951245c0550b103c4500000d1030f01c001034017580b0240c0207132010800d041c4007011a09203d000c641c0108020b2034907181c00b8900d07907481626070080000210021844107581111503600308880340c0701070f800400040500e076a1030f1b03a10301441d0161244a15900800c064804150804510901140e8041c0c580000e1500c0d41c0d41c40c0da03001c60030200410040d244580b0b01003004004c6100301040300d07004034000e280ca54141200d540281c030107554441c0401400050600001e580421148101c070341c0342c1010051500c501c80c07190070307009492002d0032400e143c405506010381100a0782c1c0035000d0099640c021956240c1d926a9140c401500407160194450b4416500003901c0c1403030010142c1401041c2c807503246e04c03404c0d01109039202 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 782612706 1250 782611456 782611469
    0x40807030f1b0602190212040e04021f1d030a081803120a0914120705090c0d02032701090b01060f05130e100e040201120905010b09040311071712090a03050304 70
    0x320340f440013980310115000c1103021724001041d640c0c440130b001714520311650242c0c541c90510b240c0810215141c8120491a454411003132010403504e198005203501c40c44a4200100202c00d0050240781c01c4c003060417000580c103c50003915004a00500040e000c40b2201003941501c81c0340d001c1b05101007480702500c0204100c0d5104404145056010141c1d00112101103100e226010019002244006880803c88105984000e5103580d5a00201094002d18001c40301c110700000c02c110305045207408a102c0000388860640c410a10ba09001d4200d0b0072400c4000c00c000b00b02c5006114450040812001d1031005203841450000312010242020f18540e201d4080c0b44040803e0106400e040c025050140c01c0302061000c8525094000800115002c500005040c1e550204181440000c1d000a4010700e0050044007c904240c0b4000700300b40700c074403e00d141a02030034074046a154146402c8440300c0701100014044084d0450a49500e50300400b00c1c00d600040100c4000300080c6c080c009030004045 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 782613956 1250 782612706 782612711
    0x16080702190b1503010e070504090309090f1b1704140a210e0d0503030106030207022709010e2a2404060921170903071202040f05040807030f1b06 64
    0x3003495106410480300c4a103d031181e4141100c80d0b2038014001619401c8030021200400d4080017400d0690fa0f80340c2d103400110000b814100100130100c80ca4114000032030380f0b40404040081505000c5070800003480c0f5005480d40c00e00041804104414041c8441c0394400e8240d80c4c0b105520f668542005c0d030740d000440e100307204280501c070819802c002008a021016540d4914060040c1e6810341c407440140540424154041010420b640320404400c0c640d148a81c00f220800b801d20016401c0680111141d20700c175030030710990344191800410406e10050a200176040d210020340b25200c0ba4031000c080780f41d00305211210060013250898812949181a1700445a9490901600400700080d54110f1100103050402000e141018003e0416005400c10a0b204260102c40307107080c0070317203c2c81e00c00c194940700716600442c10307081d880e01e0314221510840742044031a034000c0010003503c604803070190242d40c040c4415004280600c070303800e800c4085490301c00740391860a900c50305000c10788801a14201d5 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 782615206 1250 782613956 782613961
    0x9070915090e090303070503040b1308040303020f0105010b2115040507110d030c080a0203040c03060c051b0d0804030c05030405180403120b030304050d03031b081b0316080702190b 79
    0x300e0800ba99508040802c014514618200030086c06501c00500024035290503800020110600d51a642405652080344591369646c2ea04000b135982d8001d807181b9100d5448c010000820098807412544961031207140041030342481201380c3c0398184018803080c0120544410b150342650b440c410b0500c192419100c01358600f4400b00510314200904e4055018545023102e0001001e40052003503511070410003015075a60340c1d901d840010495103510081085050000d0030741c080760030401038281b0130504040d12a030711a031032101d641c0c0c80388540b6520001c05e00c840003180200380700c1c01c031411200740104101c0f071500e03545502143d00c807404105032030416000e0f0001d1004150340040d20800303640c007080c801c0c090802c0c0807001a40364443e40c0719807441002510b08403402c06020341c0000c000000003002c01d42c0040011140540182412150b052084802000304945d450300402030300d000300900f0003040c408440e8030200b07481c1d01d030024150a0070351150081903642494030751038843d6490300c1800c603c0141d0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 782616456 1250 782615206 782615219
    0x3030904061d13150e03090a0b03060312040e060105031f0b074224140a081f09050d020d1b050303060907200f10050103030e0907091509 60
    0x250800b404182d4404001d10f00c40010070100d01d4551030b08181c103100041d084401981261840c407400111640105401ca070008080a03a440958480c801c02c1c1c050740c00d03c0001e02103818080c800d40c001d0342000d810020224109510440c0650707440022a014544283c80e07249601c03000c1d080d00c0d40504189540000c5030000c1100d1080c3c01c07441102811a05800501c01e84040f0402c5941002041c994000c1a04d01e0381010000760002c101100c034840d015040051102041034400000b40175801c5000309201c20303100c80d402c00140031011918070102404508110b03e080ca0800c4892300d8000a200791244040300c0450010310030544c0d038079090380044c40d1a001c14000540340c6400c5180030442d10990346503940200760040f00720303a4051002c44034400b480d40d40400503180121181da0405038400c520342c160315180c90019483c0c40142119041706e0b106110340d01c07240d0950708240030050001c5c0b5100c0c45283d06007820500150002d2043c101440c0ca41c0d10f9041003941d207080001da040008803048410000d1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 782617706 1250 782616456 782616509
    0xd060f230a06050a05090f0601020c1c0507050a0305060106051c0e010906051005060a0c022817160510030b0402031e0901020306010507030c03031808031f0302010e06090303090406 79
    0x200000e68100042c0b9207480009408106c00070084244045890300244040e0b00c00e00035040907200041c4500c001c0b04880607114080408910300310b6040c480c812010416140207030108044940c440003c0565a081c40e400304ca4a030400780903441c141c180204090304040050141800c4100208000240081f1341d05001056440c090b0408154030b8090b01c3c184015101c50301100c8031040d05040c01c40310310a00c0e00c0420200104441201c400c1e00303109009491a80b125a01041150740c00300200c0103d41e03d4200c85034a0700041502c11500741e404000c00c00035801c090000340c410401c0c031b08001490342c6145003c907060703038421035140b16820401510b80043c0300901c02100e070800e400100071411881c01d440081c100e03100740180502032116000040040500c039402c64240140c50742c070540441034407450024516001074428001c0c0c480300c10501040e005443c40c40e841201c0c1c05031f441c900f521705417600f800016444070070203d0300341c0401c000304101500d645c0130f0038005200751040e010054829a481642 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 782618956 1250 782617706 782617709
    0x90f0d230703111b01050901030c0903080403051c020613020f2707140301080a1b030f0302031809093c0f01060e0c0f0a1214070f0507020d060f230a06 66
    0x100700110715130740807040e64068159122036a0038200012042100c800503901050340d41c2c0010060400001c020081000c04a100b07101040c003c0e80206042512420a03130310703100c08581d11030500d00d1008032100946003150030400d46a90190840140820170001d9403100551410100c1031584c5c08014043e02da98444c17250348020302c02408690441d4186442503441c3e1101e20070180540c803204c3e0b044003400701107006881c0107680c0002e41420145c840c3c83c0203034807a04403200079a03d55140d19042c1d01182071401c2964401d082c01c4c4041c151144501040111f034500701d00010710203400710540716445d0310400c00000000341c03213a00100705445103201003600350303445134108801000040081c000e0035100c4c9000c0d5032410080909003074560306031000484440c50b0744182c0c0034820b42841407242c3c01c4102c0d6485240104625510b02d900154210002d44a5105100d80250000320103102e82c000b04440740c0c441880120001004a4120825001c1c4c0e0014168540043c280c8021101808030a41c0c05204940 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 782620206 1250 782618956 782618983
    0x1050d083717010f03050705060721090f0504020301060c03030903030f06060e040f060807090218090114150c030a0507020d1a090601331205010803090108090f0d23070311 75
    0x492131400c43e82c1d81c0741c95a01c0f0388151401034002241000c100184500b02040c4010345031011610200380c01d000070011100c9108120b840a481100841c80741813600031241031b196251100f07560740d00ca030f58088000b03040800090b400c06580781d405418480581c05050003c0c5000e5440001c004500c0080104841d443c0703201c85d0f030081c40c0100404c2041b0b008915070702151010340380141c64005e01c4100441000c24261304680c8030b400e840020a5103044501d4420100e6400d940715580714100e50308001e100c0c4161802019035501c20700c01c4840d030f944a2402040c07864409000041c98961998580c02041c03c80d004040c55000040e013007041010042106138010b04c2c0324140c801c00c6000c80c1d00100144200300a43d0301009403590752188000d8040c04510785d000002100c108510740e514140a500c9030802d07000c61f40040c20000109a040c0000651055001c00e0b40020344205558102c059840844821804044000c0041000a42060140a8410a0301035240c0041c09645c0b421003a081040f00503110 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 782621456 1250 782620206 782620229
    0x90a02070b160c050105010608041109060f040b240c2e020a03023c09060f13081005010306060506070b0c031f031a01050d08371701 58
    0x4a000c6507582281c1608071140d07181c04064a44a0340040b600306000003409400e030341c00d01000051180d03004a071103208901031100090a40740e1103041200300d0409035850f41c0c2c88001c0c4000c000d1985001e03407107030700f1100d80200a06655182c034210785842829001240c00c954102182580c0c0da50000c0c011a19450b901c08c0301014141d4103000000e0044031060600d000c0b565003c28140c030000d008e0342c1100c201c03603007000c810b4202703d0180a58070111164000f404019040300481000ca810b0402c1c161021214000c040d00d040090524104c00742e90000c104007102280380c0040001c01385010b100c800991003080c003000c9465819802d084013604c405070300c01402128202b1007000401d804001c0141c11921070712040e6a2610b6262401d84100e681c54241c2011442d414000810414a091840074003070081c919042940e0b6160204140e40c1484140902000f2041000c041c2440188195000364030034110400c101c4001050034007101000c2a59845c0410800d413141040203401503040c40c01040101c204c03 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 782622706 1250 782621456 782621467
    0x80a1a04080f070309080105040b091621021504090509010617030a0c0203071703070b0f010305100203130b010b0702030f0d091205070302030d180501020c01140a1418090a02 76
    0x101c61961154101c0300407400c0300840d561080600c2490b101c0002c0880710000e229505060a103440d001d802030324050170a20501e4808200400055401000c89860804041100800000c00300b0881c0700c081d81281d00c4040503a00305521100c40700600054001c1400014540c603007481c00b60708489564000001d0307041014440070313103601d0010072140900f1440ca0018030345803035403000c03c0c54058240c100040200e0380c6070480e071080ea0004041c1588600904811403d9100e03942e810944100a00018003513400c01d204050216040ea001550440d90040310b50740e15000e03a868103400c070442a08406003c030b90004501702540303010402980c0416400000d4170f15000c9040019280860034480d24201400041e07a860500038140541ea00458000c1e09032075010b40f8200c1d0040081e12800604110348034842400320b4554400620502c109106031235801e88140c041c213142206070001d030300c020100000351605c0031040d609400580a55800054000c000b01d41040030840d440000070301001226106005 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 782623956 1250 782622706 782622713
    0x30813170303150d060b030d0c021804030f0f0e0d06061e050603011701061a030106110a03020303071409150307121407080c0d020a02150a091109061801080a1a04 71
    0xc3c035100300101114107600c240d40f640f40c16070261203080c030401d81c140030702202d002e4825040360760780b0b08051080b07600074802e6007010703412400300a094901400043c1048000782c8000e00075035205100700d0240c14900300d8055000e0015100c8a86410202c1d041030300c50004001c400c0381c10414122103112180806203090a18020482070b001c1407080010900000001000b035903001e51113900601803030311000c0c00e07504006001c503410307a1080c800c40000911030862811310351800302d042300c2c030075034154091499911175403012540d000705003451a042c20010040101300d030340c1c0c1315008035660480520007034803072800c4e000c05840c20f02e0200d6900740c1c1c5800c00c0041034405802c040c0e0503501c02660700300b810203a1694040ea00e510300903a120035801d50310000d030940d2840c0e00000c4050601c4081c3c0040d200f2903880b242d0308801c0d210242e00003003c0c450562160201407070902500b6900c1200503220403000c0520b100b02ca42c00ca40207038000305c883d4020400c03141c1401000c1e80400305040301d040120160b0b00b003554 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 782625206 1250 782623956 782623981
    0xc120d020c0609060906030f0105150705030901030c0e060d0606090603060303200102071e0b150306060f1201060914070311030a11040308030103050d12051003020613030813170303 79
    0x7000c20303118160004030250260f07036840540f111340070040e01594503403030190a03140a180c028040d442c03003244608100c0b134000c8013000485070f03050740c080003542c18070100c20015006049030340403030420304c580d500e900042030300c5110103417248000c03041c030100f402882e004014000d01203e4000e1000c15040003401e00c00b10360011a94081c0d06141c603059500c10750f12040603402401641d000070f1050720103d210451007015800d0004080f80100b0150300d49403030b00200c05402115103001c036501500001b0000707907149400c03441007900580260482e0402d001f10440182141e842c4d80048882c60b030350700107114401e581145415030061440c2020400c50074000744085803808000c00316540c21b500e81a00c414920b04da601928011030b408008982c0346d5860b0700d8816180c083c00402c00c5c000620281d1030b504c3c0c0703110b24042c0741d00070100d82c100c541101d810743d000d128032980541c0c2000b10701c4c4c51a010010028003164000c040002000130300f00341460400c03540d070340c0716481c044460515520600a2207075840c02e06 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 782626456 1250 782625206 782625223
    0x1020f0a02090a020d0603030903050f061003060213030803132015031b0406053c09121b01020d05070b0c160b010e0709050a0b03010b0f04030c03050c120d02 69
    0x11034500c941c41d40c44040400103031142a0b2800407186c104040001015004803507074040d20b01c00d030140c0740180100f140085d96800111482d010074030149030100b0218031254020040031031625120a00580c403600d644000d5841a502031501d2040d861640c4280b20b640012a80103401e005d00740b1a18210700030024041a255113142c1840d034100102240706540c41c0c12402c808600c003041125111a5190f2014015402003810078204e10120b2108144165031309038030650008401000c00007415105088039807903041000c21507049040f5080c0d003010502d04200d03040700c0070718494079000d204030101d000a04000449d003111050007000d0044100003228180129032000b5401c6009480c1c0742014400240d5211070342e40504000904000032800c1c00c076450019205002a44950b0312290780c03941409622800c0c0e120f00301c501c610500040c00200124401403040120044d00c19003895141c0e01c90340304501555204036135992040c1103803283d0b0f041c900365860a5407512406060092421140a506c03000d01 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 782627706 1250 782626456 782626459
    0x51b040c0e0d0b181f0c0309231609050702010605010206071b030e04020a0801080127080a031d03030f0a0203130210092102031501210203100207060c03060501020f0a02 74
    0x4000000d00241852914038004c24110b00840e0442d240600000c0641c071030100e40c4203407080c10011040034030b034001d020704001c85171f0245007000742c0c0d801d9090300c0120649024601665000d1060303201d0344d006007110010003601c00c40d0f40000310784c200f070003001c1d085410540c44035044d900401e08100c0f0454003d004445008400031b43c001e102241450120f0b4121a02045554420f02c08103140d11601d521000302c60580e4100d800030444000c0c1c1c0e801c1102e21644010f2504240a00c0c0e82e120000a401c20014104200044c1004030320f501d444208601c603489504d82d2012640d00100c00c10080040404a1540001d004402141b4505205500c400745540c0004007031300a410309804498428800d031900d01c0113243c0300020303010001c0400b88103c21581002070030b81c813900c90900f000140c2100104002d04942c1c118540240c1c940c0b66042c0f0f520007480044050741d16000318048091079070035500040003000d01c500000246104544409402c5a00ca90070180c11507200c0d0000c0c01c1122000030306800307500d40 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 782628956 1250 782627706 782627723
    0x6030b061215041e0c233a06050a0e13050c100f0e06030c04062012070b1807061b0507030c0302090f10090902010c051b040c0e0d 57
    0x21410781d0741284140c10b241054001d0702c0e24599100c41104a9082c40d00c051801a042c090310701c4c101c8049950301d1600c051070080884048003040d1514180c801400c04c100c4180c02130f490500341c41441d8444000002200d1035000045c88100d1030420240704000190400719a8000c0d25818800c0342c0284950040104488040c01030f0803400b4440104510503003450001d284203440e400d810001894800480444030200d0070450500e60039241c0b000c1a0fa10840d4814500c07402c00d0314050307084818041d0b8048109022030012400c2245040034405010380b03c0c0060b4115517140c45a2a00d040003080060201c001c0304074020802d00c842c030340400d07034100300d4200d45010080c08006103000e001e071020305200105a842204000400c0064030300c400011a40215814400741d6030742d00001071001000c035141403c0d1200b405092000341016403004040e0350042c0360000d44000a95503592030410092030341c84540c0d02c0583d50704500c0c90a4002d40d038842c038141ca0702c40c0075600601d000c100c0701e040400f0010004003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 782630206 1250 782628956 782628961
    0xa0509041e060510030e0a030f120509031c0c0806060d1509051509040506011e03050d120608030708070807051501061809140a090303020405040608070f06030b0612 72
    0x80c0c0d50340040c10010040c50607038118680044107880200401c1c401d860103000c3e8040b240229502a200300480b180350740016000c42003032503504460b50806e0200c11400d114422402d103649660703511406125903d140011a17441c18058601c07007103042111341c0c80074514141b01c80d01040f290321007004c1d50058001c0d6002610798030a81010005000c0281800700450801c40700041c031740c8029081140541c5583c0340010041c09104184801d000b001c6030064101c0c0e01071310041081d80c0f00c030344114591032800030411501c0b40e00c0b5604c490500c2c4410005000048c444040c080c4004010701c102c0380144980c000540c54507940703a89410702c0d40260000036081450108246007409424401c0008055240348c12109540e1500700c080c08040300e460180d80b5071211100c0225208110744504503001c2c0c06907078125410790343e0b5000c15000e08504c0c00120200b507001d005c00290360321623000740e0014012a45c0030344003003402c003416003260081a60000e0101400e140c81c94bd02c54407a02c0445008200c081100102503 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 782631456 1250 782630206 782630209
    0x717030105180c0415080a05011a25020607030c0302060906090c09090f0304080a1b0302010905120c100207030303050a020f071506030203032a0d05030a02091c030201020712080c0a0509 81
    0x10300035584014201c0c04005c0d012105280d000e40680d00c1041140c0c2c08000c6662240080310f512540e0300000c1e06085000c1005500d58082980070640250801401202c503500560103d011608003900841c042215810f02e002010b805104140d03001080c0c0c1c00501c0680707003030651142c0d100c02c82407000d8000c59400d404602e0030402070022003c00d841c0442100d56032640d43c01c150750b4030114484295a032519170000c4d010000c541604c140c046a4059403040300e00c0d0304001c100406044898030114880c414180104010307181d452009068070403940162400c507285007409030640f04020300c0300e450070348100502e480420520040c0e680322a0010301c0e0801c9030700036501d000010442d5402c06980361002160440000020f582c4000e64202003d11000700c00c0100c0114541e030300c0c0a1000304010400501c0000c01c51071859014083c0c2807802880d1001e0451002800d841d0644030401c140c005035000284141032050030301c8014038624203403a00003018502401c10070320a0080743c040408020000464030f459 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 782632706 1250 782631456 782631481
    0x30f0911040b060c060108061f06171e091e151f08030301080706110d02061b070206040b180d0c0306090812100f06020a08030103060207030c0512071703010518 70
    0x40044e500864049513155075440f5581c500844070340c140c00d00b16484c05241106520b581c9411615140c80d1001038581d04810420450780040600308403c0d504020a8003004126201c41d004030301c003001801d800c00b80200303c4c00c2c03241400d43d0000c44540c011048012400a001d080325844560100252006c5140d05400401d413502c507441641e29100120001c20302d038a000c40e00d05e080390a03585508aa003413460002e2511012204040300268029000040000d00605050501204e603505501c1c0380c614a036000a85d2508190403410f0303014800b0840b01c0088013155103809061908a034001800c19141c0e460a030078410f180002000c16884505103000c1013114800e480c4820405000b102aa242414001078581c038144500b1001034005900018810b00105e00040408c2d048445240f540e030075038503614041d42c0b00210445c200020311700f9810114005006803500c40c02c4807004143e903800d8904249503218010310200c84e0780d00040004000582c5d81404100c50704500301040d10856680f50000400c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 782633956 1250 782632706 782632717
    0x319050309060c0a0c0e070f0809030328060f090506120604080904020409050403360909020a080313030606140607030f0e030d02010606080109020a0c0f060b061603030f0911040b06 79
    0x440b605c0f1107000302e00c0104a00541d48600c09603a105c501c05102d01d07601704e074100c90907900910103420400105148a503105806411710f1b2040d404074982c031040c40c0d010822680182d10a41040074110b60070701015201d800381607002241220061114003a1a110303a495030f02c0a00010503138040018450011307156601540c0042110603402c201501d841d0901400e5403a12598442c401c64850500001c40c651074110b00500d001d60044844441e4204104d00c0300078001814241da12001000c40015001d034100010003503246482c0d00840e46ca881e52501001f40d4074a5084000060a0b038564600d1688494050300d5a40c2c0d050715007000c443e01e074443c0903592100210f14854042c000d40405141e02c0d60150020000c1300c0b011355681b0441c0c0ea03540d000000320301a0074440c80000b240500344001003150710094580e0f03036020f440c0001d101012180000c1041d03010f102c4004410906240800030305806100d110485003486070300b07004c0c040301c0f640d85203035005010600c1442075a0342d00034080d554444400351030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 782635206 1250 782633956 782633963
    0x51e101806030605122109061213150203070f0518210c0a0b0f030709090f0614100e04020c0c0d05071e060504090c0309050d0c020319050309060c0a 65
    0x505650700c40c10020040c200d1405000d00070700c82040001288a40003914220751103840d11560f05410001815065a501280c0c1e0f035944400e05124582050b4000c02d40c15020707c0000783c00403414006450004c5a60034440c2c07080300b10b58414810402d903030390081c0c045d400314296403404903504c904400c42c0404400f403690001e6003061082d0840e4a2074074510850300c0300182010101c0e00c001c2d8060042040080b401c0c01801140d00041c005207505116a170041c6401c010513040000342207455010b400304451084180080990b120344040001320008941c0007441b11040e5032545400d01d01d00d501a1900004140307250090ba8001a00020f80c40c003446818100d08004013202c0e611a000d04002d660b8440d14042d00101c80302c2c0c0000503940300c034150320500884681e5110b49060519100c46100100000382c042000d040e241d005c04000500e05101c4c802d900d800c56214a40a41041e006262404860052040c80b000000c90130380040f42000043d601c403204122081590780c07001c20300140c28142c1210004 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 782636456 1250 782635206 782635247
    0x51b071208190f0b0a080102090f060d060e040803010519060806190b07110a0504020a0c06050405121c0e01050106021f0b09090304080c011d12150c0c0601051e10 71
    0x1400414160418480c8500417100300742c80644416071035080b07110700e035540f0b54800460802100c0d1402c0c01d4011f4900c4141c04500040c003241e441c070540030380840c11207040716041c00001c0140420300d024184c0c5500b43c00e84200310fa000302d0510344058407802001e00168400c0c0c444c0c15004841c040d031500311101400a07642001e889454a1a12000c1c0340c000000881c41009501c801261605061007540e885134a6550380100f00000c40c0c9074180244806030045d00c141c024400b501c2800015200141a1201012050140070a10049036070031a03584e07440f22130f0146d0503c00100b00180d400140d0100f41100380d02c0c1000c20b9105541e00b50010b2080c849075035081101041080f40e0100b0100250084030624002d40d0a100c1401e80110345030010f094041000c1b08425888881e1410203145139006162120304a840305c403103070300000d4207840f800c50340c2c0388050800050144c0d90031001c2c010a4010030080c1c91282c2c6a451440c1100c40e070701c4c0300307e20050140f83d0302c181c40184c05204a40008103083c4c011b602 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 782637706 1250 782636456 782636471
    0x6031606030606020111030708270105010b0306120610091e0603081b0a02010c150e0f010e0d0206060604060f09180207120809060c030903070203060a051b07120819 72
    0x81c0c090050391146101652a0040891450b03226000303d0380301344d2103503544248568499070441d85400c070a54103400e011100e05d18403050550309104440c0644115030001d0b40701d1810808111038940c03400758402480e0040c3c0b05105204410360080403d913401448045520341001c46582c1510110540300301c01c183c10031034000300340b00c0c406000304810f4401c07000c25002080400904c658a01d42e204001340004d8840310008042206810658100c0c04021000700c1c4406024404602d001c051289000169542d0342c8070501c80c4404020b03121007418180007403c0c0c5813910740300060407402a4800e05007440306400745101510301c2500000c010300349800011500400da071034114001d400503a0100d990218521a11003a117000c0c030841d9124102070402040315686581000402d60406405130308540300900c400c10051b90305201140c860144141c1c0000c1620380080f455400800d40c0708080a918000c00c00800819680300400c10407003101d040599039030321400182c0d0b040205515000640900d41500c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 782638956 1250 782637706 782637719
    0x70c030b150d08030103060c021b040c05270f01020127051c0903110108060f130213031b0603110720150c010501060504121e0507030305070b090706090e060316 70
    0x5035050747e015071010000c10580c1c4034180c0c0c1e2101d00380c00c0448100c001c5044001c003440c003900b00880c145180d151281c28030303194144060f03000a01c2c60b840460070102450050b010f0503c00e001c0c0707030410801d1000b4000003485035803044814034200c0f140c090a01d4200215070500400700000d050720b076800c202e00b921840e0810b500504134051030200301c403040700e8200c5240180d88143e001c54010580109480c0143d0040c0c000c0154030f02c0c0340340030b42000580a1024503517006515020368000c5d4069224102240015401e00b0846000c50700964181b61801096040c0206444250f0b18140d621881c0040f40110360000c007400094500000355220302c0c154100c8100190640103880344610ba40000d000c280d88650055840303019034003407035001c2d045040300480070403040c14101441d454150781c00907501d900ca450b075a041661030340042e008910001803440802ca00040e80513031200713070035015081441c1008d4004212005a108024640c1c04410100d03145a906021445c855440070400012032595102c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 782640206 1250 782638956 782638973
    0x71106030123120a050312160f110106050907050a09050316210618060b030f031905190203030402130603021302090f030106090c1815180324060902070c030b150d 71
    0x24800030030b821700d0008205008e402102001240c1565105c1090070307a00c03000100c40000d140418500d1a40d03c490000480d0b4a820b41c80c5801107102d666840e94400c100c001c0540b8244860340f01c01d0195102e800f0485000808524000641d48410001590340301e007008042c89407920080c000d8040e17860401003407009241e002a411421707100d00f409000c035040690805481e05000c41c030702040c9401c2045003a55040740c0d44a054405006402c10398108231007101480500310103680c103140581c1c400014001503140c91260000d090b03400d030740e06001d464203640c0451203000c41400400000e81d00851200882e07681c1c4ca01c0600c0b100c0d0080c00030015a0741d41c10350140500b000300412070100d44090030300c031442c1010b002c2c0c40c401d80f1400240c14103454803140342150511420151004c01204d2008003000140a841e010f4000000c017076490070300038200340030030310498515070702060303a4610402003800011172040300c2c803085076003240604605075a0215203444259480c1d4040340d0150108031805d003000b6901 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 782641456 1250 782640206 782640217
    0x80f0306040605040209010804030305060a0b0c030304030806030303010303140f04050d060915331203020c03100b28080102070c031101020114130203010f11071106030123120a0503 79
    0x4681c20b0041d5580c40d0240012440b400c4c03906800034080d50b00003000300b4065040282c001401502c44511560745040d40340090f000750b403200d40e440d00300105010905038415103581e009403044010f1880e5500d9039074081c250b4003d0340c09103040f112001c0b8400c01031102680c292401040080c11803084400e042c03810724014001030404985003a103180500d169220240706070b00390b00c00c0032848500d2801c040009081c4c1d401103c8800c1000a0907424042a010100165010003070321a07001022001c8422080504007032109001d038000a20380a4480580c3c2c0d00d003101d0789100031a1035501403020340c0b00a40100d6680d00340e00b00b0300303880d0300004403841000b010700e18107400c907401450290042d449180c012403c0e41d8603105007001013a20303a0045101181400a60719190744014000180c80146a6400d815a08424039003140741c0b6001c00c1b04000e01c80004080d80c0d52840403512079146605002540010303080f030010a0030700c031441100c0181039032100100900c1000180040b281516000d00d01290340b684003 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 782642706 1250 782641456 782641459
    0x7210b130e0105070206010f051302040923060312041509230103061d0106052104120f1e050703031103012907020a1518080705030d1e030216080f0306 66
    0xf4500040d000b9440400c2c0b0303506a81c28100072250161400080114100c61000e40e00300c8283c2c01c210000b000390a910404907800034542207200d00c40325801c400c0041c52401010907002e41c1080c0391403c1c0d858005021581070f6004400c0a1022440700c9038100c81c0e04900d03070862240e0803d80b9000400a41404621455410090341c090105503250022050162000380d4481425004400140040d42c0100d0180200c103200f58456007403030300ca81c034602c10100b00a80f41500c041c2d84401b04001e035640c0c071100004035000e113410501c0c0d03078460f041440c590f4251400d110000b040404180e070002c01d40710360050002d8840c3e081845840c1d5855511441d00b03191100e08218000103444c0b2800c2130b032070010081d41d1419800801952160386482c5d0031146c69035825a0200c00c011042c80626203010003062088c014240750300091400034100014503140000100c481001d2040e4910030807001400d0404031010000c25203405600d0312201c4080d500c0440380c03648018050400410901c070410001d074083c6108010 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 782643956 1250 782642706 782642711
    0x901090b0a0e07060c02063004150515030606210a060f050105190905040602090402120601020f0c0f060c12030903030613060b03040b1503070b070b0105010807210b130e01 75
    0x20b44290039a050441e05c1802900250240180245e04100e000313100c41468071404080220307008229910a0340c8021601252002890610314070031110504c20b0b107500100241c0400c4950401c000025601e0b8002480d0b10720502c2c4245581078103060040050607040e003154100c07008901c00b454800d01516600d40c8513555285090000100c915040540561510001025545081c280b45054001e4040100280c62140d000c008040031503e41c3e10091010040c54034800c002801c040c40020f05000c24034511020a43c0600780b0568642c1e00c0f802c1101d1126402c0361032555401c0b240c4141c504089441480d2955028084104400d085010006510541e02101c1e83c00018100b01211800c44845008411104a0520004000a16000380395400450001140c0a05140000020724007600794000780c2248101107408000c0014224030310307000d45000d0a29607000e191240008084c100c0b82400c14400144d0b07441c40c404841c0301ca82c0411001640988007908820200981401400d4030710407000d4190b1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 782645206 1250 782643956 782643959
    0x7020c060d0b1c0f080c011107060b01170c090f0409062309011103070c020a0509101a07080909041110050901020f1b041e020703080402090a0b0102060403080901090b0a0e07 76
    0x31110003185030f580350f00a01102190382c0d541ca400d00e29400c42040110250f40c1d402e14020b5843c0c0350f4002c0e0081d03030710400e0042030b403e102800040c44123000c07030148480300b00d0340418004401030300000e40741820016520703c5c14001007070000402408054038098205031a00b08594070301d0403e41c0c501c5013007041007613100100741c031420b104a00300da8406061100e03400080c070100b0b641610408040c1c00305030004020030345040c2c542001820f03000058174121031800090b0020081800c9401d0f84448250030748000606049544d102c2d46002d11440c0704282c40b134402e001c0041c082209a0465050742c0c04003a0002055012041018046ea40b2520806016118401924141003000581d40420103003611154080b40e80c18012700c00541a06c12090138122030400018410300c10324030242a8260113a0307681d440c10704150050040c5420082c2068200d1402c098580718103980001c2d10a811550510b010f110300d41d18144410f0050054060040c203440025091004002e840c2e00a04100300c2203c0c15100751a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 782646456 1250 782645206 782645239
    0x3020a0212061605030702060703090201021c091a04080a020d020d0b07030504031419080c22030c060f1d0409140606040c030e06010506070620070b060607031707020c060d0b 76
    0x41c00111b130b0110060384004000f8100714420307041742103118418011a6400024180d50519420b4490050000111310400400c03003070451014140002600021a07032034a810301c0c1c2010740703400c000b070400383c060b21065000f07004545481c040e041505800c007011205c00c0c245128024003418064600f07500240700200080c1c841504401140c840704c40c0801e010080c0141c1309001c1e81e0641300200000800314043c0001c8040c0200703400f8881091641c540c80d100c0041c103500e80341880f100c16400030820040322000d00440240c100108291403e44a15080c001d0014200007401524038030130000e040324a070788082c005801c4c0015085018010444041c0030f0120001c1c0110200c44c100840d1000950114004001c0b50429500038411580901d4000c00c0da044490600e18030785110181c9112103c40004040b020720210780d00301034001c1800c94440349040c400d034800515455000d81c003884103404840c00b00c1e5800b8001c110055480344090304990320764441d051300b54024003a404015000780e074200c5519050 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 782647706 1250 782646456 782646467
    0xc150203010510112113030b0f010e01030812040c17031b0613030e040b0a0b0a03060603021e09010306080d03021c050702120d24170607120903020a02120616 69
    0x200400003c100c0c00c3c0242e42000105840303140c49102c000d200b080001c06d07840700c224a5a000d10f00484401c2c4c0309050240c541f2001c0c0005a2010f540c0310004401070000403000c004139814410b140c090030b000d036111801d1007441d504c807a621071140c20300e4441c0b035040c45910200c050081c00d440751406420803045016080c0c5c841d8400c551001c03c41c12004408800603028401c081124003000c1c00014015841001180d00c81d8116001070410060214481591540c18080c040103060146002d600b0f01050310901081c51052028883c0b10303240c08a0000e003144d1096001e00014080403040b12948c188021019000354055a130318000d5405e40050740c00142c00e0fa0080c07901902c01a801820780043c6040b00220941106641e006450b0300c40d107e0100e1421a418041c80c0c003020300c1c1280114620304031001c1c2c03400d40d1902d0b10800540081c2c04203c029034210b4a24070000c000e05401003640713441c500d4200d040500c081d03c025844030002c03c07030982d80742001039980e10078001c85c0400000c0325100201a920b = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 782648956 1250 782647706 782647727
    0x109050a0f14060741130503030a030b10020f070b0a18090c02210301140d0f06050a0b01170a0e0f1605010215010b0409110f0a120513031d010c150203010510 69
    0xe00d542e17100f182142c82848100144402240a846a10140e45980c000b90540d0711004100000030340301c50b1017500a2402d250b46680c070885600013806401d0358a04050b8403003420380f0601601402c08142c6000c942d0151401000c042001d980b882c80a5444e44240da00400c180804500144502071020940004100c0c0d840075051211010360f040d81c0ca001c7c403e414034031440703c0c01604034000e03800d10340008030403924070342c011407040c440400c180c40d101c81032004480011140504002e00281c42c8003d0131004600c3e00d4000100050120f02c01c20000e20a170b16010745141070b04141d1081281e9200200c0d81c6082c0102030300c0f42613081d1344000c0d06160602840300001e000350200c03800c04210401080c80941c5c0500b50031082da40301d16003418003403000b02d10715800c000752400110768105001c3e025400715100d0164040c58085064442c5042c3c0d85000302002040130403c6001d0030300c8000030300c1c282c0c041e100c03001d92258043c00e000d1049140d120f01e13402035042031146d10b008808229802c400113008621808 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 782650206 1250 782648956 782649047
    0xd020d0516140c03030f101e1a040b030402010c02190f0806090c03190201030609090b090609031804050a060f0b0403050c090c0a0804020a031e02030705030109050a0f140607 76
    0x1429610317034281003600300c1c1001d01847c1c0c80c04521100011b1804000c0d242c040d500c1183c40380e110314249048040c003000e032003800410284407001c01042c440504407100380c81e08240c0a180c40500c02400e48042813600b000170f003121582001e041f600180200d4103d0401c41030b20021825140c5a840d2640003035036900d41c901d00103a050304003a401041c20011000b080039500e00501d40410103030341d1110010200e41b8001000e99040c0102d100304984103204100700c60700282e9013001549044070107044013141c040b280840901c240d03281c030301052681c4400e03008000070b00303c4680d49101c0580d0304c00d0b20306010ba106100071100c6000d011682c2046290410045100e80003007002d175480c00d2443c01044440101c001e10484c0c2c0b003544410040013240b500d007040310030003044017070389031244c8803900415140100a9110703038401c0e81005036410020310b020541200156002c10400b1600382c4901c1c3c00070b80d114000000c51014410201080309907903000c001c400106400c8241070364450010b0000e509c040c5c078581440c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 782651456 1250 782650206 782650213
    0xb12010c181217040915170f060703020f040905180d0305010303090501141306030e0f0a08071214070b0402041802150f0405040f06150804170d020d0516140c 69
    0x200810284070002c9000c40310404090b180588170f6076400c003250701c0400c800460070340d44401071040c18040042c0e4100b80c00e4400051082c82510302c02e41e40d0b40c2c84010009810150042841341044107a0010b59000e000e584070244031038036100c0e0040349840c4600d200800544202001b2100541c0a8442d4074180c0e509580c848203030314100401910500d80c048961442c1c0a001c101c202c090315151656400a0b2207540d4000c1076030040074610510f009540708000e5180d81241c01d2040015000f842101c81580d4069100144611121416102569000d0900541c1900001d8540421055581651007588200c0e01041005028101c10440c030f0b2680d0f00003500302c0b4011220b1403c03904071b078000d0030190800010091503d81c039180030805031107125900e0091342e40c44400c14004500c0c1070344182c07074690040c50080c046280949840c0c0c0e4400d40c9101c0c83d0070740f80c0c000641c2250742503035070121042908440001d00132800c0581010b400040c0d0700c0090300009901c40c00e00e030b008005d40d000b00d402d17450304607006 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 782652706 1250 782651456 782651489
    0x3070e0a140c090d0f0f12080108070522140f0a1503030804230f010515100f0806030c12030705060702030a0c20030105010f0e070507030c0b0a0b12010c18 68
    0x3401142811900c050b0f802c01e07098100071000030b0345036042c454014402c0c8000301e0021f0440b18080c1c8008810b07000154140c20518043c400c80c1c80703092034090050300414000b441910010340f44c100400700100d100c1603124108081000044503d08024005c0081c0001000101d02c00b6059449061301c1c1e02004000402d000f000c2400b14001c0040704820710030595240c0c0d46000b50806042c5040c6010048106c50f035150010402c5800002e020740d440d40c0d000740c07024045031565480041900d141c248844052000c0d0101040241d20108112840d02c1006413071000418807030122282c0c0c0e0713045120100d90340e10035200041c14541c8040107584015101d030b1600b51103942580e84081046d510191104801c0b544c0c0c51900c201680c0c00d014660007080701301c0d040000103060000395000b0340c40040c0b1100a200007013008800003940110b03010303c0d95402c190810400c2d00e4400e41d400145c00440700c12603004404d41c0041c0503407a01907115912848240d1101d01c3c003d001f482016681c9c103400e1240c00070710402d4010 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 782653956 1250 782652706 782652709
    0xc0f0e01050121020406020c0405010e010e0f090304270b03010605091308070b0f070206010e0f15031e07051804020303300a140117100c030b03070e0a140c09 69
    0x100c1c10f00c107600783c503468a8500c00441c040400ca801a41c80000180c4c00118401c84505280c0300d024050324003084584032640c10a18041d60000340581101f40b0f441d222070004103031141c18426034000c2c140c68034811a505200104d01d4080442c1d01e032219010300d2404481507503e2405110320030803102c01a100e00c01590340c940300315180751101c00e41660200b07820803440002520000f4510310503c50024601c070f442c10000d00092405405800c213036401c5c1501001e00c40b0400080174842d82c0441c82c081c410300e841d000381010a04108010701c0503548400407030440203008101040350403c0c0c540c15142c070100210000480c00e09078070250b41c080c1d05900200000246448010100c802c2400451071440b00c1031403d0407040030450b0300b1140c00020701e503550b5601c91000b19840d811401081040541b940c5000502801600d41d0301240084d04019a110324920a680c02030700204c0341e00350024156403226a03140c08403640c00790300b280c0506440349480d5001d200500428072044c012040c0d0f448460400003081c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 782655206 1250 782653956 782653967
    0x6060402090a03240c090b250f060e06070c020a090c02070314061e07020d0309050f010c02030c010c0f09152318090615030a09050115030c0f0e010501 66
    0x440d181c2c100007205000f1022410301150707080e076445018850403152582e03906213403c40b084c4445070010408010300811103039020506448001956100c80070f400c0c20b100e2640303804a40350240c02444c0c580a5801c0400340310340c40c2d00c10816203249c036059030041c6e90303900000c4035910303070140307000f5402504d2074010b0100c00c070240d00c01404c02c92240116607200f5140c1c0c0300c803003c2980240240e00c081e44000200081440303d02d921505030304440300d503280da504241c0e201075110b06101a500042550b00c070009000c0c00420010840300200b41d01c020420a22042e43c000d48a500161100f041c960a0003110413139580300b902c0c540026901da03507424030300c03d00308440001c4990681d5400b00810038600100110360301031480300e20070300045150780ba40d0b0740345a04031080741c88440f206081c8191100c0041084a4599203440c054410b240100c0950360360340c40709548001c09044501a02c03035840e060301907a820728052255010780e0301031840c01035901c1c2d40740d4400070034a81c3c5005280641088100400c00c650040 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 782656456 1250 782655206 782655217
    0x3901060915091104170f0d18140d060219110303070f0513050301021602010e0a03020901091d030d230106120207030c05160519121e05010c0207030b09010e06060402 72
    0x3d150515150340da88194032209040e0b882c014040c0c00401990300c070790314100000950181ca074105401041029a032050440b0700d140301e404c0b81186079940040c05662080b2031000644c0e0b104001310349071000c0d08031503940200035800301400306681c5542a220004008190791258074642c0e205040341054500840d042c3d00850881130910742400302c0413881359402e00182c21044008200c0f40714103403c43c00014039401d8002501e1380941014042400962070b0b500001d41036034444ca00200780d0040a0295031140002c1089043c928000850100a9600c2c5600000003c08624002d401c402c4031046d251041610700b84100300200328042c05020201c00a038029001040c001d04080031840b005403140341c01c10440034103003002c0c9180e42e00c00b07020750305c0c0c0a11084400c60481d000d02e03001c2401c081c3d007100459000031015190781b000184842d0f42e29005071842119991010080c0a020300700c00002e90750306001c1c00100c0e1107054500000e00c201105200d0b10030900d401c070b001020f06441d17500c18480254400c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 782657706 1250 782656456 782656481
    0xb010201090b0a2418060e091005070c0b15180c0a0c03120f050105120309030c04020d1b0c0501051608060906011e0504030215030f0c390106091509 65
    0x11a542c0c40c2ea41079044d040399001304401e40910008113507207800101124650341281d00e010b10201c01303000100100041d48060704490b80c000050340d807583e007001e071608c0c828003038004c0649150380200080b880c0c00300280210b0407019101103040b2503032a01c20010040045852100241c42405100700e806d1250b244a40d5090081c181000c1400d01d20103088150307800b480d142d11101e5126401009582006c580925000440710050b50401c0304000020f504c510f14070010904c05d68010890420300000d503131100650942c40d403040e070940c07200d0140c0980555042001941c0c1ca500e041d000030380c1070500300c0c3c07400030003500340e41d03980c4503a5900001c100070084044c0161f410483e00c00103010281c88550780000070303d041c1d92a8152103d00d51b10401c210f4540c484032003800c901d0107000340820402610781041d084a2440b2000341c0710707200e01810071a100003100d902c0d40d8035900c040c0103081c9605513468441924401038000d014481e110314000c8151800b03150550000e05078010204901c2d031050380f003d150100c070b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 782658956 1250 782657706 782657741
    0x403080f060f040c030207110a081f240305010b0f06070206031312021605030f150405030c060c0424080c09010219051c031512030210050403120b010201090b0a 70
    0x402c08082012242d88001580119500050050610156288038150140c0807103c164100d41401a41610b07203030401442038a80c440009141007001058020440300884411004001c0d090200c1040303805491303100c10341d1103500c0e01d4442c00083c14001005002c829002d4590b070b103400d500f03900f072001a910041038116044510301d03100f400904406070205804550f540201000302c1c803003d250014010320340c01144241d00c04101100c1007400840c0500b011900b0b190310740810754072030400398194801c0701e0801080e80220307030802604c0002440074205650052924044100038101104500c030305d400352080210350b1880001d6808486540101605e01042c4140c440c00500c072907481d00030310703181881100c158104192580c07413540440c442e110001d2003440c06000ca00c032928981090b2041b28052041d01400d920400400c0c14000c001100424202c42410045480c240c1001049486125148100c003070030541458982d41c41402091000c0f6000103104015841e0214000020a040900c000702030300c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 782660206 1250 782658956 782658979
    0x5100c020d050706020708030306181e091006090b090a1a040f05040b06030d09030f0c15110c010e1503091f02070c090612140304181a01080403080f06 66
    0x3141d41ca14601100d100c0c41c02071a41600b00320000e410489142c100c0c05a9034400d20420100e1f0b40c0d600c0801403824142d618080064a4009461001d80604582e1030161002c24050081c2d0b52400901145400c600369801c000302611503680405079200600c100340d0010300c1001186440d5482c7c0d01c0440c42e4240048801c0c00206c07154080340a0392911203007501c0c01c0c0c0c1d44100700300a010b81d40b0310480d80b001c000c0307001c0c2c0000c00070b02501a02d900c02c04d01001d000c124040d002c0c00c040020400003040640f9416010b802e40080e8080d0060034454003d8080856014900c010750742940100300038000b1840c02041503845c1030a083e2407041e01d03080142031050b148035603406000b0054081d0103006410340b440e10003603a1405541012501c050259001d4030029141c050b00700021140c0d682400e0805a00c20f81004080c0306050301580b541c040c0ea00641c0750b814261350765010001483c1e0103015440c1c003103510306522a442000564208008070f034040c021810140000311455401c001d03487e400b28009128000071b5 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 782661456 1250 782660206 782660209
    0x15060307080a150b010903081905070c030516080115090905010213120b090a08090603060d0c0803040603140c07261303050609010c3c05120703090c05100c02 69
    0x603808000030350383c1c92000c0d4091005031075180038200f000042800c1c85a5000d140d581c0b0074485200e13180720a90381603203c1c01d8400c2d84510640444008a4010381141c2d8980e4403402d189440d10049401c2c11050240c8650000740b00106014620135401c00110100b41c0701d18001c036581c0540002041141c01e55805c0200c2d0646841d04420103015150000760130388080421f141810a0100260000d01503a05c00ca03540400100c40a04503507055100f550302545036110b04001c90204520040000d0644014030808900e02400102a1003142c400d541c082c40b50002054070300492000a03079401001d0a420400c8402041c3c1039420703595510748002d1500c440c080c01e041e1035009030304030380301e41c001d03c0902c0c07903081007403000c100801a00302c1e003000000c112801960401400c044030724440c1d45142c3e64081041b5000303118620f100f640c082948040561240c20159008290b0307406a00e10500014908000c620a14802d1288203203050b0300540c3d03d0303d140c3c03e1400301302013050a05084020080740f4101c00005 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 782662706 1250 782661456 782661463
    0x10210507030605091207050319051605030c0c1801031106040b0d0501060e030d0804020405090a1a0f07111207061b02070503060c0a0e090601110d022109031506030708 73
    0x4500900000800d41003100e0001c5c1040000140d442182009210707500100382c021040319486400140d80b0140490300800954181c02040d583c0c0085400c540e004605120b0040010210320f112801920038481c00c1000308500c0c80c50101c1d0b00c0440c5020a001400024941c41031020320840062038103041070b95801c88034403541d1182400a80c07468480300100002508000080c1b0f482d1421006008007400584000348108401000688100e44074004a01c1c0007009010f9a5000c9030484c21000e1102418404110200c00541e0010b014101a40001d45424171400c04500303414401c00107403130341c2100c640020002d40c00c881800d545195540c2c80008648142c4044400400e5141d000f4021075442d050030181801001010b00e100e044040004443c01580800c100b03454a4080398007443d00d0b21030500403503011603560a1000984034052595410540000d051030103c000900700352131400c10440001d4240c0a550004c64060b80b100d9140c5e400b0b01c181d011125131040024044598890f40c86c4100342c40d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 782663956 1250 782662706 782662709
    0x51e0118030e0901050409120e0f04020708071505060904062301141003050606250515040c06020c010e0103020d1b0c030207050909070b0a050d020706020408060f10210507 75
    0x2c0342908038402d885043c0026010300506003290100a01002038845d0382070086a10650420400180d00700841c41da43c0c920321098002c0045c10440d2a008a85000b104a0f88421070551b2990102d140c1c0b001e240b1040d0040c02d204242c094441c10300c644455035610090044e450309040000c01039140344184810f07c0301118000c0c1840039880c40781150721814442c440104c0036041003058188070130890b5a0322194126480352003112071011150065401c0d080b80d82c1140d0f040107116000703e00ba985081000c420440c3c0c0240e0160352030103444c9541d480f003641e4412100c01c00d10301141010700403404c298001d6010b080e8410b03044402060420303058034107011040c2c0c181c0c648004124611490b0041c164100701d004081e102c1a02c1c144190b09041c0503442c0e441c0d2480c451a03040c03010005a00c0500d40c410710640700303038a40030b00d415512040079180541c003a40007405140100c1c0726010004e1160458042d20501490090741541031841c10400326444240e19248200c4001862849200029008010490 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 782665206 1250 782663956 782663963
    0x16110607030509011706010e0f03070b0f03070f020c0f0409020f0d03110f1f0c0203130807030b060d11040b01051b250b030c0a0c120f0806010c051e0118 67
    0x10f030743e03e28820015100c038120920a6004081e1301013044216600071981014448044a44040498910340000c3c0707800d2440c2c004c81c00103407021034500c100c0b0860ac0095030155a4944034a956950521422030f40ca03501540c1095202034203081080d4503003030a42c00506014006440b609030a10104003081c0c09000c5441c1c2200003030050010f0b0b4902ca48140b01c00c200d280e24503809803419201c5180f28000300a540c1002501c60741e40d42114404043c0200212014000c0324060109142d0340c42150350b0b16488988016070b03442080e03d0020300d440c40c260305081d24240c4d01c0200c21165481e20410300000b00f0740c44401606201040007c3c0c1445055640710721516044e007001011846070302802d00703480030403d2450f0f0807245840081800a010703800c050f2680031001ca0b003881d803580341e059030458200c0c4d2442e10242c4808040f141d0361001075444031440900c2e031200e49480c0b043c4e0700c0345001107641e82102203028010f500300710b40884600c0b55a0485845289440c40081401e01c0c0c5542c0e098402d6141d14400c5 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 782666456 1250 782665206 782665217
    0xc0f07031814060f2d0301180203010b03040615120c030224030406090f0b160806030d121503140330010e28020c100c02031611060703 59
    0x2031004072654006030020305151001c00760b003080c0b16800715a10380501030350120341c1c600200f10a2821510008014524403001030304030398540751810100e0007035000707000b8050032280402d0b168500c0c1040307000f124100d49169212500e56076881d203810004003202c240c050f640c040f8801000600e4006442c4001c08103008804110140e403031481000403501009001400041c2c66621200600d40a0340a0300c0d4825040280490551f6141c03404000301140c5a50040c030104c404014002e00a03181c000c00c15a800c5580c07a5031526803100740c10036a82d908100d2107070000414210f10113240c001c40c1c0e044500807040310f0b240703244465180c0e40d850425048103458005c0d25840480c014952032035120305441240303950024104814a21400300d641d4400c1406103552140e07100d400314203c1907062115200301d04a0384544290b100c1400030390b1000c4c1d400002400a103108220280d034910116100340c41220119400461400500111007907000307504801c00d4494111043d1000c41a8980c0c03401450726500c20341e01c6 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 782667706 1250 782666456 782666477
    0x3110f0628050402030c010804050a0b0c03060f151c0e060108012f070b041e150b2d060d060b030a050112051b0f040f0605010f050304110402030c0f0703 67
    0x520890a001c0c110010751103040c1800e1001503200819815030720300003840c013404075a42d9418111f280203840c80c0001d06800ca070600308010f8100c03090140d40140000c844102c1d168034120b04000c0c9009180040203060301041255142c9a52641d80701054002580f801040c5d2401008440382010000d900030b21890351110750a901d03558120b4a000303810400c50a1000702c5031176001c0101b0160003181c00082c50140c11b84045810322101503908552007900700c0d107031040c3e40150718081240c0e00e45034120f03004950512810b80804d2400c2d5500d032218907441c0007054405148540302d500280e651608664101004114075042c01c02c0b07e004040181030201c441c155039040c50807c40e8200d8030164414140350f03000102410000d1008500185240c0840d000f4040c3d801954001440c170746544411540d11925107180c1c0301041d88644c000100b221000d0700daa420120304d0b41c0e802c0d06c1520085400804a8032680050070f1580380a50295810051b40c07006141805480907181142d035200d0b10b4140c0200701100403 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 782668956 1250 782667706 782667751
    0xf04020301050c13060c08400503150a060b07050303100b0c1504060f180507050402070812040804030f0311070b0c0a0b0a0f0510061e0c03110f06 64
    0x2c0607001040300c030f505442d0030b03e80c051144c520080d5000d0f920070040c3c80520401403042c603a0503220f50302e2103440c05228012969502c080300c0044d001003c1003070b003000c403041030f08281120b4100b012030390b019000d4491204828411007c400d0000c05c0d403610700e9590000803d05030740c044043c11009100f000156034a040c40284107200c013a06510001018030100f160040416010450b40341851925502d0081d035200c51609a016003156a81501094034103082c02910961450703120300715034041c009603007071940c490080c44103900c15180e02401070b520030400521036010003a07003664010b0151003000e040544a644800034210400c0017034001401d0443d05107071080092101e18020828000160310f171803481924241c0346c0c0b0080390060a03030405200010400001034012180030070b040d45040203107140212407000900f00303600401c00042e606d040814410040390140071a1032405071a0071071400001d907422030740d540c1c4504510340c5038000d02c1140481501c1c00c000890140306e107500ea8491459a440 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 782670206 1250 782668956 782668961
    0x10903022a010909020c010b0301110405090f01290403050d1d10020615010e031c02100905070905040f1208060310060e15010903080a030519200a170f04020301 70
    0x1d81e10301004a40c0e02061002d030381064841c1c04131042c84501607180c0d2451a400d6004240e208003094055080568603005058020300903c19500100c50400c41030722800044202d2400902860748640391040c80e00c43c82850041c521803101082e0081c89140c10303103907982c090502e811641500080717540900c0701014000c9000203854081c0081da500400400705120003903456a001d010171000741c0104003c1103059114410800d0f994102070100d80e085000007041004100c140d072240301c0113014081c0f00c108108094041d440d105900000140002c1e400c1500302c0c001400c0c041e00448800144040d0b21000420092103001c4200050300c4819040c0b81103820315007002104400090301c03e203403550a0100d00300501c1404c1e003180c0700f80c078210081d800d0040141d03a5a041a040500107a00215100d505160b068000c24440d0703032140450344568525100020543d107801001049499061008042c020504000b80450706824901202c6070104001c060100d04402e55811100040c0c200c01c200a605090 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 782671456 1250 782670206 782670253
    0x3120302031b0a020f070f0e091b010f0c0f050f010c2d020a0f0c050a0506090d03030b0619020708010e06101503020d051602070602070f0608090f01090302 68
    0x1410194a185056110301e0803003090401c28561420003c03d03150b005610070041010512402c4080b00d208944403401380c10481c490303110b03400e01c0003071140000d0300121001c101c0680040e1140302014503000c500006440e4118070900103400c0200800075500841d0070178001ca410140618050002e510341c50564500707646400310301d141032000322959040111114906000c01010251103d0a8001e0b11303c006c13428405032600142000c42080902414007250312105d20483c0c00c119000d40d10b03141e41d03105000c4203008410903241d0062000881c40f02007406074202c444041c0c2c00400f4280350a145110828407444c01c1c0304540c00580c818038090000250034031814040c4110040203010514211512001c282c4190158070340002c820180c5049003402078060b00c80c101e00b82a024841481c1c41d50102441d00e5900300810014404e01170f00040440c00030030018187e035122110602d0440c140201566a0036014000194030702c5014510010304e107080c800c0c50302e914420340c044c000040b1114070b03042e0780007842c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 782672706 1250 782671456 782671493
    0x507050901022811040603021503150a050a140f10021f11250203150405060a0618020702061b0a0c0803030121060b04060b04050112050c0304080705030c03040b0403 72
    0x40850349030003801d0341440c4415141c1c0c4800d1004d428000940401c024115983c4001e40000300601c4201103030041001071071107100d103a05c508071202000c00c10441c0c10031440c45210b400c1560800d041c440421400f02002ca2a203000e8512409130b40c40c031012420507040c0035104001a040f00503da004010302c1c110a020031140400c0610500300c42507800e0103140f01c0d90300b07503d241c40c500a140303c1c0f480c1ca0001c420407120b6001020364610000d074501d0101000b00449088590f405100b000404600d43e5100d90025a04041d4010301c1c01c00c0c040c43c8920081d0300444060340c1c4003809001d00043d8110081001003c01008000b8100b10f08a40c90090440d041e50b0308115929041480144445001210403a00460040401200242c0310b8201000202184d0102c50b4101d4180240480c20201c0380b0001c004551080e81ca8400e4b5100e4603422104490056071880d4a524040011030040340400303010b8204640183d0503170745030940f982c050610790752045e4030002d08100003003410014015144c0744281c11680 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 782673956 1250 782672706 782672743
    0xe1003180b1005150405040e10020f0301030303050c1c0e030f07060606081e0f04080c0d0816020a0f1103071d190504020108060409081b01090b0601110303010312050d050705090102 79
    0xf130061200440c0d0046000e0203020b259900400401442d041014400c00307030003103500319600e0000704c060510a82c8240000d80201c0d0520340403e1044410608842a645040d440101d2844003a4120000f900300340c1d0101c1c1071391106200c410a800404801045541c2c82050000b948524184000d000c0200051001000402088150928411641020754099940b1001c007849541e1458003590300d0283c2c0c40140154031542c0181001250002c0c0d04a00a400001c00d6500c0500418004c80c0c1d16801442e0050003406d0403035101000441c220b0881814800050555040907220b03580c402c4008121a0700022a012a800b030102102014811100002100009002c2e51400c0c0d00064088500a0300700d0380295520381c003031418407140c0c1d01602c90b10004003580c20203010000000502034854004140d41245950b40803c0c00c070740c00340842c2d05d140c40060b03001d942160310b552148100c2161039140103050040c1008040914100d51040728860400d0b611050340b2241c08000092601c1d4400326442517402 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 782675206 1250 782673956 782673979
    0x51905040b01020c1e13020403050604150e2a04050702070e07020307030905120708060a0f0e0109050d0f020a17040603051f15090f060306051509010e1003180b1005 72
    0x3100ca0002d108070504078005d10701d2104448001c2440010905485c40e400c07840401c0120030001c0214009026074002c075034842d1568106103240003214280ea04000503070341701d101d0803180000703c0700b05103410b12101000c4071106101d00c03003c28146c0d80f041382c040c001a0444841131110b904000d43c070702d8001d1058801035040c51b01580c0c0c094001c280f6070003800c0c440c8140d28500c15180108202d070602130980d00d0103035030701400c040e98000b001e4080c4200701d1820900740320036241d003102c051040301c513400d410500030030091044203015240620303407856a104500444580d940481c0d011049200d180b541d0211469981d8500382c001070458002818015003040c440e12410140c14084030b110043d42d000302c45445000c1d24001098480001c41c5d80901da51a800c0c0a0000b501d5416910000403146c042e200c521079070603581c450660610074824031502045030500d02400d682401c010100201c01603013400030f6002c103103a1110f96807a4800c1400c60f440c0c0c8d5540c0800c01c1b1a44070080003801018280c40344440e18 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 782676456 1250 782675206 782675209
    0x28050112090305090f060c0f1c0c020f01030b120613020f0103090b010618080708010605030120160f080309010c091d0402090406061e14010914120304051905040b01020c 74
    0x5104202442d8410304040d189a221071b9640811510006c0c8010b044419810b03490081c42e803104008440c001a00d6040141c190065000d80d0390f414989a004200e5118500c0310001980105601c02d441900480c0e1a89d1a64140d03000300902c40c05800c001028420402040c23042048c0303201107146c0281050700380303080207001845200c540d50545600d401c0c2018800340340810005003c2d25684541003902c9440000160114103510840981320242c00130300c54084040712071400a8141000280c441d001003010105019218203c1000c89204507480c134840c0c0d045890302c880c40e400985802403240d55860fa000d04003078000759544002c0c890341c03061a08840400090504bc801d00400181c01034104c24000790070029150301440141000f840d408a619480e2051880304010070b029011044a6003480c0d541c0941c011500c3d50119010200c110aa0554a1003485007400380034090b541c00740302c14040450703107a48038410310101510045030301c60400e144c00200410789140d00011810343d0414814503105 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 782677706 1250 782676456 782676467
    0x30709020702060313110a0e0f090303091b1c08090405010f060c0b18120a170c04090b03160b130b030c19110a0c090f0e0705040b280501120903 63
    0x18010107041c5c450009107061185030200c1a00a1641c407251340e01000c01d80c0e07000381800b6030080d42d02003001c6806550725000136550340b009032850354490317108204101c50440c2003e2105501e2f44080c1040002c840d4061031b05680568241080b02c803508089083c100d42e00709441070500400f11011119580c0c0e10300f40028101c00000f07031000c0e045126010014100020302d404030005110082c00301c680000c080c0a549140d030304062600000104180507820308043c0340e030740039405aa90307a007030b8030710b40703464051180e00401d12452583d405008141c142c4000025042c2840018540e808115645544444805018465940208800d4801070003446201e8009109031140505012100c041240300010159a10364100c500010f45226581c0d02d04108000c40d0b130b089044540c5404140115039210104200f91203106040c030089505c144000c0105280640140c0100302c0040c0140200140c10030200011440c0c51140c0c001c007007101c110400495a003e10258052940040100503042055500500 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 782678956 1250 782677706 782677711
    0xe16140a0f230702091003050d1b061b030b0108010b07020103021e040b07060e1c03050a021c09030f0527011407050106050301060f05061207050c07140307090207020603 74
    0x20020a64124141240119045108240c203001c000c8590b00707141c003071a205580040c4080b40240c003a240440c03014590110b01c44207507548007025290703840c03801004581c1034104070711210703c1410f4806400e021802c5882940c1c0c10404040000c400301e200d10708044d0940304680446810051840f004208100700d840558088550901c0c01580d00c40e45114401414550211845401c26002600003000070320344000f0300000e8404c07032040c4a810101c1a22a03154001560782001d006800c2502001c5144250301542e842072900700f005090150245450040d0540c0c0c240708612140d59880c010f041c1500405e40031115503040c50309a103411480544450700d0460201e000d640b0b102510409159603008101641c0000d00b2402466251000c41c100280030f000c00388212400707540f9018000c0b13824144080408140e580143c092031a016200400440c4914001c041e202000300c24130203801c44030028001c620080004810440104040004143c200512076203c80a0030344100a106c00580320f2809503607 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 782680206 1250 782678956 782678977
    0x1121090f031e0702030102040f090203190209240c0d271211032811090603030a05030a060503070303080f15100c060605041b020f0625090902040e1614 66
    0x3a01c58243c0e00c0400d0190081d904102400b14100303502180301c181980c05184900305a030900c0220b0200404820300304d1092020781d0703400445588030400021b000740b10507802ea03010b51580c10703d8244054070071030901107860f50704800280841400c514840b01d14116070702c9228003c020207540c174078114141c41ca24091401c01407105000b244501d0450364280310040c956035810300e05820a00c00350042c07944070b10414204070f03050040205010018106640b10300d110700d001030700541c81d02042c00010769203a040104400c1d0312646070307000804e803510240a0740000750b01c40d4403030300d0b6281040f01c07070300309209002170a52841e01e41d29070f222009550b80402c42180c0b1403540c20b211014031294142003000e04480c0d00301d19042410301501c0d41c3d1705081300000c51200c500503401d82d400e851089a1305503c40d0800c1e10340710001c0041140d20300b5009581d01c98100b03640250704008128959540403074051b81c1040d40305040134081c0c2d100b00301284e0408400c0130072001a0349050355281400e40081c00c02c40c00b8001005 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 782681456 1250 782680206 782680267
    0x4090f14040311010608150402010f03090201141606140403021b0607020607031101050103142428090302030a2703060b030307080f0d180b0a1121090f03 67
    0xc4011829130000018085007419121f00004800c00c01380c0054040c2ca0480c0007030b04c030180c8004118071034450840c181c4d07070583d00c1d1500312402c8010704000f5080301c0303500f5840041149075000051214490122450010380240020b458141000380c2400c1c0e8039142d14003031070b102c1c2407402c01039543c03101111680e55040360000d403143c002c0d040c06c4800500c001031041c0503601e8200040180204100302c0780100300700d40c0444405400b030f4800702c0152a100e00c1c0b9929001c83d80c50100303501081c4a001202c100d124045002501c410100700413007035444008080d005a000001c451022680c080c406800002c180e10581143c80e014034004030292255100c06001e00f41d079010304c0f0711190340c1803045880264205403400e03151921041100751b580e00114044009525181702541d8018402c00d48042e0250005c0300320b8071559525007000302901d4440080c030310590040000c00613803070070198404c20700000a0b8134001c0074030b804443c880c43d01c60101303082007141d4014091002c0da40a070304c0302140e840f0b564081c80c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 782682706 1250 782681456 782681477
    0x13080322170319122c070e13060924050c03010303020c092701290d061a0405091011030c071403040305060c0d050709050d1e02100504090f140403 64
    0x1100c00e1a902c007861202e0608150640e05c41c01007048102030361020105245158144131280c60380d03219140e1245d0180c0b2941000014807511450008000c114050140891541a01d507196821400e0b06201c1120040e641c165901928041c1e105250380900c03041c540f80d11b10350468038040e5407542a828007a108411a1000410b41d0400346404a403031451051290304a40c021050701d03019203841c100401d003035140c800c0c607100d295142081000d040300024001e481c4030242ca4841c6800b80115100c1a070841218905006564031244600752255181401400c0e0401d20000c103d0140d9450b44680310710040144184000c800031641200c0c1110b81c0910904c0746008550720b0241140110390000e4078900a01040000d0f458020700100401c400c24001044180d0340c2d180c068500d80d071355014141e00300c8142040d600028200054242c4451281c00fa038000380e8480340d00240106101d0030030380000960105040286034098042c4829840f280c0405000048120b1f11000c80e80710010b001600b0000036440c4d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 782683956 1250 782682706 782682757
    0x1030209090a0501110909061009060c17070807020429042a0801171603080309010b1201020d0b0109031205210403020606090f04030212130803221703 66
    0xa01040250f02c80020310602040d0400100c90760031880059014183c0840014440d2904041038070301102e40b40c440c01c10751803c10004444409030403108031030a0500303030b606000305840100035041c1913100d034981c20f6440c2e10380c1c4103101c282c401301e40c007500b8646400d5400e500411000c98415004850580700041c00e80009181f07081c000000c40440300139800f4050009812a5005443d03c0c141c603216881d031540009005085a84d4041d04e8440c1602e4078400b034014000100620300941c0c02100e184004190002c41c20001003070031010051504c113681d400143e03181700314014000c0e5030407440d090801c40e090034510789800003008170001c0319008104000809100524864001043c1101a0380d5040120308d040d1602a590340740c20b80d100b52051a0f02c000140780950540b800c3c03480b5a600d0f902500303180700214403140f069080b96042100c2c200c55440701007400841003019185446000050395026107041d40c08000c4211180c10480010000c0303110308000c03110020031142c403c803510303a60f04c180964082 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 782685206 1250 782683956 782683963
    0x2b1a090616120908040524071b05090f1605070c090b04111b1506012003162001181401030209090c0d05090303060d030c020402070c08070602070602060f0103020909 72
    0x2000341542e4640251107040c81011300c0a0030070307a0001e45031002d00c041c11046816110217081d00e03040070030100b0440c4100145031191401d81d602d202001316141181c4820001c0e0310a14103d40e90020545a0810007a40d84203179131202050f0f42071810228607180311500c40c02c0d40e02410b802035140c20b5480f01400034958130381d030307000d080c0c2486010105526411462101c003000250700343d48050903c10146039400322030011014501440058646602c40903c000707500100c40d001d40942107107408284014003601288256440c3d882d48100610300a260100340c2401c2c008a1408949040215020344a0760000980086105840d02c2e00401d0360070440c12401240030b403040d40704890300034519078148001c204040016050619030504244041d6980d440f030255240000c0340c00301e50100c00360524101090007110042c644034000f420262a0032000e4031031100b144656030040900f82d02030f02040144507814400714001e05044e2029098074240032103980b00c55601030002038418080344020525482040 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 782686456 1250 782685206 782685227
    0x118050406120c060906050702102a0203070b0a050a110c04090c03110108150409030c0c1e0f060210020c0c15130506030603070608062b1a090616 64
    0x1041031054075101c1c0c03118942c48420940403074000491602c0882e4030340c02582c800054800d50342d5241e0600e400e81d020004000090368110042c4040002c0c0784005e0074154182e01c07085284800c00b807040002e54030616142c007051f80e200101c903500a10290102c40d82c4072007207071241d40c941d1800070032161781c510055041800c5155515480740c9032640314000c00016155040840307000d05840d0695011000055130600d508803000700c0e44e040310380000b9415190a07401052a18020302d0410302c080b9081e07995104045013a0410040000366902039510034221100030070280c110079109038401d51418002035070b00e841c0a001400483d40100e000303801948100400344440d070006001d24510000440700c101107610a007014084003c44880219050900404580c003400f4060010f00806103004011503c0d24809060030b0381c0564020840c0c84040c26403076954407050103c103103100c0090440d1500c44440303a001c12056002d1003101d000c001e4241c001245103035000281d121103040c8a002002c0441e01076850 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 782687706 1250 782686456 782686459
    0x4020712030e2a01030b28060306050910030305030907050a0f170f0307170d140703050123060d1508030306010215070e0f120d0309060f020423060d02030411040c031a011805 76
    0x14605107070f01c407910091087d04980260310104a669268001d001045508460b41a2806945081040081d10a01c02580d101c1c8511040d9002d0580303a100140702001a41e01a03610705052071070500105410601400c3e1000200b0000d11201c000000310a441e030080d010041e00c0031400e426800b111022001c01c4507440081d600c0c04002d40800d03090008440d5000b0303510140001e19003000458007410344c410700c02a00e0a02580403050441c1d6108020240d400742c05070702c1419071251001205030780f41062384805466110702950f220300e04040024507014007150008003c00504091002c805c2e042a40c0e401d1700002652220040721401c00420300303141c584610402c0c144110305000030001c1c0d0540c070040401d84110f0040c4280713a0403815101c00c0c0e000383e0117484502c883c0080d0749a030321302d60240c211440c103801030201030902d24000d13822000c80e042100d0580e4046141c2180c6966481e20b80714513044030300b90341010002c1c20050300503541c050741e070701c0d801c2c50501140740b05201010640e040310200030f000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 782688956 1250 782687706 782687749
    0x6010f12030912030c0506072c0d0203010e030c010f020918090c060d0e0708010c0e06030a0605090703020a12061505130504060f030201111f0b04020712030e2a01030b 73
    0xe0f98500103000300c6615070f0603640d42c0a038202168003a44511003034254101d04e910400e12a46905610030401180c411015034080801142540140c5003802208690700d60301c40038588924120300d040c0d09552502c7e4000300d00d12320401c075400380e45c0c2d034440b00c240210b1306030011705480740c0d540e40400c0d240001d44005154401404111400c05180c91303000f001203900c104050701c2c030180d556182103082e070f101184400c002c600917007150340c11030501c04c014503801500c411001c00d0040d61000483d01a10003900c2c8071000907000688592440d0300078070700c100686280801040143d150140e4661240a040e04260810000259a401000000130b550307025007401030003000003950380c910340300e0b80d02c44503c4220f000c505890f400c55000d25000c0344034130107546040307410350f031617590000d44800801c030005415601590900201020820034445401001025200014000341c90080503103132285010049048541000c004600c2c003010360744548801c0028200418240814400524031101c03031040d10a0000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 782690206 1250 782688956 782688989
    0x13060b0301060f0203120f0403091211100e010903121412061002071415041d010614090f06030907080a06050a0b010f05161b12060e06010f120309 64
    0x201009604075011a150b05882c1c4503001401d9032217024801c914914855903400181d80e1051904001d58000e2107031604c00d24043d2128201400c0800c030000a484800001202400a0811841711162600a8145115507002101c0024488034190200501e000604a1080710507405030f103145151250421000307480300070000115404000c112030103442140d002c007056643e180081a100c0a032010051410341e07601c2810309005254060009503151034008010000e860300314661110310005000504007582e52502e000204814003142d00304c441135070100140302c0b0564034103100d0124000107a8a035074503551034a540d01c1c103200340780e0321558050044102c0c20041003455400380344121142a001c001d1240b0800044815540100b28400070038010090b202c0e421554146954007030340b10704031500e03040e0204254116001101d0b807040140300c004d451050200081802000041030910703009041c00d600d05608880d54070400e202e04030500000d0511001458414604140504184c120408000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 782691456 1250 782690206 782690219
    0x42307060507110603010b0d020304080712170a2c03070f05071a03010e060607020f190f1a041a070614011805010b030a020901110d0201020403050d0504031505061306 73
    0x3030780856070403107180f2038000701800d5601e031641c26641600c00003000d49041581b8012810000d5001030b0094410f8a824407803200000d10001441000201958034100c072030301c021131403004903000540860085400c1003032481d5802101c105054008503850140c52842c6010501181148134a1070083d155198000c0d00078107105001820f0012100007050035401101d40c48416090b5000c20300403c031381c0031507003804286545080c00252140500003064000316101040025860342081026203c10310360600040000350f64512202000b4140745911001b00c0c0c020f42030b00e41320351080c0e00900d060120803046001c0c0c056a088281e072b850940c040c4042004003d1302c014165094000d00c922034800c0c18130395211080200d140038441c1240c04521146046840d24882c02c03001e500400c0030541081003402800480310344c100060804030b00c60f40c000503907075425030925a0804a01c0443c41e001c4c00401c000c1000040c030221035981031004010000079050700c40000043c541900304440c26000c80c207258020030340 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 782692706 1250 782691456 782691467
    0x41511010b0f040923010c0f02030405030606040c0e041a13020c060c07031101060602030702040e0c010f1101091e1103060405030f030a0e0d030f05070f0507060c0509060f0901170402030604230706 86
    0x1686688c503402000005014120f9681c4100d005a6405030041c5011881c182010b4000b4102032840e400c18048000c81d040206d01200c002100036004244060313103000d02c9040000c0a05001442100c00b5460200550400b90342c034980a020089008800070703000040c5407055020300c0d40090614003d00625940d400000e40d20b800909050f4452880c0400002c81381d80001101100181c043c0c4481044401216007500c081440018100c260354a41c41c081c000981400a5400d00300c0500d81061802040c1d070415030204015015860301030381c001c03c00e1002041d40013082e600b030340e40e4480c1c040390307243da4007800b080c00707803070b504041c0b011500ca800c9d1406491601900031a40103603624070200316540d036181c8100d4031629800d100501040c42042400e010501907001001c0742200d03804c1840c500f000200105040c1e9000c0d5041030551000482c82c4040d80d03070300828840c100740c035a00e00781d20b6508054002949580e00a4801001090349030346503000f42c00b0f504000b0744600300010655601b6a61400f02070f09 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 782693956 1250 782692706 782692721
    0x90a080d05010f05091e19111c02030903040b070c030204230c04060912020a03081204110607021807020a02090106020f060604020a05072006041511010b0f04092301 72
    0x2501003c0800105103800c246800c540704811880181c138a412608070b4203501131101800048100106514455001001e801100254070422041c03a503604102c054002010382c42d010b02683c42401007040c443d80a0000094905442d42d0300802943c424252606c405000169400250464201441c0c41500c0202400c460454603a440201d901e0341d030364824038000c5109501510b00440d444207020b0250700c1101c101003513805d02c00b60422584d01d44940310305099800c031400d226100c600320000c210411103944030506801000703507461400d281180e4001002da1503000708401421b1000e00004030600d208100746426140c01030b040b1034095866441c000d449841c00b0811030807078800c140111790907003024421948000400d640c4d607420300c52260b8800060580c12038038046140000d03003c107004da41d03401d00248020300c00c1c01d65403091902c21010240085220721040e010903413424078800c0c0715869500403542024400c0398001001c1c551898034071410904541c02d2240e1000206600019010560081c403 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 782695206 1250 782693956 782693969
    0x6220b0903012f0a02011d03071707030819021b0102030907081609050c0d0c030b1c0201090e09010915020403060509120a03020a0318030309030e0a0509040b090a080d0501 75
    0x3c00d0612000c0d014032000102c2e0b400700c01d070400031103200d02120030710405030900194910011480341181800001e810300c0100e00300c80607400000301b002c00c009180700040400c007141407031181861800c1c1c4019202c1c0780002d01c2940c032035085006240b00f60b900355044034807041c00700da0220031948001800070700030f4000b100c20f1011842840404103003d0000104030304285190312500c0f441c1810400740c640507003c0507000f00030303189045c00b014810003017038050340c40856099980000c40b00121030400424607194110111501407500111002d40d0340103142606847e8050400d40064550000703031801080300800281c03040b1071103001d000005e040b42c2c005004590007514188017603210454125150100a00881c200302400c02402d0005170198001d048031030554140052480030a2400480b0b403107034101c046000980c0d0f403002400b0150005d2134480c00c90002da405144250134580480d82c08a0094809442a0707405000034074584402c0000f80b84066004003150b80b40c030280c1601c0e001810003801000d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 782696456 1250 782695206 782695211
    0xa0501050709081f020a020c12030307020706081512030d02070b011701020f030f0a180501140a02030105100c0203030f070c0911070f1b050a0f090b030106050f06220b090301 76
    0x1840b0500045200c413450381e000320071024180c4946000c00035800344590b4019405200d08040301940c401c0e035606140d0119030041c698070712304030000900f0583d868200d4010b0041d2a81400301c10005240c100303148950568281030504401000d642c03a600480304102d1000d0300000790321003040002d015040c100d9403010800f00c0000b00400c0c0b150b01340d008204d01c84c02c0d50741092001400d410b5007400350320b0300f100304240005981c1e21a20041c03841c0451000f01680c081c1c1d140c105260ba417084450550b0f500c113034049011401c550601001500380414806e01100708401c4d41d82c03040955070240304440e1460a071208107907903613600749040001c000310b034410120304c4c2d0310700380040d44608030340412a0302081c1d0044071082143c030255103469150303551241300c5254143d5850003060a484100c4110003a0100456109141c1c3c0392806500c16210540c00080c000e07410300e501040b035512283ca10068628003100c1c580e494190f00c140701502c45080341c01905504810900c0007075805080002004a1407058009 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 782697706 1250 782696456 782696459
    0x6090d38040b0c032d06090a0b01081303090803030403180b07020d0807031704050c0a05030f0604080915072402070b010902030a02070203061f0e090d030c0c02030a0501050709 77
    0x126004400d08580150001c5040c00001c0e528101d00d60007142c1c05203c0003140194811206080071800710451000003414404070103029046c40c2c003540d050792100000c14240410104000000c0100300050864410f404018810b042014000e40c80382000e002a60200c03512464541030040c0800f00c00420230044440e001d1020413100e4890044a030030940141c641c03003842c84140c1d50343d88182e010520542c104520400010b0348403600e80442e600482c003490050010311160310400c00b0950042d032045209900031308034035549a4000c1042544542c01210040d1502c00300c00110768806107004071a05071000001d058400c0100c4460301c900000300080222002e003c03041542d1080b0321400d03002601c0042540010008110a43c0046034050709641e00541040398079404246010000c0c0c407034403040c4007501e854281d00703c2d481403a0740080101c44604800c0c2e0030040052170700d0710444a0f9441c1055142c1e0640074045d030081030364100099001d4200c90454209050560003001d0075284000040d664490 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 782698956 1250 782697706 782697803
    0x909160807021b0f0127050f0a18180c03030f080f060616020420070524070c0809130203180c030d030209040b04050702100b0a0e0606090d 61
    0x10403260039035400c2d643c0d00030344010b1020010010300c6100b5136410441c94000241c1110760550150022040b42411005400c0c1058108404040c0c2c000b42103001b4401c505040180048030b680c038080800030201c00081301000d01806214010200d0f901802c0e17081025000000c240c0e1003081c0e0070003180b044e1380320350307090b100c41003000d03802c1000b40c0c1c0060b40710200b4807003c890308001d00c6000c1c086620007800000c10401901c50350011440c0341d01c1000c2e03100d0002c50340702d003402030034000803a4410121002a112043e60006569040c1024200300200301e01010f078003003004000400c40e1800c40c0024520342d40420356845440c0a540119045c03145003e11500c282d4a80c030300024080c00882004003d0700a007682c1d10b208400a400c203912280c5c0c0a5251010316816441d648201382c025200f07680605032040e80100100143c0c1e0b805e22883c0e014000c0d0541c00c101da07131543c0690907007040c0121039890b44c0701c002c0130018102c40070000340540113071000300079140c8584c281c03100c14104896400494506084400 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 782700206 1250 782698956 782698963
    0x81b0d0503040303020c071a090901090603170f071b081c020706030b13020a020601030b0c09090105013b010f02340b0406031a090402100f05090916080702 68
    0x1014001003941480818000307030113500503000611100041798034869a4907604140a0f072903d0002d507040740001005171460034103090440c0586010710342400000e195030782d00680185440483d4200e00c4000c212183c90916140444124075045540a10b140f043c168075444604c2c4684115885481400d40040c803044100d1400000c82c0320940103458014038040054018040d40d1078450750110000030031640c94456171000c3d0812840c2076000304155070551400701007900001d0040500c062007485020b40c1c2c0c2d078550b031031141510428600022407080002c000100b200c1c40c00519504095440c089402060fa884000c06a4200998600e24030340314101d401c0c2d8840480d0010510102c00d40031600f100c420440001080c41e41044041060701a5600a518030300e400c2134101e80d00082e00c0b40c030140c00c1d00844802482e5166000c441d60256424540d00144024107200035200c1400000000040f42c140900b0581d25540301c0980104100c0c5001c40c0003903078061824410001082841c07020482c0e191001 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 782701456 1250 782700206 782700223
    0xe010e070c0201020a06050703060f121109100902090d06020d09062912031c0f0609020910081503030f07050f01141b040f0e07021c02280609081b 64
    0x680242045d44055140d1743c1c0a0480105904280354861a001031076070341c030280f9000204070022020503000e4040c90104800b900600c442c0344100f00202c00e00c00004890a4980c084406103040107a403480d0705000300364081c0c03034074001400e03d600c042107080d090b40554004881c0c452003807004000006a001c4402c62044035103082030105820020348410608044179150560b8907814200ea050581100e4440340d040a002c5080d8a07190326842220075007140d0340204d078082c0910358419070502e40c0030742c08901c032071032503801c040300b00188400450081c440e041040a03100720040e041c0c070350340d40341031866154030391200004860f02d100304000108010010f102d41c1800701054401c40c0b0803901c134030f4011a01204150111913486c2e90400000503000445210b08000300101a0003244a01c0d01c084042c2c2045010048087d821100c402c07040d03681540070800c180560b81c0801503520340550109081c10b03003e14520b00500e143c0c5040c114a09010700007003d01007020038120034401d011901820345441c0c0200 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 782702706 1250 782701456 782701459
    0x1506050a0c1704031e030f090605070b15030106120c120209070f0e0303121f0f290f121608151207170d081306110f040e010e070c02 58
    0x2a22552000203602c25280b0501040c0c2004107402d00f91680c503940798202e405940c8003031198061500034100764110503140021b642c103040c602d075a645840c801400c58070410b03800038000302c10b0200140621046101021048102400822030b443c0c0f244290b00c90b8070b04141055071540d9210740001400c0c840c80c90b0004c241640948840115214450107990b2520a03580c00003e221501c110380b4a5502c0800c0540034044901048071200c1c10864140001807a2644440541c0c00030641d0030b008150907400900c04641a40040d07c506200580441b401048034110120756440c0c0042e40202a200300c40103811a480390b8031489001d83c0364440c0d21240244801c200601040380c2000190914481000e50542e244000e019034421513400c0d00280e041c030f84550070103000034126050300018280200b2a4411748075040c20402031608200301714041221218000504443d03e40b240409400d64500c242c0701b1050742c04a40c5515240ca80b102004a0102401040d61041485000848440c4501c0800444540 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 782703956 1250 782702706 782702717
    0x1005060a050d05030f130501080a1404021203070204060e0a0e030403030921140609010e03390609060103050114010e07030e072601050109060602030a0c050c09010602011506050a 78
    0x40c1c6410320840402028041e02c041c00705225602a000910009140d25031407400c1d050301281c10b0800160070800b014183c101030514040f80d0505031503c1e24134168020707804490b4003c0000070100b60901d1480f030040000e4005050910008032061044406c501400301d00740c0c10701054058032170b00c039640e005a22001c0d0020741e500c074041140b0a4603240140340d440c82188001c0099900c0e840c1c00100302c00303008101c0240c0c3e01c10740c20440b40180a00c81d0040351540d4001542c0303401c80300703d0203270805400f0402e51a01c002405020075803507036a8000c01441d00720074500b55031052610303010040c1c0720a001d00c026a074a5003860f514126111066412506940811060544644600d5801c0b00207006034407110016209030200411809410790301070045840103801482c0000010f1004e07400c0d07803010b074480102c003400c109040c40340580102c1038454140903403404101c80c50490030260b19280c031101e02c05812035203150002c95420b506403c0310804040c43c1514660165403054221102e10810291100003038 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 782705206 1250 782703956 782703959
    0x22090804170a200307030210080709050a050f040f0e0a030908060105040908160c03060216020a090c090b213402030301050d0203240906070801120822171005060a 71
    0x4200030083c4640d1002900f15642280c0300d80c080707001090f1000030702c1c001c1080765042148c40b42e40300440c4009000107a171000011403500000c0303294103c0643e1060b02c84e84d143d44400c00807402550020403810781c0781d01152411400c5080203092414507005030341d03440c0104c0e00041403904250107509106540080011700c1c01e0030841070b80f842110b43d042c088801c48610036000022500500252010b10300305444001f01000d80c2c410001c034035080360700801c025030030204e01100703981e00325110404841c0c68a01c0c460f0b54505081d50700607030a025070005041d860340c080510207090000080c501003d040c411118042000300c0d82903842003403104d001d001c01a40100014091414000c070210145840a070440b0320908c00002a1075085140c011000304400224040040342503042000e66000105806c00c82501e50410f400c0a50360f824048021700f01c421b00103011b2b0522034111621401540500180881d025250b03800b2142d40c062000140c040da01c00c0c10300c0c40b2079a4409204280c01b035103005000b20f8109 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 782706456 1250 782705206 782705243
    0xb010801060c111f09080f06010303050304080d020f030a0b010e0f01110f01050f1f1d18031206010e0a0b0909070e12030a030c05160222090804170a 65
    0x4901e0640304543c81e180d04580b00c2e140b44c490002c4d044903408139021080c1c0e2007010900042518400384e0100300c0a6004078403140d9034a002240031380c1034070703018a0469038950722800c0407015485045401c803506440042c008110702800c1001d14082c155205061084001c0312004403641e01c4012110750340081c00c1040e60546602039400c01e46020840400da1b01c005991a08440c21140100c0e000c0b07236150300320741c20413000c002080001e204442c1c40c08001c00c10141484a02030003140c1880c070f0908004101e0300403c1042ca51101d80c08107000c00c0c503007200d664004070700000d0710b81c00c0144c8030701d40401c82e00b00710113440349041800c00055403180040c10b4103008441c0300308812071030050110018001850903d00e103035190a15051810070781d40c402596181c8100350002c0880702d81c0020a0308100c8180017040c001076020030780980c41901221400d075000b9811038070202001c00c0c540d0002e5101c0c541031030302c010880028041d00841398071039090030f501294400110348440038200000c1c0313503040000b01004007 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 782707706 1250 782706456 782706467
    0x1051c0201030b03010e0109210f0c06060302220b060f0a050702040b31110f09010207151205010803070809120a1b090506010903080f16060f0902030d030b01080106 72
    0x12a00524001c1080e0520300082400c662079025a451665150b41052003401081710015080c21201c1d0398420704c1403151440101815800181da004000b40400c5800500410b41c11000186030002c0000c1031065044001142d290152045a00c200d400e0071056001403500c05c2c151240d03495443e90701880e100e61818210340c1c41d03000320000c80c1e2141d640e070a42c21542d11000b004c894000c240101095804001c1881001c02002c070a100352400c0342000d1800e0751010040c2d003a20159051042815100c0c00d0102c0180c0c1003c040d60030807121002500e48035051141d200010703040020a921003088141d880d06085501c9110f5910081c040000400c90004c680c11b00c161000e54076080141915203160302981d800141d0381064100000d4619508400e20080e400e43c030440c0c2c0c205d03a00f402c114070030a24564500301c01b03014042c510003e025000c5a018110b60b448002201081c0d8003100400c42da0341c00c400d4400050109602c01c1c0d0080c800c510301c18200307500901c0383e864240416141c40845031710f06041242c4 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 782708956 1250 782707706 782707759
    0x8011b02072d030b010614130302090a0f0e07061101090803060603090f03120f0601021507120b09042001140301030b040f021201051602030405090408030a110a0203070213050105 78
    0x1412214a6034000002d40780300d02500610310a850350f641e02e52511000a140e10300303034050414007000c04c02030b855840820b1181c0700c0031250b043d5403200c03040e600c010100c2c00401c11501c0204050b814080090200b001c0403540038160342e0340da210b0040d4180e64610f842c3c200c81d40a20020481031040001c43c070300349040d03c00b45501809040449209050b5040042e0658002004507070302e240d500c6086c40242d1040c0700410303a2010080c030081c2290b05072a012029218070140c1000d06000703450b1050b0b40300c81159000094400c43c0070f00003140d40c1c00d052034034601d821580e0640f40701b005d203d1790039024158400c0e2001c0000603000c080c02c605503400c0d1f840d80329402c1d00182c8100c4851703000c2c204220050b151500101805464040006042e24022a00002407000c01c0851411500104000d1000755107461085801c2a0020700f020b48a0303841107a46401824644401c545642c80814048001603000000381442482902d480f403000800300070404c1520b07030a0080b140d00810a20b00400305a049c482c0801303 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 782710206 1250 782708956 782708999
    0x926030906090a031b0303120b01050304060506011b0309091b020a030e0409061a150306010516020f0604080f0118020d0201030b031614010e0d0f1205070501110408011b0207 76
    0xa07144c0e5070340d603030080075110516000c3d42000b00b06010030a250b00f141744840c03041940ea000784108484000001c0c07072407000401c010801580c90011a400782d100b04a40c1c001c40f50038a04064040419050103040032015215039941c03075007085007201160300503c03541c0603228110740061090120302c0c0d4060350903403030502c195504a540c0d07040e2200450340c14058182074408085542d0014921002030112015940d012802c00e040b0401c00d001090740d0110464242d00f40402c3c070382400300e10502c006001e6003a03200101d680318030302003000303d0300c640042000034005860308002c00625281c01d104210031070134084042d52101b1080c40c824055402508491403600008080c0c1d80c84400040e600c0031015080c1e08142c40340c2c0c0d60041c180041c0e5820002c1c814015008403654125841941c0d10040100c82e2400010aa025542079035008603016105885a041c0d00000904c0b004111042501c2550051b108805581d03090807a02e510622240050300010340c060b40c0a0090282055502902e080700e142040d07 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 782711456 1250 782710206 782710219
    0x8061306110a0c02270a09020d0204020a030c09140303090d03050d0518010b0109141c050a08070c290a0c14011b050418110c010c092603090609 63
    0x1071400a80e00208501416611810984200343c010f00c0014604104a444450800060303034801030307100c2d09419400b81e19282d0100d1702842600c0424410001620020b412900103c0d140c4030705505a00a1511001240d8801d0b20751641d4402403010b030102c0f82e24080d0103400c1044480200e00307055607030081aa0280c10b11038940300524540c20304443c000c40d43c1e2074048840c031b603415080030028021b003110390600740b9101522a0924070b10700d1104004001451040443d01011034100c08094a0441800d4010082c1d4850302e05500304181181e00680044914503001c19020401c545c090032007200c0d0b0300501110f072816400485141d10107511010401041c404015810000904841007079104440b0f40340010901032111b2448407884075154a040060160601051140d4040040035220414540c0000b0810010b400c4010a2038401c2c00d0303054a540d400c000032103d40e03036081b00004080724407141040310103000500d50340102c21500d603128051904200040380700d5291181c060101100000c101 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 782712706 1250 782711456 782711471
    0xb060607020d0f02040501080d121a15030a230f0907170f010b031f020307090306020c0c0f03011b0309050c0604061119120f0e04020a090e1008061306 66
    0x103101e442c1189000c4400c0b0f0751803400341c0c04500b09805591300400d00320004011034000000050071340035021024a2801ea55501c083d0f02544082500e6040008040e04072040c001650403007040360f52007150200446070400080c004c0302e03a620041c40094907444030b1a800552078440c02c1d140030307000207800030246100cac0e00f0000c922010244210800c0c074503034000400f003280498002d00d0a4980400e24240310b42c11410103699640210ba0403c01080d4292400582e00d5640103420b40314840d00303403c0600094030120350400820000a500c01030b20320101d6910242302c5000c0101400d0b580e0700c410825103240b86814051410340030382c006041d09442403069031079070107a1001251040d00031b50310100c005110550007103c03200c801d0011040c102210707034600010001c02d40b2040c007010901c81050081210500100440318450820300030301690080040d0759070038403410010900344c0326003d090040701c050004140f6210000c0c008604617030490002c0c00071503845503a4400e15040e4200280d8000e52100704 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 782713956 1250 782712706 782712709
    0x9060c060e010507050706141005090c040b0f04030b06030c060d0b04060b07210f021f0209030109030518120d050f0f0406020d08010506070302070b0a030e030d0204030227040b06060702 81
    0x1850721483c105d076501915034200e410100240c0d11004034403280710b00c0c09014019448040360040302582c1081d40d208a0540314101d0298843c8110360044c14401c4012900d502141501c0c0010300c1107178000c11512030300b5105c001c100f6444001c0030411681c8000100480c0c07100e240c0c603811141c02242e00400c00100b8a60311038590081c0d84c07003064111440c0d603030302c201c0c21030040102c0c550400075151480c1c2400010845503010b50703501c0c41c50320300456500f03003a10031050944041c0c04803803019001400074420720560340380250164110402c00c6003c0d09061001c6e1410b8100030048003000f040c0c100c000c0c0921205120181c032150b1080030501041c0000308202e0300c2d402e01006c010030082c0f07443e5000f45156a401c0800604642043e08032500c41c160420115011a600168400c299104200020303602d001cec855043e4001c00d0039003509007240c0004136065607440051380c0600220f038001d407421400d02da82050a000070300d4035941005013960b01d9401013404141c0d001c1c40980d020a029241c5450000b40c3d40 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 782715206 1250 782713956 782713961
    0x30f020c061503060f0106080c070f080a0c1e03020a1e0807051c080c09010f020c2e09031a060a0b0c010515060405010e0d08040e010e01060207140109060c060e01 71
    0x54084a403100300e81101103050800704034440c5c1c440b50b103400210040d414064003d204890140050002c2d89e8089620003d016441030300d84009507001c40826a50402035034094141342a2704d40a940c01d44078200360300e44041902d030b90400001d905a0241040721866607486589071802c2440705400c5c40e50203144000624410001d100c054000d1000308840b4150341c218404070080108030004208444050105a81880c2c0507a10f1868090070521002c242481c012486c103110b000c10180c0c03101203d036805004e15920780d02100c2008040d808014980e500e00e02c1500c03041503a01c002403000d00540100c400f91503003508a42c2c0c01c603e0007004244c10b240e4900110980781c02100402515075514411710441151205a0308552041658450704092600c00003070446061011440d00644481491100f000b14100c00c4802034000da604d6600e07103507150310074004910000d0042a001d4850104042540e00a508104000316016035030011510304201040769940504041202d02c0c075100d05070821140030a0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 782716456 1250 782715206 782715211
    0x5190509030705010e0304050f060706200c0114040c030b0c19051231080d09050106150203070c17010213080c130b03061f030b01030503030f15090403030f020c06 71
    0x140119140c50b86401c00c0350844049003840301140c0d204200c200060786400e13071b824001d0b10b012030b00107844183c142880f82c00791640300368460280100c0c2608240903624580940840203400008005510070300300c2081200c102038402501d815402d6004200203125003111a42c09181078484e80d0501114032000c440d00c8080381200000f14601007440c4c51108940c0d15103070351040f41004099a040303402000d00300340c4404044102200941d8500c0c2d41700380020760086400f20107002004100440f000d00b0114002c041901801a4130780700c500000d81a58800801d54046030381009801e442280f4180007030040d100200b54004455401f8001e03261030320400c855840c001d01c3da901c003520b0b040c0c1d244c0041120b440700819504003418584a030800c0e181d18001105a8401000460000b40600510000349115030980c0010010030007000007004104021001e54042c1c09402d1034802c0d40c0d103560004880c0c912046070026000000c60300040c3c0030a20a410924060300000f07401032034a25484040c7d030821108 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 782717706 1250 782716456 782716471
    0xb03042909031b061317040b0705010516020303150f0f030105070e01081f0b03070c14010c080a0203240604081002041701090309030b0619141206070f03051905 70
    0x8904520020994050007103040d0a200c0a0540c0707151817004681160380724031018021100c0700041521506114040311301510320b030b0031070984030407240c9007541c06000c2c21031302c00442c0c3c510604142805400041507900031642000c01c0c041c54610395042c022801c070060103156020b02c4401c001055510203116090003810182c0d12207410341c05100c009818500301170701c1741a0010302c0300030b4242d68114100d00c60041c0e03031441c0c44c1e0700da89803580c9408407101245072802501e030342048c1c1007401810005510650307081000b80c54074081603880701c502000b00d00081782c1030456425610680041502419469214581c00918030344c24943c03140152494042c03002010507469a00180034000d0181c42e2000c14140c1402c0030003032182e0440c0c0c1c0d4004000c4421480300070114045400414001e035129401d001c0101203501c4041509940e5011004958051070380c1300380a0306c0b070103000e5110f100303000c030b80a84100440d0b141d0340078100f0f030003c044000b000e004181d0840b02c0c415400b81c9480c0b1199000b680c0c0680d41 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 782718956 1250 782717706 782717713
    0x10020109060c0f2102090307060915031130090c1809072105010504030306091d03030610020a200307080d02060a090212060f100902040b03042909 64
    0xd24103039003100c2000e40800140001400100c410550000700e1894207441e04c403603281900c0081407082d0103400f5150f000c0d0f41c140104140805c0b41c4c2d501910200840d0410601248449a602d02c245d044a035038540007a0b10510810421000780607900d411825140601402200c504041a031004502c0d0152001180c80c5c001400170a12458030b07110a10150044c50200c00e52030030a0800d09030384241d1442054046031514074003500b00302c00c2225054000d50004002c1c483c500c1d107490000c1c02030540b405421022460903204a09810004902c00d103404000c1004514503160701d0704004580d10000701c114118401d50803c0000524440c840b48140b4489280c0711107a007a81400f018144215508010240d5024024184495500142407070300b0185a500002d0b40c29254001f2541d02c0f1305241304440503126000600400d541e051071901e21a1000c1d0305010480e94030350740c1130b809030700c03651051442d40041400820302240007403010100304101d640c0820008070840c00200c2d150902159030101d180c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 782720206 1250 782718956 782718971
    0x317010e0711031206040e030f0f031b120606180a150311070b01060804230606013f0207150209041515120621020a05090106050d0902030a02100201 65
    0x207801c200049000b15941d03010f1130404204640103800310200a00d80361013a5120240c000d04590b06000701c885003110040102e0780c80529040c1802c03998000c2e1401060301c3e800010380d0040e803901000340c0392051030802400100d034884208001c09a0814002058000c0341c3e4004521a50354005c1460f00030042e440e0420800d187c001d0b0007400b00ca01189505107600001c02c28800002c01c07080c00c0c0390640d0900d0034890910348075820a40c1844411100800c0780e0350420300240c0d810140010024820b24090740d40142e00020030001c04500c01c40c41555001c82d06204e10f1400303041c0100800b00013807002e9440700604244550702e40744030202044130312860b0154005008090741c1498000c1c008460403040052500901e4980c00d110901c8050f0002810040340301c0c0e20304174100300f54000300020400000c0108840038507458000e010b91a40070201e118158900000825041c40401241260030949450341032100d06480740c0701600071410308903414003400788600300581d10070200d100000710350780c00020b070304 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 782721456 1250 782720206 782720221
    0x2040b040e06040f02040e04031202070b0f15300a020301090b01030b010902070b16090e09070e16140d06030c030b0405060a09021e010201060b0706020a090f0506160317010e 76
    0x216030048510313421a00411062100002400c2c0d142c0e0016031601c0c08000144020011100a0054450003000700301c1003401c0c01080001d0301010f5000d01038946940007420b0a4404104150450b841e05801c0a4142100b49240001d88601c6003004140c60040e03440140803680003900b100e810040440d407800248006006020b1340d61506405807480d51002c40c60b0441d5034070b91650158004000320f64020841d801d1740f10766841031245500a280c0b14120f02401e0a20031012030f03c840032402041400968600000c2d03002e1100c020f01c0003203041540b00c4104030113403051060b5a41d030100c100d243c5000e80340d0b400080024000110680258095802e1078001e041502d0014103001016240e419540e090500d10000340e13031003031b1040545200c008098130000b5810300050340901200e034001071400002003504010310950f500100040880c070384e16220700980754540342c680903400e40070301c58001038203000c1000c1c018010b0f03920302c01c1180a4100711018414002c003d94210101f41c02c0394025071054000e002c040c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 782722706 1250 782721456 782721461
    0xe040812071103073e1504051c02060c0f03030a06080a0b0708060a0b030c0306040e0d0207051e1306060e04060b120a0207080a0f170c031902040b040e0604 68
    0x70051902e800e115040d141d030255240a000e0700a49a80d1a01c1c1c0b840c0c0f02d81c10204c0a216607080302020a040540e010003100c96400e10410125029004c2c0160700c5605050702c0b4100d906580006043c1c0d8464031b60070140b040c07940c43d023010480c0c012004201a4052400c20014003012094000041d40e891610510490545203d5072254040d54131043c0360b10700103001280745e00d6000c1814075014800b80c2e91080003e1413941c4d0395200e605403460000038003078005440702c0103502c0340005072020700c00020581d4030b555448058084010058100800c24806031900c0d02c810840010f95a05502d1900b140200091071803c603401c0214650b0b1382d03003000300300b0107402c02902c02c40d4050440f010030540e0328003412251544a101c4205410002d20000a8010f841603411344440310f4004a80940716032882402034208201248600d001c141c3c40e00c4448440300301c80603028814141c4a01090560716031450b50000720f06a1072004c90030315000e010110742c0c0d0000034058801005850002076060400800380800c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 782723956 1250 782722706 782722711
    0x6030313171507020c19090603050109021804051f0219050d06090203010537060c05010b04091e0507170714040908070305030c12100302040b01111c05040e040812 71
    0x36001c1900080102690f00490b51800c05c078401c0d1110310300002104060b0248103001d4201814241c0761180102c00e0200550001240d140300707a0f104048007420341549140c01c80203d400500b25404004602c7c3c460305003000041c2c400740c107458090700301081e900c070210608980f402c2680c0000e0002c115600c04420314040c400040003c02011031455041c0000b29941904820280c1507902072111180c0b4080e01c0e02c1031204403118541c1d6451006e40c1c131130034005c119842c80c03031058500b0342c28060000e0b02c034074052003031044003540300a590600021300701215480141844003a140c42c021803000050750b0440c80610407407001030f170b4050178005091013100d0307140b0020240054059031800c040a400105603404a407521034141c2081340c0c0340e64411002e05154460070003084c0199030114248100340d500d102c081403d4a1084805000d440000001100c04d049001e1200e40d50b40c1c000401e640b8081e000c4041004044190314085240985990410b00b1040003560301f1141303030400154192082c80002604c54 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 782725206 1250 782723956 782723983
    0x5040308030c190c021e1305130201090e01050907120e0f10140402060a03090804170106031416151704050c0102010e070609090b04020903100506040c030b13050603031317 75
    0x81d00c45115801040c0071090300c0c803030328980b0780358890495801c0d0b4428908245410750b200d024005407510016450004000549c01c0b4085080002c01040d4113030403c200905072100600504059918480d0854041412170310805a00e030356845c005489403418000104003014030001810760003500282c41040700c0842c00358042244165060200507603540040300c5841d4280d113000f042103003c90030710241c2e41c45541d00419251200cad90643c3c240c10010f404c40c00459010705003150904a01081c125142c41d004818440030b00401c030800d022560188120b8a0014058642031002d024016040b80e0400030a480c02e90301d56000f040b100c1500d690902a0020316502e45010f004d006241800190440c80240078901d06c0311b8403504100125221a03058440e600ba000301200c0e27080e06c045071a50f00030041542e4072805a0b0510413145e10090013401000f82525020b400184070070000c48207140101000f81c596607050008100300f0300d01e9024900e940004e0035528003010303d40c400e01e0f46002c0c641320b0f2608008 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 782726456 1250 782725206 782725217
    0x3040b0f090d170601091205070312080105130f060b040303030b0a0b0903030307030b0102120d2c03120a0f090b0709120b150a03080d020c0c04060e1605040308030c19 73
    0xb540c01e80d4410b2402480750601e5500250795111040183c80c2e010003500401030750380c81c501c00c507403d00c80005111421a40292401c01542041c01022690200240a07a50704a4811041085001c14a034421540c0007200300d0300080f0103440c0c16074014598016401603000a40300d0040701c5c1185803058412008143d1610342500d0042c40c140426280c1c04000e1180d07061581d140c0d40002240d00a112a000d01411515047e030f07200c110507000b500030500c0c01e1041c00608600c00061141d4411044800034243c1c4440045007803080d180f50004460300c00a00d0f90050369126068095014400d01840c42c1c1e0030b00c60000d0302007520f00b10b040103003600260b80c0038008198684610001041030010502c0d00300144001080e940110100070070402507080e07000408080d07000482d1211038100b5400b4042c0340f005035003030ba14100074400802042e0f40240c02204810b882e10801710b070101c060004500c2040c045800c00600b000d81d03a440b81e070750329042201d1031400d0b40c800065280b00e4101000d4004a514100d0500 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 782727706 1250 782726456 782726473
    0x8040f0503070806061c06090602190806030105040510020a1713020114180418021f0e03070e0c090109030f05030a0314041101110c0904050a0b0609041a060f0603040b0f09 75
    0x200c0d240070482280e846e01c500d850721501405107a81202008a401c03034425540e445c020801d00c0320002803600e1140000c1c060f034000c02c2c244c0c038060003068015900803008100321003d0042c040000e52109842d4401d0081d02c540070011500d02003c1c180c8500041e41d12401c4070400d034000034040342e0a14043c160602c84c108507001000c001e556a200d4100d005a0300019203091721410704944001c041c8019502061a1005904008154140440e1500c05544000e00d1f010a8406c1c1641c40869001d601e0801d203020b40080c0ca40340b45440a490010014034200440340d580c3c0d21001c1c0c035030300008000d5500390800180e410301141c050058040d4482c13158840344107480d1030780b1501c14441c40811142d04100007034689540f83c610030014859491002401000541028548103580341c9040d1f4040381c1034164207001820381e1a0840a49108a4001e14000101c1400604e01d43c01441d00801c615401000c40c01852606d0f210200914413503072150081e070046050080c020251310310700400300d5845a004088 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 782728956 1250 782727706 782727709
    0xc120f0c0d0519060e0709120611120103060b010f32030103080d1d0a1104060b13030b0108010b01120c0203040e0403180801060b04050402070804092d02090108010608040f08040f050307080606 84
    0xc0c5d2802c82d2301595016a0700d8100341b07002c00284c100c01100703000106c0c0c0883c2c9a0790708803d060b06d182c1202d10a51041003404d80307000043d038138001c00c2e40740d80010502880000b03000001c14482250300c1911554010300d009103e40c007071040c03500b007a081990401404070700810854698844c0d24841500450b11900e6031404140c0300d0382d03801120100801e60142c240e805019900e032500640e0180901042c96a1200c4843d400c82c0c0c881c4100344000d4990480b56400055a10410301c6851075030701040c7c1d109807007007403012810805400030b5a000811803004000009000d0a4469618007881c8a80e035803580b94040c95014000b281c40c1504452042c0e49022820085000c044003140c6c01c036001602c000d43c6070051410004628001c91b444080c0c00f07401c10115114080780c0510706c1100c041289180140409901ba80200724002c00301c6072030200e05810014030500380154100340d4098420b41050003071600c90b03555540075401c1a4040f072140030090609002da031034280014009070a19100600c9280740110 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 782730206 1250 782728956 782728967
    0x90103020a0b1309020a0f02010609020f03040b10090f09230304150c0503070f0b070c0b040f020301020712031e0234050a08070b0c120f0c0d0519060e07 67
    0x200c2c240203020002140c40d15140304050803001000c0d07051085455948a0070040d1600c1c494011180055103406400705030102d8074829500103100214049040d99119a600e10503144050314074071014400c03020024940703400d40908002800e80100c00300d80320680e854403010000c8045004801c180c004102440002070000503078048035034203c00101104280304068864022010002c3c000d408002081d105224070030290101552203205422040da46440c2c0490b13015015490040012081601003400704220004910240e40001c1c0018507000440d66014036100044007440c02107511240400ca0540c1d1a99904941c0380309080190300d01007541854500808181d00c070f903a180b01d0301848007421172150040b1941041e074028101c46143c541410071516942000b0b20403a00c51850b10001003103a0401390960b0159060840b1001c840d480e84823481400da8002010000003240c1809051141c1c3c03640d000b030600401d04050000400c050000c0d00e08161030150700700381342510312070051000465002 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 782731456 1250 782730206 782730209
    0x120108011812090314060103140a05070306050604021c09020a1203020a060e071208040807052b021f0801090b0303031314012d1b0e01050304021f05070302010b090103020a 75
    0x546012103003402800c1c103403040c50322a00050300b15103080d01000042c5d400001c01606aa0060012501c0c0e00b4030b00a5060369042d84440091054111440c10030005529402481e0802401440941010a00c4019241d1000d00e1a5401c080e152a505510b0650030400e0580d40600003500c1c0c51903008100f520065600e6070300c03000040c041c03540c4010380c0380840824403030b5001405000110b407007015200d0900981035081030089131124001c49100050906d070044a04203c1051080344045128480c04007041882407100160303040501e03c410141c2c0401d19031910480f103900c40c1c0f140c19042d41400d22050072143c500001d240240d1003082030014023006d100603401c406038800012031424400c1d40c81e00d400351801800c44405004d00d191043c044148020614840e00b050410401a800c03405542c01b0711032134400072907004141107050b110820b520a10041d603102c0d00161040320398400c01d40306502c000681c41c4020002030008141c050030158203000303010344040c04031985a40307035046400207001181117 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 782732706 1250 782731456 782731463
    0x608060d170c03030414120405150a091e080105130816031101050a05060f100e3303040b13020901050d0609050105090c042702270703021201080118 65
    0x100e010700c007105200e1000c07100446102010380c0e480382818a0080744030404001c81956a004035048180610080025102181d100810f10f007250300382488080500c0d0301c058035500030005004030214802000e080302e2030307000107281d4001407000c0c40e0000c03646c00c4400207000c0034001710040c026000451000030550b012180498003210320300e4254601070f07400c2c5140360040d0a031542800c0812903180c19941c00700e44110829501c1c49800840201040040c2d1203a00214000c2150030000c048903003410400f2010a8003a010341d8004400800381c11041e9090046030b007900c00a00204102c20401081c4129422141c01c4071001d00d250078642c0040c0004c041400b501d0f001c0c15a540c3c448090001c1c5030480d0719100c0c0c10200801a41c1401c002454440a01031452809281000c81c4090350a20f8002047000054801c1c07402c064081030b59013005500c07041e80d41c458032510b001c0b61026104c4285201640d006009a03140166508041c001c40354443c0c405034005061030b45000b074000c41903071113140c0082030680d0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 782733812 1106 782732706 782732723
    0x7230409050a0c23070602030103230d1d0d060207030e1c1a0a0204030b010b04081018112409030f0f2e0e0c0a0608060d 53
    0xa9096000c400a0402d20411019511314410314180c514041a030a140400c05e860b8841aa0400c0c1c200f5140c10b504c010302901c481c0031048800c103000c0080c10281042001c0c15034051309030b100c98a0341116010400c1852286c130369451001003012988010119110802c41c01d00038206c511003890b80d03004400c0c0c075040e40ba04502960380b1038145030384000d105a2900e041e502148030164040c094100540e020700c004000600f0601e02c4501034a40c2c9400301d41c48030314040009181605501050051030310f00303c5141c1c01d56a8054071000714a8002400314080500303100800c440c105c0c0c03a0002ca454540c100155070710300782040002c3c510750030105c0403902a00f0040344525103134108003500d0b40d0b065021200d41e11541d10311181c10031100c204400103541203480200d800090f10401c0e890617919401201c0040110700c3c0041400740a01040d1420f58020700d003403800f0038034510f450714000d041c000 = true := by decide +kernel

theorem cover : BRFrame.Cov 782553956 782733812 := by
  have h0 := BRFrame.cov_init 782553956
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782553956 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 782553956 ≤ n) (h2 : n < 782733812) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
