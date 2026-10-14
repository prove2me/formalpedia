-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2853
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:55:59.606507+00:00
-- url     : https://prove2.me/submissions/26eb7089-6f39-4bd5-a7fe-70324da3fca4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 512949640 ≤ n < 513129496 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 512950890 1250 512949640 512949649
    0x1d1501080628090c0f0609030302120c030c060106020619050c071203020d0c050c061b0f070f08030403030207150606050706091a090d1e0f030b24120619031709 70
    0x100c50007150a071402c5401170115101c0b030846840103200ca85441003006155480194480507200516101000002082c5003c1103007041252190606101158419a91040002e4540b01d06503440700d02c422180c5044100e07143c45001e90303030241c0c90014020f4a880b9203503803204070800262044a09140d000e020850020415102e1154819481d4031410781d900c200002d02414080c00601c059540e00f010380c03190b080061000103030b90070f134018101c3c029620302c60b41c28079007603031103601e10010030b000c8000042108060f172540140c00c0c04c034402d100188070103c0940400d0240d411034005d034000170b8020310000d00030440b41d4102c0a900d074000c94140c403002121340414111210115244d07811036020f1301c5411030303c55000d04140002103004046051280c00448001e02c00c0d02c1003000e03501051345075080480596106a00041c1072503140300041d090401102003a2181e4000c40d0345901a00d0f0b908000803411306010700d8032004a540c0b0602c03a4201c60852352000306030300504070192a001c10501041069485 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 512952140 1250 512950890 512950901
    0x60309151e0204140f09070212070c08070f05041b020606130f020406170115081303020c220c02061b1e030906040606060e0907050c101d1501080628 65
    0x31210b0f64581000a44c00a00c170303040005032a1203014030251410000015030110300c9a001c0001c0c00381095030f41507c0d0410511860b029041540d05019a03400000c0707402c500c2c1030081c02c482065406000b800f0050303101607000e60320000d070500035800000c0018024a0311200c1d920704c0c500c0a0b01d0000b840c0d809030701c0703500c100c0e002604800d000c104c8a0030b40038800502081c40d580108804524034000102c0003000500e5168050b020070700301c23094107810f442094002c0c04078151922003d4950a41c000741c8103c440c282030b0000540042051070011440d06451010034518800e100b08510301340c0340601007954003010f03800b005021240742ca40783c40d42e80415080344000c40c001e00305400105103d052034203005040b074840f50304c000c0a018034405c2005090b10b811020603030101d582e00b0103585076004404045d040c1200140e140366551b290442c450098103020592540030b014050480c1c6080c0d003c0d801c0c11182000c00c0c0182c01c03a561002c800114030300409a450f03c0388115402c00170103200007002d0050143c50 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 512953390 1250 512952140 512952149
    0x41a1305070f0603110a0c061a030a0b18071a091c1115070f0201120b060403150c02011e0507020a14060a050a11120606090a061206060309151e0204 65
    0x11840b00403c6443e5050045840078108a0511460a43e240c4c0000d48492030010740282204d48480080c0175881c20700c0c1100398120f401034280e50419403245054100860111203058100090206220012000240c1d5009807204002c0d44030050b140b00c0c05c0350b42581c01400d8129401b61020079100310281c090300400004500c11080c1140c040450020480c910b900c05c2000102c080040c48030b5000f1440040b44100c0150302824402101c0580c901071130090010501c1241c1c0000d00014008204028a04010b24038a1100d4080041c43c0018004900ba078040020100541c440c400c0350000000e0741d940a1070300005280119410918150780b440d560840e40007809050760003000811205501398001d040d03221581000400c8102800d40c0d03c21b04c0d42c060900d500b82407803045070001d03550b0b071107003000c4a0404c0c2c40289850340042c1d5951009041c591205624000340e820113400040c510f000f030054031b4103d64080034421030207025500c01401000342a10f000781140d8413040f5840030301890f02c0240701a1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 512954640 1250 512953390 512953409
    0x7170709020a0c030e010201110d050603100e0a0b060306042f04050a020a020d0305010501080114150c01020702150306090703020a120e0c01030c0924110f011d06041a130507 76
    0x400c0f904001c0c05c1d072404820402d05690408680101103032940040740c1e1181841c1e10001001c0c0c480030007291626600100980f0f03060b19051443c0c80c41100003d0b001c00180c801d4280110310b80d150401e0546540f01690300030701001a1500600c400700c408503015417083ca101e00c4020802c500e0301e0018003907803415907070100110390010341c1d084001e5041c085074503054810b0074140305035498100002c0680c0b00511450024880113080040f02c3d54520445580c00c180e40c440d4241c4681800e01e14900030f60205c50708900c6101010242400c0128000559218000041c40d00e0031035940d03240160f0195100410440400030b81508808461010b0300c1303076802d400052002407000201c0300001400b120138944540b0188822900301b08110034040000e600082203070303107111030b0716241d8100c259404540aa200c2a0030b00658240d1a12108158014822400c1e4080c90101d8480c48000c9143c0b5007a081c5c0d00508071041900035403103002c514106094020000c1e150a0b50300c511152610741c2091f00d40d40105622 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 512955890 1250 512954640 512954657
    0xa091a0403120f2d021c060f0608090c0607110303031015030b240f030a1e0903020a2a0801050906060103020c0a0f030309060204080a0510020c07170709020a 69
    0x41c02e1610400b9882a8290010007095038000c0e00300383c0002942e03c0488034005000c1c0b404212900e290160740e10850010612040f0000a03000b0740007900c1c003030043c1c004114000600055480c441c4074082d00034a80b800141041d203800c03205000860f07018100590720004004071004182d142080254801d07940d0814208070b01e030403c5554403860040d9128501054103010b0086d440b0b6031920351825244400c1090400c04180c0ca01d08080740d401035042d8000b55680c08000c0005400480e00700e6034559100b44491011092014060400c580d8171302d1020700141e005201600c00117051680d01c0710004004002809014000c0100c0e104c0100781c3c0d000f10020365100c2050014040c03042103987d030131080c00d00b419401c004ca041e011954500012201400f99200321a000d01494081e502c40201680c0180b02036543d140c0710510070340e0310155000c00301d800b4840c4c0c0c11520004140e82c400e84801e0148400070b49101441c08601d01c0c5400c40e090441c441d18020520f0005603805148001c048401e05625084007 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 512957140 1250 512955890 512955917
    0x30c03020705090601090b1305030307150506100504090f11130302090906040b040b0a29240a0e040e0a031106070c0b01050d03050c0703030305010512030f030a091a0403 74
    0x1c22005610150188446206020342603801541c50801c3ea980241090b48900c6e201c062000746030441c3d032040350940000502075003070003048004c29180f0303d00a2014019610781d00244181d4011074a090800500c0600c0144400c0d01c054015081f242d050742c9022078400400720402c8507903440440184043d5910010420841c10415079055014840c640545683e10702074aa0024112004000a00305013190300040d601c0700c1554003d4550b60078500b400c400900401c070100c4c1d07030f002a03160242e1141481942291f102ca960901d21107490a52003a02c0e8103040003688107640c1c9003001c01c50745600c135481c1c1d0110070502104015003180a4003e549460035010040c108a0410101410f00d408000e010009840030503542c104c200d04633042518081c5001e511418101c5090051807211080c500500e0000814554507400a50603100102c03050210002c0803840607540348640402c84a032a281440000c18104860f400300c484140145100d002c405011042036480520840741280032070b840c0a9010ba = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 512958390 1250 512957140 512957143
    0x1e0b0a0609060602030301050f010807020a0b2412100c02010b060c0601030b0c030c0a0e0105040902120702060114011b080403151e0e150702010608011a030c01050405010518060412030c0302 83
    0x2860240080d502c0c6d541000301041c1e190200400302e5062104020104102c188200310300044182c000001143c5804d00081c14000e2403240014640c0c1580307d0b82c0e4a08140c0740c00b8006001c5003903100010094000800c07502c0001e01a103150810030340d540e0b0a400c50280d1030307450062201b43c084102400f610b604615103115141c0010f0807210743c11100348100304003122920100c902210031400c1450340d00c0501d00c012955072042c1d0304591b0840c1d0001c15007124245017108214002c80694080c0d4810340c1c1c0310308200c400e2134074001c08140040e0103107400c1032060b0110405400954000d00e01240383c02c3e2242c45981d120900f148207051070540d00c0340c907403013008001080e10028218a08050000008001079541d84451884101002000c0030b008240028003d600020051181c1d000a02800c003000015090111104c616071b4060f0080ca18084230540c416022202580c00c161903180c104541c2e40d9104c003000c1d80400c052034010400304000b15102d9540b000d1804ac09120b9074840101050a1074001d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 512959640 1250 512958390 512958401
    0x120905030418050f0c0c03040315090209010b0910031e02040605070c052707120f0608060f0408031b090d0821330913200303071e0b0a0609 61
    0x200c04103180000f40945442c0450105801c590a1017003107440c4c0c403140316414210310541d80003c24103140c03803d625800e00e1840c0c100ca2040c0e4001c4030b0040c07250381d07a03c03108038ac503100d14030186500c0800c1c14103eaa201d4081c1e44110350300016810307001005240d02000400f00d030720030b4100101141c00412000200304070b1006000190a0559918030803d00150821501a0f00d241255681d142204002084103128048101c520501081c00303015403500f1440000051110780500c003014050000000e4096020500c4d040c016a40901034a140d641d85010071034860520007030400c0d28180c2081104101c0d130b42d820000080e103004220341503540a0000101c1594600d170004044c1503c5240108600d0038880b2495540c9942d0041c120a14400038082e0b5041b020184800c0c0c951140e5000c05100d4807500b4560700b424680e103e041003a04107002403122185142d60100b00e01da050b4000c0120700c0008003041e00c8070920240d1030101d12170352082580c2c1c01e070404c4802c4940c007640540d110820405440b060141c2e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 512960890 1250 512959640 512959679
    0x27090102041712040e0c090a17070b0c07050d020102070b0d1b360807090c1701030b16050d1a0f060a05030105044106040c02030703030c1209050304 65
    0x10310340300340000460b98540c0254405e00c4140070460000038110350b007180c100e88a81100400704812281c40e1188071404103007a0001c050140301d00c0301c0100ea8241c00c04129007a0000300001016040e00e0a010413000f03119a403001c90450140000001c0c104403108051f0521003842800441e6041d580503034642c2404005420750300b0418103685030611440ba0004210000d812030007002c04914110212124174a09903115400c00d100714600003801c2d20b441d0b030001c407601055640c0d03220707600d081550700380204100380406000701c010940030a400c800300e20701c17215503e1402e0806a081000030740024044610900c80010b010ba50b540d02645c40d032a1030086103c2500341112803500b04100450300030120300050191600596880718841c60011001e035030501d00d010302241c4080c10050b0f0980a0b6651504541c40e07a8807019294003141c0f4600e03240c001e102c0c1d1000c407603000710300380740c003d071001c4000d401c02207070744820b2120080301a44081c005d8050251038074000e00040d6a2070f407401c4d1504091441c008503 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 512962140 1250 512960890 512960893
    0x210b090606040b06090d0b060f030f03090301110f0a030906090b07020d0f03020f090409060f021c061202090619030c2702090102060103120509060a0804050606040b030309270901020417 81
    0x5c0c0d82d0b44010b0a5210103400c07001c05400d958514011a116550040312160705105184e46a9501c0030004020070040d1000c5d0700038001440800045103240c0244400842d10390014003103a81c0c01d620039031021091a0003401d010400d10070355228a00b60840a54404006030001181881d501e600104c441101080c540760843c50030086e640780c014640511141c3d00e100d95110114035003800701d99000700450340d5840710119514114202155151100d900ca10500c0c6410000001001072410003800401134024140c84101c0c2d843c1c6080080c10058886c411011110901001c004200d10610000c080d10300c00817004c1e400318813605d42000c0038101000400d51640100f00521542c3d03408618281120703884502911501d0313a0b44000da41038000d88588039003114020504048107030b809000180564021020b540160b1941c1e0244026034840c550230345d8242e80b042203002c1c180d048c800c41d19800000800138408014424545041e1101c00c19030b02c64819a402043c00d001c80a445c004d26204240c0440 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 512963390 1250 512962140 512962147
    0x1302180d0b010501030b1306060801050306070e150d092f060403050a0210020a140313050907021b03070506030901090b071701090518010509010f060609060801210b090606040b06 78
    0x5a0307501c0e100350140078281c100b64a80200003507944403804006000440b52409000fa0303502d60000800b4514244286840ba02c107080c0071076521070203035280c2020410064803031100000014481013241d401000b1003c0740603542c8814001052a130801c84903901c01d0b07401102c1e410a5264600341c016504010090711071341040104000007000000e040c031070590705403030031005411a090140d04209190801501d14005d07100410b081960100040001032604292105480e803a1024804422800c48041025074000350f121401d0742d179040c081c2d4101d0309000f001c86040c40d0701d60007c503107982c0040d1100c60243e91a500c8440411443c1041a90f00c050700386070210201030a41c0724122500e0041c414411030f555504003007580b44c084043e01c2c50041e044c00009011a04001024500a002d00407181441e01d19051000c113002e4070a907541700031500b155072071004690810f144564021900c82c548219614603075030302c01c0015210603040d8410359100001d405246407100900041d40c1001c41007030712611042 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 512964640 1250 512963390 512963393
    0x3160204150b03063d080c040b1c02160f020a080606060d0207020a051c030206180c040b0f03060c07051b0d030c030309170703121b050d02091302180d 66
    0x1074007a04c0d88071800301c94110007864071036130340f40441c5801c42d207008143c1d0403030f40107100000c051520780c0007084c070710b50b20039840ba61032108002031402980661040e030102046030004803a0020103000001c44060801031030310200c04a1741c92041403542046601c59036040c1d8a50035450300810410003003860101410003840d2400c0080c01d184940481004c02c55400b140500640d1a40350440001e1322020700804541c8540001c2140001100d0001324018461100014800005800200144440368008181c0d0741d19020400018060700e100f4207401c041e040d8684440340c3d4080083d1405001400301169071007125050990403c4103c090300c000d0181a201e8001c0a078840c0c4088510303440d0146441c1c000c00f002464201c010b00b070250b5000d41141015065030052603125001011028821b41340d1007108150445100d082c0c0da456090b4400203404208c41446080c000d000030710561440c560700616000000c80080c0e95403050408102500361b01140700310030b40103448010350642030121401c180c004c000d0f = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 512965890 1250 512964640 512964659
    0x50a02090a21080a0c02030105161b0f051606120203040201080105040e0309181603090b1305030d02030c04050a05030604020906102a030201050606070b07140403050316020415 77
    0x80744505068102c8841c00c5000300319041814410980d40805895591103600070020f1840c0c01d07089059100354600b0300443c0c3c02003480000710818240a03101c14481c555940180d001402c1444021380d01101c0e0071a5210000328180007064517224005a02e4516038200078006101c0c1c4e0303903194034008461040080c040580c3e00011868111902243d0108941c0c10a0703691505602600307040c0354201c06c6084041200c400403508041c45082030740280c1142d40d411031011003d460444501030000c0da004004207a501001c0c0c02951159130040c2e048901e007001300910324003240e00403101e8907038403240414248424a4403a410070002c1c0340483c000c01807801e0a03000115880e02c0506001d104102000484103a64069185080100c80c00003040212100e40d0580312000343c2c1002046006500c0c010001c0c102d0300e8400e0990780c503130f80c100070114241e5464090030342d844586000c06080c23910b400d110000000d0001c000802c2c160b03c103180891404001481031000750381b0f811411040d14000044140801c0a1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 512967140 1250 512965890 512965909
    0xf04290610030b10020a0311070f03080304050304081f11042303070506070b09060901060602060f100b040b0a0807080105010e0405130804030b340c030e130b0103050a0209 75
    0x200d841500105041c0da040d002081c2c6404019000001d40118003a529004240c24402030300036128003d6000c00e14014030f40354812405014000c00d8040000e1003c00c1e425009160b0040c8144200e80c90b058881001d54642880d2503050b414151102c02480a5100240a100c0000043e81d149070b00341414001c8a15895006802442040046a00c1c229099604100040042c1030203408240e40e0744050401c0040f141c0c0c101c4400c00e1921409020911420b8144510811164268050302c0300e9212a044024449005401070400342017014021030208683d40040c40105208181a86e0320091004054070300c0354000c00c20780c14007044100401203641c02c00c14041c1c008034122000a225540c02c4021080710101000142c000c0c0c2c40402c0c04002c0008510445010705004403460351806040c2040c030b81000400180e07213604104c21103686031003d000b0b40e24603540601c41e0030280c0800c5401004520120142d0184060107a143d880d0b0001d1542c1500c580c035005888030800750324180d403800101e0f240e40c2c1c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 512968390 1250 512967140 512967151
    0x20f03070b060931050c0604030b0c130906120b0f011505070c120507060909020304020d0b090f15010504060b03061f11150708060609210a02090f0429 66
    0x1240f1900003a44010b802441c1c4025807459800100e0542c40d1444100140c404501e045410784500d03000704515280807419031301182d51254203004d40d03685003401040b00d504030038400d01d003a0051080c0401c01140314040d010107410840c0441001d500281407410000e04090524000054034000510905034400c4081001075201e00b0b000c1e0f503451513803822410010f0795030f00481044400800240401c032000c13680b0022071b0401d6803800c075415140c4030224201c2c8404d490003540007440c5480c3c94005034041203041d038800c000d0000d03180004001100ca03424a444010a19100005d00005100510305032140202401054078514154a4006e001c5010b0070204810b420903000902c0d040c2420071300c00c86185000c1d00408017981c165210864403100e88000945050000c1915440014a0781c01e050081d030ba01d1800c0180031504c1c6111b460044030198034500e603105c12901801260401507141e802c949030241c4a144040b80d818901130500502401000700a043d91414a8005c0f004030004010141d4001 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 512969640 1250 512968390 512968399
    0x6101205060c03070e03070e0601090602030a020706211802120102040b030c13051305070930111801050a060c03020303150f041b030e070503100f090c080d020f03070b06 74
    0x36190b41c1d2007651074440201c5417035803603c1003610200d000662011524060303c0b00303803039200516813955401c1c0d882e0f015003542d130801030b804080100728491003620421103078180185014044d89910650b5001d48500c5038500d039103480390401110031030900030a224001c2030040300860500f4100508038440b8400039022b565980408206004e01d0f020b00ba42c80310081000520164006000484080141c18102d400d2170204041420000d0f0070040d01e074441c404080710040e902000380d0b05485601030f081198505039006442c1c2c0706600e9503070b250100040042c803041d040481c0250314003010080b180c182d54100204001c1e1500c801d1340040d400109481d0440f80e2040707603105800703c00c40400d8444085580080d030060600120f642c02180403084044550f02688e41404005405030003980c1da1030365846070a401d5402034008843c003109907032004804408501d03012805000544078030f80608500d8003c903405800100380b00c41e03415010416810a40c600002441c01e0581c02d888645e441e01c0c0040006005 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 512970890 1250 512969640 512969647
    0xc1205040b03160f3212240a050d080c1e070306050a060e010e13020904060501030501180305031902160b060a0f0b0703123c090c0501030b180906101205060c 69
    0x545c1480740c156400820951141c5038035240208100891b108487c5000340782100380e89504856041510080c010344501411400308078603195205141d039401031031308500d1405520144203480c2107510300100421145001002d1103030840c180320b411960043c00f03401c0603501d000c40400007002c01e42540d82c119160131078800e007596600070740c28501805110009500c000c106003044104290752703019905030390083c0c000f0040c11014400000c00b681c030743c100c041c020070014000148030709c0b000010140e180401e03c401500f4601440f9507104042295001103611203104802c118043c140300c0482802000c0380a81d15002d02e00d042c00010f403500c40c1e0384010b8200318007090803180c015581d82060003000c50705c032084041c1501490f114001d0a4201d41e912095480e031489403015031040703001d944030140d0420b04400344a450980151300501880e01450b400446094a000703500c9a5614568031404100c0050300340340c40c104101d80381010868200c18482e2025a0f0014041080020119440444002d0440c4e5 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 512972140 1250 512970890 512970977
    0x60e0a05010c0818010504020f041d0a0501020a0206060a12060f0b0d060914120301170717070602010b01031109010807090504020a1706040504030c1205040b03160f 72
    0x600a482002a0556007032800020120340e000c00d1092091000c1c001220f1801020300c20b00342a1001a600030390311188801d610891031a1a90000d40804c942d410f01115400100d4000fa00785088680107844503540810000202d030b0b01400700f598013500450300703285124240728110520350380d1aa00506069900c101c6034204030f14992114a803100b00034800390100c071182c580310001d44903130241242c0702c00c040d2002035040d030000070340544041442c0005d5402c0d40c3c2060a03074007038641c101c1d01c8490548101c0e40300107901480301d0351134414644404080d100703903070600308040d0940f040440030b203040502c1c150420300b37409031840030741e09c0c214001d103451405600e44010444501c41c25412550b40a44001500307084541c00c0440c02e200d046e5241400e03203559540c10100402c64604a8000d408a43c1c030a03280000140454072504c2e0524060408508154440341c0c56100e80c1c000722120649040788a920040303803904a0405181c0e40c0345441c00c1c0005400a403c40048c200f080340c080c0d003203401074101d40c02 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 512973390 1250 512972140 512972143
    0x30201020409090f02040b010503130f0f06020a08010e0c040b0403080901090b0a050d0b19050904030c08160302150403021e0a08071b23090703020c0615040621060e 72
    0x10000c0806040c00d01940f052410103100b441c401010407489945040405c00c603550145040d68860030135400201d010360744a40310503c01e01107065003258040c41421000001401c90704c050030040d54560703a40c903019070420318541c3d0000006000304034044024401040340902ea4011582529804540561500c0500c0016500710706d80340c014000c116000301d10034940d141e0040c05010007400d0900c092040d2a40c0105100e1503805400c44880302c0201c00d80280081c1c06c092803207030380062082c0b030405613a03200c030f4991041303e80081c1040c200401920303032004141351b41001214072200aa0006556905040d031303010b50344501c0c025080d500c26000b50303458003001e10180840006c80741c12034000d5a48110340d1400720141c03090040400849a24650b0101e05d03c0341469280304402410a04015440c481e50208820540014022007c00d602000901e072180002e0085500460700350890744d00580041081205941641e003140d5000032140541c1468405c4d562200e10307015030400030004004442d00c1065 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 512974640 1250 512973390 512973397
    0x207050709021828081c050c100506061e030f060916030b0a080304090b030111271c03090e150d0b0901110a050403030f092601020d14180a03170403020102 68
    0x8946010360b0200117080c0b000400c22103051207801a000c18107207101801900d143c0124548500298401546801011001e92000d40c006e00c000384040d090401c22001070507000c121594190400501105101c4809660044140c008400325075028451410807824110b02d03403552820310401d91205100d102035141c000014016160440a50387d69688594064000d1316250014500a61800c8003501030822010b0641c0e031854040440c090140b43e803c10403460340020f1040080c4d020410360034071000480d4019800640c0c0d8426103981c0b10b818503140303180d410801e009020100e907c400d603001c81c2a43d41c444d04202003081c1d104240e5aa04c1d1070f22820540100180c400c00120b0943c00610345200b1a0000003810860340721740c2e2008004080ca030401c55401d1401d1150030260858040c40145562400c1c2084003201551f07000142482c41032504242a43c1e034202ea020398100000381400315071852464032240b4000480b00a201294140e58001c002030450440701d20381c3e81d100d002080815100b034046 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 512975890 1250 512974640 512974699
    0xf030b1e041d010209090108060106091a090a0815010e10030b131208010f050613060806010e1e04060510020312090a020901030320010c02031c0b0301060902070507090218 75
    0x2880366881c01d02001c1e9001758000b000003441403458000000791143d000480505a907516550444018a4403200601d150b26150b41c040b44103100303210b205d210343c8a00041100070694a40204107588440e10086902103040e0409260104103d08000c0259601c0049804503907000b0380c91140751340c42c0f100380d00340d210702040001c10f0542c01d048014200c56101c0a41e50580e01281c02c0b05030500d54803404c20529103d0780600503100c1c0d0880d0801c10406004450440d030041e81810084e100300400c1c400a03074400d9034407420302048195003040c80910304040c4100350281c40b050b11202003101c00c0500c083c0d503074000c400030889a10920f02c0018640d1070300b4040340004603030141541c0310950312072401500c482ea101050450140b110301e100050303000140100c903080165074015525114150b2180c04120b101043c0c809969505c030408040c442d1024443e4900814500030700585602032880c259040600680c4050020b5005015801c4000187c10144d003032190103c42c542004801840f04404181c841190b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 512977140 1250 512975890 512975921
    0x19090e0907032001020c15090919061215110c01020c010212070302120106120608030c0f0c0303040303051c09060f150602010618200307020d0f030b1e04 67
    0x14030402540005504054074402c2c8254442c0d00b122080008090800f030300364074016030000b080001c03582009400f80500320050010306142903a54004194080815621030004900580080d02483d550b40f0441e000381c050494040442101d64072885010716070540800035486d0b031060138940c088400700885004101e0305000b99100c101e031600d018000d401c85810054940c404200003880c862092003250300d52800c40e9041b038456420300004849080d1300c0c1e00101000c99032000080744c1001d0800152480c10140c800030001d40280040c1d00c3e04100751224130354001e501c24071082c00001d4201d415603006400c042c605080d028200c000c14005410401409802680f8040718090a00402d0300519810310002003840380050366420304908032240d62003103410f02c1c00e40090398800200650850103201c11860b44d00000204140ca907050a94010b5a440d4090380c090088107e13002e8205a030107023604513908040042e03005200101d0004549451384154400c1c041c80d49a916503206d5115a0700d200780b450 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 512978390 1250 512977140 512977169
    0x30a0c030b07181d09010f0f0504050d02030a12090213090501050402090619050609030f0f030703090f0f052e05091504081f1b091502010902061909 65
    0x2000700d803207001514804001401040a80810a00d443d2030408890040507103001d072410740402540e080720064803090155486491180a00342c0340d003d85842c0282c2e114001506007000d01d042c91a005200884109540041c805090303020b801960b600103900500710302046000f558400a180241e41c80c0705031400300d26000c0d0b94030038860154082c0384254825940344849858410822180960210351117000384034031035003840305040100182c1508100036003280c06101c50141d00300e0415a040440d00d80590005c81c40c070003456800b11880000f010002d10b0313507a005060062141e1400f9490003018001c0c4d4045416510078400c0b0000c214040714500c1201418090364100140658802c10303007070b48204100c503401d040e40040c0710202e604541c45230004054406211105146283c100f04030180e84039900c0c07000281e645050340d00a1009121907076444141410003140800300307a611809901160b14204182005807107004c22240000280b15000b64190f50f91001203030464080d4100c0d4400b0b90202c03 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 512979640 1250 512978390 512978393
    0xf120607110f0d090608060a05060f0f0f0304211805100203120108011e0614012a060903110f0601032d140d0f09090209060c03030f0a05070c03080f06030a0c03 70
    0x5180344c070035503510382c1c0c0e845c10540300d19082080383c6c0824090250311900070007200c00c9010200d00102500c80003010220300b4286040030400a68000f01c0302518841240305000107a0181d00c0f000000b90f0003941130900344200c1a0030340e4503440409019560140211880ca6941030b8000c02c03ea813a41464100110140c0da12104e84c1c40c00381030b10a0004581404440b00070003405018041c510684255003110840d058605004546c1004084100c0303507446401d001005038808841c43c4107455038001c441c007151403155813900400788120320000c0c07041504215440e04402e075000c81e14904582e04041c401c1d4181808040c6420400c0c801c016406030b80003821030410030001c5002204040844140035546600365444003540c040d07403000e1002001401c8284107001c2d0348541c0e03025110316500604041c0c208003804210f10314542c8207551082000602d601081500c032442d0040c1503101041d032800d404881200e0350090305402000d048110329511460000d00c0c1520100030703002005401081030400940d69 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 512980890 1250 512979640 512979647
    0x80909130506061008151f05041e180c18030f0204051f1e0e0106120f0c1b02030a082101080102031b090d02040f0b0f120607110f0d 58
    0x155022100390082400151003880c000d8107904903404c042c2ca0310b0209036644045108681c0304224511703803101c10000b502d080356007050f403610007801907911020b540f10301b0801c45204d10002c0400b94030381401c4040d02405814102411829040b03020140840c4112081d182a50100d5244451610202c02c40c0000030038060b800c540e20001034025141004aa2210380342c15420b0107101c05000c403400f0303141e4800c02000c54030440c02d0004580c6c0b82400c00380e04d911144801c198450a83c4034400145181e110305002c142c1c2031080140d5900600401c04c4010b51500f0058460000300340e1056000000200b80000e546042c030034403103810b502c490459138400000c403d02c0503512511004104840b540e4002080b500014421203000c1c43e0003402c0550700d0300868010510b154042c00310a034102c05001d0001c001030711640100303982c2690155010030300003024030503c00c4840201c2443c0e80701e441d0000701c42d10b44182c0882c0040d0016940d161070b0941007a142e40b103034642011040400c915101d03101c0b007600050790 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 512982140 1250 512980890 512980921
    0x71a0d15171b030d0c03080a09060f0504031e23040e16090f0609050402030c0904060603020a1218020603060307150801170f060f18100509060c0c03070f080909 70
    0x9001d00c4910906200b10103059940c043d684011000ca04102090740c04a801108202c0d4000d8100c980400e42c400940e6840095070441c0c2080900540c9800a0000b0940c1102c5040300361008000075440110343c844008058410100721035206007001410040d0840d802070880d005401840c00c2c2070302c9130426851b140c6d41302241225641c00146d4442001c11038811140d0300d601151a141d40d001401824207007080f0007540b000e0b0004c1c2e5926810850160640c669020302e00042c101c0b900e0058039064020070103011003080e070711000d0780b081c60f100312003010000d002007040d0031030b40580794513480c0d940302004070340750180c0ea4010071042d940030003038100c0d2623500440e958107881c0398070740f01810a4070002005549118031000750119800000024a00b60440440e80c1c0e840405032080c44150311035010020b08108210804803d000c1d10f9070100085070600700079464000c40403240043c0342220402003d5100c0c0101100100404015000c810031b111303030803055800300d00008010660f83c0c24104401c140805 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 512983390 1250 512982140 512982163
    0x51003090206030c070201090e1b0a121503030206010f180b0402090a0b070204060f0b1b070b0d05100b03061008062b02030f06061c05101d071a0d1517 66
    0x2407a16102155002c80000321030300400440542c0d4904070324840a204ac6608444000810003516211100920406001e54010783c0a0104941e8049041d810000d0404a05800822184070b004000700400c100c100340050301c85074000780c000f522104bd940060068071902c50020385c070a0b2109004a811402e16008080d160320172241081400d503142c1e000a00010503100d0780c00d25000501020030503041c2c01c1d4481501c1d6644506403040d03140ca8880410454100780241d4950554690411142d02c240031034890181141d07103502e074154500400000d54248006c10242c003040780c0b81002c2902c588a0403035140301c01c8143c842690390850010f0304005031014001d0280d00c80e00c2150501444030102042c501d0088501034000c0640030304c0d80c0b0134600e0301c4510004c2281ca0384210544520440020700c1582c0c401e034004504002222205c0b800c551510382541c01840d02c10380b140320807203500ca0a1100301d03501a0106503021a01c512202c29815075612180d21415002d18000d003075401040d0041600326030314 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 512984640 1250 512983390 512983397
    0x105100506090a030c0f060f140f0c01140a0209010e0a08030a050c010e0706170a09031202070c08010e0601050a1413180f0503041a07110d0f050706030b0a090c09051003090206030c070201 82
    0x1500e141a027196032480c07080c1d0750000390104028904035840d030314005280941e1405c2c00800d0400d2170040350b03000c60340211801c00e20241d01207071b100259030344001003c01c007040444410000a003440000c13612842034404a206120000a4036180030f10290000c4401d48011025074406036a900e1001e40302c00d082503403420703400080708000fa40d00c00045c41411005a01552414604240160400e000b5845541c040e074420710100000030340070304d00340244101c242d07200340904201d500d0481030105001c07068100e0a8031164142c44807482d80c488030300840c811113824001150203042d204e040c613446200400c01900d10360301412a08240240007000f801101c641000030306298541c1e40c10064103010341e01c0020050302d400e40455000e40b400c42d41e07220f101e5004d100c050200d2500c540d10300345015140d90000300825103607030031901c0794549444800010480140f0512030090f0301c8100130107031802d60141600c29407008400041a51090f440079064581c0a0001c81da01e041c14460100310307400c191400c030b000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 512985890 1250 512984640 512984657
    0x50702070e10090f0c0206010603020c0304030c1403070506070305070807110619020d09031e030311030a0504060c05070b07031a030a060b090a020405090703020a2a060506030105100506090a030c0f06 87
    0x9044c40c803444807021803e50250040b079003404011000395002e940c2c1200244000e00000c008107100b5a004001070108500071040c4032000c40500d803e000c0380d948010310690043c861100800d40140407901140d50141000c1c0e610741da10700d80091940011003180350840404a10300e901d1840c00000b4040c0010950200d510320300c1401400c84040519000041140548071010455401302a6400004e03900c6410041190036250607a105640c00c211400311180b42c5410500090000074864a031400400e4a895494195141c17030702425030202800e00c1c0d04240d07031001859045084034840d0741e200f03000102038482c18103907410803801803d0209200c03403058901c00081070011a0900c00c0300c0403250b000d8072807049079803801c41c190001d4100703d12650078090304200c41d40f4032626000d904258181d04005604100d16541007802c00c503040108141e021760314100c24071403e91034000f003003400c0780d400b01c0e0520b6481007840003051815503168030051100c103840001040c00310742e4004841c103071440380c2d590304003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 512987140 1250 512985890 512985911
    0x7030e060612030f0d0b061603090501020303010323151e010f032609040f05010311092202011205070206072616030e0a03030605190b0d050702070e1009 67
    0x60394241c0b01014592a030081003007540b001000c0000d46242080840b0011743c207024000814003540c40040c481602c0c42d10f48400310101a0000a03070400b0303000a200071811581581e9585c0c0c44006000342114511410321140f41c4681c4080090048025000309000064189a140d02c0e081d040c0f035443c01d00c40c28030144008510784d1200e984d1300c005c8903001820400d105001c90610354118220b0500021f0102c0b0400c903110282e1994010080308105038100000c143d85103041841d10840c00e00c0c070403032095440005000f034039074039200d00b42c000101c02c136030440b2820024070060740c00c000e261400303040c031605050821039803e4001c140c05106203699180c1442c000b0100c1c90081d0142c0307280b0f2940d03007010354046c04207805512902400c1c0d501e00c000d003400294a2091044285000d0482a0450000e500d0303035418080740c280040310050489130104500c26203400e116059805014100174810300d250380f400041d00b6140b081100704010449000304c107400d41401046100708003040c1c06038231070306401d0803410304 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 512988390 1250 512987140 512987149
    0xb09100302120708061c200904020a050103180b0108010608070602030c0a0b10090e07050a080c1c0f0f060b150304050a1b0b040806011d011211031507030e0606 70
    0x555200b42000109840d40e502075041c0c0c1d980401420703241e041002044025201d180d030703562100c1018095141d04440050003040d80303404c10101080c00340940700c0708052000580360101c181c400d40c0c0b001d00f00415946100c1c071740e0501c400000c81d00685410b15400c000101044194082000d80700b004059400d0151902004e03aa41e11483d0481071480d80115844004603120f4441ca6070003004001c1612000c070f96924860302610220b0920080036000b0a03010001031520780110340007071074420081c00c0030348040000540407aa07070075004903c0c20340e290b41c060104400b4030686058913500c041543c204200394205003004000c40d940c1c031030082407011201620b205040c0c055038800c40d401001404080c08645e030b4114030a40c05100303003407001140400425007140600180000d0a01d40e4010446903140000748000c042d005018200c0c1d40d8414801400b110240b01100641d00760031a580440031480352002c645005004400c8904500210060180555154000c209495080c43c2207900545640c410070 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 512989640 1250 512988390 512988397
    0x20f0a090f050a0e0f0402010207030215091e0a0b0f16030c0b010504180f050a0501061202030c061e1c020d0501031109090718020d06060f08010902040b09130e070b09100302 76
    0x12084d000805001076094010b142d00103511501c10320640d8030300c5e42c1e217074049040f403944441d9882030800d0200c1c142486060005c104074100004c058410805d0385024040751400100f8006c040403244c0c00103240f103a07074610b101100c290340f6040455a0640580e800c0c028039060280d5021a00c504c0c03150000217451909004614940d503840080b11480b030120b40e00c84218100140701102c19003d09000600480c000f07104e100e004103020070322082104810305c101410a90440c480600c111002d001c094056078a070b01155541e490a801e00300d503100301214881c9003c217401d0650f0316040e4000a04011802c05030f40003a4104c9116420384000c2c4401074040000004085426840303e40c8680302c10803403504040c500030b550783c584002c0145043c080c0002103040e16840d8000c000403890b00c4051494890b88561103a00500e5090f81c11070030142000034511480c030603000828451050101d8055200b42d555001c03aa01d84181011980e0702d42d502d000c03a07542d640041306882c0c030483c400a401c0300700c1030090089 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 512990890 1250 512989640 512989649
    0x60106020709020a050a050702010e0901091e02070503120c0720041109130225140f030412020f130e010b011220070c0302090903190c0209041401020f0a090f050a 71
    0x25071b41082c800d540101c2e00c90300940400d9040000390400c1e01440c2d04c0b15150305000e40507541c80450700354500c06008010700c03400d0407a0840705204201c40400b01c0c0000c410794031400700114442c0c03081c1c1c960640a2403035001d410702c0645403902c4a103400c05500301d055165030b218181030300c040c0300d545c240208461403800307022910303604070601d0000b4201c19074a235401800e00388141c03102c806c1101060b4518240041a804040b0b0340c1d04001e05800058420401c1449100002300300194941402d007074607401c83c100c1d10344c0000e02403070607114001804c0e03803051074102488046520400200c4400480d25020f0074203028041d0110709117982104440405000d81200400c0482c5200c5d806000200812190b50000a00fa42d0390340c4070020200050369010300c1c4038040c1e182c86000756110b200c1108144000c2c003014101e0740501808101407001620390300f6141e60302a400203001804001034070f180c5806446040e200b48441c000008030380980e160015642c90039908409200c8036815224030a004180955014 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 512992140 1250 512990890 512990897
    0x10201060e0601210e030d060503120705151509040f030f11030a1202090a081f02090a060516050d0c0c1e050d030c0503040608090d0e01080c071a0405060106020709020a 74
    0x210754040880c0700344d03601014110000015002d0802600d050654200481d100c1c5a1034031080200030918040141041000b140a580f52600056955542d03481a114481030400d4003100d0000d50404842c00101a554030f0151801080e89060700c1c0803140c0f803c1c0650304030045103032035681458052141c0100032001081c580110300d49440d214042c5c500040070885203036000d4027004198200e4580c20445801040b0007401800407052900b64450343d4440c550004810303a00c140031140882d80e0304000c40381240c0d1982065a0788020050f60303241d00410308400588540704600c5000440c5a05c005100c4004c0e0080901110035515204004401500245400c20f2410b00b81c005003c545007002100c070b21188070f401d06c113041d640a503039030030f0554000d580403801046000d000c11003031000901c0100c501b10740b03c0c601141011a62400a01030060203031112569860204105c010071204071440d180c00305402d001404a8074161800964420003401804010f019984000501c175031540260b5502030207685 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 512993390 1250 512992140 512992157
    0x19030c0816030b0d020411030613090b0a05060111070605090f062a0f1b0a090207200607050a12030e0607021903030b040e160503030406140a03021c0209010201060e0601 74
    0xc4120b000c0c00503804215400841c40603180010b950f2480b69901307490000c5d821540b645009420042e51600b8101d186000e80e080209040004800414030b5030701c0403088070002034680706e1800403102844035900729000340c070441d403010030b0301c035003240c00342c55100011546001486508024007203140a030304050480010900389000ca1403500800007085c110002d01184c4071800108100751030700c82100c0d900312181d03054a5840c402410b00e08103101c090089001c0075842c00c40903588a0104405a4442d0450040c1c890012032850760b90701e00711303800590800304441075100d40d41400d030300300c1902d202e03d080824607110401d200c22401040462240760340ba00501558158030180411541a1020072800c0564507a200701150b5110b110340c400d20752200700200058990f580a400b41c4140a4110710302c290700034042000310342c2d0b0003030345004451740340c0300182d40b100e00b1a102540a03004140c900341d2803001e0340c0d0500d0510207041d8080c01046800368009d0003015540c40d10f80c1d580940c20743da840d00044020 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 512994640 1250 512993390 512993431
    0x40b120a02040507050f0301031202060f0c0307080601020705040903170603060606040b030a02040f1202103006090212102106051305070b04030c140604181119030c08 73
    0x40c0d200135070111442c2803961800d50242d0800200e81e00980007200c151001800c4018403030b50400486500030186c4007040303c2d030b0400506a0509000082280040100da600084d600f80d1092205200a04010340700740301c1d000c01890302610040e001c6001d003e68040d40d00015800780313030004e01c40c0d000d02401741c0306a140508040b03840704035078801003103c031045808020010f03031109041100c0c0010074440e550036030701c001140b040000c100d110200c000308111406c0301c0b5202300032180060000c16422404840780c4000303e03031402009001660302c5055a148040340b60f0002144916900340714101c10004904540d03115400350a801c00d8251120b01c9081d02d510076070b0300240d0550700c143d81008a600b00000b1900c00f540e10103140c070b50382d500915500300000c54104100900c900d04003000d8014030031590b5403a0b2404000c107696000301e01c1911194100205c1120000d40c0c07a502c911315001c1c0d421f800c1640c90200082003182000c60141da40b002078030b482d50041c0c00300e00c1010028000d5003800b8500b980022103 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 512995890 1250 512994640 512994649
    0x3070510050d090b04031d100e01112103010501200c04020f0909161b0f03140d05091627020319090606080c0d03020304150509060c01060302040b120a02 67
    0x2c5203442072942d03210300380380c0842d115001e20391044d440396030f54000f200c1d580440c4140345880c030860180554205004000200d41003e4420341a11f8203280c101e88000da81005a8901041480b00ea440700d01c0d50710418206105820055040e124281c0715075940503210b14804000a084510b0180c4580206c0c1031040f142c50603070000c2100d10744404d00d440c01e14141e6800500006400d0701d07040b42203040444048580e81d00a121000c030f030b50503400b00c00b040d4901d544401d000c1840840c001020010500b54400d84111110185c6401c580062810442460140c20341a070343c45468186041d03010090070005040e103111800d1500701c4900c2d004000a04043c1d0b401c540c0a0340000d80003080c03420810079001202c420070300c604103401b0f0003a1350116400d81751000c02c03400d000344e008509000710403002c0710302c000c683c000088404581807110b0400e1050300c0360000301c4460040900480e4050700005030b910014805411060550b40203d0702000f200100c442086249035107503600941a4100c00a52005071070b2 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 512997140 1250 512995890 512995897
    0x1b150309020609030d0f080a090201020709090c081203040b0f1909031b031205160c14070308030a09111219020d06050c070501144812060307051005 65
    0x800b500c1181090403074000a030400c48150000d03c002028918144030b0386a101d90560381010a0403402c01040c034881d00001d4642c805e9015042103162106403260402103201c119000821541c003d0396080007000140c070390361b6031056800352480d06040b001b0501d42080594960b02802c0910031301c8825039080d07003012010300205d6405a040c042d00c03008114081c0401c8484018251090350b6502c41c000301d03100d40c0000c94002400300541e01e1444007401541d95000310402c0c0c00250044489201030301e800d00e58500e0081307241c0000307044400c00b0081c4001c035500b50304003000306449420310703010f001044401c2c003151000c00445000c65922409030100c03c41c43c10140c01c070341c842c006407140e00c4804081c0c8030300042da013060303a20b00c40c0641d0020310102400001e03c130b20b503100801501c0e03849403400c1442d00980c1c5901400d0342e000b0105e42d0040c0b0032010083c0100b181a42ca1500080c0d6400b007030701112628030315008414150360b20030303903240025801d01c0c0105d100011303038500404012000c3c0d0110700c201c1d1140c0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 512998390 1250 512997140 512997143
    0x20f0c0d0b06220f110405090402090414010207081b06060924030607110d05030402090c0a1b03090503010e060c03010e0946050c102a1b150309 63
    0x46220302030303d1150f044a020200001c200b01004030b800c035800304040003200c003001080078003120180011711855980b2030820b5040b640481d5001d00b0742c0c0301c2c0e040204100c50300c0f1460100a6100044000800420038080c100100b194400c400c00407210200705600e406086411544c000305d8580061558070409000d058601c10140c68001000c1c210001b0a103010b105031010307404104020990300070b0640401540c0a074000d14a82581141002c7c1e011035201c0c4000741c0300c2003060401155802d410751094041c8588400c0d000e0118191007200c0c100540915000d008041c025420982c0c03003c500744001034040d0150959020b42da00c3e580c13a0207c0c21403001030203005405540198510400d4520100d11144e0041e032400c0c680e144005070301d84501c01c4802130f039160071640402130f40464002c200c0c00702d14105458003c0e00c0801078001c0c05201110000c400003218040c1174116413440e844240300c004006480c502c14152f0034181e00d176190f05445a034450b4840e4000e922964030604082c6886508803807440e5 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 512999640 1250 512998390 512998399
    0x902031c020c04050405061b0a090302060d02090d06090215040b030613110a0201020d0b120d030b1309080408190c030f1a01030b0a050a06050604050103020906040b0a080106020f0c0d0b06 82
    0x40c0c50400007025581c4c25507045d1b42c02e501840502001c1d061303043c151001c41440180d0507103803400101020300400e032240300207403003800e01044100c9000348540459100c0d03200144040b41464641c0f4100004021501c401c3c0d0081911040b40810010000101c80c01c1e1101d00c030302581541d4520041144201194041003009500c6510040d08802c84001034407507a00b923a000940c40c0c41284142104031108020030340d114020000780c1001402c1c0100300213140405038a400302d20320510501040c041d41029079252401c5103046060307000e00001c0e00240054903c6041964400691807101d06071807284c000000c0c0004021400820014803106010740c422885482001852505604050140315007640107888081c2c200d000c01c10201860b119450b4040d10109080102038182000300e042c6010354041d650526a002802c0c80c031340d80c0e84400380c40003081c440000760358072031212100910700d0301c081c818400984601407881110000104020700742d034201818140c0356214a40304e01007078050103441260403 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 513000890 1250 512999640 512999653
    0x2100509481206010e0712050606031f0e0c070506011401050909072a05211c090c030f0b0c03060d08071e120e030105100603020310150917010902031c02 67
    0x42e950034400d190013405104c0140d484d80c07904660180007000500c55007000c50703140c20f0802805940d80c0c0f054035000007200401c50114054070010107121076954000c003071680004810000054090001408494400d0f0155005640d950820448200c0000d00d02408a44144011040ca0910001e0a94000f08610300300700111040010b20b0010700d40460004100854003880700305020007003195010b01c04010b6003141c1f0791542030180311114084c4515842e5218284603010680407030300d410844116401c0b1003030021850762480d10071360b11200310f05c0071945160070100040d03012541f00b00342c030300c1210f010f40120354a04480da1405110352001c4030450313004012124800082260740303401c0c48468800c98040c54a24a130500182509120098072480380e0305013010801c41d150b1070030100c41111558200540c0340ccd2143c800c6200d00311140e400088660a13203e11001c4c240c0c0c0e0100180c0100c41e11b520f60001d050504084040c2a10100c40e0003a4142c0c2c09847d050071070b42d003000401c80460040c0d1043e21071 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 513002140 1250 513000890 513000919
    0x410a08090d1a04110f091504060302190306050105010503041709130e0d03051b09120712080a2a02090604020c011104080d050c07150210050948 63
    0x314828200c0300b00c462900348000c2200b045000c40c051020784000301c90300b4281503940780000d40e20840c0103084003080d100c04c4030740d00702640b00d9401540143d68010040b006d4896040f0359214069041d22040e66170a0903d0000241540144122402260000d640035003038842c000d450401e5030f0103100c1c556044505e070441400200030503c201a0702000d9007001d04402d08000000034103403540a8a86a0101007c442002406d45185c084030072800050300c190782d001044004c0035041406583c40325070102c1c180c0c004001004804401043c003c2c00c242c98030742400d44440700c8590812802e008a01c0c08840c80d5900201514018942c254031000060001d4505018040034a003074079102c8001d040320040104003844440c006001c1d034030602c56240b80c41c600300001e105000c0c0c1d039104a4410860204041c2c5d8050342158828032035068014034015050000d800e2100126641e1240d440c4c84100382c0889211514040b0300c3c003140341917800078075801900d100c90002036680c0751022403105154807540041c20000d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 513003390 1250 513002140 513002153
    0x40209180328020f03040b12041a0c07060608070302130e0c0a06030b0103140f0f0705190816020f100c050702030105040c1e030512090607410a08090d 66
    0x89241d004060030302c0c1c04600d490103490079200e1859400036030400c1c0814449170740c0d69000c1d02da40540d0002c3e0b451240c0c03903078140451441c03c1c078203400001035808020059a01c451100400c2091300c2031b0010003166988106440e2140507a000096000e030782110f003050480001d80204461078082001d441c90003d04000280d103980c1c4070392100000c02e031602c07940355030740d0b80503c541da4103103000d09128445481c00715242031b50014001e0940c0703040c260b10300209628604c11001e0343c0e11145180207040d9100f481420150000600b107407200384690180d03081075441480070648844018556000342280080520f2200c013500001c0e88200402901748026030260b6001d001d4240030710b00488464000d141024652500383d01c2e4641c0705c00c0416028181000007907400134845140700e111042260301c640740200091201c1c400c1e000050b00489403040340d0814441443c048140c031185001d200f40480c0e01c0b459114014030b8480d2409072680e0401113490000c2104a0024544500014461080c860740d554800 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 513004640 1250 513003390 513003427
    0x1103100e120d14040b1008121603050d050a0510050102030c060a0b030f060a020a0f09030c0e0408040e07020f10060807030f02040207080f070c060801050d03031a0a0608060a06080402091803 83
    0x107070b07030740c005d0042401b62290141c400302018010050150007a00441a9048560311603020402500c04030300b6203005c2418032510503500c8590090905001a01b072000d015400341c0000d035a00700d501510200b00040942c00003040300c1c030f13005204011b07001542d5181c1044004000841941360540507072107850208880c1030084522500f249040161a9071005000400b42c0c14009451020300c0400b030014008a090610701108071580f107400180190399a151210381030003294003c1d40050302c1c0005221407d034011400b002200400c000726501c816030f40e4015130903640a48540010703500040d000b440460b03680d089506031f10b80040e0015103004030503501c854240c4d1000c0c4260b42c0c2c100780461007008001451888000a210350301e0000459414080005d044121103400181450b543c0d200659803880d8000405070b141c403000303100e80764081e03035a5400b40011500300c9070203120f813903040c4010070400c0c003401c1214059a0081c0c25158160341c0c03144001402e11524201c981944824030047c3c82059140c07962 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 513005890 1250 513004640 513004643
    0x1171b0a03090501060b16110109150c030f181a0712080f070c1119050303030a020904060e0103211107060e010201050a05010e0c0904181103100e120d1404 68
    0x607600358107083c0f071421641c20b60000e10040004001d50041c2488065043c85550b811800002c02182000d00583c0e11890a9000e003207248640c490080c68280c100d1380000a941c02900c2e03400403a684810125202c00700c80d0100368558140c04018010a00002100c0498003000d102c001d00d40720858480300c0c0024508244c0000007041e80c0100906052202c441903007091b05414000c0c4508a20390b1103820340c0c2001d00c0214040c0b00d070f15481000409c180b810a900411019096030b0b56800c04403000c6000c0d50103c3c1809000302d0400d28000358030440b6100c240c2c1201c2d0821030202ca900e8031120304503085140c145102d4204100034110034169a0b0a1002ca4014055a150a46a051000c00290035541d004101080c01c904c0c1600421102c41d00c02d01080c0e01c030742d110314000e949404503000580240394003046c041c182d00c140d0060500b0481c1071349a0400d0030b4400c034120b6240040c03032400e6105031806030541040750b4100d01c001c4026420440050291000e20080104040011a1040700c0f00d8208640 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 513007140 1250 513005890 513005897
    0x3020312010f1502060601120b0607020a030c09110403053408010f050c0c0a140111030f04031e050405011404032405090a080f0711120d140901171b0a 66
    0x1010400610000c100f401020018005402c0c0c41c68028006401d103140080c1c01d00a250321000c84013001d5803620201c1d5080e0354000d0a00c00c203d03803a420452480c2c0010300503040a58900385041145518030780c00d85040726445001405d6035094410015007140d020a001e200e90318454101c0c11a0a40044c841001351014800000d44030b4424a07220060b100c01401c0c0305603c040030030449007580c03c08144580d4040d0020700c9404d1802140003130034010302c4124594151940d0200900002d02111680b280c060ba002c0d0382d4040c1007403d541100c8400d280718461401c003260007084104201d500684110303039000b40300102c040c10305989407aa4540d044c0d101d00074400002c41701c010303a2000e07a5684604c0342c01120740310041030911002e6441d001180700d00829032091a83c045101c8040000e004580c241700c031405403444030503081d006c0300c150752480b0062102010400907a1601c2000c1520401d4582d44c00d8140c0d02d41c11800100320082c1040500580031100c0d482d2640000d049555011000780300c903440d0f44e074 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 513008390 1250 513007140 513007169
    0x70e060403150207140109020109060e03031207020f0d2303010e070e0609040e0a1b0620010902030d0c0c0e0601050306040e0a0b0c09090c070b0414010b0d0f0308070806030d0c0302031201 82
    0x4001084ae01c250340121051100c0c0c040f22040795140001500e222032030b4402c2c0100719443d40b1200364a4140001c511741024401c91780a40c07226503010f0401c85c1307203600c605900c46840c118922408500d02090160409a00c280b07000680910312800750b403004a803010300a41e02d01140320000c90280c0d40c104814903d254405c41030340c0100003011001d5481c2241c4401015215810030310020050302e1100741e00f10060002d042801c407561800c0d132102a25650080480c1c804131202500902020312945007030b2a006c1c0b4120b00002c5c041807000380d40d48a080140d55240c070755500d10081200070121426031002c14461604050700142c0300c40e00090003188641f10f138580f0340c03610604000c01e58030000c00001300900c081c45403c00040d02d50503202d801035071141d51500d030540703416805401080c8410020358000050f003001d6041c420f070b0010030440350b4041c0c1e031070100ca079490407825200320b84140c450640560080e50303403880e1184511404c0d607116100e403050703a10b0414640c0941054038400e80015074101c1405 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 513009640 1250 513008390 513008393
    0x110313060f0e061303020301062c0c1207210608120d020405130e0d0e01020604021018260f0304032d08031005040c08010b0d0618062d031518050a0605070e060403150207140109 77
    0x40e80c036202c042c00390f8a052100d3f605001810b9118200c2c1d900491203440701084a2850007620340558002d008050310703004035019400d602001400f141d0484010300d0143c3c420007040c5600c40d1401281105060b001402c4c01e8850380c1c2808611440c8122072002c2281a06072501b00303c0ca03609008000300030a420103248111031207440704560440e2000f00145901c2040d032803600c1403003c0b0540781225003021104000f420810010740807070a00d04442240c01d125540c0107002c00c92158055402000c0b071a0f051118107031504184000c0340c0100540e07030042207203400104100c4050900408024818440200304c2070394540d01114140090003605c10043d03120f0509018102c180b07000d00c0c0d01c0000c9140080941c0c1d1620315114403c203034902000d00300c600090130300305540d201a040030f01c8138690414040700c9003a82d81070158aa15102c031081702d08900700703404034910314070841c00203024007002406580b0301883c5968006000b07800203c0309001e42d07024031010300800e6085010b62a0800103100206003120745 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 513010890 1250 513009640 513009677
    0x7060c020d080c0c2808040f030b01050907120b0109080a030e030609030f0703052107051b07080c0405061503100303110313060f0e061303020301062c0c1207 69
    0x43c070504400400740603113801c113070703001820b070f24a000444441c904250f4400c58a070350700500120054541500050005003802ca0042017100b02ca00801d400700c5c007070b629001004410181950880005107820880079603c039410303071025084a005040103d21250703100c00c600c1c1800f01c404000e902007841076092641504060101c15846900500690300c1c11600f511401134030701130300c0006001c00001044509902c19141022000300d40c141c003015803149410f03400100395a2018080c01d004080142c003445440c003001400005441104014040303180d1001c090000070030006140c540d002e03204180f10b00100c0201c000950041650b450030540c0e1609501f009007001d61911004002a4030410110451841c2d03075100301c00f90b40b05451710a109405200c01200c40010704014258051800660f0207807000614185c00200ca01c20341c002c1c03200702e565a410b0040b0740c8041d444c1881103034116000c048080c1c0c1c01101140d000486416250904090300a9841c032444200c0718040071840b0302c40ba140c6134410 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 513012140 1250 513010890 513010907
    0x8120a03150e01120602040b040e011502010b01020606010c0f20030706021207030815031f060b2a030c0d0504030c0b090a091107060e03040609051e0904020607060c020d 74
    0x400d15203070100e18104804a00000510540034980010004035007000003a8040b140184160b480d540e84031601e07400c0400701490f00b8801c80e0404e41d201821140390741c0c01801049882071050b00038010390703990903006581283c1c5541c0102d800084007403601000400c603c401d40b90090794054000c020200050615150038003039041003045d0350120102020400c500e03002c0b184803035858500402103441d009080340001204460711585070040d078015000745100111007030001c0415088c10300c0219960b0b00c0c0d00e2030502c5506210408180606001422000113095041c81c10f03401c44110780c500b01c0c00b074814500300503134400c0500009000082c10000d10842c046001e0141013680081d0303251a82110000d010121140b1814049986807403140e600035001c03509076a8071540044c0c1c02d1207000e1114940c1602c0358080d0207032070007142129401240710f08040b10300c010514040324035800045562002c000f101720707006104a0f80801d00700006800502d003405030310750041e41900103061107000510054194407 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 513013390 1250 513012140 513012161
    0x3081929011701080a060908070f0b0405010f06050d0809060f0d0906110f2a0f070f090b0109030b060d0c080303040209010b160b0c04080a1401060602030405060315040608120a03 78
    0x7030820300140700040300445e0b440111584070000003082005442c0c4005039004119004d4403140341080740c0000d100302d4502d024402d600c038034020080c400c400003900d01203407218001d454100e955103401d03100003030a14005010091004059a080c1b00300d807401000641c0c80f40c5400543d994071481c1c5102000064055844c440112244240c20031440e203084107414024007655400d00803440c246d004d07100b050614984015100101640c4c800610180942e545044c00d105605c0c40400520001803250043d200740c09401005a43e0300c6040d03403641d1280c40c0440006440b03580d0020030f0100041c002582221400024030402000d1030312450240100075014005078440e40312020208485282c40400d58035440c2c05a80c004019401500c816000446501450300508000e100305a0080c061200d09170075804404814002485080e8032800100d81380d0180d441059040720050011070404010612036084110000d04005400c03503a5010462405004924400900d0700005100b004180d160043d2400c04 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 513014640 1250 513013390 513013427
    0x50705011416050d0603080d0b090a060b070b07030e030301090f0e0d12020d110d020403050714061801030e010c0f0f0819110f0406081005030a0308192901 68
    0x1e1900c082d00b046140780c9400d80c1c1c010400001410181d00b00103a0124000d580c0200c0450345800038941c11500421007030301024819121540007131891822800380000707646020380400d081226170750307860f81d03003040203000392081c552601c103c450080d004101450080640c2c840100e0b0882c40c106d4030008458860165400c0c0c0e0300100e050a8031705410201940c94030ac441d10005a03180d203040308010040c40f15841543c41e2500008210b104010303213801034815603020700140c03204583d5a25090580b100ca083d01d0701e401581c1400444010148005400340700d80741030601045400409070341c0c60031664410000c002082c030090713012106a03030010075a0b1402013581851485c505020780310742008001c0440740c009054840040c84014085c1e08240c80809242d02005a11141c8480000e8135000007240c402c10f098594003c00140307845c00041c0550015010f86807052031b5241c1124000c030a407510003136050070f5a1103803404020f11411a00d44000320040c0140110740b007030b4420004000701884421503510 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 513015890 1250 513014640 513014681
    0x1806060306062103070f0606050303040e060d030e060304050a031b0302101505180609060d1104050403020708030d020301140a0503120d06170a05010b010503270f010c05070501 77
    0x40c0d00d002884940282084030240c000c040941d1800f1000140d4284100080c0404280282040020048441c00d2441004144401516907051540c0c81c0540d02c5101812280da0020030b55a041c51225613071414024600040b4a503e20f0b40072448a910075102194590b00c00b10818080c1a40941d40b0140250305401000e80b84000e40ca0080d0b881c034a01407944465642c0c0e040300124198640807640043c0000f40c42c243d00100c02c038100744185402100c10034002c60346480011010b140840c01c0360f60581d031080d42650382039180400d020040c8802001103080d8400e03260003285405082014100d03103107413490007507900d40c103025440c1c00b030000c0f135480309000c1c28010905020696002c44c1d49410741c18034502541d200d02c031050411001d007505a2104600c40e83d040d0113119014004a60010100d000384000d00125840348011201840200d80c840c0003602e250411001310801245124040c1d007203001102d0348030383e08044150071a07551505090115038005115000c105080c015600f014284000b000b45 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 513017140 1250 513015890 513015901
    0x106052101050a03031107050a1502010e0a0b0a0207020f09090a0611130e0a091505010e07110709331e0e180307051b130b0a05220e061806 61
    0x1240c3c05940001014410740c00210706c44007038200f28000c000c210003030200c0e200340c3e40c61030070218107500e11494000650074410140070b0503c0c0040c160503043e43c4050702c00c1042d52a20043e200940220300308a85c8640c031924000f12590703400d41703c03c0c083c1400310058090820306180800c01c0b10314051040b14038103020303c490000c00c1c002401c4501101c9900d05149000d98501d8846002040290001003a0b9040251022082d002d80d91105050310341240008509032201ca9041d944440a120b85405c0c90f40010014001040783d07802c006440b8040100c01100c2d4981e102c045030800000710300048882140b2242040340c0000b8901c0f07110219880940c90428504040e540400a00010040714901d840e8030a19500b0160400848100c9500001600c1703d081000300009040e20380a0340322413003000c8104c1540514003640c4a00d101c0100010a124082d518210a120252800403c01d10f00710078400da211100c0c08550050001924113900509481e20b0070300399240c5001d14001c1c0101c0194420b804110 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 513018390 1250 513017140 513017149
    0x518221406031e070b070b150913031d0d05010e070e10030605060117070801061d01020303060409020406030f0f02040507031a2101020c01050a061d01030308090102090603010605210105 81
    0x2400e0010140c0444446040d801345402c03c03a0b8482044090700040b240c1c00d0000b0480703954052520901c3e60704412000c0320800c441000181c3d6030003103040608402c800020b020f810610000d95004403450070744003020001902c4050030250540b09a5144c030560780041c00184507081c00ba102800d05140c0c1d900b000c51071661118418000182403d9841c00400c0c1da503809424180e40d1084602c980741d2180c507220500410340c41088c400c010104e10301000c1c00e0705128140e4030155100c881a8011400e503600c48081101401804070142d801a542d04e07008804035040307100014005024801032409100584180002c5610040504003018540b101100741030340d002c0c50304c0b04550342c110f8160300c0c00e103000d980041c0c1c282c80205003d14190b00c0081d461414410642243c0e03ca1083c00c3d9080007125031390380c00b0a40040f402ca102000d002011030040c00001e0158010f940c0001030400014184070704940800e607154808e8000c0c1c408900041000300901d0b2409081d812030015941000c1040c1d4540030100e03 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 513019640 1250 513018390 513018403
    0x12070309030f031205070513060e01050f1b070e04030914060304320a1401060602061603141315060b18040e0109081b1606051822140603 60
    0x405a03042c24410409140c07061940c1805080c00007800c20450401410151240c3c0c403188510301b004c00f103540005891405a41500c9440c041030b100c00389440b440705070850040d07200300b0070f030207642000d6030041d031078090304122900c0030301a02e0803146032600302401c000d00362540a51001c441c4e02d41600c052480c43d181d080649402c168440086100401220703d250b4007001c841408072a1002014100c07080e0000010310310b21600e0080042d60780440b0740445d0350382690001d018010140e4042004940c6024030381181324046201403900084c050b24070910916003180580b140c4600a01000d420014070200e8070411500b1070882208001c030524140e007071540c0c2c1c064180394140d9006401d56002068031242c000b0288082d0000003000f03602110300e0310480c69084020126100f40346035202c200341032400100e441030101c40c01c0740020303914985502260258003203260009180644110b803240c0d501da810150015440001008030700382c5400d54400d085486c600c1c5521000c9044005000c415140400c0f01d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 513020890 1250 513019640 513019643
    0x30f0f07021209041d10110304020f090c0706060605120a09030804020625080703080601020a0c0b03040218090a02100c0b0c030618010605090a12080a20010e0f1207030903 75
    0x42603d4440000000e0b000380601c8500034440e0040b591540b07602c80c00481c21807941001000100155a25040201242e000456000b9000304441d101b1800c2480c1070020380e540b04e00c05181c110700d4005a5901c00c400d48200d80c0c0301d5008540c0100f01e0b40f4190b840a02020340c0014901810004070006880c000c2403c04081e01c044d01540d400145c0c07000c007900706d06030705500d40707070291907054010480c4c5000c0100e03038000a000d8000502580c01b11701c41d0b600c080f41143c9450340050759100280d04101030700318582d001070000c0b41c3c0041294902d04d0100150380006200301050000381821452078010700100450860a10013004110407a200000b05280035041c3c00c0148155210703185d50310480491400040c0c0c003940d489039000e0100003c3d6007a48030340209414502a900c044106540d880d201c00c0b101c0d04800010f11480742070049182080c440e0002d02081d08020348400e10011201048508581c2c040100c1c0445070044016402444000c10100e41000204c052a601e40070365902e00074240c40c5103000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 513022140 1250 513020890 513020923
    0x50f0102061807050a0821090a0303030c031b020114070302030910090618081e090d111f360324020406050408011b120905070803040803030f0f0702 65
    0x982c204040298002130100604030b07204241d200e02c6c58580d030785000c003610104c041104c045c4151582d205000d17503807001d80161030385c05401d08694095000d002a074110f003041694503842c201d0303440c906030310780325902c0d07416000019403501c612160103040c80022301040c2898010001d01c408284001010b400317882c1202c3c0c00107401c246510780031018050030741411b484480c140c01c0f4003090091600013858011103020100e0301a8903034510b0000d01d4011010313440c1d4842e00030313482c0740c010480508041c0202040140460034441c07984d03250240c0522404c4140001038652261801004481009201031000040703218a103080c0d804c2400480015030300006006505d20780706002d1450940301c06001e00b411081c0d00350749840d01e5420081158209105002c02076080010300720301d03450000407806101030b5580e03c44106402980345600500b12702c542c00c41c1c8901c50742200190403d403d10240c0060b06120001e95030300d0500d240310001d01ca60240044951000c8001031013081a000240000031060202 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 513023390 1250 513022140 513022171
    0x4020f010f020f2517030f0d0b040f0203160e3102030a090c0b130317040b070b0a0b030706090501030c03020d09030e030f0a080d1a03101401050f010206 67
    0x5000b01e04200c0714003c9a2482d00c964000d030f00c282c6100b41d82c0c910510401c03145420f1220368461909130b007a2800007040d050f64008000c0004c0da4021200202160703480c40b0320105da1043c185e4007140403603040300c10407052a83c1c048140300501c0e2200038003410103c03061030414803084003440020b46902142c2d010022a007010707110001c1d1401820b03a2180303454585502152070789004044c020180c8104201180e49508006010032415941c0d4299210344000c001c21451146c2160341e56007505848128046221605000001e02c00801c403005049241c8100c100c4e52450602d50300d00010340e01c1401226200b85c010240500c801c561101941c01202c40910700414001c08150068000748540091000c4281c144041c030001d05030440b4a801c14150150300b110a80000d8600c40c0c0d03143c4000c0342008000620400100640030a0b0341c001410034108d415004498110040c0001d1811503a0000846c02e103444100311581c1c0340311300101c03600528050300c42108290302140000e440b008018135001c0100d0906 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 513024640 1250 513023390 513023417
    0xb070809040b120a05010b0102070e040302100c18030606030b010506520201020d03020406090521190b0702060103150e010603080f0c0106080a120f021609060501110604020f01 77
    0x1091014045600d40c0035030340c1544c0742c3d081050203089044070050161040c2100000c8200320311903810b10558140d405084412400c8a650024156a0081e13108001e50070240e02031001031144240c0041d4441c600016040e4554a82507965010503845144995001d000001841003803110a0018000303031b20444045403412800d40000160004c4072108141e0700d00000d07820008040342c03800700c0c24002d0f0201c84005c282c143c4101d099120310301403000010400d410820460a02d40780c0e40d6804d04002c0d600d000b055500301b00c45440d140040c9000c0130080e010074000c40a010354141140d800401ca4400b800496043d512800484c244450b00e40e902c1e60f079159092200a6000e500c12070146920a51030340d520700d00718218a1040e00030b21000a071359440c4c0340c00000d0013a0005000444a036020042000d0002c0c1c1c0041545d454600503191019400b0b52210010400c02040104001d0306400c2400616941090001006c1000301410750600d03511403018040943e0740c298880e900080e09181c22220b40105 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 513025890 1250 513024640 513024649
    0x6040813080109120815031b0a08031207090603020403050a020f131b0f03140601030518070b071103010506090f0c04050303071101031b05030712020f120108070b070809040b 76
    0xd55004140c594030784556401080101c1c0c1c03003480b0a030f000d075550200d9a210708880400b0815840c0340264103a00c207070b040316052200c02c001e00550b0900284001042c9650341c842c6070071948803600d5902420010000c2018240e048030b41000600154075045050070b0950345e9803a610080c0e00307400791040e02440c0b0184c8071503603000f910310a0078540c4030040c014a0300c01e461581591528601c4100815080072240450705e10a1141041c483ca0420044186448090056001784000707800c1544184409a43c000740720350401c2010001d00b20b20081581d80d6000d1f007881c034940610401458881e904001c24410f40d5a2486c4490307070031440ca04154120b58031400e00700d09440c880c5a00243e05400041940c13400d1087e803000001c0c2081003030300d0034081340c5d94a084a040b00310003d0104400f1503070520100f04a03d106d005103285006410f84010315050341401c060180350450030441c10309880500c014406000140720304001456034812440c18004aa69003100c030f03009424181e40642c2d924106a00503565 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 513027140 1250 513025890 513025927
    0x906070501020c0c0f101205070203041d040512030106050714030408150604050f06010f0806011701120311010b030c13231501020a030f0305070e03070b0a02120c060408 74
    0x40c02030085644640125a454440e030080c880c2c280708601c4005030b000241000c2d20140d0980c0d015030354140314142d160121100070080900407004510081c030000c50000d013032002c1c920418000075070301c0d0280e160502d0902c1c60100a11185203c07214188010017680da04a0306613205c19a10490745005006115101c1307280d40111707400854140308030003894007903820307164120b401060103450501c500c0e0b80e21110000d0241003a0b400500140403400003031b0b2150b00c140a01c6810240500d00085603035500520058440d0007030308401d90034107030040c0385410140c00584500c010724038140240200b11006000a03110501c0e12074403801b1b204400706480e80210b030381e40006440c0c9140d0440303510b40c035035a10b11110200030440310085200846442c205441d80009041030700164540e0f500c9000381c180100c118060034000d41148107210b10380203640300700ea03018007a803409440b20101c229100c81c0601e000910300110405a180c280c5000c02c001d559a0311b0202d841503100c0d170440e2042e03070f03600124500020040e2 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 513028390 1250 513027140 513027143
    0x20a050136050f0f06040b07060b10030c0219230309030a0302070602070b040b04090f0e0d110705011407140a0512120a050f06010813020d0f0c0611070902090607 71
    0x7551841031291008100d41c4a8003694000d07909003100406100500510304040c000084c0d0000e800d0204004201c03104e0000c0250b18030411000c5040250000801c285515030000312010075110495a00d10b40c0d410003840c0014800c01044c00d107140510348910310b8041c8281101420303190030000203003ea0104208071501030001504031450b051144c24020b45030680e5001d22801401140c0000920601c200c040d10144d40e002204503107802d117007258a400800700c000350104107549031001404003500520008441344610346075016280000403085040522541009041c05200c5043c0c440c1070612405a4000644c021490a90184000c02107403500542d020000c0191180407801c142c0010f5010140041c102640725203030365901d0b40c5d807682d800e80b001110040f0750b0400310000503c90307601c0307080d40d60380141e0352078100c0c8119807494010070080da007108070646502c031070a150300c000c03c140c00a5810003440c892416002c2589405009522034940d446201240e6030086642203881ea1200c0c00c480459 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 513029640 1250 513028390 513028457
    0x19060302030703150b0408070e0c030a020711041a040b0a180905160f030c17190c1d090712120f120203090c010e03010b01050715021614100207020a0501 67
    0xc541e81c0342c1d1a030b5070780d22070700400c6080c2c0035a234400522841c00a41304c50107040000d1166045542c2d040083d0000d400402040d240400c4001c1500d08544442c4516003042a040405d1081c107034070001480b09562090210328040d8034107210410400743d003800203800b20864144040f51040c0c01e0b0800e00d1815405820382c11042c2140036001030b880b04824030b8001140d10456104001c070345d481e080345422000748030345e264460700032911000c0c0145507000c42e06c0b13030284688200c02682d9103e003003600e45564205441e44070842c4400c10320440010400c03821000345130040e03903515014039035a21100c403003510746141030a00c90401520030400340924843c60760f0003520402107480e454038911580c1d468070b0540303155003c030704504620145401c043c0a0840320540684a440c5403038050307130795810105042c0c2c05086520745d0034000d42c100d18500c107144c544050300400c0040c43d4010081c0029041c140c140c1421102540b0400c5010010707120008100100c58003420301c040c81c40014898036200461781600d100c3ca0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 513030890 1250 513029640 513029681
    0xa060e07090204080610050301150303050a0201150803040816060504270f06090510050901140109030c0603020309060f040203060106050904090f03020d020c0105030f0c07030c0803090a1119060302030703 89
    0x13450b0004960b0704c030380c0c40c000f0240c110540d514103050032211800c007094429003a180742480804c1c051001420a801e440c400014003024003150800c43c4e4165801443d141d400c0001e04020180003040010300e002e01007400c00707160707518200c4050300d680b003184189035940b58004401907140115043d800600800c4040c144644a101da030080002d00c5c0902401007010702d0f000100346c40660700030a403420b583e4083e1961701140d00307140d04103104140002da01ea04014403000c0200015841c0010b0b100103110640300941c42e414611802c03402c2120040c0300c0e0501d03a0f078503401c100140c0e8000480504450b03041c02c0c0b00790344a000c800803e01801c09020080c02c024085400c03401095400610400021156420359041e090b02c0801101c10784410303a44d1400003900d0740d0226940c40142001454024030904042060000031380c0c1e4281c41c0c1d082200c082d00f468000e003204000307000368048144031100040f03480140380c401921010704e580042d401003100301580400001d031502d0003580018400d20071515080078 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 513032140 1250 513030890 513030899
    0x27060703090606060c020f0f040b06070f1406090705010518061603020606061309053705010b07030507031d360103170309070e0109020a0f0e030a060e07090204 70
    0x41c2940380411140c0a103440c000080040c07154a8140340e069000b4680d13408a03004031b08126640704402a0594042e64a6040200075603c030030041c04018818400c080ca800c00d5070410085e448644106001ca9402240400c4460000800c0d800c040c0c480900b4083d44404003400c050454051740e800321038200d00001440c800ca1002269280c20fa41c1c401d80c04c8540c10303a604002c0c4541c03405000000080044a59402c0c00241401d800141d07210281080300d111004817803000e00c0703585a0140da8040280005141d02071710312413501440d40506503502c00a45401a140da005149224640f8050308000c4140710f20075242c0c1c0400b43c04010340390018460b411030226182e0800910805050101140903444132640314101c0c4030000b507040340c0d040700721001541d00386032460103240e1004148052074043d0103030101ea0510803450300c0b4080e0102000050701c950001c900603201040e10181d01060042408909045079800100321900ca0392040700810380544441c1014500340701c40d0400e2100c680041808103 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 513033390 1250 513032140 513032147
    0xd0606050d0605190b0c010e030a0804060e030307080a0b010c0204060f1805161d041d1528110a02160b04081b030c1e010207090e06270607 61
    0x408941d50680401c00719948808000c9410484a6a54440302c99003000300506012800901502e01c1103800100716100744009003803d542c132101294001c41c502000784818043e02d17200d50110000c1c410021895828030103070252418000500d5003122a880e00c1c203500191b4411000d02500c0307503000d40103011180d1500a42000701c0341501508070515900c0b83c084541e00c1c410b00070280a08540181440e140016620845900c52440c8120501c00400c14110502e51114400c1104041c0404204005110328600d414100344111f80d1249082c1ca100d010711003c8111180b55006414680700d001080003141c21502010f0564111002d50200011904a4440350082500c40c4250019000071032425101c000260b05401203015580d0035601c0131004c220852418881c01100328002000c40303004148000025a05d901406a031001f201c2d40409481c100d543c040009101400c1600390034407803200f0b403114070750b5200c50080252030001506004d4081805075440e4017400540e40000341e804515081c01e019 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 513034640 1250 513033390 513033397
    0x909070e030f0f1002040b0702010e0a0e040c030b07020c0117100f09060e010f120f0609020402070302010603120e01080c09041b2d0c1b08031605010606031107080a050d060605 77
    0x107500c3c5024910580a50010910071102680c070710a58079800c0c200d481e001195500080040d07150001c259110114070b4035160340243c1c0c4030f94821407110380c5182c00c41c944640c41880161040080d9449800c4109081ea000b541c1e144050706030b80d010364500d5a6695404521001d40d60001e424015030a40104031801650003d01c16154a00840786999a840354040c1c1e03619823034812036202c0188101c02d2000290388036800000203010b00c2003c90381c9045500001c089074418641100581e5407000108100406100000031002d41800c107200241410400684440001070100c2d00240000a10b41107079a10781c0d11140b80c0d07a51881c03004ad05400300e0b00001d0312640c503000d803036511800c0c108900003082e0003640c11881c04651581d200e03500101181e031a02c800c1c0003564855480410800e2001c603008004202034090031140c8054002d088000d03082041c212648c0360052410142011542d40c7d1102104c011078902544c4820866590440f0190450306401101146e0116500b45440007450940c041d000c0c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 513035890 1250 513034640 513034663
    0x220e0c1201020910080c0d0213050618090114060403060b040f0203101701061508070e0319140316021309020a0b070201032307050a03060510031b050408030909070e030f 74
    0x40c00c0c01308005a0b816220014202d50003540310008101d500813162440c3c000c1d20000c40c000480d00502a2100700140c030a8100684c0741600002c6450b445c0100e18000b8400c5004121640400d0700b6081404081000c0b03110314000a403405846190703060031915154015800802410021901c0342800c3c0b4014442006500c1031500031901c0340c00c43c00c07c0303141c18032a40f4125400050b503403465016044050b15a02e000804900601c1241050410b040e2010f11000c100030203c00b0705031511180c54502944c4000441c00c07101c0450340f0520a0382c915039255150760540300d4049454ae083e9481c00003a500107403084a9000350021070107c800110758401130701074407406100f624188081e000c0501b98100a4400e0300200c07a003000b00c0e40c0411102c600a000401304601c01d46404241c20341c484e00410b050a0b07044506000080d9509900b04003803004c07043d041d61500207854203600c1c0500c1c1c0480740d5964002c540103144075070441800f143c00e1502420100c0000b0344007905603000300c1840810381e07071550345c00c068 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 513037140 1250 513035890 513035899
    0x7180209100503060102030d0911090906011e0b041a210103030f05030610050a0504091416021c050d06081009050606032805210d0605220e0c12010209 66
    0x2280107a500540c1030368410001a401981420050303236289015054428003078900c2c0c40e1400c040c00480d1a50408584203030151401071405502d04820b24002c0b081101c0350303945040220b0810b205401c90b0100702d6088401403800e40307200c0c41085121000c1803140803840300c4007200c8010341005000c1c13201c18490407240070b500c403040d1081c1007000c02d03600c0748421901c49034040c050b601d803010140d0184000e442020464a8160300301a1140d03c00c2080312060304c034210740c60310f5810804c180c20f80c00000b8040d4005030303440070700ba5420760ba100901c2c0d16074513070030300d00248400032544200c2901d080e032007000105618000c60f40e100c0100c280440082c9200c40050700c55004a100041940c28001104245a82c4a01e84c4011448040b403851000c2c0030105401c903410700a0780950720a03442d03948070b10754a40d010040280c1d03a408100e41454125840c6600660080007a000c8079801501211100040c0b01000c0c040400d04400c800102c505000e8941c1406510494450a501821105502030b24050784250b4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 513038390 1250 513037140 513037159
    0x4050c0402041503051510031a030a0305040902070501021c0c18060c0201121d06101d06010c021801120506060603151002010e34061b0507180209 64
    0x9040c8001e078400ca0040c6000c010740140074842c1c06102c5c0d40b205601260000c1000e0881c440b41d070005000000241e00000060386801c0611b90508103070940b000b16150460042400001565002e0807a00440c418200400c0c0d0200b090010302a0a40491315000c2d455038803c440c44910383d603403000500032160081e000a10400b050000c1c80500c09440054901903112141e032241c0650045425008080040920944a50314004104900c82c102040d041e503400c06801c00303203401100300d080581c1c168010001c41e515003101c28049244c040140703400110a02e01585004170600224442c600c4550b16140d544a01000000d1066011302d024804544941c003600c20a4640c0b07000c01080d40010b0750300d00400c1150145405980c540340c1c80e1400305400030f0001180769081e9420080c10700b5400c00c4007004034180c05201844c1604582c0300904100070884107440c015007888c0005007a48000000110003040b00d62510060140400000c00140300c80d00e03410307400408042c41e40010750800c0d80540e00800004 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 513039640 1250 513038390 513038413
    0xc080d020721211a0910051201051012081b0c0f03210702031501090507030c031b0305070207120f0c080a0f2d0b010e10060903140c060c060405 63
    0x1070b42e040c0300f41c8440d80d02804081c0c0400080c00028182d154041c031100d010340c20840c070f040c2c0b05c0303001c0315200e0562055900051442c0405014080c0c6940442030189d0b45004100b051041ca55039120b4103403689407401440c034400d180307007546c4184160020b01c0a0071001d5018450004000940164a400140d03443c3c89400c2d17070b410038580d403140c201e41c10309003001000b000c480c161100d250203008000d00050443d09055000b030861050806c0a81010103510303119400c120485403d03000d560b183d40e8091404000c101c07110b840c00b07035842c0245a240f2081580f1031001c101880e20800400700549960740d410007e5180f14504140341850006048a1181403104009880c080108000c003281d9004000311014148941d216074003034190b4240010b1000f10751807940d40d00413003d0001c1602510508250146505200707481400a4009106c08040048607038240038455001424400720b0b03a00082041c0319141c2a40400c0c140000d80001c0c85c1c0221003c6042500a00b00098480c000c4d0300583c161620010003 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 513040890 1250 513039640 513039647
    0x10b010908031323060705030901090e0f06090402040f0c0206010513050c0a05070812011403070801110d020c0f0a0f031b08040b0c0c06030a02070b06030115060c080d020721 76
    0x4488500c0e03c40e1501802c2008603c0c0c0b481c0141039140b90a60301d840d01011580000380068010440c143c030b40d40e101107110300c00c550704103a00d00301034804200d0a244914107109040001140248400d007c0c4c01c80070701040854407241c010100c006003958007442001e2540c54001d681e11000d22445105940d403094003081390310a80305203405086840760b814038000320782c042a20990b0007040100c403060000c0000e007510180c006009030103070220011458003203503000b04142c5800100e03001400c030760740f4103410300c0c090300112022640d01002e1900701585685015942c41d040c02c0c0402444002070280004034030820050301c401440c0780d4403035140d400801c0b4200300c100140050404004224080800c001e02c20748040758041c1c9042c6c5805012508143d0f4000c012445a400540d1040c800030303004070b0707524200302211101c543c1c0724000b540200903410000800c602c51268504c100f00500c68508400d4040c8854501219a0b0061841d029035884d0b80c64a801504540d070740141802008600e842c18904a20 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 513042140 1250 513040890 513040897
    0x609020d0b072610030305031008010c110c040618090f05010509030304030807210905100603150b040908041401021905070f051c0305030a0b0307031b1d240402030405010b01090803 79
    0x44429104605d0641e80c09840303031360000d08100b51b456590200054014401d018280802510b41d9403442500e038205016403170f0041c42030a80d440307141483d0007030206030b000906c07141030803440007008151866142802c20000c3d40d520b41c0070307000d035080408200e0304080010065004900c42e83e0b895030070350b90b0345808079201c490313201450124100900594106d406690000081c4501403015601c4940c1e04001e00c1701142c505038002c48115a22910704071030702000340300d0f41c5101d100554007031010300015078400819120300c0c02480c9170568900000e02c01039200b00038805a0070f28030300710301190548900b409a5298031920804409445070b01011803507007400301900042002440e45628218550340e002d41381500010310300000c1c265540700c00b4100781d0302040310340700035030003a030309004c1c00c0300c41c408001c2e0390324140e401c45100110b01c070241310b14021103800601e90040301030790310398003218000b80300d1140c9540145401703034490b001000740001c8c4401940b04c400c000c0c07004d8a03808286956030b0065a141d00 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 513043390 1250 513042140 513042151
    0x8030705030d15081b0406080708060604150510031b0e010804060c030b060403141005090d050906040b030114090a051003030e0a0510021e16030609020d0b0726 70
    0x20001d0080444420241c3c2002600e02c0c84041c203084041c1e01c8200251416510308000d10302404180700002d102d051070f1107084084c1c144000036120305800c10400d0307650b885c4042c10880c0901c1d5a252400303048022080f0300c0024000042c8114a40e20010324001d0240003c2105032114522600e1141c0e9814010080c0503119503068645100315515a2071300070090802d4010041131503100c8414000c69500c480040018512603103420398000840000715291101078401344205600d8601440500f64000858903680005850b0981d80d410301e15001c600d441c0039680c000d2910301c00110000c1400020a42401060318003a1549241030755406484410340300b0a8440c11640008400180b01081c42228924403542d400f80681004641e104041000c0120300c40b00701d001a0000b045042c800704003d048468880c0000004010025200026065070407251000070300c0349948a45000454540041d14035000790040310050701c2d0318120a01605c8103081c24000c107c04c0c01c5400d641040c81c00011501401103 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 513044640 1250 513043390 513043393
    0x30609010302060d0902040c0f0206010f050a0e150409080702010f0201090201050d0c03020403170a14030403171f080303010f060507110909030f0423061c0b01030902030709020406080108030705 85
    0x180d185400f80031440c0e00024504442c1c98070b0756801e070056181ea000e41e901860711540d5002401d85035090007400c020040e00a003540c510041800c01c03540d5541c0c10704000b603407900d5031507940948403921034540160316148031681107400e01c05d2404c14440d2500140c100903000317881d50510900c05c1c1100720300300d802da004000d0118800f440f10408030300e8076500942024850341001481c0c19182d481c3c4e06407c0c00320101403a000240000c07a41c00041c1d0210006c0c100030305289005045080554014080b03400d00407000d0f80e4803030000000303000400c0b003480900307a01083c00d032040328180d100c0c403495869500901864081d113042da00000707059885081102e00880d0001c00c41c0d00b503440c1c2c01301041092003001c0d202a400c0d120500c42c289a0307030101e0008100a0034110202880c404103040200ba40c0c031040e1000d80d12402042c0041c6640138100c03480400b450102e48030024002002c800140d00074500709202030b40600c80c01201160315803040d801401036812a449440817682d031100c07015a04d200b41040207009 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 513045890 1250 513044640 513044659
    0xe01060e010f2f010f020d06080c0604031703070c08130806010501020d090312180f06020d05091e13020f12090304050a090203061302030a0507110c0d02010513270b060306 75
    0x103040142c00c007000d5a0700380c4000b085c1d8041c40d0040c64281d070004001400120b5071007108000c0b4410820412880203070644819091030302d5031315106400068510b52904a51000000600d4984603403154226550301040c0d080d02d1b000c1140c40180301c000640070b5040d00c1d00c02c941c0045038a42c00001d500d100a0860b564007a4454150b03038901c6004524100f1040074021a00d01c4403d000e403901241d0800350402c260b0407540646801c400070302d0100c030b2070840414031508101d4114681c44440d900200124001005a00320b02030b8004a64000100802c41c15130390b2000c5041111f01c0c150500030301d06120000d010001e1038603042d0340c05490348120711032540d0043d0381100401811039180c015580c4181c0c001c00b005e010317104049a000607a801101c0e0f00244580ea81c0400c480340750460004c040300d03419003006101140c4600003007964240000390180c144200401c40c2844903140c40c25501c0540503440008644450144030400010072006070415400d08080c3c20000700e00301401030301d1051130700410f80d060 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 513047140 1250 513045890 513045947
    0x306010b160c050303210a0b011e17131115030106180503071404050708090d050d1805010518011505060708070c0f1403060114190e01060e010f 63
    0x15141c07100001102d12890301800090b042d58240003500103282c00340e02c80d862010400d0184d42d450b090042c071480c081807410500c00200e90b440f00d40417a0b015a111350b8024801100001a104801900c4515031054400c07420001040c001901a4268030b1103050031030540711000007080b4030002201e9881480e50300c00c0c80100b006910076045500c4007641084a00021a22a80840e0501c0819085109030700c0d0050206402c07030415104980d405102440d081c4c01604160040e55164014280400100080400d9071000318180c1d60014901291000d54085405041d29040340a05021108141040200217035964001d0b810f00074051190302d583e0501800034100010080039400800c07054460b05024030004000800007980740740034004d4211030942482c40e00d040e00403110305541d81c0c82d019070045001041082c0381c407490405105022180445800c1d4800604203c803c900d07482180ca1340004000050801d0f040503101781d20f41c9082c0d84160f6085005d00064504160898141003011300c030029000c0d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 513048390 1250 513047140 513047167
    0x30c06070f0807061a10020706030c022409060c18090411210c060406020a02060304141e100212060d210e1806010804060f140c0a0e0306010b 62
    0x20031500c80c0d07848500206160300ca030011038001d104120b450175551031942491441c980111418208101d90070004c034100010002e40ba08120312404042c9a1140160414203009000c44403800c400c146e40c50451000125400329110000d075800c1d0002e000300c80c00f02d9040d10423281200d00c0e1030b64416941c030a034090201842000b9a0041090340c000d0150010741e4a0307551114450803c0c0241500d50524030042c92020504001111118170f214040400040200c55008511284426012100142c4940d281d0030603174460307160100070750154040c001c040004405c000c00d401d41e468030315500b1a0b214458a05500c001c922441ca10080da0b050f4550000c0c0040c41c0100c2a1004640b155403900f0f040d17030031104845561586098040003151010005901c5400d1030b600d006d50b070071180140703000c05003410000030b090300601a001030082070721542c07a1801c07440590006002d00c2d82b281b1b4040580c0c41e044c0d205d003c0c130b80c00c00034a1000007140350aa42c00e1a1400090282c141c84000e007855107800048901e64 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 513049640 1250 513048390 513048397
    0x2a05150a08040c051017060d210314091005070203270d0c030311010f05060904020405060f041a030c0303120f040503070b0109060e1b2b0603050c10030e1c120c0306050310050105030c06 81
    0xc27810592580000000d03e241904040d02801201004101ea030213481d510b14242d8030010500011580107108038400440b07424000c140c909021a84032140000710400b082201c11a00400341c020714104100208060380031300465607582d500d500030800c40e01e0418040003610000d80b0311541c880304801c0070401500d001e5120076000b441c003c2500311b0054490300402d040d038424800c3c030304100071501d501d0344450909016100c0f0000040780039605e07004080d0820050b440010708040040d030440300000d020400308004998110707802c00f4460320a9a035601c0b00d02e000c0d08450203140b2285101601060680b88100307114280b840d440308803e405c1542805551010403280a5019268004180c1038a00701c2c030140f0805c0050740c00303500600045002c100030310540b071b410407000d503003050b01d49207070f41c1500700f00031030504c034050b10381036815034040e0740e4003800c80ba1025540c880440d842d00c1c0c040c0a0607281d0305940102c007100c40540c107a50440c40c01d115060100e820034414290950891040c9190914000004 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 513050890 1250 513049640 513049703
    0x60b09100201090b0f011805160c080f030c1308010b0117070306030803090604050111070b04030c020109090c180609050901170a2a05150a08040c051017060d 69
    0x20f6401d065445482c070121040d42c3c0aa54045d40c0f10052006603070030710b41c010801c01801014002810004441c80380710344803407909000c00c9a4106140d0030000c810003164401c034060300105171a8100024546003c0d80b05240a449201c080d050019110382d06005001039554141c51344028030401c541e107007404890041c00d040405a4448000c0000741c00b6001850080041e400102443d15062600741d0031102c9003900520035240038000c010000d01102642d5a2155061602c034014400f40c0c030059555540c16082070750b50790306080782002e41c1d82e880603c000400c2184050341c8c54070303503540100b0b640c002d100c0c0c050241c2208102c0010300c10300040b004c1c81d45e0301284030011110420701640b5034060704030508406540020039118100f8003c3e00c2205200301520781190001da242c8112406144184122301ca07213005d00c81c0300000142448000c1c4250380c002c0c40040d0030442184070001303009002040d0049400711041250002c280103041480e01542c003c6e034031040c0d10500349200a483d4101c0c00b80c1e40d04 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 513052140 1250 513050890 513050893
    0x51b0f010c080402030d09050a060f030906061d181002070203030903010203101701060f17010e06130204050c0a2102070503070305030103050c030a02061606060f06170a060b091002 79
    0x8550006824840c04024000300e0307485060310b0070035104050030028148000c108012030100103000f103584280390032040303900320b00306000018800c0a090b07025142e40103000d8038240c60304800141140c0a042c954805180065062005507184c10212191800380c0106212940c031808548034660369a0b8014010940014200d07030401c0803003800071342a6803048850030000880030604006042e8028803d484458060001b48506410441036000f0036100d880352500c42c41d4035009049000000b03501c00005404024192034942ca89a48000e5030340641040490056191400140e40310f0568015600200c500341e903007840940e01c0e25100220521071500315070310250300700203040019400700002e14003d840703515a103840e50b03d941040340c241100084158003d4100290110040c0d42d154115042c0c0110103035a1100080d04c0c1c10030350010880380c1c00a103075400300404007064050f0040000600704490040483c40380ea90f01e80c511043e0f60881c451041400d40178030441c4024505600e05805000f180d20 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 513053390 1250 513052140 513052153
    0x2100524060409110901080a1e1d0706030b010e010206091209150a02160b03040c0501140f0403111c080f03042a0828060f02071703012301051b 63
    0x110361008031440400070315842c0600217014030f0780d543c000002036840103091004000d01d0560b01001c0901603590710001050f5640e9a50b1128039003214404202d4880000342240c1c011a01c5520150083c1800b443c0d05002c43d001019401031588005040e902c10108240503001001d00300c01c3c0044142c0020110070751080d0085103d4200c10350f8040905002851540284900011014000400d031816081b8000c01f12007041004040b0300d060030403008441003807038900d4091000319030555140c011006200489100000c2c00828000d00c0240564804401c0302d124581d203400e100303404034000003404c1c001c05082040c8900303258038555101440e405401824907080340310000103050454001d405282c80d06400071042404425401c00c810005024180d14a10b10040f210f1014450f0003071a0000421041c0c42e00140b0720f1000f00e54058940403a4481c20801d411418120f1a5040303400900440074408084240d6440340204900000c595510684841d441c0002d40a0842440000074101031014842c11 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 513054640 1250 513053390 513053399
    0xf06040f0b0d23010e0a050c1b160801051806010e07030b2710080303070516080918010314190803040314030705070615060f0c0f1e03021005240604 65
    0x8103c450100603500a042d03001c1d60500d0b4040402c09009084071096620345020800040c202504039603d190746c00142101009060035028a0800c1d2440c2c0540319070b008d044002158030f01504005e0040a503a41464030228800724416a502002d126550305101c075900400c240602030f03030029400e0000504011501d29080000f030b0601d010000c030468105840c90108222040741a0070301c005824804040c1d8a1414402d1004125000c0c5400e030400c0a0354030740c6000c2c104030340c0c0000c1302e07554134014220324035618148607041300482c0300740b1050780e00014a010319003d4006c007058800d01c0c4800190030400c3e841c0651921201c07a00014411005d101d090301c0030301c00619003d40914440c42c115961035030b0f1010381e45000415604529032986100c04240380074003d0a4201113481e044500b14038140b14044480e040c8800d10300c000301e0000d01218020142c0044105444244040b214003c2d02101c080300c01003503180040302c508440103030401200513203001501c072690005240c8110001d000da800c143c0c0381c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 513055890 1250 513054640 513054671
    0x10507060225050c01020a0308150402040f06020307050f07030f14030c0106090203060406050a1404050c1309021308060f0c0a21020d060f0b0304080310150804020f06040f0b0d 77
    0x240300c030350422007081401c0b002008020031080841c52000e102508041f41a69000340620708060510707482480b030764466800c03c0d2195411b8800a00c400c449454016a43d0000039440307501c5030344107032050700402c90f26044034000040c0d00e00c02c03240e103c0003181c4544a9507c2d1340800390055040c00040e40001c020782611a0000d00a500142180042c016600d00744102003000704d585550040f03005282243d02003101c00646142616080801d440200c0d03140d60701c48840c101ca2042440c000010341188001003164070555000d450100c14846800c20282e44910030240e40342011146c01c131100d0340300d60010b400a058074024240ea600c0c1420711001d240d20700c00b11700c9080d0f988610140a100e074080b0f6a00e076407070309600500e001004135038540c80d800d0303041c12000d55007803100503c003902490001000c1809040203581c44d50043c02c0380d09941210f1841140b0040941c10309a500ba0320403040488c00250b00d1601c00c04460071108848000402c15241c0303da0007005170001a00c40c2802c5540e45040401302c01c1 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 513057140 1250 513055890 513055927
    0x60405090a0507030f09021f0203040807060f030501210f11060d0212060603250e0a03060203091b061608160c0906060c0c140d051e060c070c050105070602 68
    0x8001d000890186010a80281100c00b41e00701c0b09a01c41c204007880d005030b210b4004500b034001803180700084001d030701001a45184106e9000d10351030702c40c0740d2001865a1340042410000022647e0600140e6620300c0b800c09c21a92110140502c81460401c1000003500e130500394400d00c0c407070381111084100005c0018016044078203004603040d0000741c0300b04510315500030980c0c084d00485180f4114108003108001c00000c070544e40c0c1845819580c083c0200340140c0b81c1156131003004010070300440d240c1c80d041010b9081070380c10140501c250b02e82c445c203d107246031110481d060058051800d02201d030712101c80300140fa040a5600700c10810000741c1c0400f0380c1040c5900c1c40d020342750035914140341010060880c0d070158000740401940201d460005000f0b8100e400490340210000035030081c840340014807460416000501610030040b036052158460255444034102e000f00350751080e0389043e081c28680c0700710400200000c02081007800558000c801800f08603008641c01030038030020880c007441481 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 513058390 1250 513057140 513057151
    0x250209420913060615120e12030c070804181a01050f0d0209062a031201030204090302100c080108010b0105030108031e1603181707031e0807060b0907210b06040509 72
    0x11808440044881e4000001441b40c00c40e140c0200100e02e682291280c0340c1c00e6140700d6150300a00000400d074000900d102782d500d01c5400814466443d41c1c3c814600e203072100000820100b6909000d03011004030b402c0551041d86000c180c445610f094420303a01c440c11a8450f94005214642c2400441002d80711000a0011a51030300d0144851802000709214941600340e00403015600800100040b0040e01500c0c0c1d0443c1d9060b1404114080146130070b0341400b04400510095914240514010941c003280060490f20454002c014940300711004441030710090240f80c103a98010803581940304c0c3c6244206101c10300c0303210850f041c80c045400f500d203403d08500e0140e000540034640b049020b5201a406801082d9500c001d001c4e0391074801580b52034040c980300280c5286c1d805603141000c0b1064014009031654007881c00e540d03c5007946440c1004240c40d110450085040c10001400c0341e026801004000410684000c135070040146510068400d003100680c200300140400580c6407030380d2a03043d0080 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 513059640 1250 513058390 513058409
    0xd030e0103021b0f0a170315010c020f1305010306060f0e190e070828050c0f0109050402130f050405090a24020301031202010509122502094209130606 66
    0x10b100c142020324080300c0d0b1107200300c1031200c1003007402601c23118201c603030480030f1080c249082e80c0800d6000190f110f40629400e00c0e00700710070403400e400061480c1e00ca141601c1c401c84041141e40e8865105008403501e40c060b00e0312051540000c64807040c40711146100a4107240301c085900f0854074903550400758268006d40e40c42d031102040d1100d0840403000080115943c0a82e10044600c135124180d41d081c42c010098083c019240c44140d0740e9103d40c0c0150301400d000341040d50703a040b480f030501728510454401e000030a4a0320902180f60b02d004e0081902070700c9100000d00c81c9a000da142c0b00000a0300380d4182c50040307400b81180803c1041d40c00a94029070180e00c040c500c0b262481406400e40340b000348000a65049110040c00825202003903032005901010483c0046001c18205007860072403030740280d840f0302e0340070401100410310781a10050246a60095880da0910860760fa00e4030440d031628945225013051080702c908028207925400159950742100d501d10b5a00d4802c2121510340200c84c11 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 513060890 1250 513059640 513059653
    0x5130b030304090c02160504050f01090e07080313030501050123060a0306030204110a18150302090a08010f021921020f0702090106180f03120f050f0406031401050d030e0103021b0f 79
    0x81e0b1824150340001807e054400f0312a9282c2207400d24000b400c14040d407030131a5600c00e00300030605001c114680290a03a81b086903550000600070000b110340314030003120150300340800814001c0420f0280b040030310120410720307154840325040100365049004071384100343d030310b110010150380c0c0d40c0554040b884000d401e40f030361748035481802803078810305403240603260480e00d001704000c50031050102940401450f0060f100d0b40918006040f42d516940024520740c00c01d00c5100d80049198001d000700100024140800c0c2101d0001b81c1d003141c944883c4083c6c00e1041c2080e000b4041c41e640082000d840c100c80c01e82e241042e154000356140e103081e0040f40020350b0710640010b0003500b00d940305016000c080e95080005146540d00ca00030003551081c88100f10740c211003032803c0780c000d900740c40c40082c00300c01c01601d90f903d565004000786920618900c00440c0400001000d050498000140700e80544e44e6142c9104904d00540280d4003100c03441e230141a59518047e10180300344503548a50b00161302800c007 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 513062140 1250 513060890 513060913
    0x3001050c030a050c09090a0f060f090c03060e0705040605130909050f1908090d03180b03060f01050a02060423120c06090105070c1502040e0c0702180105130b030304090c02 75
    0x8807000241300002c01401080741c40c984ea640d0102d02c030780c0140c000401145401179548400e0213004258042c0250999032040400d6a9901ea0803a00d0600d03004d5404215440e034a2010036000c2d6000d840940200b0760070401440100c0c810f60050812229008140741004e959160210864070b40c010192102e4020903907180048400303010105452000c42e2940459103c0e54490b20b0042c862030030070350711550003003a010302054000c02c110302c000c501c1c84403075544092ba1083d4544a80d44101e500030700c11404140307002d0203580500b054880d004500d900400d00381c0c0e1581c0e14440040e040380104101c1391036044101c1000c000400104c681c07034400d2070105855081d0240c0203490841d002d0298142c0740d0512042042050b0310444180c1c40a401141c0f60f11a0280c0d010800001c1c4650f81013601000780800c100083c8808d10001030100500c203a400c20fa456224038805407480c14280a0a03034441d020b007482108840c5150030126203950020141c0749003980d51032164044030340c503190200260700601c55200 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 513063390 1250 513062140 513062161
    0x140108060118050402130302220e0616030e0111190e0d020f01080a2a110a03050301060f0302040504050702060103020913030207170a050109050c15093001050c03 71
    0xd801003420709001c1c031181c0c11801c20300c10620b00d502a603030040784d0102d0b00c91850001301200c00011600507201c1690310f21901850005d40081e0b01e01990307002c0c101641c0c03400c103010010358140300e00b5200704000e0100006075812405003c0c0604240c1240d0340b28001240c4010180c00101b801c0060600c5010001680c0302c80035041c0e06d031080c2e0300ca00c01d81c80c070400b81c4056118880e022800401c00d1800e804c00d65140d6158800030720301ca00070003c900d1804403480c61400b54440c404405211180c86400f8445d1226450b15500c41804c000200000e200788010003149000d01556070300e009180c1005814a5185c42c0803c0c102d400407221f01005910610041040d800c01c0b1400f1900f09902d07ca480103134030542c1d00c01075540c1e80c5610840020300694144012610303030600c945003c040d03100b4000c0c00604c0a50070302d950348c8c5850b0640c092044088070080e602406018003210003082010741180a041e64145000001804984160141c0e4440051124041d84203100e035601c5105070450003a12414599a40e1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 513064640 1250 513063390 513063407
    0x20c10120c080402030c04090f14010603060e0105090a11030a020618040506010f080c1b060a050604050705090109033504060905062506020f0c0a0b0a0c09030b1f1401 73
    0x4034240030402c018000503803000300d5030000c4082c0076540850404118913103a07044040b503076000303000c0280100f4000c0c0300c41419041001100c0c0900000d100f1012900d03e000e00f241c5041c1c482c0b000550000c40701134009420200806210315005007590004402da401103901a40a148001c443c00e240009069580c03820f8030a20350001001c2c039251070002c2030007002511042c1d0203040c070075130040d0100b90780b13150001d00c85192020307002c0c40003984d01c40d003411445040034020544030342c0e101e03a00745000600e202e0310440030313140800816511010201c1c41c0d03480b2030040741d41740481305c0060b05141925500c040030260103580e030a101d00c001c0301c2e9564540040107041000503000584203810410401658045d008492a480c0000c010400c3c20041c0c2460184000e110b00400c6d00c01c144008900040140e001007003401040d03000f806605540e694040e208000c65480c06828404258032010034804100181c42407035006145145903072800c140c0c2082150041c070a41c0c8054080e510407400c1200d1540e003c03412 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 513065890 1250 513064640 513064661
    0x322080601050102030301030b25020f1b03070b0f0c16080c0406060522050312041d1308031509040b04120206010b0a0302091503010608090708030c0a0f0201020c1012 73
    0x1411141d414480000d4a0b0711040c132018262140b00c0300403440a1032183c080f414841b1190540d054840078621002c1c0d202d461502070340c1c500e406502901d030750003d1650148440175500a000d008424100b4604900f507030445020103500101c03c1c003c014a0314000c11040116002020f1020440b81c038040401d03180c50711100e8810b00660410204000454110099035045e111a03058062402d248400807010310840b58403007a4184a80780102c00007498000082040c0c07078445500080c5041c0841c044180500103032140c40912546611050120b21503001a640003181618148401d0044000055007001d050300c043d80ca090100052204001014030140c8441c3d1103030001c0d01030b0b90302d04041200380380070324038a40c0709143d000500014255111100040d042031100c00c8542c495031101c80052903072108075000d00080c4074590340800c41c02c4c0c00105803941d020f81030340200038460091351105c1c00341c901e007003041f130551058080034001540c581000400c007801540d54810410300c081c08503000d46800103030 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 513067140 1250 513065890 513065893
    0x301030b0a0b0a17030d0c11161202010509010504091b17040b070e0a030605010f0302042711040e030c01090506070903050c06180a061e170a0f020c032208 68
    0x190b180958850201d22400c803441e1400b8a864105042455410342c45602007038003845141078401014550400300403021a070f658070443d600c0c101354039a0fa28014269000b07218039108030360388550041d03109100416440c0070600d40241000c0d500c0741c1c0c58058540c511014078410000b61600c400c0c05c1c0e032104440f2041c1460035058107450820f501e500741400e60282141c010008000400d0700e164643d264541d0043d41d000d58100950742c0d40f04100c50b41d00a10b80801c03481182040305140c03400c52004201c4005041800e202c0304403c1300c940e1881e08008024910a41043d00c4d200880d9040c2c3e81840a0310042e50440004030b0052004e107031450515000600300c40c01e0000c192001e0000c00c80000f504491070704140c1c3e00da565428414550100488110201075200c400072901064065000d000500480400303585040b483c0080201500c40c0545124000000c000c42d90009001c0f04841c3c10101c0c040c6070300ca03030043c0307803180500c29641940e105902d1007810486054a400d0f02c40d0030000600000d2413540e0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 513068390 1250 513067140 513067151
    0xc27061c0c18030f0f0201020c03030c0a2907030b010e10120f0612080904090f030f020f010203060d0f020d0210180e0412110c1c0b07080105011e1b0501020301030b0a 73
    0x5071610480c1130300c203101a00f0100007014400031a4020490202400c00007402c40b80c43d1441c60b99140c0d942c0d10550782c201c9138003d0540d90306004210914187c18299000c5410342c40c41e030f5075500220010300882e50450704101d00141007600a0311221044200c08030142d03031702d4010000c050b85920a54007005000b128a03483d0481c10080d081c0007041800b52154042c051540d5400f41100103404ac00341044050881074a64840b0300401d50440d80c1818142c0582c1c003592403d4140010007804c030300003210501c3c1c003c1c9962241800040054104065413840100344410400a64011070140742c0002c0c1e01902140aa0001e400076689400042c3d000b0010038400b11010f18117503a4180c8003a03409030100c800c0c0b000d0103130381610f070000c01e100c1a40d14030b00c00340c2840009425071680a8035003041c1d42d03041d60070760070a10108a600703100700c0380700c0e05a03901a1200b018010380700006074030101e0003602c032a0821500500080c10441868251814903005800150b140e5040d0f0514070b60148005d401d4019007843d05 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 513069640 1250 513068390 513068393
    0xc03060903032a050319020d0c08011505070c03021210110918010807210f0303051e0f0f22081b0604240209130501030303050c27061c0c1803 62
    0x10480c6c0c1d02040401c080c10703049a0040c503150190140400c0040c000e070410510f5440b1950100e00c140c12181d503044409024414002c00340c03240e2280b100003600d0ba80d4041010700150400c00707034200466025a084441c880d4810500100311740303035071140d02e40d807c0e4002829590f6140c80001c0c0c5076120b09841800c1d03020751400700400e51f1601d00c0d11490b100324980d005071100d001081d02c82c0402280d003081c0d01110f11b54651800600901040360480581651070381e90481c4d000100805910940b80442545a140c4071607444090021004000c40c04c02e03404036440d01c4199450b80640040c8034802d0490a440701c010b035850103102480c000b603600c031940c0544100404664903500c2440a0900403005d42c44400000c03e664000e4418101c000307801c020b54081c0c0c1402070700b1aa001034101c034000d60f01000a51124a80f071002441411030f46150311001e000026160400c82079025502400180040e1811904580e4201c4560b0040c0000d505181e480c000c42400e50f41000201c0f120740311640c0440a4541103 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 513070890 1250 513069640 513069647
    0x201050103030908240a110a02030904050a02160f050705030d080a0509030a02070b13051e03010b01030204080a060209031509030304030e031603120c1b03021323040c03060903032a 79
    0x181550460300fa078401d004a206c02d107440d840040001d02c10310005584001c03110700a0742d00c2d4070400450340941d00d0a400543c0521280c801d480300e03240003a080c0c0e03410f000c103038481007045040000140c5003070180360000116a64104907480010013a0749904080745404079128045950003010f01c40076400c20440301040031b0f8007082030805d503001c80d0140c58982c0072140c0e080440e01c41d96044250000b90315102d88400300c4101c01485002c09088000348a80d1012200440c160b00a51154000d56400744e0360a0000078801d030085c203200030b8040c00300c40342c04800c030010400460703041d0b901d601c4130707007001040c0024140c2c040e05c102c0280790b043d40105000f0761b03501041402d07107509106c0a08101105c1011881c03d030f1061b000004c0b01d941066440e21031640c4002c80741c48151840c40128418500f120030100901c1060041c848042400e17919444152150010305114010080045a28807030705000800010054441c882d1070500035940011310b901840114a4020740024400801d0074002006030f0380c43d0390 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 513072140 1250 513070890 513070933
    0x24160806060a0302131205010b0a15110a020d0308070f09031101080a0f060312020106140d120c05060412080106020c2107051e01090b0304050a0b0c09100201050103030908 75
    0x181524095502d251251044009000701da40b11010100141c90008112444484661025004000801c455035220041121100c400c1c4600e40e603042a1745ca100340b4140c001d40205540d03180000990314881199400200250303c414000ca010a0a000c14002c4d410b5005116400240700c90402c50101c90440c1c4880c1b805134064440a4100181480051580380c0070340c01404494032808010b0002c0b60300d070319200f03400300810040c02c0010b40ca8a140040c003c01c0a00c078100d0440d6002d802c8081d0341107692a48450208070000310310a10031601c50600008504000181c86280100035101f00d13039522040c01440064180c0c00101150f104081132521a0303240c0d800d4410f040c40111011222500d9140d226007045120342c4a02e81c0150b1242a800f55400308200d0000031200980e100241141c4a401c0d982c01c600044e02d002d005903024038606400500600e5105800443c050b0100c0c0c02c041c2020b000402d1284401c1034080142d44417001001015000300511014180d448054507072004041c80312844640c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 513073390 1250 513072140 513072151
    0xc13050a0b160212240705040f090e030909010e011508090d08040203160603090b0c07030519090b0d0902040b01020d0e1c021519140304020d060e241608 67
    0x181d526614504541d940002c40f0004804c400030307107001003078401894030b40c10b02665015107207101c660009012035204404660540d09407030070b4000800e051040d80303001061007209800c045d210820041d03d440d031350018114024941c142c1101c1c0d840d81400c11001282008034804024000c0b00d900340300e034840000c20f22220105080c80e28200903500d41c00001c0c80c2c05001a01a20b20192040b40407038410745c140c00841c2020300801c0035880702e032103094a5035000d04c01c1210190004800703010510051507c0b184c9490708a04a180c0900c2040c1c640c000c80b00d06034001d1001d035a07160f03541c041060031402d0600403500a00e00900281ca6045c80c040305c090030b01108074110901c1000d104007a542003d03c0844400602500075100580d048902180b80e46664440c0c0418030500d8400070ba40d1601d240b0804810300700c9540c103c6071f01d0440c1c46d01d40c207100b0408000c003000c4030007a4454039240d400c034034100b03c0002421441c840044000014801e0172103820400303480c0448640d5008003000030141c00001d4190080c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 513074640 1250 513073390 513073417
    0x316021b012d12060e01080d080702010e24240d050f0313080f0a15020c031603050301061205010e04020906130203070e130212060f0d0b0c13050a0b 65
    0x28a402080301e6581010040250b1541d03654401d056016070740308a01c400741c04501d4604104240d2141000d10610300244a000003c2c0c0c0b08a0780341c4601d511420f50350360480c4890002088084100e02002e081030943d040d01011020015080c0c060035011000d4150003044010060504920b50100003800084e00c002c01d501031074540100c03d003003000405c50007440749404410749840d546144ca400c10f0790286032054276841e02c111000c804a540010402da4999079104119560421030134140201940128000c0700e400c1c04184002d1584101075110034402621070f41e03401d9079a6041ca80007a000c0c548cc0407020110514101c0144008a50b1141e0560091340446090031203968400000d070401944580d0000f5031350010051201e05500b00d0098148440c040300c0e0b4074485040064688228001c02c58059a182d1070701010034140d06105690011102015180c244417080700d88071580c1c3d44a0942c2c500781d0310f010000d00102603082810100b4041c001c116004411249001d504c12120700544031464140e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 513075890 1250 513074640 513074657
    0x200f0402090a0803030c090f0603070206150a080d030c0f1d0d110607050d08060f030309041a030f0c0a0902040503060a18020a1202010230160b0c0316021b01 69
    0x380e4840b070401c0000c100d80d10450303580e8548010f07006101d4001801141c06031142c6401040e5078580038007981d10603030041c0c0c0100456501c980800c00141c00c04400a5002001c00780042820381c424000803036a9203041d00c0106009541a038000c1c00b40007261580c504120303500c461a02c0039200044400400001140e040141c040507041038079084428080d4180d000400103052000c109020a14485681aa4503040d510303585000a00000190045009a05420402006050f89032030ba000701d01c20200c00c44030742c2c0d0b152044804246484848403000690342d02c08690043c2ea17240c0700c1400806004140c2c025410103192030042a540c18025040403081a05d030000020742900000271221000e03002005240c400d940c0e031a107400a019402420790060013082c0c00c0910107a50004030b01199500c0c03200442805180801100d42d0781c000c80d00907030302c5040410452010880100f02d141c00395520784174041d80d80c1800b076031305206194445003010030354002000c0c8005801c40f01d981c0f240168000c1c2800582c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 513077140 1250 513075890 513075907
    0x20d02010b010f030e100c11060901060b030112050a02060c0106030b15030a15150f06021b0f2b03030c09090e06010e060f03070311040f09050303010603111e07200f0402 74
    0x140054640c00c100030514000f12080340b00e510540001750350f00d00c4002d8070801c1d112b1540050070380d143d5000b4155070303210400c01003200d210b03184681106240036006507070360000244e0029400b54480303240d01031140e450300401d1040c00348169046030052000c605100c1d4481000c404603480d03000c00d00c40944400045e109090100421380c01120001350894050280e8580f954001c0381510107070f024041c010310440c2c1401c02c144465441100e64003000401c40c010044800c010040246840c010750303100d0b2600890017003444909031020385101442138030013003150350780000000c001d98440e0380300c03080031810142021a81e4001146c0380d0f05442a4240a400542d548030104072503043d5080c940341c06104951000040c000e00c1040340da0702c038000b00e400740709034861242c640c019140b02010140064204000400c082d600030303409080103d68405009040141d0200d264011410751103030041458000208202001800c1d951019008a1444020b16030080d03203000c10301c03044a000c5401d0241d85c1c001000c91 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 513078390 1250 513077140 513077143
    0x50a03031d240a02070507030602030a0b150c0d0c03080a0c0c150605041b09050607030e0d0503031509040b13050f0f0c12010920060f0a020c01020d02010b010f030e 72
    0x111007549a4100e800c0c005880080300301c0400a480a42c002940c1c4401199116140e4021148a07540140c000d002c82030441d250003000790700c0680840ba0301544d0b101060b0241e254a08440c030380d48007002031140c40783c1801c4c00450901d10b4500044c030070404034481480000b5003043e01c0580285500340000344d401010502a00c24031841607010b00440e040c45040c160f8420a5084402907e6066a0a000c90701d6860240c2c112074071510a850042075104e0303070501c101c0c180400a04a100d00a00c4c10340b494a0a46010811144004a040e6406e40002041041201e0240040070303040c0b10a440c1c0c004a0300d000d840d025003522001e45040c1d2452038218141d41032110401180440010302c2c8240d503e103840300661282c2c1e13480d0b0010090f0045079411074004e00e040040c030403100c04079040f030b280841c20b0f5039030421444c911404081196010100f1f00040b00b110310204080d014880051b00101704403800440060701d00284d1000000c11a814400001401e0b40d110b6550311a021050a002c2541c00a070600c45 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 513079640 1250 513078390 513078431
    0x80a05090a020d05030a021b060703080a1104120614010e06040905160602012708041a0705030d0614030a1707031b0305041e0f032a06090f0501030504050a0303 70
    0x2e503005880f442c1d04018410048024180344040d502120804601040c0d110381e8100c204030803540c0641c0500140020a00480080d0303445000803400003103c00500340219510b0300030b034204900a0b00c14510800c2041540c0c0310314125401c2542c030260480d850407840400f00c4134014411402140c0740c54900003041000c12501200c030340b00045101c61151241300090003405400e00e030b4400d4842d80c80c0a2105280100a40d0a4141c0c0081c805850075003400c00e00b101d01480c0380d0280090785c0041040c04041030b800c1c0080d00715050300440100e031162501144441446c1180f0200340729420040b141e00015a0b080c00002c00184001c14554651040b07003000c3da0040a010100402c80035444024410164808000d10948209000300c1a022070318003151040c0b0071180c003071070a0a03014110140041490b015007120b402e8404000010020840581c01c18140e00c0c5070300c03080c00710701c141c0014406e2401d41d10454010304428a8100181e15207030315000d60343d9500722000303011f0664842c2804c52020844c41b42c0c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 513080890 1250 513079640 513079643
    0xe0a0e04060501170604051e0309150a0207050f0d02121501030b0f09150402010305060d080711031c090501050912010f06090608030903031c06031a0f060d02011e090f0311030c01030903080a05090a 86
    0x3983e03550214254100c0e16030300403618000140078083b40480c03180380c04882d00035a8217014080c0c7c00780b0000e980c20310404069806a10756148100a80d407400e01016182d2180030b0341c814013401005050159141c242c9100c082c01e0300001e80c01a0395029402e005c100302d1590305c00d809203130114464032040003040c03100c0d60340c0f94003400c9840002180c2052125200300c40c0e010b03500a4080b078518090b4000b00000c1d20004421840000d017404408008640c031541c094240b00030300800b04000103903101d072801d007103d90350206031414a403079590400c1104068440e2800909404002c2d601c2c01c101310300065164403a8440084864500000f0250709504607440b00018603485170301100c2c944499244007a0040d400c651038002c0c0005280000c0c000c1c10401d00c0320740e1950781030716800c0e14001034020350011110f980384a00304005100500098000b03da10b4140700848c000c01d03c04444e058490241414202032079685814503040c800d14100280c1d002019650140c0c400390b002805868601c0240d0030281080c10 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 513082140 1250 513080890 513080899
    0x80d05090d06322a030f191802030c12120705010e030f120c192712030206090c090c0c03070807080d0b01020d020d0e0a0e04060501170604051e0309 65
    0xa20b500d4643c5000c01a000b400203c256114003810f603059100d014100995100491a0603c040740b81a90a1038840390801c50200f206200c020482c86140221038620b202c0c42502c6520120103429414140010b81b288402614a160318036040c4601582c0da2151140318000740e40001816014404294040a00821801c0c1525990b40703a09183c2800c0f03810002c58010140452800f0544d414131080c1101e07600103048010140401c4801016546122845248240c000c1d0003000d02d8410200c4032a0b40c0080c102803904954000d0590500a01d40b0000410740703005540308003440030403580c40c0c11506510a422401c15a5920a400c80844c21802142e8004019001c085105420800b150020301404484d4802c108080b000520049a90301070120042001d40c03c5540242c40031440340c1620300340010f002e41004107140d40c0746803016180d0422607082d58015911001803001081d50103410200711b003210000d0405041c944c83d0240c40300407030340e554044544610b444800b410350a205440c1240c034000d0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 513083390 1250 513082140 513082211
    0x30c02090a061701021312030c020a15110105010e0c030702120c0102040303030c3b21010c02160509073e01090c0b0c030405060a09080d05090d06 64
    0x860202410160040303c189009911106028040520030f40d0030381c0018081c88079145181510f071045a0103d2501581080700014500b8007584803900c81c0802080042c0c8a07421840991000520700e188180394240580d040000412491043c104001e41001c8541030195036500c503d8030036498202900c4400792002c00202d4610030512066000d0000c0300c1c0281c6003400900255681102d0446e04046101004c101e4a907002114502540110200e800c1102c80103030010400000034021003000c6221303442c40c00b071494150126101c2030140c0c01c020507079400180030001a116401000f05001d0080d0303800303100070100003043d1510030102130f0303520129001c0740800450409000d4524000c00b8021f400003218604641c40200300521604132002e1f082004c480e201402c09144007500da019441006c1d02d44401d202c0415103030345d1800101243c41803600d904101c507103046000c50404104039024130511000b401a90016211240a44405940000001110781102c540101d61100c1c4086403100102c021 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 513084640 1250 513083390 513083401
    0x20f070e04050c0d08030703050c04180204050406090b15030a18121e0e12070e071206120f1203060b0c031209010603021c061107120e03010b1c030c0209 67
    0x1415024600840580352002034600a2041000544da0010700c00041000040d5045c3c1c880d9000c560481610301c2650f00e055a41c0800c010003803090004520a1035000404100c1403910b446001c0041124040078411860040700050390006900d444045140b000800510b42030015030241c13122240c0e000031a200c0d40d406041841d070141c03101074408042412108070f441c5412141a1035844280107655203810640301c0d0b010310000303803e520412500c40c0b064440c04649610308030f503218450442580d4010140c48650310100a582080e4081c0d00c40c41000c000c20408101e00004044500380c0000948007a409414000c6005000c02d52100814000209810425010210040030081c92946600c61584c03141a042822144244802980700d94a0700c0351100c030000411210103018018140080c1401c440b1202c20751720351000c50100c0702c10802c840117420003600210390b412240800e500800102c1c42081c0030440d80aa5071084418801d2649003000070144070390a025a66640984204502e0801 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 513085890 1250 513084640 513084659
    0x16140307120e012c0a0b1602120304020108040f05150411120601050d0b10090218040c0e0a0e1b120711060705040e070c0602121b040b0d0c020f07 64
    0x80808101c0d0281c1048a00c1e00114414001c4004d0b03aa0540320a42c10801103440c0315540341001011680b01d40111800c0901164016846d58421418200803a02800c0d101a0090030a880700d02e00010500302441440090b1340d01405141d07000380d000d0b540048241003418114689030142c12500884a43c000800c001c01800250846c0681c40a0314100e00d043e401040540c0c80380000d0040d80c0d00b05008000c40000319003200140350300024001c4000510035224003910069a03c04001a0380750090016442194145485540c25031007003483d000b12003441d51000150049590b00c41c503010414040c0118607210791011498101c03244c000c1805a07510145000180c02035030031141000414074407209039903a0440802d00e54030404155070358030300d8107050403006224610080c2043d003c2054a2000400107103051000b00092041d0405011f1203280030182c9459221140d0141c02501406001c02c000c0b0614010948000200651000ca600244680100c0c504413414110030b60340d10036010f000a00046 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 513087140 1250 513085890 513085907
    0x6060806192306060306210d39110d0c03020f040912050d140910060b0408100b0303131d0f070804021905130c0201061d16140307 57
    0x10001801446070300c1c50b070b541d000310350a18140d80d010120742c0015518503001004560150009041003ca102c101030b22000c0358400d86101000c0740d100001d01004a42c100c00c80c81101441c4500b45d2901c150b00a00452688920400c80c207441103c0038505010040e001c2d41450440c0005450380034500f1881c100300c10741084a00c4241d02400002000c00d40c80d007041c1c06401889508010868a100120306084820307078850903c200480d55950384d009005140858994010b40d0030b100201707200c01042400d54115441030b8411006402c0800040100081c082507015005e05403500020b181040600841e096118241c0810301c0050058404140406d0b00d010009071381e9184407881156a40322200c1d107494090990f0704801180d030000000d001890104280743d41c02e42c0885450584c15907420109441d41d45040c0050300031501c4980d0129042e509119400040400c41c002d41001c0c3e131290f00d07820700710344054035082d0340c02e12802900703400300d0299841142400310030f03070703a07907900c1c0703441038000f4002034 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 513088390 1250 513087140 513087181
    0x1801021812060907210501050c03060306070309050709020d020d2a170c03090307060e1c08040206040b0306150703120c032306040915050717090c01080406060806 71
    0x80055a0310001e10200040d101d02c10040d00000302411801d184a0f624552690001024522055810003000036400c2c0103007401010014006504c909100040508021000b8105d070304141c07074820f40c440450f400090010032a050848010f9448030740c10604006407003041403941400b0305058424a10322200c8001070550800f05100402880546400b15a468030710211902c6080d032940206811300b410000468006007114200cae0310f8201789650748025501c9030041c2d03907216041421120800c44040e03680408000c880d00d8100d580340303020717800611940070314000c0c00e036600390100000e001c1d030f1150b0142c006184d882c41d85154443c0d26506e00208120380d8080482d004a01f480907451142c1d01034000d0f01031149000c1d5010b455840903082c140b508100003404a540607444411a2011917031001240309801001040818103140c00360f406000c1e505200c0030590501d42c10390802c504080082440d82c8900c0c1c0901c1c2c4002541c849051080241096402c00b840c54041c041c00c1c011070400d2005001c0311030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 513089640 1250 513088390 513088399
    0x20708150108060106090f0303050a050403060c11010b0a0605030c030a0902180a060b190c050102090423070c0c0603110f0a030f1d2d012c01020a0c030818010218 71
    0x282e0300c0710760803200c09046205010141c1c1c7c03581e8080c130000e40034001800600205242c9a410160703280ca4040640309060a00000b2404400514078a15428041c45038410400e0b144803501c24a000801006880002c0061414040201c04078802d1201a000320300c0d003540040c80071801401d08801d00b94465025035844010500e403c40000d03021488005071400807002d0209201a07802c943ca0075035200c041135804403219507080289845076611803007030381d1250003032100e0814031038400c58034000d88004c003510b01000d0000051030361000584442e008416180700f0b25010451000068142e1a140901c0102640b2550702181428103c2d030f040c0d1000c03a600085039030034869061003031040581e402c280195501c03907801c90035180d00170111004000482c20f03045116001141d55810144e800c50b00c00040d00c0c102c00c500c40c1e200c070f0340e40000610a5482c548450b0000c5140070494034001c0e049070054040201884040000555020002074880a00c066a040290356500d984080c0000c5c403d9088607542c0b05 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 513090890 1250 513089640 513089653
    0x601150206010806040803161709011d06040b1f0302100c02100c02010906051804091a0c03060303070201080703020912011506090b032e08060114040209100807020708150108 76
    0x4860340044d40c2170046804c80c900ca45980c48652250000c1440b0303043e554140810310000e10062040c1002c018401d20196000040042e20403c2900e41e00028200342007140d4081c5080c040822105100150012b01c5003200c6914803003c0d161100300100f003a400a50310809441580000d9500084a48900c5100320340386040300b2221102901c00b1190084080d00140c40100203000e00da008200529440e0508441c0009507840600001d00f541c103841d40440351140166002c0503005c0030f201e003640c0c0100066401e00d05602d0000007280d80c9020324100641005807000115103414060340c101c580006010389040c24100300e800a0074040c10310459204032042070441d0004070140b04281c16400c0d5241d40c2c1d080c52940d210328000058501c0e2030211464400c8501c404201900805c1c0300c04002402d102009c3c160540c9828041c204a41070850310502031801048a201036568142c60301107070510a0410040503107a1400403840e00038140c0018045218004c45000400280c280440c100d80106084401 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 513092140 1250 513090890 513090899
    0x40902070b06060a080c090301090c090c09052e0516050a020f060f0315061b07091a06090120010e2d07171c11010f200c070503060115020601 62
    0x1004e21900e5250b000007422038021644030300c803d2004010252000b400860164696243e103100014558040840981d5032001415983e801c02c1c601d03801000105c2e440400c080881c1002207184440000380c01d01200c1131509107240c18015230170f42d280031007440d40e0003451051600d0219a90006684181d02c5080d10307441035140b5180000485280104448001d403c6494100036141810618401d4035032060090080c124069154082410120112401424403501d0031682030122002804000e00d11074102414001300e0300c0d4402100c085940a1134140441d46041c6241a2000e01908011102c1d5003011505030f029200003444000c941d5a0405580d0214188400d4140407210300c8002d00507a0008001044070360044c41c0aa0945243c44058600c0b80741c802400e200306071440070000300131420fa07e0841c90341d207800f48602076205000780010000c6c054076018060548130040705405080c0000145050481004c0c0610700081c440a070403110503503102c06800c90503108002d00440140b042900018 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 513093390 1250 513092140 513092149
    0xa0c05040204060c1e020411030109060609030b15010c021e1e0306042310051509040b0105040207050106090606050306240403111918060f14040b0d0503040902070b06 73
    0xb01140c146031500d2810485075511a0320001c90145025280c01c1c96040040260322940924011031546081d0a642c035030612041ca42140e41c5a00002c00f04130308034406200241220681c40e401c40c0d56140e28096200d03481700100c9003107285a80094101c10544c0d45061800e00c0d151581c001c5410450f05d10301c59401030100c0c41103003071101103030790352580c1b1001c042804550041c3c05401c0071a0b040c1d0054001c440c1c81c50405180c001c10040d81625281e681c0200454103542c0900485040021600d030461400e1a45607001c00b007406000d0301748500d500180000030841c0940c4580c0040038108800e022803586c500e4058074542049a0142c09820f42c035500041e0048135090035500c0d410541c2d90b4504117070075501c8050309041c005012580000d61b02c80c54001702d24811242c080202031011034002001082c4a12009030b502c990f020620312040f4000500c12804400001502c01e40d0a65001540920300300015211180a400c00f40c0780d80400031f00840e108103203400500d1014003900380c84007551540020301 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 513094640 1250 513093390 513093397
    0x302030a0b0103111605150108070f060c0f021009030b0f060301050928080c0f06010314240901021308060108010b060c0a0204090203070b0d02030618010b1b031b0a0c050402 76
    0x859000070024101410344621180c00414001d4080360b079140c4014100408000003270304680c1550740a4242001302c1c007000701c4044080c01162502d01c50b1000c0039944c4480080503204020320400c12208040c24280c440e0445400864100c0035140b41c0d030a003000c003990340b0003040d51814001d50a1400087c0154800a107601e4840101d80c1114004003440080c0034804034400300071a6040410404d50250b102c041083c58503421061026000319451454095441080440e41c2e6209820038bd0110003d646414405c4040900040c00040542e4641d551035009201d401000c18042080c60008280e00f200050420b05952100c0e00800c6a00c443c042000190302489080c0e444d281d02400d000001418290050f01c8039074406012204501d8070f03605062065044440d69a00043e801f20401c01c0510340342d104500c0401c418103ca40e540d504040c0048070500c100300d01c5841c0c10b4405146903a440038108211804c03416070980c0503044104604500b911501039901c2a00c581052a034046201c2c50244201c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 513095890 1250 513094640 513094661
    0xc0c060b060a0f030e0a0c031103071a0a110f0a051b0303040b090f010e0307181a01050a1815090e0a0608071a041802070b280207210302030a0b0103 65
    0x503108007010701c42c3d0450140920802d072541070b0041d4480200003964041c041d201031031040052088000b202c00034076140c4660760b0b000d9a0400c406400788203d20242d003044807a03007910361428030305403419070880074a8611100d0000c05a13118110111040c8000400c0e40304c003070a1941c2d82c500300c0d502ca12040685c0e134000c0d0b00521002c40d2040100000a142c01c41144e41c03030078010b040640040c42e410340042c0c1003024662240c3c2c52036090760300c020f008070110701c0f4148003440210304160b41080f20600080090081201d1034080c08030140f070b00c0c01344c0511226140000c0c0b00e00180443c400305125401801d80c0c880b8440c2d944403822220200711204594040d0b10191482d01000705030700c505c0e048001e9034810086640203031501c0c00700700c081664004e282c0b0030300013540000c0001d81c5c0ca292030310f0311140e0024010600c00c68000011401151416001c00000140c1e80000016803102d05a06111a502840c0d00140c90140c05a00c201c11a058064010314480c80307401c4030030010080391000640036035035800003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 513097140 1250 513095890 513095897
    0xa050606101205180d05040b03070807110a0501140a020c2112090102090a0819030323041209080f120a090503100204030507050a051c060b040c0c060b060a 68
    0x80e0300341805090810010014600010b0310041201c1610465209440300044203060188145280d00c040120940941551506d24982454009150f00702c0c0000703400041040b0482000ca000303284a40345e05407250a20340c040c0c0c0c20042c09032601030300810510640312400d688100016488040070b100b03407180e400350080940440c4e542c01d41034480341440420304081412040c0611000c001d100d000c007910a0241c030000503076404a2000304110803500346d0140ea0f030342d40301589480302c0c880501c00c07072880d055160401003a004007080d10124400c240e0600d80011407000400c000500c107160107001c00344405038442c9041030b500d94052988861920001ca80351b42d20500c02555101158001800703240e80328540305603201d07200d500103400c1c40302290758640a540c01280900c14000706102c0315004000c200da407424420300c1d107000711b10304c0c3c001e010402120a50b00c421758810301442e034000b5100060020801c00c010741c501100030341200784c070441c203480280c5000d0803901c05003482012220990901d44 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 513098390 1250 513097140 513097153
    0x110604030c092301033c03020a05120301151d04112106010504170114090d091e0b1c0f0608070b040305060f101a071202060403120e03070807080301170a05 68
    0x748a000612813204103a41c0040b030391b900b565900054200c0f203070051190340504206520f60a001e0b02c0c0c81203080d1550481c500400040040a03010010100e49074101d08182d8002072001041300b914840d00680680c1180c100031055514089120040c140808645c080c4450103200c0021654080380880d1007501240c03082000713020568406200da40b140340f002e07001040f1005502004145114280c1300c0328010b43c002c00803042034135009845c10000e440341060503007602c4ac0c400406d0f071300000507124070b0f603140500140c070407030507a01285803c1c4400f51410061000e01d8015642d9001848036106d010060302a040e0041051b1803480c08036007c40b501f0400a00494840741401441044003400d050007190060400040440c18514600581e400f00e0110070b4446056080400300030444482c42c904642002080100090704082020302c1c0301080b80b40040d04c0c030041842c80d441e503c1070f8000540301740b401060110820401000a505030380800c050a0340540654201c00c2c4c1d18000307a03c004000303070000e1 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 513099640 1250 513098390 513098423
    0xa0506090a1109010513051009030b0f04020a140301140f1504050c0307050c0f100c260123041505040c09120f080904020a090501020c100c110604030c09230103 70
    0x5001520a0480c0c045d07806d54400d940b01c0003da030300984450541e012503100e40040003031103c0e003c40290b000d40300e9141c2d17041d80d1400d540021f4201200c0d0049529507a021540c00b1180c0d00c003544804403d42104610206504004824003980d00d402c03205203440e410300002d12456401c05008d014001d01030980315908607100e649003038455070010345002801d4441d0030b6110502000400c205202822902c03000921002401ca004100d10030380e00d030403102c4d04c09000344018100203501c16181118103907904495003004480300440140b8030850880c0d805400d1800b8032410607504a02d030230403500704482c1080007000b610f0003170300d1407022480350201c400c000f071002c00003089501000824a520880b0070f1781c80c1800c401e001a0032a08046040b100040c90360030140482d503010883d030099000200d810050746034000a0040130328006c00402000c404940d060081542c82d00300989014540c003000444d071880e1907a10312002041c2c00a002e98850f4080b40c50010000d841324001816250070008012400440303 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 513100890 1250 513099640 513099647
    0x50a0605070b0f060d02031b040f0e0a1202160b130801050c0304241a0907020f03090d0224070605100b04090203040c3b070e1c05060a0506090a110901 66
    0x13070101340c100c50940001001a54140204c5007107008124801d00f00c1ca4010040c8401c8401c8150403000032803401141007401c03013000440301c004962002c08071a03510300c0c148080b81014840811003940d00c008a001280c3c1d044010090802905103403c0440e1090350b808005080c1c03102520a41482103080003c5404a440400080c88030748080050484032001c9142030812035200442c0341d14401c00e02081e400d1203203090440c01da08151180300800c4100c100c04880c40e103a2248404041c42864809649421519084c980c0c00752102002c1d034140020f03c0a07030703000040f40d00c00d01041314a5890100002d0f0403038100e0481000303451000007590b05090030b20940400a5001810548081480030310000f09007000e0418815110074100c040c1c3c504085107064080e100c202d0301000c030000410101081541c81d408a41801e2409046840c0b805050319040020301505900c000901140508400c0100c5402550007041c0201c40c16150000b80d5500c82c10350804a640c08185455400c00810441300399610 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 513102140 1250 513100890 513100921
    0xf090c2105030d0509153304050a0e0d09120807050c10050a02070e0408090603060112020304050604020f06030f011401090f080105070201060e0f070c03110a0c050a0605070b 76
    0x842264005a1251500c0e010b285810045020318100d890f0703010400500301c1800b171a51000c105410683c02420900d5052284200301042d424500301c074004900310301e039481a5100c42e0000d010300204840c1c28004d02140241c500040e81076110b110740703040e2240280c0700781644c4080b11145061611035140c2aa41e41c00640d10032001981d10b817080d50b5581303500f83d81d4401103034001c1c4c146803103003079881401c004e0103410854203500001c182540700b020000407620f03107002c07126207210480d95169203030f40e0341c0c005840171450040d10000e03c03032002c8200800c0010020317401d8092802164082d031502e001100308003c905c4105c5e41d10340c0120668004001c004c4520101440c203d07030505003a140641c40700084c1541407819444205e150f03458034180503081d40c080c03240f10003500550f21004407d207456a40031000b400c0c081c0c030501c10002003844000c10301d482816071090249c081002d46032a00c006052440040f03041c0d0166a00c02c01030480c000900f140103a0454100315801640c050440c3e80d070404070000c0c2c01 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 513103390 1250 513102140 513102179
    0xd12030513080909131b090e0d3c03060806010e04050c010f1112070c080601120f0201090b040902090301050a051e09030d0c12050702030a050f0d0b10020a02040f090c 73
    0x42410b050440080d10500c09240d074090008905086c0c00d14000d0440c0130380d4450201a010754010141c1284042c1e481020070030156803007001034140c50b075840ca4201d070003452040303510001c488540b0041a540e501d50003000869003c04100d42d41a600d030b00480b1102070056400400c186d02241041145500030301001c4080400c03418080341c4121120701c19400c18400c0da40242c05000009a080204505000c0b800701406020780100050f6052000c1800c290710540d03405411a043e40350414216886006e001c005402c500708900d403996038429000019400c41c0c4a9240b1a500b030100003040c20f0090300c0703024030820503040041070905003c09005030f600806068140355010402c103044010303810b0b00a00f0349a540e01d64034a002254007990880807075501404910854104200c6482050b901c807090b2049210500c1403941c0e95590298984001e2010300185900004e803001100404c40c1c011a021044900a50f018089034014001c00012200001802050109000420302140d880030041032180e0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 513104640 1250 513103390 513103411
    0x30711040204141e060412060609050702030901140408070b0403021c20030307060e0601030309080d09063b0a300f0507090606090602010e0d030b0f0d12030513080909 73
    0x200d1303040001c204c00da07000c2e41003e00540c80803c101010010244030f010020000c03000c0800c0300c1c1c20880002500c912805030954104003140e0800014440d03010110f84c0241070b403808903030700c4533580c200c0214150020300c01a441580400542c0c1c0000903007815409080d07038020440c0440c0c0044c11280100101d016140d15050710052080720700088030380c420301d00c58800140c0142419813541c60004c045200030b8010300915000f418034088425040440d02d401e507041030038000d074a1102d04100840c8001c4c0d0f603083c09580c502c1462100006032240501c0d08402c0c900741c840d40146921040701484420000304c42400e902042d0300800c182032041c050f1100003038400c0848454081c2d20f62a041e1800b800390300510703540b96072171804001c5c1c0350308848000021f2195000074045041e0115002e500e0390500740c0c0c00000c1c10340307540340340f015a0b1311903420100b07030300008142c180020720b182480d4105401c01d200d40004a0715040109000350340c00c2c01401c0030310754424240e9240110340c40612180840c040c0481255 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 513105890 1250 513104640 513104689
    0xe040b0106030c08280b09040c03060c214113080f030406060b03040b0f010515030f061906050909090114071805041a0f040c090e10080d0203071104020414 68
    0x36541c1c1f02c82c1340d00450051450550440c11810400301b01c640307104007034090081c050480000419407441c0b410b0985554100011500b44d149408070240c4004604999001000042d0340010303500a0030600d0030860750b600f056141c3c5c2e260030310307554005417140001d0300c03d4a0600003c0e000b448040300071a4130500c0384002040d003a43c1c1e11b8100405400548084400d41d40320b1b07042240c482c4052090317030f00414040b03403540c0c0e00d201074103007801c298070019155200043c460340010b4202d88451803a03072030300f00c0c0c102c3d000c1075240d64034000103103640c0100e21800e1040f201c0e0800306040300c1d0305004454001c081c804450505841d07060342a07403410a1000c0caa400c80046001c0001c0b140c2e158820103000e20007030996614180f140388100404079403503403176107031040740342c206503039503040d0312039005c10582c1e4a805c05100c0c4c584525000e148107c0240e4446a1144208010180216800300103860824480c1d0000c4c1d03a140000070400c0240e004030b0041000d8102c0b8a16986010f2501041480c0041e0002903c940c0c1d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 513107140 1250 513105890 513105911
    0x10021308030a0c141f0b04141302011d03120d060b0a03020702010216080c0f0105070f0f02120a080f09011b0b01180e0a0602130e040b0106030c0828 65
    0x1950000b00c61030001c00d010350181410302060401d22646080454080d04506200c0d6000d00d20846130f00040600003603039a44942e1441d21140c1c80016205070417040006940340c040d04494030b450130309000300d002410b1158023100f5514814840c0242102c0200908245001500842443c0e004440c18608103034480c03a00040d81c048540003030188101541d00565111440d000180c5031821500c50100d910703007090800c01c2880c10210304103610303810460b413404001d0301c8940100c6a80c0241c01c0081c02810648801804001c0074054211050788240c8085c407501d4190984141c031405840b001600c400810001c031001c0503030120080c4041007050610100ca100e40f84600c0850412809040ba004050030005121240b241c1481d800c0e1303000c25882c10b00450016800721915070b0210030b00144010313000b0072101d100c3c8500134840301c06000342600441c1c0918150401d170800c29401e20449020038600f4040034032843c41801242c0c440e000c0c202f00240c0f28645075080300e603c904d04648035644103a031800007a0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 513108390 1250 513107140 513107143
    0xd0b0117012c07140d060317070302010e0a030f030b0616060c0e060f0d0b12060a02031608130f0212010f0b1810141f0512011710021308 60
    0x40c040c002d5000c89848250800030741194000e07240c220400c1e40404001003202c0c0560001c49282d8002d0782401c01501c0b2240300602401408181d0002400b04116a8004502442d180003602980d4001d40c0280103a00f110500907499503041305010700058414050225114040c0d04041c980620140074107152002110312242d0b540c00780c02040b03420391f4131004e040300860b610402580300c4220440f41c99242c0158004100345030303c01c00d1140b01030030392601c580c50440d030346124030b4020704095031040e00c04510300802003000a500440e1801481a0903800c2003825600c1000094882e01414070300c000c4199051311407201880c000103040f0b0784009010983c0c15030003c2800f070040e81d42000540807031084d81c010304022180390075006c0203000c05002d03410018402c0c0346d61800c0d000c440c140e03504414012094004190360b0480c921b0352240b903c4052044610041d0311400a055020803080e49445598035a00120b10000c03020600d82010b910034080100c3c000455070003024500300c80c442502000380c0d03964429 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 513109640 1250 513108390 513108437
    0x6020703021903081509013804030503041a2106030f240f040c0b0d0f14061908060c0a0c060507050417010b01091401020c03060421020604080d0b01 65
    0x1240000c0c2e104d400c0c000400071010001c0700c89202142c4220107913041041603110360802e03449090020070543c000074103449510070200c5801e0704180409076520340b2802c0041d500c0c0d0051098101d240f001d8120003c5501100c4140ca82e5031000e40c13440e14090344400c0c240340c01c05402606407581802042c0d515040743d00d04001c00708185141014400400c050303c20820280700004280c09903594002c810400010808504241515016500c0d55194000405582c0081000c2044484550314241d030509401d44402e0010303202c2d03d000c50792a440030004061100802e081d5200e80c2480d9030040d03010420350b51041028090220803803410441440d034945445040d140103960f010003240340050f042c0000614100803000300307400c1400904c600071104000800d12505440b0b4190b1510041c0c10300716840e84203103c041000c00e8010211425814030f424800c20050300303114140f000c200313008852462207002084007886150031114045c101001d500003940038158032040c0720704024a0034640300302c00c520700219 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 513110890 1250 513109640 513109643
    0x703020d06020d1a01020706080621030f040315060815010501051c05040b01090513030e0f18070207050f01090303080105040f11070f111e120c04090807050d03140103060207030219 79
    0x200100400304c2c001a0a00e5102d030040c204200360b07001004059152510358580380c50404c1c40c0d000c161440d6141c5182140030f0104501d2015800060000c240b003404e040405420135826010032000d83c4e5001147c0d69031026000c42941c8403040e00040110b5070161014000c0300b520f10105c510821005007002017192400c0702c00b02e41c0074544100522a15080d480345d15840382d842e0200d9490b81e02031303450150140d40f245c074100d0310039013034004240030607140c09698082c54480413810440304d040c95180a51500782c18016140110b291070288440da6108040c04421250507441d0341341d403030b42441c1c144070203807101d40c60340625580c8400ca0203500c0182e500040c070445018164100019445203402c4090709440c5020911074004425a42e5020f540111103a071400400c0b01c0c1001001c05034401c0c00d0601180420240e402490030000e8010302c0300444c0100f904511500649074180700d220030036001c98607049001d45401c0e1400700140002081c40e4020401c070740c000e00441d450040030a0100c003d0b8032a1410 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 513112140 1250 513110890 513110921
    0x810180e0d03060b1c0207021e010e01021f0e01020702030303040c21020f090406060816031502030705030106110a05031303121106160c0b0c040f090506030703020d06020d 75
    0x10126401024010032040807058a400d000c4680707000404100e5000329240030643d207040344001c204404099045842c6540d02910f00305401084100d4403007801c40180b01240800e01c0040080b400d90302c0030410131030803003681424000500c42d8551440040549511901d110b42d820040c20000d82c0c1c1c01c00c041c5204510644981c00280c0c2051140c0da4402e1201c4903010141c6102120440103a9130b6004c0020018415218440d4540e19401e028010707100c07550001c80e80d405032211a1210308840704908050b0f03806801b5814556040c1c410303800403480211003d0001950034030041c049507128810500c10b141282d01100c45480454907841c3c19503204058400311002446020400c00c41e416840400160305401e04242088144107410b40b0761400504624909603000c0350209142e000e07010402017140c0140c400380c81c602c2d2104584d180365209000d10001400000d50010708422180140b03880b58501601a0a00300e03d10390074404000320090045800640902c4002c048840c1c600c65640d2884101c40f = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 513113390 1250 513112140 513112151
    0x2120f0418060803030430050306040b0a03050c0d0c03122a050a060b15161109010303050706020f1c091511031302120a0506060316060f081018 63
    0x5462201c140c2000070102a460904800300085400072041e2907100f030b00321070840e1000c081440da4006168400c041d076410b89071400b8036001000e034410040c1d072080c2000e030b4040284038035032820043c001005220003809588500c40d40006400e03c41030520505210b03070040c1c403013562640c0c2c48001c025042c48015001880901005004c504000042c2881803d81441c000303101140b61100c0352140084034000d056662211114840d98413000f032140054020016941d44429001d103040340c01800d019400d0300c80f101d91042c3e2900500e000080d1a048030f5064403014030305211075071100c001c0c0d00a00541c11040d003092080c800d11641980e1032142da2540010700007800729580c6012011000641c9605140e50715040b148000114034074100d03500301080ca0105032010b840362001030045140d04100c1c0e8400d00030101402c080100c002a03950154008900b0b48298125103042007002c21224440c51000501d802d0010211a02800c005508000c030300c019102e020342c45070426000740c0440062607545d50f0703a45 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 513114640 1250 513113390 513113399
    0x1d1e19051c050301032625021206130b070302090907080609090c0121020708041805010b03040f06021b060c0a0e03070510050309100f0603020102013902120f04 70
    0x201c071000821a51401d2240c203550445d1101999003840314055880c13680342000c6490541a070200752000520303a00c2086601e2020f000d442c00e12000600000c038050240880115890b000100300b0741d100e40c0c120a5500320b00f1140f0303120030386503000c050900b60070705500304039070803e540310074012a1048807035480d4590355052000034007094035401041d208458000806500c001e0380d0001348014501c00354860801e2401102006200074440c40c08024810741000070002000b103078a94940d20403c46960041020b0383ea500c1820f0000d11003140c0003071091050310303403050005002c0e5002e40651040941005800e140270030202d0320380102950321614484001c9205044294013102c0f5404068064001e030030f04510f000040742125218401140502c41d001c000611812820814201c0c040750406c41400004201d03d4000001c0011b404207034015424a0311712a000c0c404461082101c12032442c407140d40320f8450f18520520104800480d08500580d049000c514000001070810501001030065889290 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 513115890 1250 513114640 513114673
    0x5120c0306011214010506130f06020a05160501140d0e070305010b03011d0303060904050f03130303170613020a090302090a1b09030c030305090f04020a080103061d1e1905 75
    0xe5500f24070380b90741000382900d00f6291504019044400c252401c6445400d4a0700800701c0542035040914003100140d0700190300c84c1d000a0042d800c60140050f20b402c40b41d021045500702c40f29018050200d0741300c0110b609181003000c0103002c3c0000303581c40091142c2c8010000c90070403406600aa5680c0c0d15200b6100b500d150a1140c80b00b01c1110076808402800c0580b009a2640001487d4601c54a024000a810700c502880b110030104400c405a039620018401000f0a40d42240010350005100d010500f401c0e2103815400c0d40281801001000c0b42104042c1400c0a0350141240c4010810803900000058a0f00312455009505509011600e040300310700b0b00c0000b50303000400800300300c526101007000c03420300380c105c2090f01d815240259945041c64003040c0606e651100d4135411a10009442459941c0200070ba4140c0303101300000c0c0101807a011744030321003806481040c200c0390081c1e1403880d01107401c44210307071910300100181e039030000c2401044c00d610700140f041690035070004040c00050903030 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 513117140 1250 513115890 513115907
    0x8280216061a030a0f02100207031b03051005071209030203040914010905090601151101060e0f1b0c1f090c0329040b0a05040f0c0816050a0509061005120c030601 71
    0x4043d80286154071290326031244c16003010344080c2c09118580b8404803098030034042940035540105100d4000b85000184058030000b40c8010746041c00341540071580c40b01c60780100c9000d8401d030380e141402c001540c2c1001005100300001241036100401c000240511680a03020b0f948000b5107a03d4080c2d8504140d4034103070355004205901c180c010000500408000340e404c82010107180c50490207881540540e140100401e801400701501075900f0402c03544024021188520910018080c0301c541c0c4010b0a1068003480310140150f40101c1030460000015004140c0900003192021509013181d80300c51004801941080d10081e400080c5050001700982d00344889281c0c0c105805950b1400e521740c411450f80c05070602519944841c046170920102e00f80c0081020b40010390600c100380d81e2080c240d51049240f051384008000c601340011180b4092425000300c1d04082d000e080ea55a50504101300c6480e038081c0b441c2030000a0081e13040c0e0b00c2c1403d40480c81071450100c81a6207041003c0003414551 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 513118390 1250 513117140 513117191
    0x170c011d0a1104052e0308031819020a06030f0609050403020a03020d0f080c07020d1505100602030f37080402010e0d02030705100201180c14010828021606 68
    0x1418842804818031443c45081c5900c0444c5c900b0145c0a401045d00000300785a580c0064083c44000c024041062195001c00880d442c04008603010f070080643c480c506040b401744003941c040d0310301c041040b00a01079008855002e40204001659a4a035414901294410f9070141e0040c1c1c4110745e00b504250301040341c0320489410b4200120306124a010052a10380f00034825030000ca4045003600840d00c51660710395110b41d20081003c10004080c0d0b04900400088494400e0148542030018015001008440703025621a21203481d0907102d400c6ea800001c1c46000c184040c04510002d20240310002c0e4885899817142d030f44584082c1441c1c00010700c621440c5550501c15000707400d10400603500010180c0407594151030b150110b9060b0107050b0300401c2200c070034000713a2811003a2441000681d5001c401903a1200307000b00101015031004556000c1c040f110101e14600c0101e4200001008070b040d42900c201d0880094646207214840030340c2ca0550081c2203500c0d545a0306c102c1100d82001c015601d126 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 513119640 1250 513118390 513118399
    0x213080c03060c0c06010303050d0906020304030e19050303070b1308040312120203090a0f081605010912030e0d08040c091b0905120309010327080a03110304170c011d0a11 75
    0x100c2c507000117440e0300041c84010140000021007055140d015000581e040f40c10003021500e03440c042c20094180000c881b4554402c0a4000511503010004846003003030b00d0014004500344941647c620584080281c000203160402080036400641d0341c200400186109079078170365007052000c1014007521202c0400113041c0f40140100140d071040010071035200c54010701003070800950b5003040700251043c9405113080742d5a01120f4428844150014920729101b10355034103503000e0001040b4201c549820700e2480c030b13401c074100a00e82d4a00c02c50580350454040c012500720595034050000403203110440c0e44102806c071740d4000d8019904019008010003054494800f22140c40000d19101e205030204d060605907121107480140c1035820154021072404010503100c0c1180d0304040e50700360801c0701c1031400030b41080700540c100b00c08082901c0c0100e6000011052000030400c048800d50001d6008a04d60742d0b031410000041581c80026802c019071500c00f070b0074009004e04140984204009505006 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 513120890 1250 513119640 513119647
    0x806071205070e0303040b0408121e070c081501060f020a0b010b0a0c050d03091b030506010306180b010306050114010203120601030c110a030518030d090302130213080c03060c 77
    0x10540100440d08500110000001c0c10340d560780c820b80d0800694007849405102c0032a002c907540502074000d005031407000d422101d525100c0d0b55140110f00c500350341c8140e1000750340d0304101508215805041802d204d2101d480045803a42821031900c00312240e2000e000e0042001008100e4012001050a941c2440601001c1581d5152020181c5044c0700f80b01403181d0028908000600c034200e803c05050388582503500043d010000107010308240102070b116140b08245900c01d5500c0c4801103801c0340e078080090540341e840c40e1501c00007046082c04800c0008250030494001580d0707000c80e03a010710301c1a42c00040b154140207410904904c0001a18150340c0f00700154124401d0f80c08940d0b03404a024038011440740d5000e2000c9032103d00b0000d0011561103100f03c080d0070035030020090f00141c0214460240c14103041400c2590307030002680c081001c151000300c14409030801204048480d880700d0409807a06c03002c178030303842f003402280c1e03010352000d801c500b1600c42940780612009030003180c0c1c00a480d04 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 513122140 1250 513120890 513120901
    0x302120d0806060c01060512011d0a050703062007060501090605060c03120702190818012a1b0608010e060306460b0f01050309070e0a0b100f02070806 66
    0x8010700290000703214075404035082542500075040b820240c24050b05c034418000c90000124040c0c01d03c00c03940b107018411003c80f540c0c030f84800207150600300d8101005201481c516103c400c024995540f40729103003e0744802240480701c10743d0080c40080d115260000c2c0c55072400300000119a002d03000340d4890382c8100254080c100001041e100310300030101e0501c106846035034060b41703001d24421030103510042e0300c4146020f100d0008042d00c034610840d030071840004003c1e00116103400800014003100b40ca1211030841c1002801001140d0900c944021907101e081a00030044e03000669200c1000240d45000602104107501146c03038114606400070011824101001e200d101002548031100040d0034000c20449450303007483c050380c4510195540ca0a00e02d54100030080d2201e94049801802c148904242c694412002c4900c2000440d0240c0190742c1400c0886180305405800210916110000118241c1c0c403000300b400f003803009444502e0700e200c0920004c0c0c14a02d0301d901c03110840e00b00000f04007 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 513123390 1250 513122140 513122147
    0x8060c040302040f02160c090605010c020a1707050a08160b0f030115030f060603050f071719020706060609170a08090607031101050c0301050a0e0129070b0f010302120d 74
    0x24140d0340e040300d003c44c40382500e860300380c002c0c05090705400d6100c90400849043c0062542c62600b40c481d248802e0018a03112001543d607800e040038001c0d0428a0b05c1010446522000b18803101e1864540544a12541e6100000c1480b51240c12801e0240c00c44080c00c20f08800800907070000300154203000381032011000315280c0a010502c159902c5d100c01e5182200064469480828070040e2107a0804c200c944540f03004000701412110820058410400300c0d14007400344010f4442c0e4240600b140089030b4402402c00300c0703110681020003805030248500c0b000141c041c007681014083c0c2c2d50344c0b10101c526000c2c4131414562101e01a4150f50003103219840403640910444000c040e00ba00d0150761000d591504503402841c103010809507510b070038140422560268000c0d07048070000c441d0f4643c5242c4440e03000748a00803c0c41580421985103104000c000302408100c880491600b49160602005480300c0c10407000482d0300441120140c0e0040c0304524042d48200903010010000b0500320250b06800b4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 513124640 1250 513123390 513123397
    0xb0904080405040b0102120c060f07110604061d01050a020d150f03020402130503010911040e07291b03031905070512090313060c051c02030f0c03040b0414010908060c 73
    0x11405941c0f0340c8001345032030b4000c20210111080c188002035646040c0801180c4800301540c2603c0380542600104501c1842200d080214004a0003e0111510f5656400c07000b0300c0e41c4405261380b50885000301c91114021f00c51503200c1c141254015039500550b80c03150301103850701018510714061071034042c02189003103802c100070f8a5054400598421112410403011101940301e40d074558200421b090030809100e030183c004800c140c0e401d210008882854a0325401c0e0b5005a0710b0084545030003126102c0001e9100310440301300d41c441440d20540842d80c0300700c0601d41211a10035030002086c080d8101c0309081d1146090401c51081005d4245688011f00d9031041d00e585e2003850b0080000710701030200600440fa03041c682403200d281750b50b07503031100035100125a0800303448034040c9038034018480a40350120a1481b000768040e40c0303099440c021b100784d10b0b04aa40c82800c0b9120500000c15100c44040050000d44107400000004010290005042c03004a80100d0101d070024002d10980070074084c01d5 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 513125890 1250 513124640 513124649
    0x507060906051b1e1c0e030c0607020414131104090b0601030e1005070c02121b06030901020409111210050307210b01031109090c03190201170711010b09040804 70
    0x241514805108810316058000201074542800e000300c80c0154800040c130200200721003085051790915590007a180e0f240351500d83c0d0341680190350582080e00d4000001e10030184000c1c0000343c15842110010032221045841c9105800000a688284042194040120502283c0038030840c802e9a032090784000300a0300d8070703061648480820b00161010700110031945c00489041141d0724041000a0010684080036401000348800302100c44001007486040381080e4601c0c203c41a0349181400034035400201002c4095500b400041501c01d5030780100b80b041c80b002d501d00d42c1c9a034140e00b909140950040c1c2442c44d1211140f40411141d00c0c08200310003107842d00d5125041403001241618005607907a1401423040140380008410480306a242042d01401a030310b48a607a61501c3e80c00d1b41d212541e05045034135501000c2d4130307020030070040214a04a403061408030b9400307043e00c01341c1c8a940d0007030707842c0707004a901140031018a6502b4462002900400c481c50050703403c00352180d00c418803c5006 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 513127140 1250 513125890 513125917
    0x30d0e0a021c0f0b25050a11120a230d0b040513021809160905070f09060e0d0c030b070305090c0330090909010c120501061710090e0604050706090605 66
    0x24041d681922401c0000e8090106101c021208480c0080403640100c000360007050712307108108034541d8001800c2c04201d42e0485818600301c16048256a002591510800d032030341911007403403030581c0380000b500c035081549401143c0c0a002c0e10400c010f0f076500604800c0c01c0d4802040c4000940c2e81c42c50480303421114030107194880c0c5c0740d00603d03500f4900c100000c95601d0714802c078005084584c5a01036031041c2207a07030b50000c401410f0b174421950f40c80b541c81840c001400300c007100305140c13034a6220340c0326403841180b102c08555501e03a0303151005541181c480010175910010805040420302c80b08400c1c0b0011009130440c189108820039025103054180c562005d00113002146901d540402c0b5821150010200300780c9207014a0440e0180c80d240780040001120390b071044071845403500a6a060b60403d840300c0462840710f1101d002400c4006001001d40c014034280054045010b1242025103254a030182c41c0310f2610b410f00d01e141510a0340104100000c01004220b142d40c0101600c50101d8041d1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 513128390 1250 513127140 513127163
    0x3030711060906070b0105031002040b120c090d0503030f0c04051c08210901060812070206130f0b041703040e070503040f02030601060f0305070c080a11030d0e0a021c0f 74
    0x5011940c41e000303400380160008000504c410901c011454403c3c101c1d1812000c6490817404000440d00ba13015034400c480604030f040c841c541c0c1d40902080300560110f1900125400c0c54138000008241601e000300c02d07540341e04008140b092004a0000c0d20354002c2c07600ca429807500b46044080f0b014441c500b107642140c0240603143e20304010042d011519060741164101c4100b007101083d04401a0059410308071543c40d12100045100d404182c0311501c0c20020380301c60a00c40c0a809000311a4489048000e0000c04210042000c220074414000030302883c4a1494445090840e0182c1d10782d1414200302c050740c82070000300301800312101c4041d44070100e07282c400d8480e100c500d001002810b803600001d50601900c0001303d02a9403001c240e0304031095503942031015031503450066a40c0341402902a041c40d00030080742d01c1039405101c0c2103035021140e20807a481c0c561a07910940803601340c2c0d82200d842e5000302855200350b1038400411070301c0100e9250a18100850356440e00382440e4000b00003800300310040c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 513129496 1106 513128390 513128423
    0x10c0206091e0c060a02101b030b0a0f2d060807082401031d030304060e010e03160b07051902010605010206091926040801060e0a020702030307 63
    0x80003030f01000d509031003849144ea02131030708070041d84a6031a42e039008003558400c0950005414007124840c010300c520042c19104c0a400151240044200501c204903041911900300c480c1c0f000050f00104811032840140c2000b92903603402c10180c40c0002072640e801c40e007110311400c0c40e40e44e680c020390b0790714040040c4031142c02d42d200d42c040400403102800b54081d61050040f043c54082c1050340503c20342031a8a580c0c4212401c884640c2c50399002820175009003c2c210003040a000510300300344081d03211014402d9682030140c640c1c40d498011846040c01001280c0002c0040001100c040c1020712002c0d028108604c1aa40103104034400261281e070040361661880300440c1d40e9500d5030055448820400043c0b0b1450507414411a9200c400c5002142c000c00007000d48800105007686424080001c17504020410f81d212801000000010b98021045510165200760380005d0346100 = true := by decide +kernel

theorem cover : BRFrame.Cov 512949640 513129496 := by
  have h0 := BRFrame.cov_init 512949640
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512949640 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 512949640 ≤ n) (h2 : n < 513129496) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
