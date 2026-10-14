-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2003
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:25:36.961437+00:00
-- url     : https://prove2.me/submissions/a1397f7d-127e-496b-949a-48b384d55cb9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 360071942 ≤ n < 360251798 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 360073192 1250 360071942 360071977
    0x4020a0314030409060b39060411090708010b030c071e05150705091c06021216021203040b13051212011a04080334060b040c03230c 58
    0x200307406a0b907544207002e0410281d041250008010b440001034403040503c0000407003090101c0202e6982c80d4001d01d0040090030811201c0c4000a403080c081140602e005000c8141e91510800611800410150524081080400041028198500942e0f401002c2d1010b115501e16190911139000000072800d0060100050401c00070400d000800d030403080c66009400d00182c1d6422002d4402c0d0041c1015150843c0103c0500c80c80c085050402900043c800c050060900c0c601d0303c840300352010100e0710035110f41c400103098a1080e40402494003a0940394104c586585059612516a42c01c01b90492941c1d00c006508202080414001514a9510405c50307940b10807604c005855603141c28440c0c9400240c80340d41000000d22150222030540c0d030203000452601a20401a001d507000c50901d446880c18082800c3c0381d502004031500207100d004140200302c1c0020041080210740c10440d498080c10b150400110304d592440c80a20041520320140516550f120088011240709924000c0e0f03d60956 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 360074442 1250 360073192 360073223
    0x3010c02281a011412060c0f030a1401081608070b07120320210403020307031809090311010506010903020f010507020f03060f0708010b270301090b0702031b011a0904020a03 76
    0x1c161800070045400c17a03806031141d8011103400e44071902a2103007810040304100003011880110300441d0020b240b503200040d8014110110800f0680c00c0c6c0082e810f0741c103d050816102c10610103040301a00051003d020ba1600d0005804201d2007080d038014084024941489200c80c040d90001c0c5207100351001030f00c8036440c2080102c0095114510710300740d03c80450521302040201003e114411549a00154078204542d10155500d22640513100042c0b14914400719030031015000b1003100c0351107600d4500e10180010b031200d0a45400070051410403180034030400141c0e540c10b104200f003107406e0900b0741c0d484840c0e0010595103009400c102d6010300c02c48007441301c1d104820403514424a5103a503608442c2e601e6000c0103020744510f21030f011080d600c7e500e407041c1010084501c2502034400400000d04016181d8540400c1d01049074031102580000c1402d071701c1991244420b082d04d110900007000188200e080f502c4498034000340c604c0c010900240000c045442d6000803501540d048080d00f840c0049 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 360075692 1250 360074442 360074459
    0xe0904060608010617100e071206090b09010b0a17071a0307080606070809011d1906030501051206040b07030902090c0a03181101121b0e03010c02281a01 67
    0xe14840d509070780d840d140d40041c1c64441402800c0d0000d80d51005001e80310301c86d036040c0300038010381554102e0502480100090702c000c00440b0b4a0b83c03510401000c40c40206a0415444004006000002036414003a21090350f96441603c00140d482e0020012014900b405000d443c0041c40c0c2c0065030485142c0c04124448520a40603612800b0300c1e960b0807042d0751300c4005208003400799180040c092041070000740340d60340c050003142d188681d00d1a49061b80c2200c0e900002c160011310000314a441552040078000380c1d625000c0c0c280907110640d0658000f004038801039a8807a0010000b90104021001081e4464070a80021181c0c5070010004046030074060705030070386540f007500c4020202c2d24100c03000b1510000085d080980e55044581c41c50300c44450801503d9030724a50819809540da5104811004002020044c000803c03c2c0d07580d40c0075120301000d01d803c6895131030311102554081034010601400802502c00202500491520f444280d0714024000810380648001e03503184540010401ca01b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 360076942 1250 360075692 360075701
    0x804140a21090b03041e06020a08090c09010815090106030f03051c0912050306030f030409090320030a0f050415030c031404020603070c022116060503010f12030e090406 74
    0x441c14800107030007440c036920a88098180d44100010400180002130100d4090340030480c028001c10411000c4800ca6920407007242d21a0884d0404981a2814807800034804c02025001e0b43c1c082c1c4201d801075050402a0760795688814007041c80814000000e50355100030340151008685c80780717001503280390a00d0042c0a54000780c0300400f4405280c4561812000b45000e00600580c0010810340c00c09201c03403044560f03a000603c01d54051140701c003144481d0070104000c3c4020208000700007071070107461500400d480b02402a0a0941ca410861810855004400c684101d41a402c00c04e85803039400c038080e00c1601890707100d210245a50041e21502d150940c00182902540d6981080b604655841a1501020075980690000d00a2000804240c0103034209818940000c00765040b0441122852000b201590703800241a04102070003203181c0d030b0610b4544050025800d260341158140459030320110700c1351240101c1d203252890610107060144003105103040c03025090000c01e15150902002a0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 360078192 1250 360076942 360076973
    0x1209210203030912070c0501080c070f0c080f0a0804210606090605092d0c0705060c0a110604030806010c150e060912160b040204062402100b010c030804140a 69
    0x1402900b082e007071482403904c00c45005c02d40c0101d50618003801e00e4011a0618402044203104c4281002501c000c100281030480c85036201d0540c0d240b155003010b65890030002164401500c2e5030040d01902c0000702418152070a803074003000c12807110440c40500040c09160000040d145030f29214012480a103150406020780d501502c4980e03c0e51182c5200104c4200d018188400742556081c880507051800e05207d90170a0f0118078940c141025500e070035040649c103035000703980d40d94002012462550420106159030941c2c0b070150549180035200130386900d00042c4200d040120222101e810003101c070041c07024510526000300001c00707401f41c025594040540300c0c94164031a41e49140f00050042040f502070f82e0b00c080c400d400100300c030756030600700400140080303070b2060301e4030000b00b01103212400341c490310701000c40d4000f00501084000f0341000300c0040d00c140710340c2c1000c0c3e0440c030b61398010703c250f04856414941825a941c2c1d500741056900140e8402c801c180c00784425400c2440101c0b400035801c03 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 360079442 1250 360078192 360078211
    0x1315150e101e0f031d0f0d05090603010902090303070b07030c0905041e23040c0906050604120308070e031606030e0303101205010f110c060a0b01120921020303 70
    0x40386100542529035041d07501e6004000c01c482032690b81c4042c4201c60395403400c0384505000c942141c8420701000200003e580d200042d501c145c02d01d04805904100b1441056014201280340c01e07151004140ca5200502800c3c286d2034000600d10066282001243c541c150016440100c0d82020304004005e05107010440700010030300b03040428185464860300200c4120001501542584155904003801050410300f100940c01e401818051007045540c0d0302c624401d110500403981800304800868140b9081603006640a0006121141801e00060b09050301814540c03116030722140125820300fa80040b0503058060401c002e00c0002c008415982902d035203803001d000000b0440340055582c001180d070f144111200060401c59011100c03461006640030b0000821401c03c980c0c902c60903107100340c01c000e100c03245c006600c5e21000400d000c01074000e040c40e41c0c2400034002140008001d071075911000180030740e9400c40c2a003008946e00e64440c1c00b211001c440115410348403406920394208850810340d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 360080692 1250 360079442 360079459
    0x1204090b120c030c010f180b090310020405060301031112100204230f060f0f040f05101e0503061c110a150903080a11060907031205091315150e 63
    0x7800040450000b07015074025004012014500d0b00444200003110038404c24040491418170300c240071220240301400190103001d1b40d41014109061500380044080b40b9014030612090143e41d40d40c00031a41180d4000c1c07442165440d5207000940030149440303070720f42d41e41708a0b400b00b00c8159258001d08200c0701004150040d0710b610622440001d03550310321065000414000403941403030808013904614034030103400c07424044102d80801c0560720640241d9444010100200020314140341800848601c80c90000d55010313584145150030a81e09c040403052040210000701c554551503441404601c020640100b04a9a81842e148940c020020203001d46800308011802c91b000e400040c403909425030341d03460720600e55100c2c03180540140380c3c01010000401e107003152800e8104400360244d91020081e102d140c3c03640c03602c240512602c03500b500903c81c0c1480300345580c1d61040301100710340e100e0034000300e40e00321007492140c04a00c80f0303040040582c0e044501241c1d401e13070102c0f180d800188107440e05070 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 360081942 1250 360080692 360080719
    0xc240e01060807350f070801051603090308061513060507060b0a0501081306020409060611010c0f0c0219080111040305061302090606090114030106110106052b03021204090b 76
    0x41c040b01c10740552408102820380620f0020800e84540b0841300c0164251141c030b4840409290402e40741e40d00103004d5a4440d024000460303070503c1e8106000301036090401076004a581c02a11003000109014130482c1030695000310388103440c04403681612182c4100e1407003a1541d04c0030700a9000f11f20705441140c42d00a040045040c00c41420041d144161500541c640d40c0800d01c9040d1120034008541c140c0d001d002c0083c0c086003034016540686040e4598071580e40009200d40d08660a4941c072030b00b04403400201e03c80090b0003012144006405640500c0d092000901501c1c40b00050717031110580e0340c45e10308031000d5007110601900c2600e200d1002d031071a82e260907243c04154042c084000c0d51020000002c00c8040c50240000c0c0907040f011704180312002c0c08403802d4911a0000d80c025804240503541030702441c0000c1c42020094101210780e400c5900f068505c1210b20038000d5004202c00120407591000d050003002649484100c17400450364641d103d007060000341241002448c0200366515419 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 360083192 1250 360081942 360081959
    0xa03060e1602190809030105071d030721020d05030a270e18160e070e15040b07170301060c03171e06010e090f040b0c0a0c240e01060807 60
    0x8505854070342e0007040f14060340802d80c1e0000b080642c080f52003a84c100201c02c207988003030007143c0c400e400ca902d0b0450107000700c10008940041124400d4800c0e04042c0c0144810750500c6040c9020803140011100640701c40d101040106c0a100c0c00030300b0a12003c00c040c01d02c6548a80603004900e0102c8135841c81101c226070201080d0780034080d4420b03010101c80043c106441c2e2003c1401c0b940390020454410f00400d602d080118034054100c19450ba03141420041a5901310f901003030300440688080c000e019204600780d11500490041030f0300d8650020301c6000340060014800c4008442d0400507030380396502c000103401c8100058040b40401c80b8002d00d602e4103e00110322a00c9200c2c103000818070701d40415081d203c01d0700001c203924103100d01c03428803a0254580341005c62080c004440d103a501030030203003014000d944000305035114000c400c01102003025802803612040301d43c407403d280c1080740494042000000782c002200a41c03860040703000c82280c015001482124110016280219210581d0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 360084442 1250 360083192 360083221
    0x90b0406051017070b1c020a03050601091203050f300901060603051311011202040e09010f2c070e090a0c05030102091008090a0b0c03040303060803090a050f1201020a03060e 76
    0x2401c00c0f64004034010400110a1001802c102440041c01552861513088000898101c0c4422800081e941c1082050341d507004600c800103031002c66220f6a140c4c4003582c0040070791040c940507884a00010400d0341c87c0074400711500c800340380d010500c0346036044030188221070310404403440400366080000021f5114002d00c00e0034028240ca10400c042440162a0a104103031805c3e1103604210142424102103081c2d1700c0580068605581d64421608040007040d082d00d10803c040c0b007581d80340400601201080c28401d9114031202506405140031600e00242072112507486551000458401c02c40c8542020444181e620301c600c0e441990240c5410030700d400c038058030801d41e8001da002804c036544533000342c90090b80700d5200001c44d4100b0410b581d0b101c03d140c6082c3c840080600020082c0410560540558805848980700a40c01d04028070005800e606407032140300c0c001c100c80c1e4241419a00c401c03c0c0d440582140e200295500c03c2c2002004008010314031401003041000e20124002d044510327031 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 360085692 1250 360084442 360084479
    0x4090b070f0c1a040f051e011512170903030f03041209060203090607051903020a05060c120406020c030d0504030807030b03070302090c0a05040f1509050414070f0201090b04060510 79
    0x2401a1112180c042c0c3c920400b030160042d612650759488410000e402009a410807180d040c2c0107000c0002400c07030150039100196885d150641044000744000c0581c0c1046164041e0010083c4d04c5c15414569030300602d1080e80c180d5900340c003001a43d00d4041159000450150b0301c00d000d0410001010341c001c40706070010b4000c10006800070800c00c3c003141f034440080e0081e54083c80c15200c0000c0c407100c05013003042e008001200560030400e074040c00e008040c4059680700391036040701d500d80315a03034900d0840180010001800c0b80da01203080d41141004000380c07440c4031419002040315082604019100309022102040001d040081809a6040101c1c072502102d40c040c002030307180e440d241040c42403a0014400350040150611000406c810714519080081015010940c5800f00c1150b0080c00d08499402030741c091420040380f02407aa14024040703a011150349000d6000c3d64440500301c1c090074100c030300a40111000424082848070690107a4055505040802a00b9a80303c9005070802e20220 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 360086942 1250 360085692 360085703
    0x15031003020913050604060f0b03010e0d031113301b060905060306040e010b060313051b010c151e0624020304031205040f091d3904090b070f0c 63
    0xb8041400070750103070414540c008e9600400705801c00d00e8000b090844076044419542c6901c04003a1040c007942520680d081d14030000c94561a128602d80c035040d40c44498440c8980c02000651100e16890090301c9000c98442a00c0080390301c5440c50400d05000001d040c540d1203400c032198000524170f40107041e0301c0200c4a0141901f0700b140e840e0301c2004001c2800428041140d52140780ca100c280d0360b880d008611501d10601d41c80b80061840c1440d61030650000b11b4808403020103041d0740302d66a00800c03040d140c150f0180b0315105611403004040080c080c02201e45c0089038168078000a05002608200701780c50056850114000c4525404583e00410100c8407000d80c00421091000c1400840014014100342c00c10502d8030fa610007401c50014056813040b2103032540c888400f00c1003010f03001000c2c0440d0745803000345024102d0b254110046440b61115000e40013410940e0003240c0c01c410302d181c8203058000c0c81089904028107000194800443c0e40380002a505074600704240e006d110307070042068202 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 360088192 1250 360086942 360086953
    0x251701150e090a03140409061d160503240a0b042904050d140a1406070c0c090b0112060303020d02070e01030c050409061404050f1002040e0c091503100302091305 71
    0x192416a840c0000c244a1170403914104400710780e0541c58001c0d80300512410a40002c058403100104c551800c010b4480344148640c842c404070b05070341c00019a40c200200010427250302031702054002c42e040e0030070310140e0007000d0103000240d91444200904211032460702245c1556060098200601500d000d041c0300402d0144130a00c1b903420240c400042d05c9100d442e01414590300c074484540f6180d01c1b2002240c004081d003410f0000710005000081d002052410701d40d19804440da80e41450030018000c00c8159543c60720521004d0f0311403401d00c40d1500302100104281134890400035141c40c20b2000340c0000d40304103080060110407485865049070340103002030780501d0511040001512140703e0a4034501d407138a2525640c4030703028000314000d40c4180003c100b403019880c4880d0401d80d00301c0002c40c2d071314418041080f04c8401c4100250740281c580d0482507440800074000ba0300c4004400c400310841c00e003c406c00000d016080d1407007083da0f0080300d08242c19500c030404a22003012070392000b031498000 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 360089442 1250 360088192 360088213
    0x201060b1e13080102160215090904120e060d060609150c02060d020d020c1606030e060103020d031b05060f0604020405013c0509040e010608251701150e09 68
    0x40e1014100c020b01810400070420b540d088078900303a0704051500c0340c0542d100400c1350214940b400c100c901d09105102564101140c1800049107030800401c0a8400450500a100c01503c203101c5500b80300d600a241d2505c0300308940703142d0300130304a40c004e8101042081d03001248100198405010516155840140d00449079092245070380085091000c0e441e001d1213044c40001e50307070014040b090031603c000c04440b00c4942849a0300c03440b0b58481e03814145040b0540003029004210681902e4041d54010b060148a24080310100728518645590401d420b0000c400c20001255850141002030311000554460b04100001c920a52142c94086040385c54040343d4600800c403e103005418220150060300e03041c007542541051120301007c001000001c98804514191280c5803c0350004002000031a0500d01c1c07030fa555035201c40c1320505001000601010007139030300312100c1c060114001c0466540c0c02400030140600030803028490305040185010440c000b840e105175102e4008040207090a558 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 360090692 1250 360089442 360089497
    0xf0305031605010b120c0a0504060f0512030405090702030a0e010e060d181203140a06080613051204240212041502070308040e040b130203100b010323070201060b 71
    0x14500c0469040d52102c03c4422696a00340d200c0d50510700c102c1c042c0c4203842102c001c02c5902401c62304002d1080f46004c405003c138440180582082e40d8040e129694003403180c2000501d14043da61040354041c001f5020032468640c04400340003094015100c82981190302c1c00127568440d560401181c00403400d204901c2c80300c19980010006030241815080544d000e030b111076203808000c03120f5501080e1506030528081100303034111540708100c1c1001304207081c1407802d8030b0748510000d854540c040d00800162000d005050010040c1044024201517a503a40d4550403980b2800000b550300102e16044040100280040781550306030044403210344c90103003031030207599889068144810451050540c08800641c9410007007005d84401040fa41741440d0034070341340d0003101e03000b003080c035440c0f0b00001c1001c0140c400281002d4184691040450550100070048000300744444000622040c100664214061070000e034a010f0040341c1e00034031442d0345074040c1e01c41601c521444d866114107200d04241602030b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 360091942 1250 360090692 360090727
    0x1060e0105030a051e0c03010f06020703080706230f01050406121a100806010e09161d0402130c110c01050c0c060906040e01080d020d031b12150605090a0f030503 71
    0x240c118200071401a40501a0300a80f001c1b5020076203000c0001c0103000f95410705031403070000c1800d0b20080c00c0703d50031070340ca0384918000c04c81c00500c84ea480781c030b81c46c00390f00100f40c034840ca00d000d01c0a550a1031801d0b4401c69400340082c440c0342d001d9882c001022603841004071350740403219084406426000d041030101411020000d15105990083c68400709011805200312802030090325402407a908040244c0b9080c841c1d03071042590990a000b400b00025041e00514030001814502c0d6984d0316901e90020440403a034010307004856600d018102034600d60000c501d411400f109404407071030080d928005503420701c604049590258000320b40610f051500c14024005103002800041c10281d407003003041d451420a070490101c6400140f244649140d04000181c1c64200900e0240442c1181205514124030b040800404010f40b9184018140c21160080b509002c01c0043c008401f540d00c5100800340e4002c1c1340031610408681c14001550100ca1912100340da41101c00345160a55841c010403000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 360093192 1250 360091942 360091951
    0x30303060905371103041b030f060c090b040314120c0712020609040e060f0a050f011e0503070f05040501080a03080c130504090320060702191509110901060e0105030a05 74
    0x1401c00c280902d005003c5004000003c8064050309440b4101403a1070254a0501103080c0c0f10516003c00410100e81407030142412a40c210344002815250b90314120740680c03654020002848002400104100485500074013180d1075100351445051581809099031044002008803580240000e0000b014010158442d0920080040c0d140c54142d2003c40c083e200c50222201c42c0e900506d00308421050060483c5900c030801201c200118a42001200c00f042818029407403000006284c00b032130600c505106401920780101150040c0d9030b01d4900308520001402801d019504200000402030f0000480750b090341c0c0d01d5240c541c515503525161443c15001039440c1020103143c0e040c0064a41c54510840004038041da80300c100507000c013198951800107140c1c0d0414191b01000800c4003c80e40400c40740d0040c01e0040c543e4100c2300031401c01090818044003945115850104184204820303220186030066003a6120740d400d030790b103a1059402c4400c0e0015207020070020400a0460919503200036800f = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 360094442 1250 360093192 360093271
    0x6071d040b10120207170a0f021212130c1806060512060105090d0b0a02030a1428060e0a061409040b0726040f0605063c1306030303060905 61
    0xc001c000e4641c592654a1454100c1c0f00c2d1b400000c60300e40c569403200340c215214000e40000e041c080320400389010244240300000c11403840e4400840c0b001207103402c40100c000e40148107131003c15202c1102201c0303404180c1c1d0f00310840c1e1030910002000c0340200199150b074000d03904c81c9011740d583c080045d20264000c44002c0e602140d842d44080000d01508601e50181d402c000c4010384924128401c1401c48807c0c440d80ca0a0201442c01c10005031280742e52001c883c228800caa40000d0b0b51111a4006030100e608224681e540e12800c003d020400c0d54480c2044030340700c0140802400c1e4003024011003440076900038026220000000d0102409140c01490b0300a00d845900c42401034283c044403510820340e4221500e030a26200e08083c8640303402904e07008403040301c01000300c640c0700c0300e142d0006020040035817841c9454169524106520310b05142c0d100400341c00901109085c86800c4000d0000380000c0b40031921f41000400c00452500c25684140d45541800d50907002003000d002001e100c0e540c03075845 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 360095692 1250 360094442 360094447
    0x15080a0b0a11040b120109090203030d0e011b030504050d091505031003080a05070b0a0501050d020f04060806190e03030c090d140d05071509050a02061b06071d040b101202 75
    0x110350b800c100081c030080030281046071315242501e01c448445031042e48170f10001c608003000c0c5405660040200c645c03880000d0000980c004a038031039a40541111000c0c00c0250114400c07201e1003940640005201c0ea1103901916882d80c01e00c8001e4171000402d01844c1c55010091a182d811940103600075034100706501c1d4400d4242ea0313280d40c1c0501903480706410030b00060010500504000c261030f68560080b00c4048127000d15810007010075450180c0a60191085030101e0400040b0748407944400090085142a85c00c0c0c0d291070907408285010201019001b2890818100c44400c0c0210540c0e0040804c141030903d0030302e1140c200711115441340e03000d540c0c024011075603400250080088844150342138a07110340724034142c206022180d8100240140342800d1003659030000b500422549600b65040350740070b880e40c1580c1c0d60741e00455400112824544291028809126004214051020b035900070031841410040c2c140000c0c1c610706044a600501d050a54009450040800d5203144a00c1c5a0060 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 360096942 1250 360095692 360095711
    0x8040b0c04150f0e040c02030d0c0509030106090c020f010b100f02030c011e06050109151b080a0e040f0b0f2413050a050102120906030c070b0a0b010315080a0b0a 71
    0x5014100c0001000400d10f41c04030300d1421a0881c420301826075080b9010095000c0703282019440b8443c1e1017031030001d1546c030310900801074015810380e11010301c054020420142c881a445005124a0070142c0140c4101c0d10600300800c01409150308411019240441c00c40c2850419101050400d1151080d400b0601ca154a03450003403080b28400d0303100800b403501030001180213800f02c5007143c024a042040c104001e10124141480d2940302e090a440c160107441440315602520041903000108007460015507100601c0d84506094034001c011202000040031000030f500444015207425500003c94805034001494640c0c07012112512401020181c0400c910b0100103131b520400200c40d288404080c10b00481c01c284110001a003802e000070a59201203240d0b02c0741c40d000c0c050100f4416240000043e1850b200c10b020388002c9640003010b01400d0504060300c0d4098801a00060f0001c3c1c5060000c103e0682e50200940465000034081c0280b1030b995240c030030030020010f02c80c500c8182c407070314410b = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 360098192 1250 360096942 360096959
    0x105121504230703030e0301090b010e100e010608060a0b0c0c040b010216030c03350703020709020409051605040506072019030c050306100b07020301060513150b0a08040b0c04 77
    0x32140c2000d01c070302900d015400e503d00500741c10061b942c55070090303141407440300004445031080e60650700001102190340e51026042c240038619500319190300c040d8400001001ca0b00401c86a000c1c0400b1249200a00e0f103626803a44c15010b0f81030407a02c1640540400e02c21814268043c1600340d0781881602c0040b400c01c0c1070003000300382603481180c1140001004005001010b8480d0b403000c0025070085000040214100321200c1c3c012840f0b01c00c4000c00220074003014000c000c108024910b90105646541c0d0305c0c2c8100c0c0007810112142d03403c60240e106c02c0c5600030720030801c54007601e1000b42801c0c105201a10b5101d075104030841c110008a03c4040900c005549050034051a40c2034600030801060851070420200d12055000c14060703442a4144020785403001c4880c02601c3d044442d150703c2c2c88141c00000d0251845038052900061400a0035410312280c0d00f0011010b100c01d40419241a03890041548502c07078482c0880001c0c0c074440102300000c00c200c130b45d6600f2900c84c0c5101e90800b500c074102e1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 360099442 1250 360098192 360098243
    0x20913060b070b09210c0a150209131103150d0b0a0b011206050319030519091401080118150803030a020421020a180f06120201080105121504 62
    0x14890444045510010020f03c040c03150b07805007104004d07145000901d440119040040d1140a545850108400041c504d040251001300343c1c21007240e00d0f00e5406201c482d002980a0301445000d14802c0d4940a503d02c40c6029424941c0401c44105240d6500d40f06452800c00d0250a1260711144031354644000c14041e400c00d500800030020001991040f010000d03068030000a072800c10a410090100a2964003040403081024424004242c40c0c840e40303801c4500c1d11404845814084641403030b400300c2d81d400303040303202551403e0743c5004e1405040b00c010348440384240715040181d845040045034404003908183c140b03054410311400d43c43d072a103201c1425070f0411214140c03110380c04074081181d145001ca0b0070b045056450000f5907541c1041c1c0100f0300740101809190f4104030600041805080554001d00c1201e060341401c022003070b120405461404a0b4510503800101000c00100d0300b45807029544000d0202c03e001440004944200203440b017800071320030754a80c100b5070100180070139400f00 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 360100692 1250 360099442 360099449
    0x6010504170114060907080a02030705070b070f081b04030f140703200901081b0a080313261009032105070212090f0904020622090f0c08060402091306 66
    0xc00c818841c10f11a1104a070000c0c64244140210b00600c000c007600300c1d510540112500d0400350362a6a03c600a41daa880340440c001c005060a000300001766900c6000110702c5042c030b968880d825220003c200d00c80103000c0102c941d9070318040100700001040302512020b21403190041c8044030304900152802c00303140c0d038825a1030014560711071002c503010120f0b10022400071100045554145849507984804450800c58400f1a02400103810354440240900401103001104c4d035034004c0103100d04406c00c00d48666004824045860711480e41c107001c0040c85244e0240080c044400da8800010142c5070303402066061001c28034030314603c3c000801207440d400d12042c501140360b00f4004d00c028642400c1248003002c00000340650b5050f96106407070007400d040c003206d84000c41d8035140009102c521800d049a443c0c004503a00c3c081410b01241c0c0380c0f80c11039241a90410440345c452400c00140ca9105031f80c140000d10703140008401e49020b6014284e81400640f0a2a00351650b68030b50088845941 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 360101942 1250 360100692 360100739
    0x60308040803031506030408120a090b07030c0e0a06022a10050c1902090a0b1512062128060f051512030702010e15070308060906010201021305040506010504 69
    0x410010301310004d0244001c13144003078400c18a98075282c2c032041e0381c9000b00380e48014402150804580b04007403980044941c075800917544045410003c07005001000d203402d032030001c101c0030b5107a41d0a038503210151004a80440d00540f01132070040683c6900f200080410b00601800c000745c03510252201e1702c40164108081c0c4902c0c0d541d0440f280b00520b00f02c04134490841260b9007940c80801a102c0d03a8140350801c15403600807800c84200c03c005821581c41c0c3c0b51544115101240210000c1c00003002a0300900007654045a4070303190b1a0640d650000d555003075881540042c181d5403826002040203d201c10700425501a01020340eaa141c0685403403940848000c1c0c6c0300c07018011044004110f41c502188d04640f02c0180341800b016030340c0c40f40209000a4144000c01003d4006030701d40e005c61040251510041c180d5500e40c92401400c00d0358241c801500421140001500c154014400c40b148868150720b150310181c602400c00000e40030041034241000014440014036201080034082c200c034001 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 360103192 1250 360101942 360101947
    0x10501050c070f1d01150c23060a02093c150703120501080d0e04020307030908070c080c01031107020906030f030a2c0d030e18090f0f0708070506030a060308040803 72
    0x14015a903c0103068000c460322810009614041581101710704040c9648840343d51841c4050200c0f511100c23040e01e140220380c1c003036001080f5004801d9802455040000c858207104020084140320208400000310f24425001c2095002101c1e0030240904400701d0051042e0300d07440480030b8556064010389011400300c1c040c0080b049410080d401183e000d440418001c10100c034090070010725007204101981e0146900101060343e40f446a00507510894018030066520b40081ca45034220280324030604805004840000c5034646c071070b0041c1e08d00748540421490409d01d1a4081104100e400340280c0e13454420800d104980034414405807204000e29140d220000c03c641102d10840b0072040e01e400c0480a910426103082d513902040350044940500d0080100c80340d10000c28240719000c0d10741d460914586041061000700040e5103607120a410003950181c1074440711040d990340c00c5004490886e0002c080500141c20020091640301d1802c440100300c1e182c0d00e480c0c20080e0390060704082003d4000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 360104442 1250 360103192 360103229
    0x3030c02011a1305090c0301020705031206040b150a03061701060603140c040e0705130306060305150405330a050115090e0a0507020a14010c110c0603010501050c070f 73
    0x82c4035041010303030601800364203404a00001503401d0404840d07500510b64410205000341030810040a1302200900215238550003400d0880d80c94100443d0010b2101a540000e03440e402c0c46e01500a8006010388000c1e00008411007440700b94000940c82d408265444c80e0000e80c040101c90080104010500001281403c0c5a0700400769950a8510130305000200700f88107101488100316030494446054007182d41e03c690b03504175110b101d01c2c009075502402142020051266540c4004c0440e8400c4045844240d00320040501403002250003910700d40100c10300001c3d06e120604d000c1500c42040712100e25008035198a94a40c1d0400c0d078204501640e00c0c00140041c5d000000048402e50944c200000054a1300a80400c03019004003201006e54440001c80d1110b402049a100e00e5030703108900d0700300031b20205401e0740280000c06503d40000d18400700b2038074040e000710344405548000b40000745144e08140054641d54000c020014161060080004099452007928805044500000c410700d004 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 360105692 1250 360104442 360104447
    0x714060d090b160c1208040f0b04031218030c1707060906020703020c011d01031a030625031107120c0503040803031f050108060d05071a040f080a0b040f0206040504020703030c 77
    0x40c004280001e000b131090700b801c04a40010b0300c000000b0708030703c2d00c64a00d40da98604050f420795204401084c101c4003070140800c054001442610b0465010b01c10003401c0c4000c14050414810844c019010840001085010070980f206200003941125046440c10001d0790361501103443c5584243c590703680c0401c0f000100340c2c2c10b100c2540f00510918281c200c1407c070032010100210ba05202c507050654a00c0e802d0525100c400c80d0200e22403000b802e485907890843d8002d035165416500c2801c003440710740c0c180c4600c0c130b000f8441c08485800071020036081400903030740d0090140310b19440b0400d102d56201c0b8000007440410090018014550146881c3e0401c28411191102d090010302140c10345002e080c021640c1c07040c9455400ba074102c49080442c5e100e4209507041c900244c114100c3c1c03000300da6110001404c5100107000f04c80070f11030004030040c0d541415540b210000900103010710008000b0034081104102c20203034860005142a1038555034030004bc04030f9114841c02c8010907241c0103480315564 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 360106942 1250 360105692 360105721
    0x1412040905090c180703110a020c12060c07302604020618190603060810111b011103011203080603010c2703020a12020a090e0714060d090b 61
    0x380c04000b80002c480000c001003c0804428041c213164189000141901d4403e410924802e40d600c0d00320355803000500d01c025255044000307003d00404002c004c0c00480c140c0015001e12070074000e41c05504114090351b0b0f04541202c10507052050410241d8000303e0b01c014400f108040c8100350b1a81e1038400e500c41042c1d10801030740c7c030100c1e1104058508220240e00e508048030302403282100c80110350044200040e030f10245061030400484841040481d000c1d4241e8802d4041d6a41e5204480c008480e040301c00c01a01c421103103840d038841c420710501e0040000b04d104e92a0070b40388540040303125071200b1607034502074000b41d2041c110141d141d1400000d06811144450704000300750f0007840031441d04134001d0902a408010200c5d01002d1240a00314040d095009001450340105440441079440c07024a010380300720342e8107a00c12440720380001081c140c14410003000001c60005080240c0c038160040fc0039902c107610058000d10204026580b01480b81310340844188200700c0d0f188542824440c000c20302 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 360108192 1250 360106942 360106951
    0x1080105101403030901030e210a0914060a030c050c06070f033806070209011502010c0507050c06031015031d010b0d020f030f0601030305070218060d030305041412040905 75
    0x10402e03003a150141c40100498401c6842800c2c08148456003070300c0a40380c0f01c4c540c0307803440d600700b900c4c04403800c0145260010160081c2d140d07a4034800743e84030400043c04c40442a21036901c00402c2190384181800798100c400c140015081c40c509000310b4a40d15410480c048030148005040c0410722074404d5058070568486680130b5914055801c0d0b001241198520341c856070a004a084551410440d5113807011200c1c400c0e0f001c2c044800dd03503514040c80c5000c0d11007003441c6015501300191807d040784a10b09403441700b40c0210081000100703110030b11001ba4030191126425141070380d07000c9205006405c440301240c68503600080d10491140280c0d400c580344002140550341011020070b45980c070401700ea9210342d0120ba40c002c2400075000040e281c001c014040d00914001d5800010905800102030034003d402500d407801d010b40001003004160500b1190141d0200c03aa00400010a100794425644184136200c0911000143c803481d0349070195034552090411070028040c410200c00340901c0c1e820 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 360109442 1250 360108192 360108209
    0x6031c27120b0903040f0801020910031808210f090c040e030f0f04030f0302071703030106050409020304150e0f100e0607050703180906030b06090c0f130e0108010510 73
    0x300d0909544049a0720001c002030415680440401d5042c1c0c03052003214010191034000d0140f03c0e40e22049035000c3d4210300e041a02c905400342071862214020b000c0c0e94500303a04039160803d103220658900300c0c1c5421a004007451805180e800360700804803121901e00a007250204880c9918110404501e4921001c82d101d016606015004401203000425182041140c1103440c0d202d994030001d10415001d10f034000740500440c140000140b580119035041521100c10844030100030480803907a59100a21410300090800c0208200c1050181c2c05541c1240c4200505082085054903d40613944030020004254100c031117403402d00301040211130407980000c81c003446444018101c00d0385400e8014000014020005a428201403182031001c1c80140080c84007084142c60303404a43c018802ca0108a82802d0080b01142c5036150107a0380074801c2c21000361051900340f204584c961241c0100c400c2c04c1c1c00048940340400d03950039280d0707406d004c1c200b021700005442c81d200000364410900c65008214 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 360110692 1250 360109442 360109517
    0x603010e010e1e16021501092403080406030b01030917180a12030c0201120f050a0b06030f010303050d0603080f03040c050d150c0909050a06060f030c08010e06031c 72
    0x58143d03203403055001e1003291541e00c1c500342580e802d0b13090440c1c4218503400c0c3e081c007400206145009900c100e85a0010324001c44802028090f0880040c1250101501c196400c1c4002c015881c440c0e0440199018103250110303482d0115071318040051009100362040c4200820150481d45000f403018503140c27001c440d020000342c40c20102c240c007945841c0c0040d040010001c00503080d64021126040050170140d0101710380c0d98003000c1ca10040006a484409032414080200c00c41d203404826640a08046c050042c040c1c5d1940d074065031301e680250440c7c2d29150302c80b04000f0205101d000030701030032503d8022866403440e19190203007c02c040ca4102901c04c0418888207030100d80309242504d81c01c0c0620000284003692140165004d550503400b4158a078208000c2202001198100000b1205c194036482c91100d614507058096403010101000007070942801040085804201c681c2c1064010b02030712405a494100103034406003035903011002c98040c12500c07181d07902c8110022204602d114001c0b0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 360111942 1250 360110692 360110731
    0x3030c0509090c07060b191a04030809010806030709020c060a050a0608150907050a12030f030b012c03031b0727050a110a030915020a0e010c03020c0603010e010e 71
    0xc500a50103068a01d043c0e0300419080d08005850303105c2440440e005021403a254030a00760074902e160305000700d00d044480a03100400798030b948000e54054980c000300300f6007801d00d09030044800c280d00404295040c494004000764078403480c4010710716801104090f100600d403800f1980e080d140081e003000e04031450408200405100031236402c00e03804035501003000a4584060302c41c90a0155008154001c441e00c10000e04100c40c0f02c88000020310030744a0711000d01c0b00e04400e8045802ca084107501040310440c0600e100403d141ca4108162100340602c0501009880402e1440c1c202c0e41440c001800d80d00d0a03446400c00c1088030b04c0042004036909800140c103c5151050000081c0b00034100a48501c045078114409411013104030002a08083d00e94251240040141030340303032000e441d1100342000c00c000c0384101d4001c450404190340c6038061999421001101d01425a000590450240148c44030195643c04011030080482e150142507030f5050002554081300040c020b04100041e035003044 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 360113192 1250 360111942 360111949
    0xe07030c0f050f15042612030a051006020d0c03050705011104180b010c02060304330b010e0f060f04090c0e040c05031b0f07020301020f0a1b0503030a0f240303030c0509 74
    0xc0303080c0c404006e59190200e00400c80b480345000c9910503180140110805006203005d107001840c0b1411100d40203120b141c03030340c0f500e0600d40b43e540c2c010700700103030010310341030503d2806081a140c02c00d100380352891074000d841e2140c0d400c452120704040d000b030030f001600704028402600f4030b460310340021070304100000313000c00040c03d452401040280035280100004060001c40451a4007150703841c030504400407444050040304000358104c0d181e210b0325000405009500c104940004080003500307013041003244100300895500000c100716004c420400010071030002c24000c40b091010f16440380070420400b001048251001400f070b100070880280704105820f00c0d04a08411901c0c80360f120a603072110b01803004a010b109000c00650503600008151480740a0000103201040c0e00340d1f110498030440d460009241210b844020b420baa2003400401e010382d0382036100741c1d07804a5282c0e000644440b0307403e603c9550301400c0104881c10100e28010010705405000f1980b0001c0340786041842e044046001 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 360114442 1250 360113192 360113197
    0x50604080d08040303020d021207352502100f050f0415270c05060f0d15050901080a060e010c050409022d0d06060c020109090e07030c0f050f15 63
    0x81d8000c001c8440d02050600d030095040394a28181d0050035035886294a00d10114000c060700c038100081c019044641d020405040c01c3c5200c00011f102244103034000c080482440e01c030280600080da921011601b5580085022500011600341c000d000b1001c68036490714101c4c0c55410411541908040070800000e00c1c1240840c0c0c002d900180c43d030004803101c0509801026081141d1044c8454400110401c9520f0f500d100301a41c4904000902283c0b038800307100141c0039980382552041c809200100c464851600070120b26040e0b42c9440d00e0030b03035803580011100b803001c0e848400301790003043d035040a221880c0607840b0b8401144000303202c00c80134400e00a18501c11440b60a6200c0c0d80460700200704012680c88003a40098003500c0104d0607080d21814030f032907101007000b200d01c1e071030314030000340360342c003580d203801c505601610b0748409980b0740504180035202c62314180c0d000b406488804000242607400680103400d00c165075038020b80c04d0105201c5907500740e01150784101c5995010b461070401c4c8008 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 360115692 1250 360114442 360114463
    0x3040602060a0515010804030804052a04110414130b15071b05011b080d0207050c090f010f0905060f040908090109050a0b030103031b080c010b0a0506070f020420070b0103020a05060408 81
    0x12700c2100c5a5803410401e00300b0b4000d0441005412080202002c82c900112980188060440d41000203842c17980e00091640318034440e0f031615042d01c504003d1039181c83d201c9074800240703890012410b43c0350b0380001900d0081d1005100407440c0f012440c8810b10084000c0080d03e130000c0500160f4507801d250010749290318842c14005816180c9200d102048210011303a0349100340703008250b48804141c88c2894490b08040442c50240100c030340003d40d0300d840074680794100c2d103004500010241c2000152006020010312081d0013400420504d10349071110700c035664056000700c1445855405e0900010080c0e803207540014800e03100c01c0d0092000c898594102d078116603160411000c408400d034003501e50f4101d403440180c1121004039803090560410742200c144904115054800c0340e45400800072140502d240140014002e902240014100b90b4080b2a5402040b003e610003146003060001c40c03548903c40c03c4070340312042c200401c11410442241030180108450050a041c20010b0700d507a070741d00c04c51 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 360116942 1250 360115692 360115697
    0xc090506032107030f02060106120c090815090c0a0305061302010c080d0507020106090207120e130f09060e0d051603050405090702031305030318010302180303040602060a051501080403 81
    0x10125650780da0030401044500030825869015400c100141881900302000980124410540d11300c01d443c400310381181a00d41c6601d42d80500e000e0000780100a1013246000d00602c02021000f19a1503003c01c9400300206104800102074a000810036042200b00c0d503c040c0150380e07044003840021b03400300b591a888818614103030080c91060004036990318103d60054011240000c40710344135002500000e01c1202d00341c00a00c44140d441c6403d100303d00c81c0690191541d0380c542d0450341111300c0348121100070380c00101000101541e00c05407808035150b8100c0c2415040d900e00120bc10001d40e401361040c4a222600030381040528514003408510a07134103a5140c40d40702d00b401d01e042600440988015110141c1051820325041601940e243d110a00c041010038024100042600d0000700b103542c40907040400784ca0f61200c41340154041e40080c2c048800c5007062094007203882d2010405000200307001c0e40140307000d082011141c0200d0300f02038650400c9103103100740a402a42c100d20030f0303034100c0c0c0d062 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 360118192 1250 360116942 360116951
    0x2011e0e011206150518010801060c1b0512070509010b04291c05010801180309090c031b02012712210504050c12060f0f09070b030903070309120c09 65
    0x2110044014515908442c01e00504201020134055201d4090a104000401100c000b80509001901c19801c24803544000402c4076a1400c0000d1150f01400500103050f0049403840c1e4407140022071000d403105000d0125840580b0401c46441c01805660040c403841030003074035007801d100d00c0d01d0300306030f05504811a1110600b030390228448214201d9089103609080c11410044400604015110038400e41c42030b9800c25043d071822042d015001d80702280c0c5a181c0902503483c18401c0380c042c1101104290601d035680c0c41c0300303000c100043c046d40d00b00001540005820407407130741c00785607500513581858412001a5a41c400256541c00b40240031411418a0100107105520080440506010011f103560a01c01400200100001e118800f01d4003290100c02c201c650403207040d9903150840340c00032002d40c464040b50010701421072a6070012002d009035401700b61200d00c1c41d15240d000380c072130b0342e1142d00c001098018180d1100001c2d0181000003c0d00c0400c0743d0944510480c10064015101995a00c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 360119442 1250 360118192 360118217
    0x612030d050c070605070509010f1b0c0b22063018050105130309171903080a050a0e060403120204170a020301140603211b01050402011e0e01 62
    0x10800e440c0c0c42050000144428904101c0c41d021a821148080f1003807414034000c10306480c0200e0070307078540d0342e0181d5400000342d00180c021901180200c070101c801c0c4881240700004504039810210140c18200d00c91950f0b605250340d000c40b80e070303003403289802d454001c40310038020355a00c00b061902d64500e00d2400320449044105a58200601458011603030f4a0903105400070307200710030f08000340740c0100e000b0451b40d540c0f12548007080712540030090000d50750400522004912003003507c40d071444801103d800000860001c904401031a43c15008609c04004200c00c951542c0200c0e0b51042d504242400802070300e101440c2da0382e0f4080c0008041c8500c019070200c2d0284d0f00d80c161030091072042082d8100350480052561a101498411303800b9500f4140c11000c1c18508c8440613000d81c10103401000941c880c007160081c1d0407404118210106000c0007041000417001402c0426008020000520ba00b8540300140c006045007039048203ca85103a41c000c1c04540080350f01d28034070000c2c00c040b001c0c1d032003 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 360120692 1250 360119442 360119479
    0x206010911091002010b010906030606092903040803010807141f020a170c010f09020901120503090306070e091f0b0a031b080f1005030709020711030715020d09050906 73
    0x192050365400583e001198006168150070840004600b0b0300c4150100d03480d913400b10305544590142a0100384881c81c1000b00840c200b080750780c900f842d8400c0c519000c03d0300750280221362051714152032404c008001840310305000e101c50001061003c030100c0c0c00e0380190b8003044142004456600d8900401d2030f00d07008840c000d014210300c0c10b9004103006244440e00c00304016030307040462403018541c40c0602503207200581d4400c035012260010240307181d50b0b02c0e0a115000c1045d4030001143c06000a1020300d405032000c01065005450a454011f045420501032001d10017005200c0d0041c500302049982200ea0781c0c50440c8140c440c000c9501e40c1c0c8407640b4409401504940a50309603860b145409205080ea1203001180150340b010451034079501d03401000034828400340203c55143d08006c0c0d04001c604415801014118860605502c016030b80314002420148168082075140c0c4140302c000e4000c0d9030502c03d8225000312810300050090a02c004650440001084640110341c035560040d06401c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 360121942 1250 360120692 360120697
    0xa080901020f070e312a1202011e0f030b03032217150c1e07060b0f060a08160309172104151d1515030a030206010911 52
    0xc0180007180c424551340ca501000007a0211050410600d02c00c141d81c0c0707041d00c10700480403c40f03581d03035440003501041d407252907181051841d0450b4081d42c4102d001141104c0c2e012810040105d480503d80404450002501c13440c1d045c0c904c516403500c0d007a54070100581010f0400490711350b503d000510300592401281c5144110026004003203040440310600014440c10182075880122900c07030302501c650601591440c00401042205001000041c81c480455019101c00c41c00901894100b50050200c00090b5002c84801d45a40751620001540c03400c00f41d5040c440d040c2c1c1505c4880c0b410400c0d01000b0502da80c0607020004105642c031102d80c940348a80c108010b04ca80108050034119240c800c0d03092103a0003800801c076a0480142c940c007102442d5108140300d541c01c008640b40b404000c540220003424061030024010000c1000032200791002c0208e03907030b4000d140d60900201d00700794031111038107824903403d180f00342d0106a006e4006a07001c140c04c1d046510b1594003094851201502c10040d0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 360123192 1250 360121942 360121963
    0x9010e0a2c0304080d08100902030901180807030f1409010320190e040903050d02070f050f011e09020a050111152707080c0d030306050a09150608090a08090102 70
    0x7203000d49600c0703035003030040000e0007201c3c211021541d503002c0305c59060707404010844029403c0c035003110b02000150441e030002d5600800e0a1f00001e0419815030180d9a8403000715810742d2032a101145200806821025022241c01c0784e0409000504030400301e02c03281d1044d81040c1c2d04058440d81c203420200741c0701114065145c20f2074010380c0c82c0c0400380c0040c66604a42503052000451507589c0c0005400d0900ca00c80312690565119440c081d100481c04020b0b51080b134085540752080418040491014000030128805200020070180d01c100d410000b001011000d210f402c070f19140c0c07a8401665030109c41811100d0a080601401d641928500d081c181ca1400710707424202c2d00c40070410a6940418441001c01658907c90707480d6016100c45a520581030060450b50b0340075010a0066103030400c851170307009203c0d21300401c8a41c1c8071004a40e40800d10390000004c69151000e8030800b21903004283c001d0041132810b113600703241085890b0354860104078060034500001038050708691091082c2ca000 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 360124442 1250 360123192 360123251
    0x9050c0103090c050d080309060c0306061b031204030302090a0f080a121205040c0e150a0b030a2409060e0403080a0534201c17010b09010e09010e0a 65
    0x1907110605001106c2d5000b00d8440030b06002d0341e0005105481120140d034022080640101e0410705110031409400d5014050281039100522403500c54030021040c03e0300c6280b081d0380160f11188030b042400542141600442c40c0c3c56820030b01031120340c0002400e80100740c0c02107071002c070b1400700181c16141803101080191802d07043ca0100b0013400f887d840000211048061400039960b69100c1c1101c1d0814080011580510606001c000e142c60326801b468003c407a100d030000e00b074403080301003110b404410541d00c191240c2201d020026841c0500c201c8004003507a100080c41d03440e003542d0080c0f000b20024204051287d841000c511100c1c1100903c48030106901c80a016991040300d20300360904108000d0030003d40c0c01d031100c5507100d60b11090040301c2011100102484100000186019400311050308200010220846808411807050a009180700341d0034584d24446080010056000100914090810107004100341e50030b083e4850350003d0190000a440a0400c83d40a0b0b80d00007001580074 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 360125692 1250 360124442 360124459
    0x5030732031902090705030c03041104180606360504080d02030a0917040501020309010c0203100c08010815060d0311160b1803071d0405160e0a0c020109050c0103090c05 74
    0x581d1032080920010140210f413002550342e55500700f11036501c0111490694001c0900200700007030a00042080945030082001c10041c0c1595003015849404003810b96415890346000c000340c0c10a103207598916101060341c81d049402c2030100740c0c2d03c1c40400040041c442d54660004003030298480945102d40000f1400303568a0801200c0308002d40707440300b000d56540154031070800140300043c0480e812524182c000d1810010504010b6581c04d034400d0050780c00d8014200c58048402c0503203d9500c46c103186071919a03482d414000300600c0c151104080c002d0a800c03180a000d04c035909d8100344017071158146000c403850045031071481d0400c81070f064175644d142c281e1000404c0038080400604014a101d41d415000c2c10b0303ca80c100b694620640c8140c2b44006100720003c42c10160003c2e0107035109008100b20380b01d9003c9044080701c044016400703214000b00507024031200d801c00d401040c08603d542d2001344003c00d07040d222103482c0c00344840c0c01414075581c1c030620810068820031400050100415004 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 360126942 1250 360125692 360125713
    0x60402190504050a0b0f010c110f0607060905010c110102070c0e13120f110114061c140c04060501020a02102708030a02011b09120c03050d02070504060503073203 71
    0x4081c003000610240f00d00600e524107661540700300d41c210552383e0007505c1c8828030b11180c018815914444040290841020006280465118080c540070903100700c000007081c0c000c810004201094080044d1101c6e40100710440128241d0341651064861524440f8081d0b21080805811f5070034129000b020380d61200103815413950094400c0d100e07800b07162150b65620001030445400c0300c128500a42c07000840b0400300b003007400e1459500c0700070304e50051911586401e64462603100c449610104c03403258040d550b07546030780c00e01d40514401030000307000400d043c40882e030000342800c10601084042007000c05843d8034012204003003010100401641100301c6807608443c50316a401920424055801c000140d011051616049850040c2d01d958507203646081c2440e5500c00e800400050307030707541c5d90040c0100c0414024081e440b222905070700106041440d1105100c15a0b482d40e004c54400e4101142c10040480e070800316141d042c0b079190200c2caa030000b545090851111106003207070148120f45011 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 360128192 1250 360126942 360126961
    0x121302030a0b040203061803040b07020f132f070201030f1d0a120513030303020d022109060a06080d26040f0b0105100909020702030717010b01080c090306040219050405 74
    0x2030307000b50f0085e41a00d5a640d10b091064203980080b025413201039204210401040b2100c8020700280c9200400c0740e250f01d10a00001990841c546010f80382c0c55550350400c0e0006161600207404034410304685124a0b070b061100409240206500a814981c40c0d003180038449655038000100c603004c41881c00200340c594801169a241c082104442c00040e41710503508150150703050324100f07400119032100d42820f544c0d0172000f035041f83c406076400301d8007400311590000c40200300d042010850044c00c2d91520b01903800c24504540540340520b642d00c0c00406020b070000110728a5101f10302d0341000244400b00b081111049900e294071100025803041c288020010742040d601507440c091080c0003901c5c0d0321502008003031080e117884480814000241041419140d4002c0d05001d40002d00341c502003680e881d044a501c1c0380c2c1d801d8030b60301c3d039545000c55011503030003040e41c0d6049001c0480303440c100304014020a6031000c0c0030b0006031241c130601045140102c00e00b030700c020240c00c1c068800e000500f04001030 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 360129442 1250 360128192 360128213
    0x20307050703030e0a020319030201022502190b0f130b030406050601080f060109060309080c070303110f07032303040909110a1403060a020a02010b040908120c030c121302030a 77
    0x2200000d040c940792810b03a00d000114840802d40090203000d40012230000b10070302020380402201035540901c80d00b001d40050807a62080c48511000b29070004901d0b10410400e12464415042c0500c61040c00f404103d40820544589449a4080617990b00d600f0300e03842d00d10320441d8044404000300004000411140e500810300540c1c2c2a01d07100219110b030b10100c0070221088882c3c60001c1c054490401c50513219070403543c4100e0060329564a400b00350400a03007804643e410a50202c5c2c240c012102003940b08116282240f651000904405402d6079a1000300d5041002113011245240410003071440e001d03c02c80d0018101d18070b04000d13200092410000c100b260500c40d0703114054407240040c9030000c02503110f4007640002d0107441c917551514600300c02500041000340466684112030320003030702c49114031400d440c001c46030991603014031607201000304001802036400807406d000b070103101c1c640c1505440b8500962038001c0039507501c1d550000d000760b4030040040d40c9841101004020300014114 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 360130692 1250 360129442 360129457
    0x10e06010b1b2e230402010908120f1305130519050f060904060b1210050105010c121d0a0329061e030a120210050601090b0904090f020402030705 64
    0x440b4040c1075041c001c0c0d140c0b076459121040350f9800010071003030402020b6074070041c0503803034820307000501034000c100c8048000030710308821100300c8007a003e00040d9070300b005030900145405030042114040000b1028007600400c01c00c0350510901140c0107903400b4049982d00007400000c4c3c45252100c81c03807802c540190000303440800c04500d00c0c0c6c2010031160114061113101e5050b5280500e503d4440074140107024000600030384500b031fa80c1607481200d5072051080510401848000c110b0000340006040c02c940041e8001030502c07560074500300008810400002040d0064288900c1140d00f10820304400c06000080c0c9500409407440071080003500c903c40490b83d4900b01825400051a0043e104903420540310b06911075020354014410100e941c03005c0038030a802500f5541117540550b19011091900d50809002d81c0040e060341c0c00400080c420b180d4003103070900c1d00c4007c0c1c9240ca080c121031403080880440c000c91b00c0c0c054180c18803011a188284850b4040c00c2150750740340451004120307401000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 360131942 1250 360130692 360130717
    0xe01051c240b030c0405240a0c030809070602060103121209060911031f0b27040209090c0120010e0d0518090c0d022a0115090e0c01030e010e06010b 65
    0x44040b54141040040e41c2c40340181c0d8808901c1c0c42d080c02c0401c80c401404e210681000306c03003814082c0700182d00001402d02e610003600c1d0300500d802c0601e4050b16944000b40003000c184e02c1b4240411006a001802604480d004010121840000f4a00312074a01d248010301c180b49040002d110108007a591000c01c0143c069010384101c0d41c8941d00b00354407240031100c0e001103001c035550034007000c0d40d05500441c0c007071100130004c41500d58080100803144458624000302440030404202c15800c00b0301110754003d0f12400640000c0c110100060107121031115620f40c810752110302c110b1642003d601100043d0b40500485800c0c81507940001c015520884120465031071002d1441581c0c14043c0d1818041c40c09086141d052850340071103440250080440c003105144114125440e47c0700421803000601300c80000440d005445400d40750342641150310036403415241c03420070462600045103000d0407800c2442c2c0030852a0802410901420030000d0320b4035a406810b00000d0410745010041c1615140034 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 360133192 1250 360131942 360132011
    0x160303021605121b0c010225180501050f010c05100f2c0c121902010c0c080c01020c010509100c05030409060e06040c0509030304090207080d020c0f010e0304060e01051c 74
    0x120716640d05c40c20300000507800350b0b0118100a019002c641c4102000308411103a000c62030f90343e140200003030720002c140002c00d10341e103000521031814900c1448080480a0803c2030540406070365040e51030303802c4074084e6061039403185010240e540d2900641e82110710005101d00161603546c46164004c0405034140c2603218614040c00e09050005610310349807000c4000e000f03d00f9400c10340d9101481c010310101d040049081f0403030002a0355000040c0605601030040c0492040c04002a24024040c1d03802414031005200107402d981d108c4194400e04200307450811224801c91805500c3c5000da5080b0034010307428040c0101f9040340040c5410301c21a03044070140000e41680308161540d1040d030450a400d03400800090188400039001841010b10a286143c0f40100620b003c2007260080307040ca800755000200702480d8501d0074069484c0010840016600c1c0c02d04d0128040c1008866006042c14414007085031214040401c1d1020390700402444103000b0090540c000b1000f014148081d0000415103 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 360134442 1250 360133192 360133237
    0x17071a010512070302040914160f09050f130609080f071106070b0f1f03030302180405012601021611030607080108030a050d0e0f010510050616030302160512 69
    0x4800026155501e49003c1d200e000d0454080c04050181c8020a49566588444001c1320750703010004540080f00700c1614200c261f0403c845801d041905034450032400b8142024030881c0855031007215041840c07045480c08400440c54002d02601d58030002414100011881d49c0c034408008005040d01e13403140710f032041e041105004109050003109001f030000c82c4110002520041c1d4a02401c0e0040001d50344502c2120f15083c50a4200200b5017040380041e801140e8030300c40103403000c0000d4003a402160305000c0342d0f0410001c04603c080c1e94610703402141d070b0040d490b10042130079411500f0b43c2c0e03812103003401c62503100d01700120403c089401c13030340c001c0c854540003078261b80c450131005044c0c0d45804003540c640080700740110740c690000d110070f0003e503030f49a0174080d8154080103c91198080b9400100301481c2c00c1141a001501d0ba5005c0c0d4042e000030000103141e800e9652200f40c610390305040043e2164200d050000c00805081801080c0e846400326220300c9040540140010034502051143c07485003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 360135692 1250 360134442 360134449
    0x4050406080327010c0c1508090321060a052106070804110f060c0f010501060f05040506030c030a060509070203040311100c02130e010f021c050c0a03020717071a0105 73
    0x76001100c001c0811003020111040c03ca40c2440e00c01e1001490010940340864541d030130348807074541c011740054088450340413005030030030711281e0b004410401075424081c0b10f921200511004100840c02081c0c0140001d10070740d101c2172200080d180203030041c0b020b5140900c2840000514500e50004d52240c0000246058070880002d84501e900007081c03044088940c0601426400310088a0340c4001c0030311041100c2c07501000400e21144508001180c0780d4900303040500302c0c0719404000010040d04020034005d42d00c50310100c80d0401d0f03144410300d641e0303503603001404004c1c8500c1e004150b101c9160340c288080c00d03a00001400c01c1c1d0f400b0340da0070300c1011140c0d401c000100d0301581d10340012500c04103008016103410640e5026814411401040d0b0200400941c2e0855502e03100e1051125408918602142d19404078080c8034001d2000c10801810040302030305046c00b800c40303500109a0001081810020000d11000c3c00004001d00c035600c071040751a2803040d06084030079080200c08184c000145a18 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 360136942 1250 360135692 360135697
    0x40504060b04030c031511030c0a0f020c06120c0903030c0313060c020d02240a0309030e09010f15051204030e041404020901060f03060e04030512070509031b04140705040504060803 79
    0x25401480c01032000e1171680e6840344034800c8042c2120030340d560b026070614118000000c6100c1e004d4040a1640c401140c072006d4003a2710006c030740e1011076101c0090710006031280c2e02140d1001c00b040c0604846681c1d0300c121322015114070100d0039014080860f00905010002000e401e0081ea01004500c140e038817048115807000c44000c0c06076102d4030500080001d070a184084501c0e8410791400c1c040d440d4a03902c01c01d0007545c8422002c50020742c5e0743c80104241944189480c1c0c1c6404200c9584281303504d001551500c4c8140b03402040c02c200e83e6052202c102c207001d00f0480e01c3c801e4031802141d01030b152505018111112544c4624050390411840c401c4c03000004549901c200d81c014407841c1f60fa424000c044641035824040401070558684000c503071160300c400c2d0188980d10942d80d0321f540b80f005154659040038050f080d0380030302400344a00609075030302003400c82c18041488441c0c08003003807040008000d0b24980da03541080007844030902c001181e0001c000c4c810b454003941d00740480f9039642a41036591 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 360138192 1250 360136942 360136949
    0x212070c0f08071b3803010302010e010c0c0e1801090314090d060e010b042f0a03090b091e03070c120809031e01060e011d0711030708040504060b04 65
    0x704100101000000c1c0c1520192600030301814504200c42d0106903a8000146190801c11005c00e4201c00702001200811400140b0b220b03034044562180d03054840c5a100f0b00040c08020305110750741240041c01c0c1d1151504092094100086030b0409a80326074215600c0c80c2501d5501c44041d102019131070500d0140540900103516a0724074041100030360a080607501702442541c0d006229030803200220b0b0560080c00c10310340660b000006c050452608000864254150280411007012651400107020f5034000c401c18400030001962014001000c6004204d5914010801491101803010a4030002a0400c2482d41c00c0450840c040007004d40941c0c90003040001004140110401c0c00312607402d0441e81a160b106400b65414900ca0354002820031100d00c08500701100c46115908100f0400d0240d04001c0c031001c2040d001550411801e0800e00b06451145d084823001340c0081400c1034415012500300d00609010382e40ca5025901d46840c2c20b50091060342d00c520b041000c04100d00038000100c6040303 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 360139442 1250 360138192 360138203
    0x4110a0f08100f1b05132106021c05040f02010e03120d18020406080a060f02030106300c0c02241b070b04090e0d020114060f0307180212070c 62
    0x100903040d001c001c043c00410041069107521443c3c124403070181d41d0408032145040380c546030b031141c50b0641e82d0781806146074448042c441e8518240c0595001110715054820341000c00940d036880b00e90300e001d40002162114075155881d0108000030320407a00f4425051a00c02d034dc805030190420001c041c2d491190071404042000204110441ea000315403103c0c0700c0e00d0311301d1451f840010003a000101100d4150703220042d15005880d0500811207184109080901c440b0021415941012002006008070544400402602248010321000b416844e1281c640c51404180540004440020070002d400c040c100c6c060300d64000e1007001030090307005c680450440385900905100080d905242c80e80071421030030541d8000d180c404502483c0120040000d4031001001240c2d000c0c62104d260718140c1d01c400e45c001103900d005c11580c01800300821080d00704004581c6c1000340c4480d40c001a00b0314015511803400c40c2400c4c60749c030364010b1654020f070a400e6500117082c1000d0f42e4440d802d803023001d10325000518 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 360140692 1250 360139442 360139453
    0xb0409030e0d020307090906060e0c0a020601030f060b032b0305010e150a09020c06150609030a110402090a090902010314090a030f030e0a1a07030c090308090103090b04110a0f08 78
    0x700c0c01d10040c1a500c072070004007101c010720740d10030034201200c1513100280c500300e40b00e440c14031480d02d0b40c10020307402c00c0c1800e29a500e8242e003600000d44402043c00010720fa480e010003444140519a040354911540090039940074244040c28042d1090090703042040c0355608500402c0028002c0c45818121030403403400381596a20a400d0210075000c40d04c00d1944400041c80104482c01144094a000680c2e10010080e0b81050180c952203c007060fa041482a541000b02d60500c0d0ac020803900c801c04da014400d03420f0540d1580000340a0300400001d1508000c503000006207040d0960040b1813054001c4c1c800300424040c6416221003490200c510800701d5104a6803003000a20402c00c40d00210b59925000600291031001d644c01d20303020241c140c4000c0034540e0b0303001e83c0c81c1d82d0b941d0320b9400408604040007041d0f0022000340044075188000380c020340d00420040282d901036001000c140d94810031001c224646440c03d140c500b00c0400170180500b4a2480100d48000854203180035154844010b24 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 360141942 1250 360140692 360140717
    0x40207080f09010c05030c010e06060a060f120623240712170903120108030414010c17030c1b03180402070c0e13050c060304020f0909120708030405010b040903 70
    0x5640c0c8010b03566410810703100e14640c0481d10500c0034040030400d8000215811120340d0b005860440003500d46442600e482104201c0c2c10740101215914095a0820b056013070039480e10200101056400201092203082d0001101d5081c1c0260b804628021506008078408544080f40481954020344504c508100001d6002c26249054004494040e1400c0301c0d0310082d061140046140a44103140c1d9a8408102c115002c030900680e2400b408056000b1070809142c521141004801004030360706200800e80d6440500100049001e500865060442e030303030b41040c1300c0328411980903403446540900e030040c1880310200301004a030640e408d0303001c1c1511640e20241c2080000e50100b401159440b13411032001418140c01031407030388504c240741840f640f0703002c150401c24107042d60131861a00c9140308000704401a9504541c0c64000041038540d1851555100042451f00c519560106400540411204c0400c641070004504c01e6105400902c00c1c60890024071055602c03c40c001000b02d01c606c0c2d07418 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 360143192 1250 360141942 360141967
    0x20604050603150303070305030f0901330e0718080705010e2b150f090f081b07030807110108100b0a020c19090c0c0506040803060d151a04020708 64
    0x710380001c1c03c80c6204440b4a03e41c00041d185600035007088001c00c00102c104068401e40b9102a980703d000c1800a201ca811021068160b00074050102811030a440140d03545010850b0064000f6007012650703003069041c40e0b0307005400820121001103440081c50804602d0010105182048036410784031080010b400c0400c200a84680c4410031188540480524082c84040058000614010f02414405c1d44004821102743c828241251104c01d0070300042c1800241d20800c81d0382d00c42d030012070306500d401d21020b01042c4402d03203441462984c443e2480200602c40080000c0c100f0fa40f00310610280c01d0b40301001943e0185040707420b142142c04081c81000740b041584e00400442c24035105a4104140c4500041e12200d000703020800e50400c2c10105000c0e0101030722a400840c0c0a904040071446000e076213a41d9550701c01040103140e12408030100d252620b481072003950103a448001c5002d40145205114010a0394284e0200311008681c2d02c0728650400d0710032a028a41c02284441c502080030020 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 360144442 1250 360143192 360143197
    0x501021b01050d0e01020a0818011404060903020304030506011e09060b070f0c050a09050a0507050c0a0f0303060314060f07080105030c06090310050c040305010b040b3607180801090206040506 84
    0x280c0390f25610b03149101c0500500784000d00400189464000c128140040001400343d211110007805031b2410780020720022820341c03072943c410340c400c5010072101c0301ea10b000c0b8214003440d400101303144074050000c0b8000810710b10761103d02d20341c807d040d0701955503604008203545491040409050303082210b0f81c0400d00c11200204018083d03d249800c156039000480d01d1a030031944210003881d551001e021030b403013142c050907400440500e04607007421542422b903230303c417601c0f584000d010500c2031243d0800c150107504290300031500494a00f400741049803a650300c41c2c0e8200c070100703500010b0100280800b03001da40100d05071038000d07000f040c00c80c40010510490758082003809503d40719051100d0034544080c01303020300c5041c078110072948075440c52404909480007810100d11490405004c04401d031184002d15410407000300800d910056101c10540d158141760750280354400d18101007140c600d41004020792200c40c01440c03415000d0340d0380300413400c0b00c2d0081802940144100300800051400001 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 360145692 1250 360144442 360144457
    0x303051e030106090305010b04060f18150902031503120406050c0c120a0507150804151b021c0504030b0c09030709020a080a0605060304020f060315030f01150501021b0105 75
    0x50401245106110301840d030030903400303000080c08144090081000a004080c2c904106070360034400c403424080794000c00d0946020b20307081e95454055a001c000f001740c00040d1998002454040340603100e4607200042d51080311a00c44190505100364104e0030005280d00c0200d0403026828203003818104120350795401065012054440d040780c02c51250b495118104c08441514020400c6150f2072410a0500007181d209070301105c0b05a01452285400000c2264029441400c9190400c0c1550440f0700504010b03c0041e41500c1d141940710010b41c001a40044900811450f21011151200c0480c1c0c0341c8510300008100ba0000b0002c101416403200142400420050941d94100d4540341c2c00002c9810846154000581c0001401000c2502c0d20484004d03082c2511902d02e10320b021340109850000d00c05180303004200010010700000c85502e50040360310001802e81303c2d0300c04440c0c4464040c0451007601c550000301e4100004441d80001104050900e00c40c843d42450083d0780c0065603903810664 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 360146942 1250 360145692 360145717
    0x207020f2706210c090f192a03060f1a0f0c0c031212010609120308040203160f08060f1e063c0105040605070b06060c060f0a0b010f09030305 62
    0x302c01c0d91000300072214a020118010000c00021343c4503800c00c0010400540240b00800a61017401206c0e4840d900300802c0100d0701101040424081a0241c0450058200051440034160302d080704940d06030031500441e9030780900c07602e42c507807a05008003242c00c400c4401a060f04007045904060419040036107845c106010503504440010070220341400c0c040100446001070004001001e906c039045884e01609035460000c25890802c804e811628525080c0a0144456680003d04642d02004034101c0140300345002000540d031030340c00711840400b40c0905a480e010382d100084202080c407900038800c80c00c00000c80064841180e10010000d0050b00316900001603030088144004145841c4600700302c0318000c0311400b00c11800d01080b00802d5800141040801c200030040b03550b20900b52402903403c003001180d5a140c01c00000c01900ca241c900c0d4450380185410001158100d041441c0f00325520f130818010901300100441e03203c3c0c0400391040c04640420f00900c04039110750058482400e264 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 360148192 1250 360146942 360146959
    0x6010507170d0903020a03180605030a0e010f02041502010e060708160923120a0302061602030405120106080d030603120c020103090b09061602030f032d0a0207020f2706 74
    0x40c03040e030300f607650f240802d0300564018440c141c00c141d03001000e452100c03680296018160304181005000303103c040c0108400b2915002c40d144c03043c81c2035215512051b40540110740c1d41d03944404401c00903e0340080800035500e89003403002d000c0f01c00304d549071040c441ea980d600f07420313910540700b00802034480103a4410060040c40c0403404d261500c0304240030135844462404014a42c0c030401ca0070801ba0b182e203012940186400c20f002030340020300150050b960300c482c14805004044100d01d14043c950019520440c102c4102890480c194004400d0b10020400d990301c0c06841041a4183c2e0440c1c4002030106010f40915811b0034412000c581480f4414500441c2001c0607844481040b0342c00c0c2e46410b100c2c2c1298040c000d2062640c4400c0c0300708101800a07605100c407035100b44072240001000f03d008486806101010314046100c070f42c5a104012000c000103080c00d006080003034110b0241203002d1032111800030117601c5d000300440c59440b1a044403844004004140301c4885a001c0c0903e60006030a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 360149442 1250 360148192 360148207
    0x9030207080a0b0115020a020108040803130b160e060406020703030e0d0602030f090717071502030403051203010f14060706110d06180f0501050904030c0f0b0708060a0e0601050717 79
    0x2480b0030544580a070080005650505d2000c0452154500b04201954052100a00181d0f0401d080b240d005400041054030780e079541d801c260380c1c00d100500080000c01484100900c40c50384800103548100c03c3e0f0b40e40c2039100c0081e410701000d403159004000241c0c6c8069070400009102e090311256600c0e02070201d02403a1003035542c0d6000d0340c100381c461031998842c072001c03c46e4540781005000000c1c01d02511045d00c2610345407405031100100d010781c1502c103e0016a003030080b0700070400c03038000310b9000040350303916050821441181d410030700454101c0b82c42c0300e000180c92400e104080440240c02406503151858a6841400809800c44500302d014002d024010a4425070312505000b00440300d520740000842d070012604550b41d40b2120750f00c0034644401403109803200c40e1440d07401541418030040751b20041c03e18a00310300c0c900d2030041003508104108842140d01c40f42c2140601c0090324002040d50301c407070f848502d064007100c0c4240090001c1c031044020410b4000400c10031020b1100d80c03850607a8 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 360150692 1250 360149442 360149459
    0x40804151806020d081501051e040e04050604060509030702061803120f040801060e090c22020403210c032313090203040c0e0114010509210d02100213030609030207 72
    0x100c1d0740c041d101680001a5100c003558002c00c40d9684013998142d40100300e00c0303810000c0c0a034081c1c520203234a12040203000105090090084401400708080c080c500c1d0300d024030f410343d5248806c82d800c44042d4100b40204038070070300020641c0e00783d84c0d00800407814400d208450320420000700501e00d42c18890045d0720300159030760000030b05002451102d003035074990400c8299130035a1181c2d4004811a6003c6040045070072003c682c1c3c40e913100d000c44400300300810381d14010f41100c2003d84100201c902c0090300004110244400540c510841072140001e035a8154050300c2203101e10b940a0081a40b000580d500c140ea030490480ca10741032412018207048805881e00d10340c410350b1300310030015036000003404144040c002031080100130022091843d5070503c984024000d00429101e030602c500450360301d00300d80d560b00070811060340000b1181d012280e40d03400300d03656074000080c1e14058014400100c1c0301c000c09000700c8140e0400c600d524065185940d442500a2120400503030841c01040c002150509 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 360151942 1250 360150692 360150737
    0x90b011b0519060f06080a02030304030609030c060e1f0902011e050c0304030503040e1305120a0306030b0a051801090b011406070803010609060e0a03050a1104110a020a05010f0504080415 82
    0xd003d0749000456900e40c454000446103160054000c962140d041c15006a60000840d004d40e94004004105003150f45010750b84081c0c0013400801603400d280600300f6600d00090700f1904050710005449030204420b00c00c030111840c1c0c0710044d0000d40380c6456040740004021007401001c0f9585007891800150840c81c500b150440e4008072a650400503007085282c0300144003903003180c1c0c40840315000913250b55810b984d940c3c0a45c40a480c003030f404140700501601a5100302c00458105000300c1e15440c1480041c402000c0403144000c07080d4000e00003082500c0140710320400b29a001e40401020317400c0a03a07003044c82c01145c0350240d02000810a220028900001843c003c14450f00e4035032a082c200000907220705040c28529000c0d0b441400c00f0000329100040b07400c10117411054400c0e00e01d06220204028124002c5900080311000500070880d80c1e00083c030140b01c07400342000300460400c03c0039541c1030740c2050b2000384c02d800c4107001c1404604481c400000302c1d156141040440092180700900505 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 360153192 1250 360151942 360151993
    0x21060b030f0102070b0a0605060a0203071b150201410a0912020706020705030a0c0b0901111204141c0b0c070c120b0a050106080c160206070813090b011b05 68
    0x4502c0c0501086d0180c5014190180031b040340c4140c2003505c3c0c00002543c034000d10300007400f000303103120001c13080c004401d20105c00740c01c0c40050310030320702c9090801a0103001c496070b10000242032800300356080052095046402e042c0d0046030703c00b0580110242d20840c0010340041c000c07941d074507507180025a01409101c0700c20201e0300501042d074680304c2c010341800007a2381b01038025001441800001a1019001400d840d01518095141e4484500486011640c515004032900c07804661883c000c0c420405401240c00b030302001d014035603000e4207000000000481d029a10742000a41e980010400e1041f540d0000000b040d06040c001c0b10b4840000100540c0e1103174514a80c0c4a5140050058440c02a07034860a0f54405211952500310300800500c001054400004001704400c4458a10042200c1c0c03a150002e0103551180761508168116a01140c444241e02e042a00002114159402a5010240161110010741c2400c00915410850301c80c811100c0303015140e0341504000e0f190340d24111a = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 360154442 1250 360153192 360153203
    0x15040b07050706171504050c12090f16081c050708070614090a030c1439092e080303090604020f010e0924060c0d02010621060b030f010207 61
    0x3e1403c100980480311011024114203684010400030400062181100340d2090f10700280580e80c00e59404000c3c020101001e06038800386043c020701020024503100e006541c0d5040e165000345203207490300900b440748224041078110b02035140d845590100300c0090b0f80700702d0426a24010065550000707a03800300d80203c0d00e00f950b40304480c941400e402c10032a8007904000044c8048201510080c01c0308542810007007074911031912401d030003a002d210210100e009400c030425580c0503021880712000b010518003054405513505246c00c0c1c80c090342940e0064001d860310055000c03411100090406e140d50f10020b0540f09903e0024070300c0410402513104120b20030103040305051902c10403425140030000c2074100b100e60610b00341c0554a1030742d4507411404c800782e651a2540b060701881c01e10750080803103d034040004204028850780104600c0080003c2c0e900802c042900c890038252000796401c0109100031102c18078200081e080d500450321140b005040b02c00e207000140c400340c01d90384100d408a88 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 360155692 1250 360154442 360154453
    0xf1b020708010c091d070e0402040e04150c14031e070305042105040b07060b0306010e2512090f0213061d4606030317041115040b0705 59
    0x1881c0c000b846400618005481c10010461400491000140e4001c5d0035441d410088400b051550380502292101d680001c0c0c4155195540d8064850000070102c0b01134429010440001c81211820f1107005140417154079000b11114511025048541000300405594584545401011005110210700c11502e5980214540c901482d0802132510072041d03102e46283c0b6000150503042d00902075030140e036148101d46480b500d1604088001e0020408440c1d094010f01001003018069000d50782c0c0b081c4c1d00d4415080114a003128540786103c0d10061090000d89003103990508100581c0090b40828080d00c0d40d15103001c0c20b500003e40e607400b0f61035022162552503a04109251100629a05407482e00601310344c14900a800402d510b61140f80103091407141c400d0074011400120003403a10800b89813004031340a1b0110800c0401041030b070000350045105074a44400700b458480c891072280da80318861060b0020078005200c0c255491000b41c2042074070622010031031000350000340012900580003001c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 360156942 1250 360155692 360155699
    0x6090e0c150a0f261915300819110714120f070b0306040e0c09040201050309100908030a18030f03020c150c18090c041509080105250f080103060f1b0207 67
    0x8803041a0180701b10819503040801450522100303501c03080c8000109002c0e901c00c00c410100f140c4444110082950350041501084882c401d00f8031024645035813103c407603100550261960790901d51240d00f00d8800d20590022160400480c144141d0400b10704440c6040d460112060030035101d50421401040044200641882c050250b00740076000c0c10090304001c0000d00c007040010350010000b9042c030074000042281e0480400c003030b154590081c4000c01a01d1324620b0150911350050361640703015420010281300b4007000042080456038983c403454a904c0c5402030a174080d4001513691541802010300702d018000c074039a00b140c032407400d0b04081c80da02d105010320181070038010401c05000b141280108000c468410084400780c80500c0b483d8101400200b504541001c40c2e504046141d50a100a0010807a000c080e48400000080c2800c1120088074000b2101600c0f105180c00018031a00010000318a0300c1c2c1c080040181b4400000c034020920b401e0f400c038402d035920b001d880160b00c80d00e001c1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 360158192 1250 360156942 360156991
    0x206030a140109060b030f071b0302060106090e092a041109120304060c0809060906041d07080912030405010603050d0507030f0206060a030803070306090e0c150a0f26 73
    0x2d02400c032102d001c03c0300f00d00308098119540001483d58005030080c13400710b0212030058491920288020122001107002d614000352114802c2c4500b2010511480001c90f200324061341a5200e00e5401c80206034030350f085100b01401c02e44144154001418140c4100c19940b00c9000e81c1e192642c4800c2002d41e10582481800b200c1d50920032401042e4000384014049144d1107404601407030b800a24480d01d0b125200700003a0544140302c521070340004006000180e2039602151200f140384600f103100500d603101d41e000e807030190080f03030005066040030314407040d4400c1d81d00185030000c0c0108000036003592240e41d524942140b8110345404a000418180c0800d54000b04440d84030085202070403170380c02e240d00403da0b00f13282400000d05c180d5000c00000d00b41ca2107135211400610701c90900f0b020304984286510381310b00150000a000d00040020310381c04c00b0300d000c210b07140c9207a255200042079412150440d1010b40c04640304201c40074040d44000540c0344000200e028000001e200c8090103214002c9 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 360159442 1250 360158192 360158231
    0x12040f0b011d10081c0203040807060e01030e0a0b061306030f0609050d0c3c0c090b030c060409050415020309070e010e16030c09031502070b01050916050a05070206030a 74
    0x10a03c07003070710700c101c140100301e804600003030002000b05032100e00d840d0140082e0b0540c021034120061030b00c9607400c0065580e80c04024501100740a803010880b40501c140080e44030b0140342002380500c003900e80841d6890500f844008d043301a041c60018500d6103c0da0b48010795a0304043c03e485180d181c03201c1c00f040c810140501266040941084a00c030087c682d01c008801114080143c007403036030388465078103207404061204240c1d114458150912034840c43c1c14100a20a4003910000614141d01c00205040005017201c0b9580000c165a090600d00780740d00020b404014030448501d8944a07500910f100d40f400a9406400300b00d0180a40030308040c040d503080001644040c01320000c40b070510a0100c4198812074840e0b1407450003080c01c2c032605505540c260515032004041b02403060300990f06400d150701a1900c42c0c8101100d43e8207076612401c01c100c40f1400d884140d038460418000003407160040c40100f04800050400c10b0804140ba00043c001e6001100c01c06455030300e4481000746c40a6a10301c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 360160692 1250 360159442 360159451
    0x36010510170703030c0f03031d070614040609030602070302070b070305070b0a0903050d0c0e030a0b0405010e010507020d030f11070506040203070503030c03220f0303050c1603030512040f0b011d 85
    0x4140b071514544005217003000307545c0c028005040030491282450311940010302c002c0380017540c030320000303000e85481a0740d01040d00c2451700260140700d1203806002d582d8200c8040b910280c1c1ca002c541821a1200b00c020f5004000c02c60940c07052100014141c1d0300340020709071442c026110140c84200070700303004003072210082440d549146483d01c94000250000151424414203050000321a00d018000f9a98113000c5100c207503051080d22154800c00424203000da00c5a4031481c02030000c5050a140d00303080c1c500585101d400360b08200900510244254030a0344041c0c0b201d400819489914081007400303170702c400020380d05074000b14100f01c190b06041240324000d00d0305034019490501c120041d65264084d04062040c09900410710408514000b40070001804000680f40640c0b035a914001e0300550006003500040d00400c00b03403400c004891090042102e0300341d12154500307409540310a501d110020411507040f0071004055001c21007190419020b0318180c8034903041c0d50408018030889440040 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 360161942 1250 360160692 360160739
    0x10050f04150615110a0804080f1504030507031103040b0d0608010e060103020a05040207050309031c09081c0e04021303030e01020c0915010c02120a0c03020f0936010510 74
    0x104600e4540b0070800c0c40c0c0518a1510300d04d9081980360250070260500000340c140c40020501068004002c960100401007550445010a00c3d03064140070148007141c000d4045501807040308080390007084620034a04181c016603141c5615113003010815005032980001165072a0414030040009229248512082c000280320540c51540051402d421501a442c0a0303600810301c0c10412008000740c4411040040c10b1b2030003445006000302c071424481c00e00701d0001700b5005c00000c07802d60118400d0031540d0307011240c48450945590980e01c4d666203a140c141c00c550308020008654100820071030140d846941c40001d002e015100091a0401080e00e480c0f181103c1d009005100b119000c1d07040b48040c0a003006540c821460000a50559280710a01d4003030060510750b9081141c080b0b1418242c17482240c2121161300c0d00130510001a2044940c0207140c2c4100c109089103580740690000e012180702d070301c0b1891141000341603096031010748020b00801c600d040f05001586040d5014018940401e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 360163192 1250 360161942 360161951
    0x13060c14011505100c0204060905101d0c13030803090706090b09210a14150a270c080703030801152a11090f04050c2403060310050f0415 60
    0x880501e004050a204080c401c213101a08191040d0103003030340ca41e0041d0001c00400c10700313a070340c460305000d02800c65400f4222140044040303682c80d055280c40310321b40d100150b8a1742c1692410240714045e440044107481c43d1601d03200c0000040c9400008510440b981406840703610314201c00078041c0c10b0389422070069094144000200e50f2103800d1600c40401c0701807400c4090030015401c0354141416540054200104810308034504100041c400b080078a1048120025031344807031450049179402c0707620070088490484110031030075029118140460044c1c0700040540e58510110303242080c0c5a01c03c50210f40e00c3e20041210b00f01f44c0704541910321580c2850984d01c0d501002440d0309010102c040c4407404e041c008a0014440e41101c110341c044005010790900c3d06120303c58045c4550b0489045850f4494451001d4803070802003007059406841c0e20303080702148071020320480e03140c000621540d0580300d01d041810412200380511b9003c0d41a0f000071804a0a06003441450030403009052030070b05062 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 360164442 1250 360163192 360163211
    0x10204051005090306070f020c0d0611040b070308010803041a07230703050c090c0301061d0a1d061503010911070c090c020f010905030301181404050106090e1501061413060c1401 78
    0x480c80b20342780e02c0e00711840c011203041450800014410303420809818031010501042c4414940000d10381c06010742c60307010250ba40c801e070140da24812402015480c001c99154880000603400240070071a129114411240541080b0144000002c2000b100c0f03170fa02c0710b50108184402400807010401013911141000d02d000c49480b422448184500400c01842c000049440902d40030b100e10100e100070510b18209030364500f12446508084108001c001c20308002c80d1045c40c003121064410380403980d4a500316843c104440000781040001015040c4007000b501c1d0006010304176030342c041d021543d00001d20142c0290001e183c0524221407544507890702c690361001c9040003090307a04481c1c0b4012000c0d100d000030140300000d00720003480c0d60541244070040c4010404190060000d85410b5070301080328510105107070b9500c070052468000691038003001401868401d02140322642800140d1303501d02204040c0040108200340e002400107104a07607917034100b018a4283d0004642d1110090000070b05 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 360165692 1250 360164442 360164447
    0x513140d080a0c0b0f04061b0903060e01020f04080f070e150f06041d062713060e0d020c04050f010819051e0a1a070c060e010204051005090306070f 65
    0xe41500038081d8078011606503480740c03003240324075051944040340c903115091080e1078141e40401a10120380c2982800c0755000108000404050103403c2a910780710b506240d516a100108258400d6400f04c0d5020048043d03410000d0b030041c0010150390000300b450000e80c0300e0701070414a4070380001100c0e220b200140f10880c00314410400c80c0e0390040b5660b000c0c40d12540b0009559114a0380030035000b01c880c1040040d001400742c0810311481051302c120319110302248082202080d8050003201100d0140d020400c2520304202c191110b502c1403800140740b0642201480c0350072075841480e03006034801202c206190615000d8650041d10041e00124154103020f0851b480e2600341d01826440201405424140941044400c4115054074450261807401c20070094484160400a0343c05a20f0185014a1000c042c58603070300c100165035031000010a940c1e01c1c04081c003203580d05040755640a01021520741c0d110224100c202e4031030703200d841c0d445a015040c14107102004044800b4060084019894183c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 360166942 1250 360165692 360165709
    0x40c0c1103030a140c012a090e24030f0307050a1214071218080d020601080703050c061b01050f0708151513031403040837030309060c051314 62
    0x4150fa0302481d1151795946856004055202000055441600c20031824240001d2405111811039541140390307901d642d5084401141a59000704045007074282c091103401d81000f544030508001c041d05c10341c11041801d0f13032550300085415550b540215182000300140400c440003401403030300b000d040c480c0c41d0002440d00350050030000751002c0b0b200c501d6070048610542c6940c1520281c440303c2c80c1e006441c0c60781d0a980350340010800c009886800300204084100081c0d99040f0b0f03500c0700007840740005c0803083c420039411840c030302070010700308403d0200010340a0246074414450000070566514190400411380e61020304241d000560020322440e00d0f40b108200040c103100e040c003006a5445c5403062044030840c03943c0c0081d01d200c1101e00d850700d904102100070011650f0139001c55003140c45080c201e02440300ac203c1c442ca651807018480350281200901e40c007646d14001c1c10005a40c91040c1c0325042a44c40102d03898000540c0020240602d0784158000000340040703000c4003d00b90410400b160041 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 360168192 1250 360166942 360166967
    0x80a020a120f060911010207091104050118090219030c111005060111011109030f19030c0c0b0d0b150f03010506030408090307060302090301050a1b0804050c040c0c1103030a 76
    0x11080407103207010b0101e003508490300c456111208014400f00d50070080709202652030783c0b034014000c500e00002c10301c80314080c2840061400c0c1d04103240c1031401d001591040d00c00e660311a070288011400103250b101505c05003298081030406d01c002000c0120b802000c40300c1d80d4068000b800080d05255403007041c001903811040c00040c40c00a1a03455450043e0f030581c90a0701c3c445115801c0c0a41d14940c150f4080240c83c81c21415003c640c1101c0901440c15151800780602c40d884504400001022074070401c540120030b40030f070290410302d54562102480941c841c02e010401d0301e840d0107180700c4a0030312802c4061a0b980402030345080c05460036860410303100603c0f0780c500c540c402002080621201008079002940000c1c112400c0e1940e6150190107900410b81c101c1c030951070b01001402d500c6050042003020707500c07151142c0c8005006501035a440b00040c00545e02842051804550783d26240305207581c10080d40c6824040c1ca4251802c48541d140394071216000703400500916002c00d8100c520780252 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 360169442 1250 360168192 360168209
    0x20c1903120807050c0a052a090c03190f1b1805130f0c0804030801050f06040509040303060320040617031c1104090b040c0801080d030c091e0e01080a020a 68
    0x2e5150316200301c07050b0044002a0146000341c600b0542003207000180d00920255106024594000041e00d40010b00c144808081e000443d880c001040c0b0703d1000001c642c0030400c41809a1010105103903081120020142c2242042c0d481a100d0410954003e0007021041c1c0d0b890044000465080180c1f00c0c0900c0c3c0c842c59010340100486482443d425400c031021088a03130008114140c0c1c00c80c40107052400030341301603003c81e05103400480d4904210141c2410711002400c440d26284c03410003409840c000040c01a0100740c0c0c0ca5001200088541c140c8008042e0114440b03076107050a00d0401c402c940c503d5010204032001040c0a0201c076802000351092014030314030f581c11000210b031489010b415842c600002e981ca0001c0c001c02c0c103115943c0a000321076016101000300c10480360094460704000e01400c1e00d01d900044078203040d18400d411043d450040c900d0701c0c2d40a103603540c44101080c0400f08500041002005050000d5240382a2250040802d40010081010643c000c20003601c0a40161080c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 360170692 1250 360169442 360169457
    0x90c0e280b0303090402030f060109060302042715030303020a0f0806031b03160807150e031f0b0d060209011e05040e07090e042103061802030a1b020c190312 69
    0x282d9081c019509105005401035540f0301d0241c5158006000c1250307401c0c0421241c1502181680c400d00c241d40c00d0b600385807a540a0b140d00d044a12291400d61052010880c0e200c0502c00d5001014141e003a00030f511a403009a1243c0400300080c0c442205240384e101004401c03001c000a03550002035030b809904998204150407521507020a06040a81d200980c0c0300042c00c01c001403881000601e0f0040360103813500503c01c0f540d609000c80c0c465031b42c804082d6140d0300845400d0b08a0038201c10200301020b0040c40002c10f1410400031444401c107900003030302d4803503000c142c98040b540c206541c9204015070941401c0f042d1070b400402790070750260740519030001a810002604540c000c3c022071001c0c11b03029216441c0e80c542407a2031124107604d00c0c95500140800d46403441490301074090300c026502d480302c0388080c0458811014000350801030010341255121041d50b45d0340102036a04920140a035806408000d007690107120310300540001004180320002da081010a410a080b0800c207036041c07a0110 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 360171942 1250 360170692 360170711
    0x2031b041a06340b04020906060a0806210a08091203030601020d030b0103060515030403020715021b0f0d080304060e06010513020a0c050d021e0f07050909030409090c0e28 75
    0x10a83d00c04015980e10740900b100c0301c4000c2c0b01e0700c46a010f104038401c0b43c20704d070550341d03080a11030720b4050750a02401140e1058081403d524241001224100c1c1028803424090710b5134000500d0500e42e010140d80c0001c00107012412400c2c207040d0b00e5115202400154554102040000d50b99050b44d03610204240d900c1e0804925688a90000f02c01054001c10164802d402003520300c0003a40241c03001c40251241d8100001d614140500b0400c0c40e00313940d009041d0340c15902c400d0300080d4503004141c41d84540b03050000b010507500da00c86141010b000343e00c0f02d600d03490540342000486884031000781144c0d00100042020f03039144d40e0900d0049550390405a00d401c41e200c1d0590342d02c020305400078603a02070740d24001c040c3d40c6e002403d1700c40300c0c41c039441610300050342e41400f646400c807500d0000300e1034006640900143c2040e4144680041260080b40d182c40e98450a800445580c41d50890f20000e83c08401c11052240d01d40b680e1704605610000c091190740c03402054582082204622416038982e00c2d4407 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 360173192 1250 360171942 360171997
    0xe060903130b0d0b100e120f0c010c0c08010c050403021305190f020d0e031809010308031b130801021305060a080a0f0b091905130807081602031b041a06 67
    0x208001ca0b030140004c0d8241d004407070086c0c80100010355003801113a499003140204540002d01c4151014007074040c0c03040540340c00c011202001c0d100c205407801d40d98284005440002449070048640440e070702c0686950030f40c410000c3e41e016041c42c81042a0174101441082820030100b150944180080020a00381c2004100080d0060300c5840c16882c3c0340403498041c002020008000d841c00008445104011a108000c0d06407000c3c0030252400100b840011040c1c0007449400e980001c08690550a180b02030829040180320fa40240d103680c1d4021174400308040703900307211002402c000c540003400d01c65241d0b1f00900f880001404038000e6600c9010b444800d508039449031081000203000d40c1202d1074070245581101a0b813080b10b8000074034001c0000c40c204480d030f9144043c15801303912289040465240c00241d900644004005021554201001643e0412000d160014400406030001041d90308000854009483d503001c5407010010488241c0c1e200821102200040203080b002204d81c1e01c00f0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 360174442 1250 360173192 360173201
    0x41e080306041815060905100308070602030c1e0d0c0908030702040c0519110607020f0d0806011407050105040b01090b030c09090102040b03042423040f080406030e060903130b0d 78
    0x3900f040764908219035013200e0b6800000030703175002c84400d000c192182e07508680300c10705034070015000240600c1b00e000021066001546c21100e00c000403401c016129400300c1d544061651002000703400041c400d2400001c0303006400541c0d4450801e09003003490200025160711412070024803550f03540da80510f00134000c0041e10038007450b0703541d1044141c48540018201282c0900414403901c1080c0000707c02600c00203066441e1400007004c1c1c490801201c070191007499024154906118007054201100151540031340145800b901c004681400d05080801800006070030010100781040e400143c40d8400040c0c01e00c0c1c000307081e1507800c299901ca03100c0a0080c022a040303108010701c00004e002c188103400b19444c111000801d44c10a181130310f013070008120307000f070b0b40030000300f0302d800b4420314101090303117a050b50150040c4003070446d21b8816540c02c0000da2042c0c0118003c00c1d5240e0441d480414104a456480100c0ea00114074000002046569501d403c0c42000c000080015002c55440c4550b0070 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 360175692 1250 360174442 360174491
    0xc0901120201090315020c120c0a031107080a0f061b02190c12030f020d09050d0b1909080315061309020903101b0e0f1318021305041e08030604 63
    0x4980d5110005c5c2c02d480040e52051191400d030b0300c03914042d409010940011564120302e0031004001d070b0041e0355010b907524080940400420700440c1000680e4003018044403050b144280c0b10070b4108400c6250040480d114080c50110b01c20fa41a000c0d07403810b40016080480c0c0a503401118510f0840c0e241c160b03015182a081541402c0c5401c116508042c1c016000e905041000d4007501c1c168490b042003101c0000c0148079295011400e05e01c0d2a01180c0300d804141d41081049402c5211410211030050546030900c034111802c00002080061400c40c4004180501608940443c0381040c41205d0341c40103801800b440001c43c1e0b00040000040c0d030204043d1125002c030080610025090175141600e042c03042c0c4121010500c0844010070b64a0407424020f00681d00401249060b1849100e02e001404040221058680802ca1040243c1e603195180004d04000400c0070909182515041c0703040009040050b02c2407a0001904c4001204601640e5208400707031340c0003810341c0d1004000d540c18840c800 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 360176942 1250 360175692 360175703
    0xc031805041a04050c030f0a020703120203151e180a090c17100204060f03111606051611070303180906080303070e031c18050603090d020c030c09011202010903 70
    0x303a080045a65002c1555454001110308000503030350f2140c0100c4c2c4e8031045a004800b201c00b500003801240759a03000c5d1102c01e0013494010400120721250000300e038400e03560002c082c1c0d40202411140c0c07030080b240d000494a0750441212000ca07410118240d9507480f0b0b20264000c035160f0010300c8409403580001c586a402000c16604195500070010400d040e00c1400e00180c01221080d1403a40340e14001c40f0221501c036030b0342c101e4000b4011804c400901d40c240000c00411010008420784414807403000aa240c003aa50014403070800c00e80d403403644650322aaa1090090640ea040240c200101e114400c4a070076041946039071160940f040750500494010350203a81c81e0440c0440c00d0032000024601c20082525100e491850b40c00800d50b6540d61940c08401c02c0003800c3c1c0d0407000901c612001001c100228031200342a0341c844c400503180380c000f01c50b04102680803881e443d903480d50410200002c1101600a00048036100d00442e00ca80b80500410115443d142d481404592251801c3c1c0e00858104 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 360178192 1250 360176942 360176951
    0x2180402120a05010503060103030c0f031709011d06311709040e070302030319050c0307050d12050f060f01050c010f1a0108010f061b1203200a0c03180504 68
    0x207075000c040608040e03a1046500d85480300204803414001002d6041c0c80d0184c841c5d50b041181551250480d003001034040b81005041d6000010009040c054680554040000402c0199040d01e4034145d04085407003010301c86d0b02c50b0003800600c8d020042440e4209400074600903001244a40000300184620030007010854034444089640107800007a00092000700c6050000d840d01414a41e5507402902010354590003c00090600105c8082e4411548030700d03080c07103414249161011800c40c1c0101000b5105078224255203e0300c0340d40410804501203880c0d00c104418103021541e4100320360000c2c40140a4a0f030b9425108840e8002c1041c1e4200d15549002480550001c50380c807800b4012180c140090440300301c07102c10596001d120400e041c3c0700c00c013402c07620944c40d0840450300d6403903201204807100c21480f9220702151014940307065600e85610080750b030030040361140d00b0440c00c004042803040801c1c85042415584103c20b0301000d609894004082010705c0000e000f032000d15480a0b5201b80341 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 360179442 1250 360178192 360178207
    0x10302010c050f12030604050105040e0d120e19120503071b0f140a020111030702090a090c0f0b0a0801050d020607060f0e01020c0715090e010e091501080c040b0307050f0402180402 79
    0xa010043d441b030700c0c2c1590140656640e0350144401c1c1c441d2038030302501c1d9402200036040564402c0b68203102c0c849600350003044080103012800e040940300c04e0034030211002d0321003000a20840305030b402100081460032034038503d02050014a1a12403020030140d8001200c181ea0034825491107001c0100e801035603521541907075945541d80c4101801d0101d010510000e944141c021001c4151750055402405150f0166035070b001500c010902c1d18170031030b20400201004680714400b854000054200048420b0361a007100304e02400715801640001d126049103410701c8010703101c0d00141c4808541c88907011942e0380c81080150050000f044400c16190300c0464952100b100020344032044480481c421840c0614a00e42101c48503100d0252410a034411070040110f000c0d00305800b43d0000c510000e81e8014190101c040021220aa111600592084e04c0ca05a00c0c46c2520500358042000c90041c1025850180410f88014504034640c2c0302e55408039a940e21b4028045059200d003c0007402103544810 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 360180692 1250 360179442 360179473
    0xd12110414120105061c0212010207390311010c05030d0c12020f03130f08031e1003150905010608030c072103120c23030a0c080c03010302010c050f 65
    0x1030100c1898468801442051446581031041d203000340000b9020340400300c01285107181c44c0806020885e04501c8150a43d0010032003131018201031442410303e09100c10038001f95040e5011a40b0300a8602140003903081d0000c330f8000303100c5048a61104447c8030103140e810041e181c06404240c060f01c207020000f0b201507409003503823100606544544403c402400c45007014812400b80220083c424181040440e80483d40d0203c502c51252052000318081d050b141c3c1e441d000b54005503041180451104181c55022110074401a4007590b4500b0751290b213450754540c50340580c1c00c0e502d03032483c0507502c008001c14840d0039000328010f805400f0817aa030341e034528481c60355206144d100307000c00c118240f010b030000c0303885400020340728030340580d40e0100e84a0588151001012100b034014144032500160f210700d012605038042d9508030303212840341c680c07600c030615400780c0d44d20740701c95010410307801c0c10480c0c001c05140a80e0b05494081c64400765182080c60201e161016009c21020706d0301c102e8a4440c1600e8 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 360181942 1250 360180692 360180719
    0x11b030f032009060c0316060603020f0103020703020c0913020a080c1f0503070503060a17010501031b0509180102040b0301080303060310140f090705180609010f080d121104 76
    0x803079804200c40c4080203941c105000050900c0c4420ba0020050300c1d0880c03030000050002141c01d80701313a9280ca950b1602080d0314102000e0200d80c100d4a0310b604100354503011044c0f070f1301d004007800d00b5132070710b034190b60002d4403000b944000600c1028002c011600c1141003601d64a60150301400c6040d1064864400c50b680e40e210b403552034403694002202440c80c85060000499041598950354155180c040c0103445941000f01013540001d001c0d50002081c1006101907241040080c00016465041d801c0001c4002c100350001c080e4500c03d13000c100865100d032000150300a4900d0801c0021240b0200321502a21480d0f01040a80300040000310710b0801c0400118054a4210211440c2c2e04286011506690381519001c0d806002040007071403410702c8d8402140d0100340d44098484658942c0000f036030140c5260700d03808600b0f0b00071382080024101104040e0140034243c0000303200f030345032000007592401662410020842e07030707620100b00c510081d086040745a03241c5a10688441e16409034010300c5 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 360183192 1250 360181942 360181967
    0xf0a0509190e01330308030403141c09020310020c15060f0a06090807060206010e0f06030a020a0602010b0a14060a050a020f15070206070806300607052a06040b06011b03 74
    0x40841c4800c0d1181c002c09410100112584686c41c9801c41c0c4d229201610b940d9696000010041020000f01202c140b8a054441d500050090005503040380741c0103040c80e0405806400c1e00c0a4810000000110700003e542081e1000d901c0d800d02c9c4641d1608041020405000360240d0483d40841d00400c40f0358020b400041500c80c0dc900b02e0300d40f81e54801080780c0c1e074402841008184c08a610121740520f2090300c070a50310032400313130807034003070220a5002c6080d056050380054010b07592003e00070301034038061620300020110200c0d908040da040ca000198580300303803089a814444001165020079000344207240341e914060041e030b0410104d4030031078880c4040c1120410014080d0900144055005a581c1e50107601d0241c8407118031101d02c0104081d00c01d400680d80032521921100c1215228100401c42c8a0303089603850946416840c0100c3c0a940c2d00322401c0358101d010a1a021102c8100041c080d40c03242d08081e05400ca0784901005035008201c40089000081d00b061301c00e41410b400141c140c940 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 360184442 1250 360183192 360183251
    0xa03081b1f0b100302032703070209040303020c010e0a0218130803070804031e0e10030e01060803040501030c020d140f0d021801090f1404021803100b0f0a0509190e01 73
    0x1c07060748032044041b8801212105206c01c102085101040d584940c22a50042c0340710840e881e216160300040d4900c02c044808500294001802e450f50303100070301038110221200c100404040c40f940c2c0c00a866101c500119402c005040030010360030201c980417400440b07800c00179155490510300d100034000541281d059012032194030800c1080c5410607400c0d11407060981d241c441141e241405c1180719540d10981900301901e80100c000300d14000c2c480c9100500486004650b5249004000340c140e500810f1a01c055401480b1206840d80c4c01140e2046c2900c840070215503101c1d50141305036264044e0748071441507107202241400c081560149480540d040c00d88a485c0c0107030ba1201c1002ea82200c0c0d000764960451100000c0c50107041540103032500c12280c50789140f8941102001c00e1500c103000f03505c0d0800da501d9120180c4203041048840c19603840a40d00c290586041401003204010040c01507103400508003454480700107160b002d4134044180100901c10b00e1050401600e0039018452401da5 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 360185692 1250 360184442 360184459
    0xc1701021b060109050c090d11040e070e1f0303090e070318030201140c0a0e0d05031e07151503030e030a0803070507020a0902070317132306060a03081b1f0b 69
    0x50556020082d907081f848001c10781408010f00e40c0e6541200c00680b04407070f030000d44032601d820300c0c0507080c040400070301445600c0040502d0500740c06030000c8611503400061064400c020300129a2201502007590651484601d190700c030090114020314017195055105040021248101581074006400448004104003446c3e10303103090080b51842820401c002062001c1820000741c02d09c42c2030404090300980940341080c20000403540340308243c26403d4900c03d0002846000c0241d4881d0070314071022540c2041011203410f440c00d010020150101a0501c10380300d4042c0d14560381000403039029503100502544030306210601800e9508034110403481070500e060007241101e520700c269002171b901513a4944a9604c103400080300c00b2005081c0034902403980300040041080724140c072402c81c0d140d1104101c243d080e2a0a1414640040c006502c10f0861200c00c101040081c0140d46601800000a841d544400400c05203010402c0004000781d600480030680d11585641c003c0c060b1042c250785144 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 360186942 1250 360185692 360185701
    0x90f0102042d0e0a0906060f06091d040c063c09050f030a02040510030c231c080c01021210030201030b150d0f02090409060608190c1701021b06010905 66
    0x2070b80080c075005006a81d124040081c03803c20880d0881c81c0c0041c01050001101902c0d01c03208481d8420f180c00003800302d82188000c00c0160310255004601410302030101c100d40c20550303030b418a41d40c26882410200842c09203000107100c02c105c4100840404020312002c20000da02d60400e8641c00030354003e020400600e40000c55040000031031580210080140006014a50820000b820040c0140c0d078031440c80840440003071206004030340a04580d8000f141050030810b06a0043ca50461949003d081002203520451040d00518120268000085602c2e000d0021550340207019851054280941003c240000c00c001d00c2814000e8038005e0ba000d20010780c440d81070bc80d1442038620709841c2503404001c01c070b584495507401507070a42d1486001620703010345c5c3e0b40040c060b101d9481c4181e580300d40d203e00c02c0000c03840400910003903003803aa070707003035a005981d40301e2242d030078000c0c461a141d03c0d4901c868070060071020f60440790703500b03503071500401150000d09429903103101c24003030286540c0c906800305 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 360188192 1250 360186942 360187019
    0xc0d110f01061805070504050621060d0203061603020c010c08060a0b09030d0f09090f0e06150f1c08030f01090e070b04150c0b010b1309091208090f010204 68
    0x1a0300303807503e0041104800e000d1600c04401410005c004404121084c031020409654000081ca00013481d03039001c0700380c15105a003004151a01178101e511658060182c0d40051314041055907000800b100c4203010400440c1e02507003c0d120303070301d030b1400765500c1c1006c114032094000c05035a002e003206451030001e00d522209500110b100742800ca0381e1650044c5401c030b612600c42c030001580441d1900e0004880b580c0c6803250000c1d184405004d800301500d0b0352901e0ba03003810801041d90301031004480c82d540400810003142c846460380791110300070520500c06001d00d030300004101415660005043d65603103008490422811800c0c01303148840c908000c444d81e5008000240142910010400d2a203010300d40020740c2d041c03804440c8128188100500c4030f0000c82c49900c0c015008040d83d60340c16640d200c442e80d9012410050760000740109180209030b0006c10014089009400380600304800a52100207641d85462407144c2d24034119800094041168100d800c43e028058008104100808002042c43e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 360189442 1250 360188192 360188201
    0x31e0201090b0717041211010c0209070e030a0203060901020c2401053706022a04020702060706110a080702030309060c03190609060806070504030c0e0c0c0d110f01 72
    0x64000340205105001c103941c1c640040c0f841521849000100f40c0003442521000c0c1c00135030046414511103010398050040c480400c40441109107001c529070303c01e03a0f0010b00420005490102084803880410391661820441180384540090440b0356501c0c00b4102d080c040d6004070340c6480680941404c01c0407045010071003500348401d200c140301440e828001481b08421b0360300c5081c28465910041640032140d84010451503640a801100501e424000081e00c0d110280604048861600460321601030801c4c20704030300c95004403000340e520b04240c0006116405140000b60a807894041b465001c1d0646500030b01140100780c41e0180a0360343c410341039859010480e6801f050f500b01d0310001d4070429441006540c080c60098070030700e102c0e10011030502180c1003500301c42046070340e81d0018402010100700241e8018241c1c9095803510b42940d84804d900e0031144100c003103002465001c10462820602074424010380e1030122050f01e401c040c4020420220388218100900581c0b460301d00a81c0180070303 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 360190692 1250 360189442 360189503
    0x2160c0626070806010c0b04211103030406091a0a05040b01060516030c020103320a0b18040303060b0c0c121204060c0206040b0705060a0e03090f01030c090302031603 73
    0x20649250360759080560342684010051030401076040201c01c001500030000c1c80c015406448258540a01c2c1541ca241c42a4003c545009000c2c43d49240d4001c6000040cc030307030344541d0085020034089440c0c5481c0b64200141600b02da1861a9241000b01c82586688007074801d43c0541d01080d05a6030751907058409201d600706c0701c460039008440d0800803e029110300194544189000507040300752421302030055082c5003103440034591050700c4800c90b400742040c098004c561410204200b030b8000b00081c6101400c1003004090f00121070014041c035000c3d0384110010b00c0101c1c2c000e69100620200309440d0605200300911918040070907001244001544841f01c0030145e04041c076150a140d01030b198400c1000040345d212108000100d11026100007810f00e042c859002403006050100700e9a00769010482c8466450740305022a03c05541e40c5d00c0b2201d61a5005c0c20001500d100c0c07076004803a8a50a608069058403c1e500c071840444000304403e81120300a141c410840840000844452030100e41c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 360191942 1250 360190692 360190757
    0xe090714062d0313020a1a0a1409030d030605130b0609040f200415050a0f050d0f090302030918060f28141005070507090f02160c06 58
    0x1c40055002080d9040490003440444028144410b1204a0441e0b00c226a00c1081000f1102c10b0303411420440c65030806032540c0b01d000803541a16003a09040d500890311030004001c8010181008007403801d0490709262000f809a80103140103010250140c1220301c60341c8d00840360100d01030b000000c05e20034001c00302001004585007000c08000c001c090208840d00a0880366180000016000800d03030f96238607605004003007910f891911801c07030f40740c0020300f60741030a1000030018038103060b5001a0600340d0f1006410200d480b041c10a9101c0020306004040309201c604d4140c40c1d50030f00d81c0000c043c0c5081c94045804a6190915070f00240042e00140d0780e80382c001020f464070104915000781104259189400c024040f1104080d811094500c03071740c450f134480394400f10045014289002210f46030a5242010f503e05081035450b281d49a817070344207007100a80e0300c9240241104aa404076144030003120745481601c0e11a085c00d0040144a103e00e101003102041c50f4840c05030402d000700341403107035039 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 360193192 1250 360191942 360191947
    0x50604032f070515090604030f0c0f080d03051b0304030309060615020c0402250b01050103060b030c121008030403080d061512020f09150c060a0b0a0b0c1005010e09071406 75
    0x20074041d00420b0030307584448a4200b072010103107685071080030300300460081c1c0d0418072100d110304002482b0301c0c00e60800454203002e210103000e021300000b034440b00400980707000a2942e403046881880980c50380e51342c41d07000600000b840103060703240d0410204580120780400451340d9a151030840d201e0703e0251100543c20070251070401e07181c139070b020b04210340220041c039542c800796401c2c08446e46007486003110701d405604014030413540e1601c038200240c804e030321500e481d40c208001032111b68004c04400300c0103000381c03400154070351803174a07030020051108908803030f00d940c1c9a20345031825401500100050520b4410f001895150381203d500c0c644c011a20344086201034450340102961100d007160412610400440c0181d44a003400c4003c80c071000307140c0310344a082075203000e400c010000d4008c0300c2d0309051a0288201d6603032a0100401c4424401c800d607a2024000b40180c10820454102d0884e5403604000182d1403a45040f070b181318011a10070342d40f90f42c0d2241491448140e80c2e1803840c0c0c000406 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 360194442 1250 360193192 360193199
    0x801080709021e0a050a0905090606030f04150f02090f0906010c1e02060a03050106030c0942020601030c080714100c0209010602011d010203060d1e050604032f07 71
    0x3603900030b080760f0b50006454540342d620402c0e108010351105018400003500040c1010742c25a000e101180500340440384602c0030f0030000006000350001814044880c5d0300000810100000c41c1d84410543c148480203001110600c03040328001d402502c5609d015001c5410100344624240c602d0600c1040141c40300503101c807403901d6001c0303001034036400000700c000d003607441070050b0752a100500011421549e000c1007660400394010b041d01d030402014014043c40311418014100101043c2c10a102c01000510151150151001c3c00d020f0740c00107402140d4840c50308024440c0d001c00c0c2c00741a01d003c0d019881a0f581c1d80c4402d039a950301ca5100b004410b610403001d4480c00c0c5000080020380b08407c0c502050706c64159000900010301c2a4400c40150b0355406911200106018001d000c00190b40000c6055107810300105014415094008080310010441003c0174960043c0c07424150381c21000300c49591800303103405030051821180c000740d164040d50720021015151b8020441c0d00c1040e00150084a28 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 360195692 1250 360194442 360194459
    0x702090c07020a03080c0715020a020a0308090301140901060e07020a030512130204050703050a0b010315120611030f0601170106020c0d02040e0d0c15020307020304032406060503061008010807 84
    0x1100004036404000380d080080442da88801402d00c1515017006811f2442c40c000021641d03500220b40c1e0300564002e401a031015a58402d03000f02160303002815640e40c0c1d0385400020b0f004008200001309040c0349401407160350030341580302000f03035400400c01c0d80ba15100c1a40c140e9544502180042c00514100640f04000703074502219608000f00200a455800380f550011781501d404903080e0740001c0c0c2e04c03400c01c151402075004420019030300b030800300403800200481124001d0a8040d50080d40014a0928100440755001c445503580d4401000d4603410b040480c50b041580a035081400101180d0107110072910000990b412140150010000f140559003840300f50f1510403405d1380d215944150b9a4005081444060f418074a9a40e8007080d17140f641c070303119450640c0e6080b0040c0051060042081c1250000102e50640380c0000d02480318100303101c0c0303c1c4840c140c6240c06500407030401d9400140a070300310010310301a050440c4d4082003401c3c440d04c210f41054007482a041c403a8400c0800300160740 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 360196942 1250 360195692 360195697
    0x305060901151e0f03050705031003060e03040801020a0807080604021c0504140106080c0909070303021f0e01020a03020301140405040b161214010e0109060b07030e010203160c051201020702090c 85
    0xc42c141003c0c0042a141e415510860b8200903489010604140004041d540d061255581c069140d0600c1c03825400e01105103d8445064040144840c0d900c41c000d80c004003081054400409500e002076580307203131062000341107000a0782c03090045000c46000c00c40c13a1a1900031b45034540c00d840030089005036601804000380c00003500903545250140b000d4a80748200b809480301404500004000c224592000d101100710000e01c2c10585400200d018030010ba404200c0c96403c0544641c1e902844284a2190b402840d84000103d031b0740d0710000740000c4294050700514102c03142c4001d8107584040b4601800b0580d00704982c001c042d1201c00002449020852046030307245c801c6841c051102c0e5201e100b030716080700c07000755000364000c214000400125115180c0346024016801061082c84c0c40c1101c00005030046c500000d052085040507070106034400c02c2900ca0745036003a030302000d41c20070604100320050b61a008a40c0180003425400000d440c050003200d200a9015181d6803aa541d000580d000ca41c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 360198192 1250 360196942 360196979
    0xa030f11030f0304240b12060f0609100b04140f01050a08071404050319020907020304030c061b05011404030e041a0f030307050a0303022104210509030304060207090c0305060901 78
    0x9084c0200010041c0c1c041c0390510142902c480800501d51041404003d003141c80d07c4c2145440c0c2d4005e00411040d81d03100110190881c0702950301c40d00d16100d800400c400002130b42c000343c0d00e0300404600050214420101061442429030f8010355210408004685500c141c82042022400400120381e126100e64100c840c41505120300c20300f00340e01d0343c000078201416400300e9032441c2c000b003221105503e8452001500103515000039882d003491540c50741030107902441000306006021140c504101551030360080302e95032000007081315041d50003914210820170b45007034002070788100034040c150800344294221903003541c540001c070381c0081302040600344d400b02c3c1340354040c0001e0180701c00060080021134002c0744640c03001351f140c04024104c5140c3e80d01444a00301c081c07a000b4140401319003400c0c0d0005d110319011840d0f42c42407103505001d441e10311400d800a0741600c40000e001400717650126400003034403903180c014440080940c80031004d5030008d844259024082070010407910340c458420000741c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 360199442 1250 360198192 360198203
    0xf0a081504110306090709180f090209070804052104351b100e01050c0c090c0409110901020319030f0204090f1d0c010c050f0607020a030f11030f0304 66
    0x3061450008a4180c41d80da0710752154480c0d01000340003440c0b6100d145546e2001040c941304020f00d1400610310341020040403448041541c0f000c0503c4403030800d41040603002d070050501c10840c01c1c00a80101900b0080394140e400c1d001c4c48602c282c1403219203455100d000002c8003028206810185111041d240d14142400451290820340c0000310f164120701c1c1001c600c00001d0943c140c40035030102241980e91950501c83e60307000424900881c2c010807000100d00d000c0c80c0190702c03101402c40580c03805a0316004c5550024000c000c019203034000034022700c00d07a001007600b03100040d01341c0ca10071000c0c00ce80040a002da0414403c0408102d00e59901c004070314038914003c901410010021012a4001d030401c04941d510340101c0ea017510f203075000c0c0d140300700d8264069050a1901034020740d11242a4000203040110743c07001c11040c450200002c0c040d40b0b00140644010741001e00c4041d42e01d40c44c401003140410000070805406030f004182102c4541144000b0b1454203425a1503044140d200401c2142c2 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 360200692 1250 360199442 360199471
    0x90c060e0604090c05090901150507060c0c0c030b071205040506041b030606060e0a0503240c0c06090105092803140d090606061407020105160c05150403170f0a08 71
    0x3d2429007409000c1002106844250307480c2c29000512000c044141c0105611004403841100d5240e80b00c030441e401142c018800040d122500c040c106c51110078908094880900c0b800c000c410f000e03030003c100e40200441d0322407503d140700200400c1d00b036480848018202d0b07040440080c02040b9010454041190001d40ca401d404d07490342d4506084903c40d07085100003c044010f03961050034809840c0700502800c130000c05026241107021b050303002d4480640051104120017207107841400d401a00c069139002002e0781d18503c0e10040c103d000b40704c108c1d4100f080e84107110078501150f514a218248403545628051403058075a10141d42400b0380003e1031048620810986220070018410900510712035800030030164a80b8400031310481030340d900590164800c100160041c1e03085030072229081031160b0a1416904141403044128880e80c0c0304940025510f07120024110303c240003041681d00c1401c0341541003640c11603105160103104544022140d04003c01420749000341580e41c2c2c80009180c0031403 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 360201942 1250 360200692 360200699
    0x12020f0907022b0f321603020a1a0603070b160b040f0212030a0c03030b0409020a031a070507110415050604090e0708010203100e07170c040501030c03090c060e0604 72
    0x140d4004280408010391100c1c042a2003445a001c070241920041e01d14107a2002c0300d64090020f000ca07800e514120802ca205e2002c801c01c0300702941501d10300c243c008400303010110f00742406510303030b024501c08403a0744c5528480030102008030307500310307001e40030160041000e5820701c00008900d41c8110400c0002e80004007104c070025086d00342461007944184a0000c03c8901407042c07005603480100035142c1a04103000e1812801d901ca24400031054062601144890783d15000c40c004100700140070390041c0d00100301000f03201400b0b07018051140241610440c0d03035070301c82c403c8a4074021060010844036844c200700aa074681a0007030300316001031820202d462640d17200007030002d5010360710410040b519820495a01e10b010f204001c000e00b1003000070343c03440c40c02c0f0743d2a5205410a0040c018115820004222034900c00c00310082e192451042a5403141042070344c512440e003161203064002400c04001c00c08040c4a8003c00726134941c0010a04281410408166415060402240e8000e00c0c00d10001 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 360203192 1250 360201942 360201973
    0x10f0608011a091c020102010b01031b0f120f020c0d020a0c0302041a0904060e010b0a0b30090a200109051201140c18010512010306051008030c0609060112020f090702 73
    0x1034848441055800340c0007054170002e42543e201c80b00781d6044c585080750b155201c0c912241440b901c0c40080c64079403140c13a8999004d40300b8480c0c9c6258401c85a250042c0f525510000e5401401c40c8010201123411014071650101e94a6155680043c601c00c2c41d0b0b0b00401c0141006c3d044060954028040c0440710004040842c055a008a40699900ea02c0701860b180002c020300c01c00300520300c00e8900349102408c02823641418403a0b4600d801240901c0d40400141540d54940e8004030010010181d0320390034503410300c9990390b03506001176501c03880282c440d0103001c00d4202106e0b912038061310fa01350814503203010400640d8480d00d40314202e541340d40c04608051100c07664a0f120f0004462101e0300c2c2e03c0a5014840409020070314507052180401880c0c04004030100c00c00c0c11258099004030301070790380400ea652650000da0000d10648030103d280880c0c1000455007510401e842401c80e20079a9039042600b080c002154400b1350040348119a0a2407400c080403401e0b80701070710340100d411840c40050700 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 360204442 1250 360203192 360203209
    0xd0903110a030306090b0f0d02190509010308040609060305010e0403030b0f06040f0f050d02011202071109070309050120041811040b0a09060c110d030e030f15010f0608011a09 77
    0x8400290307982d9024040703942c00b40700d5020841c206642c0c1f056806482008586503030f81c2c01030060710a414003c0005190302d100e40c400d0010700380c040e2603c4a10b503524602486035800c14010390700400d04140c070100d2501e01c2031180c541280c038031504039885034071551070940c0240700800c1030541089400407610f40035281c410084c0005e1a0322104000800d00c0c20078201c40500300d075001940304401d1820f4400250703a114100141101c0388480041e510242031900074403000003c030a00b50410541c001700041e1a81507030107841c4280c0242d0013880b4642c0f0403214411134501501c0386078200300f002c5c03005000c100419020041d032081144000502481c401c85040d15640056103d605d91000000d400603000d036004603410028959802e150b070200504e551081414a03050000300c0c003070080131034400c4c02d240c42035408401400000e030a6442c00100090040d444110240000703005a50107000054540382641e10740044170251340c0e40741440d90a03c6299118146860003a403d59a003e02c00c0b20300565a5415 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 360205692 1250 360204442 360204463
    0x9010c170c010e0303060d08180409060c030506030708061b0c0109121b030e100c0204110307020106061125080319030f050402090115030e010e0609060c0f0d090311 72
    0x24641c40d00442140e860070740304003250030540340d0014418004187c44d01010070180b242d11225564403005000102400001c10b490943d0f80203091151a106100c820350010001c2c001964050007150303201c2e807c1c50f9540c1214441c03014581d003e040007600140d0039800b140710744400101c1513840c0020b031200c007509507444070304203451400e000e0a41c000c41e141c1184800040741500e4032200d140b41056200a0300e40b0152074885805240f4810346180c00921480700d441c1c146500a00800c41403944e03141e9440d26400441d030180140d0b10b08903021070b8050054140e014205901401800c0a12050314104c1e04c581c1c0c0500c950001c00c03424800400d1300039080c800703064051030200b2000c2030742c59070440c01000d0725101200e0400c01ca207840140005a140c6078810340c191484a5500c000784815084200c1c02071040142c5003078203500e815400740b0070b0072010807218045c44400c001c40e8010f45511001403907620400309000340e000c2c002c03c042c0c990600380e6080014500e00038104020360361142d40303030309007849240b070ba = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 360206942 1250 360205692 360205733
    0xb09060702191e060504030f0606081905010e0a050a0204180c09140c042105071706091b030a03110a0b09010203090d020d0e06031003020402070507140105071709010c 73
    0x203082c001c2c03683c4a0b104410401460b2218040070385400c001519078800c5001c042c010071030b80e101402c00d01016410070001480b089040b6404404d900301c1d143d076212003050044130b003075080500340b100d101d07000035100d201a0381040c09400e0041b102c0d03007000001c101070000655015140072004000c2031502c3c2000d001404040b00206030303883d0f26602040c0382d80c0000c04142c4151401d01050011140f84180110f81d0340c8915140d82c042c16881c1030280c54070400c0c1c0d12555403d561001107420783d0a000c00d4941c01180321804641540035407028500c1012050108503070182c8c0a1000070010a1181305c442410441c00c50664020000e41d46802150354402c550140640e90008240800c46100704071003c59980c840c4040c0c5100039482500824012481c072003544904000b20110f81103454107a451030013540c1c000c01c115550100b42c680951140440d100302c030f000d007140c20354079600e03940184111030386154405c0750654100a0303482002615003001981e54100844044039030300144844100005c10701c1c3c80e1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 360208192 1250 360206942 360206989
    0x1d03012d0608010615031e11070203070f0e060607150f0e0c01020c01050f0a1e11061317160501050a0506130608100914010f0506090903070308010b09060702 69
    0x182036065410651229085a2621804024460008981c0c800400c0580340c0841d5030b00d0803884001020401600c11620140740220035000c0c140014020942207100b94159000c44e650744898041000c05480b8001d004d0501c00c001804a140113002419811311070089050031450700c640d60700441e10b0b900d403c03c42690b5200e030b400500072002c00031840c0b020313000d100512100c206580000e02c0d50107400c4500c500628042410100b03030f80038000d1020110310382d07802003030743c101c0ca00d0006180144202d1880f030f0700d020741c41c00b28606042c5a151031502c01c0d044080da1a04000744401410305501c401c5010164034170034005400041e0080c003a02d130140c2c6400c0c801240d81e040000c10041440c4401c0c140701c040d249404420040c211000c51311092000c0000710015805c2444d040c40700012120200c070b480d5551038548a180e40307107a035910143c0200d606840e00881551026003940d568400d000010b004150400c00401c003c04c100c400070940c210002d080d460400d02507901064142d0400c100f100c0000154 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 360209442 1250 360208192 360208271
    0xc06090a03052e020a120c170421050301030302030421140109060b03010b0f1e03030a050d0b0402041410091d09060a0c0c12091a090a080601061d0301 66
    0x141008021446152403046152801182010b40444c1c42c401719161b1203910f8080c03031812540140c480710136418000c1c0c40414240740070300d00100f00014506440460075102000c40300714500c68030689050300d9140d0010f5103007074201304c409074000c0d950880b942c40c42c50782450610700150560303480851800c0104008110424246840c5c0199500820814001c0e85440b50300003440d541c00c040408003d0064030942c07844035491002101c803200042a80b90107110000c0c454001d0340e40000104241211610200500c501840402041e8419480b4a070382c00321146d14514418549014030310110301035030414400c01540c50b010410381200c444040d0f490010090300300f101010082c0000350f4072202044081044903810314020340303400c1241401411440c4802d20044030a40100306a82c0a0002291021403e0311182c488500c6548601c00c214040c1c0f014800c000f90040c2c0002d01d03541a1902c9032181d5841e08000c0503101424040708507a243d056489003100384007a0661503107403140c10501c0b40c111403103080 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 360210692 1250 360209442 360209503
    0x80c03010c05031306090f1a011a0a1e03090c15080f01080d08070c0b010f0519060206130f0204020d050f0c0a020d0f110706020c0a080c030c06090a0305 67
    0x10400074050040c108104400201c0c00300c00c0001d015804130001400001d00e080c000d05c456600c44000340780c080780d50341c0520401c41c90007c1d541244d40500e041084c0510311040d4103d140998030100000c2008501a10300031203000050300c400804c80c0c034001850407100c2e1103c50145440b076201040524184a9841503150f12055050b401008078090791415403418900c2035440b401001403004200c0c100740402c04441c440c104001003241c2041740f05440d0b585030035243c004040300c0e105840c40f6100742c0c00c19454091408546030103c81c07040d0007030405542c1c1c00700101074801000d4411038500d50340c0180c59005903142d1015020403081440c0010b80c600d01200c3c80c0b24014006400302144000c01d03c00d5042131a400034101d40107602e00d18100c620028030400075290301030b1000203031209000340c090101d0003e60014412905840803112084041c0c0d076001007a440740310303021300c554268105500000003800c0510090103200005000b605245549031621410002540383c1c038078425148480f85c441049 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 360211942 1250 360210692 360210701
    0x2030f1f0f02030412050f040e010f060f0314070818060405030a090605040308041404020405091806070e1e01050712080a0b010e012f03040902030402090703090c0306090615080c0301 80
    0x50361041140303036084c2511a901c1d03610340c210a8400704130000840120018a101c15100100144c0907881c1003940c4400c5040090010360269100055100c414045064402d010f1740f1418240a50b8002c100e89411a00701e80140c00100001c40c8003203003090008281c1030030070100e13200f0ac0c000c41c051a11a000310034001c02e2000302d68009020800244424400710301104100e0b03003140d405c001010500ca41d100013140190046500a0342c0c40300751007081107ca4001e01710355007035001045086e00d030b8a80d00c601040d581c1d060034488040e007000306400d00c60400350208510700c0c070001d814104141410341c05c0e1340d4240030480c034080b810005110501448152840e1307002c2e503003d0706000d08004514541000008050540050094040c0251451002103a04101801480401286041c0ea80d21a03c40700c8010107540181e070224003d141d0480055400f40c840d1003400c841a038800ca441440e1443d503112075014105c0800c080e121555501101d1080744400302c421802410044044c0000381103440c00c05007100e = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 360213192 1250 360211942 360211961
    0x30e0705010c02060d020c190f060b0406120b090f06181908030705090103090804080d08010f0e010b0307030b030a0b0105181909080702060a0e032107080702030f1f 72
    0x6410302140c2c010f036a00e04c281e560301c0b500c4500042c0c4412082004600e004d59080e103864402070394888050520010450410942d4001c0c41d0a0002540c0d000030300045805a104001e1303807501000c10600082c1c424a601070300184080d00302c45181d14049048c82c11720070309541240300001c0d040d020221522040c802d580140903044209a030702e609584402c407040c80024501010481d00007001c060b581c1c0294040000c0d02d8001350b410740c50705c0d142c1c0100c545e03e10990f031108012a62620000501c0c503200300250b015a041545980400e9103480c5c1d01202503040030301f00740c00745519000c0001c07a680b010803030303056441e0180d06010f17007551512041c001c507040c4640d02401d001c07002d00100b1140e0001400d0902c50721182d00c60000380c0d40501d0170700c1c00b164019464029807007580000e0b41282c00e6486100b03000c10f510102d094810842c00c0b917403d100b46c0c4142403105260300c0001c0c040c0303401069400016105440c005000c0d1182c040c1140310031410060700c020201000e901c1903011601c415028481c2e4002c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 360214442 1250 360213192 360213197
    0x91e01080f04031b1a0103060204050a14100c021203030c1b060f06010e01021006150906051908061f0206040b16090302040e070e040c08010b04110711030319030e070501 74
    0xd410961801010105000c81010215840515450402289481829080d11285c0904180356141d260900280d4480d105491085049220100e05114054901c640045000b010481054070150090711070501180d0140e0340018015038807101c0702020f1004601c291251244107980e08026556900d001300e00d48009081070b8450300420040c00003c113485500041300342040342040b40c3c010700403403820102c215240c3c520b07800c0c400b000403280e0745980340c880f4004064803051001904e95034212078501903000d00071001300c072003c40d51030f15900422150703810482c0500440d02440c80d240034825503081c514580001a840381c0c0c20032040c008101c1095030406a0f284203d814074902000043c02c20b4400d010203881295992504290044200249402800f6240d03521a66240900304040c00764850310803000305500300011104185054800c030000c408043c5030460030901d8a8482d10f4800c0c908000c0c0503007610003049884c0780d601c008024a4918041950003003010908040d42c6401c00c4000da01141c107 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 360215692 1250 360214442 360214471
    0x10f060c021023040e04020a08030310090e120415080a020406120506030307050a030807080714030115020a060609020c15010503030319091b031109090705010311091e0108 75
    0x16914040055aa50540d103024006503194410004000c004503290f50558100058002020444103110742e200c1ca0085400300c0d6203503591101039450f884105c0c0c114808184401040c040e414031640b00a414007500300440750290100860520a40d129800090f09010310791080030350f180c0d000201e07550207403122100b5410186442c0015100b1541c1e52003840d2104e89034400500240c40420542d0f45013900034003140c00b81412400e01500503842654240e001900d260009401980030f031801c0c1c0c03406400c0702006480e50786030907a010034400c82c10300f245045000e100310b80c0c008600c1a000390701c041c2c0b040100059540ea800c511030741c9420812018000d10844000041102e99408001c0d25804403500948005000e00c8071180001000130240040140901c9802d22920510110203401900c1c810503004042c01d40d16000c01c2002001290344440700d50140d40240440c0d480b030f42103894035040740034407030741422007100c00210380c00e00d4004180d07021030300008401101d41e841070090381c000e0341c80340380200b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 360216942 1250 360215692 360215717
    0x30803240f030c061c020f0405130509060402010509040e16290403020904020a03050304080610060206160f0207050303030a1406090714090d0501020c0105010503010e030405061918030b010f06 84
    0xc1d01c2d1030b03408416600c136503804a10b41d50751036261035a4420a0711002011590b03552035031082c1200f03030854094a8026203016658081c0301181e8458180205a20030081400f60348950046030f9035801202c82c581c01980710300341e11090380c00400480d001c01e070701c070b10452006e2801e119403404050030f204010b03032010054800000103009010100d0f02920380580724440c1d250b8581c0041100148d0700ea10013001d510000400040040b004619207000d00e01b4171741804617165552004980c1c074034060340c2401203916521400b04600d03003e203007194000c40c1240182d4042e0742d82d41c1d00103401c64000f1140f1030189615144d80c180c41c4841104110360050044036001301c1420092801803509800100b80300402c6030020380780c0400e03610301c02091059980301c4029941c450350340c83c031180a41000e1081500942c00c25070760805145d8084142c0301a510054102030030310000007004465190402c4680003400100c3c01030600d400c0c2d04104407005980a01501c44903945004400f05406509910180130000d1040c4401c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 360218192 1250 360216942 360216949
    0xb0f0414060f0103060503030d0c08060411090d0302011506020a2a03030f03150611070e0c090105031b160b0c0721121d010e030f22030803240f 63
    0x96070030503401c0e151900303a0b9030b844006900410241d04030035407502c4041800d11482110b9000007481c100c1680c1d4800c41e42c1c8420302408280c40290000552062007401081d0217400c069a1614580340241700201c0d002d4004158100c00c9540d50b00103c0058001201d10740500c040314040b403d021070301e201c407e4110403413803901c520382c06000d00004040040440d61022528801e401101c900d803005506a96401e40c0c8900103400c0206202c1da82066000d003101c005000070b00c2c88112031088413030a1065142c208200c5c0111503a61005019142018454802e00c000404980140007000b5901e40250501001c2e030800005411000380307901c1c504903040101030000707202040f03484115005c06407031007030790120a00280d4061800d0b25070043c11501c3c1001075030b0040c1c1d8882605d280d03c1742100081007140c015104e65912881903500b004180c2c1c008020050070101e4190903441c1500b8036024003502961260b54a45095005490789020354600604800d5180302c01c080d44180c841c0b0440c2c00d030318511031543c0030 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 360219442 1250 360218192 360218231
    0x30904110a081b0c16090b031209120a0c03050a0c0f03030c0f031e0f1205101a0d020715110306030d2003040f0603060e09030403060518030703030b0f04 67
    0x1001402d10188200c0e00c40d0300f80c40d40030b072107007003060000343c0b000508825002d485070540c0e8401c420120f41090703003190360fa01380441c1c1c9010700400121068038014441040c0002601425003405c505d01c40c1340c00d083c02242c43c0b841480d015620601c06405902c2190030480450015500904014090b0b102c04000103a0011894001a580031084500c24440c60a041e120500d0010201000e00258618440040c0e480007541c94600405d844e0180f286040940d00d40072a41e007140d1b401d1307940140140130310465025030402c8044405220302c02d442e054100341c4000c141d810100d02111403c442c4140f0303220b460300e0340c05003455041c89045458154542040003075a02c0000500c00c4051101401b00301d42c0d5218008005120345010b10b0840b0780c1c0f41e41d42e102c4031400e4081d911030b40c80000d2074800040342a80180b606980240c030140d00640c04e0500b161140c1c401480e010b01400d400480150500321a50710510107088094000d403000201200c541307050200d2030000e1440310340b10364a07118081d104100d102d9003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 360220692 1250 360219442 360219451
    0x702030a03090204020409050f0603100212011404230f070c1e2105180103020403020612070e0a09020901203003041419030516020a0302060c030904110a08 68
    0x401003102c50841c00402c0003403240d40c1014141d28140030400c01c40c1c42d1000380480c040c03181641111010314455007084100e01410030380c080198145c0e401000b00d00d14840b06a40c050074003c00c0020703168400b03e05c80c841c03c603082c240b680c18100b0325810442581d0500582070b5202000342007201e50119542e55002c00c004c2c2d410300400c0740100c054048410311640c1c0c03082c7c800c020340c0c9034681002d410b44200040d001d038200200c8115410303e0341c00d4198455101b402547c0440c0d42c050300f600d081224408400c1e8002c00300404590401c50188103441c51682c1e1580340b1002401444070059030ba1100b078000414045100003555440001c0c1206e04c051070364002200c240014481c02424080780c2404840c4100c0c0e00400d0035800711280100030311040c00800316818003210324000449040d030b60113180110344000d0941c40a004900113024583c04a0303400c440b0b41c901284020b1840c0104d585030390008000c0d40010001c3c056552003c510180c19042c103100d64106510481d51450410742e4288008000080040 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 360221942 1250 360220692 360220697
    0x231e010f090609270f080309010e010509010e0c0d060e070b0c0d091a090301020c061e180d050901020f01060b041a03040b0403030b03030d09061a0123090310140a0b090702030a 77
    0x149900505c910b14024141c06540304c0c0f400c0341d8a003411840c2e80c0c0600a42108031041707519040119000b0b0174148280010408448098030045410f4030400c00c2d2000321300420341d115500c40c010200c901400340300000c068071101020a8688180e12040780c50030442d4040d00c014441009030500001e00d01d00c50001c0504002001c03150741e1503400010034064042e045c1e90701030a12848050140100115403009034486c042ca8141820303517a984940c0821a850104214464002d0742652445e2441a4002c105918041c011540491130405141d070841d880c6038003100c1c0d07a100120342800034003550740c44105100c66081c255401d41c00d02d82c80d06101e809026000506140c3e468401c1d20054a040c001d540382110011020088690103061003000380c65800045205041a6030761941c4030341c092522015402c080c42081d4201e6a0340e019828a180d1104035148e5051042b10a0112040f0791340c043c2228640500c542904a820f0030990b91040c0d4040200c4140300302c0403c020081c2d0a54000151100740181e031 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 360223192 1250 360221942 360222011
    0x11070902090d020306040609050d0203030403052208030304031706030106050303090f0307030b01080a030e060c0a02010c020112020a0921021807050702060304030203090f0103231e010f090609 84
    0x81d00044161a19110094260080c0c2c2c042009201141c0e00c01000603004074161070010480c000b04a03180c1c4401c58005000c42d609100000d030070484174070203102c10203103036400900594851030954650b400c02c48084001480011500030307652084d91003150402c0d0154002c3c002e8500301400640c8a008034070466010700d01020301020039942c02c10045004642040001403103584545074641c0360b111046054012454001a407542424032201b00c8502c50391041c0a001c80700e2207a03004441a00c01900142d040105c5462601403070000d47c801031000b440d454036581070151a102c8000c4450b0f82038009035807040c1c0300901c102e0140e21001c1079030f0b008441c00380a8081c2a40c54410135107440c01030b0b580207900002d02004000030541c000000b000707400300c22500c5200b5521404011030130707100c1940d00703440064a007001c5010044043c0040701d82000e015240c0048800002c0c1c4038241c50542603025040307110008408004200e21071003000040c14805000740000340e030325030302170b1041040c0585110501882 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 360224442 1250 360223192 360223207
    0x10c120504050c120708010b06090d06090f2003010e12040605030907030c0308031e0402060d1e0207110a0b0f040e130b01140411090d350703080711070902 68
    0x10f000f4900040c1c2d0040c44044454581d00e44a5a528054050280a5864402c50700002d29002056403c000c2c00140302800000720f5607100c102804544004030f4403c218960300300b000034a55490811200e40030380580207100c0d43c9504240c00d6400081800510707030000c0c03c4200c256030310b180840e000d0352440c1c200190380c0e4a400e4080c514200065001800700001100c011041000134001140240751080181c1d114441003180681c501e182a14004d40c0aa020004070b0107000482c1c01410010243d00305040300d0351441c4500c00140d80c401102201d51000321102607449151000168028140b100103d5003460004024007216104500034041c40451500000340801304110010750425808608a400c035651580b40d03912000700c00c245244a01c0c144070000c5800140781054920001c1c008281035103964150319507940e00758240a030201080080c1c100c00c3c003606020314984031881c1118010075950502400d0080581348003400c0b180411004128414080200283c842c05a40c24200c0041c1c0c0c6845 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 360225692 1250 360224442 360224453
    0x60f060304050d0e19060504030b091f0b01140d0605010212030c03012739020a0209060f180103020432190f0e010b060f030712060f030809010e03010c120504 69
    0x741e1703070405c8804016011011610b140d0080c06041100c0c82805032462585800341c40503280c1c5d0440d8440c040d01c1103402c08030003c22402d40c201400091060401c121009802c2c1aa805244e1294880e260303920340ba010204500d590411506c22011040d8840504605003d4400b1286200602c070740b80030040e1910b0b01181c40d0703002c00f0005002c078542ca207040044417041c2106815520242e980b2100d946240310340d480381c868001c2c1400c072440c50f441c1d0242c01515255401c0058000c0c2c06028550030001c140840e003010b44500503449503465010039039aa1640c951b1040009480e07000c0c101512480d5841c80800c00005039080d002c150280c2c04822803040d46e1080040e000c00c10705154044040f6050000f00700e9900c02d982d21414124060070024880c3e003035518140052485562220098030f1003c00000d4031061065500ca80c01e80310030360000c00c105a0f510802c060841c55508262614180041e1250711581c001d80c070045061002e130001d000310b00500102400b02c401d10080c0140c01920758002804000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 360226942 1250 360225692 360225709
    0x80a0212030a05060a08061e0a0209060c030c19080d0903020c041505130c020d050d02120a020307030b12060a0207020103060504060602071d011229040605060f060304050d0e 76
    0x2001103001945038039003502084003400f420341d00703180035610307444021a041c080072460300d1186943d604203001d5841030342205603000070300030540d10880e80c1c203020906499850b0320050400881d010010742e03c0f2031540c41e82605120030b000c2640701d4642d0607006040040e841c001580c021110444001864600c0b6040690410070f4412551354480c0c50461019104015450103070142d0300700303554000c02c0942c12050300084401e281c10500c0582e0000e004680402d2180c00205045c0c0046040507081c030210440d1004d060038150344221420750040100102a0b606204050f4060001c84007030501ca603455428688a04018041c404090380015081c0e05590003500308200401000e403080050700e640e220001c0d00e07296180510701d2261410340304100c0c02c000d10245181650710742102012001d01990301c003041000ca8010001c803030074295450307002504000c51245e2080e80502c00c0458649850002c000c3c85018007002544600010700070710000c20400200060700d2210745c10328031200c0d06030500007641003 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 360228192 1250 360226942 360226963
    0x10905121f060614130e04030903050a030e090a090201090506090a050a090603050c0105310308120405071d040803040f1509060b0109031101030f0b10020c03071401050304080a02 78
    0x1040c0200c0e446400450300d074001e808a403544d582d000010060300e181d0480a102e04508554462aa01c00a10070110b2265840d0b40062090402855417542c0e6942c06003000045e900640124640c03400e040103504000440d560b001407410801c00120b5400e0b40081c04d07444881c0150380c000d01c404182400c65880e95450880a00002010040d0003030703a0724134101c041d004500040702c0c2d40c05820031000c00740d4003441c207413280005000e50b80120076880e0703200c05020740004e84500594103850344001000c148558010a141400000703452590318280c10039601d0400c0356480038801000700d5a03071600000203a440e00b0740140e841140590b50307807224100485ea42c0e541c1c88002d45501c0002401c00003080261780f11504061080c07406000141302d59006490108803880060b2011200f50681b81556201c0d80c0410b400c1108507030000b41e0880b1550200d6030b4200000300c1d1402507440542e10207101d1908201c1d00c402445080311042d002c01d80280000e0540c0005440200504000300c2d007031341541d0081c0301d143c0e0003 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 360229442 1250 360228192 360228223
    0x70f0308180303040513051608040f0602070f320304180b0a1d0114030c0a050603100305060c0a02210f0c01180807140d080c0703020c03030c0601180b01090512 70
    0x1641c190f0b05440b4007c0006a44001c008251010b10382e1100e402586007622441d049503a040d080d00403520b803000650300c05d21003241ca0404416103c0001820308110100003c0e8a4401c0d424418000c2134204881226182d0404940e0007880b0400c001c3c44810b015012a4045002c0411444a03050101c0c807410300641200c56a0b10b8480c82601d804032500036224103e81500200d60704050b2070b1020b05032a10b6a928003d07400c02c000300d00a220318100a0000d642000300c0c0c03094106116684e8455a04150007511000c00040c0700041f0f0020499041121801348805c07400416080018080e4054091044078011100140d01142d050300b20007084d8482c1c003030302d5206104210391112030301c0e00c2200c680c07181078101c1e070b11820700c0e0000300e00b0603000030900041e4002d80c0b00d00c000703502c40000c0b5096a4124480441c05c5110340690842035031800c4c0302404c20b0300500310041200e54100524080300d1810f102c07500071028a806140e00c0580e9010015004032001030322942004e0050140e42400c0507ea010003884 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 360230692 1250 360229442 360229459
    0xb030c0415230a0303020d090f030f02010f122c03091c08040b0c06010501120506180a091a04050d020a0f02010f0e04020304050a0c060203070c0b0d020426070f03081803030405 77
    0x241071b000704400c1910344950b5607040900c1d446205070036136550345000c0a0070140d400d0f00e80078019401b9074040782d40e034606400d050081d0384001c040082501c03000c1c01da51401034400046880e0350b02504044071601c0c0500000f5605180c0000085146a1490f00e00c2c1c208251a10b40c0840c1802011402c58000e004040700c2103988010010f4000c0d610032080c8981c134001080c8041140054100784921350062000500582c156469903440d8801c01d14040d11354446107030345036503000003d61281807a002c0d00d81000700382c000d140341c83d042682c00c1042140000003076402000c45030001402000c8840010795090900d100d0380c400d500d000300c1d90b214280c4081c0742c101d48000140400c2c4040050241000da1060103940040c0e85c850f4412a03c030b000d1860000d00503d13071004180400050800500840c4019075070050401d030381c034401e030140c001d20041c40070f070207226041d10010791100c28041030001d010004400c1c0007091a6540d200c1442c892150508403c0c400b0103c0e003101a0b8040c02102d0003880003e000a0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 360231942 1250 360230692 360230699
    0x9130b0f0909060108120a050316120c021501080604031403190c02030d290f030c04091b0605070b071209050d180f05011407030509040504060b030c0415230a 69
    0x541c1d800080c01034510b1840746c841007150640a420031903101c900c0598445043d03031600c07111008080f0820080c6018842020300b0001c184440384100302021040f82d0080c040442d4104444010b02c0703042e0049402070700220b0801000c40d8010300302d12046007440e0360403039070395036252010480d006072100404103140c10f06071a0059540e0010103050000c6c0c2480c010805030220304c02540c01c6001c2850a00e18210201d91149040c1c60f16004604604401400391000c5843c0140058200c0d070310004120b903070b10181d41d1a40d00511005529002030121428068580441030b22201d2614100500d00e00c200f0100c550007110115054000240143d40042155071002d410b0001810f0780f040c90a00c9108410340750380000740c0c84403000c23a03a800c0303903810f8550110100e40004070356060750103080290180802040008030307544407441002d120714010310001800100c41020141065040c0c002140300c0d9007801090581d2b5803006883c202101e143c80ea1080000f0a01000c00d0495412074041c43e610104020000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 360233192 1250 360231942 360231961
    0x50a0311120109140432030c01020a0932030a0f030e0315011208070804081b040c080f0a0e0106050d0b01050a0e0106230d021306021209130b0f09 64
    0x140c181c6007403c02c10720801c500002d83e103030308110803a070241521910341c586a004002d0340c1214040b0008040e564503800082900703491542e8070030340100ca0181c0d4006016074050786d00840380405032040c4101490016100d44110400816803080403070001245015001f059400300f082000443e0302c0610207a0501c1d01d801d015148091a1072410300a0180030f912505400110a5540c16503180302400c546083c0c0079111001e00d80c20010303040314016410800450781345000c00200c0082599400c5080c215600d03003080c041a02e40645018091144090a0240d900100e0b40c003540d0101900e0b100140507141c50704480e000d00103a60083c1c0d000f124256200c4103101040041c941038842c02d84024100d00d648800d4244840004d00c15080080c40403007010038900b41709402c00d80c00041300c1000074101500b00002a003268440b004a80590260f2942045590703011311178180c90b120560241404d0200100108030b410100c00c1c04170003020741d90300b111000d65440c031031544582c04010300001074500e00740c2011b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 360234442 1250 360233192 360233227
    0x10e0d0308010905060a08060c0c0106030b09033006011206050a0b030402100c02030a111f080a060501050309070506031003081b070909030f0e1503100905060619050a0311 75
    0x10041618200b0f00000e000d0b0034102c2c0040d0403545908002c01c2c449c0c2c0c0300303402e00c40300f40c100000d000040c0d5203910000000c900b9600e002c80c05039001002a40e46c0d410590b0220440f45030044805406201c024107414500810290345580110203087c1b000e4091041860600140746036008968400e01c0381c14003188091008025501c00c61082e034a142850500d01c9064480141041e0020f502d0f0f4040b01d076150000da03e13400c24020803040581106000704520b1a6420a10381c03131204200020341e29020805800042c0c010100109003e082081c038504107906016240c4126000305401404000085643c1c0f5012800640c01550403902250700c0b43c0000e40985400010101c0a4425100e090b0000c5a03449051207240e003080d5254642e070300c034100852004e80354844111039441d0700c0075640852900c10280500194071032488885a803150301e00b88504101242c1c0301034070039405148284031000071004840920012901c00e41840b94032044040b03000c8016010801f80c0c80701e012000301c1c4256036000000e09 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 360235692 1250 360234442 360234449
    0x10e060f010929041e17191b03080702011e0906201006081002040b030f040807060504050f0f240c041205010b0924060d090c031a010f080309040b010e0d030801 70
    0x8000007940d0b036040440d1303000410380580b102e960040790030f800f00e0001071f441199517680304501c0055806000302c913004103c012a130007a1030841000400d0303411581d020702d100d04144140c500310210074032103200090180c00180101400c1c40300031459418015800c2c80118280710104003101d044091584502c4003030007040c030030308219209035009050315001034000d0b5016a800b10f400c43c1d003942e40f1740e146d06210840c064001d450b800010062840400c0300ca0041c1803040b8000d5005001010581407858641460f90310819040d0304018040c0301c00101c0c0d6081c45010b00008104500c25807207070120020b25114a038403900c000c0840d050504100a81034120300700c501800c540174a40d80d600c0002d0280e0410095440c00001c4480f5030b07003200b032460904003520315440503441c0080c0106c0da0340d9842494421981007910300503d00c4000c040c0700404800094090034086696413481860030411983c2d86c00340c0031000f0b110716200e141c0480164461140340344011802020178801580a08018119400a02 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 360236942 1250 360235692 360235739
    0xc040c1704052401081002131e0e01120f0f06180309030519021f1209140d110622150c080702011509020f040e040b010e060f01092904 59
    0x44600050f0f411a00d8003030494840c680504841b011b2003210b10029489600240008040c40802141c0801002c101920200400c42c040d138085052000c2c40602c03e0050b8855014040d14105c0440010010504c0c410b00503800421076484541605c1c20002806603019000d052000c038070030a5040c1076111924400b240d00500945400d600c00c1e5000d80b80c621112500607411241040d90030318504003240d1030384440071031460b2402c02c030156424128150340704110155840207005100b4044803e050180080d5a060740c140304040314581e03483d43e42c036a40014901544200c0c0e001002c0030016a00a100303882caa8400c100c1130b20f0409880c5d00c2401800443c00100000308224001094240148113009000c3d204185074a905841c0c0249900a94040f10b0080454007081c170001681d00b2a103100640520f02c030350743c242307100c0d810072402540c400c00c000c01c110b1117504100584c0d005640c1051941080e11280035801c40e000719036903001d840d502d00200140a140800240010b8028842000e40801800c0b04 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 360238192 1250 360236942 360236983
    0x405280b22050a05090c0a1101060b280e130f0507270807210503040e060321040302060d09050a0c06020c0402030411010f17070f1b050c040c170405 65
    0x34000c0c0001c00310701d80100c030340209550000c0f68400000c0c0c4050f04685689213007886400072300300c8109007582d400c2d5009030801c075401300c0c110039800001101442e00310b4800c114011180c0e86410b00924110510000d140142805110504003591982222049030042c03e020701c071038185000300070040c02041e07540b419000402084d515100312082d00780b204849125001b05100c900300342c50103012204d90301058144d1300c01d000700c66000440030300c0504001c21b07402e011403402c2c0ca09001410b040915086844034203d10601c5040c82c00082c03541039900f030300d4040e07a48580781d41032058010020b1150150140c1103201d5201c1000821001606010a8600715405d580340c88180c00244000d03070000790390042c8095030100540c5801e51140035142c1800722185800700c046180c1c0c038010660284140c0301900020340059075110b041b50481403a12800188605842168020307840d595203651264100e14800d036101e111044c900c0344642902c10400c0414008044035060900c1c203d0307170382d001944080c424100003 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 360239442 1250 360238192 360238199
    0x10507051215010c060506040e0f03030403110304150e060912010c14090a1a2703060c070f1b21050607090f060c060f0501060807140405280b22 63
    0x14440310901c01e0b00180c64002c01c0407019038a041c00307440f000380840d8019540d460564401001003003180c000d08892400b039030b640d05041c18000d0241d07501a83ca400d450380704000030003003900b1942d040d4112681614000e44d202c0c104400041a504c1000d00007a40b0017103500c0b00048082c010351011500e0701c81070300c3d030200c07501c402e24072108280181c1071035503806004040b080100c2d521120520480b0851a242c0a150a95050150007106041103015070324040c480d60011140c10100500c41d00031a41005050400d091966103581055a4490081c0b1103440f22a07030b40e030040300c002c4003107015183e27114506d8101080c00301099502415071074140c401c0c1c0302e1f41c0080350f00a40294541400d442105101000440c11b141c415180d5010719501200c601e42d0b168404004003580d403081501070700c010390f612805401d01c4180141245407104454540c1c00f0100400c01295a0b0440c110301003c40e0a4000c405c06651001903241c2c249a641c04415201b0b4005460902d10912085a06241c0f001140e595074803071303d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 360240692 1250 360239442 360239461
    0x3120f01120204090c24090b030c0f09041508011401091a090405030c0102070b041401141501020307080309071e051309110d0b1605030f060d030504080105070512 71
    0x1400c0c41855000c00ca400303818009420644c001070740d4070f80210403014038036a85001110000d42010726441c681ca5071140d011041c190304c02c0301e0b00000c00d04a2103a13411403e002c2010a080e124014042411910011300801c40d525070360001c1c540f4866500031410300d00d0741c2d907020501038842c4e11074484c060b42c08000082001c81c081d01c294500c01118151200884c88040d052110000c00500b0a03251844140300080c00140240000e040107403060f104038003d401e113868464011107410088400e09d9052010301c0500700b050300070040d80a0700501600c0454405240141d0031881400700242c040c610000c108114002c0015480049500d070b651038103c82910b110541504100c90300919034070110340d8446844007407598000602c498040c03c150054803c16038005002680508030444060000c5820000b0072410f12221140d0726116013051869031030000180b0742d07084402801184139081c00701621050611450541d0050603841008101c1400c0c003881c064401d410420846d2540c103c0000010740707009 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 360241942 1250 360240692 360240721
    0xe07030906380d0f0201080912071a01050409120f0c050109050102030105090606040b0403110a0e150907020705010c0b091509010219090503030d0b040b040204030f050c0a1a0c0106090507020312 85
    0xc0e004048081911001c5c0d004550112015044800d5072155207480000281400d004002d61441403450900006d1580602280280145d00c2188a01d25140145000c2691440700014010700707441e090080742c00d523060681d1100b80c1400060702e90743c031b4031040ba4100601540154140c3c0e17400c0310045d266546110804c0305610490180d54600a000d00007000083c00f184030a00d81034000030f010040c6c5540710040b50050040440f1609103500c00c0c1d4081d114241800d44400d90000907510192901500300000030780541c0c54402c004240101140000304110420b01c4605d02007090340c2c004850a00344840c146000c0d400c840c1c00d080422103841c2d0aa1449801203111908440014000c3e40c1030014181d0382c80018088890b42c07a030401d484101c0c0b00e81954a40c40100f018503c95091b0f80142081030a01c03901e4a0400150340d80614941b9409209240e00140703846109102140c020365618020206203003d082c2a03400854428245801d01c050030b90040090968102130782202e070035035995a44084000c2 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 360243192 1250 360241942 360241969
    0x50720070e1b120606071208040b0f10062102070317090601320301020a020a0c09060605091219031707090e06120703201201060e0703090638 62
    0x40e04000455030555040f8400307902c0304008061609100c0a83c0790301d00d6500e86400e802e000241c441003048200084c1042860f00312038200c031002e00300e141c0741c610b1014034451030145da001d10121190203010000415504100c22480780410740d240e0310149409416800a01c1100c4852011800011600c1e80001a000d0481c0c0d0340088034242c104181268000c887c060543c1036600c01d402d0121188141c0b424001440740b252640c1c01469a008182000c00c003500c00b98000782820b6040400420540d680032064600250b02112030118809020450364900408082d040440300c4d0503007101c5042c50b4000c43c2c00c6500b02e84c580591005591840000c699010150180076050240040465620f00b4050642c24110304240f0460707091356140d864003200c042d00c2403c240221110020840318070300700f03003002c911084038980080c000307241010301442040038001e040c1c00425075210020000c1c80903e03000700000c1c0383c420b4400450070403800340c5a0f804000c001c408543c0304881d100c049a5030b0030554a0401507 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 360244442 1250 360243192 360243241
    0xd06030f230606120a02040615090906050f06031e0103060203010611030a020d182706050d030e010e040605041812020a020d2907020a020306010621050720070e 70
    0x85070f841c201004003070004050f90b03103054851003070103a0058403603100c0c44c1c0103055604e05c1c0914150b414900102050b14030303080201345506005042203503440d2444e03c1203034100c0c00c8550945039a40c541d40d0398088c81503a000a00a440e07904000800e10507503500660684601e5511001c4c0f0880c801da2050b542c2c40b441c5160401030b070000c50240ca80c0c074071442d040c00c908141803048000050b03540100c0082d001d060407842140102941c0900b9801090741300d540010031090b1006040c0e15000d07280600f5040c0c40d40c00407410302001512510b42da1b0b90f00d51000d005000020003c1207942d80c0b029025001d0451150100c422101c4a600e80040c58000280c000119134014081c0004003c1561800c040d004d0350b048202900a49024843c00683c5041c40c0354400c0c00d0303507801410461440e0040601d040340c1a403118040c400111114211115440000c002c204031260000ca002e4039160011900c2c81c032450341c1e09094056080900b0b984880100f074550485128140100c12502d804000c04031030505a00790658 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 360245692 1250 360244442 360244453
    0x1103040519060b040c032406090905070309080c0a200618180f090d1b03030b0a0306060603020408070b0405010e12010603170304030f0f09050609060d06030f23 70
    0xd512100030079007070621511000c140c00c41024007240c2565031008481e00461746440c60740300c0040e02960038001e070210410780e0744506c07031074046c0c00303041c15046020303410303815444030005941c581c0260003207524154055010340d0b0311141228080c0c0c5840c00b00004884c85808000c00d414804100f03034000381818401007205142c000c0b1400e0101c510f030303007140f6400d802ca00c0c18004500f1512048499512840d041810a03105141c11245142805202103115043c170844007002c08141c650702030440050755050a000520403080c500107070300b040e042d0784010a91400c060012524592680250003203900840844000984400c24001140100e0103150b0002c0c101030060304462401c44018108040000000100c0c81e440780c030380e0305203200020b10151514400006120415030300c418a2508100149032035441111140002003d10700c4030301c079440c46030402040c8080c080d03030b4042c203c5842c07081d0755404004803503503072500b100d00c0444400145c5a020796420001c10032000e400c61241c030801c62201408 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 360246942 1250 360245692 360245713
    0x1a031204090b010c120f020f0a03090b2139090103051f0801020304031d0102070b18030a050d090b030c071b080f1c0c1a06010203070c0e01060311030405 67
    0x80203003442c0d0318104611050140045482c0e046084006400e903500c0b418046513141019140c0ba01c179180140066200f90b110f007000c280e0061401043e40e4034480c08580e82c0350a4045a420381a00c40c421460341903058051000301e10245000212090408000802c041d90500c6a10b8031071a0440440c1c1041404200f1501150b10a6000a9000b042950072a1a542808941ca43c070800560000c800982d4004103000a064000c2d11460b4200e0945010038049020540003e4986074103118284029101058202c400da4940d007800d000c0140c003a044586e803200343d0400e559641c82d81c09200e00440d15142010400c4040f20f01200d1003054815201c07450214903903600b80d50b42440342203980a030824494085000141400b83c84450903402d40180b00c1030301c42000416070034040a0b105818040c003440e400303002074403400c01044400a015042030042ea01e4100507420361182d44001402c40034240404101c0f50041c0c42c2c024180e80300744e5010000c01086800005d101d12064070098010b40c8400c8001 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 360248192 1250 360246942 360246959
    0x5120606030a0e0a1506090c120c0908250914070507080d02030a0906060611100902120d090f080a0c1203090b030c0403030206060411270307091a031204 67
    0x841d041009960001880c00200381400c0c10080d01c85012a8440a00d80f600c01c0002500d01a0300003078903000e43d0400c450b42d801c620140050100c0030090030700b2a1503080341544203002fa078a4400500002c415279400002c04100a41d240480c03180390013028110070004980c41701c0c60322403144c20054840d210203142c0c031400800e43e41070704205011913507001c080100745104034280c00a180500310324200420801c18502d440015074286400040c10018600307118202100300140c0600f0740340050800252581c0180082608029407441c046007a10405440d107102c11b5000318854101c2c0ca010380713030700106500d640c0003d13290344801d00068010f92070100d040c01818902c94a008029102c0e040030803036203680d41001107050300111182c902001c2c003c5420402c0c0354040c0605a8130210465042013018081800c00f1094041c040e01c5216104000c0c0000c44003608190800e215600b00408031403850b6a0f032002d28000d400c001e401d5402a07400712540981c0c80c10000b42c4810f601c00250b4800c3c0c106401c202c442d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 360249442 1250 360248192 360248197
    0xc15020403060e03340c14040b100207050f0d06050106020a0c140307170102162004050105090117070b07050a17030603062a0715050f090a0f02010c02040e011a0105120606 75
    0x2005000b24042c068000651100c10820050000c1031f155020b240c040000c00c0122000350418600440120780880000c6a000c11008103482084589000e03070949200869805280100000d0000307140c1000070403015000285400c00c0340c840d4030070000103a00c40380c0083c00b20b502606440d03010351001000303000c644400755064400c100e14900040c00c20448403c4034003000c030405001c2c0c0c3c1c03106002ca1004608100c8501c525a00da00c10b4905011551400e004900859414413502580364070408071401400c0052000f00c0060205a0960741c64010500f0699100c8030881c034215082750a142c12603c5202128056900c104001005004a0b6540b984091115040440301201c9200d01d40100c0e0f080c0c0c10301d0b02c0074299181c041d204401003002840c00c2d940480384090000070504c140381080102a010008189850303c0d40440e18056615041c40143e4880640c075800940c4541031004d484419901544076510f10804550010ba0411080340155124031401041d49525464074002a0242c20031900 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 360250692 1250 360249442 360249517
    0xa2a1208031b090d0c090e010e0a140115030309090c0305040b06010305150312070b0903030c0a03090213050906090607110a06091b0e010e011508160c15020403060e03 73
    0x18400d107094a42000101d1130741c400c1c1c00407950446040400d01030102c26100340001605117000812003440040340865440d040b680d0300070001c0d140b54004041c141c0c020740041007800c450041048150351246400380491718507000340110345141c420500700c0c1c14441c3c00381d54002c070740001c10800140c031610011405844002c10303022100102d0340d40080b880c0c60803c1100a210310020165440d40c2c164640b11a2002d8040e18181d900d40c020b0080c40703e00038444048038100d41180c100002c0180c483d102080c001c8807a084651413a600d031001704440321201081c1288200c01d050151031042ea1442802d507404240011120003a5104010750b00003d1003942c0903a00f07450085c900030102c0e54140c20010f04899203900014000d100d190010080200c42c0c01e143ca024042d10503e8003041c01242400070180f8000510200301546c0e940304c4144a24002c06e43c4030100c540140d4038039800b44040d078886001e517000d4402110b04c1807a10005581800000c0b0980e40d0880c0502b00e00d0981c140040c8030368949071003020 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 360251798 1106 360250692 360250741
    0x5090103111e09040c150f12020a031b090515160305090402071a150105040b0406030c17071706031f05090a2a120803 52
    0x204210707101c1c10281d40305540c40060107182c206007455005065001603208040c001070051a00380300701500e6041401c040c0360100d10004407030301c1e801c0c0140a800108220061105c581d0a50002e140c100024a0007241c10620258004090710030242410041029050100841d003001e40d40c03007496a401c55409800d02d0746d0840601030b2b580c0f15036030041c00c00000081e09040369031280c0c1901c803d190080280c4c0095481e0404a41011509a4500c1c0304d65030a18a40e8034158820000c40341514402c1c14001d007030600d4190150040c110b0702a0316002e0101d801000400c8414445c0054402c0350241d90314925844201d0034016a558050801c50090304511811402c1c84505590240d503101d0213803000036240c0d2441d00e100c2c01c0042c40040104411300031a85503511040009550f00d5010041c008400401c5da1009c8559910000b0003000b080c2c5070b010710002e40c901090580001c481e440a0 = true := by decide +kernel

theorem cover : BRFrame.Cov 360071942 360251798 := by
  have h0 := BRFrame.cov_init 360071942
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360071942 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 360071942 ≤ n) (h2 : n < 360251798) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
