-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3993
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:15:34.280839+00:00
-- url     : https://prove2.me/submissions/c0e7a940-f243-4a62-b8c9-20a68addf937

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 717985611 ≤ n < 718165467 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 717986861 1250 717985611 717985613
    0xc03040f0509090c030c04020306030f0a0f030801080f072102041415010201091a060d150e0c040e030706050a0608010606051b0309010807110a0b150f01030b061b1216 73
    0x281d850710180c0f14030300c943c11401c5000441d0f5000281011401002e58001d61240d0303d520000b03081510b07040501000b03000e624040810820841c02c00d800d440d21a88035642039903258074a45039500f140382e200700d5055111800c03d2050001001c202c1d1120402e1040c41690415254041415261030701c0229400d20380850034080300c52620700b80040403103400e10082100c20300359115602484640108000c54002a2001c02c07482d80300c2c001d02080250704441d28403002040e660b1042c000700001d440c0c80b85903001d0780d02c3da41d6880c5000e00842d110280444015030500380151110802810050407407019250f4508001075141e4084c0030b400002d26140e21400d4484005948a09100c0b241080d40d0049400c00c1101c0022a0b80020380b4541040d094580304400f03200d01e9848903d0702c1100f51010b0f244049007410403041094440302ca06001d0030594110a050030700e00300641c00d680502d4050b81c0d1101c018450510700284032540501c0310100907040350a00309200790440b40c582d0101d0440004c401041c01c1c048 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 717988111 1250 717986861 717986869
    0x30804061e1a04022b06030813080616140a030f0c09050306060a12030f02030f1216080f0c090a0506040303180e010302031b040b150a0207290f0c03040f05 68
    0x94001900c00303514004142401c03000c2030415010903c2d1028542c0760802c112178180c0d0000000d181d004956640d106040341c103002a0440300d1142c90314511501d0006655001d145181601403d156100c07000d035080380200340601500805562020144d0782e007900200700e100ea000c1c8104d001056142c050b40c0609013001d2508100005010b1030050800c0d020403c841c40c006410b284203541c051a100901d4241264100d0461040380304050a00c00080f403280d90141820700b803140a49250b141d2240345c00e41c0448203451000c001c803250590540384034002a07600c0d007103400804403248010086460350303464000103941504107810a0700061040b0200940300034020324404060541d081c8079400640c910b50001e9507030703040c00742440304110025001c98000d82ba1034220403d1080b0040040b04041d202d004010225000790303849a00510a260340001e070035021403a00d01101c0310b550380130b0031012400c1704003564035401011240e124040400c04c40082003000c0c0060b201130103c800f10302000030700c2d2500300 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 717989361 1250 717988111 717988151
    0xf09042307230d020304080715020a0801060f0f0e12010504050304080106060c050c1003022109010506060703080c03180f0105072c28030f02030d090f03030804061e 72
    0x503110407503490b10382009209451050355a40e442519000d030740c95a030b40c500b81d100e03406075030301c01000100d00c2050800c8001c5550081c0440c9038450b5100c400c56a80d428085038aa49144401d1010808150506003018403500e00c61507594400344ca0300b45816009082030307084130011601034545030804075052004070428010078004100e503191540640f591921950380300d0180041051045200003100b00c2018040d4040d03840c007003541c1450380c80035000308125941c080360031030300c101e6103504c1c100014129103403090644500907055550100142d03141c150300e51075030380050f00b030001151f041e202100d440301c07003040288241c5544900124550404010103414880c0c441840082d21421810002c0c80702e1021103440d0308840c00b140d1004043c45200f00803006000c135102c0120844410117808003e014a48072400c4030180b007507003110b012000030364040b103d03c02d4a0096548041112808201003481000d040e6000707402400c0002d45c50007980001c88010b07030b061055200b400d441d8680412145015021 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 717990611 1250 717989361 717989387
    0xf091e081e2508040e100302040c180e0c400e070504230f1201021c0507020604020d0302010e1c0f030615030c03020c07120510110f09042307 62
    0x1400b401c04240e075800344a0301035030203174980300c0e8000d41c00107440d1101565000c0045401074010003079030148007002404183d19040ba00030b1240e01c02400502804928260340c0b05510183c1d8041c14071032a40c0d03415982e4050500c00c62a410b91301c0400d88206007900e10500f52400481c03c0e2444624900752040a1592008103000c0c24000184420010b2011008000282c0d1000d01c0e1940011a04000000d003014010f41c0c40340d40061106d0380c0702e1003001055004094040ca10006680c071043c1e00f07410b031801e443c0102c41410040c0c0040001c2001410301444403000e60344640001314141c1003070210540b60a44209403050a103d84a401e5000345030402c0300c0c603a81c03450b6440d00b40245401c01e40400456003925082c0070405988800d0001c03c6442603041d680541035040940320351607030b030b91002214201054000d5a9500036014007840448192040c2d10001c040441c0303d07428610403401d00203160700250000c0350070940350700c0245131031008210300040007900c0000f250090700384401c004040d4540a0f070 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 717991861 1250 717990611 717990667
    0xa02070201020a020f03100c08060f04060f030201030c09080313050108070305101a040e010e2d0105240304060c091401020a0f0c080d0309060f091e081e 67
    0x1188801507640480c10944994040d1920748440c00c40e40c01107854600c45032020080c072407525045040d1079901c028400d00841003107600ca1803c407045010007007107440034490020501d034003410403c0154040c2e0000d641c450201c3c2042140555645c04090075075002540d81002400941c41c24011076030401d00003a0460000d01d0100290318000d0380078a00e144050280e128080b03031101d20000d070003110300c0403500a0400c5615504140d6941c50502805000580709a2501a1320440b15140c01e00c41080c9440605465150000d0b40d91811090180b102e5005124030301017030620340080300301e841410003940180c6c811240014610340789000146007a80c42e410541f092948036001c1c4060380e90000750646d80d542c0000920744074840625211000038000d5128614034020400c41c0608140c241c0e0150328000c1c0507850902c01481c2c0105448111510014001d0003c04100300da4002c20182c41514071009100b00000e6180c0f09484440c108580800034010101003000100da241004090010b030b044894480d07 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 717993111 1250 717991861 717991867
    0x212010c03051b120901021b0106050f0103090c0b03060301020702101d03010b06070b1005121005070504050d061802060f0405040e0714060703090317031e2e17060f0a02 74
    0x1101500c803604c1a02d48001c1c00c402d0400106000c440e00790304961103a04030f10074030301c1c0400f15250030718080c3c0418807032588070700d03503895051a095000307000d0b484c50319900c6402c0f0307000c141c00e00701402c460f030700b015110702c0d003541d820301481e03006881c2c10720401d0a22000c4c0e02c910414100b0210030902402d030600003540681d0400224801a850f56404d40e038040381d0003e030018041d518408862041003080d80001e50144800c10f045482c44d800ac01c1400118070030705814405030342c07210402d40b4288114400d4580004264078041b010070300c0c5600113400f04d20840300b02900f425282d000a0f0468011110800a030740d40002c08024501c1d080c4140350701543e903440601000b03860007448000034464603180c14000c50b00011660100b41c032421a03440030390b50007481c28640b03211100b07298481c4d400071150510f1000714401c2d03030007034a40c80020f420b1150340c051a400845490355003051056001d00c030400700b040c2e468a03030085901c1c0300d40a1807400c40c41003030300188154035006c1d490400c42c960107055100c00c1d901c10 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 717994361 1250 717993111 717993151
    0xf0b041e0b010507050d05041d0402010e0603180706020f10060e0a09140f03030610170a0e010605030f0a030201060509130b06010e0402030703050a0606020705030a110303070212010c0305 82
    0xc0050314828a039518400070380414aa00140c072144030788a0010042d000e5001d1012115821034090810f0714a000400507040a200c42018240d80c0d0030748001c0d01164170b5035403041c000d15103500155072046107400c41c180341e100c52003001407400e6400d1f00200003503002120040c44204080101c0381d002d0303c840b4800e12285260400030021064040c06d00081d1030b0301e03020084288032420030000d8074041d20300e08482e99542e0b41d0140726220b03003080d21490300c564844060141107130300c0b42c0400c40d041da06048403c1815160003441e58001c101900d4445503654079628001203036581442058034003140741c4e020b89803003449894003e0031070345150400c900c076404000900a41030400b0312859101948685120b07103a880c0c0f4801600e902550b400c0c020340c0580008204407446902d908440d024554000051040c161242000e030b890b1050390141c01d81640c40b4480e107202181445200d03a18211024080d80e20303121315074002c50042e600c0d08010034002c7e910b4014498003d5454451654401011001c140303400b412 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 717995611 1250 717994361 717994391
    0x60b040207062007030e0603091f060302090604060501051b190b0405061006020303070f031b0c020901051507033504050d0305011d040201030609051006110d021504140d030f0b04 78
    0x10701c00f44d8010300f008030012702e5010042010360300b400000502e00410405204014024200c1c601089001d00300a401080c0142042e0042034103841050710b03894108820341c00d9446085d42d0155080040e841881c0034515a01c1c0c0c070040320780b04c150213444601e440386801e0030854504a0702070900399801c400140100706c00c035800b0042d650849954600044001c1c00c810040b40038105002914088064004c400202d1a82040300c0701c1d4514130a81c9c50003810ba80e44c0b82040301001407000c085090b1901046018002031040180c84040c1194034810880b541c0d0820200c4520001414030f195a400e0070010301060000800c82c4001c1c0c808603150a22443d030500458a940b180b40c800100c550659042c0890f04680c0203400080103407a0b0300504210384d140c940015018140703e80300b10b5000c02c00140b20102d40440c00701e059000b04180d03800410185661900c400026a0300400a407070b041c085a0b21100306280920030b040450440e50f0300401c0204003040c0d0f03801140c0710940d02a20a80c681190321041d018 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 717996861 1250 717995611 717995627
    0x106050415031703090114100302030c01031103220c1707080a0305040e15040f0204060f03020301051c0212030d06090605090f0412032c0c0a140607060b04020706200703 74
    0x3600640f00b6440742c0b41e0000b000d000d0540840003403070301d030b1b105020040203419600305d0f03900716402181100c48030540200103404842006060300c408140400c00100036420400300624403070b000301210b031350031070b1107403280400900e03550407054403a02545199929620200603490140504101403c400c00c0b0b250380c0035040388114800c840b404200c80001403107030104445001d844420141040c03010100c81d5041400030750040c014100451141d5400040561003403080e207040e2480902050754001d501c9070043c0711010652401ca030300010750301459132144402c2c0090080e1112a520210b541401c0050042c00e0310034540080340121064000c00c41e840c80c2c0380809541150300080b0f510000c000c05801100504030003401080041031000e080189900c5140700310034a12041c405071408880071a04101c0c002c40284140324000d403082152070024a4400002c21849200c1c200000341180000c0115085e600803520955900c2c1d5039060151000e00080011003042010b02c2d046464224183e50140c4498 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 717998111 1250 717996861 717996893
    0x609160b1201030b040c051c1b14040902042018010c120c0c050a06051806070f06052802030a0605040b101103090a151e0903110d021002010605041503 66
    0x501d24081001d005506840d1b4024220180c0464495091894100044c0f129501c04680b5120b10040c1070351300060420301c2ca0b00361034030102400c0b107500306841040042c3c41c43d40401d0b07034072550b0340da090b00c842c044002d030354500b0758000c1e01c505450f8035403641510510009201c105052040039180140041e0003110352195004003400c008500406508124000d91942c2c0c00007070b04038000e0b0780003040c0c568020303000d0300c4c2c132500c69a14441c2c034041e0001442414081e00b0001081c002c00c904040000840903048207521041002003078040e41c42c2c0e0b203170310205440002c507a984095800814080c070001366001e440c0c040d103810b41d41404144510008210748151032510720081203466200f52601d60800e1041b2002d105001b0050141e40703440d000d50301020b003036a44000c00403d5040b0310300003034480c40790f54035040e10754940c940c1c40010b03246846200441c1100e401d12644180b501d404c410050750b400b05e410780c1d00300b1300d54000070301641401c0501c001c4400c9041030144904c1080300130400200c140004032009 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 717999361 1250 717998111 717998123
    0xb0301060507050a140115090e060414030c0a1a15130908070b0a0209031e03040b0c01090c090e10091e021909090209070302030f0a110c0609160b120103 67
    0x203030b40b141803440c10311140607402052420103800c60700035004150006504407512680d1038074040c1d0f4400038503080311020380b92001c4541001c400500421507507107202c1c0c10305079404141c0749081030240f500381c106542c01c4811a034140e044d6660000001445441c01d51102099440e1442c070007200c000207440d245820440112641c84040880c200007010090b280030b95030002480516082c00e003e81400b079013180514074001d1040c40d520303100110b400f400d04a401a003810181d8035250809940900c80d034850b800b01111036490b01e5030240010700d0001d041c4010701d04500d002407000c0c1032001c4c4c0d90070143c5e09412038501505212041c4041290341041b8244050543c1ca070003000821480810240303400e0660744820044105000192001650440c800a500c2280c050485a4980c0b4055080340410799602c108030720740720700150b0341c08440da0000812020300e41e04203040c83e0034020356516002c8101c3c1c0c241c2268100031507542c1d68003107144150018000700c6d40c0c46800d2800140401e8070310b01c4140b1001e004 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 718000611 1250 717999361 717999367
    0xc07090c020102070f0f06050603030319050601090321200304120204141501080a02030915060111070b0405040606050a022a120105090f0607020a0803040203030f120a060504060b03010605 82
    0x18001d6044421640d03004006403422817060038026440700d0800001e98095040a002a0b0b49250200840e4401d009090548036840344001e000001080c1c000c00c1541802068440840403940c0382000ba03442d9002c001c252510450003500081180c0080c969581c01b0310384174940e19202650101c10303202602d980c070403043d2000d84a0f0000402038142c1321008048a4119004e101c041141446405100413081c0c0f00d1200c0c0341c6400400504910084402c204540c000ca1f000b000d542809540036600605c05140c0240c1d150380501c800c90500c0c48692220b01510310000e010046410b01d40a508010411424500e0401000200c003170340f00e482d5050141150741d4085200c03e20642800c0c00804151b4000c0c280e141038509403800a0700915059440a10600c00c1103d02042d081d00060320310b200d03003040d0303010300704550455440400c103410150040b80d140c0000e000e91040b54a00c0c1000e800b20f1440095000c89030b0030101c0ca210106e4401d900200d000e181040d0003031012060060489044903200c0c40c066503 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 718001861 1250 718000611 718000631
    0x5011a01032706110723070308070233120f0c040e1003062d110f0a0c060c08070809060f162102090f09100510020a06140f0c0c0709 58
    0x8020282c4440380954182c0c0496844280800d000410100b403000400b2140c0000c044080a687c3c1e852601c402029403078100030050050412040c146080070144000c1440404400c4c154004450300c40c0c0780e02d0001c0e6000c220003c20020700f9a1040c0c00030f62070341200050307081440407094548a113014107442b00000c60081681000c00020410007990090f00c20400d03070408164076800c0001d08802030590040e2000c0c1c05684e144a4880d41401f000c603944064641402000b42d410903407c0000c00c00280700c802c0e840315000ca0a603001f0101020100d60700c09a147c0317041d0202404910000c0c00b440541d0b403000080000c2102c4a00b16180c0007140341e45280c040600880e0308a44992030b8150170b90fa142c07060450152b03000342640181049002c11591422207407101c80030b000d4180402c03506110842180c1c0010845814080003040d490006481a076000c00c03001e403141d4061740c102d1002d00360a83c20140800c8001120410045c0d00082407881d4249041e440e0031826580f808c95000d9126540d80c4c5d0b9070070790 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 718003111 1250 718001861 718001873
    0x5090f06101b061d0610090c140c06040204060b0a0c110f0414090d03020c0c13021204030f030b04020405090f0c0d06140307050108040203060703051b0705011a010327 73
    0x501510740ca0703102c0164024041c07420001400584200c2262181c00c80300522825502140070352007004605080c5481078940300c1000e000c3c20440d00310406101d1000c4101656180130001010070084420040c039990800b84113000454000c0d911408952806111004c03c07241c1c45860111005d8000390320020f4000b007400007404881005081079805071400a00410304408100110f21a1074200140c9101004c00340042d01030f441600054403940d00400b000d031000c1e241c03d0006c214810000d01006003001135000c84d14070541ea0a54080d0b021442100c09080c0c160b034540502540c24034151815401e2528000101d240150060b03d540507031440440007806032028441030702c4d01c541d0301000c00d116040e40c4248a50200c000c1c4450280a0b01944102040550082059074052980138004048a0741c4d8404210010080a00041c270302180000381700f840002110007810100303009000005004d40300c05541c5071109000c40060b070506007059010218010780030480520700018140665210007603181c01 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 718004361 1250 718003111 718003127
    0x1b0901031d0d0314090a060f110a1d060f04030305090103270312050f010b07030e060406120b0f0f01050904060503010c052a032a010908031005090f0610 67
    0x1240720504002203020410005a40c02140c4580e202084044c108420f001d981d0b0303a040344c03c0d0081754001c07060500020420752220b104001581d900180100e14100d1604242d80300210300400103410581b0200a614103603a10701c1420f504654040ca0701c20301c4480350324140036600c40501406400700d9502e0310f6074040c0d0000c81c45c4500304110b98800810f00000c815410103409010b40001310150b0781361202d01a10721506014200500301c030662a031170040c41c0c809550003d2002c03010844c4050b5030003a682c0f40c107000350001e485580c41d8001e40140e0750182c0d4049a191034000c0c0c0c4a0781c05a680c90015807140003c800d80b40c5428601a5910380030403012501901e00c42d48405e415601c1c00445105496108001d4003508500c04104008030000505a8400c2c03241c01e40c0ca180a41c000b08006001030103500c000800c4500841a0074404080c2e024a090865410b40c0c81510201c8001003042050b0241d00740842c064001203c090f115402d121064400070a40107200600601004000116030750080d000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 718005611 1250 718004361 718004381
    0x6121a0a090e011d070e06130e010c1d1503070e0904050c01030c09032406180506120109030e0910081b040c03090b042006040308120c031b090103 64
    0x10500e041035035441204010241505200499483c1c10ba0703100c0c0c1011204e406400c82c240440080c9055801e043c60511800d1028100643c000402003500e00a41c100340100041d1a40b04000040c0c034185a0030b02038104d5030143d44010b080741c00042100d4003981c0349024140d02842c8004400e03240e41d103400f42607503c00042250241d00400010401c000c1140001c0e200001002c01c0e079090108400c881e00c2642c41c0031031408004c20745007420784130209001340a1100440d0002420b00411416503443e5052001c0c00c00551280b500d41c3c070303901080000e00340380300010081c00440008210f14502ca0710300400300140740b0403003407240c208880401c0e000310300462064064020b1360706031248914031103803000c0000c3d201d628803805513040902001c6051300a1180480b060b4008441402590b22a91a4000043c0c01c0341c0507081d03000031803400e400301e440c0d01010700099441120b98554a00d064415042c24100092201010010030010001300e0a03522030050420b441c050092601d41d25076000503005403142e0a0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 718006861 1250 718005611 718005619
    0x50a0507031421041205070c0611150103060c020610141c0c150e090c0d05060d060e07050102060c03100b0d140403030204150201110318014206121a 65
    0x452410058800405401117214800301c404070746000d8420b807100d000f607110180000f0403071401008150700441504035002c0b0058182c81034401034041c400c10200c801c0c0c0003078072041e40c0c600300e0700c21445d010880d850700400300e1652802150710700101003038120032240026000303c85011b18503050400030140442541e621a0007060455140c945402c5880014110400083d034201c2c6081c03450b0034800c902d14000c4040f103a440385000100c210b40c3d40075020141400b50844000340c41c00c2c01089a9103e00d00013a401c40c0083c000440c80c08000925062004d0080f0700181da0400a10007482c0541c0c0154046a01c00c1d0000c82c0c40d490380000480c010041e000d9a4011040500200010154560f0040080c1d070006804800900ca030200d08070b00701c90540d12091a01e000c00c001080b4601c0c030381c00c048544215400c00200d2803580160310b40748900c2009040710039407206240b4415055208080450083c0340c0c0c840c01c0b80040389010030061211841603c94524583c0e1003200881244000c2d00007a00004094 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 718008111 1250 718006861 718006897
    0x1903111b101b261509100f210506010b1c02090901030b040212030c070501030c0e130f110409090308010618060309210e040b060909010312020f0d0c12050a05070314 72
    0x1000311104c2111010a40307124681d2a0000b40240d480c850783c1400355900d40349040f201b1070600700840001b1001d07a800301400ba00c13a1404100107a410001e10b80032300186040030340c903441d280c2d02c00c82807019109101c600e00c600500925805407907070060141180c4d084007107051603840e01c1c00410a20441081d600d07400b0300002602c90300300d0a0004d40e04003112001c0c1e03010008035801d0301040361646080b04400741e20540500f58a1204112504484007840b46d41d4800580f04110310700e40321040d40b140c4e126002c1651560040c405054010f10030a00409032800d20022594610a250014075081e005520078140d40369031881c2444a06960300901002102c1caa004c0c06450380c03400f902c207200819035584070341d00307000d50711165007441e10964a000c00301400c00f0700c1da079085507641154499541c9072034085106800500003081d0f400c0180314481c2005460708000340800d4184145c90039181c0344c050080c45010004044556440422641c01640516103088a030f0011060707603486209244e403410318000c82d0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 718009361 1250 718008111 718008121
    0x110a020d020d0c050d030e1009050a02090a061203080702032b0f020408121c0c1d0a0b03060f12100c0e0f03031903111b101b26 56
    0x1446148020081d02207500c40c6107802e504440241d09100000d0090308030383c50f02c0b111503000c0c2d0040e00b4180c40f01025036100304055490401200c9210000390b4180c0c0c8200c0f5400b00b541400241d0035081386a520003400001c1c20030350410080710b0500c5004007048850070000d505075200b4401c0d154038070340c0d0103c8205404014040081d501c010744040c080380508e0002603c08800741403007124116038489001c1c000c20360350702412280b03d41002c5608080051000c8014901c0c0d1610300c00d003c680421034580d00159079111907190000c81034000c481d402010701c440240074045400059951180382100c05c0561300310761074007141d40540c00340000e00c440d108140d8501a4000250005c034a1290a40c0d5074440d00318602c8100001030403103c180c0790b00b540040146002d00e807103400d8221407111480c1804642620400c0c11070040380d00c0003c1310701d03c802c0c900102101d400c10501441d0714007008a441072028100e020840450200b203da070150910484811510a903110401c1d0b694005008107602c201902e00703 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 718010611 1250 718009361 718009363
    0x204030804080606120c0f0a150f02120909010311030a150b1206100302240a020709050105030a0b01091d060c0405010e0d0f0314040b0c0c0301060f0506030c0904110a02 74
    0xc80e010b9000c8074059080001c0d11810001c0140141500b4203008045108002c02804150040848200e400c05064a00401c091000610324045000e003a43c488140c2d0b941924001c0c1040c8850401d0441044100404400e07982e41003500c905698201584551800440001034641300c080140200f40c00035601174040b20079001e0b80440700c04041500c1c80540c809074003000c0d5072501c3d8200d0b242c10659100d21001e00150800200d2242e40103100369002c513898085607106003c5400540e408001640480f20a018280b541d024440c0140016001800700401582d9000b50240d0140101c0e200c0c20381e01c0b17000c4120b001c030459213000011185e10542d041c505191800c041194800c0c010580481c0c8000091211030800c0904044426002518040003100c65074084852601410558055400c01d000109030b501c84070004000c5449440020b0180740c8d001c070185400c0da10507501c95800b00144500801180d1150b200b01c80d40160032004155480400b400050014114080e007514080f002282100586030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 718011861 1250 718010611 718010617
    0x20705060907090608010b0303070807050f1f14072304050a0b030a2a0f0e090f090111180d080f1909141f0917010f0e0109020f0d140102040308 63
    0xa44410512004d41c455100c6800c0c1c4a085160700e800d64010412900480c1200000c0c0001398800c6080da4800320313028015914000d80c484003020000e4840300307440e090301c0c4035101748100010320441e400d809142c0b60f4000780955000000c1c3c1981c050712400e0b0401c10b03008000850703014100042518010548811500e40a50401ca808040c81441c0910f94401842e80c0c2d000c4101100c1d0310140060481d5130000c08440e548040d80d00705040c031070314513043d0007243d658260075446001050091691481e0000100303082d03401621050951401c01c200384170880e2544d484491400350140c0d800d01540c0b00300d1404000510551001b98040000442c0d4000d6642c0d0491a280b2120401c0c3d072602810303600c681c1c00f03495074580c020302654401c03010840001154200b03094044d03e41c03030600b0160119070303a40000c1030845c05600c5a05d9000e9540f4480250071180911032160040e09040003040f071310183c1c0c3d011441da0580d1004152042062804000800400c0c402c01d0b00080d43c400020741d1160b03528038040b01d171a0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 718013111 1250 718011861 718011869
    0x8061906050405040609020c0705060d1e02030f071404050103020f1204052b09030f140a080a09060512040305091302362d06280801080718020705060907 67
    0x21704240001030646014003c3c0ea80181d6404040c2000310b14003c1045400e07031004042e520403070380f518481c00c001c0c1c10860420b41460411a0003590300d2500301030305000000010040000c0c05821019881c5179100c80301a202554020300b0010313610801d961001c54540910b84400d2001902c030b10401042180104440c02044001e00340e8488000a08800884150198110380e0005480017010000b26020300698903d00c0d019015241c00780800b500094209514044151003482001401c52240c0d40d01010950081c250351800500f01041044180e180700c01c0a08043c0c108030011810b1141d950b1900c01846151622100440d034482110701521211040329200d0642031048501224a020114120380c0544400800c000260782811038804071004198095a03500c0f2680b18032400251600d200501848101c02c41031081e07103400c0c40700c01409000a4034544d0400010784010801114001088020740300954244088070703042c414030340d0007030080c1c26000d4217900c61b031010b1001980d0041032500540b = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 718014361 1250 718013111 718013119
    0x18030b011508010b180f01141815071502030a06050604171209220b0402040806041502070b01090c050f1c0b150a270806090105070f08060108061906050405 68
    0x1076a604c55070980b0f540610603000008500c225410000d902d015890407592480504084001c0404000d40204503008a0300c80c0b04800542d80c110200e5150121843d0140207400040700e2406000f940c80c000c03146614850103241507000710129519041e290080380241202920345912640ea035441000d0b14590803031181071074041c41c0b0700000c5000c4110210b41005001810140c184000c41034000e248040102c60440700955910844086a40d00d000170700091106500805403401c160501c4580f61a031400c05c0c0000c944108111000030340004c006504651180d4400641100c404009407140c0c458401244402840010300c0704051814510140050220882c10030041d800e410034410010000e424155051074180103030866284a0b03048410501d0300c0e400e880225418001e840f00c01904560000e600d140c00900401032201400d10449602284a1030498000d8032103100c09400e00c400507111a042008900004101e5100c0c82000600589030210400c0d20507a40e0740002d00755006401540c0c86 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 718015611 1250 718014361 718014377
    0x11031c0e030706080711120406090f0803161704091404110306010e161e0819020702100c06091505090706020703080307260901140115020d18030b0115 66
    0x1241000549030b0107454941c0c80d0001c0a880f202e50585e4690000c000c0d4036a548100351540100c0a05140508018411900c0d10001c003401d041d0301060010580e0008445503100b07009142020100e651039a0405400c11020f1a0b446d26034981450a07202d1600100340f03250a00707010004440c103d101d5144180d01410a0140203241c410806880f2a001c1c825860b100d9030040100300704c5c40340181c200380000c0d000d0504000c4082c803040d1980b000011860100040341002d070400a801d010480018068100403008501d091410390008005a240492355410001c071560060304022a03135101c2c0002d02d4020b03403c041c84c400010303c9040a0001116005140c0c007800d040080c0752400040c0440503070b5401030b140da04542d2000300440713002e4070503078603c0e4884080b02c00d08000041c218003054040c08111001045002d401d0440c1c086581c4180d000200741c0f840d80d41c00c5603425501050b20403580d40f80d440e000384424140103000812224640001d8038160014000094425940505540e801e07a1070b21017080d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 718016861 1250 718015611 718015637
    0x3110d0c060f0513020103020c0c091303140f0415142a1513110a0305010e0c1c020907091502010b1c05060c0703140f030414030301061b11031c 63
    0x42d50030030348104c41440032010704500150b0080c0c01130540c0710a030a040750500007030707003000130f800e11740544840c1d9070111201c0940701850340c440c8000d00c1449803082d01c949002102c1b44130482d503109510a5050700221104003201c040e20500c290094055614980764803854200075101c0c055112a010220310030b00428000484440456082001c030360000c06840d075507440c1c4500d4001c580038443c040301c000201d10003000c50340c0d954914070000795000380c00010b440090042e10728502030351003102900c0fa40c48400500100c2c54200c000c20540c0b941504e40f100aa01d076100151903009054000000e030943d04146021344540c154400c0b448100304803002ca0900c99105600200e4220015014125410101c0000c074100364004c02030081500c2460020070082002442c1802600103002c0300351341c4030b400001c1c00b040c460039103901c04e20140640007451642d41b44c80406460400d50034088801d10b0000d405500038844c0c1c4406a15804130b01805480c044071803401c00c01e9048a007101100301151003100401 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 718018111 1250 718016861 718016891
    0x303020a051c1e0b13050a0209120d032703030e0c030d0c03080109020702031903021212010e1e07110f01050705041d06090c030a090614090d1d060703110d0c06 70
    0x10004e604003414442d09415040079000203010003c0c40c658100d40c0030407001440b9241c5051440b03000ea4007001a0842604610004050302e0801c0c0031002d02c11070211400d0844010b01c00902d1000394181400120b47c4149400c550a0030250165154180140d0840207521030304101507007007291080e501c3c0c2d44035a8840710300c40100d003d00e90b406509030780810880300b8031480300400159410301a004841c801d1059201c00e940c15404250305200d99142000100050084540d416400008150010450407070740d405601031401c1c0101030904000d01190500d030080c1090011144460302c0d540203003e94a07207020090480e500038811180e1300b5444041c0c00c60200c00d0741e800940101300007460100f00380c850f03048181b01c540024000302d030300070f0351010b00e90005910303441840c00e04003050341800124600301000d5810504c440102d14148400456680064404006d0000b0b048200b19200b98480e032103420200c5858000b2416105544503030b4100c40201a00600e0328543c03181f080d041031180c081214112 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 718019361 1250 718018111 718018121
    0x20307020106083d090f0213090b0619050a0803040f05060f0f0306060c01090f021c0f530c0c04270312050105040501120303020a051c1e 60
    0x2648201000300c0005403003590382001011805555440d0b103c8014941da0040c21071304002c100310348044d5411030f0801142094009288406070304030082110128035210f020250380c00400c0f49109075004065218101200f071001c00191001618400b003041d2a040800c0c1d413907000d40584b0346010207090f80040c69242500c00c44149030b542410340e9048c010103980500071a000500155440342082c480112000800d10845540030b0042441b0f2190111600620205110280000200200c41c1c04000c0c081009104840c0659501092070964525101120711036407107500c0140c0e81d000b290a104441a0f040742c24051510001800001480456890b00c81c00d2403181840c400074542014561107818a484e40c082d0160003a1840c000280c144d40c011000000301c0c03001011004610b078980c3c2105444210b00ca0706000d0181940c0030445541020820808660f054400034105038000884000c01445807043d214900740110b41740740c3e8010030031140c0018203d42e55540c200c540944155013a100994014 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 718020611 1250 718019361 718019383
    0x9050306160c030e06041a0d0507110d0e1309050604050705030d080c090a09052805010503190305040e010b040801050a110301050d060b0613181a0d11031002030702010608 75
    0x601201d07140140d03001d4420500030308803071758800d005000c0007500d83e01c54040d40254462805401c0d6030703800710100041c11140301400715070130003180000c064682c4500140600030340c811810001401343c0c181000501c0f004141030500c0040e401d040e5400c04002c40051150701451250f41924405c075120030600d980c0700f18000040c4005401b05010035100d4008070024801c840010703011010482d11a0b4204050751015680c400300c01d01e00202024840100c0721ba105502540608140241d51600000079511340161084070701d8022114909801c00d409001104c1c0103102044401300690307507440003c20f03160010311904c5c020f9402c00c000220780c1c0710184540c0e862180c130a405582181d003420705101d500040d644044036041d40e19800c1040d9a541e0300084c0c11522030000d0240c40e25800d1002d101d100c0a0481d01000409047c00205800d000030f00b80b41e03082d60602a0b6103c2c0c0105250300341210382c8a02c0322000e94060050008107406182a90010743c428406c3d60020b21600356581c1c8620354600714021 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 718021861 1250 718020611 718020617
    0x181503060d020f031509031305031c0302030720010501030b060306160509060c060a0506010905031b010804020f0603090c100f1407060e0f0a060b06160b1b0a0905030616 74
    0x74810014030300400c0c0e010051102404481841c00040103801101005507200700c0d8540c00030824603102130b180d6617204090041540904600311a108102e2000074000044905054000c40040d1215202d041c40c2526000c100c5d0b115103c00d1613205c043d5000348002c0c0015109a0b035100300140d080c0c1400600c950060ba112000c941a048901004031015007041812580c0300b4000c004004140300c0400885002d00201e6000040500304600003506003040d551200303029410541c40c1400410081c005071a09150a0038840d645580342c2c0700048049601b031444950000e004010f00803c8100050780b800e400c1020f0b140549c016041038815100c408040507a0b0000880160f04001039045000145c050a8803412010440203078906089041070003801d009800c0c0d500660305030091050f24002d11031780d22010b8410515049042c459801c05400001c80079001e580100701168059000c1280503040d0301d0b4640000342c55103820080200002c030395110700380c424441d000100310001501c50403052040b080f62 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 718023111 1250 718021861 718021879
    0x90807030e011806030b030f010504030503011401050403061109130203100b070c030c030503030901200307110c041e14070c02012d03052403100f090818150306 70
    0x150301100c541c084a000c8a042007114410900c400d0642c903011005071900d6103000c034650f442e1609040c5829562000881260b0400c000d00c00403d41080c105c1e03055680303030751004d000500b0310340c0144c03202d106980c0000c001c0c03468844540c2142c040000900701c4120100d42070104200d00c02c4500c41a03000665901501100c0c040c0100b00610212000b082103a20540700000c2a0740d41e921101d00304a0030364020f0350359030000030030000d81540a01c69400003143e0f403e040c3da079081900014150f2800f00401c148140210303181036501050302003080c090007c1c0010014404e0240c41c03059890302c0040904c81d20036180c2040711682003c602c024205100703030040c3d034940701194410340046a802c2500d504061080000c544000c0c0040c0703000c02046013408003a1400f18040c188903c4110001403905508888020701039206491992b0101d1180c240c020781410208614104810484c024504810300034440040080c1c500c0401042805040368842c0c21210781d09101d202c0e80c24032041d0b100c01c461540e4440c0d802 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 718024361 1250 718023111 718023113
    0xa0f060c020d0507030507170118030503041a0a0e0c010804080d020306061b0a120e0d08030c0409021b0d0c0c180204150e150403050a0b13020604030312050a090807 72
    0x5403481400660000340b12115540b800e495450800c4800c0c0c006a4094010b28014030041d070403040701d0522400c0005c02004019081005111012040540141086000804a400c2c01400050120f40900c0c6190184281c10090f00c03040080091042c0310f0201e004107404000250700a01c81c25102c4c64000f188140b41160040c0400c0081d4001000a07074008400c1c44050b0b440240c01c1100c240c0468824002c5c016400300d41400310500200c00354800400c0100c0c0303080354198403180468120154401c6200b41c03241c80741d60a8201310b01a0340c1155015600c0402c0c8400450b18000724440728140000549000710050002140d016120003030140900070281e03800c210003c10441040c8101e881340d07400604007500c074120b0501c0c01c1000500440000c2500f01c50403190318082483e0303c020b111900002e8a441d185903600d0fa01c0c1d003035549000d411000303180c1c0042e00d80c400380c00c01400c1482e1b00030b001c1031f034484c0c413840c015200d201c0002c0c8602c43d451806c400035a541610744242c0b20569005014207081c4081 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 718025611 1250 718024361 718024367
    0x1020f03011511060f0604050c0f0901030911121e120a0e01020102040f090b040c0516022407080c070e01030c0b0a090f08070305011803080403080c120c040608060a0f06 74
    0x342d4035070a080000301c1d403020241140c1800458010f110700c01403c01c85040440c1088183d54014011703145510040021001035144441102d2a091003820b01080400441c14000c1800003001089500102030445225151401080280b2505801e219100140d940300030801c1e40e80d8200140d02801e80001c220b03210200b8000ca604030606841403001520f029140e0401c1d01080c5c080d1303880800f40c00c0c0c40704020800303841c1a000c1d16800f42003a140050030814408201d02514001d80400303030103a109112078140261840a03140c43c1d10702c0c1b100da40c5550740c0c09c0d07240107070b1a41c0c0900c01d012618064030340040341482c000340d550740c100c2e13810640420b05941000e11440259208114680901c510030000081240468aa0100600010000d03011451441c28400c0c00d44041c000147e03400c0810340c068100090f0406030481d0050b4052411000580e61003000c0d680a01c5905081c03c0c402114004001180280c1340040060701c01654170b01ca0716850b00400e02c40001e10600515240700036012081c00300a00c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 718026861 1250 718025611 718025639
    0x8150f04021818010c05030601030c02010504081602040609020c030c070f030206120703140412120204180507050408030c03030403110628020d020d0615110309040b010c05010f05040c0801020f0301 86
    0x81550a0f80b20560310004140e803c44080d40c525802007032010080005660f09841681d052601c540003d014500d040d9541c1a0346210301500e030420b8440f011003500c1036454540c4018054811100115900e01016400c907580743c00416501195100e009c1b00410980b00e4400c0c89412079501401c1380741820b1143c83c80e1840c183e801000c040400d95119440306101c0d00701407082c0c1c081d50017043c1205200490140003030031101e44146620545004000802c6041c2d0101d404102d85684460700003080e4540340c4040341e8504c0740b0b6105074003511021404607010100400150b003c2c034070940301c400041c0890b12002d83c13a000c3c1119100280354458424400404207c8902c180c028018503005107407412809448080303030001d801c004070245c0d89034004e20512801c0d01404d8031a0b509411b10240c1c0000c030300c6031140d9a1182c1c01120340110b45403280d8003a00c1c0d000e10440d43c1050361250003402124120a04c201c0100021a002e0310000f180080001e9001018400caa40300010a011549140c3c01d28454400201d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 718028111 1250 718026861 718026871
    0xa06090b07032d030614090103112409030d1103221a12060103090c09091a040f20010c0314040801050108030a02062202100905030708150f040218 64
    0x10000300070510360241c40650032012070441034410f88191004403030040071241950001881c41c95242003042440d9244480360741160343c80303242d0410042030000801e49a485c0b1940110b868640030b099409454644409409880301c15812140d444030314070000c40f060408491301c5031442d0001c1290b45c418403038070808071101c820100d0020103045d44d100410001506c0785081c03061030000215040d03400410360700c0b1842e00708030240b03000d01543c00751b6100c056a1400c0e5115503e401313690382d14410200030302d072040381c0307004071000351000140d19185c102a410546a09812680303c00e007141042c4403800b00c0b51010400d050181c3d1400307c80d0446070f4003903d4412820900c020710303000c103200003d0034220074040c55020380701c40e03009140c43d10880100a45042c101400100320388440d010140108084d00219503181ca4048860014590044d10309803101d11848e0000368050142c4079000c9084400003941502c600e07801d5035102901d80d100c4801c4000c0d1041520025480f0700c183c07600040c45007641c01a95002 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 718029361 1250 718028111 718028117
    0xc0603190b090108030d0b03010c051b190f050c0405010f0506070515131205030c19050712110d05120a090510090b010e0630030906070605150a06090b0703 68
    0x141d074a40c00100301e00c0c0c1c2640035001c585c3c400a0380c24035a118031701a90150000a50090000c020682800351040c0268440101140b00404c0c4541803401c040020740c0c0340d116158003c00340d1004c14104146038418810040c0c3c2c07144035540612809092610a25048461a50b880b0160509201c10003c0c0c03584820401e503094495070356041e80740141641c08038020444500007006c101d01d1850402c04600c0d0340600c990900000748100250b04c0103003000c4031000d08140390541400f016132182641d05019041028200d000640400c0305250341003001f010907419030700201d4481c45802c550484544c454658044000c2000e140400d40915540c2c0001001d140302d8404da410300d907441c00501c800c81f070f84514181c80c1c4412950040028507614039406420000607140307a0074480d00b6541d003159001411410a0075135003a849a070001d050284103072aa08400103120644e034100d43e0403e0f4000c0c107015102c1003103065000c0c854065924203000c115003140c0254a554800c44d1500e500c1e4441d6400802d41a0300f8 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 718030611 1250 718029361 718029371
    0x7050901120f02040801060b0a2a05060711010e0c0f1219060c140a0203030f040804260c030c030d12090209010b030a05071b08131a0406110c060319 65
    0x780ea00c00740290600c01140e20401a280ca280284503800d5400e503601103590034030100400d240550740300384005807001085150a00e51812a1816280d034000c16801504034000c0d4401d00c81d080390711140900c00810b848000b032100300d844e0703045aa00c4d0000d40400540c09482641050101e0515619402d0a8186401174450040303001c01640d9441039803440407120507603518214680c103504070103202c80400c1c01d010790301e0520300c0c40a0082d54a220150030141444988400141007101150480d0b01820400340041d0480b82e04010fa03228070400c840c01c8035494054006800141e0400050015072a6001801410911213000d401d450040d004007151091035115860b800240c0c84090000f8001c100144c4a81d5a07482c11964800450754094403803002c1003038940f00380d2240406451002c0d03419822180c4107642c0e41c0d02d42034112605a481d030100902c002c180340c0d20034803466104050012103240740c45441044e41004c070b555031134151603c1e13119031111007400070440010091841c0c0000c80005140000c1c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 718031861 1250 718030611 718030637
    0x31b0f0918180c0317031e0402040e0f0c010e0603040308010b0f0403120908011d03042d0f061101050106050a0c06022205040e0a1109100f0305030a110c0907050901 72
    0x100704140082030f98840404201001042000f9811424440200c83c21606504040c4841d0b00001030090414100707184050104040d569036500c43d0402c020b400003182c44030001210690385404d401400346020403405101050141400c1044a00c9164582d480490581c00c1070202e04072508001020a05003006000c040b002540340707044180d040b200c54580c46c8400e440d050604d82518213215060800c191007102c030000c035000c008207071429690701c4012200010710315550700354a0102d003c2d5909114a4660740080c0c00d040690154041d078001d82c1c0c40c40c8064190103070213401d0311420310801001900800031810707202d1081041e1900a40f00b01005480c1c01003400001060031900303100382518507018801009140f91a10440c248a030b2104081c00c841111500c4615400c503441207080c2c003c0501100007422181030442c29000340080a000c030100d41c0c0c82c0d0800c0c59490300005510b402103190300015000e82800000c2110103e440100600659a1a0305040b10207400141c0381906200010a10b05 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 718033111 1250 718031861 718031891
    0xa032004030807061116021e0402160c1502032b050f0610020a081207050705030408031801080105100e040608032b20090f10031b0f0918 60
    0x100085000302d100c1511485182000760895180000352100500c00b008400340b0190b15880c1d210301d290701103841d20f003505440d1390b5448000c41c815900991042c0300154006200c0362800c0d113610b603d809101988151a02c9128059042e001e140c80c100260740107110340c00404c2e940d110715a05061010040c003110001303e01e289026104140c4008e031a0603421410400c190809289070200c403821403000b80540921a21228050b00c04c0451844005010400203030040d4024001c0b5220107600c481103941e6660780780d2019449404c0214000c01040140108c1000d5600c5500c0c0396043c1d4000038154944544050800d80d0300610019040740c010740c9500b00045d0030f01013800a030034580403000504d107402840a904284205400c188401800e01d4024081154055204540c3d014000044603969403620342e00000d00400c80003505030f620204802291030703086c2d4941c02018000e030f070009014036109071014044da84040001c420000040700142c080044007210a0b24903420134884000090305d5205e00454 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 718034361 1250 718033111 718033117
    0xb03150f04020306060907050d02030c301003080405010302160203100c0801090e0d080403030906061409130201050d020d090b070c0c17070924181802060a0320 70
    0x4080d4104100400c0d81000e010803944010b00b140c1046480c54a0707040506940500c0e42c61035404c071380c04000100c0340020141164155440007803490048007040e2104800340310304a4400024000810200e0010700e4250001815603030300000d01d13400c041c200001103009401c040c5520302958203600641025890a010387c1e148038045e1840803664003000d4402500742641a4400069146421414407468a010454082020351481e00c40b039a516641400c1700079000c03010b00600381d40d14100000a107040000c6054044420940b030305401b954070504084404600d90a0190210b00c0400912461000c564000c09070181104030010702400c850b20340701070b240c00c101c0f584808984101060403d000b4070000d104020005042c4051640203000300305a128901480303400c40d8640c6500401e840d01e80700c0070103100052020100005420b9071840107005a650080041c0c079000e02d0508001e98254103501c85c9880c00c1d4003c1c20961400d1103081c001c034000e0108011201488051490710a041e107071403402 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 718035611 1250 718034361 718034371
    0xc070303172527050a05030c0a090914060c090a0501020a020102060f2205010f05160e06072406050f06070803060927010b1e09190609020408010f0c210b0315 69
    0xc024080f50a10f41404042061500114801e90080c4030740082543e40b2008030f4152101150041510304091902038910500001510058001e50080040042201024281e5800100c0300110700c1c550b10801680c640c2d111003000b0340183c01800c0015400312500040c60340000d41704440c1200c240ca04c00030003050461030341c1304423520f0751503078144000c03507000303000d0b19030010030300d4a140030b21094080b070207840e0721a003624941c002c84000c19200700748100c0700c580c0206803114241050310100040c081000800702d40c041c95108034420040503600782070900a03605c005130710330300310352550b1a00c5042002200d0020002400095040000160410409058200c0b100c513500046001d01421b410071003c4010b5a00801d5126061201184960b40b40c0007030680040640398a010300403406106030014024513040000c08034000107000407104030545c003c8a08012400b02001843e0707660900319071826010340c0c96000b43c400580c0d18051411036503c8400341140c01001c458020071130385c030012041781c0d080750 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 718036861 1250 718035611 718035677
    0x807110c0a030302030c0c220c032325210603060c0815100801051e030105090c0a080c030a080d060312030b090f0c031305120c0703031725 61
    0x586c20040d00c2c040001480001044078009105401c83c100c086860240c06140c007213080e103e451580e1061302a41c07282070034544480d80c80312074201050416000400c25201d903000380d00c0d42c5041c012207020459000016000907500e40c0304038408030704810000410390b0031161046544d0000000001c0062052115101080d00e521070f51385032003403100100c0a2120b10150080c0d00030200c10902c698810b14003819208200c4010a1000c8460305601001514181d102d42561802080c044103010019804019400451300c28011342e4032580813540781c00790209510f0b010742c080c41402d00000c0c0d252014201d498000500016900c1d5651107004812001008450100f6500c0d022003c46040410300c1d603a00c501030480040d00741c00c0c860559400792000a05c0340c50300f4842546110b0800100384451040840360301d01d016242d105122400d1345a20652004401142e6160307000d201e03510717152001d00d00ca10401e071040b9180002d2110b441e541104424118401c100d07040640b607048602078003140d031400e042e00e1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 718038111 1250 718036861 718036867
    0x90f0606020609031801051b0703030e0f010c0c05090414120918060f04050a06030c09020306101d13060504050a09110a03021309020d0b1918030807110c0a03030203 72
    0x14019041c4100502810420b130801c015161040032140b640712400b00c002c2c82c040ba0381c0d000052074030701802509681c9400038090b01c1000410b1507444400411400b1040711000c072100d92000c0103440164046200404802200d0741c10003c1d45000b40032143d106008801c82e1403002d0810700807034180701d1171002c40c2c48202030224503203800b81014150641564064481d040d000e062910001d02e0906140c10810f124603102c0e80010694406504103000039540214042c1c600d0b03032103481c0040603410444146018446c81c4d17202d40c0a503442081030b030340e1042c040040151042d41c1901480030300520320402c1c2214949401c0d000507103445d43c0c031841e07106811043c400108421189041048210038490892281c4001074052015948141480800c800304100005801c119440803407403a1a01da0380142c5405084000c110031214542100004901428001c01c0303130b4442d4283d4030b007003404000c078040c0000764500000780040d40078030740124080e9001021943e138a450900002c20303000c179030b400490040e0004 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 718039361 1250 718038111 718038119
    0x20325050108040305030a0b0102030c0d171302060415200313080d021002250305030f010909030507020d170f0a110106031a100e13050f010c0f110304090f06 69
    0x4112280080d01091800d80c0040c01d140d14014410700010385085015a17035030810080b5a8000c2084800c0c060301142999500700d10440040c0c03072411580c41c0540c00c0d400304000a500311010205800c1c19980c001d0848d810701d8100310341c00b10705543d030a04090138810f141002105204490068031600c1400030001e40da41d00010181529000d0641e1002940d40d015030458500c03d03030089900b0180e80301d150001a2a2400b0048011201c04042c1002c480031140d24600ca003856072040c01180f0900e02c0e201c50030b142d0303680d6060001c125a0fa18a001d0005007084c0403c00052401c103501d10f12190040b44124940000b10142450907445441d800c0d030f003030314002800034840b6045064008030201c500004c1200d24030f140c40d00341e1540c60022194108407031820014030b003055800c140c08040c0c803400c440b80b011071030042c2c0c1001c0390303010003e81074450380304ea41c0c80340e0b50501e41401508800b041d159100f00440000610a47c0c103040042c0c02554a40801d100210305441d043c0710321440c0070081000441c07050303d4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 718040611 1250 718039361 718039423
    0x6050405010e060108210d0c05031e0103110108041a0c21010b0714100516140a0e0405100b120411090c1804091b080705240702010c0203 60
    0x5000c10510190b080382004024245c8007159a11500b000e510002040000f210b0038071400e842120070000e1024900081c01d4403550b44603014501c2900b40042035000e1280443c00251096000d110040546c01491801c0880354440c605441c0c201d840390314601e2208034070048440c071a44088032040c10303101c00811407902240344003000d01e0302404202e0b0034050715410403000f50340e03520903004003810840c21404085c102a004003c19a021126000c0810146c00d040c0c6007005140c05003c42c01000908000c18030b10040c1132001100c07503035071242d1220541c0c4403c6000780405040b0080c00100e400a4444000824019120040c596542c00031403512052070145040380056000d417501d50300980c2014104503503541030740125883d5803005c9000310748d04d004c0200054054000040e00904000142c0c08154003c3c0096085070161070f072a100755069251036206000e04600d6030104c9000142000c803a9110701d81c02d89008160250041c0b40c009048041600880d103032901003c9460ba40040c60000c03c14417541c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 718041861 1250 718040611 718040621
    0x7031e0216020405090a0f080301030606090b09062b0308060319080a0305040501111620030a02041806050f0a05010e0c1801020709050a02090a17150a0b0301090605040501 75
    0x12a860046092040d245094807101c101d00000074000d07030fa80ca01249600d13008006520005502000e220204680e62402c0d112a070002c0c4403c0b00c0a40c02c100c404a490080e0b802241da4611025241c040f8503580c0804100c00c4002d1829200c10b00481c03600185604c5001400c1c203403d981c02521884081d05022050501d84000e00540c07404407082413403000000340d82c100489111081500d40130075591680e08001e40101f1030028980d07912070001400d140ba1003c4180b0810305c4d64021403001c003003009503a907007451041002d4601641768001c1d07030f54500180b50035801034008082041d481407101c2150340d146011100d0a5540921406080e000c004445000d0b0244a0150600c02c40d045140c0c21f20030010461400341440c426005413800c40361a040d80d200b0003801c030040901c044c043c0907070705052008034020750022081c0c1d4083d1001174008030704075001d422000c1d00c404040c0018910f807000f421030b01003141000740001d604261150101c8070107550034098443c0309802140b0001d217038286440c1140c2140c0e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 718043111 1250 718041861 718041911
    0x4030c15061a031b0706060e0a0c110604110d03030b331323031b0103060609050907030b01020a050a0503030a1404020d0b0603030904090f030206060102070326120703 73
    0x710301041003201301c402540300000c450804007803440d03c2d0012071901c24007a04541d00007100c128010410029025080e4000b0f00110001d502d4614032070b10325000c030325100c5a007290050500c204e0b010b880e240c50704114000000c11406442c002591440c0e002c00100072188140e40201500a82604404404440c2d40545501500f120b1520b00d00b1941c200581003134055441404640c028503100410500c110480441c034000000b4280c4010344142c04039411001d80103d949400240ba00c3c0011881030701600d503043c150b41c0000c101a04603540c005085004d013014121641c1140504504100018030400205c0380d0144144040d54a92501100800c1161100c00e50100e038412001c0a000245e1503501d00d600c181030b007127485000c0c070395143c41c0400e15520981000940040c6003000c03080c00d001942540c0818507100740c2c240c8034152143d0004990394440d90002400003040d0445c0c0b10503124050400d62040007113450710b90300b061003c600302c1050f164126450300220742c8800380201c00c084007108a424003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 718044361 1250 718043111 718043159
    0xa050d02060f07080115050c03070f0c05040b060f1803160918120e0a0b070b0604060b0a1d010210111b0d020c010804080409052e031a04030c1506 64
    0x14503010f0b00051a5000600c244003603005041c0b18008030910841c21100c48555050882c2d59a80040c039001c0403900012801b0781c0d11031500c00c00403a4138030f0140100c2da981003000b40141d06052035030400361000e5004c040901c1d0309440804000c2103684080c001304000c80500c5401d4070b485890f0000820036110300d02c110003000d1100008a500091003003501500c803264070f103000c4211440e030101007009503040350002d10b103442010914500b001587c1502d83d20a0500380c07428030844d640c8051540d100d00803d00c6590124280c008410406415003e6600001c801441200d1324060b040020400301d070309220a045802c00005010f0a0040e80340b0600b0b84000c1641004241c204d0311100700a44600284400070304106003a00843c06100b054801d64019048008040105040c0341950340800346014042110b240ca40009420014075490745010403a0b0300048003625420407501c140b090130a000300f085040c041f2001410340855140d09040d1403a241c007203c0010343c581048400004100800c0600c104 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 718045611 1250 718044361 718044391
    0x1060b07030f03051303080403171302041103040c03080f040b0a03090618051f020f0a0c0201090906082e0f2003010807260d0905270106050306030f0a050d0206 70
    0x5d010701d02c0042008158143c540900151124070b07089421440c841200c042990040f01440f0780c1c030413003c2803641c0d40c91003183d0800088445403458120780c001110060009e4044030401c0012480345001082d201003042c014030f01d01a00c40c8a2104035420400c0c0c402c001990f20443c2d001040020b01c10041500f5111070b500ea122178417a902d0036a514007403085003841c07002107501005c5070402d80d01600c041040e003601c09600c0b2a2060001030410305000c0342a400264030010004d41443c003441100c055842e100301500780e40c0445480c11148078620091003a150380c2a90490031500c590b8840c05040410150000c40c0c1c8080b00c3e288201300500c5200001d4501800b080104402c0c4000101241150485144021280d03461503034821f0004c0302c4202000b05004504d00e1040540c1e00850741000c2ea80215011000c0d00b5014440c8080004002c0440444501c6040140041d9000c1c4025660154000702268544403403981c50b1400d00300100c1e42119541e200b4620044043e805111240c0e1009698904140d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 718046861 1250 718045611 718045621
    0x30b0306071b0c08010c03051f090506060702122a0109090b06120c0a08100b090405060a0f030309080d020604020a0b03060d080c0a030e031603031b0501060b07030f0305 74
    0x40ca480014019409112403000034180102d500030141d508a9081140f181005035600321003400ba1092480c9000004d1810000602944d414100d2035081c010f0300000308102c2d070601e0b071040010700c00a01890380c80201071100c0b00050307841c900c0f041041c041030300c05080101c2014510303100000014860341c581140d84000554640d0780f101410003118030b20500841d41c1884403000c101c2d94414100d0310095900d0020402c0701600c904002400024100e640d1a01030b83e4681012001000c1c0c41d0142c0c0e40c1c1d1440130010b04a061805070003058100c540248011011ba5030740c1240c9014182551085002c034201c06010412030105101081d1500c1c2503001402007031405500040403440f523400703900444140403004c224be40c1c40b140342d48425a58880c2e91143c0e034440100350603595150b03c034411000600f2500c007000e4503003400314050300c2c00c0005a5400c10f4280c2140e40035100b08801400000395501042c000300c0c0800c03403d000726002884c40c0ca08990362044030f41401404102038410603400c0c5424082482 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 718048111 1250 718046861 718046863
    0x2031b0f070b04060507110409020402031f21060f060f080a020114030c12071b031106131709060705030706020a080c0313030e18010b04090f27020a1208030115030b03 73
    0x41c00c1e00b07511441f10b030100d10700d80001074003c062512001e50420300c08070030810304021b80c05601d40b00c14000c7c180e1101c6955108074a0711604045403410000c7c0141d0807002c03002070a20b800102c141a111000419584e03200c5500034071a00c2c16601c076010076800361008005550b00000e0f8050801c43c4005001d02e146081c0a00c1b02e12403081ea85a540245c0500300040c81c43d501c250802c10400c00c20000c131525002607420f0080560f03031503800c55507079405528040341203e071003948100507070341d8003001522440301d404123419800c6c0c100b2051281c104008008a40002d5020f20040076800c1c480c00300180c83d401c2501c002005480000c08843d002c401c20024085201004910040700350b40c18a0135804101200010480e402c150501c0610a0724455001080040081000e401030791800c160030001030340e00306918407e80300d19105100400315920400482c1c00040b641c4e0912080c000303000000590343d80c51444110544a0000b41c6038035001000502440d0100c40e0803808401aa19081c030071226104006 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 718049361 1250 718048111 718048117
    0x2210c040311190b13050102010509062409090607020d0504210c0509070e03010506101e090e1014010c020102030a110f010c0201050a061a03130302031b0f070b040605 73
    0x50b140c0b4807250600e40d000ea6a46581020f800200360701c1807100c5070780e9002c2d00c5440d0442c5041034115180820301250f02d51051081901c1192701c00014104c130f4442414008c1800d045000c180001d41d540f9913801e0b030701c4d00e0310030310b0380c2c06140344200420442c504400f0003410314400c4030013081000002c21040000c1008881142c00301c0f99040c0c840c1401501c64900180400040d0748800c0e0012554801c01c100d00b5003140491400c08410380090005940381000c105601f400245510302280c03a60040b032964070410611000d204885003061411a601c0d180021100d080455001a02e40f020308000e00c0b540ca07411641d80c2c2d00d50001e003031071051084542d0010b500ea025000e440070400011071641140c180d01001411074984040c0020801102c06c500001d02900c811164180841c4c2405c41c00a0322480810518200d00c0c00300c1407003400d54030b5180101d49104032113034094086210500941000c02e020700681d000c0c0784007240041a41c2c004c0400001d08001c16039104600c5500142310420141d0f800c4800c03 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 718050611 1250 718049361 718049363
    0x30304020d03030c0903020d110907030e07060819061203090605120a1a280b030424061a07030f020c0303090d080d0218090c0403050d0507030c02100302210c0403 71
    0x4c60120b40c200c02c01c40780c82810317600280d4401c00c0000071200707000ca08000804840c500380c034022116070366a41c054042d520082200300c1d09500100c03041141d00c0c450581d6079003000181d8a0030b1041d80d52090024140c2e9041d07003003204039034004082e28041503000f030440c1d8010a0a410500c0c01c001c0f0754082c6e0703800d80030003c01d518585626440c0b0b03d01c44080316140d109811400501007a00e84166400e101091403003502011103d502042002c1086d208400907240308a510141ca00120b60001c0c201ca400907900c0b81d0300c4112039403078100c042460b500b840c00c003501c054910640c141d1540e00034100101039280b131032401010b40d00400d090180a031000301c02c481c2d820906070b4421900b0125407610703104034464040e18444180c07001c0350180074042060501d5007900705c212001001c9480b002521a15842948001030081c0c1c0241120303007015000b400500b260b81c6c06800d000a1021054001c5551034142201c03441c0040e500040e039030024841ea461b000d600070442006840c251070607103540016031143d400 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 718051861 1250 718050611 718050617
    0x11040e1e1b0c0d020d0906030b0906220c0e040f020a0c0221010617010c0f1715100e030f07121403090a031505010501080c0304150b151902030304020d03 67
    0x2420000c14441541141d50940030340e8221401030f4001c2200a454008280014000400840000490030b00c04d00500d04c03203241c02091043d90361540010400d17a448044120a02e81441c440c0a005c10240ba01c62045240da098584c0d560500c80941000102c522144120b42d0403441807228410303850f48102d80800003541a900444c180712040e400306980c8940c038201008075802e104011602941d000303110520202248002d010b5840520015103580220000c244005104034109043c8112032941c2250005440152007103101c4140b800705030354550f08440702d404601d011401c2c4010b402c1c108070b2220307010916030162420700d050524545904d100540c000c0c00108880243e058103003010320407540110343c020419a26542e0700e00e48003541c280c0310100ca04105191000003d101d501681c01d00c0d202d2447c26000900d55a60750365825040c007040001c40c038101e5601c40348040f15032280c2940000c1c104491207a03940b80c1c40182c442c01d5100c145c5c180c9210442d00240140001620740e10008141c0aa25003 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 718053111 1250 718051861 718051891
    0x608012105010f06030f05210a0f2102120a061203050309031909090f0501060905190b1c0506031b2b0c0311030606061b0a0611040e1e 59
    0x2003040c82c09030112000c40c3c00010301c0e00c0000800c00c00320040c010a004c1c0309009a400001d0f40000011400d075071070b58610410f03003040000248091042858000e405c9203802d0002050038125040b107100642c0340d2107403c80c0d507070004180d5070904090240c02e0740414007030401e001c89820404407184011142500809114002c00882c40c01081441039034140b20345601d41010110785c1e010010074550f411b1094050b03162601c21100c0c0520120302501d41030b40c0c115180c44581c545800d0510040c0d4401141070804000150008900045903800038420030290306080142600704201002c21244080c051900c26440410b05000700380350001c6003141004215010301900d0180c45540c1400d100a00b1400ea0b108150300c0d000c400c115207040074000f524011108110607224810505998480641c0d5240c1d00040c203218103450400c0c1403110001c851403a0056940ae51104d99542c000c0c0e42085040000c40b220102d003d00c1400071010800364000744e240364002d08600300072840c0742c9480b40500440d50400d598 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 718054361 1250 718053111 718053113
    0xa0c02060909070f110a0b130f06110901090522090507080d05070606050f031c14070f030f0f08040204021b16050306010f0b040b090a0b0d02030402030706080121 71
    0x310094a4400d01c0140801100c0c2c0b510002c02014028011070320004240401c0d191001e80d000040e005c417040758812501c000d5504d890748031000c6407842443c11035460608101d151b0019415019032050700001c1c00d8959101c508020024001801c1c68221b02d000303041d08650005141c14120b03440c1e8009105440c0006d20305002d00707160b4141502600020254402c800300b030412150301c03a004041e040d00550341081695265010041072040b1040b13010380c181e01c2040703840341e0f100d5283c3c00d040d0b44070b00d141410503039a4400d985c001903940040c0020f8881e0150301c3e618100f0705800221900400035585040c1c3e02028000202070a41000680040c3c000d80c0d003c01e000085c4030f00c01603480050a4540d0485148500440f00d0200d44403180c0503450007409005d000195401e40300001c401135800856109080c141450040b01c40b580002d84000c1c1c0c001e01d2548001413142c406e00c01042140d02c0e04801580d20701c6c05005040c6002480c4c0d0000c9c2c20062101c00403c003001024030381c9182e154801c2e291030b40c14042 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 718055611 1250 718054361 718054369
    0x20306010306031202060a1802030a0b0903090a031110030b2110060b070203010b0a05010507150b120f070b09010f0819021305090a020c031209150a0b040b0f01050a0c02 74
    0x80b54100800020b200e5203110340d1581c000810700d1040141035018070400d4001c40c0c040e8402d1807541e030700a405621401c403060010740f2100085510400c02d004903410403003081d001407454030150348281c403a680024000001801c000c80e42000803090340c2014400c5480b604040703a46100c100c001c925401c0421802803c020900b03020814080c0d034003810a1001d251a25110515075001d414100d00c25803070181c0010680c10420510f004540058503418201000c603220680058070154501140e07903580c00392203942340e645458050111a201c00106903056a2541051410b040c90304101008082405118041c2c0e030702c5018408400b44514003005551105102c40c9102848894000da0080c0049050050b42c54080d078580103c54003245e4408036600d603000740301d08901c075000d120811a0001c101e004028000349114607086403000d42100c041001d8240362045006c420313100801281d40fa10203401e000e1405000d1590030038812035001407905a0000082c0c03817071240091007018406042c20135429503036 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 718056861 1250 718055611 718055621
    0x81c020102040b0301241e1b02030303010e07120515010f02011d01230f060f011209030306170d023d060e0106050717030a110a021606210203060103 65
    0x80b03601a5984c40c0e507101c0441294422580e5601031003282c204140410791031003880ca88203403140410040ca24056600d81c11a192000007070150600e80ca91800500140c81c10002507009000000d90684181400302005103e00303144c05103146403d05203400d101d407106c41c0840c148001d52090074451a80480c40100b40c1c05028501d01d03a480385001034040d084c000c0010b410404415103002e881603030a0320301d40744518401800b40c41181e09961070340700254250500c4071149005e4041410305c0c034007501005406034141c880010007140029140c20040006010300703400d00301b541c06058090006403d6001c0025641c0d81c0d10f04da80c1d016000e41000141d042210700108801d04071800010b1030784200031107c61800380c0b41c280b281c0c44e180c0c02e4070000050440d10460640c1d0b29580c1c010040c44042c541142c0e245550342001d000390118503560100031002180b110000e00b9110090340140c890202007041941c01d45215902040510641c0002e01c400c0da01d20b800c0d140c0c80301c10f1101c0c0043c1c40c3d1311140c0040700204 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 718058111 1250 718056861 718056869
    0x180301090f02090c1201030f0507030b010f08060604050403080402010822050a150b03100c0306050a03050d02060f09030406080c040f170c030c1309170a0f030e010501081c02010204 79
    0x946046804820300480444445955000303850f8a00c603a241c100022070700e44580400b40c00c0904c610801800082c619407864140c190091045035619900e07a121489062403c0e48140b4209684070410001d030041803042c6648403100f220100664901524003400e02000148001c3c100101d034000a080ba443c200c403200803217490a042c03040d40c0149442d115944400041050b40c4061241d2041c04002445014032169010b019014041010300300c005d10b8061b00b0203542010a054460801050640b40d51143d04019030165004020b0221840c4002c0e080c41405050024184045820005d0350000001101d040300c070345180c15040b43d51103061004e1580241c2d0401c0c06205150b04000404040d1a00d070b8503003042c4030744103448000c2c1e50032042594444411600c1070300311110801d41c4c81c2014080e408541c142c1d00503090582c0700c844060005a150340b045805401150490452149040d8144100f180583c105402041b9550504404a58650444e200c0c116a08040d40d52985414800e40555000b0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 718059361 1250 718058111 718058113
    0x3020309070b04061d090702070b130b03070903021e0a050607030302090904030f1413210f060c020d031104050906060c0f010902011103121b093d0806061803 69
    0x403130b01d0380c80c01403810b007041c4800045003020416265691400c035041501541c0260004d02946140c01d1300109030360800018450410014580010094036410065114441d55582d151030b140c110b00c10400721885841e030180352554608031074002a12a11350101c25601c0c1154000c1d22003000d442d044000e441a0292540c0000100c400e1100701504160b82c0c50142c400c54a4240072920b0f007403e900c0722801180070f007084964162000304910303000c8400c1e01c540401840c4140962034a191150407824080700300407511641c0c3d4412802071154180300c0b181d4504690301c1c00340104880c0941e4185240128082e9610448500c40810192f50324041200c042e203803448c0607a03180140350042e20b0300a050160b01030b80802e400365142c0100001c044101d40340845803c0060801e6200c000d00214040031000704500c0d15176003000724804039926004076044540e800d13541c14284069070030117030079082103521406082a04100c142c2c0a0103800100c0343d5030000c004e503040c58450780010003030407980901c040d1403601 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 718060611 1250 718059361 718059367
    0x2301030e01180f1419030f030e0604050d020f03040f03020f190b0403050c2205150301150503010b01050403030203030112080d06080606012a150f111902160603020309070b 75
    0x403c001e652145240c28026140840e45220303400c41c8030784031104104c00500c9480030b510a400000d00038524101141c1c07a13481d00142c0c088612483c0340c542507050b03c043d281c1d68042100c800d0a65070410002d4850a8140080c1d8141880c04510f00c03140002800000c1c0f04003110414004a84c40318440c0c41c401c0c4584140b40a20140e03141164211079210380026117090050324601d2125040c850f14052125151032111017207113401354603a8000b0403001d0312641e80804090000101503909024201a0203400c11409110034901003c25084907170054070181031007018041000481d40200a5a0441d848908813060503042407a05002c20321501d181c3c00c580b2440c00001107210384000440d0b52041c1c0083e02c503c8801104c4101108000c803482114030452030980910b8400114400c03041000100d04503000f007103141300a03805005894401c00b54080d08040418501821910728004140c0000d10340080c1400d540044d12641c0e9030200c5020b400e09141d00000448c44020703040054000501c103000c09551 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 718061861 1250 718060611 718060613
    0x3070620030a0512060d0b061014031e09061017011104150f030e1b12010c030c080124031109090405210f160804230a2301030e0118 58
    0x441904141c0c2002850700c4e000c00080e0040c10700c3d4924120180d044501d6952680d0380d40704010006c005220501d040000c0100e00010700292074010354015041c50116000034081c1c158009072580000306001c00d00c0e0f200790140603c61104140c1c001c242c03410505451000d12207460001d02516502140300c02417200040c0008031004800e1000503c80c141c0d82e600075004a03951006c50584400341140d0455400100e151051040c02d00310100c18108081d106001088440c1e030110300b1150303840c6208003c0b0303484410540038103500000c2c42d8094980b0314840c00c1d03913484140c0e5218842d148a40c000d814950f4078003042d80680210025101d0001c1d005240000e01d2416103486501e0b064074007648600c54080700c01001c60711319689d0940e007103c2e260413181c5003000305032035611210071620003054504400400c00410100e00d5060340380c0754181c1404015948805450501c4000c84030360f40111062810404038200702c031542041e00142500c24680891130380382404215004106420361203088a82d032800c804 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 718063111 1250 718061861 718061867
    0x1906020604060f1e0b13020316080702060c0702040c0c0609060f0515090a02071e081e210402130e06091203070503040602160215070c050a0503070620030a 68
    0x7885a8414141403040f41000400901035440080150384011031922200e02180c03040da2180e040094010000101c00c000091a40e0407031340b05072012240400824400041c198000c1000c5070000c403140300a03c100d2400c90320014042c050720400030b208548441d010341c405403180f81c41080594020303804202440e202d00d0030300d005046500030502001e081c030000455001e41c0495411030003201815a18260755100d035234074000d6120140031102440c6214044000c0d0241c410300c045c2c01407080c58015682c0d40800c00c0c80740119908186403141e0002084182001220030700e11038425400d515110800d521a07100040030200042221340c0c41c2450700720a00ba2007440090312a000340417a074241c90f0900345003405070410384001c40300e0310045441080030800054070b9500810611100c080000c07005465540000c14003200881c1a9900c0007021514006018105401500500e0103d6016801c640f400010903112002407081e1414007180c446540210f9505051801d0440640020b50303555212004c400707 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 718064361 1250 718063111 718063123
    0x602091309030305010e240301240303120b060901030b040b120c0a0f060e090403021014060103150e0112020103090c0308040608160c06180203120910020102070b04060b190602 77
    0x42d0b0010b420403000242c0b0740c04184900b8041d040030104031103a8402c0c5c4003460081d8101d0401d1580640d80e8006203400304e41400307003042903102e8000801007003d01d03501340201a6031185051423259441c164840e2441d50f9180200d80301a0400e0801082c4901a00c1c0040c0040580c4c0c094250003030048400e007010b250020030074030340c082011601c100f01191a54a420410b01c90741c0079030400304106142003d51840c004c0f456507845442441142c41c4041c001c0c440e03070151846012200407040365003050200561f0140a02880c4841004030170005619140060b04d803981b06224031003092110040500569101c0d80000c00c009030042c601000e25541c0780341c0800745502c2031054600013200345000c1851240035444c10b121000c4240e54030301a58100c2c1d101c19004000009542e81501142d401010040e103041c0081c0c48290401c0c440d141d00c400c03401051007044a0031040000840e44100320107000a900c04031604d401ca504202e0000d401090324020602889081a40b08039049036a0f00000c2d5003a40003c40e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 718065611 1250 718064361 718064363
    0x70209220804170c090112140d08070f03090f020f06071a04110306131e120903050f0a0807140c090a0f0c140d0c05090a14090f06010503130602091309 66
    0x482104500c110f0700e10b519042480d020550100701180100300340034902050074600c3d4041e81d5014144560304418601c1c0c030001e10749810104075808100310103550440301d441c032640710074182440000c0c9150b5405019000200009100d0401010103004503142c090035114040e074041d000040c040320032a42c462011030b084404036603010900100202d2030a0204440e40a1807005c04080c550210560741e401000e001c1c40901800801c0c120303610300200f1100d04a800c80100710b85c03036020140d811400c04500301110400604280d43c0600d2118001400e036900301c8400c2c03a00254240401c0041a4003241042c82604005034802041018420f401c5031076400068901000502040000f81e000c8083d07402e69421401c0250030758091080e004d5020258220183d81c0540e864414500f0716a6800034650401c541c01c82c2484454000d01c0742c0c0e407400c2030003070f0a07080b880034008420b440c502080001c229110090600059018041f00b550800c650b940607903030b40041c0280004907015010508100400c00040 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 718066861 1250 718065611 718065629
    0x9050a0209030a0b0a020d090b060a060906050a0302030a0e0708250510050306130e0a050709060b07080c01090501050109023c0c070e0c1207020102090105070209220804 74
    0x4110522240d10841d20720369800340240040c50780940350b421524000034103490400b9000c2203812807038070b2a48074041c42548114000c49060a002d0184000d5440542080d020301400c0401401003039080002e86820103102c1ca000340e541d42d10501c80d58040e25000148214a115080004c2800e180102d521509100d01520303130700e41da510502ea84130702840036201e01c50700300c800a062078510318441c000031540501d000c1c2081444500001c4e803d42200c01030b51109407260403c59404c01001b00611021005200e201c1c8240003440c10280520f44034480d64000610b0075000180001001e103080d0041e030a0303241c20100801084d0303903c40b01d010180d4840001803101710000c0c10018500d03030301030025004c1d0400200040709000c8045040030a980d00080c255100c0d441605000035116000c03401c1540301d41308804056031600d4050600901001c0060b10301c5042d0b90050142d602280d0340036080e00e8807960101c0d202d040e540c480580221030032a1500c0032116509440c0468018030106100610403140d040d0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 718068111 1250 718066861 718066871
    0xc0c200f0406061121030103030305061206040302060108010c080412080712050c09040b0108070c0809030c0a0902131502100c0318060605011d01081314160303090b070b0414100f02030109 82
    0x801524241111000c05c0c180342c6010700c011700c0420311940c052984407501400c0300d414200c1c80003003540f5240007100c045005900220040c00003410a02030300300e507080c80b402d10f1032040c2020394401120903d444480c904100c4c42d6400964102d125903643c0e1440c400109007081142085002c01b101741d8007003080380703010b1401d1680e00c01c01540f0a0482510501166440c450722403000c0c2d503440349941c0401c0c1d245030715110308280142107594036050b0b1390040840c40d1005aa0b194485034008105242c1c0e44858100c0740c400c00d43ca12015008181c90036540591100003c0c0b07011286400d07002854515071b01404114240c0e1500200300003a8403d0f41601c20980352141e11341100d00c50100010f00c242011400101c000c80802c0154541c00502001c05209201d125590034024001c00c1c9801d80e07114124100c4214880d080040c507400081c80700c098a09891094588540c54071200d07007281c03001d0002090040c5041d13050b6002003007840700703003074240d2215428440101d0403d00032010303410a0160b600f0042c45d00c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 718069361 1250 718068111 718068133
    0xa05090a0b0904062004030b0f04031202040b0403061404021003091a150102100c0f0c0503040506070b10080a0210050a110601060c050c04090201020d0c06021c060305010c0c200f04060611 82
    0x43c030541d02142e030301c078600b01c202799151300300c8a15460b00a8021002d00600d4001203100400c42d002507c00b1f40461806951981c2c0703907007040d900340c40c1188100c04001c00c0450600026031a40c0040105108560902023004605440e00001d400811080f24103000c07520740030720000d51450790000303860340b070700f40d0031110351a0400c04200c0444141400e9100450402c107403041c0414000c6041c04601e90041041d80d04040e555130118106500c4a00c08981c00e00c80001045280718a4640c000c0291401c200103140d00441640821000d0803030072405020700102260400307145d8170440c403031024410b0280c1504c27459650750380c2c080d100f0a10702034212910300070345507004000d0401c0cac401c44200302d8059004045884400d01d00380c0f0045880300c02900c0c019001c00001807a850110031f846002e00b40040f000401c0d600d182080b500711188403800030100708155200740c01048150034401e49910b406e10854035810907150008000310841c880075a013041c01c00c2d0000030b41e1038000100041c0d422806007034a00c00d000f1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 718070611 1250 718069361 718069421
    0x60f030103121d0d0c0f0e190b2b0614151504090e070f0605130e100e1515071e08030103031d03010905100c0c020a05090a0b090406 58
    0x14042082084030001d03c0c60f0900c2d440e0201d104440c241c05909080b0019446031602001d0320b6030b54120401d0390351284c091001c840241101d5100d054108481006004240170010310803c5010034040300e000b6407241000401100f2040f10300c806a4094003c10082103002c038004445001121550f484280c104920030a0b41000c68807506090900c000b403510301414886800d0041001450300c280c203100304180481c1401040703074014040c0c40941c0b00c1d140c41d80321116520b04481c1c01030f001450b0f16540c07007040c41034411290422100381c07402040c617168941d4a52110a4618101c0415540d101f100410800b00c0a00d500b4014803032540074414250002c2600c0707aa0b0784040b204840e005204000c10001000441e11902e8000d1011030680f1906d003009810600090a403402c81350b0a80d1241c03c403202c5440914058424052514a03906191109086540000704020001d2260314000d0300da0b1303000100c1c0b40002d94404028200c00912000d05401d290900c08000d100d819007450000e05e08520188200c48 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 718071861 1250 718070611 718070627
    0x4030203060a05040309121103010609020a020a060c0216030b011502010203060306041e0803040b07030c1b29092113090e15070e040614090123060f03010312 69
    0x280140c01484180c41c0c04038000014400200700394100850300201054200b9807515641200e03000322084e040c0a84804101400c44042d544000c014a1040292100003500410640c100d0b6800900014224403510341c00d0f82840341d21a19001c21400c9244040b00300001d49a007076060382d52011541c100840900000c1c1c2c00c0744003d54540d54035620502c00100001d1038156203004002c001c0d031200300343ca5881c2c0c1c5d4910640d081600c08031003a00624081000ca694107106030960429186851401c4010703044a40c0c0111540680c080d103c450710301d0f5907019000c00c0d82d84017548413904e012003c5c410328008400e02c2e01c0300c40381e071990b54502c9107969140c0d0103039107a4015038400c0036507401c0d460764503407400e007805009000c00442c030300281c02202013402c41d158180f11454420f000b0b9482e910b60f1052040100411207155401800402c0c0007054402c810f42c40788064581034464482c0400024008080e6908003282c8141206911900002d00003d00030010780c05941241d02c20f6002d030071014401c20f0141e82502c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 718073111 1250 718071861 718071863
    0x180905041a09010f02040b120703060f1203030b12210406050904050a18032003070f080f070606030606060f210c1106100f05090c04050904020a050303031e0a020403 72
    0x85800902a451807080564468021050600000f042030429070344c002684c01c640d001c078144100c0428070290f07000d20b03100c815900118038030f005c02070340d820b1108003001d03200e842c001e0601c0c030107442c03040c0c0301014000c3d445204991001442941168111002d05955441e502a10340c680350744116085803030f2031140181c409451f03e985600d8108452758082c00000c0400614818000ea280c81c81890085480c0c403d2030031050181c1d0700c10509005443c00c500703080b180c0c140c0104659100700402404200e5000c4e105c0c82c82540010107035640d07418988042c0d024014008007428851800c14004104443d5502c07480c2150915100e903d0554a80c2c5401c0e02d0607000c4000d90481d070f803400c940502c181a119804804021a18141450484804000395250810403120080b42d804144811b00c101c80d4032941d03200003407000300d49480035450700303041d0010316014510801d4091010356011030215500c414078440a050040c003203079142d24004000c1c84001c0d41c11041000d020a0000101c0c00d100c20b039000319002d507 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 718074361 1250 718073111 718073123
    0x915050306040c2c091e0f0402010c14060108060f040f0f170c1506060a1e121a130c09030219030b070504090b04050609060f150a18090504 61
    0x555a1074240009811160480c030100060314080c611100300d46100700350214082882040040481000e004500d1405001900a8a04014000f040e840f6200030f60354130000c400742c0920141c0322440107071003120026000a26000c4081c0d2803072a20310000540782d0484000000319030345502c514010408681d825035002e440d0f190220164008201c2c84a14184e040744251044031021909019103e02c50f0000040c011030340d00200910381c60660180420350b0402000c5581515007400c81b9805024101c0072602c08580010b2401c0c0603415a0080c81d0002c0f0f0204540d80c24820300780030035250400c10a0701500306200701d04031104410100500d2040d00720180d5580c640e600300c14210340801c00b86002211124511090201001c000111482146c034014043c0e500c45d41e848a042c1500310301503c1e62029001c0c022881d081c10043c180d070750301c00400d4210b102a28031410a844030b030046034400544078002040c2000004e80d005070380358041e0310036002d034860340004841940c03560b040c60190b90f000e41d400350507 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 718075611 1250 718074361 718074367
    0x2040b04091e1b0207060c0201120e0f100c020c0a2d080d0302092806110f0d0c03090b121b0904090b100b07150209060c060a02030604050112020d030305070e150901091505 75
    0x210b0ae41e94015a2204d00203811079407241161020b036407a00e180e01c0d402401042d1102a1000030507010421920303141c0007220210b48050501e60103040e4045e80c01ca407441d040c88050714441c40b81d00c1c9220804041e08030041a11680100510040c0195014036075680c0540030f540b00b03803685601030543d000c058101c0002441401454410101d50610a111020300680254005910303100c000300802c650702441901c030324400030868140a8616441940401c09064080241c00e040c00c201c3e20100b035100402e20102c03060074034081d1503484240200580103401c149454508014405810540b078820940d1207860010152110340c280725034003418030001d00c0c41c08001d03107a0010900d1174000c0c0c4401c080191035503042c80c034a41d0007149800c100340d81e0030702d406500109100c000d044c18001c8902400304403403614000a680ea01003400303140142c00c0074042550b6a404078980324410703001010650401824a091a29007501500071580a8400c95000c40e20519000801550046101070654101c0c0c6580e81 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 718076861 1250 718075611 718075637
    0x6031b03141f0e010305070e010602030c0a02060d0b09090a12050c060610170705030106090b090f0d171b0f06010509070f03061d1902040b04091e1b0207060c0201 71
    0x110303002070071150007080b002d00da1000c22004040d90429008600501c0148122803524420020b00302060300002c0440d041080040660354000400e800c0c030301c1d41a600fa0b0707641d8844070304000c000c24400280c1c690000008061004080000540e0380d105402280740f10010195244241d5103032060000041c480e401c50000103400380b40c2054a035010588600300382000f002c08400c51403a082e4215041003b10744007000612000741c1c8192702a020b0300320034841600e0040074000059210b20308884951180a008029078100055040005907501500391030f951140c04c1c03c0d011940d40e0004e802c0044d417a105540200344001800180d00741201c80113880c1642e03036280e010044a007818240310300c1050544819000412050181c4044610200b05201400d24244940c541845c00c01131228203c2490040c481407001540043c01c40e011118141b100281c0d4240020100b618082821035031000ca0707245c800b141000c040d00c49100c1181054980c2554a020749608013038600c581840c4000c0c2c00500da82c50994 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 718078111 1250 718076861 718076881
    0x5031210120609050a0f0b1f0b0301090f06030501060603020409110708040512190b070e030703030909020d1104060c021212070303050a0e01060807080f010612020f060409050106031b0314 82
    0x1240f03081c061815607a0310310a6882e0020082c84810b011030310300f060f620411000541c5c40103a89010340c811120402040d240c18061a51030206020300d050712541c0c0e511540c020700490f4090340003103502200a10590fa55248081c000303400a10440c0100c60500b1200d2219404040031140d80b03690000d0610304180c00c0005201e090641d5504911451050440708003016400d50040d80846200d81e52000d11440e1052000f4a9582e034400c0d064001d501102050000035003011900c016150120401a1110010312404002d06078170184c160031030300002804030707070642e0010010508038004c1c0e68a4058130a08261a69215a407180301000c80b03400380880c0e40000d00c01c0d0082d80d0481d103038503400b091240d1071040b01401c48601e503100c1225070340a43c1080045590500050015181c0d000c000c01c01f1514180c446d01e40f8180d0790340f0081c4541500d090400b00390341d0342002c1d80c000e810011810030840d0307101c44005c1d00a0071b041c04c858400c81544426071840794030038069904070a030800c8881d000e51f110716a101e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 718079361 1250 718078111 718078121
    0x51c0314010f1203050d050a0207060e0a0c03060b150c030a02190c05100e03030c0106030302010e150f100803040608061e010f0c1529030703050304060c0c090504050312101206 77
    0x200c041000c00c01100c6c80300005070103003500400700d40c0d40040c1d65510618205040381e20040400c1d656400c4840c0d4803001c21525039a200032242c1080010404010210000b00310784c40240c81c1802404004c1940c0c01c48840010140040781c003e80c0803524040c0300f603680e08007014000c01009102051103407050241e82410700f0b5120b0307900403c0c14824820104007000034210b030403068404446a55843c410000c1c9a824029000b105000b82c0140c202481c00d00318804010400400c0324200441c81c41c04034030300c03543d40c034841c000400100307054940300d6849010003040040305548492080b004c41500c460005562000304940000503140c042440071801c02c01d40d101503d440c402e81d415034803600204552011801400c5040c00300440540120422031440c022100d5081ca6850195028002c1030001401c004125410f82c4c020f4103200c54400c03020b160003031142103c1e8010011a80c101000c1c0420030100102511310010b000b90b4080c020340d54244040c7c5c01c61203a00c9034801c840014450308000c2265a401 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 718080611 1250 718079361 718079363
    0x10e1005181002010b090a0b0604030b060d080a020609060702060c090904050a060501080109060617060402060706060305150105180c031305101a150703020a0b13051c0314010f12 78
    0x162071400304548000581071414005030b0340140c0d454245141141c0f502c10481d6034006001d61003040040b4802000c03490314001c0c0d01004181100110205125640c0d01c280e034810194000701c003030754511030341100035210041074600e0902c0340300f41c0000c05c0d07820340013040182c490201520b4541c140703910102042100e400240042d2000c1c09401c2030340002c54524080c06028207509000401c14141c2450100111411940080c1c15000d0307103081d1078016600440e8954000d45c0480380300d132b116506410312500802c1c5039840103015104a0b1105003604a0400520741216004c68881026450340700704144090340443d599054881c041000a40c04011581c0c9607803400d020304101c0305e443d01104003d50854580d55103280c41141e80c4004607481d480d106c00110401c41310518043d051000507500690350b42c80c201002071180c106080043d96610010a02c55844da40101c00c50b490b03408a0540d0b501803201202d11500084d00303120003800024000f000f0700b4102e451481c0000c805625113020401d0b081c0030070304 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 718081861 1250 718080611 718080637
    0x424020a230904090305130506040e04020f150c0703110301020307080c0a110708010603120c111e04050f06130605130905070f0305012a170a1b1706010e1005 69
    0x11140502e42ca85101e04040313139209454869880c20021944000c0c4640c661000703128090801041c4811404041000d07007003641912050000002000000e025026485094880400105aa11078140002446421203020300d802125003109042414240d2200711801804650103002086455101900501c0220002e180010001d140f051446040c0034456010f035030307942e4442605009200c0c403a48040e4078018641801401d113900b80c3e403030403448146510024855040e008000c603142c40c1c003d0300d4249513480280200440d280ca0380c103440764403100765009405103200d1010400031103d1846801d00b07440c0001c1054603100900c03400800075007107561040310f050080d500300050243c1120031600280d03100310000303d00503082200032019004101411080018070000610769582c11540004100d190580c00d000a6500d10179aa07000d0304542906400f40340c50119000400c0c0c0d401950085201c2990b41c4002054442d00011160440349491160340000346c1c0d02c030310004a02070f00043c010624419 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 718083111 1250 718081861 718081867
    0x604020301030f26041e090c020d1d060406021b030d0203090d080405030109050715081012020414190b0f03061311100314280b0f090424020a23 63
    0x421306240da001a80404c01005005000000b4900c100980d20003034696031000b00480799031820000d555010107285802070000c0b500344000e0001350b41000700c203800006003080342c0d0381390b446c18000e5444011038148030719800c43d8180810a86404140150b0540180e8011070070301400070100003244600020860301070700704100000e41502c0038081c02c20030302c1c060b40c00b40c0701c180c0c508802c15a480519520800406c005401040802422003400c44261000d10070302507010b12407440071074018294500076810300d120000810440c0305203038030507144c0c1408544051055030144424040c0000c1c43c60140396040c8c1207040080ca0a0814901c01d9000ea4010149051060114004515030b41c0d8000300c0c0d42c1c0001d03103410100e811480c90f076080503000308804c480751908580c51003250f658841030138000902203485004401d220341c0e400c900d611103140010513131142030030a4505003c0e564810a15020114000641110541ca99100ba104420169110007101d1441c8030701e00604112025402110b0f500c0174 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 718084361 1250 718083111 718083173
    0xb091b0c01060b030103051e0a2a0b13050103142206020c010b1c02150a0228110a0e040204050a09050307050705030c0604081203070c1e06050604020301030f 69
    0x9002d08001003804105441e640e504600342070707041c03000910f02d5905104c0d002c688070405d40c40000c0c0c1555080e800484116a000c128234007005074145c000c1c03584082c4550844003041e036402908c018483d60f0010442990f400b5980c10040d01078070010345018000c00c43c3c0d60700144821081d9410f1060501800c3c0c00404c403805c1d03c1d038501040382c00a0000c124140c0d03550a28411030308203a14041c58194200c0910405035880f54006030b240d4a901c00d03107030b000000200d182d07410789008200f07022842030550000c504130a8540c9200541c102007000035218104003520340341035400d042c00114199008020402565a900e40a000c050a8080c11582c3e420341d41d41940c802180040c405005424801c034040d00c200340c80d00c002c05180010842c0d2407031194004000400510500190400d200d00074800389030b071259103038801030b6841d140c4103030080d11a8111040740d00134a04602228549244204804c00ca6519103005101c1240800d02008002c40403402c0f0001c0800d0180d200e8528005210580840d14800 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 718085611 1250 718084361 718084363
    0xf05120309150903070909150207050c010f110d0203090306010e250c0b011404051b160609021002070f0806070c1e06062c072c0d0c05130b091b0c 64
    0x144d00c1b8052036079554640004111500b043c8080840501006604010841e12480e485102c082c1c185810b00040c81125154240078614202d5030031502000e407407003d1440e25029407290300030445280700b4000c031000464000c0380c2c8014540502200c10101e181082c0c0003944020350300022030640c6c184041c5052000005802c9813009000e0101004070365203051a150501095a002400090100d4074034a5140c4107500c04030191201c0c90100c1805050b10603081c1010ba004200c8080060b410890340d4064012044e00091603a0031030348101544812196204840c2c0d48440e405d41d9035400290301d80e4884004140702842c040d480600750b065400d00ca201680e00c00d800c441d81c40e803002e41c54031011042900f141d10442003081180184406118281c500680c0050002104100407040342c10700c85155502d030740101100c003000700c801800e44110102c0302d042c80021000b4901ca42c0d88250306101200d41c180005004460314200302400b1058a910f954030401c10a015002030700e0340d0744400703001211440344 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 718086861 1250 718085611 718085623
    0x10f02070f0f080d0206060f0f0d0203030c15100311060c1e0106060f090b04050907051e030604060b070f03051803010f0902010212030c0a14220f05120309150903 71
    0x1110075190340080f80751031415418000c659242c6401e540201042200c3d42d155580c00200c05031040310016100e40c41400080d043c0480880d000e5090b200204001107036420009000200c070300d0b0030712900c0550380e5286c1440a850058080107003440056442c9606a050010140040c800001d0654150086a5410340220421680e12050344d80d100c00e410480c0d150807400810404d009407410030020383c1000080c80361072040b841440d00440f0300d4400500742c03078030032410303111001040501c581c0c44918149842025804c15100140f0861400d81c3c0010320072401d170111160f0f00c0c0c0c058003541c0e101c404c0782c4066465400c000355120800050383d910b01e0031035a0078407800b04000c12000300090680201d000082c5004109109008012420030501180c1000d0130103540d45d00c0701503d040c1080034201c0207078000f18050540707070040b1a52142c80480c5200700807005e020a848840940449403640c0d03000300700d0403451400f804034182d00100500e0606003030008404c201242650181881c00310041d02007442c2c41 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 718088111 1250 718086861 718086869
    0x1107120516140a15020c120c120a03090c090b0d060c0908030c100506040b01020a0803040503070804150f021b0d020f0d030518031f0207020a050303030a09140714010f02070f 76
    0x90860030b035010030001500300d05801c141c1c1c4d0440860802c5503041c07489507561850300f4245881b00c00414200140d07a03041000c1c0c04001240c00101c0c0d10342e40e00001c0031700035001448003160881a035410208504505124036980b00300d0090030f008845541d17868031801803a0210202c000c0042000c03020070030b40c4040008000e9142e244008200900b5140b51010841d0406000c8920950030420b550f046682c0c000340c400d16064001c00c031590340c2d0f00c1700e1500301d140d0711071104002e069000c08a8005002c5011118055070a40281c8541c1c4d0414011207040f61100c004120600341c00d07892030024555411301642c1c50190904c06450381c442d184211000900d6032640c401d04034000341001a03e801004600201680b1180c2c2c107900030604110904141f40c451500a090745965990120714841075613501c0078603000402000e030980c2d982e401d24100c80c6016183c403040548040610064101a04100003026401c440091022544201c80c0380b0044454819031100c01c001c40c031074020003080013010008980010 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 718089361 1250 718088111 718088113
    0xf18070f1203030b0f030a03080a021201060f031a060d0c0e1201061a03010e0c0309030d06090e1213050f03100c030b090610080711070f0806040303110712051614 71
    0x40c1e111440c0040c2510781c211401400340c078404103141560344002940441c100d40c0343c03d1190195a40d1341200c0024061a000600c050070002e0001802941013040c904c00d9202550341800040030792602550001a031a0300d440d005241007004256031000c4d0362100d0017104d1540303800700150508200241100c0350f00c0f240036189035901e02c0c0402410501100445400644524071802c56260580f0102d100d40004c250100011000000962002c402d00844150000000082243d40d0311440068001e21080040c0f100500c1010400904420200155a2048aa800c0200241d420103061124010300c40d281e0f15058440d44180c80201c80040c007a40765080c1d1240c3d80040d0f10b08010781005000d02c0003070241406100344540020300e00d603005d1041c0d58880b446007031442802110b6515686442c17007035403110780c0c0d00403004e102080982c0007144e690700540c002d94050221881d120403006103403080030b400030032141c00300759200c0559003d007002d0718400c200d10030800e5030035203191540400840d403100740c101d031 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 718090611 1250 718089361 718089389
    0x903120c150203181f0515030307050d030506010221090a050a030803160309020f0d020a05030d110f0309010f0305040804031e050105220b04140d23030f18070f 70
    0x14681300c00c0c5492650304551001080101ca07003807420b03c0812400104198401e46030700020701202c248503103c6a1743c0e140541165074400030b074103110761202da031070304840c000a0030701000c00c500e50310010701c1601da440d091402c4003145100c07080f00300190344128511508801302c07940000d565038030780c6200c400031070044070119aa0b107840780340050240820307140c41c1c06040c074018641c409078850401030700b024981079540107002d202e903000144d09901c0740d90100760706120b955100f65806a00c41d403a050911503800844181010310050582c0300e0013161140b0780080c00c4030380196101031090f04103d40082c00340b03919074601034072a22451071800c140076042d05220300260348041000424443e00390b02054000905003030010b07000c0095a810692440500f40410050114051003000440101640c599008032880c4458030003002c0d0049446420340c42e500c9c1e102000385030301e0070307407030b030101c034801c0602844084295503000d003400300302d480a030096280c03481842c41c08101d1070748078407900001e80150207a080c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 718091861 1250 718090611 718090621
    0x52a04060e040c09050405060d141e0a1a0a0204080d091806030b180f030301171203010b2a0a03021e0304050a330807030c03020306010903120c150203 66
    0x11003501c085140d028034544142041000e41c01501c80040d984103d4010945441d20000034214040c001d04c0074020350090500d19000f903d002504144001000d400c4015142104401580300c9030980000b41018902800f8030081c03040c03580c02a64000174840d030046c00c3c540c50b80d50840c82c00085514000204004013401c1c0300c0c942c2c400010003400b2503160000e0101e40d0555490483c0100040c202519201f039010204d00550b03001d02542c0c64040321942240c3e16581d5400400729050144418611240104440070340019403039022203050f5007504038002e04d42108001100c1601d140003401c001702c01d000d00d406014220007844501e104500a90040441c420750850418465101c40c0c0f0311240c40d44108030401030740e1903005244023151103440000001e110b5003040e200c1c1210f030001010540c0201c100d050318851ba04412824000d01e40c41c0d60811220005882c26022440181c1c2e040b40442c90921003000040e23800803003040000001d00e0008840501ca5448100c501d0b0000d950655194001c42041 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 718093111 1250 718091861 718091867
    0x102091f14040f060801080f1f110d090606050d0b13020109051e0f1207090b0a17010903021203061f021612171c02090a031515050102060c0a03052a0406 67
    0x51b014001001c042c0c10080410140301c2c1d13a402015400d400381c03d1305081705203d05900c1da4810152103490b00e00c2c0d1680c0b914442080001061040800c442261400e42d01013002e00304440c42128087c0e2143c140c084039118800c2c2d82a0aa110007000c81c10000b80450115040c0c0b03601340c110b512420740020458081e0700070010410300d04040140b6501503240303441c002a6440740080c03440c0c201c1d00e60300300005007822110080740401c00a81c201001c8416400480800700034158400351080d4065404e0301d0342c04040c2c20014000d48001c1d240c503648104004a080788084c0b60109149045044d40100e0b01364010364999600c040213a64004a03001d2800c64203507040c0424400c03440c00500d0002e445510b004021541405226001f0302d41c507100913030106802c02503444110359800915042450880e01c40c1c1e03140c0d1520090681441d8100071080301110006941d400040c20380e000340d071499001414000c03171260890040c10018411802140d040c514065a030301c111074100544484210b22030358a9042c8040a = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 718094361 1250 718093111 718093127
    0x1818050312150109090b0a08070b1801170105100e04061e08010c230412060b012d110109060509030301031b0b0702042a0e0a080102091f14040f06 64
    0x642c140d441d405aa040701d0781c0c0d012940c64150b808400c00003403002e12250120788007015030307040205503114407030303004c0740191161028112481c04403424010325810b03800115044603065440e4a54040301c040140000d183c20709110215000b0703440e00e5502c202000000a06440e015888828622001d149500c0303003200319403144018205001c000d003c03881c8240c10040c07007a07e030081d000400c040440d0380e5440b07101d00b02080301c0091040241c0d0000f6480c5034201031008103080c0c510b81340400c0400103a03110000311080340403604610407100d0302150003804010340e5004500c4150002d00e541e02c103044d5001030b04c240b1580d40141486c070001c41d142e605610b0f203070340c2c14410308500c06400503a40c0341c10840c10a00c20119071001e81d05403008a5010411100446081d1780c0301c0e21044501091b900c40b9507035a600c06901154075104aa0402500c4d0740c9010ba10700f02d10900001c00e030400819642410b17424192111030200030b03c2c615042c15005942c520000880d00550400350100111001c1004599804019 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 718095611 1250 718094361 718094371
    0x15180b0603010606141621030c080a0e0a06050606040506030103081803070305060c0a110f0a020112090c0b0903030c03040909050d03140f0a110a03020d0c02161818050312 75
    0x1105440e030034a20305520704d5003d1b0111a004000c41c055004040203e11401001c00404031b44d40c0031a01c0881c2072014024110044954002440260003d85040040c0c0914085800401c000d41004100350b20381c00042d1000505080d008281000001200c4d01c03410003c41c02036000d4000180c582880303012514241c0c104000303003842503101c4131050021950126500b40c015103560000743e42d9400d20700082d10070f441030300a142e0741e42c01a145000c00000001c00d80e4070585100f42da90141921001800c80211082900e014009412082082c003c81000e807000b8056207200808507810300d41401101890b40e40290402d01e8101e40301c210314010401c0401c50003403080b0305400d0500c00c480001001c1c8003240e10062499000510040c041548103501740e0000104454401506079601c5a02e100a8045e5200400c0c03c00b003145001c0503030680340e1010031030440c0e8284c0100300e01505840c1c4001703a2601d00f4810411030345103a0300c900d00e8401056072207a455080707200e00041e54072a030800490201581e0001c107 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 718096861 1250 718095611 718095617
    0x30e1603050d1101090807200108100603150b0c07060e091302040218150705120f0405150c15010302040b0f0102100207050f0a2f01050715180b0603010606 68
    0x110500001e040070405040c0b0000743d180a041e020412a02280074101030107001d418208001488000c0c8500c03c2ca070501c1d0518803480c1480125185001164001320031200c3c0c03040081c0d4080180700203446038129408800420741c40c01c0e611600d840310001030b94000b0400c9400c036030003c5820414181c100302c41420f0024102c0f04034060b07281c0420b40b0b0a07210040f120080c8215070005102c900341c2d156011200e13200c000130300a000303040030189042c3d8603640480c0d003e03122413041c00c0c25001c1c1d01600d00708445442d041d9252050400d45030030b0034045035403400c104030090030b2014004d142c0007800400c244480c0549503080b80e050381d40b450042c001103c6d01141070324010706094007519000d980004917200ca0b40111600141d0b1043d16080503410040010035800c0140111410942440010940040c030945000da104e0403407025030712207200c054805004240840d50030301c511008074805015000c10039258040210307a141280071006852014030038102d9000c1d4441062103400e0034248180c002801c0360741 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 718098111 1250 718096861 718096903
    0x12a1b0606141f0918090b01030809032a0d080c0f0c0a0501021b150f03190506030703050a03141c0606081003080f0a020703150c0f092405040510030e 66
    0x2c028015415805075150784015201580384017000c66001940c01600902c001c140b40d40c5078030b04512158403102001c2e1191046901d0340d40704c2d072080c0c22580348041344484507011401c1c184092207401000248241c5200c0414004800702c02c40511492030900900009004030013030314401c0090105c02d5822450455005a41075145112000d404042941c4101c0380b1a007890416070414a2034420702d0b8155030601c1c00403050116401d0f41120b0300c44030301280c6c2001e00c080d40d50482807546e84d14061001a103070742d100052500202f801000640000103107038019600c0c00340c2881d490003611201c0410501c800384d03100420008640e2200c8070036001008178150100107491a266070441d401030078034100d4455800100c1814450007000107500559002400d080b644940d0880742000300f55004600000c10a081e00c80c020307503440340500c00c0a440a060441e0f110840d00308607550b4816076021000180001004045800d41d2440f152000c042d10306e1341c001c0380300c01c851a86c030f900b8100303164054903001902c6 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 718099361 1250 718098111 718098169
    0xa0302100e10030b270a090606080a081216050a05030408130602030901140c07050609060405040903050d0e0c0d030e010311030109270203030415020a08030103080c012a1b060614 78
    0x10017520b030810b10411000c568005103041c440010324035030b031104c4401d10420103203004000c1c0702006000c142c542d00034020301d607658200000400200c40c540440000720304210382d41e80c0c01e00078405181c006014200890400d02c0e26101901265525085600036a101103160b00f002e6901c10702154100c1d201d281c0160408100102d440e40d02d007001d0290500c40c000100342e4a12a895820690b002000c00600030701c80c940360350501503d550300020518001c5410b0080030602c00724005001e80110340080d018040d503409548003290001c0b161090749041540360417145a04945e8440510701808902a001030104030718881a0410104100c040500e0100c03502148007681d80442070b5070460752040313101260038002c0c01080382005840d03100100300f004040004002d01403003402611480554a00822a91100c6270200005038005c4400444006481c203030282618401e02c13000354545c0c00144407400e0340080da81c602050b9a03094100d501c030300751501200050351928105407800303000d0b111ba0800303102540c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 718100611 1250 718099361 718099429
    0x804061b0f0e01050712080417030603060f06031009030f0f18030f051501061805030c2206030218070e060f070b06011209030c0308150a0302100e10030b 67
    0x15610700c001e2201a28000c2c2540c0d0207141211013203039100740c0701c40c40c450810030b010300070400c19901910906040c41002070b001d032421080b00e000d504024010314a964030300003000c0456400a02e00f0390107006031b6001118000ca1801410001e6100c0c0d250741c0e0701c5904091005001d091180200070400c02e90986001c07280490210403030903650001e00812020996081c1180b5002c4046230590602c3e580100015580746c0c0815044052020464500b1030b140e602e0301099540c2d00c134030b1000740d4022180031001c143d01c0144038160086602e00c002c04608136980b5000105030181d46141880101d084000300305031942d20455191181c0c00803201203042500241c0301c400389002d07202d4020103040700034012402e103a0143c2c180c1d0b1035001c40c524081c400c100f0b4618008105c0c0300454000c4021032200400300321400080c40361000e640d48041c0601103954955004c00944904964000081c40f460074202c212139100e00390300245110003034401180203030800d005d00c800c00007400c0c075503442001140c0d0760304a0001 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 718101861 1250 718100611 718100627
    0x20f030105061b0a12090608061c050c0d030815010504030f060207031701080a0309060207080c131103090303040b060f060703110c1e040e0d08160903020307060804061b 74
    0x8040d15840d03200d01885018a036002c2010040b00003920901284c00100301220800c4501c10f04950303a0380c0d04050360f483d0103580c4041c05841d1281d203c40b40201906058040c20307504542d19000d08112031828094001182810380010400d40002c0c80341004c0180b1905036217600380001d482031034498501071650320358000c0007903420401080c0a07000502d00d0306061040900807000781400d400c020455039501c680b503a64400540e400c40101d007588100082c09400814003404880d681030103048025445801c0011003107044900e1440e16603075030042083c181401c40554810003c01d801596a8181410710518200c00100a00c1c03040c200c0e01400641520340b44191801320354181045100c6203030340b0302200e050141102c50181c02007141410340c2c0900036195841026008155810040780d038003080016142ca22600190002c0303140d88cc017140700c02c81e041036806442030b014503080311880c3d10784e0700003410101c0360750041c0001035445041c0414001644901d414212103001012182801d550025107120 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 718103111 1250 718101861 718101869
    0xa03090320061b07021818010603020108070f051e09030f011806020304030c0512040918050601031403040f0e0601030b19060809150126060106080a02070f060f0618020f0301 76
    0x901c407000415003985210305403515941e00604404da64440f40051b011025011240c0300c155502580e2201756400041c4659403d50b070f010f81d1801696501c2344020b840c64140c0c400c401040000030000b008651800d42007001105058928440d52031354102d0070103140080d01094201c984c0d141020121f003451180c0381c41c04a8030781c030401c096200c0d92242400c2d1000f01d02c0000103012070040c0a0300d2800010507000510566400000030404000000c0e4007041044100c80002e00f03552000d001403001c5071310b11452a000d60040b03c2124038064030b5081c0b0003064000e940c0907003500700382001489290360b014040e29141d1182034805013050120242103060781c000c64490034040c4a080340108040034820f201d0b1071076220800041020300d5039a20b801e84405050108a8500108460318081c1001c001044080c104c0d40c8550302c0c40e019807a1000e2600007584103032422580070050158500026040c0e001e4410120081c107800181c3d0f51509503140160011b40480e002d40d2403040002403040c500000a8a040d1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 718104361 1250 718103111 718103131
    0x5100920090d0807060222060908031b0a080a05040815060609040f0b04091a01150503041217070206060103060504110403150228030f061a070204060b0a0309032006 72
    0x1596030760400343d41074420420050001400050340301407190994416a84a0800b291100c0349255200001c8410362034901440c1800c1d08104010508034589000403408081c00c0c3d405d4132a401401c2d175422000780c0c404010100481c4010030b04000f070700d03400d0100300b04000c1507010140d51841c2410000340e46110380007405101e0f130350340c0c816030506e42d101c4d510260360400080d2040288030210306069010310100f1045801c01c450550010840702c181c40340c0316003950314a44401d03055403600c0e0364030a802c0c0c0860000307408014000521341d03400019109440e000e080f2540280c4640c2c24088001002d940e680c2e004540102c1c10300c0400320303c413040c1004480c112034004c1c903520a03110107012404081d10840b24005a40031000c0e11184c06900494464048010291000c002e10500e41441100340c0f56180f192461200e600140d850b44485554010310030340e0310003031001911589440c000e0341c1c02d4211151100000340e0b111b00e104101600806061645844031340d600d13115641c805240303980e4481c01003150003030b = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 718105611 1250 718104361 718104379
    0x4060e040609061103090309090c040e1b22050907080907060518130c020712020d060908091201050106020d031a01051c1103040204050c0304110f0a08010510092009 72
    0x502205620011009207804d0060707175681010500300b0303902c2c0c1156040c5d900c5000c0340c0300414581c1c3c40e64001c41d03080703139000c01017000503a0703034004079805150138200b4201010350200640c2840c22602401d04689070080d518806801d81808188101c80e06c00900c45000c0c084881c1c140300303401c00300080080480e1000d241442e5510f0900088102040720f408005c0d030480700c40c16810103200040c0e0003600364200c040d030880b0446036450100507400102c0c0d00000e508043c0e43c0481c3d03404149980c101808036401aa10341d4a030499040101d4642540c00c44070000036507540d0b00602180ea03040c085000c60200f13524007406401c0c00c45025890b01c01c4402610f40c144035000680140741c10740322811201c0f441030008100080c0c09810745002e2a0781c030845040b40310b64940070015a44170003e405990280b600041c0e89000848002c0170f01808540e02030b44158002600d036400190100240161849040b0400c02041a645030008807410348074034001d00855102a4031145491140000542da8103e40403140507403 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 718106861 1250 718105611 718105613
    0x306010e060d110706020a0215070e040b0d150506091609120320030306010801150806040515030706050c0f03090108070509181f36020d020403050a0b0604060e040609 73
    0x38207940f10f0442511001044d0001813100355030182165019030f40986040305542c0030101c030b4024084602c40042041d604aa24031421700d640000c071100c2004d0b240c180c4025054440403d050488017080e0a03050700e900801c003441c101182c1c41a04519016070101c0c3d420140c7d2006403031502035001d48445002200b22402c140b510800c82d010b07802015201c540c0c3c115850640d01500c0e079100300e50b43c502040b45075000042d80502c0e8607134003440c42c03865620b0040507100d03581000080d041c00f0b8800d0400301c0e6918a80340c1740341d8090001c4001400180c0711640d4035424900d884ac1004caaa15074403155400900c01a01e059030003070141c5a0000a070300c0d0607981c400384040081d40c100b80f401c0092112880400c00c01084801140e0000f00068400c2c5005401507940c41c0d695840e03946c60b4048112060100c03c080b0304520041c90140420142c4000142c00d02c00c130541007104030f0308039030700685881c1e000043c1c1609001e009a9101d0f0082021b40b03051158a0a0100c404084d00b0302400003082182d940c10020 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 718108111 1250 718106861 718106887
    0x10912140a061401060e0102030901080c09120f030c060c040806130f05010c090305191502070602070204020d15080d08010308161b170f0d11100f02031b0306010e06 72
    0x1001154410801c00070942ca00d0f0101000300024015200440c07440700e609102507000000355000d8081c140c2d2122610317551581c1040c256000120b107260803806410010100c20020701c440b40003600d04000554603405030490701450050060224a4488801c00040c00444008031303006034003055142040c0d2440e0441d150080403501070140150255291514104015900032901c1d4116401a000ca86020b107031942c5803800c00e204460024461000001d046442c02c9a5401401c1864040c11005040900c20707000b05040e680054a0020f880e41d07900c1c28103541036001d0b4103801c05000c01200904040c01000e0340901035039018000580704040121b07001c201d9810720b82d0f045d01d00c0381d0f01c14032869603502d040344031a00d00c0d40300340110030040342c45a0b1741210740000000e58851041c2030000034001160030740c00690780c02c4004204044180908a00c04442402d14003a03848028a48100140c0d0781c600030f62110b034030b040000c1c0070000200c1c0c10400e02203182e03800f00c0c92001c842c1f0119000e541e82c0d40c59031058 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 718109361 1250 718108111 718108123
    0x30204051003140a150506090f07181d180c130603140d02060702241003200a06050c0c04050613090f110103091e0c050402220501091214 60
    0x1045900c031060020500f040200300f0300c1c4624407441a00f81050003030403416080e00d20842d8aa41c006017910000f81507030444243c184c3c4c02060781e04040d4100e1403040d01e001a0340055030000d280619001114032950b50350500000d40c00500000e0206581009000e59504d852800102511841a041250101044c140d201e00d00841d809100c40b10301d0070480480b191100100d10000c005401200d00040711a8008620b814100c0307018054403c045022000d511403040018000e241007a20301e0304044002080c1d2910499200744509104442182040c200521068035402c84002c1290030f100f003d07c111303400a41c03409004003c46c2c3c0454039170741e4400820f850030850301101040e2400d191221342440780351030314607400c0e42c020350740c6070301c03900003d401034041e503100003401041c101504030b1203840f10704401840005144503d071001401039035400040c1c1030b0380120302c0c0900c4070034201440c10f264031100d0a5201c0102001c4c2080740c110340c0344c15040c1030b442c0c2d641c05020f009120014806a1b40200074041 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 718110611 1250 718109361 718109363
    0x503060f060a260c0405060d0e070807030b0106020a03120b030c031c1b030806060a02070503010614090906090c0d0804030f030314310f0f031d010c020604030204051003 74
    0x51502d60180c1c02004000104401080b07401c1c50303c500007921407030320a41c0f00343e00c00d00c101d5100900d031610b0310090050651100c1e04004070b46a548014114180c0d040c400341008000140040c0002411428824902081a40f1440565001401c3d07000000d400105180d0842300c17520000540086200c0231a08000308100d0f069814010203803820312500f00d4411846080103113a45040c000340050020244403a8803a02c05004501d5480014400346007801c000d00e55410148180c4080a035143c0200e0b00395a501d811101030f584021070111183d041070115683d108811000030010f074245002c6444d100d070040e005c224080d491100005003480100011900250751080003134069010900340103000f000200c0ca0b01c0b00c103548140c04100d00c0c56159900030014844800e00c203101c5c222408074031958204406c000c9900d1490b0f0480800454560b20020844d98044d84541824107900813004114684050f8034505104203001c019015851300010755003503980c180c400041a89a43d01d03584184200c0d030348 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 718111861 1250 718110611 718110619
    0x6071409010e010c150c050c1920060f0c030711030a030e0f010c080d0c2d08190f090b011a0409020f04050307080307030816050d151d01050906011b030503060f 70
    0x112440d03401398401c008110340d07090075040d610345462270980e0512050514201910043d503c1940062203003001c0000341c01c5600c014482490282900c000a41d5600700729180411500003207200018440f403c0581d4024080c110041c0000040b160b5000d051a50900103090083d03078000303412503a90340217282c1c6500702504403071907944a81c4601c0b40070005e88070b401c4542c000107100d04040c00300c0004000321505000e00303244c2e2141140d0500c900c00c03116034000a00681c2c481440a00c1101540070f070303104455120918150100d1890642c0c10217440c01c0c18185c1c080c800035160901c05c1045600782c4070948059860f0701e000582c0e40d8486031190703805800b9941002d0741c580581c80000038981c0b000401000d0043c400d4550783c00c207956082079041c00c085e0950b1a840421001c10240c04c42d07221903408160b542e080c07a610007003200d4403102d0b440807001c2c1c07040100c0312034941c10005004900e0081602d541c814424a004443c000c04402d054842c000c45480080a010012011400d651b1b912034602c0d0041c0c00c054 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 718113111 1250 718111861 718111871
    0x14070809031326010c080a050a0906020c16170304050f0d020306010b04080709020316180b03100810020403030509010c0c0e04062a0207050f0d0602030906071409010e010c15 76
    0x481d26442c0b0040f030003500c802110f406080c401560380180100340e205101511500a00e54039507031004081e0900070100c0320504c0e580c003032800000e480f0384007400040302c25100500d80b442c84c0c6c07203107641124965004038540d8020f1510b0500c14000c00130450301561804d850344813031040c00d8400300b6000074071600b00075450f00560002082115400c0080c1085524100480307540c1940c4125101c120700c070035142900c507040e412540401141c0158007146a5403018141514030913914404a04642c10a035501c911214500c01c0c00c00ca00c400c200441c0d5080c000590b021851b191440d5070280161240a40f02414845d03080c1c0c0300c0f014007c3c90000c1c01c006081013030030b01065203044e262500040c410260904401d4000d1491040620020600521035100ca9001890010b0400c01001210600414860307406803120800500042c140c0c0084c50049046100800c0c440c00d1208010f000d0400601c00c517054683e003408450b940f41e80c4503810002158084c03d00603507000356414107228040b20b210800b40841c0c101 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 718114361 1250 718113111 718113119
    0x3010909061514030607030b0a06050306011e03150b2a1507020a0210170403052a0d2c130b280501090305370308011503140708090313 59
    0x14401d41c2e41d81d43c40480590381c4982c0c5440b130039012140d08c0007000e90001c41c0c510b800d1001a0007100110b402444c14106072090340e8a00c018007613101c040081e84000640c4403441d04e00104152010b400241518508060421a850340e13060030b0360074243d10648100c41c510b03403410451750301800814401207108003644111300e45000d0203580c9a29a4804a01031411030900300501c1d40304100103000c10204150452854840762000c564981000ca5541e240781b5401c542c03400007080d0ba1452403456584007024101c2000407100103032043c220760f54036207000c0c005071103281ca4499840314503190b01c880c02c42d800d03c200540700010400910b82c0d20341e87ca03045411035a21041c060495480844900c000405000d01c1f9038859004450040b032910004141d6885581503551242c900103028460b6030440000c0c0807641141503600c0721205c0c9559040d008a0050341c011b2224503860003048080c0c24030790600388400c5100400b059100b170300041454080105500210320800c1050084404c5000010300300d03d080c580b0703 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 718115611 1250 718114361 718114379
    0x105070b0c0a14040302011e02010b1009150e010f0c05030409050f040b060301200c0a0c0b0711040b1f0210020316030506030609070312050702030105043203030109090615 75
    0x401542c0c480420807801c4602401541d00048400303807503060396106600781e040c519003c0d0008905000d031065548515607410310752100c0314a007070034042e03581d2130030342a0349049640481e58a00300715400c104440882210305a076080742910000034403030710303190fa990202c030b0801500b1805180c100c200b00030f00302800c0c4644204d400040c0790003107008441e403010799150081014205c45008003030364000595103000c41c00403110302014258035071208040c0e03120003801e9503d03401c80e4a05a04030592640b4081405018002165509521080242c40400a01c517403880010109104001b032070117602242910035210030b2080c8502000c2d080c14441c259201d084c12804000301c240000c85801c0001d00d4000061403d203000520302d0f014a035001d020f0181c107070940c4c46075001e200188401409102081084c48010384003407003105d200d00e0144540c40d0301c9010002202105040224501e56013550403860101c0c02d401c01b0086a0440d841800300040b007800034038207000a0210903000504840c0074140008a20407 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 718116861 1250 718115611 718115617
    0x3050604080a021c0503040201030e0703030914040f05010e0f01080109380106020705031005060a09050612030f0d0c080f0f0a0e0a0c0f0e01123e0a090903021009020105070b0c 77
    0x8c400d89081c80240d903188101c0d651049607200242c00100c1c2d6507030410241c84803084600e080d0f80050804208801c2d1001c81009482c000c2c0c0c042050448010100f02c0c030b5444a204080c0136142100003807000c00d4294131100c44050050b110011034522000d0000719032652418013002400244c81000030300d41e51a036020b91102a1072140398028000c41070307a0510003076540324441c0b0616008001c000745904203c1d40200030100140340703e402c41584034800008000420140c0030304000d0100e19950f500110311442c042d203200c1b030025010f00488100f800305003141b4a5859038003070000d2030130b42c03555030792480108050003280840340d150b801890040418410300851010030b440e1071010481c03407155075401e2580100001d214600c80306524140050002e0b001c920104d90a600d0300030341c2042c0da00d1454410b0100601026405003504c0001caa5284508060072198000c040e602d104114a200d80d480c082e454080104d81c55450b680d40354200c0f0216801802540c60355034010b20822003d1070481c9992416034 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 718118111 1250 718116861 718116863
    0xa020c0604050c031b130c030905060f040507050f090612010615030608120405060706110f180109080c011709030c030307020f0712020a06030911061602040b0a03050604080a021c050304 81
    0x401405c0c144181038824414490340e800700584440d0503d20b100c00110001c1c00e2a22000040545400000010071020081d09020b1800100c1c81c1c112070800d450020f1038519a03038002d901611401e608443c03183c0e40c01529940c420b5003521800321060040303021a00400442e001040608030900c3e4035038402e541a4400c0d4281c03501c01c000c4540841307500d860b00105004d24131071070343c0c48ae604000700300019404ad00000c505e88950040f0a060012620b5203070020b8100041d10388981001d8044403000d0b613402517000c001481100080d180d2100c1440000b0066003000d100c000c81c03c0755240100341442000c2088800184440042d0f986070f00b80b02c2c80003521400f0018000c0032911503240c01040b01c0740c1aa680ca5449540100107100303162074441c00350081d000040054600d10020003c62115454100c000c00307000743e804802c44481d07007003481007000b200c4082c15298044c050700c000910000744c00064054006810468941d258004044100d241480c3c1400c901c030b140841401424400c0e800501940c011 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 718119361 1250 718118111 718118113
    0x509090a29090f0f1f0510050901020c01030b06160503120f07140c0a0303111c0b01030f020304050c04020913020c071802030f0f19050c0403030917060f0a020c0604050c03 75
    0x1078841505900c604101030390018107001c880350105010f031246259540c03170742c207813405900e4095645500242295035006c18410200d034001941400c0d0390b0b41070000b0100f00030242020054030301030001081040c040c00200721035414558408c071050280c200180c40901c0c032404403c103440e1414400c07150705c110040e22060041801426800d00071a07080050311200324400005204109494030201c0c0078000c041090100d0032010031400b0380d81c8075074410b200030240ca0071501184d5400ea40c40014100c40049480078060741c818001e2000040300031500c4041c4c41021a4003584481128000440e280310810004010031b2001030306524100003c00d2075801c4a040000b14482032500d43d0800d401d03440f04554005641c0c102c1000140a82d0250400d241c01c00c0841e102958080c101c038980204031241030703a4a511040011404204056110b180b1101034910710140c80081048020110741d2a500070305802001c400000014140d05000d5065941002009085500501f810b0808588805182e1051402 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 718120611 1250 718119361 718119379
    0x905030f0706050907030f11181608090c010c0605150901150e0d020d02370f060908061911030403030207050c01051801050d0207060236010509090a29 66
    0x513010104507401201c3d005901e2402003442540c4007035a802e0210016540700c503243c4492040130648414092280ea034021400e91030000015014113600c800034840845944a0343c01560b0340d9900081c5040c881e03038040b0300440c0580303034040f011948a800000c4207810000c400000105c40005400c450089105512405e5680007103506100c4050001180650864982e0325110014144015031500c155046400340e80380000201601854000509001f620610030010a0141078540b20401c4000e0105061004050b4034080d0900e0312008003e0000c0f01f4a00402003582c1e4440c0b40c1c0c0c00400c81d00e202c1000701956440c040c03038050000c1d0005802170313030307107200d007a182c484107500601c1281c040f80e20f00301d00d003108448030500450700c1d03030700010300729007405e030280812030005030341e4000340507152440d0b43c607521702c80f68250000d003a40b0100750350805480060483c03c84582d8204049030000c10003070b12400e40c29075502501c10068010310182c0c8030744203004401c00ca24100c4850707141030000011a41c4500c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 718121861 1250 718120611 718120621
    0x61805120d23031305070305030a030605040e07080d140c150114011706060c0f0a0b010501081f05090702032809080c1005030915040318082a040905030f070605 70
    0x2142c41901014a404041c0800204000525080442000511030000c44035120380f25503805003544c100300c00745400701c0d8545005021030b1030a802085030102f182002070a40703c5c03800249659503103e014508052000f000844640740c00d031281100c030318907491000c07216017140b14001171151910901ca070031010089072a5440656110b000d841c501d520086803003118644030780301081801d034800043e00e003c030300c9200554803400380180a0f81006034040d041000309036250800145c0302c0c03036000706410358095545224541101c000000e00c416a0402c1ea42504281c0d55038a083c0c0c5544a0a10301c0300030320b00360b2170000003d00603004030088080c0700c83d6591100d282d507913464585d40c0e10100f5200b0340c1c002054010380d0b0f007442c4100040c55000740034004450341c507201440074007507000d0255070a800045201103a803171a149403201180061400784001c00380c04650401c4400888444c06004004030050044034410f036132107411a101040d04401600d40d982c00b1a40080e50300d5101d00012107003c0c0c28400011 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 718123111 1250 718121861 718121897
    0x1209060f020a170309070f140301060b07030801091d0a050c030c01051305060d0b1906020d05090102191704080a0618080313020a03140307051510061805120d 69
    0x55007a5031000311216200d00d40d10038001e00e501300600031911849011030002c1c440300d0614240d40145001d650950141c1c3c039030b40a05003540d1050300680710400b000c2010800196004c0762103411510400310000303034a00460089d10121495036842010742c480c0003010403d0040201d60540850702c120304035050100d440005441c1401844112903001c84412000c01150900500030b10401c04510030000e100c000c40c100140c4001121149045007103074480b010303c8070603010442c40b160350000d03092803800c200071200000c0d55802c18070b282d80f111142c170390a40810000312040403d401410703003007410b13111500d81c44070a50303480016505944950800c03c05e41440c0740121004180d9941140700320b440c540c1c0c0ca03c1554102280c1c40c401301d80181303030180e000004c204c207555601030b10010200034566840703241c00c00758580803481564040d20344c100824000f180008040e15001c0b00c045003403103c41c500e540c01a42820a40355840703540c0190107109801a410000701e1841c84501c0d0036201d4036104900300c0340007 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 718124361 1250 718123111 718123123
    0xa0b160201140c0706051f060504030501140f06010c030e09150316080d1115070306030b1605090418060e0d0215070905120115030c1d0f0a050907031209060f02 70
    0xd40141001000042045e907080254802901070044850324220701740d0074000046980a100080c00105083c800c118082c066401d00621180c0740400c0703400d090030390495011014041c9814040c0800c100070805010726400d0440750b900404284181c5006101010b040d0800c0d0301e020b100c3d0080e8044046142001024035054402c480b0050203040c540c010142c034141d03010209440300b48282c9070007440c52294511000d105c0c24142d17901148007881c625054448000142004420041c2101c500c41c03140d03400700035a1480b40b011100803800c80c0061030191120500510060f1000e4245a414540e0304800640702401c12441e03800c41c1e60350340d2060929410f4842c10f0b6540000100d03810010400c5203014422540908150400000c5441407000d80c2d001c02c5200b640116070031210940b041104c401c46001102c054581c456802e6500d150000286200d8040181400c21440d514804910680e0003002058051603100201400441c008140542240030303610501d8005102402c1c3d42181c58400b05030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 718125611 1250 718124361 718124371
    0x40f06110705010e0d080c01021305030114270709020c0f15010e2701060320011418101e09030f0f111c060b0f0d0605090a0b16020114 59
    0x750106504210046500300d203030111a99102804e01207250100e000d00004000b03c1d2048000160384030340b0170f00500d100804651019100c4e900d001c40950443c0c07035030f040380f42d4851b80150200c40c92100c095020001c546190001c810648103510011800404980c01000303010740303480451b1131002c8003075203090340c4556860901c107002e1001e800400c0f030361a488030940c2c0c0081c510356601e8480302c405c200f4451801e11400b280d400907915143c00300b0034481d4000f00350007078182c0d10550808a80454002908503807e200140584c00320004840610481c80f000c0d000000000900c05101c140001100a120444032001c2c582c64032620105203552074041c52500e011681e102803880c0ba4000d958039100821400884250f0b411000740c04c10024550321000d914031206805a00045410a5030800c44100c5c4d217004403d5000d1141018040700355030f540001e000055902503c041665950140606e06280712404000d140301c03401014481569035181c0070140c170440c254001c10041d160f481d081921048240c030 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 718126861 1250 718125611 718125613
    0x209010509060d06091502070b06090916260f0a030914010804060b0109030c0f06180501200106080109030c05010b040623030a02060304061409010506010e040e0a060e03040f0611 78
    0x144400c0094a69000b441c55140244142c01c1c40346c144144071026a400a10219442610385003042030f40d180015400360025007020062601c00101404401204414080c0c00c0c103442101021005c3c041e42200b100b40760700c140c82e090303a120390405800c060b545c020015046011804911000c1440d91085040407512841691407002513169900c410009212a100b814108500c03050302101148242400b0b50040c88590010703803080d80303480401041c3d680c0f00c030346185503460340d58004c110350303070b4081c145204a40d4a0790000c4c03080790500001c04d004080325807212500b9400c01075101c05042c0c005d41d4035a10a0b0087c00240b0031032102d0f41c10402101e0071030080040282d0109056185124801e83d456802078000d001c45140381099000690383e50012a4100e510a80f9200000703202c56290b003074180c00002d018002c0c01030f4281000060080711040720003074000e5680d030a00241d0003104000013003502d60091030070002c4c015600179994507030b400360003003000703130340031300c00c001a40a1060490b103001150b880 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 718128111 1250 718126861 718126879
    0x121b0b06041e060b0d11040e07051c150603060501111b030f0f1b090f01030807080904020703030b010e0d03172a070b010f05030303040b0c0408010c020a020901050906 73
    0x360400c401400920500c1c41c000128000c0c09a64020314401c0c0c002400d5002c0503180c44030321124201c016034003020070034070b6105001c0c00204000500140016006242801e050b40c441940c1c2910501d0586440b000800c0c0c5400c1101c241c0d921a20249500b0540303559a4040c00102d40710001558280005440045a944420100340304580107440c000d2840d4001001d58541c00d40c10ba000a00c0e10400c100003202d1ba81200c4160f40004010111080e40000127032505040d51400700300ca80070390348052002820b1468000b5400c0b08100aa42c12500200c100600854030b0b4030503070030014010041055207501154200b50840098a030265001017010303455919403018001d9001d9807800284040c050b0b080c4c1504000546d010328064624807490031420703c02c41038840d111428010305100040c0e001c00c3d44688004420707c96501c021044981c842d810071600243d42d11291004001030ac5554094070080d46003510350801164040783c4400c103640215031608807641c1b11420001015829640715074000188 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 718129361 1250 718128111 718128121
    0xe010e010b040e07140c16090f110d180215030702070e010513090501181407051f2712051e0c0108090102070f0f060e0115170c0a03121b0b 61
    0x3c5c2100f801c1140c10510b9582400b00700451540340c09810803040d01c032482c0c03450301489038282c1d5104041c2400e4041c00c0030700c51305c2550142c0c50034038801da01c0c2d2106000d40340c51102ca181800b200803864503560190200c0011500c91005400075081961340070b005000740c86000400507000902d15040c1c5000603d06c1c50500700da1281c0030300820180d10101d415548592070250420814801032060314000c0b40c050301b4200e0910703c0e040c2005200c0c0c005910030b078500c1005122072000380c00c101040c0310a41c14002ca5011a41406940800403002c100c0c994404101000c100f0004050301c0200c1c0b58414012600740380112900425800383c100061000350b40882502001c071341c07088481c1604085072000046c6406101c1d11109020380e1410015078002000e4003894003004a0b40c03154420111035100200011310340811160380c10a414800c03280e4036400180d03014601030007030101c03210411008160b15801ca580c0d01d490304100c02c542034146c000c550751a203804603010001ca030381c00c00903500c006c03100c00550716 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 718130611 1250 718129361 718129367
    0x9090601060e011707210204030b011404020c07081c030902031203250f08010504140a0b040609020c0606181e18010e0703061a03031617040e010e010b040e07 69
    0xb08840c14100100c0502001071801d00311502e90041030141d80d40da80040c0071004e8030403404210420100d0444c8108420800705001d51102c41c192840c0c9413900304414003400000d40a401490510542801220070016074240001103038008503000311100c100480030a10180c1c100c40d4a80c1010b5003642000301c41e0707549201c141d8000c640c00050303031800c10000c1ca1011041c100c0243c07842d00000109504081c4000d41c5a00140101d0061404480601c20790595512030300c11102d010700300280c141c1c0c44400106260b640c60300140301030044010215100c1040c104680c2d92075109072080741c01441d41d001003180300c084c0b030b0b2080c41c400c03030280480f044001601d1103101060000201340d150381d568100f2115040001c20700402d076071345051070f0042c55020305504103c1c08581001c140d801c03a10403002000e010584000c0b080e96404024a00a41c101d4000e83c10f1011a80815103a041c03003102d000a00030070112a8512414140c440144886480da81c0321604103001d84281e02404111011240003d80c03442c2c4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 718131861 1250 718130611 718130627
    0x90f060a090e070c031707020a020d1e0b011a0a080c0706180b101e06080408070b0103230610090e070504060602010605010201050606041401050f0c03071a060909060106 74
    0xd440c81d16089465803010545072811050b10700f00000ba1301015a6014141e00408a00c030440541c660050f0700d003825100a9615407040000074007034441c185031a814800304569226089586a0503102400018508442e513808240034074040a10240f298400480054066402c00c684540321000151100040c450b00e58010040884044e600c80701000c441c4031002541e03400551007410242d8283c00c080101010111444d0803500303808070b0505d0f0360400040c0f030140076412074020b424040b019854508180300c55100716800a004115240000010017824250445a4407200c84825507426640d014003a2600e01c2500c0700d000c00351440300140309141203039208024440608003180c0122b83c0d00c90214065840543c4050050307551814100880c5d40c0a01607194005011507140f4505800c0131554141001111041410010301107520b0411b07030074290854a0b4441f5003011640c44903ca46001200b000c01502c150342401e507505c2c04109a0b08100c400c1d41e0207048850041c002e5a0b0905504a0f10f083c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 718133111 1250 718131861 718131877
    0x2e260c09061e130506040e0a110d030e10020a0c0803041d0a0f050930040e07120213030201121e050604090804090914060f0a02070309031209060311090f06 68
    0x41d032691200142e03a03903035803001c0d0b4031181d00e0301c0101e0340d0715203181000f0440d00d1006140307007a03800243e00d08000030700700245003442100c2150040688006810101d5010600c000c400740c100c05031880241c021900042c1440d101c506c10f003014403500d03440c2c2d0768143d124021031081e0b00301d00b503c2c003240c0240940807000d0181c0c40709240d0800501c150000414505488090722104c003a60400041d0040410300da400503001944001c01c2c0301d10500000002150038410f13445030212000d0400040b03070f901d912982a078058100000420b64a8041c04121501c549085110403030100e0b800c040070707096030b034514012603003000d00702c103240e030610f107a80b1244030090180200096801035480c0412400a02c0000141000e4807000c5c07400a00b995081c6003000800703447d0301814020b40d22a82c10001440c1c5010720065111054000158440c1500e00d000c1e2000340b2180c000400b40c100e10000b400c40d02c3d502900d028105d4900f55000c0c401c8049004c0482558410282d00030741110040480000e24103202d4000d000e84 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 718134361 1250 718133111 718133149
    0x5040e0411012a0516030b0a050703060e010306050a0f111603031806050907061404140d0605090102090a15090e0c090d03020d11152e260c0906 63
    0x1d58205604016903841c0400204402543c401481d040c40010401844040750000030b4402c001d0443d2500c1d154004010310a505c3c00e501c031000682e845101e0340244004098400402101d56101e10b8040007520707044031158182072500700b29134142251801070320702224803011007600d0a0300703081c04083c0c1a914540140c080c562500b041c008407411205169260f035010780c0c0000f6441c20034802d018100f00c00c0380e00c080d0401a000c0502c44070b411303404003200c00700c40e0b0359080200c404c4080c00100d1081d0036080302c083e00701450710081000040b0190002c22020900b11408446292907402e150300034080820101c0000d0503500c028400f00c1c0c2204a91504803a000340f01c00d0814401500060752500d000348110010f0300030b602c48901098200408513103003074401c0081e2102c00020001c039612010300a05e51407120002c413608600300c5c2c2c2000c542400c41c040c9040e501003200e4560312a5203050390544005944603103442401e800c548004500c07030644c03043c020502c103036a0300c403c81080f90340303180f0003024401 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 718135611 1250 718134361 718134377
    0xd0804150f0e070f08120406050f031005210d09060906030b040b060403080c0613150209210601050a050a0b040504020a0216060207030b1e220c2405040e041101 70
    0x10a40d0030070040c80242030315030001e031005061840307080c1440c1152186c04444d175014401446450f4200c001d4600b40c4039110b400a48941d2078445c00e9161034030030303488160492401c0b40201005c0e10095070070003091580808441301050020000c8420010034814800003c7e9031200c01d0207240e2080c0c00038100442d00074000705289040c0707400100d07140d100d644101e0380c1c001c0024009040b84024400d55900c00440c03142c804203031807640c440303940c0d00000e4205140000d500042901303559903115a001800d50141c0f000d150304502c00c035032a5548503000c0c05241c1c46450114800561442e041d03401809481100c2100381c202844c0805000c040d42080c40ba034810b5000c0e6002075003513400801d040382c00800701a40141015859420404143c61024088c12100c6100801d481c01c1700c000980c5098104004c01b11860700c4111409440700c07450840d580c004c182d411641d10001d083e0410383c100000310481100c196160205000064a46116511824245051840008000c0765905a0502520406051111b9 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 718136861 1250 718135611 718135631
    0x100c110909070506130905100602150c0d02070b0103110d02030a14070509070909051e1501050c0f0a0b1e01031506090e0a050c030c010c0803040606120b04050d0804150f 74
    0x1103681040e080c6061718082c44d1020011002e2a014441d0020764100c4038110076814030780001d440311550940c661b01d410101d4041840004a48100c52900075640c13400c40d10350030701d8130707256841c40c0d000c1c4401c0c1d4182c040401d1070030080c41c01a40b44550320b0303070080007007402240e00d544219041d21000e600f02c03414040c010f00000c00d03484220107984540140da43d00c0c0d05203410040c031142101d078040c2007480c5101c80541c680604100b04610340c9e40080814914020035002200122824071402c04909940d02540382c1051110400181a01540d8030507050300081e580ca0041d1030140c8901640402200c036a510010404142980920407034090317a0900800c0d8640c441b400101981c245030648072207a0710212000c018001c00740520340407148110080c0c0035110324071000910726609070401900b945170020105003000703100d6001e48000c0404881108205d003840c00c1803200c4071011182076845002e9160300f030b882140b0a001d4203104942c081c0143d841118801c420000900390f20141e100d103143e4a40d0040 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 718138111 1250 718136861 718136869
    0x4050a0204141605130308030907030503040b040810150e04080903160e07080702030915090301050403090e0f010302151b120c07091406240a080105100c1109090705 72
    0xe00c9000e06208214800e0070701c0b00103403000c0f950412141c420008140310000710522411000c0c0d003140e410900144d00d03a16010951818001d0701e070310040c042e110001700041c00301c8050016108441a1340c0c1070301c09000c01c01d000c04040e02c886001c8419070034007860061200841602c44140c101d4051a170043c105406c00d40400d103041415080701c801507403549010881c0a00888140354400b4407440d080d0030754107110b40c01035601c2c000c000310b2901c0f481c1030f41240c02c80d02420005403098071800a009210f14113060070007400f0000240501c0440302000000104a05020185030b8100d940c050310906441c1100c08040300c283e0041d403400e49020800384298082d18000b04441c10b103084640207000d41e01c685101c201c5140070b10b90782c4500030807420315a000d040340044203130312a803280707050764900448080340d0b014203485685640c401c100c040004c030754800b629601c042141e041e07842c03d030b4006003000c0c1c071042e0a0f41c2c0c410b80020700508607c80d904207c3c000e418910030300c43d08401d9440c12207a40d60f858000003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 718139361 1250 718138111 718138121
    0x6150723010617010e0d110a211b050d0302070312050a0507110c01080c1e0d0c02071202090619050409060b090a0e07120c2408100b090904050a0204 65
    0x548007a074507900284182030740500c21182e092100c00003000250941d041180d19a21400000f105101d500c0a00303209101051140c1454250301548940488048214100214820200c002d00140c8141080305481301a02100c600964020000300405030700d28004a000c0d60200f1422010811215802c06948609002d000d015683d10313000410030b45400c0c0d0703008207500c0c05001ca412155100300c8520f030090743c11018003904203111909040d90340115445910130f14003070719403c590840000034404843e16041d031103600cc152540d800c1ea03040350784e642000b8030035102c0307043c020394095041d40c0031078910b24000140400d40203200556403500350307440340007401325016510306540d1180c80304541c3c221031401c0b1003104d500c84040c400c101301f4084100340c10f81d590803040c0078040204042075801c00900840e480048020100440b80740d00d12600c9030081180c10b0000304441d00407415a0000c10603004000c02040241d501a00c012824901c4d03070350420802d1180500195002d0060846000250700d45000b5 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 718140611 1250 718139361 718139423
    0xa0b04090609051005102c040f1103071802070c050306010b130509040b04030c03020c03011d0d080609060f1302121f0308031518190c020105061507 65
    0x1c001034004090401c0c82c10302e40d09001c028904d92500301045403007121170780560150b4521001c2e00281032081110038800541103608624070b2240da004000410201d000c001e41210701c00c200c2d00300380c141c0807414035640f50141c1c0500c41d2803c000a07085000c00410747d01600260b4050441a007809640f04d02003410300f00700381c000010a81c00081c105400c40d141c1c142080041509441401d000c0c903060321000b40b0501d0141005040220038510700c810b05200300314040840310000c008112a100ba041490348920100c40003c00360b0040e4002401910700030303440203100b5003001e81440030350b03034507400ac100d48444c6050103180e01a119155051448441e031005d450029090741014499042201c0c0c0b40380745d400c3e00200a10302a40050092000811040940b0703003080242c00d41051f010410070004603503104010b4056960302e140b000300300d002d0034018240c034104080910f08020b41c44559000702e00340c2d0f0b011610076401460078010b4944a03084034000b00342c0c090043e503201c0d94005051894482c0c0d1110120 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 718141861 1250 718140611 718140623
    0x40f020d060506100c080a05090a270e0102090a051c080f07021c120302070f0b1e073e10020d051024021014040501050c030c040e0a0b0409 61
    0x200003c6080143d0f07900d05031903160502100021541d51650598030503529803001300600822030001c2c0b42c131801d0004c03020f403868507400e0440142c591498650040044184009903082404010400a061080310324151000d041d00c1c040c1e030300700424402c00001034140280c4501910000401190842001d800030042119800c7d9641c1c0085c010410001012005040e01c170410984442c001040b01e003c4542d108580c1c00d0160b115402405c04075410354050344050b1851000d0000c0013160002c1c4a214140130103540d100d4112a00c1d081802c81c0c00d00e01c19a52074284100b0300800ca004584070100c4801c0c0380d06111415544141900c82c1e00d820080c121040000f200e4000c900c100d240c1115000c3d080e8044008240f410f1074a15011003800380d140a56040000d118241309410505071080c04095903001c648401070060001c1c000b031507143c81400303c40540c4c10b0b520340f401081d551900b11044078020000c184029040c40e00b0403030003500030303032003e0301c17200800c0d65501c5204890740f41d90241284030380c0074407 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 718143111 1250 718141861 718141871
    0x90c050f010201150911040e191b050f0903070906060c0c0801050c09060a0e19030506090d0e2107090903020c10120b0a031a09240a05040f020d06 64
    0x828004800010206103040d6418007090401044816000c80c00311880c5c0700020800200540100c0340501c02c0d5008600d00d091590100310480045081e0844001c2d07450408101d054a101702d81082c5401400503a000100700b000400b040c030036014090b2543c1d6100409032042d480d40c8800c078000711075155200c03002050030088800c05205407400d60b0f50003002e4550090049103050004020340c0d00c290700e0142d02c20280413a04d000d40512400ba4400c107107030003070300d840035041d641b40604400c10124481294903200381c2c0f0000b04c1d050b40221340d042d071500703880e281d41c10484040c9003040040a6042c114420500104c410060040340800c00f24004003490b0100040d800340d1420000d0910980303400160007003024403418a000c583c0540c107001240e1011100203403050060300000c00400c0c07160300240c50501400040b400e400010200e05000c6c1644c5000c43c0ca442c607200c51140150109580101c503c0e200000008038807240350341080354028401c2c00d0113204019140d0000706401400003040e18095650 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 718144361 1250 718143111 718143119
    0x1020d03020406080f1e07020304080c010e061e07050105040b04022b02060a03180c051f0c06090f0506180601060207050a15030617030a090e2403030d090c 68
    0x5004202214585103000c0d803419041680140940320302030040300d6800d03a043c0000e030720180118030004494560194840d0b07582051400256170742c010b406048210300400b2180700466005480c034199a03072001d02554281011300008203e090000c1d600c19210b50010048100064000e00c280c2d44210312401542d00071303080c5401070080108642c0540c1d0f1141c51200981c4080003c402007506106504654250352141d4681c03003240a03040640303081d00012284224141003059140c401c0c0c050750b101355483d00c4062070064510b400c3c07034020558180800e00e4058480085a02034022040c114001c1992030f030750413842e5941510f805012640c11408106241e0041816441070056500408052008280c2c00f4141000039109050601c07c480301c004a0840040d41140682c00690050890001c0c0d080c0041311000e915881c2c0e4448411400051191000441c2c00d90703480944501445200c1c400040e0b00c8003c1d008407413021851082c0d203515200a00030081e8800c0d80780030304140c0b2886078003000c21061070 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 718145611 1250 718144361 718144363
    0x2030a120c1b0608161803050c0915091311090a0e01060b0c0c041515020303191e050a0f060f09061d040323030406022a1b010908060103050c0102 64
    0x2c00b03940c44a024103550081044aa000b00902d400c03400c0326041100c56410140241c80003007070912a03162041802c100002880008601421040e00036140740901d40d461403080511424034035280c990017081c080c0840c07041202180d502c80384520801042c505000d80300b0003c0c1008400b2501002c0168461011101050342801114000e28005100e14140314507500c1e656114250801a14011543c0300d00110b820ba48008025000306030785050b20000024802c0b00070f49940c0100d60081da0225124426001c040043c4108400c0d1a2848400300807080f0502d00b4202815010b001c01c41034548404000c100c1d48aa4898400208004a8a640002c1c5400d01520540e512a4070003100100c2c003800801011081903000e070340c040e03410300e440245000940c5060803070740011806250040c002000f004108205030340103110541c80e4480414000101500325101c5142c810300701d8060360400e02c6000c1c070340d00c0110b01d03400b8a98014180100c4150b216400d282c80c01c0400d900507509540010f42119495070 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 718146861 1250 718145611 718145633
    0x40e01050606030a0b03031201060c0201021b100c031107080f0f0303060d020607021c1208420d0809010f0525030309020303121005101b02030a120c 65
    0x11100000c0c41186404030000300a400000c1c003c0742440e4440d992040945d03070510403288400d060004103030003541c5550009118403a03015089003d4425144032902043c401d205c40b44203508000c103410300b071041d44801203622a209200890501040001442580d002400b00304041c0c00d40d0402032810201040d4000d20704080c1c404101966001001404055254018140a807507019500c0b41d40c0c030412403000c6410b610340100307803504118500401008002c00c1d10101c07800c02d450340d0341e080745030345030718140681d03200d41d004c000400585040602e5249241c180da145408042c0310002e640321402c8070011a0860000003412203103501d000072544032640c1c0100a6113400c81c0d0030710702241010212980748814807028400c0340001c4403102c10301c004052081c0c100d50005d0303034060305482d280e101c00403852264a40c03e90701000c462109031008a8241404644000144e1322544c82c0c03c180401d5640340d000394080468142d8040c0141c10152011603c1050403260040003aa1003a581c3e8015040c01502d100b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 718148111 1250 718146861 718146881
    0x4080a021c29010b0424020f07030807120e010203090f04110a111006080709021e04030f030906020f03121003051c030605100c02062206030e0c062d0d140604 69
    0x7982844244486e00c04130000300c10b102103488041c0703185800303e4410fa141000032032040c856817056540204c1084046400750403400d10030b8200e00151103190206486407c1030740391490044c2d2040c080c020044c075004481c000c284101510003e010b1481d420b1100056120040c1c4901040e40e00384c07034080542c5d003088400e42d09a07411100300b0445040946241e290640d51096001d20b5401150b288880a503981c04940c818500c140311598542d81c03071038581d02c85500c03d40f040d40403407003203035002030306130300119481036071201c2000a14945210441c1140e0031100240010000031901c117001300006008001d4500481e0540b1800a444841e40100030256801600145d00550301205039442c02600700c0344000d00b4990445510791286150981c0304120040040c00800c00010150700045d501e400d07500080c480f80908007074400c450011745c207112003480307a6100f0459980940702200810384007401c0070307100e428001c1c990760300e803000360301e80300007030310400d203030484512000c0001e04c481031400744a080c0d050 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 718149361 1250 718148111 718148129
    0x20a0302131203050f0706110a0f080a1e020703050d150e100305030a08090a12110c0a08060c0306030f01020c0615100e01050f0708030a0b1504080a021c2901 69
    0x180b907440e5801400c0f40102c0c614030001c0b04d00800c4020400c201030300301e500e40e0b00352500710f580c0707401c45650010042003490b4010790101d1520808107680803000d000e81c40e403040002074828444c00380170100b04029440301c0c5c0d0a40c00c014045c48000608203540c02a20301c1c0102d01e17401c07030b960345080001c84201d00101505000c5412441e04041001903004015035909011600f40403d4603580e40901504004030210001c10b01048603983c54500f94110030038000d034003420011501301009080c01d124001005001c0d204455004500003120204440f0040d50700460260079100725900ca100308600766040840825065081501044840c403000000c07845100380848034a1044240c2e002c0c098200b04078140400d0421400181c22808003c3c070404441c100e55000e0021996454802c070030320010521a041039109898204504541c01d041030b080e00c01340e50703e040290103070401590030015002c0103942403000c21000708000b000490190321000040b0303990b8500d240b05e03204d540403031052619816003200c044 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 718150611 1250 718149361 718149389
    0x160b0415020d08060f0a1503050a0e03040b0d05040201030623030105071e03050c13080c040507170a0b0d211202160b04150c0c111e091801020a030213 66
    0xd010b51003c0b1054110300305403240e01d2400c8458010513070780c0c070158000006151450424100302507066204038442e47c0c00f5a820002c0c440c000007469240d03c80ca20a01444480902c036074030502140b0fa00080d00148141000141c0c95038031403020340d0444546110000140700350050892a081c20700585610080d60310b088001131200d4039060031f80814814282c404c056841000451403924401141d0300050f5404050b0145907036800040d5076206444113031070180d41803a000c28482402584c0d011201c10401c140210f0643e151842c0340c00900d03400f01c000d5400f00c4000c610700d0214a0800c0d03c24210620101c0d040180042800040c01600c000c2a1840c2c0c070b00d104201c00084145504051708040d60f01c6510000d403926103040081c2c000c1708004415281070f1030130780e01169182c2c01c000c041c0490f52140703c141c0d0581d4604000c104421000f1515040c4c038640700c5410440a140984070507a01c9130001c0b2280e950700d000009182c2c00c9812801400340405e40c00a20752108040c4140d06600901e00b032000040 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 718151861 1250 718150611 718150633
    0xc0c0b04060c060902010c0212160b0405060f0c0a1703070f081b22060816030509060a0e0a05060118060909020d030c03021509072d05010f02160b041502 67
    0x90b808000070103854656560503290440e84a80303080c4a14176001481005201d40c400c0c000c60310f868920610001c0360070002000941901c40c1e405035004c4650080c185400c080b142181742207198001601d0040500030411080d0000d1003070506e0454601c030819049841c0c1c50003000190481c0c8100744048213110141c4200f02c2404205000230007529002d050300d5440d071031007901004041c0d12030204020130300002d05002c42d1140d0700010b6240300300303203c604081000b0200782042d0f04a620a07100c10145802101c0060104041038000b0665070401c0800c450051660391902c078100f010a8001c400700d00b181c8491905198198006c4501910940e24104500c0911303600140150302001001010721036010480d10a060007801040c400d034600e09494511813030b24800f640c0c1c56101c6030148407400e03100b1004840011100b8000c618ac00103204183d09152070505005441100445d09818118841d082c0c00c00e04468405240f0b10040c82d601008588039800e1101019102c040d1001010840d070003051415 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 718153111 1250 718151861 718151867
    0xd170f1305032a03030720030105130807030f201507090609121b0b0403051203151504150c150e0a080c0304090606051201050a150302130509070c0c0b0406 68
    0xf0700c0a600003010151034080424154002c2980291001606114060088842501040384a00c0c00c80c02000725582c1c0501d524001c0039000800f41c9150001c0c022040083e0203100045883e05407410500c0080001d040d100c00d0750311b0000f00d00d0000c1e0300b0500c0702e021014150081c882e0001701500f86201e1042c01c1403401001ca000601ca501c04502681c54000c0600007900c440c8500e011315807181c0f030712603512040c1084465126200c02c40b0b141c85001c00b41207698010b041968060b400391401c0c0d0410b220b0f40b40800107460800215090b800c4000c00c00010519210064216034106036124180d4005250030400b1540ca20940308024140c1005440c040d06800801d400c110550b000d8406501c03260700d54001c034990b005580110b0401480d194012450a8111014003001782c03920041942c0b076070700d078014400c00d4610b510800d0030b1010043e0109011a000750080c01c00b41a0342d80e6004119a40d4900042c40001d060321501d0100b00c80410042c01c0c032800c42c140d00090003140d0141c1d4a0145409402 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 718154361 1250 718153111 718153153
    0xf0305041701020712020c010f1b02190e0606040b09040b01030b1c1403070b01050d06060902040f03140718020d0b19080d0201021c09050a020405010905060415140d170f130503 77
    0x56020064900d18001d40107400ac548020000e4020b0a03141040801400d81c481d080458003903000b13002d03e00c00010f98603141c9079040343c09540364041c001d400c03e0700c02400d1001404d04002e080d4140f58480300d29007410341f00c800780d43c00c040a00d080c0300d05940340c09080050000039030201102490700204519000f083c1c5500055044441c282e4800d040006039041c9007008054079005101d00600010b000111603984220a1080c1c0f03000f0131f04d0390000c0d00c4903000300d03030703110110b2250300c1e107500680102110500c00f40d80548010303100b02001080c4841d0b41c00010b81c1c0000b0540811540c1c0b401c04409100c880c004102c0115134942c01e000842c58270110b900f142c4020204150140003c03900e80c44031400f0030505105032350405501410900181d6141c8602a001d0b007001c5451902503490101002022002c071090002141c840860800300d0b036010030107011030a5450300701900c44002c1800d41e10314648001000b030200d80300844072036443d0210160300c9095200e031544500d2203940072421114040c040c000f21 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 718155611 1250 718154361 718154387
    0xa14030c011404030506010e060a05041503080a140705060702011b08060d2907030b0d020604035604050309042f1305011b0f0305041701020712020c01 66
    0x4100b088924164815429102ea500010024001c44000046c071220408000740118400c8600030152501e440601c811203001104007100411100d000300003250900c002002d1951170303803a19002c411040b004040c1c4070340c004074089500d07501c1202003000e0ac59084c070906980a0400103049000010044c0042c44888040c20302c51044240d40e40c3c4070100703d5244030600304424ad440107000041090301c0d6216000008550700300c080307402c0c0030b4445010300d000c0710100b1450740c1c02400d2a00302411034a840000300403510001c00c0c0c0f204242e40c003e00c0f2404c8800d00b6004503a000101e0381c001006500c840c01c40d450b45100c81c0e043c1c69100b10074000091804025607450741f205490000307408941481425040e481d0740340340e2000756150080c601000c003c0000601402401c40709074110b84e50b0f110011103410085c105600030f4070b0600707242500014141c113180555a4080e1400500300398441c071034500a42d042000402281c2c0d0700040c2442081101c0300b911140d000e050010b08200140300002038901c0b594858 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 718156861 1250 718155611 718155617
    0xf050306070824221505091b1c020301032301020a090608060f041503020102010e0303160507030210060f032003100e0111030a0203270a0b130b09030301050a14030c01 73
    0x509441c5949a491040c020300d00e10004c000c1d80b5400e9404001e00a01841d41c900300103220310038010030141030009549005001400d144241c03000c0342d0901c004140c2048603042c5c4608410710412201100320b0010b50701850081c0c0d60548011b81807200280c05001c0000c0e50280380e4014402e5401c0a900807040b98112589270614010710b999403030016028407020001103500c07030703d440b102001118a003c08201964070030b070000c021a8020b40103043e900e00044901000d03040b2080070002a091080c0701404d1064403e0040307522004803402c0410a40701c841d00001103444009808006212100380d02d04d1414445031410880102c0c1800480d450b000c040e0514140641c48905524445409500c420040134050326042d4487c106401c030880a54400d8541000c0000c04940c1c1440fa004803610540350341e04d10400405010843d69548482003000510a001c1003001e100000d01181310381040c41e1082d0202c0018503629818107003001207085a41c2c01c550510360754280741502030b480001e401208180c0900b = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 718158111 1250 718156861 718156921
    0x10609091a100e0411030a2403020d05030d06060c03090617180705060304060c02060601110307031d090a140a0605091b07020d0f0203011d15180102040f0503060708 72
    0x2c40b0a41d01076001480840d00140b03010b001a602c1c100c0303400554059040d4500034403a00700c00812100102c5072408203242081310a071802c10040c50507400090780544110140c9042c1882030342e80d0300890780c481d0320050100e81c00398101810154002c00f0030025001d2414a94000700d8140042c0541d540001e00141040000180c0303594031080410418004001c0180020340d6481d09242c41005448e0b41d0f15200c0242c030508000c51a02d40c024a4019000342103900150306102441d2012030b02d030484100440c0100e40c04560001154944c03074410341c880d840d842c0c070115061900044c5950303442d40040045010500d450018041580c60b200c1e1980c12840b0785141604c0c801540600c04da0030b104e0307408029481061520210f0070090380c1101c030002d50f0b0084000700020300c010030b50301c4403c2001400040c0b154000702c1d4400001300350f000030283c2203058140184801b2043c1304505089034481d4000c1105030f100903508010b2843c04100d42503012215140049403410907005c07200d010403804a610385407180c80 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 718159361 1250 718158111 718158139
    0x105040b031f12062309120f040905070c0c090b0310271a010906050d02010f090503120c0c0d08040509070507020a261513051e06010609091a 62
    0x30b296a001030a500c0c0a005030058052810710000d0040c495155011516902c01d014081400c0d45814030444510024141c04a403d004180d4241d200365044001182c00744408540062540314031403103442503883c1c0346180792003824205d44c072102d241c0c40840c040d401c0141d448016100412031100d00c1065440100d048140c114100d595040d8044d600302c00441c00c0d00d0b00300d0602c202c0d0441c01e02180602e406169440e40c0352036001040c0c4400d4090a03400110744c1110900551040b10f040c690341d6101d24220300c0c4191164002410b100c10550100e40d41c0b5400300ba00407540b14103203e105407200b8200d0f01080910060b6a488801d8016846114446d041381400a0461402801103a00c210b50042030b40300c00c261242042510450b14030042d0390303000c2c40070b004600c01100004407490001045008929141e0b6a46100d47d820840072004407014042c0440310f2450748220000e09002407d410040c1c40f4960608000803c0d0507101e0f801042d50908012440b01121070400240c414002c060341d2100d05000d00c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 718160611 1250 718159361 718159411
    0x52a04030512190c0f29010303081806010e010b0307110106031506121505060609180a1b05030115110f070303021902031207050a0b04030207140105040b03 68
    0x916803014003507002c0c03014200e942072242001072554060040d5907000c0258641c00c2121891191600100903c0340d21001c4c50100b031269a034921014000f05e0421441400c0c09007120314520280d0086003c10044410f00034a0052044c1100600c42d00b03034014441e0390b15001c98003c1c8904180305407014140e0000100c2d41491062902e41444a00c00000f84843c0d40e507840c10890140c0381c070010b2900545000b101095a154907410380a401e5008040000c0c21200121078070300400d40504502d520030000c100242441d2038458031419450601c206a06242c9403000d00d80043d03480540c03090941031a80c0c041c2069154000d400d40381034580d0114000c0d200c85055030b0030740e0b21202c0d080c5881090f07c6922003180d021140040c001c82520321960950301c00000c4103000f0460811240c0c0d0095042d0041502c040c050828480500340d002c1c001c108462404000f030702c030f01780c815406403801d0b00160000b40c42406410300201d0088070415080c80d0261800b03150824149072404080e189100d42e110074050380c01c482d18 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 718161861 1250 718160611 718160617
    0x1513050c150a022419061e0f080303060d150b06030903070c090507272105061e01120201090f090c0e0a050114030a02070b010e040213052a 61
    0x100140c907071081e80d0008028079486802c45a21200144126221000c800349002c0103007003094000801051903031665200d258504151100900c2c1113a9101e9000804040300f24011040140d800c3e03d13521250300700140700d22140d845410218159204209004842e101c100211040581000407280c14000140841014003105607581b540000c0220900849142c040014805a0b10036a2060540380c0e03101e1401d000d0700d40880e0f94001007522040c1d0110384842340040e0301d031903800c125448210503445214040b021900c011200100a10b03501e44c4500f0031100300b10640d00002d08002000c51080b0312050a80546014042c00c600c00c4100d080c48030459000d05a110003400007800480c0082c3d032152541c01c010b00d09421704000080042d4030801c00707402e02c40c0b40f4405440301030303590082100c0901c1d11682c49a202030820810a60308020504c041a808100a03019103204e51100c0314604180c010070065074071902d0b62100d0a45030400340080c44000c000f04c10051201d0001e00d40700c0401038240c210170780c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 718163111 1250 718161861 718161883
    0xb0a1206060b0f25020303220801020d270f020d060216060e1213290f03010e0a0203060f0f0d0b1312020a0804050d020f030d0f11151305 60
    0x160109660091110400250801282c03034500c110440e400808441d5003a10940c0019406410400c8450358102d0300c18504503488010820401e0202d40d2a5110ad08903403141d083c03440c025603104c02000d0076000f0b082968265000d10440808142032a40f2145510620404024495850294038400704800c076019a040280c0461884254000170b013401030140c0310244459005001d824268143d4003130f4041500c030f460b40b201d81d282100a043c0900c00790241c0401030000c281c1c0310b610059000b1110154010207120141d40c8805440b5450101c8600021030041d0080b0b14150042c001c10a19850340296117103000c808980a0034040071410101b200d001030b80402a01c0c00c0403100030001500c00c00300d400c0d061a4443e8254100100c035200080b80c490a0b9030304014200c1004110820a5280048410f40080e00040041705100e1141000900c0c220313403c60840b010810410a0a10141e0801680f07000081042e0251081550002c2c6030260302c2002490741e500c4902c1c5054200c140f0904018940404c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 718164361 1250 718163111 718163129
    0x60106143001080607021207080705120a0302041a0304030c12030209040f0504050d050306310f1505060f0708130305070b0301140103090b161110021c0b0a120606 71
    0x300740c41000d41000c22109000e82e400398031481e004a80c0961001071420f2024010704011414131300301c3d070380c2c2c1c00440c0e00c22001666148142c4814448000b81d0380001c1043c04566100181e94a00c0d02501c1010200007903550040c0712803d00401000c2508180c95401990b40000b40700451440130750242c009000700030b081d58000c0d1070540003250f031002c554445030090340500100c076800602108100d070b0520084030f030142c00000002101d46400c030390161b01401c4911800250300700c4c0032800600802c0b2080c220000c0300746034480702c02014156900341a01e02034042980c46900c1c046107014000c0307403489502001004d01200003000b12524141c034414001660303014090b9140710341d44042ea251a42c00138080d0702400410010395094135806232040c52012a0300c005110800e176900780c0203c40101500401109011030641800351b11081401044d81e10007400c2001a2911868510502d448c07090740b812100740740c0780451100b615076440c03070280120b440250103000d41444070716041014001e1fa034800c0d056 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 718165467 1106 718164361 718164427
    0xf0f06090e0622090803071205091c05130f0801021e040806070f0c02040f0c0f0206010b09041518020301051810140103140c040e0906010614 62
    0x80f2800c1944001101130654490049980c400c039170701d90005022451031010360025110f00c9420500100082c140074002da0880c49001e0244407810050205c01300d0788404403000d05080a02400802c0c21440d0004d0307543c06094041d410882000d851114030380701c401403110721701007641c0441d0341140003032070b9030b48903036a045c1c680300c0c106424002004024800400075071194001c010050002c800005000161680c004124045900740c92003190003e00c010003461007074105550b111101140d0003e031441d40c19172641200e01a641c007640c119100d5090a10b500c0500d0790103941240d80a0301c0ea0009145d190790640320718003084030940c10322010a54140050340403d1044807a291042c14005481c64022000800412003115080d80001001030203210716001030820070340202d907480c004d06095040039005448a080d0194602c10031001244003c0900b0b40840ca259083c04203451580c2 = true := by decide +kernel

theorem cover : BRFrame.Cov 717985611 718165467 := by
  have h0 := BRFrame.cov_init 717985611
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717985611 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 717985611 ≤ n) (h2 : n < 718165467) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
