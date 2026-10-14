-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3671
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:20:43.970108+00:00
-- url     : https://prove2.me/submissions/a9608e27-581d-4c50-8508-82feb317a26d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 660071942 ≤ n < 660251798 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 660073192 1250 660071942 660071953
    0xe0f0604050403120923070b040b0a23040f1d010303050c150a02120906010312030b011116030c0906031e020f0d050a030e0609030307030305040213090302031e040602 73
    0x3800010440140141c04000d08001d038001c41c40c010b4010020160b003e4084d449801c01440840080c800d030034049400c6603400010100b2142c903855080d14106e5881225042c2c552a02c51300541e0800012510511500c541603201031300b122100c0f02074800e84a124408200407901d40c40e203000080c0184207041200c41c1208010000684103500030b00003801704400b41c40b1401d14089255100090554052101680101b002204607d00544055008849000030040c9500d1034a80d645001c100c40440d40030540c0365000c0042603401420b00494410701d0030121194001404c542c440140340c640000c03a00b003810400c00180c522100e0203100d055941105900700c822001d4807403902101d003458800c070b0b0002004072012a0f41c0d6640800000c2880c0540040c1c84440154030f0010700450305800b000c3e00c25402031045141030b44000082e229601e500d07050000380358035240000742c0e124014400907080d59003044410010907034080050548409015203801c289045600000c40f1030045018560041c0d101 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 660074442 1250 660073192 660073201
    0x2101060c1b0324231509010b12040c0b040801050a14090c21010c0207080f0303040803011401020a02150a140f070b07120204030809010e0f0303030115110a06090302070e0f 75
    0x300f200d99021440300e00c0000807002c100620407009018840a0320301800c42200800146800a801015032004111340c030301c42c550b040140901d418040c10b4060404030482100203405c000c02c41d034102000d0940b040740680c40e1590ba00300580a00001c9485d0b0014509048500e04400002103002e8000d00f9420042d2409460311300601000600f091081620301c1542a081210754600f84a0303050104a01c2d8003901c40b00e030400100c14030b0035000c0c05500c10141e104008100208400c182039a05442461011059106030400100e16004200c40301943c41001089440e0000e0b00e40d40082480c01c0311501c440c2a601211201c030b00035401219286481c21004001c0c080009860003190b940c800c6090a00c036034041005000d103000c82e0041d800444480400107182101d40d038000c1b01c014280101103448901d518111000b190702d034001881a1120410542c560280c1c5a015188a540344103d00d411141d000e10581072401c040d1810702e40c1a4054003690001240c80016401c000b849100090310000701502c5 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 660075692 1250 660074442 660074483
    0x807030e07050a0b0717161707050d03240305190f1403070b0a020307020d1b0609060c0306120b060d030c0b071106060a0e04082101060c1b03 62
    0x840361100c0c5203015190700401c03655100c1e036082000e404000d603010b48031001440d00c2460141008506408440e0912502c110004003e0503010345a40c08010102449000619403d05020391240200355000c1c0d82403424600b94542d002d03207840d950503d031041540c2410003111a440425000140c9660801040030782c10040070603c00000c24841c0c000c51038440603680fa1a44d91210300d00050206410001d05902445030b81103078140c110400d100c0841c6103040003940031356505400b1441806001e40300e45100d41c80e100090301c0d4010350390440b20030301c134401325494450b000b014110310030400b1a203040c0000c98050b000c0b03003205001d150b215284400ca80c42c2c110400c500000384080403402c00500280c0400094170f281e1685025030043d8845441e580b948228160805100a24660082c1c900c1c400810805490560a070303081a002000c03260307102000c245540f0160049550714000780c0d110400001c03015400500b03000b546006640042b00081a007000791041c0e2424800603042d01c0083c1d068404190 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 660076942 1250 660075692 660075701
    0x8030c0d0e19030b041415090c0111060604050a0e0111120106020c010516020f040c050310140a090f0f020f0309060c0909040303020d0f0e010c02100c0f14040e2e0303080703 76
    0x82c014000180600c4016006d1461b0615036481484851044000e00040403000c200c2284a40400d081046240121416566458200402640c8038039140c2c00800c1450780307540d201c2489005600001d10104075482900780c441d078014811600085095400000c05a10100e0040e47e8110140c1d106441c010b90a035502080110700e1078140da01010704445028295a40e02c00c04040200c59101c06480b49802c16260f040b182640d130284484500381c0c3d01c10640740e5075418807401510508100013500000180c200c100804001d8041706089100055405000d540072000e144902001001c4507515034802c8041c0d0028000c001590b5000803103500440d0000c1d0194002d0044c0502400300002c21800c034a50010070b86209460198560355545001079089905100c2c00f22001c216405c18031000c6410400200703034071380d10a00c00080018540182081c3c1ca002011280100350b0f1428040650034042408070030702d40004c4001e82c4095407140d12282e1b070107000e801c09040b40d4043c0c070781d035845548040c1c06034040d0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 660078192 1250 660076942 660076951
    0x2a0908151609050303070b06031c2703020a082a0616060b1518060306030303161e2115060e2409010f05070c1e08030c0d0e19030b 57
    0x1102010b004503a64404001902e6400e00450b00307800542001c1040c14108100504800300302920700503a8005203400400000344503c1400c126068030040403003650200390141c00007075000169500000300f60381c0000b005c0102d0158504100c0300b600c1183d4480741784103091040e4a400c4401848074041c02c940741440c460b40b107801603e010400580385800550f604415107103421284c00e000c141d00b041d0b0b032102c500280f8020015100180b5508107100020342e64040240302d00702c0030140503030401c0c443e4841d80d959210880c02d00300c011412030742072202030070349031000c40d41300307040d002003484000011b4170340c00341050030003070003c110303542c281050401c036004500c4005681c1c000a5076981d4404101180e070b80c85a80b1003003200c3d8a40c41d825800d000514000091039940708000f070500201003c520b083c6a994101c070b045403200d0800728040b8190055640166201000d01e02010560741c4c80c180d40418800700d007500d282e5425107419159000c210703001c01e0b084201c0f8001e4072082814800240078004043c0c20 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 660079442 1250 660078192 660078197
    0x61e070302131e06080702070509060d0c0e09030a080c0a12111b0c090703140c1e0d052703040612090b0c0d05130209070c03032a09081516 61
    0x100358980c00039020041c1c14164880d911030030f481d010402c542d801010b45410030310510103003e070f20f4070302000540407030700c00f4240f648100c52403610041040f8068003034a00034908802103041714504101c8454503074100b050000041020395001170142225002219800c403503c1d1102a195551100024018400304d2044021050200107c01d54007c6108c080c20a1601d054018100d65005409100703402801904440c11b06081050070046a03107400030301a840140300c08115110181000711030610804c0c4448002e0040c000030740800344d809182c0029102e010126200c212040c100c51042001c110f448901000300d800901003844034911822405010030041600843d840440c0d4483e400c0e4290b0564040488080000718410304900340c1c014154041144c8606407908100ea07004111996402081e800411515880d990205130281e44035102d489010042c02003000c0e074004c1142074291404c1030b85004101000d0001415200020f102d030380080325003107211225100c00081e0050aa42502d48105 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 660080692 1250 660079442 660079477
    0x309020a0b031003030201060801020c03071e080301180e0607020d0e130204090b0907050f091302130627050a050d03050c0f0a060f090201080601140903010603060e061e070302 77
    0x740109031a001e503010342107001c40384198070b1541c82c020b8215045513000521903401441400308600d03010040d201a2600420070107102c01350381403a14500980300600404285000c8000303c2c20000030388041e8461000180c042042600d015006642c45d41d040f5841c00050b0f1240e00d080710365910807403801c0e210720005003401c4480400c42c0c030750400b640c00a4000002090303443c0b042121524103040069004051804c0175072901e401403150301554411900b255004a01511507008485540c2d41244c07611106c003540e030909291107135001014901c0303540350a0a004030b1302d0403081402ca0106056000ca40e8002e148101c3d861406c1c003845950380d807040d000e40601806014102c14808188a0050350710031550150a50340b40c50300d0003034111810602c2c5410510724000590b40182d030440640350b00900c0901b000304074101034485108003480703152800340c0c165003014000801c010064011035044d43d0030074162501d076510369041c44c0081164240c0c0c0841c1d05846808a05007a000768010701429403511600d84 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 660081942 1250 660080692 660080699
    0x20a170913020309060a15031a101206090c050105090a05040e0c030604030e030709050c180301060503030c0c18060604091e05130c080f0a061802030a03050c0d050405100309020a 78
    0x2822600100c0d03003103404c0e420500400015a40b184511002255000191521035045403200300100d1b441039000449041c06074045591000ca0b10f1003c0c0c020602c50301e903800c0030496031070828041e001416048881144140c80490b007507000380144c0d1030851001c0c081010035071030081000003030301e0000c0c800c90890081d042c40480035201486220b104174000e460301c040c850348a81c01d141c64a2860380c00700726100e2421080c001c10070a088200e90741d100200a042800d0185540002c0c014440c0340c0c09542c2c94071001400301400c0c1808039424042a4044602401c00d010b040d500340034605045070080da00410400c0144078940307081d801403664a51b03d10b18803103800c41218106040b12005d03916241c44007542801041000409040c030009820110b000e0408044502400c543e14280c003600141000e0305c03408102e1354080c0040201149a03001400c80c1c80000c902c0c1809065903021550541c621300403000c40c1c0031b2041c0501d049404481018155641d00c81b020a800c0340140030724081243d200c0103040000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 660083192 1250 660081942 660081979
    0x80415020705031918090903120614010e040b03070b03040c050603040f020f030a050c0f150f03011508040b0406020f0d090b19060e040201180f060e0907020a1709 71
    0x10100a8482d0005680e200d4111540140010522058004110600c1884218443c2580300102200c05022011031142101e1805480d0714510320302100b907042ca056000940e4001416182c1160082030701c4001207011504180419510120a407a4141d40195410410803080310b00440d8058020301c0c4d0078401e543c4610000e009603105071419030304081001c03000000d616000e903c504001c44110000e10098500740c0e075103a118030283c8034680c1b040790801000911074483c201251140c0d800800c1241c2d89400b0596107002c03a800038003d0740702840401c81a101c40318016504140550b4000d00c0780c680035551035890070040d51006450314001282800310b000b50050720700030708410b244209100802c0d460981280380c0d90f20102041d10649504104c0c00304604c0e00b04210458000f90280f82207110860914440c03108114243d01c80384114071944000500b003580802550304100003103d240c040364450640c100e81d6106003400107409029440c1e4074844070000342d8002c04041001800324241502c0c4103410 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 660084442 1250 660083192 660083197
    0xa080d020a021309050606101404120c0503240604060b0a0f1d090103060509010e1e01060603060b09120c040f090b10030b040b04170304080a0e0a0b070308041502 71
    0x19600541e0101c9007400840c50001400306a60b1a285000c210b0580d4580310709a0700e08000e8000390090b10000d000486a83c40350f09203907881c02c070f14030078030795215035030004403a015100c1303201a51090150b19021410b40303004581e40171103110548111010100042022800c0c0d01c0140010781c0c002d541c3c038400503030800541c0140c4041c02d250740701c4030b203401080c05d80602200f0083c06803b1000f0504da0140843c1e5962000b0241500e0f000300000078580d80f0800c1d00c900400d403051010b22207103e04083c0908102c02001e0041020b111b4000a1002540d6480103a00355a0140604a6040000d00c80111141040101c06400004ca0b804a40c00c8007503603070103c1c0c1101c88514081a01c961031320107100c140441c0c0c0814907042080c500341041d0300c501e582c550204c45000944000c0c482d04c41e14010500340306d520f8441c50005c3c0d200213502c941d24107140c60f1485460f8800d00004000c1540305000094500d0075946450490780c03e40a40c82ca052800da40840f131004005104503000302213080d103180d4201c2c10303102 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 660085692 1250 660084442 660084463
    0xa0f170f07020f030c0a031b08190e010807140a0c06021611060703051213060c050d05090109031e120204091401300809030105190b0102030909150a08 66
    0x4621200e050142000f41051080c400a43c95076100b0052484503080000b40f04080c01d4140c40c201c0300300e0886410030380c3c2103051864041c01180003ca20b840f041d0144074640110f600c000d44501101040c0e0703800640798a40c00326071071404221060850580701c00c0d100c0003003014008030b203441034602410790340da24105d07041341d00da454182c1d521240c1c12040001896241100705800c540c4103041a449981c020410320031821520140301d4650f0115501c00c07600004806100d80c00242071080302a048030081c800c1c0c100e010395100b03007801c25012481503075042c40f80003e0580c16550f000c202109039441c40e24501c4c4000c0f00c90f0200410750244416070001341c4040c1c00907090503507011441c50000c1c42107807900001a00500c40056188400c0440440c0010801c00381c0003860078000032003940c6080c240054003400f44900e41550800e020482019041d00b030014040e0040681041003c1d070000c01280d40e40101050940c100402502254884da000f00f00c4901c00d40000b001002c280d40c89030710440c280600500b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 660086942 1250 660085692 660085711
    0x9040510060e220c02070f0902030406060b0304170a05070203162606130f020405100503072309280e1b010e1e06070b060405070807050a0f17 62
    0x1042401041d900008001c0b0114080714034943c56503071640310910503240158001071850351110000030303060003803152000070f041d4200b0b000f281c96518a580006036100f02c1d01140d0903454071001091b0304440300b050fa030080b5006102c2480311401c031080d04603198002c0c5040418803805114000060390200010100001c1c10321401180910345030390006a880c21203074036031040d0038420300030b50983c0c400102550701c60340741015012062468141200340265810b0081e4001d81400b04101d50038541d03041c20300490320164101c410a640d150300318550358400303903496440214022250480c230307d0b11214240e0040c110308181750440030107207140c2c440f803503050f0800e60700b084d01c0302d5024207030303020901c8034403451004000e06401d0103580a00003440c0c9400302004e14426401903d402c5000d920910040c41c43c10400f4040c81c3d42c40d02c480c01c100000c0782c0101c0b0418815410100058484c42c0301b440824003403100d80d141e0707d0420140300000d88211000f034203014100480c2580391541e54940e521098003560558 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 660088192 1250 660086942 660086971
    0x90a0906031101050705150703060308160c06020105090718021303050d0f090506040b0d1b020a020f0301022506020906181c030906030b120319090e1509060105090405 73
    0x1403410303803609098102d1182c10b1120900055010620125992694200804100406036540c0c00309400504142c0c001034191103003c1082c1c42c9000700a400780c05132a01031440b8003085036032280201e00385c98040300c3d9103102e504240c20410044040c16101002c0c0403440c1005420002008591180c40e41d07294404d9a82d60700521801c10308580200300081000079a07c0e1100200b82018086110b92066100d0b100c284100041c621500342c41a50000b80994040858a548040d25000081d0f440750445000c0c1d110f07071150303003c102c21481c4c140b08540c20040004101201c00101822141640c2030400c000e440881d003c1244041995a02e8000c042601000f00706642034101c035414845242248000c1c980311003440d864517404aa0050743c55400c4460610303020400401000100d03200e1048002915254440440d80002c1442d04140441c1d500095a0750880007550301d01248038403070004d5070110a0104130507042c4900e410200780c4641d001ca01810301d03a02d0542104049400c40c3c80c01c0340c080c0c0c51902c12 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 660089442 1250 660088192 660088199
    0x4050303010302130204080601030b091504080301052d1c0c060507060c0c030c060b040908120a11130504020310210b060312030f040f05060108031c0c0206071202090a0906 75
    0x34511010710f420b480700c0c0031400d2034101305040303554023018080600802c03011030000b0401001040040303100c4920350448503903414149401d0a00e0780080c05120f10440081d0f00d45a140000111200002c005c004424100f644050080c0038501103078014014a01c0a1084c0030303804980c055080d00c00601040d51f803070382c0c1c0d12142c5c2056011100007081c52400c200c503c600140101c2e40c400600500160481c1b000240204060005401800c0300312005103c006c010582c00382140981810a104900d40801480b983c02d060070720301c400d80700700b0440210352803010b80240900c0c20160f019540c4104d40d8080b00e4001525100200749842540045110740a00e50500c3e40401c9a10f1280711b400c01001c1e4014414000001c0b4800d4031800020402084082121b00050610500b90442611207070420283c943d1544c552518988981c054000d1941c11035881e88a204000c51074420314101010540c003416281d103400c541200c0c0c2c00510081c0c0700030325800340040c209554a150022000f04045840024550328 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 660090692 1250 660089442 660089449
    0x2121e030c1612150b030106090905011b050d050c1e0d06050321031005090403020f0c0a0f060815040e010b010216030f03050f0f1b0c03070b160201030f0504050303010302 75
    0x1200780d9542611142010020f5092103400d168219a1240700c0e0640158081589402041c00c107034026459802c004000820480c140c1c40070000360700420092002203034a101d01440348902c04021030001e00e0030040a40301000c15400303260030010300010303649001030303912a010205004000f4407480e250300041013028003c0038840c000050070240e0140407032030b20720150007400c01910010300030340000c004009102c607900c405880c000b03000c0c02003640c1c0807401c05003030080d500c0b00048440d50446c4a4060300b004246028440c2d003044404038206944101d062030320880390440050507241d40b41180150000c2260344900840c030204541e10b00005109540500080c5010702c008030088985100200510105d2000c869960b401c40c0c050070051368401610b102ca070800d100f1035041c1c41c904140032808896281580298280041142080b5903500c1c00100030503480d20824465034039a030b8010090b641c4165400804052a0340c01410005643e444400ca1607007a1031003103c04a41541001006008628 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 660091942 1250 660090692 660090703
    0x50a080d0c030b0f040207021504090207170405060306120f0f0609100b100305060312040b0a081e1b070503070c05040e0316061d1006090e01090f02121e030c 69
    0x118034060020f08140380218041d1600d0113101030107244c0001d03d50055484940c140381c0782030040801c032965603598410000094001d101b040300d004040700081140c661211080e9015038100500051441e183c00c0108a24480300500c140c4003070240300070611040505004200443d480c41010b0002071418051083c00c0c04111808600310529000f500c40054403211a1890360701c480d03080001d03090300d4444c00289480811000481c480000040100d030303c0040c0c10107088248015183c440c0c40d91240c0c05203905103210825481c10710710542000418242a41c1c54108081c0303c0f082c1c00520740650354a9490440d03101030010384989401c00010400d50400e0310a811a40c1000000703035050510000c2880304000c2c4000e00580101d0325005400c0d03100107150300c000c02c40c10f00d41c0c040700c000680d800f010038003510350742c4640a00700d0b02d0701120074000c00042c0580381e2800d0703010f003043c80e090045508001c0c0c200d803d000c00b161140300303444044060008261440340c2a00b00e8600071501d13050881d40c0c5500d0031 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 660093192 1250 660091942 660091961
    0xb1303121404080d02040b0406050403060501090203010302060904090606090903020f15010608240607030c020f040204051c0f02060a0815040c050d1a09010b0912010513020913050a080d 81
    0x525296010980d19003072a40c0c5a00b0540c05682c00e55650020713025040a03008541158540d01800035000415a4024006000b10bd10031041404103a981d00b60881c101e02007480041e411920420a40c0340c1407800354090240c183c0701d00c400055454440740c07194100d802c00b00080300940e100d5030b08018889002c2040b07034210425000f0700c014660604600401d0700f0707005024032074280864220000c407040444007560354150058082500d4105070300b80204449226082a809107147d000424030608090003101d090300e0340a010001e900c6a42c42d001500c2c102040410344102007803802d070100603902e034002005240842d5451401c03a0400302000c0020b0404501000d100320324218103825141e400106a88180b501f80c0e10014810890302400d00340742e0000d140140d4030040700e100203c3c0090900014080e03000f0241c0c1c1460702072071300c024642c4c203c920984031143d0400421440c180149010511180d01c00384100c0c2c010901c1c5005d586403451b0900e480c404645800c40414803104444440c45820100c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 660094442 1250 660093192 660093227
    0x30b0f07020a0f06110a0504090e0a110d05101109090a1b031a033c07030b13120305070f050310060e15220602030c030904020d06030b1303 61
    0x29400e0004000c2d40d1001c0755000202a240e0b00011182800000d5002000c40c00030601020b80d20081510020a15406809032900541c5032804051400800003180d140b503d0b44030540d1080103654004004404503900b0080301c00d4031445106c40c0400306203001b605400c041340d1003956210820a01000f01c040e6004140b400e5441c07030080400181031003003840c0400c0d44c455040000310a0b00307542041031207800040340c964051044044400d81e4000c0520000e0159200f4004d1691070011030003c0360000d0003e02c101c605540c0420020f2020420100205030010f10350346180a80d9001079440d80c14149807000802d02184d516801c0294543e005000b204170000c3c00d241c1189940381520708046866050302401c4104202040241c00c00d4030f0703c0030700005020036a0003d944030200d0702d10140285544c240f203110001502300c0c00046490001040c1c400005c90240910b007055144800d01c0001d4000320038001c14951a9000000419140002a80100c0c0c0701038031540512850709011b00210501c822107900c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 660095692 1250 660094442 660094471
    0x32006071106090a17280b18010603050d0305040b0c091008060402162409050d0804050a0609030e040b06040f23100906080718120f0b10030b 62
    0x28140881c06420900111456034980d810000400d98410181e0030400c03410800449142c00c0410004064a500c89180c85000c0e01c00360258a0018109003100000c3c600002030340401e00c5204401c4040c424054000c0001030783c03583d40c0e01c4031464130107880c080b000400d540302d051006110b00c03826101c7e404031003980000e05c0e1030004404034580242125030302e0300300900c607030100d2201c0c1d980e50100c0c1c840004904080311081800c0c1000c0907403560800241c0400c0e81640c04c0c2e001e5615180c01142241031704007014100642c2c08000c1a46c880d003009000701c440d0300a0151900008100d481002d8901d4025520503a00c5175518091004840c4078500840c820242030008001d00b0314610b40c0ca509440078940c40701c4060f02d42980080440700d40d003002c1030340b00d00341c41c003015075003903105810104980c05591440301c0c64451540c00e0750700e02c1d0901e03080c402020744180c2c20301c00603071480d05804e1b01c40c4c881c05049400b1101c5854042e5003807010360b40c0108604044c0d038100113000c04014a03079040880e07041e1501 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 660096942 1250 660095692 660095707
    0x60501020c01140903161706130b061504050a0902030a0b0111060a02090a0504050a0b0118051e1801080f0f0609150612010e060403030e060702070504050a060906032006 74
    0x7040311152004182d0200c0c80060041d0b4030362400d00003120911448141b0070302513a120b464001c0020350602d8510798034400c900c009a510400303140e21b00b040c1c0b82c00044c1460540c891105101c4110700380407404000c440c080200068a4568460f418020207580c2c42c016103e003480110700c01074070300c030b00c1410f4104000700c0401c8905203004120590082c909507401655109040041101049154010390f030247c40c1200b007040200c040d8020030384159090362488417541c1d074044189400003ca0040035003112140180c0d20002c0d241c1501c6144860000706488801100c3d4070071490452000d8001100702c6d089480c1c0e40700707d488100008521303902c50b98050120ba250200c40da5032780b05401d07060101c4044d021000700b001500d96281c6144441c440320300a110702c8031141c0d96950ba03020107a4040300020728040c80e00180c00d401003509405010183d02502c046440c107402c01003d0040913100d40d0703a1a0361104001401c02d10381c0b0990000b507100d10304122101c040c041d4040c0203d2215494580078480410100 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 660098192 1250 660096942 660096947
    0x603110303122a1305030106061809050a020c060412020607020a0b0609040f020a03030c17030412032c100c051e0a0903060518160b121e010f0801060501020c01 70
    0xe684040c5610000c40c010f00814400e04a40d00c481006004505001480141351410742c10600181c942c140c000b840556074580089862202d002c55110ba05082800e040c07241c99495004903070044581ca10141c20102200740d8142480000d03a4210394108080001000903a0188403040d4040c8507400502030b07401075070700d40c940c0ca0140144030074840e07021040042c04000700303a001650300580280115440d0354681c500605900c06940040d40c98004018441ca409060502200d210701c0c1d00005800b0300c1d016015080d0003410002906581041103200040483c078100c00823820003864090041185c1142090031800310b0f4900b1880f9020404104140c1120761183d9244a0403070408028995071060400e40880300654181c000030011400c010902c490006601007000c2044010030541c4c1c01c4155401100390f45001e40d2150184210081c000c200b006281000c00c1984030b201c52007030762113201120050540102d4242c00c032001e11821400300f4000303c03409100725070241100f8001440c02c1650351002 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 660099442 1250 660098192 660098227
    0x902070c060302090604050d170a09140a1203081302030f0a0b060a030b040f03020f03040e0106170621030906070f1b0b070602030702031c06060e032b0203070807060603110303 77
    0x4070390245d03030402328090812080c0101c044440104030b00d60b0713031a000c07503680061140440b4414041107209030001c03010389141c4400031104580e03100350440c0326010746980580b40f91074000d02a4071300c944180150702c05602c061260085201c5940042c00403d4028a0407500d6800c01410700e0340603200b6a0000c0c8001500c0c0c041182d013207600b084140c05004401c3c90100e02c0e1141150100c000c5010108001650b140b1400210703040c0d5905444984017071602072001d18400c6e00031202036902ca107000ca0f40411710000f0b0942c1c0000200d441003a40d15240d42c000105469500c2450200c403400f0f8101c103040c0030700c603034498074a4059548100340103c00340380c41d547e20142d000740240640203079400000300d204d4900030421651403a00b1081108088421017051000402180c1f040c0804a6968041c0020350b00d808600590041c81d0042c50300440c0684425180a00317211054443c19071104000780f00110355a40058511144240004180c0c03606501c0c1480b10190b1160340c09001e54024801000c052144094 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 660100692 1250 660099442 660099449
    0x22407031a0a05091306060603060f0617010608130606150e0913060b040b04090b060a060f050706090206121f0e06010c1104200c070602070513090f0b010902070c060302090604 77
    0x61444c100d0f100d80e0020311000b80c042e070300204a42d00e0010009940340d0150071940132514020070303840c800c554800040e01c403070070000582040b441c04030005020103805110041c1e0040039917018842c2c0030005665034030032031f20340350080109003100942c021006a0300c09446042e80b841901c544400342045c0310714024050b50440010185501c40a103010b00f03840c0e982c401012500014001e00c003d0641d0708014a600809807800d501031194180f01280040c001d0b041540c2c2c501c455501e0070326051007034580200510920300100d0340701c082049840c02145103156454042c400d00c2540c83d06803c00480c4000521000b9406140c441c2517007003c01480780e030031200300680e00c0c0e0402820a07409200d40e001500410702207940903844003081c905107482e000036502500b43c801c9402d0865a820b82c07034402c282e95813070302ca1140c5544a60601c00070500c404441c2c101d0480c01d0f110b800c002000c0c641c1039a400e00d60341d809812465111764040345580034001840491720007480503040440c64124a0270118406115901 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 660101942 1250 660100692 660100699
    0x90a09020c0706031a1809060601050306030a030804050312010e01080f0616050c0106050603010602010221011a0706140c2508090411071e051228022407031a0a05 71
    0x89002000b0701104400005d18000b0042c59010441d00d000031031180d015143c040051059100141d06035000d9070449002c1d0b9001802009400740302c4c2c1c0d003240d200c1d0000f002102c02d40000c0c46220b200142da58400743c0a0010f640040d0181d41c10001e510b4901880380c50300c0540c55100c2800d01035120f0710824206070100003454001d603101070b00003103e40503003e503602c0240c0080c000000002c940794103501500702200d91003d8459201054682e203841e15000b03010700e150740100e4040641c0f10b60660b90050052501c101c0d0302003600d0f200000030301c1c8046001c4402c04010b1304001052150040a0310617410802201c45981ba140000c60f210064640503117010703103026035941d25000203403040d40d509a51140d0f521081141c0381030122a000300200b0a1001c0c115000d10485da840c403200c0e80010107a0320043c40c080100380c01c00042c1c03085081c181400918030b406600030740295100e0350000111661242141c20480c040c03906203400d00a084413811484024038403100c2c0100c4103140d90309540031044a1003207 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 660103192 1250 660101942 660101951
    0x7031e0504030815120f1006080a0837020d090905251b08070b070504120f06060e0f01030302072c040515040b152e09050d08090a09020c070603 63
    0x1d0011403003617107020362401102c1c03107400070002c0c1d80e52001030030304102003500e01e0601c00b4680d5401c00b965110303075068008040c950144a0002c5050001100f00d1340c4c2c103469002003000340200303041e04849510300703000000140c001090421038503800c48074181c01803044142c10042490200b04c1020281d136007800325000a21089002c1e0241441544240c030010490701c0c0308814490113240011099101140407242100d01c00c000688ca18011b01c2030302c0032100303a8601c4000d02c0d80280d82d10f108240300b64404580507540c13224085200382400510f1031261207000d02a00c4954114240a4070b0005664046800c211800414081d40c101c507202000940b007040100c0221521680f030481d00348442c0c10115201c840c6220204010301c001c12820602400d28188042d60801d01001800803402506105969400324014990416411501204c2c82e008075445c0c004221919000003840031a5100d07410341e034a600101e00c40d40240351440e40000101200c0600714a05403110f811a900c403200ca100b03590505985 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 660104442 1250 660103192 660103231
    0x20a0515031506190f05130e011a12010b0d290901081606050f0c01090f0c0911221802071709100f02010f0c080a0507090509010b0a0c02060307031e05040308 69
    0x181d0309660a0007c0c1e0082a85603e48400107440440c070240325048602d142e915820209100040842c1d500b01041c00401d0180c1e8207122000c1d40f07951060803c0981d4607070710600ca020981c0f91503508865003c9d50115150149000c000300b11a60106810401041c0c0000b50005600c240c800c8000b0222a40b0f801e000f92142401801082980200c0e140e24960f54240340840f4204801040c200d42003610501160300704e151695502411240040200c1a01c0c1340e04000300801106610f074140c6505160082100245450368a860f4900328416800407072550041410320401a4030300c000403030080a00b00150401c410034001031a504840001c00c4240030b2110b5201001d80e10039044444c22056001042c0b081c1110b0b4000140401c404851880940d841d100109459074031a039115411074400a04407175241c0d081039a138034400e602510b2050700b445401410100180c40350380c040c40c03003030f201d5880009041e030f000641203a400c032319035121490140c0382408000020b0f030046c1e455500006400c0c10071624050 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 660105692 1250 660104442 660104447
    0x1b01030b030109171207180303030902041523060316051605150103062702060c03130803040617042105091e01111513020a0515031506190f 61
    0xa119002034100e1140400c00c040c549481380042ca0018542d090341e01d0135545148049401084a41c9014a10f0416600810200b0f00c2908000141c034002000042c1c1e60041050000d040c01c0b0380d80c85030200b0340d1411300c00640707a0402d0a0420f4603074819141e551071450420b403410041d550a000b500140140490050983c1000c144014030303065000c8121504603000d500040c8000409200895480381403010500a12410b0380c00802c801c41803608201c0c00d00042c1d82002025040b00124000030f10041c80f4044c400c3d45040c214000070141d480240d035a580c1450401400c8510100f00c502036030801c00103000025040884c4c2d41880782d03864800702d16034901c42030304403402d22074456015032200701204600715181e400701c900001400240c0700c650b446055058120b4440d0482c4040075001c50000c000901c0206020240303e800c00d00c01865140c2c0c058903080019030000009a0140d0b541d1400300400c100c800e04040200120181240c1150401101d4114451420282c58240c000c016119014000650 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 660106942 1250 660105692 660105701
    0x3020309210604030509040b10081308160f050705030718020c1c110f0706020d080901020702180106090f0e011202040905030c011418030a14040b030a0902121b01030b0301 75
    0x1110903003580c41600f031504004025400415a483c400d074030f42101d80d5030b00c0c0f0301071038030464007203031605c5a40320781da07078100700043c0c403030040b201600c00c5901042682e000b4800c0d18240701030b01d40b0900d13030a040404103003030203403074103061f500094000c0e4000030f4284200740e10b07440c10b1032685069440c0540d592440d070140e141000c1c602d26403141603600750840728001d0764108401c081d0f8010781c50304075440c014800103000c0d0b9401603031107507601503040b84c1c1385030000ca4418071034241d0040d0740d81c0008d840c0c401964081100310300c050060510443c600b00042c450664405e403507038010071080c50001661410030341384003000ca81c1071050101c1c42d40c0381c62060b011900c81d0741040c0ca90380c3d0840141d07034942c004d180c0802e000c2d054070410001e45034800e40004d14501d800303c604110a550890055041102001c420740d003504200c07c840c26180d20034000012100b158000444c1314940840f000b154220705441400041d000000002074260000101ca04560480c51421040103000340303008a52040d080c80480e0041 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 660108192 1250 660106942 660106999
    0xc0705030d030603060f1a040216140a0b100503030f071b08060610110c0111030c06160e03010c080402040506011202070f12180b07080c030a030b03010608070303020309 74
    0x5005103915003071015016440142164000c0500f400901a0b02c03001c60116510740000c140c0107403449000c2581030901d58007625070130b00c1802000f0040620380e1a1b0041c0c0c450301410046450b84880c05e58003c009100c0d44994005050007080000c0d9030401c80026180e00400603012254140410003800340500701107980b448601c820360030090561589200c640310041114441d008005a082080c0b1131071041030000c20f0f50810380007801400c01003400448445106541843c0035104c240000a01040103011b602e00517a411050108154100304025040322760b410415071080c0d2401610800d02a00300200b154001e604540016051344c070407005031020054000459408c40c80454003100308041002100191402a005143c1c030103010340d012242d5031032100d0740407039040103613000300f010b004c024026140d00d500c501c05441c103251a02c4c001a1035a0042204000041d40300c82c0746402506007807040340d005c1c040d1000500304003825520040e5481c4038a0400711300640104071011182c031000b82c24008030 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 660109442 1250 660108192 660108199
    0x60103090812090a060c0521040201020c061314060301050918120403050a051905070e04080706230c040f0b07111f090b090a03080c0f01050c0a0305010803040501080402060c0705 78
    0xd081440209a0310500900b041301c0f02c4d4a1b0446c09004e00303025030300783c80d452a8800144a05106000204c034030400010740220705600c111040300e242c0c2e030ba5200180103104407000340b03c004a071804440000490081000c1400b4502c104018405521140701e9154024502c00b1410740e84d240100c1420300d840810324036851036410114003c0b0030450041800b040440c05001142d100c02c00c8400141c070080e4031240000c1c900d510503142006041e042d07031a041d078028001d031070300381c202421511010700381d89485213004404066045403d070010f03a40c0d800c107500704804a118504060603d00c080708019040d010301c410311107000c2110002c10400e0f0106c00c08118016140c800c034100a03140c00344000f03803100061004078400102c0400d000024500b9640520f01c0100749030a21031031a11036072500d5001c0707642403145000e0709007100585082400380780d0081c624003102560319200000010200c82040e00310010a820401007000140e0340074000e25080794040300e0b61551514203001141c82d040c555403187c0d07007 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 660110692 1250 660109442 660109477
    0x503100510030c02070e01080c130603020a0e040203150712150b07060c020d14090105030c09030706080603010b0103051b0307021e06010302010f08070804141f020307110d080601030908 81
    0xc545030302d500140c02c0030300c1503000c44441d10748580c40c180c0b40306000d0051030160750040340c1c2c0d80144e1800340c080e0880e800440c4000121181c40b60081181925150040b08964480710248000c509040100510448406030011001d050a90004080003098000c255100380c03031300407880e02002e00800f01001481519580740d40c0f000342c0d00d4000c01034240c1d058450054040c154a8045180c010f1604090400c9000c1010380351900b0500159569003000d4a843e652a40a2004980c142c401700100c0380078041e035454694a80c40c0c040704150a560b82c0c501102d04050408081c02614000140c41075003920301e03d1103c9840740d0312884102c0c0fa080c1e100f980106001d03010403a5541c035440119040381642d0003070383e0f100443d03000038100b81c65020341074800341c002131141c500140204040e0349907003d484030090262201013a01a10214150700780486181c103803035000081c84a410f411100310444000800064081c050406801800c4036034010012814140c0740c85120007040100320446040c0c2a403000d00e0036 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 660111942 1250 660110692 660110719
    0x408091302030910061a030a020a050913050901051f09090f0209011202010e01030515010305040c090905060114040b0303040e0c040e010303050a081807050f0d0203010603031806090e0705031005 85
    0x44d9944c4030131141e5910036140031804101440ba11941d1031084140c031404501d561920071a42c0020b6008410301810008140002c02007542c0e0108032000c660076080c1d0100d901d00780381c0062801c44102a00b454511000c141680c81c008101d45002012a40100e400050b80600c2e810700e0406100c038810001d6000440e0000802e81260b100c50690100b8000e030707102c5900da00705c040154101d4009407250300c540100700b00181c42c258425040160f005105184001c0c8403035503082e44c035055030300c9000222602d8004800621018500c00c210200c110700440d0b0900404158401084d128442da0141940c0f201e00180001d200248060843d801420b420340b400341c0030340c0d41c0d0a00030302542000d0000000a240d40c000f107050f80c00d00c01d4074038603034a040e1400b8000c41c40c036010400034880079962610b0341100e400381c0b880c4050781d420f20840300258003e44406c041901c40300c028112402e0300360004000d200c0e41810901801e405101c1c00d0358043c010f810040d5480e110b1203400b50003080a40e0141d58420b910180340b8 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 660113192 1250 660111942 660111961
    0x50909031c021314030f1e012910031b0905031506031c0207030c06030501061103070507061409130f06120819110a030f080702030909040809130203 65
    0x106071140c1005000d0710032412039180007040e4070500030380200081c000602402604510354038a608014018111740c18101e2549010b0b01385100e0f240750f03010f40741940c003184a00354401e015410f0840c003442440844107800c0b1210107a200301c1c4031000c3d801307085400d02a404050080c0e11408400754940304440700074014000050810400c1d000b01c0b03019000d84510400403c401191082c018a4014042e0200000001d80c01605400d05202881144542ea200102049010504030080c104582d4045219030514101400780e01440703448404941c070410108001c00e5001c5601c030241c0e04546841d145440100d8020080c43c040c81e0f880c2030717116480d1840200e10038600c1d44a101c1e4803810700c00a000e040e1707450902c2c200311783d0000000350102c402004443c0040906200d15509a00b1174140143c070010b200090b680340484065040b808990000052a02c0c941c1082820b503104001d84000c501c0c1080312804036040440c00b40c401401000041002561961a41d01c0f00c002e650620504640364601400f40 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 660114442 1250 660113192 660113197
    0x10e06060406120f020f01020c090a060f0f1a1305031f0b1507120315030b0915090c01230f040306060608091506194203090c05090903 59
    0x12240326518216002400121100384050f8039500120320304001040b64007400100726031400d4190440c010703010700202c207564600724035010f02d04800c800103180c0d04040781c0101c030a001c4d801c80c58460002100c100142c04070030004c00e00d04850350700c14640f904003080c043c0a144100b500b02980c980540031199200301c000d02100c8000e03820f20041400500380c12800d0095013451901900c1e0120f03420055140803804142401d5865a924580041da46071110b20701224034940707410894060305804144241c2d180c0420106040611034880100c43d03007820b10035136a90304820444141031003040f0402252040040e0b02e181050024500e2555440f4803941904800d0340c410f020440d44036283c5100852a40d10071402c0714403c1d0001c10090001c2003041008143c006001007205078000c4910407541ca450005e1205200141000c0d82000302d441c081c080510032a28003410000c20002d61803604c0000c1c11003c048460341e000369401c001410618a087c00310400c40705401540d00000b0100605c2003100b0300000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 660115692 1250 660114442 660114451
    0x20030307090b04050102070902090d0b0103050a140102041508060a090c02010b0a170c06070510060b0d05090d0905130f1b091505070b07110a0b0601110609070b0318010e06 75
    0x503a10071150710b80850303120501440c040c1034010f90140905000c1100281c0c020025241c0c020660310051100d0340e0b501d0144442604101c0e00c030780001e4400410000d03142c0307001c4040403824000b941041d0a040034540c5075080d0b44056010040702c45e0208542d61a10002c09028007048039042c8107440c40048040d01030220522071a014080140b0001520850190240710000900000e03000354006401000000c0d000004184c4290203007c8000780d101165204003802450303907100560300c4e20b1f1245521411140010480101d030303045520300f1010b150380020140c1c10354001311064072002050301001c100800000c51103a803900d01c0d01e078840081138030001104110310072aa50b0030b410345441c1c910070040034109440c0f600210b1400e100c201c001904014006600c410705181000341c800c0c0c13011140b842c0c00f14001c0c0583c0e8241d51801844600c0d684000c40002c3c4e50314003002801030741060703002c0700e40d01d420794800c203124001c0200200360b000c140107020390780d40c3d0240b00082c0300e02d006c0034000d140c40319001c0c1d8 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 660116942 1250 660115692 660115697
    0xa060f140103052503080d2a03230603060105040509101a1516030c02010c051b040501150813140604032c0f011d060d0504020a06030e1c20030307 64
    0x40d014034114003800ba103041031700d60002c070440c24040d105d15094081c1041810400c00300e5403040b00303845108200080400420301c1030f500451241d04a100f2080c180740c0c04414003410f4002c82003000381c07644000981c04d04448056400203000c5d41c0b940070060500c1d84c04069090780a0604d8466a03500300150110400288100c60451600030040724a58151142e140c01c4c1384a4602c60090401103400390180604490040c10010780c0d0502940e110360a082d00d00700307841506400320010328a0b90410341300385400750900d03144204803840000b2003d40007240040c004006402c0c403420071400c0107020a038042c005c10554040311614141450080d00c41c410707000703545a0052032002c0c40d40d064201e0111a820515024215403a2600100d0044030a1180d18182010340c5004002c40d0407a84c540c079000b8102080003580c005a1401d140c03040207005505c50340500205401e003d03401c00c6034800414140f00d11506810700325640c14600c1d0080d1130301d0211200304101c60062501c00f0200c0140030004510400e0700360b = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 660118192 1250 660116942 660116983
    0x40f03110906090702060c03060a21110f0310020f090307060215160c140f1c0305010e07080c1804180302150124032a08180a060f14010305 61
    0x1d02800156007044900c580140e10038000f280c1788980c7e202c01103800c0f140181405074243c1d15103882e181140c001d813000c0c240c0464240c0c00724060210300e05840302e0003142120041e8000040c00700181d60390016480010406a0000d041c0c45441c030600c0c112005445d02405940800340e60b664060b4071020074124000c0084841c00c0001c40074461064a1103d0a04584130030b0389091060300d0381d45c1c2c11300c50210341c10104d04c55602003c140290801c00c92800c141c1412080d11021010303c40101134031410f07844503028810070000d000c082a04a40d80640c05134005400a407105960442c3c1402c0642020344c160304140fa00007109040c51800304032115050081e000c6980d01058411441e038150800d106001c0d4101002d141f070140f06d800640005012413103803401154241c8403e003500038800f0720844092072407082d038182c14205508885103e50150002070858202a000e00e91245c4a40382c0070401000a0340d1095040b41001c01c0b6800989041c04c55554180b441da160700c0c00e00d40e1821182d1900301c600484 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 660119442 1250 660118192 660118201
    0xf03080109060302150a020c181b031504020c0a0c0b07060b0612160c0c0905010e1815100314060417130e04050c1005180a08060f0c040f031109 63
    0x40c0d0050404507139000d0038210000e228a120503c080d000581424118000d030a00b1851664854003241111007110720504a203003481c0d10fa456070400500d180c00711083e03081c41003080105103418903608101c1c06960160303031707001e0b0f40381c070503040c540122001010040100004150b40311180003801e2118407601c400c0220440c80c1042104e01d000340d601c500e00c1882c0140002e0b4074064050039a0b0292102402c006450903001d5039521004c41d01604910501640d0341c0041080b00c56241e98a40c0010740d1403d4644840c141441044d100c0c0d42e0785015501a50000c00800c516103040c61180004503041080300307041800f14502107840742800e440a483c0d4900f41030034a0b80d01c40140d0b0842e00c0111036041082c070440e20f804203101032154001c01c10354050180140300c42e0540c4450440c1c81040b002030351019522001c1c015001c043c84000741605004004082c0d0034400740100142c0039400401e424004e8207555a1140c014101c0d02c1150840c90a01101003000020010000c03194810240b00b11216000d1340e85 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 660120692 1250 660119442 660119459
    0x1005210a0b0a0e04060b13020414040f0506090a0221070507110301021614102301060507171c0c09030b1b0a080903070c030c03050d031517010b09040f030801 69
    0x40a0080c142d45440d030f0804540040c200317911400b03c9160203001c0391410b080d8014420102e03002030b030000c0d0740b030047c08203c00071a103041c0c491100e8503821004100200d080400c00b2445520004104801c0c0603400034900c446915014410030365600518a80d645034504020000c100c0e4009140440303410828a80d01441c82c6811300070b8403100c1c480e600f0500a440392030344074426942e0410a92800f00d0040c500003a441c4003182c000c60040800700607403e04143d528108400c001030341607120300300704101440840002012404149002100c0350301c040c0d103d401c0201c000900c0d0308880225015170b854520a6543c080c1c00079030341022a030086140201507074940b012800c0050300040329801c03030701c2c0412004402381d0140c0003140d045421242101d0800800d03a5444054513410740058a216103409010420881e0400c9003044030b00715807406112540794141c506181e0610fa0180300204800111314600d800001d60010003880c40007840d6070380c682400d08112131402070060703090b00080c2110001090841 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 660121942 1250 660120692 660120709
    0x904062d08030a050d0612030c1406010305060a0902011701080120070c060f1214010527160e0303180a060c050a0f0204060305060403211a1005210a0b 66
    0x3a41107001c2c52600d920b100d4119250b5102051040600e0764409010480c107103000354042c8114031130344404180030100d092180a5401c201400d464603072001c40180b000600214a05811031030b028400b2616100c1440140d03400120b0b851000c2c4028900000000c6005054010a426894224000086a10f0548100c44920400ba070260104585c280c00308109c6115014121000485140400c5c801e01032201c024141d0b52000508000c15846034014007052910705260421002070075440c0555141004c0240c00c118002480180011800c03543e141c0658020070302059100320081c1076a40d60361298520000c031710082e07038102d030242d5003000010800b039000e28003044090717400c4402010326549a5441420101c1c010000320303001500c0d04d800000064003004403e00803803003030700d985c800e1410700041800c44491001051400c9810441e064201040324041000e01c00025100405131403c50641a1018032498682c488c00a03880c120b1036048280024065015540d001c83c1400712054502c200b02109 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 660123192 1250 660121942 660121949
    0xc06070801140f190807090902011202090d110301020c0307050618150406050c090a08030306091b0d051b040e1009091a040c210201030b041a010c05030904062d 70
    0xb0f40004910806450405440465a6958a84068a203464000380350404a481e880038064a44400400c800c5603004410040c85c22000c1c0c0c400c6040440342c40010311003040c1c0440213032501e18507032001c0c1e206450a4044480c0060b48504070780c2e8a03040781ca0322554801044501801944841e140c204103a02c010030900c54404504501d2051034031a44c031610b000300006044080400b00c200811a91912020400320040a4101c081c40e03c030b240c21401c0c06090f001c010480c4240c003243c011138081c0356000c64247c0303000760244c410000703441d82c4590103a002c0460740c004c03840c00c1147c0418001403070f85a8501540c408c0c8081c082e4811455038410484c4c0070f403001c4c21130083c40343e0000c80d14100050070045001d94414012004404011780d64000c840c03071104421003640401201c41000400e41d6010f014001c08580c0c191000c00000c03202c1c044084024000c80740c05070405c1500661042444020410b503102c0880017001000304550f54a10320070b400940d845d80e80068140f100003010681000b0310404102e = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 660124442 1250 660123192 660123199
    0x1206072d080f07020c18010e0a0c02120f090604120213090b060f060702040e070906060215010501180b030a050109051f0501080c0c1b0f091b070807080c0607080114 72
    0x319110b0842e042c44001c0014450030841c0304100c0140c031030396a034a08100c50400c0f1b10304181031a50605030050b440000040130303d290a401c02007180c003140d900143c0d0200c0301058089107625800d05005001181c0300301480d00342d10403008500850151040b14420071b600344215031428030103480c0c0c550801a20714141003e003041c50f0040c00120181000d00c50300c000004002c00540c50b01089a001900300c07102d043c24240f090340051001c1c0005400342c8a541d01600140c00144030000b950895403081c810140507a6041220580c0703e4800c416031000401c014011003281c95490345000210800240400d10035030b40f203141440702040340705403440745841003459012035400b0300f1400e00e001502c545001801182c40e0650400c42e045000d0303020b00030342081d4507581e04201d95940c03610042007040d48060901500c10f291110a2210200c81c0254a1018800702d43c80a80c5408032418418554001e11001410750b00d00040c800040300d40c00302d4038174030680481d12442c40316602d0300b400c00880015000b900e9003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 660125692 1250 660124442 660124457
    0xf08100c090612050a06170a03030c09050a15050c031602030d140703030903020c061602090601030c0504120501061505091201020405010e1306030f05030a030c0503150f1206072d 78
    0x41c1c419503904513683c840105080807030407595610010381420102e01d8072072000c0c0c01011482c000c0541c980200c00c20601685405031300f4900740000544082d8061080011410084d82c5180703d050003401983c60038580501500e132681100c420480441041401c201c0c4079006001c21000c0043c050080c1c2c0701c002c000c4d5811141042540d1713405070000c2c00310b05403d07400e40c4220500141079a44000003041d032500040306040e181d0301c11b4410303c4500381000d40101d0505007031010110300f007039001707040c1c030100c0d03c100c4459000204681005030050206822200340d881c4601d00e4074242c20340040003421125015034a41d500da8150904003802c030f010f00d0060b240001c130840c92240451401564441040509000008556079a40c0e225080005000c108940c590400710b0711801d1283c15103da80c0384444242080d500e98604100310309034000da010781c0288158940000c0e8011600d802c07980324403c0918104070740c09400c0008002d8034641400c104100084400d40a41d03d10200c2201d180d42d2800441c0c44059 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 660126942 1250 660125692 660125717
    0x302060c030c1207030b19030213020a2307050312060f0f03100b0a150c030f020c01020606010804051005090609010b0a140105160602040303030911120d03150f08100c0906 75
    0x60ba46040503044c1410181c58640d49205941c51915a2880e1340e4615049001c142c0b940c414080e00a81113001d02d5001403040c448400c3d45034011000c1000c58884100180708035a130810340300350030701403c0d6000c0e1180c80b001c18103001c00c1060104240c0a841d0444010245114040800504001e80040d454158101c001001e44d9200c107900070426008006201110040d00c0e403d400420783d06800d05400081c041181c54018190052221810b800e81440905411040e41c800070b940c03114050103240c100b0004074001000d05c80148a505d8070355503204014041c505198141e036540d81401e503620102035107849503905031460030044110844d8050074201d80ca9400b043d0054403503806c00ba21543c3c4402c3c4031110741d80050300c644010000395109480021f0600000c6c02e200c0c2e068420003101038002c901c1400340001d4114001003415070284a40713030125101981c42c480706012a400e5010b007101c1003803100007084003080401c0780c41c15030803802c0c2e08002f044100c0c3d1007250b031082c07544900008600350002c2107 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 660128192 1250 660126942 660126967
    0xc0102100b0f03100516110c010507140a0317010609032003030408060112060506040207032c10120c08010b04060f17040f0b010504061401080a06080f07030302060c030c 74
    0x11501e06008091815405103500880d0419018581003c032982c2d42c0c1c000c11101015000b01c104c0488428900500c0001d000ca801316504e0640014203818842c010032a00100544041203840c0300e6440419104010030071700e40a0002c10540d500d00c05c00214031800810028402c0541074200c0360020441d080380800b038030456a490020f03180c0150540010400881d4000307007040803500034007074901008440c0c42242020b50456030f02806c01c500c117500402401300400d43c0031060b40301c030b0803028000d4115000510003d01d14042c820701b1031034101440e6070903070540e180c01150300040c0c060b411105029101d041582140c51490901036200206030900081c80408e1103041490b0f528852414500f606070520b040c02e00b24036004941c11a109500c900c2c8200c1005418045a4010081500c041c0300b4281031034030a076160840081058100041d1900041c80d030040380e046800101525415620a401100405901c501c00c1d80015005441280c000c120b000c20340d4000c491040001c1003816042c0107004403207 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 660129442 1250 660128192 660128201
    0x8220f050304050d031e02010209090123040c0c06050a0605150a03140c190201050613090f0c0b0918070c08030405011e0209040e01020f04031b0e040b180c010210 71
    0xe54881c801484041a243c450801040d049800307500c44020030310385040c9a0944c1e10611601d14110390060081e180b4545070f4019140c103603140d01415070310428240c40b1105d01148003925250740241085a501000c5800c071504038207050245c0e01c00c0c88150794403481390064541070b00c5070070703000a40100d240b041d5a0040c0098400e0540f6450042902203100002240e80e01c0c0503502e10b0b00d030034800281003410001d00c0d40300305000368103800244082d04c2c0980000700b198050006030a4102e4030303200312108200030311601701e10581d408000082c600e620307100180d449400031414507001c1e00c024045100040701e101e0800d0720072004c0daa10091000c4965544d04c002d900b0241049510307640b14a1690014407407007003940001c2c840d41000684503c0c6c61810001500d03e851012407007640b0400c41c1d0003c4060160459050341e40081d4041078116802c0f5401521000039409001000d9180d0107200c01c105515000c0b50080044401d91081c1e402c042a0060700e0310708070f801e42405640a84101400034103c3d422 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 660130692 1250 660129442 660129473
    0x13150b07030c201011060c03060303040b041203230a181d0f07050408031602030f0a06062310030b011b0f051605010c110a050418030822 60
    0x401c2c2d2029025540c52072100c884541801e0742e2205841c5081c0242c0c2080340200f8440102d5203004a01078071002d1599846107009031802c10000307070010001d12180c40c10011100146614041c031603541e80e4606903132072403100d800d10803030016030300d0030415060b810100e910b01d030340001040040f40360108000701501c0044450294501080d840c0400040411143c0c2d4401d800c25450500700b00c2e20318111621401d82c0100415075420302c40140014070101c2000800c0d03a0f141494901d0035042c1c03d1550001910704603045c0b15880c45c41c820a01c8403006c022541d00f0510407141c0100c40d020000f410406480d92024501000d1038200781d4100d0b100e40e030103102c0d82020651900605040103100384142c1c5428607820303112003e450740962011524200314003080180341c8103e405d0139403500c060400300000d04980181502401e60244c000d400c0c4410f80d60564184010300e00100108810505828011200240f80000b03402040000c00010a5904241c051080c800d580030310090034407050707541e925149002c462 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 660131942 1250 660130692 660130697
    0xf030411060c010b01031104120b040204090c0b1804110d0203040c090c2c090412020c0306040f1e230304080303100f06020304080a03031a041a13150b0703 68
    0x240d2040301c0d2545002000710070325200010600340201800501034840c00303070025040c14420001003020514101042c503c41d50700c0705500d849a00d590000501503c4112030250262061010004141c0122801003001205030704440f900300c5a820200701c200c0d60810031550100c10200140d40c03040005500440d445482485d103205015201c440310740c1115688130b081c10200703042c2c0d02c81d801c0b8039403c44546d0140030f100b114406080702c2420041140300d68007506c0104225003010200c5a220b000f88601800110040e040f10040e250a0400703003400d00082c4400c1d6020100758440710407081007814007a94141e003100030506d0304001a6502c40c841180c24001c0000d42c001800082100c0c042440118001c802544910204078245180d40c810000c440c0d00910655108000c03c2003580f50103e514a01d540d05410009100c900c00300c05c001d01e080d119074100394814601502c5c40d400c142040b050780c1c0e010b90180c0f001d10441d1200381040084074143c440b00e0240c418108003c0002e0880f54000f050418401d1 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 660133192 1250 660131942 660131963
    0x9020a0f0e0705070201021c080105130510051009031406010e0c090d1e0804031406101d070309080a0f02191a06010c0c09060315020f2205060f0405130902060f0304 72
    0x43d0351702c948c00c0d0221074041001402c2440100b00d246032074000d13180c0803841c104e410810f071700b003000e11072540030114860380380902d00c03040b000c00156003c0d02940303000f140c129641c041c1015003621403a880b01424018519414000c10205130010142c4040d207084030700142c50b83c482c110300e030380350b108800643d44540702405010044180002c0d180d1009000203500c0313440c007100701e100d2213003082d0b003007a0000b40340002080d00c05500300002c91034a00c0c00801811092480c0505803a1580110040c000e2020084c010580024070b40b0011035105a5000e0340003e02d1742901e11450004980c680310050001001c0c1114822190040489128000c41c541141c07050605c802c00702507981d904464581e0a5100c140400d641d28001c2050240640001400340d070009070840c0350a0507110740b034085001c0c0c0804607242e132100c80d05207040900c5010711940a0305005288540b0341c00c0401d0308440d01c1e4081d014490151580401241e400720b40790103600070b840d600801007170030807650304407000c00d6410080041d103c5002d0f0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 660134442 1250 660133192 660133213
    0x6021006080a11150a0c05010f1b0e13020a050c01050106110d050c01180f0b060105130e1021061803020a12020705041b17040c05060c0f030d09020a0f0e070507020102 73
    0x1a0f030020916905d9a40303038074082c04000d00f010340c00c49040000e4916610f06001d041c890410360307130485035203422072070a02100c03400c07480b004107041c602480d54107001d09200240180c80340d03410402504440c02c620700284226070300c0e400103c840b01503094104105600600a1030f10300e5009601408c0c82d00220000060900c1c00d43c480c0c010122240c80d000c6c0c82c4054a9400842484524011181d1082003070070502d24152a1903403100081b0020b22900d490408407401143c1003400503803051000b081e80d07807545100030404111001c2c52440300340045414500d4641307030040c04018980c0400005804d03801900f1040c5803503c81c00350346c21038908040c045000350034000c170320350b507851154101c0001c0141701e841c0340501d00c41d03000c0d0520300d80d2141e40320130724041d00800000514114481e0240d50f0250345c02c03521001e504035000d2800e455200e0003080c500000c40c50349281c00840d40f0601626000300c44941d11143d0726118944d4003d507074001c41050b4503505000480181c0a9001003111520610483d07216024 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 660135692 1250 660134442 660134479
    0x91401090b090610050915040b09010e0907090b090604331d061513050405011d0f0408030601030b010c0206030906010f05041401350706021006080a11 66
    0x10845088404003505024031410040030010031381d2044501c1c0d82d8608103424400001c80c0340d0002400360031100980707078482c500d640755500502240038014021314030713558454059001c19101111410711030700c501000014000414061081d020b50040d01c072080b941c681d607003408003030300d8000f1f000d40420140c62040c0b0502c4424078482900c03000d480b248a01c030349040074107814007040b072500300c1c0f44041d43c4801800300e99603034100606052021100c549a4411310b5800b10302038402a540301d954401d14200c00080d40c1888600700c6444007001c0c0318a860b10303036980d21802204070802ea9014203154002d02c00200154001c2e4011103208405060814807030220790300140303a03a0302c12110705280380c20240c0104544410b40c141600500006c0701c2c01c4c000c0306071603a191140b559052245898108030442001042c800c40121080c90703140c0c4061900b5080403034040c2c0c07a91011188139a2005100f04410001540200c0c49800e0554001c0da000c2c03c0701104644405640300c0c105060241e0142240035032038140e24 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 660136942 1250 660135692 660135701
    0xd0f080109051305240a1e091403070309050405010e010315090305090d0303200309030d050c0403020a0617010b07020604260706111905071517070504092d091401 71
    0x520305d01d0101d1401500116065400c6000c0c003140c0015050510f4440340d00320000f02144126611540012040e0190429440c81c03070b00b200d2500082e000c0040d55109159009074101c069602c04d40d824070980c2d903141a0343c0040e400900c0054403244044e40280d0030b00d185a048000300500900c1d1131800d10f001d1200103070300f030748815200b00c3c0841c1e591071071450007012000c00c0d0102c11000045880c118585a00c40c242c903403244441a2690382ea58100103500c2115110075103000d50f030040c11422150345c80303203000307400544c07202c540c4a008013400340001090702c8400c0c100c911965000c0c20b0107040c28a06100806940110b042d203080c242404400c00200b21001c00c03018008162a944200025016500c0c02d800c0407240e044004121034040340720008104c0008801d01120000001c5034110180d2100486550b4800400c4868099200c2d09002e1400e0740140903000392020351030108140d105010018600b502c10103441d40c99a29050240e00501d00158054041c440c060202e02512102c01c00da25400c45 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 660138192 1250 660136942 660136963
    0x60207020414040b0601030603050319030603230712050a02061812010b1203160b060d050609010507030507020c13020307050904090b09280b1009020a0f020d0f080109051305 76
    0x40e541c403c00c0180a030724040c26420100030b0904020440c00c1d52245901c234440d00c0ca20b45000311700001c1d041440340c071a0340090300454014441015110000b000d451312010f0350070380c0030210701c1a00d40c0428411088040762000c0c030f5000c8024040f1224a038288122070b0400030800050700040984004070b034a455002e000d241d81c050000042c5846030404200048410581d1144a81c4c414420720680541e07040000540c281c01c0703540710790103507170740000500c40100300b00000300240103403405c1c410040c005411450003289a5141480740f0b55420310202d80d110803904244c0da1106255484910344d03102d0360300850f00f00b4050300d03003103252108410228099950313080085503840107650800c10744c15028070528070301e50b4080400110016800704860040754000b40003800744020400416082c0480b004004000e0401d11000c0d510354200401c0500b15140341d50800380940039984101000c00d2084941511080d1251103820b82c2d64203050440009282c01001200c420280c140c440c0081081000f091018 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 660139442 1250 660138192 660138221
    0x150a061e0e1e0319020901050906030106080a0c0e07050c030a0e040b041107050c04060326090a030501051e0118020f071b060e09010e0a020306010201060306053c040206070602070204 80
    0x20b4003102c0003858a003001d404c4c1410b4003c50384000101c0180e03100702c0640d04460044504805945038640080e0042c0311603449160705100302407003401003052484080d400c445404040344c02581d1600400d03603441c814180354210a4100b00a8040c48078080c0c214110020345c041d03c001000c55150002c6070440b0380c440c141d002949004035824081290030001e807181e109d42030310306010300d0380745a88d240409030030394800c030400ca0740703c1002c9180c42d1005000d0b1104c00e4070040c03030440c6041ea47e05040b4002c10301500c4215000b0f16001c0ca0340a00c0604031842c134102d68403480b500d5004c2c0d03001d86d82000250061002c00800480422801001ca884803401c20f030706403003081c900d1000d5450060040e01300e101c10201030780540c6400c001042083d0100e8034513684811b40b0980541d881d950080100c0c010499030300300419580c03078501413284070f80c4421100580c255180721a40b03180d80c01c100f0500c101115082c22a00b00d4202c4c040010014140368000c1c007086442100003500b820081c1d40018140c4800c1c14401e000c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 660140692 1250 660139442 660139489
    0x14060a0938070302120c12040e01030501050f060a12020114131e0e040305071b080c1c0b010302150d05010602030717070302060601050c030c0102040806150a061e0e 72
    0x1aa005521090449150707080e501c146032a0103035802a440d20038030042c0c8810202c0201d0a0181d41001b807104009182c04202d440d55035030344455401161800c20300040d100c6602c6d1000060518519050641c0541c00007400180340074076004840300040e00b1604101d040040c1e1340b1a030041c2e4610080642803038455401d0b41528507040c1207004028414008d01003441842c01102009003000740f0107046e0f003168051030314568648250501e240141d1910041a2a91031804800110280003040801d5035000466a601e01148240301d0403180c034000c040d014044116a2004000501e130822583e52041001d0302c07180c1c00c2900c0d1245840880d40300340d1202015810005c0e60104124129035084038180013441000e08140060300c0007982c40c04000c2c82d082c1071000004200d01c04010800076101c103400320000a6541d1600d42030655129001900d00c1e1924103044069144c140c0b40495148003501c40c81d40c1c031018003000b000f107034003c0c40002400308800c0c041000300c101110380721910110554400540c2504 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 660141942 1250 660140692 660140759
    0x7090504060b0f011b030e1512091608100e010b060a081f080d030c0216081608060105090a05062b030206010b18040905011407170a050114060a09 64
    0x260f034400c0c81400703030421001801e248541c403d80514252065014588601d04003000c1002c268010350b0300c00c8804d1440d0001c510842c4000080ca103892041001c00150340c01c4052021032481041c3c0c180c02004550f402074140c40941e40c607c0c1e070011201085000010408000010114260782d00c59a040700c0080e10030b0307040003004911800030148490000c008440001d1030803480b1501d8a0990340c95100f050f403141020110a4803c2008152129940e550311040300d84d03c070040d41d41d40f5000351740f014050032541000900c03250080f8020b4100c510181803100107944240004000305001040031b9409031003078146d0100c890180000d1900c4d1540c0c44100f4409455500300a89070400c164804454204100582d00c07442048081c03099034442c06540124004141c1d01d0241d024000d4078161a07003e032001e41c00c004555034040c0c0b11620414000742940560380355070107079601391002402803a0b0b030303204141440901e0342080301c000c0110806500d080103004c4d8844040e80ba8108410078400d0440182d0300840 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 660143192 1250 660141942 660141949
    0x803040507051c0209040510050c09090a1512141f1505010f050d060305030c010203160201091e0809030d0806010906030917030c040902030106050712031404080a0207090504060b 78
    0x900252404543c10700c100340701c50001c003c0200150000902511704c2c42c0102d0304000003000070085c00d09240d9000d00031490000c04042941c0c01c2074446e43d10820702200803130f08041c0795105015000480301c103007186090400d40500e074074021a050480f4a90b41c0c107050417400c1e400500c54541d411810810340c0c0e10612002210000b0398601080c44d03681400c050204200580e0050201108880341e800c02c079480d524202c42c03020081c0765661016107180400604007000241c190700542c81000c0f0203944500c2d450070300344100d0807a18500d500822075141c0c0c1c074905022800c4250060340c101e12400000f46402d12490103e400c0c0048030f4014000b20f1000003d0000c0c640e00172551401801e90791900300880c985a4441341104c1083e009800450381c000801301c4e1140403210221806400702400c10356895079600300042041e4090402903075030303600d400001d4510303a1180c0502c180d0010111100600741d1541d440d40001a800003580e8001d5201e0750200041901c1d007405940d1049010381000242c0c0070001c03007072 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 660144442 1250 660143192 660143203
    0x5070f15030203100e2211030f0303100909111e0906061602040b0619020a03020d1407060e07120c03140114070305060d0c09020304030306140a051203041208030405 72
    0x2001810b0060041140000c131a8066070700b00c030504c0a490540c1c2d10780c1181c103507908242c0220642181d1043c1905000d0210340205a01324030820743c01c40b104102580119926808292021041c4146105080100c604c00c1c1e00304280c082d000c2c01c40215010f100c1c1c40000c000608400c60106920211142c101852410000b440d41c01300003920b01c0307460058084544080750582c050004d20841da5085020900d44038081a070b0360905100d240c908011100700d801070740e0745802803c00c078011b20a04080f00c00c1d0310303c0703000003007081540045900c0c2000e045ea61568040d010008190300c2c148103072170000030f941002310300310ba1440d030041243d04522403c5040c0401402003c4d8010740c00b986c1400032007410030915045656110031945800030700d40d12600000340000c0c040d2400035100796082080820070700101e0740118000c500c203407410048990b0f20760301e40e40c2c0c41441c000c1ca6984100070003010071041c20078040d41034104541c241520310380780d25007000081d20502c2600c160350400c4048208010484200709 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 660145692 1250 660144442 660144479
    0x6110d020705060f1804050c0d05070c0209060112151701060b0a0e0d0c03080d0c0e0f090a020c161d0109050f041e120e030d08160e060705070f 63
    0x1d811903030306081c0802e01920034078818210802c80082c81d0307100071074102031241d50140018000d008906055100c0f074829004a00003041f0b80707182c02c000c11000c5000701d00c40c0706000d6000e0600003403030369200015501d1003080303404103c402d074644103412403100842160b1000380195190303e081600c1040001421a46d04c1d07003003078141140c00c00c8200ca06c1500235240320000a822500c0310510100b9180c0a4160343c800d500042080c0004203075020b505030660045c010134851135440d81001d0410204200100d90074102c46600099003070041040700c12150001c200d0302d4039100407240311054034800c025100e4207a510031550414a82510600195a401050700618030348100384540d051624041280305d0b40584010003040d002215404000700340203000e00c8031a006440c080960500704409401d0301181c00c11a803090141e2000450307024045d1508902a80c281341302000c2c11402a00d09a0b40441e4006001d0b030b004000f0f01503940011400c00001d40070340100021220413034a4105031b400e104850f0071 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 660146942 1250 660145692 660145697
    0x8091e070612060b03151203030c12090d0f1d09010b04031718401506080606090a15020a0b0709140d03090902040b0301050a05043e030106110d 63
    0x350b081010070040410b1300c6d0401c58000d01001130508450004481950301008900c3c94000402040300e0f8402080113400e01d150700702081c40441c1c0d6014001500d4260040c0f50102190002400b4091944a12454600c0300038407158079990680030f030000388280c8000d0b8480c2c204e0000000d400c2c000c22042086841010294030980380c00c05480d2950f420000c0d0f61103c19034000c100c9400c480307480040480b03a0040d0308a82c240614003d07112058980c0f4014414118007080c5420030800c406000c1140342200c08136200d5a4413807201c1d4a0300003c10075141d0298444980c0f010340110086441c515000d520803180d0000d400404820038640340418405200500c07401c203019071403c0c204140b07403040d1401c1e8005201190716040c100384525055400e10a11341045488030720202e0301040c0141c0400c001d505984084034500300300707540d4034200705c203403032041c15034040301c041468094512821552210f0304a64000005041d0100d00c1340012101360000d178020400601c011142d84101c12080c40303500d41510a91 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 660148192 1250 660146942 660146951
    0x1080718081501241d01030f0c030c02010b2d0a0e0f0f070e0a0b2a01091104201303061b08090a03050a1805030a0303060503100e070608091e070612 65
    0x6014100911503060081c10914580742c40c103051f8441d031b1041401c1d0031904000c01c600850800018004c041c0d40300204003662802140d1041860443c0c6c4485944071701124091020b034080f030b0003c0e50380d07805603803483e0000c203800000f0400704d0007541003c1c859002500c58541e91316144506440b40705000e0010b00900503419080000ca880704200c0205947c2703402e082076034800054080030305000120b5400c400760129a0320354480c0c20310640100341968002c020003642d8039841010003044540d0380390a503c9001d504c201807000300b0407a034040c04080645900a030340040d580e40b20102a11030003503e11492001956902c18055041740c3c00c0c94110b410540241604405550040c0c4680309591840050102d500311801e41001003449200241c003001d400c0d124481a40d14003e4081c00c1240107861003030155000d10000380149116440303042c1350f5840207043c02b514105003511410000341800c0700c580984811384840c0007403115025004090346000305125444c241009024507071006401404a040 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 660149442 1250 660148192 660148259
    0x50a030c031709190503161b0b03010e070e012105010302041407020a23030c0609010507020a2109120b24030a02040e03040e01090b010207050a0501080718081501 71
    0x619402041e4540c0d482842c484e0107814028554081c0d2641080560503608040081190250103004104494804400000d8440c10100c2c031038002400b42280b61404500007501561080e407442070180410f050000e2a03540180117400301052070b90380740b00d059031035400401c00c5080034400c0b0403003803604020900075420000301c025100e5401c0074010301030700032503100640b180d45d400106013001010801201ea40d5100c5104032a00c4d0381040755101e03515441d00740000e01043c00400c0000c01d03158806186842400c40c6d01ea03400c3d040020401c02c2007049480340c00483d111050340f80450182c0d000300f41c010307424600b0f11035134980c88130b4010f40758084409140c4000e105440014149801e80ea040b00c004c81c004403403a00702403460050307230301c1003807942581000020768507155401962400003e80c00d5031900750711201170000030701c210320625001440b0100010f4000340b0541c110404907030840e2520002c00e540c0d41704103161961004801201e1403541004000100310300c520500340d1020281900b555004 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 660150692 1250 660149442 660149461
    0x5060f2a091813030c05010b0a08010f0e070e04031101021e0c07060e150c1903050309120304030f0e01032c0601090908040302100e0a120b0601090e06040207020607050a030c0317 78
    0x903c100c02000c2c014402141c60400200f9007080304a4000600b46030200c6640380d440a0290541992048040e40780c90b8440c41c841d2030104e42402920300080b40c0100070349139540d00b02c2d4449000248201155400c0c1300e0094501000042c460400020212803515002c80c0740d241030415080c2d0b400541403120502d04d45621ba1103002c484159441d48082154a031005a403e03942450610003080b404150210441410150400c01a43c0075a031040201c5040190368109141c1c0b5120a0302d018002c144958214a5098030655001a0460f4185001301d801c4c50088002c0c240560840221103454030003500840c11594100002c6006202c0090144098081a141c030000c5100f5400040d008000c8000510380c03c44c040c13640c1403941c80f005000010007a590720071818030307416090320803548021001e020a00c02e62040b0042c1054940c85407102d00e2903211801084029800424100c5c0c0040c0140542008a10284401e4113194080d4803004a01100b070318008226901000350741c02e0245030340050212940 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 660151942 1250 660150692 660150721
    0x1806050a050f0114010905090109230c03040602210412270b07020616050a060506061206100e0d050c19030b0a020304060b0409061407050705060f2a0918 67
    0x2001901c85030b5112662800480f0406d4150300200d411104a000014042c019540051035055484a079094102c0c0c1110551443c1c0078240d4140500a8041c001300e030110700f490703000384040c0d0031030641803c2c10070911484483e0807408071400e49001a90311030b000728090b0006001c0c05e00c0c07041103403c1040224920718454004001d8080ca241c1307030401082d018210744030700084810f1410880400480403089203080c2d070380d0740000c0c0011154282083e012448505081d0141d901030002c02c2c02c2c6610711703a151014401000c44600010302000804502041c00f5110007080410341402100a4090080356000b0301c000c41d03020300826094030f44004001c1001c5a400c01c0469048503a155015070703070b40c5881c01c003040a00801824954440d00e81380c0e4032020011580c0c0b080c08041c6000090700e203076580c1c1c0c0784150b4045c0a000006840380c0c06c4840081c881d481c2e00e01d4190390259104212160314080480f0282d0007001e28000d0b0b00700b2084c0021000c9451a091401c503240c1103d08101d101c0e43d1808410092210 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 660153192 1250 660151942 660151949
    0xc0424030b04030311070f020f01050a0e0d0501060b070c051503010617060105040b0d0510090506100c020d08041e08060106051b0a02120a111e060711041806050a050f01 74
    0x2000404040742c101403180d0483c0300c0c2d031100070b0912a00c4e007501e400d040303401d80c1c8010000c91180110221800195026400b911038080d0f440c0c0350b103040000703038200b03110500b2540e0000300c619550b180c00220325610564050000c06000d00c0003030006505041c24010740ba00b280c901c6000c0349000780010015541e225800414280c804945918552039800059030180038a07080f411010802159086c142d90040d40410f20030f0600c8101c4401080c1d41e00f52403011100c042d104c0980241307200d10b000c010319001d2281e0909841c40a0b1a030799036458075032100c020740e40068101ca48a084441d101031400700ca01000a0041d000a07405004030354501200a00144241d18014080a140005400014100740103182c2c0541d000b80c002d205045a4450342a01d8840240045881100409042c40d00d8100745e0aa4000d42c250050650030010740c001c20016290040b02e4219491011541c0c400c4d010b4403030f400780401040d01009000907001d0149000346c01e0b54030080190404926040800070000120309071107044 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 660154442 1250 660153192 660153203
    0x1b12060b03070b2205090c0a08070806013203041b0b0c0601170a0506070207082e15080f01140f040308010b130801151a16081303020d050c042403 64
    0x602440340082a004c104e80d4030040d4881284000c200c50780342d07288018502c0090541e980740c1180d40707503031050701d200e0f0065616500080c01c451404424040342d03130b100c441c540e40720040303421510300300d0804e107101d50b00803101100d0f0081040704051905040a038190081c2c2260f120103030525940c00722071940e40e04140314024208200030b0788010102c0b002d02c5441d44803500075007507030054a01003074042d680d1082485241041c0c41801440403848004c9540c1c10340f20000707800720075a95154903541d18040c0503041c1c1c60716040250f4200004441004010001100c25940004500c8088616440500c014000c0c994400700500f00204000258001311407070540b0380c4404880e86502020300780b000408000d400c0801a5031a11014048000d92184500c00700e03a8116181001c0b04000101600b032402145242001511515065800924018040c0c024411000900c00600f0307600e4000601b030300800750041c0c513a034000c0d00040b0b81c0d80c03c01d400b407021804065100c400340e04041883e4020801000d1002819 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 660155692 1250 660154442 660154477
    0x70621050403051c060509010609080312071e030e01110906070201200a03030902121204090b0415090b040e0d17090a0b01030b180613020105071b12060b03070b 70
    0x3018000d10a0311090713180d000100648003280030b980c50003004103018841c840d034554070000030402c1c13061200c0d6080e540c041e40a14204440903102c03c124000c0a0300000a2120949040140880c85814128039403a40c0d40e01107441824039082e2030860b55602c010a080c80800c01c84050b40342c88100486074181da080c40d014405000d04c000c6415010392814004940d80100301c1e06800307250f85500140c03603186c000c8440007030003000307002c1c02907940380d140003401254001403000700038008803a4009a60b68102500c0030810011080000200e1001500305031101c5648440d00700c1e03a4109440381045e05541200101952040d1000c0a8441d9031007180380c2440c41e150b60700240c040d80041c01084d54141c0d0100036682d07a542c40c4d1502d8426840121f0340344808072012040c40c40410000200350707000301d00358440340f140f00d4255001110381d644091001e44042d0b2800075040c0c41c0100508405000b061442d12030760b01c02c15603103020380c141d483d0205541c5c46640b14540a2107041c0e00081250400d2403260261003 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 660156942 1250 660155692 660155701
    0x525030309060f1218020310150320061c0b034204030903140109020913330605030a050d05210a09060b04090309061809050c0a0207062105 61
    0x884883c1c03405a402c0312207041171320307100310a071003d20714030700c281d2089050383c000f008400c0c1d002080780c0590141e00d00070101d0f034504101080c20a504c1c1c0102c003074560071020110580001080b9140e12200801069400480b65a1044c407200d21801c400f00d070044001c0e001b421181c3d400381441503000c4054038081c1d00da038480442e01c5044450103202600e0100760750b040600e445e0a011702001020702c8181d50004c0e03214007520640c0018455130043d20781c000c1000039180c46c4d90600c031210940032a000c0360f00070950050385e03404102d64203881d8800045118140d014030904074400080d1103441c0c1c0454080d9221000500c0092404038401c0c8049030107103005a150550712020200150300301c45403490314040607050098001c003a800841c112030041c002803200007506001c1c00f0480d006601c02a0000c0c0702c5080611900d4403031507000e1110888003592140d0705072180d2100c2c040350000c1e1030314a44400006201c160080c0c041c000c1174014a0799080610009048600301c0342690000401c18092985d81c00004 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 660158192 1250 660156942 660156947
    0x303240d1403040906080304150c170a1101050a1d03070804050609041b03060303030b0a030b041401230f16020a0609080d02040b030615160b040c0806040525030309060f 74
    0x10b07002080c8013841400300755034420358a600d980c014080e140ca030101e040d000049040c000d01100d8011580540d004c805042a81031603c000e803c031003148010400c0c03030441009035080c2401410300481a100c8000341281c040c03050b00d0420410031000301d50b42d410522410300031641c0101918201d0301d05880326a9602100760019004040382503803284581500e80b0500640c1d6030581c8000162031007900d0800540c0c4100d4200281001903120003002d0380b10360400580000d41c4030f1541d42551920000206210b540009242404004400da203207941001e0030030400300d8540c1e01205604094000240350b042680c020009445126810700a0b010b540c0701d00d0001c04015660b400c0700c0152040715000c40d04c4640716010780b40b15500a40e000c2d48030390381021411000040c00c408940c240c3c60081084008d03420b0556414a0f0000010301c1901d0030313580c400001440320410310480e03114078403400150503412303c0b040075101054203070a0311107e0544803180510000c0c0d0880201c034280c0c2c4190038002e00c10403510504 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 660159442 1250 660158192 660158197
    0xb010e01210903020303070908030403080403061d070b09090a0b181b130303032003280507030516020604030e040504081902031305030a0b01031202120c0303240d1403 73
    0x1d210400346040060028140e0100c0514080d20207070351480600d036a242c607059a00d0041340001ba01b914002c000c20400180f90341c0c498040340d203003916040b020408030031440d82808010b5110003281c503c0019842040d14107411066400506640b040081d0701c0d01001180c510000700c800d01002081500115402c0c8010f00c1e20010b01d410507181907661707005041c50241c1e40c42080d1104801207420031020360680080701c2085213500c103596072814115903400c07140e6642c5011510b035200b04010490b00c40d10385d0110b14003405106d11526140802c840c1440907170b0f4102a0115850355046411940501001a61215060b154404201c50214140d1a1800c18007174902c0713400c0e44808280e40b012007540009030040041d201c0c0800d2000760b02c060035a070708140340e00e80c80a030340018100b030394a40040c00043c071180c1c0220521032700b92045a890f90010100000790368046040c4c0d000c640c0c400300c100170b4150b5a80300310a4100e0030361082c842c001c401050104401610804000340044038000d07803482290410800e = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 660160692 1250 660159442 660159497
    0x9030a0501020706140a05090d050d0b0402030a150b13090b010504080d08040201030e010c020606040f02041d09010501140f0f0121091b03080d110f0c100b03010b010e01 74
    0x2150ba643c014039024000340442620021761890a40c001544400244503151080e11103501a28140320090000c075803907484091902e10b580d56502080c02580c41d82c1c4051803050300f486200007203c40714220302c030403031060550110aa0311420000c502c0c1c1c1c3c100a041c00003c9400c0302c58042002003110005a40d140035076017040b6010300c07079521189007203035104c4070f900e00841c000e03242000312000789041c180c02d0b00e0310300b080040540e00c082c012a0843c10154062035410b100103000504094071116000c03c4011841d4101504130b000c041444000c08080c81941e00401889019801e4a0001401b0a101590742d05010384110b503000f090480a034001ca42e00c105940e00007001c030040c813008034585001030840420a0301c8a540048801d98110440000d04050700d42002c0c07850b0406011191100c09880003041140440704240400c1d035101c103140c4003510014040c20050811180c09500d070764110b44071010201d00c203038104080055140d80090a02c1d94041c000e1170001012507860904100650201c0d0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 660161942 1250 660160692 660160703
    0xb16030807200a14030a0e09090307050d0f12090b04060b0a03120201020d1b1709030904020d0207060c02070f0923090321013c0321080112060209030a 66
    0x291000c1e141c0b02d001c190400a684a00b091542c1c1c1445020595504c0c0606814080455030794034402c545494001c0809900280c5c082c01c9030300d40b000c50340e91503040c5120852604041046c44803090509038110f403040480d401d41410400c00c4c0d054a488141501001400141c031040c0d66680ca43c05584a041c1c041d80030b9600710b10020000c02000c0700090003940300d001681c4069240800c6c280401102c5240c0c18083c01990b5100c58481c2581400904840c03c041d040b1030f440c1c441000f01c0003c030317200c0d8005400b44c040d07111801a03da6180e81484002d40303030302040e00c0c411904401010b2294041100d0044150380d140c3d080040c4a00d01100c070320440e15910301c4030782e0b0030503020300c20040303103020010003480f480641a200c9400c1154405030307241c00f4002800f42c802e6010004207000502040050140184502800c178402d00036406411250f5107401c42c2c0007982da6091009250001c0201058a040030100d540f4101c11103600d4104180301100310900014070140d00051b911540d6501000a4101540c002 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 660163192 1250 660161942 660161987
    0x2a01030212160e0a0b04090b0604030615170303061e03010f060f0f05010f020322053f0c0603070203041814010e040201050a08190606020102030f010b16030807 70
    0x40302d240c1401c84000e803042d40007803030300003c610040c10031038140001c03507101c1d101c1c0c2810702e4180682500a040c1451721250429402d0100002161076805259012003141005002c141d007000ca16210703030f0b0509054030140358010010f0021540701d210540c1d41010740036052040c038160700c0d000a40940b5401500b4150740781424000310b20b0715000d42d100c100319000f528800e00c80ca940c4034015610314680381500800b580040c002060b200720300150010dc81c481000501403d140c492000483d11112003008210900624180c25001e00d25041780a0004a18249000c0c0504551a046658818520925000740c070f012011485080c001c00940700074004429100d0250111070809034004c0181e21146001d800b001d400001f049848282007a002c0c0c2d406942d0346103404400407054841c0c03c1c2c06402000780c10b0740300d403c1c2c0c0221030701c91003200081c1015a00159503814800300301c1300c2295040c0c21122414104010034145142c030038401040055040c184100c0307a648400341a510321450a03407429011054 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 660164442 1250 660163192 660163201
    0x414070915120c06110703021302031f0f18060b1c050c0a0e0405070c0203060a02131a2505070f060f030b030c010e04091a0709082a01030212 62
    0x10341001900c8401c08140405459450b100b0414a025421010b00311032042c0c0ca05115440c4288448200d04000c1c02c100c40c00c1d50303038a40c085807a10003010a0000036990100500180c14881e203c0c8030344010882d80011446030420005840201705449104264109000e1070003079141c1030b800100c014682158816218542d204001800c21482000400042c2c600000103040310547c10075079001c1010381d40c0d45d1190708141002c3c0001400007624580c00d001c80007401e000107903410844640f0403072405002507254900310303801150b1745e00c107600440e9507404414004010004001700789c81c0c94400c084642c04a17a00043c040201402e102000505240200080400d6004081034220200c0d484bd41d9400511400040c0c22821038413003450b1598150000f11088959600c20010ac00700c80354004d000259518050f5500700d615002c21071031401c848290300030007100035000341804004148580240441160201d5542c498062052116000c101007428450301640320b68165203154a0038107449025081 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 660165692 1250 660164442 660164459
    0xe040f06060c02090f010e06010507080706150f051e040c091206020403030905190302041a121c0c080406080c040e0f0610051305090703020f070c14040504050c0108041407 75
    0x641c00306078041c00035040429205d02004507842d040b141990f481a080e80c55200044075942e200a0703054640020500030b03180403402030710034003035402c2180000003a0b00e4513050304207030b00c0342c1d40d40e125500c24004501200c3e809401420b0700700c20303070304102d8000500c0d014580054407004015002050b1800c1446509401c1000781da00a1065034026141e105a1564039000c10a1500c542d8901d83e0784807420701400c10050400e5005000c003080420f1007032443d80031520201d00c0c040260682400030354003070412164441300f0406411a18400c91501941c00003e81d10707400e08078800ea21a61040060210004146d00030107070595010b0904d1043d81d542d1414024004110120140d40d42e07441003501c031004031201070140040702c1c200c416203142140c90b1840c22080100a4500420820915808000b885400f4014000070450144600d0700c1748000c6040c04072186011111820844c003a0b8501030a00c404200000385200d001c04003440d1a100c41e60310351030105030000d50b107402014184143c0780049270840 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 660166942 1250 660165692 660165707
    0x17030a03140903160819170105181b12040809030114100b0d0b0a06021b040506180a0b1c051015060810150302180906060a0e040f0606 59
    0x410a950500c118041d9039600d40e04003400742c407418074690041200c4c02d080c1085403448140c85000b540c11030705044070b0310310644414408410f580d00003503400703142e00d0341c114268085601401382525191084200844403126a00c0301501c45120024541c4102c21a40c03010800c07140c09544101c940011410310b49080c84083d0000440729200c1e50070000e030011080850490144122aa806c484024034505105010141c1c0650840903040351160444c1d141612601e10803c01404035070700500d80010019a41b003150980d81a4591189040c20240005956101c4e62141c9002031011710b440c5a40b10000e18034010a6002d0249401850303102070303480d009840f0ba40c40c004450140095a0010203008001d0b402c0b210342000304940540c02e0b46003401494851030841d81d010100035101010700d0380b50032030b51003405200c0b41c2450000703400041185864204089110001a06449503c603a0070424001040c0713000b0404610108403d4114944807070741c85421543d101543e0080400905490310742c001d0031070 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 660168192 1250 660166942 660166957
    0x20306091303021c030e030408061e0705090108150d0809040606020c0306010e07110a080a030f140a02090109051302091002031e0d060b0c1e1209060d061703 69
    0x4801440c00107080700340800281c0341c07903a81070f8064416194841001d010007035503030008034101665240003814007a410001030000c0c000c02d60091034146058424000c0303124000390358012489020382803001c1c454022066400300e2409082140c0d29955075500c043daa00050484950701118042800c014031031030b14010f0000c4401900d09100080d00c4006c01d0340e42d02e5402c900f4940642c84000108110b9500380400c81c0c0001340c1d0f1034a0310030710720a021000d01c0c0c50340e41707034007610140d800240d441106605886081c0724074000704814801c16410303100c41c0514031002070021031441d40014502480760700c01d0910502038500244699031180150640c0d00c001d400c940c0116008132034035002030a102d0b000209440c0c2d809041520014214521552481150040c40045007034544403800070035030421000107002d00c03502090081c2030000403003051903003140101d4070003030f002e4000f003905a00c41034600d41250380c01c06007034641c22360300e00d0103941040080c0b050703911800707034000e14280c9040d008102200906a4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 660169442 1250 660168192 660168199
    0x90703110304060608190206070605060604081c02150105310e0c0301060509010506030412020a1e030206061e120309040e06010603050a271104110d0e0319050f0705070603020306 78
    0x5444070ba50f03854150320032004000c0c8d44000148a003400265294110540c4004082e1080d8140f076601c641e150b01e408011a1009000301c2411014020b0380d42c100803000c80d25690011f030344215450301010400203240d541c0b4100030115900c540300c4e612501111320f00ea82c080c080b5000c000c18040170880644608001071803a12035401d040c400903551500b14903036030580340d00400042c61921190741e0340c42034401ca0861801540901c500c0440031075034020b4407a81541c201315045800c00c0031031400070300340100144064840c42070f01202c0743d40540285403038441000143ca020380342c1913948255904c0c40c0511515154002c0c28010b0ba68100000800c807513040318402c3d1810702c0241c86003401d0000769504119000d96540030305105000a0101d0f21240ca003950248200182e5100d944000c20180c621804581c11464400111304451400c6489100f003071421020285081120607081082d41c0300e0051280d0081100110350011140400b00032100b90640c0034044a401955415010f000b9400843d1074510 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 660170692 1250 660169442 660169453
    0xd050a0b061317030403030f050d14040c0504180b1308041715070f0c060902061c0203070e040204080601062607090330110309090a0e1e03030105090703110304060608 73
    0x3d0040c0001a64142c9030316448020b9000c14821040711990031030070b80c0e00401380d00ca01c4809071401004440c1400f80d03000c0c40c460304085090038240401d880c0c800724000101a40427222002241c918003a25801c8501c03031502d8910340e0402c0c1000d20300350150340c000c40161000c169640d2140c04000424844807a001c4000324101d5445040c282c5092a00f950302801182e0000001000556994001c1c0600c0c0d10090125042c1041031080481032425880400c0075254000f01740040d054200200740740f130b020215411740c40e0500f484005501c40806101e00c900340030054401c3d146c4000d510306901070200116103100041c1c901440c004120806d548000c0e960b1641011640b84480f02d0712500d498513022540781580e40180c01381007100c2d01410000d40e8801070005220040d855624008080e00800300100f020412401e842101418480350001840c1d040c4040c00c002400044080152030460b00b08540c05006981d440c04150044c03c07118400b2214440c00104010810116501410603500518120740 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 660171942 1250 660170692 660170729
    0x190b2d0703090503030c0a060c0309061503021c150e0109020319020a050a0e070f02010b04110909010b12010b030601030f0501151806020309040207060605101e050406050d050a0b0613 80
    0x51700c034819800341d218143c100e4903040c0082869900f00104080d96440c00240825140d12103074210341600b440d19200c41c075030000c20030540c038201a080310126814001800911000ea454454180308480078070b2584c4d8070780010000c918400c2d40440c3c00244c001d403e558040e140204401440c40c1141070413445032111080100d01801c0400d034480c25160790050217601926540400d4035074400804440c41190f40b038000301c0e0910345490251b20610600005815182d0b0840da04100000d88140c0003502404802e0203074441414503544510b0448110300d82d043d0740e90716118012400f50070700c0c502543c1854100400043c0861503046120344080c0305958495018907503e0301040703101100e208200060740248418052032903d0350041450910503540000c01076070700c0c0045045d1000615014000c241c0c038951003111040b40d5002d5500307184180c80c095243c01d040c0031001d44140181c03c2095851952400044c610007901d40c401c070b10103c0001c00903034880580c1c035265003101059026010f1008450605c00 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 660173192 1250 660171942 660171949
    0x50715080f01262514012f010203010e01080105090706020c0f060714030912011e0b0f0d2a0f030b070512010803070b06190b2d07030905 60
    0x290091040301660285070b440d02e0b2080304605180d03200c2c91010301c1a060f600050a01c00c2000c40588900398100e41010031000484900d591820f030301c11203954800d400e204240340c0e800140050007a04407804c240c0745c0d01400e0f9240e0700c4010030007600102c1c6c1d071001002041d15902c030b00c1c0311412140e000e0020702269035089111500c0304010322031003015030700c2400c08064511388a02500c10307000d4050141ca050491a8503529411f00b0070104805507a040041d05002500b00b2490103240f443d40c070302c000d000a0f41000c0d44084404400c000c100100365882e012034400e955881000d0011000042081d0b10000d00c50400c028030306555140c8440e0b0a0f40c0842080e9201700c804c00000c1103a0900240d42000c0d0314507114020413080091030002040740801c5150504c2d044101c4050280c902000216202c50041c6061071500f903004c0c28680c400e03004900a991178040c0c903240202034400341c052041d1100003000c0e1541c03030003203a030702031102c1074000d00c2d05040c40f1110a00a0010fa60082d9646901c81c0d9a40051 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 660174442 1250 660173192 660173207
    0xc091802090601120905060f0402030d11030307031505040f140105040608070308090109050a061e030218040c020106181e0506090c070c0e07020f0c0316120206090d050715 75
    0x203410040c03201c009a03a0358040d01c80d5101c0d180c42e40801082031000b0b035a405040040c00c80384c0c4011141028244070641c2010040104010301c1400c0c2018010000a54aa0340c0d0000411480406480d032548085401003850200000c01001d002404078801d181911000f0f010045c81800b00c2300304c030342c00000341450300380501000ca5080001030700129003140c0715685e5580c0006405414803005500001302522103280700802840640e4403d680b0042c0c4e45201d540045008210b00308050051000b149000c50459105540790012500060079240d0040700381d000d08201d5000244031403084400c00d42903441c581002c1004041451104910246101c400044981c06d6442035003108021001506c00000d0700001e10803240622030001c981a0790706010100344104440410060b04008031207203c069082020010003c070403006002d2648540d4014004a140c074800c0d02c0051229503407000c1591220300c00c641070b400d4040c041d050021101d04009943d003801d48615840321400394003048800f48101c80 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 660175692 1250 660174442 660174491
    0x90108100b0702090a061e090b24030a09050106090b120a1a13050d0c1a04020102062802030703150e040b0112021336021302030c070c030c09 62
    0x685030306059683d000d0018020005005d541c1c546d541e14000f003445481c0c0202e00800c6050780c051a803080e801d02039000c06543e01e880300f65004446c3d6005c512100d0820020102c043c0c103400003d25180d030f8511650300c019000c03914000d006c0d0751900350041201d03143d90300070103900d18040d207480301c0442034104a9580ea04981d48007400c10160101c603500040c07442c8619030380007407892095481c02051500c1d1142400101111040496040d48101007000700c0706c900702c41003006040341c41419141680002c0c1d00c1d40c4000b08145c9041400c800e0080118000c20069118141c0b0a28115102c0c40c0180025004065a410300a03030301040281c0042c4011110f01c120303110b50351004149085910701441c50000030800032080307a02c1590001128851440707072250428503d0720113800d024403600144c405030307246031480c540c1001030f19060280d005a21064400b0340c80c0301c84404016581daa40301c000307a00e140101c0c2001084082d0500000091181c4d9004010544614150401100e400081034807800070400340c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 660176942 1250 660175692 660175709
    0xf0606170f070503102d0b0705060c0a0c050a15050c130302060702060c06041b050105041a1e0a03140604060312030b060d02131d220804090501090209010810 69
    0x2000034000350f1090b406150806a054079503400107440d001e103d40515054200d07100c41c1052511526400405019050014440000f000e40307002c81c50744034103440d210300900c0d00410000c0024000c107081e11807215600b0503034100d025140303000d10038030f02601519600e100c503808007400d140100d00316607841d00407241a901c40755080100d140c603507401d10000342c1001c87d09a034040303428407100000000c02d01002e4821071049200528604405620031410040d0790000741c1080720a11081c003402201c8070301c400d61040b2000390940c485000741c2c0060049021004112054840401d014a050303426401584041c0301c400914200b81da9105c09202c1114801e01c0041d000c480c100700c1c08034030039000390301140b00c08202806071032401050444c2803081c2d0b4000314100000d0f01c0c10b1082008404045448900d9808129014488900b88481c2c07124547c55450b02e1450741c5c2d07072407102c14410400ca071802c44001b0101c1040501c200d6944240e04d0009400c4174400700d0110704144000340400d55000b4840c800d444054 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 660178192 1250 660176942 660176971
    0xc0606090726061801090c02010f050702030a140f0c06040605070305041104050a110301080a0b06060f030619031203230f0a0e070503010207050a05100e0714040b040f060617 76
    0x500d1001020742c0301800a80d00310032504000d501043d08080b50754080c0003005004184101400c0b002400c44001c0090007103d60b00d004148403059902200f1504c3c2100c161610a00f151440d48110740e0611440484c0c02c2103480c0080d0481e05e4180108003584518010f51007089950f803540f07070980507103800300d40061061000600310b48491403e580240e400c401200d0b40095683c0f841c10500c01203500a800c00b510640c00040303c0d20030040c00c8440150b104605441403030600e00016404842800081d00940c40303008000800d0326100748510740d68004641189410381c10407240c1001034001e10298400d50f01d80520211505018807900106d01d0107071500d010000c2191340d4001c10f28005161001110500e40903078100051103540c00d001801009000c0c20182668016a10b002c0703181541e208100e4000d40c4c248817001d0132241c002300740402180c01040f10f01011500c607030002002441c4080102d0303840f5240003030004820500b0b912007000d40e5981e03190140203041c280c1014000c803404440000d180c0045 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 660179442 1250 660178192 660178247
    0x5091006200c030d020f0127080702180c13080c01020a0b1314032101030305160602210f060d1e0c050a0311010206180c0904020a05060c06060907 64
    0x1811640016541d01016200c2d00210200041d0a01c0356840420340140e00501c0080e042400a100703504800300c1ca842401c106004414041ba45050f0320310000e408450085200802d43d110356410f080080b0308038a5404007840c00060300c12a0f07400c0007035180d007013800702080802c8003030001a699a642c0d905800800e5144200c1ea500c42d4900401003200203035040c0c0c40c0494000608000c140ca00f20f844240107152606540d03128400101195800c020074940141d00400200b5005411104107003445104000c81250504010001e442002411420f0500b0400900c50031000d400040c2e000e421404025840c0303448903010808101c404644c00740103422a0300c4848500d100762420045040d00c10003242c4020755440d00014889081d40d1b000b901c41300500741840f480c66906221156002c3c0500b010080702d02e00703007096907544012001c0700030701507100c00001c901035549150140e8010400102450354408a00401c96103502c401d40301c840c01751001d4008541598020080c001c100381111810400510304c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 660180692 1250 660179442 660179477
    0x6012a030207050a26120714010e0d0906050703090b030721021c0209030c09070507110d15020a02120d020d0b09090a080a1e082a03010b2a060105091006 67
    0x2001e80d5040c01500c100e200c40c54461501001907c800c6004030100c100c0014050758650030744401c1e400c06401034104401d460001600503200d07a09548072450318a844400a15041c0c0b0601e401780c100c2c04080c1c03400f10070070050542c0021f8401c079801c0b10b42c4103000300b9100a01d009040e170040240402014006600b4814411180e50240c1604c000040480e0f010f072100380e0210f100c049086d00c5450008000040102c14003441c42c00319400b07010107447c2d070a07601070252108004c05124440000350356400044031170390039100f00101040e640082801c980e40e070318211104002980441700600d006801c0091101d61890f04c900c00c24031030350144000d485841c00c075541d040c08a9102421300002d10600f80089032075a03818118107000071106884052640c04d000a80280c2c3c03c100c840c1030398001c10800c500703140c10052001074a04484010510f691140c4d44c00c040c0c020401c90b150001c2c0302c0311400300b0381c0401048002815a048480944032002551641a031f80c40000c50540901c3d000304546010600c18200c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 660181942 1250 660180692 660180749
    0x110c10020106030605150306010b070206120a1e1a150d180807050706030b0306070e010e01271401090e1f03021021020a0c0b06012a030207050a 63
    0x28a610001595a40b00d64500040390302c1500c44103401c3e51140070042c0542420040c2a001d819501d1146051004680c002455480b440084211750384402e0081902602660040c09407940440b21700b588010028203c0802804401ca04d800c0c0030484002e6680305080841803a002d40d04000c40c59407a0000d81c0c10004050626640348510740c00311140240003050b00480640081d5101e140030302440c620b01070000301602c00d00b0141611a0704064140034140741c00c210700301001e42c420700f4001345041401e00140d58010645040c00044401100060700201c4031081c540c05481a030a20424480f110000450300f86200d40146480340045d1000702c0c2e040004400c920003034032210010340314240e0f00c0382d002c43d0905407000e02c9003010905030308465200885481d51446040c206020860524040c1c610003031012100078000341c0080f0340403000c21281e9210b01c0700314084000782510031040102144984a4250000348242d005005806000c2010307e4282c4a0b01d084800c0c5815043d000450b815001c0320b00d0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 660183192 1250 660181942 660181969
    0x506070c050a0602010207120801180b1c03021005183f0310140f010323010611060a060b0405011b120e0415050102060705033310110c 59
    0x14036114000a541d42d80e4045400240c0015400580ca695540c80c100b00040f1043c540d0170188103a000040c01f01c1a900c250301440703c80f841402094595189001c40e4000144020044d240504102040d05068000481c10142102d40703100b0000340c0d86d4480c0c210402c620440500d591504203100c0320301d1084034100f0b103240c0c60700b031403460b0046022400e120044800c2c80c8007000c030460101008200180158034501001807000d044101501c58510380010750000380000b0082c181a699150b1030843d08003038012200118061004919550310f419010703054403110800ba0b41c1a22079000055504c0e05a409048102d6822581c1c060802c0d041c8801503030160368207045a45114013141099010411030000440081e10766152800e402307080703d0510050b0303803008502d4451031002010400003642c2c0011a180d22020b05e1074000e8a1741c41d01040143c3d2a510f080d0f404025559812290780880038005420110040031210803421411104c02a0307144141c0d10128141500040c3c0c0902040c2022a90703030454 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 660184442 1250 660183192 660183203
    0x1a0609181803030403170a200a020309090901090c150518060c060103060c02010c141204210f03050702010509071403100e0133090f09051e060a15050607 67
    0x40a0110200c1c51540d0411142600011004840456038107505008243c01110105003480804d21032070054444591200c402c80c000c000c00903280130030302d00c00d106039034000b20010101183d40c203010410a001e00b500820a03504001500030000b00d144035010040b500c022a078850303500742a100d02c2650787c00000703c454203411400411082ca2854400e2261038061441110006003e4196110003400c5510818600c13050045121010506e400c0410035101612007104010b4aaa07441b8540908170350703c40e54159201c888928503001101d40c1102d81044810341560703082155650f2160100c0c00e80e0001e4030142580e80060406002c4800c030710041031103c2074046d04541c0603003014409074080b2840e03200d041e40c16035074800c07482009440365500c1d1207130200050030134007070004481c0741d0b000f038140741740319000c00b040d900c81e9086440c208580200c2c11082d002000e9400e49030b000b000315920070020b243c090301c20340289400564414424802c0b50055424003400d0724889003024244549540902000d560 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 660185692 1250 660184442 660184471
    0x10080607050a230705100f050702241b0d0c0315030f020f063c130b03040c0b03090312010b04060221070b10031406060105090402090d151a060918 64
    0x114171304000c00350326400c096500260900000105804944000d4000011034000300c6070604441e00241c03c0c050021031103400a24284c441e141a6500c1000350000c2c854001700100b01d22032126a1703588508201d01c019202841840240700e60065078a5603808000c24080607510b001000d414125221140150080c0c00d582c1b0344138840004104142c001d8114004048042d00d08060b4410a0b603844d05040c030001c0482408c06044034200c10340000e09000d51303841c100002c800981808690f0381c18900410400c07180503580d041880b5156120307846a9484e48030806c8560000a040201c2c40480d000c64086034050b15582e401e690001c00003c00a5000c400d1451003404894082005011803c1c0950308142c2c0800b002c07880c500e4240600c42d03041c03081840a4005c1410403a299030040115001100c04503001a0f40d40304c2c01000440210015802910566800c040c940e001d4450b41d00140206d501442e0314411000d1380c6d0300b04001881a51310040e04403401c2a1003040c000d242e20351031908141d003c603e164 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 660186942 1250 660185692 660185707
    0x14060a1b050a080f0405011b0b01120524071107060e010c0c05120d020f031e030c1b031305040e0c06030c040e151c21140310080607050a23 61
    0x41040d000100b15401340d14000408214942e0051762000070111701e4120030403280007036240c0910b0581c0506c42c48041084000046042290621402d884c0c0d03c0c235288480381c01c028205820b04190401c40d4800080703440704040030383c444e00002e41e07403040310b243c4d5071100070884014004440150445204403101c02c05042c2c0409d05560306403042208070900001403140700058503009280005180c40c0c2000c0360005c1010310120040780e9100b0369071402c00c03980c4640da52078628807081030384030303848010440302d6003803c1c6440c2d2110040010302107504030880b0380307500d1070300d42003000b00311040c542c0c100626603c440c03070400c0383e810580041d55000c900b054071142050741c6d4200a44c9507400807034120310f0008500f8501c50052501d401100710364501c00a600c0100c0c40136517600c0c040142110300400c0130082038440304d64035510548030705004116510142d610b90502c0c64803a900d8a503140942c12560140c04000b689107440342d410b40c1e1641640303540f001141e00404201d564041c816410241c000c007010010035 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 660188192 1250 660186942 660186953
    0x1020a08041203020c06120411060913050103020f03150a050403090e040f0b0f010b03070e0f1206090706030b1f0201140411030d0201050105060702012f0714060a1b050a 74
    0x704000d000c01c1c01c140410390280d18009041c2254980c070719100b40402d101003030310707151030006040d4030a50114443c0208039a90b0005030190007000702c0650b001008001156007030b2110382196048074401d40c0c0c2104098101010191112101c0d2070140c8403907040700000300b03090801d40100b038210740613090a0386042c3d111324181c40b82900c115020f960141281c05402c0c00c11200b00301440d4000d01d551800c0901b941040d2a0b0102d038403028180004200001005506c15a10b2540ea01140200141400b480010804111361900c40c200c5040d100790141c030b030000911074080d020b040030f84a40140241e0410020003c0344044018141c03940b07086650354154030003074000000380e15006501a55007440c0141d070020805181c83c4191400200716418840100480e40300e54046d6030b41103030b0909265801801450051400782c84a00c0340c6e000c81081c41c0d41c0d01007204400b16441c1e05a4860340030207260518400180100c5120310500321000580c464120500103000580c3d00d64aa40300d0f40a8030328540840d11070 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 660189442 1250 660188192 660188197
    0x91003080c072903010315060b0c0d12060e0c030403091a0d0f0e0c0f0d060504140d18050409030302160309080d0c15020c0718020a032d0b01020a08 65
    0x10700d1050b0700c02d82c03007804406110300f0410550359038400c0d015901e415070402c0d006140410b00c4020051780f410065090700000d542c2042c0d01800c07403800219122080d01c0d804591380d090700341c0000d01050066003060322401d01d50080d40241d4803542c1541c03d05440b85c0c43c0e645842e41c0300810940400011810124442c036030400da000341c031b0708043c0e2050345411b43c0b030140a0450311584403100266103420000d83c0f03c03510204503443c0c44001103422000084405010900c1d035417a071200141510701e003408110801a43c28541100b082c0191308541e400c0e828284151075429000d0140d00440d514050208100c0c80c2c42d0f0030440c0464421301c2c000d07040400c0c0f01840000302e01801002c9000c00c443d03c00c1404506010002d000d5056807d240503d10894941c545921065500500d04403c64000a08603980c010410014006040c2203501d403c4400d0805003a80003500400c483c60b000134140345000e03255100030742d4007180f0401c44061140d000000011180300030008480401c1c1075001d1000c1820104803044003 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 660190692 1250 660189442 660189457
    0xf060d0905060114060c100507141917040b0a09061b022506050f13120804090b06180d0c0f09020309060a02071a091e0a02030d021b09100308 62
    0x20b01842d4108031650710b040c0703100c00b4114010308043c0440c594005001440443c007209050000615441c0c2031801c5030301a01601c46036001e5040000c8061310030084405440d07550040366103150583c580080d88038170b2050181d501034400103045000c10210845030b4005006a8800c0c00300041d0206040400c810102c088408103015820004841c40c200165981c030303178441000c030251522243c0c140000505240105441042c0b103002c0400c50840103090382c041400a0841000c01c1051509603240003041a03005004080b0001d00b400d1444800e4109101554100000502e46011a034210001e100b10702c05090010385806030314590009044000303030703680300107014200d0000d0780c2da01c1c082c0851458100007810400d47d0603c1049080081a1154640c01540180301c251844c036440e00444180340440b00c21208800c1401440508001807001a943c0001c61003a02903402e0344140c1c5005a032120f607a01c0c05001c101c1d00f000500300641c600b159519500900035000c041c6080d880361206c2840d41c00081 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 660191942 1250 660190692 660190703
    0x804060f02131404050601020f19060e030c1c0302091318020618011107030b0105010c0c080d031d06010f1a070b0f012105030d05180d0e100e0f0f060d09 67
    0x100c00c1d0060901d170003a560b20001c2800140a50040d14042559900c007146207149c0c88001803180800300501500715691401815045940b141c15510f40541c6510420208040506600d0b440381e000354064003c3e202d41c4180100640c150450b0800e090000d040d200d01007459490112440000581d01c100280910044072003050051a601c40009000360060b5003610202da800000d081000940030036415043d51800e1a18490101044c5010101442c03a0707000b644840c0120300d084d42d4202d81c107070b1052101903022100b07940f240c4928450b45440b43c00a0207880c1074010000c1c3e0505c0402c800360000745e0408003c888240c03078055070342c0304e40500c4201500d0280f0044000c0004114200b46682103840344550800303458840d09096488950b03c0c89050004161213450340d00180c0c8025280509a0b40014080240c07142900b003620010700260b88001c207144900b442507140c4040b507116441003080e01801506400c401c070104030401c1040411004070641c4030750204594a01001d550060b041410b1051 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 660193192 1250 660191942 660191969
    0xd05100c110c0f06070c030f1121120c030c011103010510020303150d06060323011b090b0d02040f0b03040201020d050c1c0210020f041a0a0804060f0213 67
    0x82030000c088400403103107494107038008140410503070b0300d0341d4509a0b840b07411948039a032510346240400100d480d540c03020f0103003400100604284100324840c49074010040b2040c1418000102120344011440c65010b055a4084e205200500c0d000314012315914058004503818445454407035030035240701100c40328418801000400c00e5060003094268150301da0b0002e9811464441054210311035440d0300d00e40310301000f024076418000e55910000c0038580000300b851402000d050005100c1034500a000110b600c0c281011401c40541c0501c02e95044080d500c40e0071544c5002e10465035a0084085104680d508110004111010000e0b034002803c0080000d516482c2c0340c000a414101d00c0c1410800303200e401c100d61901032001103050301c0a000b002d0f816100c1540e15190480c074142c500c040c0c0c1003c003407000601c0b0850480c440c014104446050382c4800807060103906103000307400795006010108001c00b010400007400c54120312880c0c0791a10006040c242075026a2040b5005503001c200b001080 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 660194442 1250 660193192 660193211
    0xc130b090a050301050c07030509060d021603110616271e0506040308070206130b0d020433050c0313030b1e010f090f020904090c060917030f090d0510 66
    0xc605000000d1500f140200030742d02c5c018190f21020b1060b01001001c0160000b10b11900e80e81e188181d900c44064007034119243e8074800c5048441a0862900707401203180b118600c948110001262441400000d0441c1b414011200c07040e181d19111900300c11b16403641400540c91080305101000081c03200d4112442083d01c0c5246909196075039810050045100300401e0022881040440360348981c180d800360b03034032110a1b08000310613085401c1403c0040300000c801c2d0030100303240c01410541e44c081901401d0b0f2900b045402c885014041b200c154424161090008000d029101405880713003100c00340d034580b10984000d03007804501c640003103030781440d82800d210f050724001a82520308010b803120840c20794141440d9022400003881020605912544a8050800c80781c06039000c8120282c021f000007102480c010458144500429001428421000407420020184e01c642d030f410a6014503d021030004003024580e21401013a40c0180440c030040b40022001c00c5010a04410410006607240c41e = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 660195692 1250 660194442 660194449
    0x1e09090a02150a1e0215011e090b0f060912060c12010b0a0c122706081308040302040513050a050c150a021b041407120b0103050f0f0c130b09 62
    0x65424110880c40814030500f0b00c92508504140c64a8000c03040703400e5040841c1c0030492402c0340420403d0701a43e00580001101100e503645901a28040b04071880c015840b108030104443da1031001d164414000b070b403a60301234102440102070b00c8001810a4007107080c200c1a81c0e20307001042c1d46078081c544002409800c521700030070b40d5501500b500300110b884e0854280b002400d042d8104030260924818461607083c290181c100c0c01841d4424004100000407411007020044141c0c3c400c10380858000000a0f10480c5034201c150031041d80106501e00b0a0b00350307001c0c030004000c000c010090003841e02e00c0c070b00f011480400080402500c11070081003160468010300c5913085001c66010740a550034001908030640201d40005144681d164110764509410006401b4200c03040140c0c00f440e68090902c0215544001d403441c0c100e240030b8007031040d0500800110202c61044a114032810f0303591010602217030a044044c1d81045520020a0400c880c0f940c0da00014641c0c1e512054040800160030506801e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 660196942 1250 660195692 660195709
    0x2070f140a02011d10030c09170304171531050c030c060a02070303080a06032418020915180a140f04032f0304090b0f041a1e09090a02 59
    0x5a510f0100104c1400c480460900821203070b19030245516000480000c501c240c03134080040c40801200d0301c3d05201d224a55841364014001d0054001011140c2c400e07100300014a446801d0300300a482c3c03096a40c100329201101c81c010881c90b0415565898035600103100c604240700039004030040c0c0140759162040624207511894080d000310018049251402c1d0040741c44c1c02101d4040c2440b44c180e5807490f01d86002415aa04002c1200c03a00000e0003080003414400c03502d0600003a101002188241a20b40d510707126a6500254000304150000300b07810121041d040b80c041380a4450350484007410032028003010200c0f81c503081c590360388140942d0384a803a580c054005d050101d034000305080603280102544030f1030035a94414105104024455005d511642080300070150a0f02e4031540c0300c444420151001e403260601c82c104050306003031140f030030f0b1144894585c20800100c1280c524001400303c40448407005402d0207240c031144040715181c042c0c9140c800c04c50740f4041c180b0f00b130481c8108a0000c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 660198192 1250 660196942 660196967
    0x80601090b1e030c06160b0403050406020607020303222609040b0d0507031412181318060b061c0903030e0a0f020d1518120e01090902070f140a0201 65
    0x1525074079001c10b0b6540300460410504241500c2c070641e074100208600741e2440c850b403c02030641105030b04000034164414041c00c1556a5542070303801c103031500d2004990f00d000582d409006c03c01c90070030030a203804008003007105540c41624840c0066041078491516036010580070441c1410004070744156142038428030f0151041141c9104000205840c0d0558801250000800101008a0042c1644402c00c1f440699619001d4003a56840c030b1440003200321044600d15500401802d40720701191940b5028801c41100307001c40f45550b0003542d4451502030036000f2a0360b6000201042a001c524507042c0c41c00075141c1c10250003081c3d100151038000d003129404202210160006801f41c40014620311a00c0e20054040b5043c0b0281001307424101d0b50b05104914003501180b80000741d40c220a03001805450443c003c00c1c400441c50310004055603118251780500e8000b40e001c403000d014070039140d80940f82041c01409407180007401a51000d000c2000c1080c0c4400a40c8030105000843d0313031024940004 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 660199442 1250 660198192 660198229
    0x6180a06020a1509030504170a030e0105040e040b0c040b0c0a1209050306040f060209040c020d0e0109060909180506090a0b01120206030403030f0b030d0908060f090a030513080601090b 81
    0x101c002d079440e00c180304401c003840da501443d1a581c000080c1440743c0156030140445070954117190001c101c3e407541c1c0d4600303010224041030175a40010788030741c002c40a940445082081d8400959200c0e519403814100042c00418418418031020401d840d0034005000780030110001000344080a003083c0090841d0355141c1d0040141c04074043c0160744000c54400c2c1c000da0310148450390051a8604070000c2d00801c0303032190b0014504905802c1440d80000c0e90081c00385652504080c6142d038400444101c0072074010700003c68a071950030003101d00254050301c940f03202c0f514182d4040c0c00aa54942c2050f409846030f0083c0d42c050b000c11030038051001e07401401048445109800e2043da80d021455600000700080c4c02e15941d007150b2900081b45c2c4c0c11041128400906580d51100030341e07405440380f10240281c45180c450900028092610f500d0441d000d80d0321240202650521542d0895980d44000d42c18510080120b50000d240801040943d0103000e0343c07180072412a482c041031100f11085002c80003103 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 660200692 1250 660199442 660199453
    0xf0a11030d09211b061d0f01140d090c05030f010b0102060a0b2103041d0103020d080708130605030615190806040b0a08060f0f04030504150e06180a0602 67
    0x4040380c118011078229100e02c90440c0180608008001c0c1070340b03200364040c144031607148522602c1c0c404d0440c86026245143c503460843c519804440d10b00c886201503150308412583d50300e480c03960003810050200e41150ba0750b00c0c0b03403d01c880e40a50649000c00c504540c0000d082e84144a1480c7c00c1c081c49004581c07081c004c004203041080000c2d5500320151486040320350342c40d510100c64a40441340707140300c1c0004842e440401c8520740c040b652030380640316125040100080304010949101000c42c1205e030028084402280039459107982503100043c100c1304518200721061070300d9002a0325500500c000d8544a8882c500303042072001607043d107020851a0f0714104181c014441c1c0d00b00d1010b01c888a10300d8200040d0391800701003001031600c041003603030220600c04005104400010050310a08240c2102101c40e1204814031b0015042130341c009002c0781003884144800c0340e58400ba82140b02851400700c05d81d07040640801c6003940b04c1180c00d080d011100d018008141030942240d401808a44010310 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 660201942 1250 660200692 660200713
    0x207060204140910030b070c121701050607020607170c07090c120504150905010f06030609350c01020d14070201060b3405011e0c050403030c12110f0a1103 68
    0x4c10520944c04001c0c003598a02000c40c411520031003c6c1c2084075803041c0441c0414081d1040030b4400401580c2e42240400910000314050a0001c16034000c00c3c1d014114500b000c019540d0100c64610400500f403965000388440303c2d0302da204224200c02040064070010703020740960310007000c1c041640c41c0c503402c450415051200041d28403032613032100604858002003c80301c0c1d103802d034054131000150340c400ca03081c840b000c02400704036130150142500c50000f80f0000240350f40020143c01b0328001050300001500084021210030344000c21500003d40b000602e80300c500208501101c2c03580508210383d60b0301170200640c0b1602441940d02504850304c1d02030400c10903585400b42000181094401d02d9005a180d12107214107103204000345038408001e021401c1044213420161103e0031305000201d007050714858003940508212003c1c0c2c0d4150f5030300d40c0c1a40c41c0c5e887d01003800700481006020411000c102c040344031800d000c3d902104080101130300c1e83c54111308006180d08102ea03d014480c0d0451705c0c141 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 660203192 1250 660201942 660201961
    0x6040504030e0d0311060705040807050d05032b02040b0a110705100f02030f03010e06150313082208060a0b0f031e1c020307030f0206060f0913020402070602041409 72
    0x961004003c41d4204004510307464100d50303048618049440a00c0b4500c20300c00c142d9003242c040c00959601504903000c2070703a00da080005040319684081e116410400c14584684504400742e44942042807500606217204480a0b003243d025a01594a000c0007040e800d5030389501810000c12003040d80014207103207091800140100382107080840600100390034810100340280159130302401c180220079240c1d86d42d08940240344000b29000b0344108c80c800107000495002005481c080c0d4007140c0010704401c0305039210810f55000c9007002120380e081c10094000e983d14040080090091344000c0c0485042c10300075141940d03205030700d052058004070801080327900c0c0080c4189142c1c0000c0c50016104801000f42400c0c1710f0b9003610002c1c01442e0740600310a083e000401807441911a07594440442070107507040340c680009a44840e40800c103001020604d180a543c03894208006e00c80755103501e10700d6400034040382c0c851141110060b0b000f00f4100080c455400e0401c0d42e40409071032050717840c40c0c6403520 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 660204442 1250 660203192 660203207
    0x20c0705011b020301140103050c090705040b210403020c0111150a0f200316080c07020f061621030b13020a180e24030d08041b0e0901050604050403 65
    0x2a01d0401808032100780402c0c0c03218211112107500034000b0040d20b40c0f101c83c40762840400740810f5505115890414000341481d101040c802c0075541d842c035041c0707801c2020154050f44a05841c203d01c410752480702940f42070b0b805906003d03500c00e80061406015220026200a201d66020036564000344c404401c4040034190483d40142001000165281c4515043c1d00038090346840c01c00590040c19030f6140305440100941c00795661558248000701c030040103c440d502c2c200e56416018500b032001c0c0e40113040040d60407c6202c4010042800c2000d18901c0014000c5000420b441141c03035020740320107003c20940410214a52454144a071041410100d0390707000d03150041c18501d50b800540342d00c0f20383c81017014002444100e001e80c401544e0b0b50000b031b104003e05440b00172600b115802c11105400f85649415604440074000c1c4c154003044e40801d9404210041050302c40300709100340c0c2c00c20005003091001c045d0501e10306108c1e031070078995100780c211100106a00e008900e01400d010201c2e4200d4503 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 660205692 1250 660204442 660204449
    0x3030c0c0906121e1209011b0203010915090303060803030c040611010207080301091a190b0d0605060a050a0f0503040c1202040e1b040b0303040321110307050601050103050a020c07 79
    0x80700262074562502060406400040c042694020300c1510102c4010516118907900510411101d06500701d03400c3e0245441100c84082c0890030b40310031000f41001d5a66403540b8180014000034030780b41141c60305c0741090207050031883c2041d40d039041c00d0101501131250300c0281a0000045045251650a0210520442c000e00050060310001c00076041001d40449a80e10361080d4041d0b00c95035a00d0100b406040e180c0590515860764138103c041c541064807810070180803503c11441c0300307072410450301000d500c000c2006070641e8981e00e01007115180d540061611408a50303469aa441100000500355114280c0007020880c0810600012407600d01e01c10f0103641d80702c0300007400f02c002840020000c1285040c8412a0f014240d07150340c07040c0c210300440b403440350300751424444010031804050b180e00c21808018008060b0032018040f00e6403404012415550500303040e96544000b405d2207285030012001110ba680c000b03c014041960305001d800c3d04080c4109045d0304141002e00c03001d03118900c500 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 660206942 1250 660205692 660205699
    0x303030c1701150c050a050d0315050303180f122d03132c1f060302070b13020406030c24030e030a0e130e15011d071805040e03031503030c0c 62
    0x1213020091000500485030019440012207940c07101c22a4040d01901044940303494082c1c5c1c001c0002900d04010007140d440131408203210708068503400821207200619000c00390407003a00840e000b00300c041081402c0e020442c429084640e1103c24503503580001c082c801c5003e841c0c2060202400000c0342001d00002c1e035252042c985014141e40700800d1401c07801540c0070024442860a2001c01458413030f00001c0d1401d04094101071035282c01065050b4032510400400440a07000000c900b113030020745080c4014030040001caa559a83d46418548124a41100440c01122010925900c80d100c1a281465020382000d2001c40395a403c180e40342e000d40c0d02c0050601441d6a010388559861a880089042e00803100300f1071041290b08035030b0340d11808034030f5041b800d15890000c9404205043c3c2080150002e54000c1195a0707546401c44490f001c0307800c1c40c00c0c1411211004200c554945c0101c41015103171030003c603228a411807000b0444061403d4641c005d4004000b8481d1103500814404203c180c1074 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 660208192 1250 660206942 660206957
    0x5090d140702031c0f18080c01110f060403050a0e010e0109092c0708100b0a0315111602100c080f1b0a03030e072c130605010303030c170115 62
    0x50011034101494101c0460710000c9660131001c286400144120510751780d651044940c140d800f084c02c64802032401001d601e544142400c500071740c460304d4200b019101c0002581c40040e100b14420f89403c03020f840807001309001096100e0810351101001d02c02c050300f4680b03103035100c02120010f84112524022280c1290315003100b03800c0c104421444100c8905455280074907040013010250301c0d10940e005110700c0703015042d40451100468010104981e9004101075000b500d940d07556031403c00d5414503e052503484802c0c40003404040000b811000d2440b44e19207800d880b1038410000c4410b01480102e013403102010030319022031711510031b4941048074040300305e41c0c0b0000c084040010010821481c3c1c554030032820b40d4010164150840669400700074125001542c881c11840003102ca1685c1c00c40c00c0c1c1c1c201d0780c88085039400381e513166900241d42c0c04100e1030310300d102d4030f1300c0c0103070f42090700183d000c6621000c001101541c044150000034950040303001265040400c005138441d00b02e01103c0070030010 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 660209442 1250 660208192 660208207
    0x30c0f05010b0312040f08030c061512030a030618020a080a0b0a030206030a200a1407060f090c050f100e150405031e16030203060412050d140a05090d14 67
    0x2d501c02409020010308840240400c0c101c15009076126000d4501c080b20010380009910000106551a20320350b14054a83ca941e0041d8201703044003156451036108245081c100031806040c0010130171980b4030381d80415980d08003180341040180c541c070b800d0341c031030f104011040410303078800c0f070702e5030041139290020a4142e010300000b4862522500003a50120300001401812401c035070050040000e6060703100055214400d16007170901480000d84046450b4005e200c00031101c200082808a118880c00100711a0001422080b22441c0340101c60a00c0712490500043c640802c1c0c0001002c0c0889650810440e1900024454030111021354040d051040050096850110698015040140440b191007521115592502c04c440d500f40c0002c0c061481c9102040704003011420540381c0180007001103840380d59800b41030034801100c6130f041000c02d102d1080d0000442c02800081c0c014908889103906009903c07408844025141e91103ea03c003039820851103800140051100424021241e1075004 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 660210692 1250 660209442 660209453
    0x702010b1c021e1311120a06060207150912150f11040306020706110f0d0b0321030925033f03021309050f06100909020a02010219091d04030c0f 63
    0x4131541c00303280302d8240017070321042c03181141c05018420315141d9400703181d40301d500c41d40040321424064440140c00c00c000600030320304c44460b02010545070b80790001909956111003181d00c81d4100003124460561074031082007031101e0250724568249210200541c0f445d0142c211494801c42c331004241680200d460014842594810701341c0003c1e42134410303507801e03215a06030401d901c5452002c1015280601b00c034420709000801c1071503c01007000650f04480d80d280da030b192903003000349042114400c28001c50038200b240900b074590116182d5541c4102c0303046252440040001e95243c00b10007810041a8209545900900441440c2c5409400c068441510101c020380300c0d01075a20f0700c0803a4100c0024030104994492880b550700220010820740340c0d83c042010509007045400c001a040d698144208025503004240b0901280001458080380700680c20079017400301e04040c08108520000c003c081040c0f40426045034442806000b0352030541d81c050040c030403044001d448007200d001c5040412070f = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 660211942 1250 660210692 660210709
    0x602060f0108210c010518060109020702100c06090f1202120c0d03110412050606010e060c06060f0a0e0a05090d090e070f17090c130c171e0702010b1c021e 68
    0x4404400074130042c83c00d107ca0110741002c402100302148140000014a00200d100f43d500c00b5900401661400c81c611400700c2d549840400151000e9968000b0310000444484540170180d2003001d0303070200040d9003400a810010030021189800038108101500d8007000f04280500c0001400e002812a102a08013401c074040c54020b2852011404900010b00c2000a0820b01c00d403000d1384e80003e00c034050f8003841200c0c020340454030007c2d40880003241c9645051011400c0a04024007045090b03035441c070007604101416142c4801e0b190b40d500605c86030903400d00200c4500038280c10112400c034034054048203500d20003020101005002c05001110034441c04c1e0750b0b0180f007907590107002c403414520401603e8202c040035a6104440352080900803a43c1ca0240034406503007521020030000c80b05240303e440040080010740720800d0401c1c018245140020303254000e1a4035800010001102c2c1b00340310461400d1000044103c480002080c0181d8944600c04042d8105010220551512b0f0300416640c5 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 660213192 1250 660211942 660211957
    0x306050118090c0324030512090105030406091502070606030506010515030106210c051809090a17090d1209061e0c020a08010501120303050a06080a08130905070503010602060f010821 80
    0x105c050072030308403190f15840701140507a07014800759203441e082c0110f41070183c0700e01c40d8694040f51042c4001404108680e000e0454580a405400d20104904142c04101c1e403007500220b40982c4d4400091092290800c507490241c60141c0782c01400800e03004024103a40014401d1508000c901506103440d1501d6040034a4148080c04080c807140c3e400260241007500411100085003284554407403c0f4a001c4508501661010700034100c4120745072528015040861b4207180088070400550381c0e9529035903000d44850f0301802c03031200e50b03c0340307000c0041c0b8000099000c1070400850301c20034000c50495442c100d401064a00f028141ca254601c041a20605958441c0140754a0320380005260020a800907920610960302044141d8503107a0810440d03589018000565024503a00c00c00144030400504001c0c00144916203020b6540b2141010382c4c1044600c0c1c00011000b0004004058040003802d82003102c2815422041d07060104160742c0e03054840b00d420130301d1005a1196003100c0c241c422103407030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 660214442 1250 660213192 660213221
    0x6060a020a0b0403081501080c09130b18070206010801140f070c020409030203030603120403080301032603010305010b041a0102150c120f0103032a231c0306050118090c03 75
    0x294503141c04c0140c49240100c0e140001c0c01c4480810105170b41c46865210321a254104a039030601d4a020284240d2408a45511907440c1d96001c1020460b521440c0348482c001d01031941d400313035143c900002400c1a1041c1e0015099030f0400c0e20804030070701410039042d40042d40c01d6139500c0d540d03a640b0045034201c0c286400a50440d2925231328100349540407000310b2040c0c074251f04a6940c44c01980814246104030310014040c10b0040c0018000118810f224030030b80f05907114480d008a900751183c2314903a20070780c01250160b43d0f5200103c05801c080c02510001c000c40701102d640941c0140004c2c0d20b40e044403d000c2d1400c6100d40000324481607403c1a101101000d01c115003240c03400c00c40c0000b2203a020301040d070200704c111003072641030401100c108000783c51810250610000958400b4103040220700d0081b10503500c0e40504072801000c01c69158a42140760b204030010100007809421205250092030400102003c616100c85111031248225549003a001420100c22002180101665880c0c000c1 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 660215692 1250 660214442 660214463
    0x50c0415030504030305100617060607020a090903030f021207080703020c010e15010503030307120908070618030e121207050106051507060c090f090c030e07060327030806060a020a 79
    0x480d90760540c00140b042d8807170f4400300400c1e160681c0e114010300c0c2d107205001c00a010a94034100071004002c03126080324007d05002d052640c5a400240c241250b44c2100701071a035200c0c042c000741580b5001e0189181c000b41000c40c9414048200c008010400030300c1c1d503050002c01400320303204612a070b04030340002c1200c600030091311b1043c02c110b50b124480b020300301c038400444c03e00100d40ca103004812203000b001c0c203803280307040303120780c0c850712000341c015040c0a44502d5400e10040002c82c2e0180030b0403840304c1c1080341c5001101960700d0080c00d1042408040d038003828521040c02403854001903000d8400c1f0103040d100c0e458030405d181c0346024200710b80009410060700b01c0110000c80088020f052110f01c906001d2091800414007140c04694512801c04040c001110400c031b943c0181e03006414500d04e82c90040b51041c04903212034070707001c41ca42c040700020365610440b040600768810a0070030300c141c0c6d170310009403152140c50040a101003d0304613031051000240401886000300700d0341c2c54080c1c0c452102d54 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 660216942 1250 660215692 660215729
    0xe06090a050402030a1e020c0c0d0f0501050f010e100b180a05030307230102070f02060c01091b1802120c0c1501081509010c020d030e120313060b03120d050c04 70
    0x4001e4540388402c00e0301102034800f9080f0040c2c0f5402519609407400009000b009d00d400c04120b04134000c5503098031031455880c42c04002c15002e00407544541c910f05220411035240210758058444010b10340c403105092030303174184460080b0300101e032010b0130041d800001a140007000100505200c1e4080d903410303c00040d807070080142d0040c2071020404a92040d1346200c8035003441d40e0a03440389601c010007103c05800c51400502d42107000d41003428550f4000105142e066641101400002004003200c40d08840c0801c04400802001005a141a0415424080040c9000d004060082d05029141074040384148944408000141608840e03075001913480d65100c106549072034040810031b070014060000503404c10014010020120300d0760740204401070390380200b1401498160030b040c26502640ca6009500d1500d58050b5000d00900400700710f8510140c513242080b1071031100064025008505800560b11211040e00e2040782a05004a1151399500b90700c1824450340c1c102c440807400146440 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 660218192 1250 660216942 660216961
    0xc070905100f1d011a071214030901240b09060c210301050a090209010e10031b0806031b03030313060f060b0315090105030c041a0904050307050c0906010e06090a05040203 75
    0x110100d5110f4400660b660b41c86101000b29240503600c401d811038000c0000743c1c006808580c9940c1001800e1514003020180d0780b8028080d41c2c0203a0b80114241c0d110356030808a555100800000328442030102c0200c0d80c580605199240124032000344121000708000340440414000082d400641ca002004607401d40d041041c015082805558020b0402120201e131070304161088076a00003050312003541540d148010080300e141510441030415031194245620441c00540031040e4080b241c139046d003149490702c00c1c986403200002074000383c585408101c0da0f06480200032a6004440c0390f400301d20740c900f2428444080c103203954001c034400d0b04d89440024451044030146005040ca070109104007001241044400e400a0052a40c150420000302c0c0081c5000c1d80108400d28020300344006007007d6500244005000f2102914190800200714040007400e03c022942008111841d03101070030b01030b00086c00300480b560614050703a03001803000c006646141c1c5510040000500565a07885e007101503 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 660219442 1250 660218192 660218219
    0x902040b0301060933030b100c02030f06072f0303070806031504120c05010e0f0c0102150106020d0804051011040501120203063a050a020f060c070905100f 68
    0x110000500c040d0700100d1441003e00300c80c2042d04180031003500b10b59050141e4030105d00d085264406041d0f03203412484031030710341c806c0090084500341c56080380304086005050410000124400c111703040752003005a002d0300301514900c0590491141a484004c1018100078102c4070703005112640701c04020448155406022148601000d40980e900c44c0d1501000010a01060341e00800c041e0f05e001074020200d00c249890090980034034008038455481800850511190608182c000d0700801d210450740e580400c070160311034440744540b092030b6142140c0207403902c611001c10740c200030354100440e046c807808000318504440c65441c20000a00b541156405079071251207010b011541c401245203007500745100f5a0b100c0c00340604840302407000d00c04048504840d800c8080c0c5c034044200702000184064030342c000324542c8140300901c6180c181d801041854110134040a100d40760410202001c09000f150078011141c81d954040340c0c41d150b454204c0d03404182500851046101c00383c0004150700c50524 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 660220692 1250 660219442 660219449
    0x200103020c1002070f33020705120c01091a2203080a0c050403060c0c05010606171503030f12010807090924060503030c16150207030803040c0f080d0201051501021b06040902040b0301 80
    0xc0d0700e001c419001b2464000d9010341100a84950041ca18852100309160700a01d44000c0d05000000d5080040c0d0700c4110b8449882c00480703442c7c0501d0204880841344035400c2c1d914400f0345043c0850b1803200d9400400743c2c18014140c00c0421385425034080c8150064007510051340c0e1101c000e1000b45004003004100e040b2099042e25190308212000840b6401001c100940c40b00b542540c903141c0d6207000035204501d01000d900380c0c040c80108828102c1640d6100035060310f50203c500c01e103155241840961401a05030002c61040c1d2504003408002031003100c040148410900c402482110720221002c0203166951001d80c0500000940600380d42001c40c1c0340f1203406641c0e168407680798a40b08081d012081d0302040e00d0140e40514400e0010400314809594401c0c071a91680c25941d032200158034801070315900c42c0140d0f0b0702042075440f00e80d40a016256110003060845510441c10307200003540c0703014090301854421a00c44481842e0b44405040703c018010300c00c0103540c2d5070341d1080c1726961a0300910 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 660221942 1250 660220692 660220763
    0x10180f0602150a0c09030803090307120206420409080406030915060806010501052d0a112805070e250203031b0a110a200103020c1002070f 61
    0x800164035043c10f842042115012691094003081c02d51b030760241190300160003010300340700a00a8000084001001c2c0a10780e841d40c2c0a410306040264240124a00c01844880c0750a1301700194540704107010100d022100c8541c405008002c4181e001c18000d04d60715a003d064040f00003008106075405801041c02c00d4482c40a049440320b05403c0b07402110494002c0104942005004020942c8554007401d100b02074400c0c04007540d02000e40c002110300b64210001c0b1602e1010540d50100c0e5040140441d14440d10005804078451600012032440b400e10440e00f40780341202d0b02182400410040301d40601488441981c1c00d0500070180003425441074548140101e0107810014a18400720a0b44d004001d030015540602040780c44900681d041887d14104000351100e102500f62800c200041009014121000380d44c0c0c1c00c02c03040b070b016122442c04241414010820401d00300800a00444000d400b480f0050b21000140f800310800e0740200c0c03026080d401841d504100800f42070b502c1000800e10340 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 660223192 1250 660221942 660221983
    0x10b0f0d0230061302160305030c1603201f0e120d060503010b030f151b0d05010f08030a053109050106080105041b0806010905150c010f060510180f0602 67
    0x350104003a403046800c6c5541d040344001040000130300441c051a00003101d444203505150703520241c1c044220f80f40600b034002540340c01401c0000c0d00c402002c00e11a0b5801009007104003540c841c2c4e021400c42c890010710f9001d580c0c803c0340b00403c00500140107280301c83e6003d99607070320223110200b028003d54002d0602c039510380f0013050070b1464000380c290048410742c00a45003c0c203001903020308100004010212001a1902d101c1c644010b600003011001545800041c507941040d11880c0074441542040103198000c10150034810b412030182c80e401c0010300c002004400c1ca0a41c92800c4540f02403050184658100700491a011207401c120b040e1045580c074403005a90320701c01c000c240c48203a1188090071414000240e0220310840e0881d40c02101030400462081d500c402003040b01e0302180c1070700c2c4c02110210310113071805801c0c05904113203115420140300450606000a0805101401420603c000144210410345203e16000003c1c80e00b2800c00c408161b84001c041d480b210001c11280b1500c60f40c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 660224442 1250 660223192 660223219
    0x32030c010b01090509010e1b270909030720032d060403050304020f03010e033603150712090605010e0a15060f050d02070507030b010b0f0d023006 64
    0xf505060045030001040030b5001d91a140d81064a075201400d80704513000d0b85010401001c922400600c500c07e001194040c0c44030890b143c040c000b0660443c0030b44140e440e0300c10300503080400030644110f10340008010190030040c0b2003480d07508424450568160080350003c40c0584c100c0f102e010940d40b01c05600c0d100c0716403421002502e03a001224003d02082e01880441c000d0f050400c107440808401070000202070761100c00c1545150480a03d0300700d000e584440c0002d51507041030458203c40d0704800101084542034000948400c00d02c0e6446801011900004540c00c0c4280b072a000d0103041d61004201c0c2c06043d0034040e0280c4400d0103581124107800012596000c5944900c400078100381c1d10181e03103a401c0c0b000031141045a281d203141040018000c0c00c3c8862940e10003000e450788284000e020041c40d41c90400d80c9402c05078040c520038801400840d000405040032290303000c400800040c0d0f1100700d03e0240c605180c28005002e5008200d020305218070034440d080e02d0141070101c0f01100b80320b24 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 660225692 1250 660224442 660224447
    0x6030d03021e0c03070609060e10020403050a2d0606030b060907020703080d06090609020706060e07050a18030602030907081204060507080d110307020a030e091332030c010b01 77
    0x42e0700e41c24031032182031110582e00e026240010342181e40a07901030b40d00c1c0104070340710f44090741da200005450442d9140d00b01d614090b020043c1e02c9564284101c15804c05240d42c84468a1f009101c0015002c800c03461080710b03c089405010031000351015600348000042400c082004244500045900701c4842c07001c91542e1800d00001845190194010140ea0741155990b4225404c0320b1a4100c06a8440301d012a07040c0080c0581d01c05009035910042c0c6810050915a0a4408980c0561502d4040d0b1091040050740413044510092444c101141449010f0480c40a000556032024101c9880803061144040c404180c406c216401413007282c422401a6203014050700c034510407440812030400850000507100800f62078403c55007940021400340b03400045c0000c0d402228440016009104542c04140e042080002c8111043c1c0e244011351620b41148030050384560f0003c0d203041030004d48401e51301640340c161801c148155400c0d02e06072400081c841e5a94012503020040c43d401d144000c5807a51 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 660226942 1250 660225692 660225697
    0x901090501030506090a0e03090a03030c1101080403080a0b010224041205090d0b1015020d0921030c051002040906030c080a0809010804030309061a090f0709062a030806030d0302 78
    0x50020005851750311110340007030042c1022101009180000c5c454025942d8039180c0250046001e92034850b0002198038200692405ca4402603040c07100c280140008a41d00100040d444818240c0006000c040200117074a012540c0d0b541500d0049248403500c84141c4801e1118062441920840440150000c05841c240101684c0c0c9030016502e000c40700200c3c142020b00c0d0782201e8070f0b040c503503a09511050510361240384091280d01503803081ca021000c1a44c004200c038000c16400030000d28100b00711000c8107680481e4180034003040700e02c00390361090150900811801c043d07085811580ca69171000701c074002d031a10388820303148200e00c5000000e00d070300007203500d1108642c03024002d071402d00e00d40f00654003100e029006800f05030352410444c000610398401c5480011501071010844c3d03036408204080d4100040030200c0c51048070050158039038000850303000340c840c0d50800d110216221078a0144200c0c0a07040e5010112140020704181a00b00002e44e000384400d60558202c030080c00020303030591 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 660228192 1250 660226942 660226951
    0x1a070903080d0c170c0301030309080601030c05010f02190b0a06060c02061608070501230a020c0c010f030902060d0218100206060d15140610020106120803040602070c030809010905010305 82
    0x61400c10000d150380b02c9990000a01c1101800e054400031401c2e40310745a440800c54095007a00c40000c014424580c000782e0540c0101b4000d0020f146e030398190703902c5444492035807003684e05001c00b80c034580906e40c0c002d014811415041d50350056040241d42460308603420195440f42050740740c408c020070070f64480c1d0401c0382c2c0c0a401070901880c20b481e2450420201d0480041511a00c00034080d01d00010170a005a4204881107406c024498100c0210001001c10150102c0340451040050f43d944131400f14075150002c109007080c592900890405034040c107080c00c1c00a6003c031000810103100d180c203502601507080080d002c00310b00103c2500303001e58150210b840101680c480d00000c1c00c940343c00740003040300343d114060181c230070031401142d030094030072071003008103800c81050400080d03040a0803400f0000c0c1851000744610307860b2030180c00c1105448000034010403400030000b0b003400b584d60100c8042d19440204081144c0d0789080003105a00130144450000b0003592000440751720a00881d03008 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 660229442 1250 660228192 660228203
    0x30b072a06151a0703050412060207050d0906020607030e03090d05010e012712030906020d33050f03070b070305071106120604020c0f0d050d060b040e06100908030301031a070903 78
    0x403c50014800c402034101207000c8040010410011030150011000f01e4903580c0f242d000944c8a540300c0c078040b4107109241ca039420802c03004001c05c2002543c0000d82c26088400d83c200003404032070302c40b030a601354850800081e03041844d654002d002c1010541c809800540c3c0d11000b00007085601c44004000301503800f01401c14500340d0b40b0786011a2815070708901c0308ac03844c100000c42040ea40e0b2405c060b1f8100c0991034001c5d030b9a030f6101c0310303105820344142000800c46000242e603140203035450001400311809a54000c01541001d0103158904001582c040c0622110f1580c42e10300f240340c010f00541c4003600840392100410002000c6050920588081444003080501c0da41c1c0c40b002400020342003000c030904144200c020340010001d040c4884440042941e90f03440e500d020010141c41542c4040d8012042600308100800c404081d450105400c01005c503160380384850007400c102d4107050282c02c25500c602000000004010045003404540c80712010300307804a0b507955500f03a542084920006d0403 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 660230692 1250 660229442 660229469
    0x3030702100512041203050901050606190c1a07140c03120a142d09122a060109060602190206210a050a180c030b072a0615 54
    0x51501d040084021505440c080741003001006280000040a5509641c400c12402c1741c00d405541c035000e400e40c4100080c000b4406804c141c80424468440c0c400031000324104001c0c15120740b482009401c900b19003140e4680b0042d21884a054096031040d0f9501011410348031010001410b03190641c3c5500480801440c20a43e02d08019503a000000300120380141d551010b2050184011488a000e01107561540c00c5000e1804003030802d01d4044a00407481d40f0b540d5040040441c000183c040c0c940301035444a076100d040386004a485103240c9644188050300c042c1840d07a282c2000100342d4100e0b00075600071301c425940c0303000903a2922403142c2c03024035440c00c102400002d030400f44c000788081d0700f10242d031550080c00080303c503d502d00c081d14411030103516207050180f42d02c5c96000c1c040050142403814101c404450f42c9140750a08a0700c001018442007100240c806402441500040c00c4000122040402840300340158064040c030100d816510340800702c004000740558805c166294a1442e00b03 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 660231942 1250 660230692 660230707
    0x4050d03053313020d0507090b0717070f1a0601021507020c120f03070f060614100807050409060323030316032417070b07020f0409021f020a05070e04020303 69
    0x101001e1240c2d5482c0d00482d40c619807502e00340e05072004180c0340d014032400045506185900414201140e070000003500070900000303004c11002c1d254001c8400402c2010381d0350340000d1909100c800301680c0080d103001204010301d0b45099516802174441d00099081d540c83c25400940d49810300e50070b07512400103030721020f00200c5e42d007821440906040703e44011600d45614400b005455a0301085040320641d240811407000c1100074003e000141410074100502085c00034040380142c010040d600041200140109070018025402c0700e018004002c4240302c41d645906011400107060503c0072102c41c0c801079254440d42010094070300a05038480100b20384648054201d01520003c05071507054032a0362840700642c4a9003114100078280400d42482031080c801d4420b0502500d9030200b100703400f080060800594500315064030022084400145d1465140003151118212034400084805402825107102d5000142d080c1034903ca03908541042d0703141c00f10742003664415500250554030a01401 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 660233192 1250 660231942 660232021
    0x317160c02010903020a0602030d2306091009091a0f0708060f04020d05072f0604140a140c0a060e0a03140f0303040c180b01140f0702030604050d0305 66
    0x4080d250700500d041c520068490300000d14401e0194061409a400001e290f0240c2582d80a002d8480110900111001c0e61005d2200e510246c000d220b188141c4610000500c5402d209050f040034150b07800d01080743c02e42500d0216117403c11140000c94110075100082d0a41c01c0d220826071041040f50356016243e100c40c0240500e0b000380e01d0311240d01036000d001500c045001403280c42d03c1703006181d0715280c1d0303085e13050041c0305400d081503d4480e10324070b108145031840c507000a034030350055440094442032a404401060504004400040443c40d080389180780941c40010841039035441200c0140d102c9503641010b840754803000580136000400c4610420114244ca066105112403403802c1d2402e8080200409045a0040358100c88010a1a40a024081c0158040000100480001c05c403a007006400a040e443c201d05c1ca4040c07240e00007920794844242035081d80d4030740d03902400312040c5081520f0030a44654001c0d007500300203454000003c4a441460036040b402d0300700c00c2c0c1c54188900915442 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 660234442 1250 660233192 660233207
    0x170306030c0405090111070c050909070b04060503040303090b0907050f030c01020a0f0206160b040606060f050306190b0d09050c061c020d0b060d050a05061e0418060203010e04031716 80
    0x20406603543c1c1c3c0c8070348208a1b0341c40e0000d080c51441101011080c2d82850200580000d020340701c43e03170035840b04000b4050001c0365801c5070f007a6800c500782940c99507103914044015040b584c1e07004080204010510880c0750b40000c805054480403242513100a04440605640c6e409400e03400c3d0050380101c40384d1010900107980c4c0707081c00c1c0c0081e0519141000d94042109070204001040314a0510442008180720280c410f0700083c041a00e0031041056044070010b00318017016140510450104503550701c41c481c0f220000c0e00520201d5a000c1d210b4640ea4000c3e002040c81c15000c0c0c5641c040c0700904501482c0c82c004641c0016200304040800c44054140e00d0020340006c5070b016100c0f030759000400c0d1195034200161054081c200b4000c160351402e00010815104040e00317650003a041222050f60303000c19072200c00140e8005a40c0050400380a040da1a00c4195801002e001148000300214105041c5024144642c1c040d450f9005480030070490402407040c11526501c1c0032401e901040c420b1803140717a1 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 660235692 1250 660234442 660234451
    0x903030412150203070909050903040e040201050d1e0b03070b07020102150a021c0209040b0f0906010507050705120706090f0b0d0902030309090a060f080a23030c100603170306030c0405 81
    0x250801c801c1e064800d040304a904c181c62440104030100b1040204030414026540c1c001c60713950145080c40e1400c80b00728140c0c40090002814828045904182c2592981c425158444401e86d10082d0410140c02d200042c00c0e1090824040d024051001c60b07202648001c0390491913060f8014404075455480140354028054002e0101c65005c0150003080c110190401c0f460400c040e50043c0c1e40d810903000c000031a6010348083e400b40101140751182980d81d0f019035030788410282002540c948091601d941020031030b402850344180e03c1c2c240d0317001a102c000b90030400d84950b601d88140c4d0549800942c158030302c3c1031050183c4030b54100200349071102c0c6601300301d100502c06002c507800d040062001030f4803080100d864002c42a55401c0c100801101301c640074000f00001000382c00407950544440410002c440a001407100540714038086100302001115024107610307003901c08020f001500c0c040608000d101c02e0340d0110700c6000c0c206925180004a90180500400030190405503005100c040e103001071 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 660236942 1250 660235692 660235703
    0x110f1b0111120a080f040213050903070501060f0501030608030c060103081305130b090a0b03060a230106050406080709050607061509090c0f080604020303161e05010f110903030412 79
    0x2180d0104205041000000301e0000d020015202c181148005040071001081c1e11000307000d1170140400340c0c4400c581c007413080200c00d00c0840c0c0d40c0d681003101441d5100e4030000402c01c3d840c001c00081c80d5070146034100306440c2c00341d07403c2c0082d0343c1e40c411840c0c0d240a402c0f04800d00d6046900104002103001c4c00424041040c1d0a00000450b900d000141c0250005d6554200d15078170b0b51144082e42c0340925203142d101004680400029074020301103a0380e04030040194410503542c004501000100002c1c5c8480c45034510a40101503031140c0005040350454824140401c1c044400700e0441801880c500c0d040c0e03072000d0040703400d01d15580c5950014000160489402d0107802c04040b440460500521680b00e0181c0d84491040389494040c00004a26070f0003254035410913014040142d6005c011119a04002200500059881e06010115400c0400908204240d8501c800108601074000d41e01d0300c8028030040089110030303c049040c601c03c14104c15819082040144540c50004099403420390040 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 660238192 1250 660236942 660236957
    0xf0108040c1e03080301120302010606030e1e0c040e0d03140c0a0c03031512170a1403100506030a0902030105060102060c0a1b0f0f05070f08030414060c010615110f1b01 74
    0xc1d103e110704c0354006e8000040b10303401c000008080c181c09008540090a091404100500141c000d01341c40704139409980174941c2c20b2200902020780104902d125007800108100502d04003d05016990160503481002182c00c003c801a00b20050034000307846441e55a140302e1600c454040e0480e40018040411014542d568000c05a407292120700d200207440035103c25000800c03e420180d20b90900c0418100c8540010000b030000c259002814540b9080d00e6164107032039848103e84c1c15207000703590f0132958100c50040200555180550801c0940500940080080f0b1300c90400481c1c0f00c032030440d803d00b04058204913104120344690000c5016070915142811854041e80d01e240900406800540306c2090602980040c004d05111940c01854a48039249600c3d02e00301d0455140c1c040c612904c0c004000d01c1d1400c4005403981c404582580130420000c110103611801010301e080b4400000340000740055242001591000034018601d00300c4800038070a01601004051241603640f500c0e40c100180c1 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 660239442 1250 660238192 660238199
    0xc020d03030e12030a151406070302030c0a150609050601080c0a02070b070501050405060c03070207090b0a09150f1d130302030702030d02060f070c030516030324050f0108040c1e 78
    0xe02c0702c800c1640c0d01003509503603800c10036029402da074011b500c6011840b0a02c00200110250054048001035090700c0813a01d079400c07401c2c00c3e81903010354003c60001d80100c1d10000d0421544036151002e100d0038007010424207403a160914110351048031820b0109100703801081c03154001d00c0182c82e0036815403045907605a03c1c0c00001016411034401210789070b443d0010f01003008002c1c03100c1580800703691607180c01e5143c0001d0085d5100310520420304125550604008603445e1405607101030805400140701c0c90a40e80c66480c9204000d200e0405203180681020441c6011030001842c400c203400001007050700c0b82c2903000c04c1d2a056860480951104010750001602c05010708590700c4016000751110340390001c0080d11a00004003c141007042c1034100fa00029041400d64814040021140314485600d1609034001c00f0880f0303801100540c00b40c500051604803000324020b0f0791302901c1504503101e9480c01503469840030f84004180b100810010304c4402c14040614400b0345510f000244401d44c4c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 660240692 1250 660239442 660239471
    0x408010c0c02040608060f010306020a02031303110102160612051819050f1203070e0a030c0b04050f151e19030b010e01020a0b0c090d140102030121030c020d0303 71
    0x50080d540c0c0c01140190103000705514261040f00024032420300a065986000b0038903200b910014040201040d60118010003124070800941c1e5284c14401c0c0c1c2003117040e41700d003060695201d40c0c440b000c3c0180b041c1596420301341152400b82040707071081c0e103c4011200c02200e09501030100141a18594540c3c018040072071003042003550615840e80f000c1c06c81c0030070f5034242981407184100385402d90750b001103410f42d0320340d11400440b5480026440c04105d0f202c039000001c1e00c4000c150307101410345401c40f41c001c2446460140204103c07581102e200607420444000e004491100c0030603078041900510032214581c8110200342c1045a005107914a49684528150703031400741d0b5074022000035540c500d401d2007942c0061962410702000d00003000d01510f1903440c0078050400400c00b20314071a010601c11015101d4078420010725034000e95130a2103054a00085000750401d1064194000062945018a6241c02c00741d000458043d928258032041e56024001d07140800345044042554030006142c0701c06 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 660241942 1250 660240692 660240701
    0x60f09090a051b03010b0a05070318090e0129041512110f040b030a1b0f0b0d1b02030a0e061c0615031401030209130b0711011107050a06050a02040801 66
    0x150070400020b86040c100d0000100c580f1201c11400c110f2010001400542c0c0345c0010740c2c90101071880c2c00c56071580c2c5032404981c10003204044462940910368003040c2c0003580d800c0700103048565002003007078010030390000c18611102d040c064055681044194203d0400b9000345240d60108040d00259039640d10119650200680056481c804002500002481d190800e1642c0440c1114117020302c01c100c00009841d102c03000801812520782e110b50311285c00350844c8510007480c000c071030491403e58540a0800d01da2088004c54805032801031511544a2011040700308800c40e07500031801c111b8854400d9500400c460345a60313100c40103011500004501c0c2508081e10306400c03501242c140d250005509143e0078800d45101031504000104601c802c025042504481d0111440e40303680c1c0303035520618400d51074a00f0280400c05000c082062042d0030200048203000c68100030842d98241c1501940780d80104500100301d030304082902000700d01c0541217142c104082e5200103141c43d0f0303a40344180c2141c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 660243192 1250 660241942 660241951
    0x14060a020f1002070b01060e010806130f021321030c20040c02030910050315010806040906050f041401050f01180e1b150301050f092a09040e07060509060f0909 70
    0x40c0c002480904221120321101c6c0149418244940c4000c0d41c000040c2c1203490040415010f90941480d03242020343d140c0100800e40a130080440d07503218040120a02c0c2c3d8818000d241d840f002c4000705450011542c0d055880c0350360569102c003800041951b415034014490560845035182405049181b9507071b512401c04800c2464005561391085103003032082d043d12904091040c04024000c200000340031800112101c682440c040c1030603076800340003070b00032b1100000c040d00ced141c9400e040294901d079511020380518000e583d448180513400d520503003615401c440303040c01c1c09450b50040080641c0400304140700307603c180000c114109100007051604040b004100c0024042c012211118203103540000c0d5101000e00c2010f00c1e560402020034404001c10784414003402c4a040064490425040c4d4000700c0303102014a41c0c800000c1c25690840c0d80c11110720756202c2d501e4001c00c002e8448000600404075951500c61034104003043d800c10003507401006801c810280200304c0c021881e542c00b4280b6228 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 660244442 1250 660243192 660243223
    0xf070b03150906100c0203070e0a06030302070828210f091a070807080c0109080706050a0218010f09090e07060201200d090c050402030906060306090714060a020f 71
    0x101c1c50410510114405602811802125840700340120b40e21143c0041c81c0108107400c00b14120403c500c0032a113003404c603030310042d90351181500344100502c860300204103c078006d900b02c6040350303102da00660310f0755005196002030001e000081c995400b0010f6145d60b1f941c4c058414040350608250540003242131460304880003400400752121360303d4011784848040c085100803114944260200c0300602c2c411890083c0100c800841d0050030004450125210f550120340280412a640c1ca8004220342208608403070481c14040064040343e140e200b502c5100c41b80201c040c00041c103035001919a61880f2400d08104141d01c5801308101c1c1441c09002d0130100309600030040355103091002401c584061410043c00c1c2807100d04803c41600b8101990405101d5000001c0c21060510384030810203c19800f0b1034100e0b00100c200600f486012078240d2140b80305030150394503071f43c806508a48461540c00349083d816000306140019040a01c050207111240e8011100003400582a007441e140b10f2060340c900 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 660245692 1250 660244442 660244447
    0x905060711071428120b01050906010503060d0221032101050a03051b0d021201021b06060d03030b210f070b03130311011407170c030702031b0f070b 65
    0x107015000c1119a00521402c0300380c41070003c20b4000200901648260429500d8008282201040360460030300002d1500c40c0c41d01a490001e031400c10846c0b8001d11900348146401c84c00120294014002c80c0e01c01c010051060280e0f45480d400c21108101c01c1c11001c2c0d10951443c407002032420104002e10020380d41400c05440c0c0d6038440400e00180c0d1050304264014501000100001100011146a130041981c409a4503078882000300c0e001c8400120007035800450900040042d0030198001d0810841600f882101000d6001030302d6610b400c20b031400d540010541c0907200c0803078480e621154018100418084181c6c00c2248600c58007103004d4100441a0490204201c48070010000c160041402d45107040c00e511f011402c0c200625440350001d41880361220b83c406400c1800c1d4021007030600c849540d1442c41c1401c0200401c0581f0b00c00e0503041c4901d0590100f01c02c2da0880342520b101c0c140c55030041d0b01e04140c44054120006150204165600c80c0351703007a001900f030a20900c000303042c078680020b8 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 660246942 1250 660245692 660245717
    0x15070f06051e06040e062e09060e070f0203031b0f03010608010e0708100509071806110d0c020a05061b0706031a09041523040c0503010605090f011809050607 69
    0x3020001402c440d1090381780c4038020240e64804204c84e035000d400d10001803a4040c0a105080100002843c00c01c0080740600e00411000c007158400307001d44060030015a4284e5410300191103040890038100056841400040c0e90764500c51104905080108040c034242400c69400f4007480d04213070810804150601c005020000740720162a034001228649200c1c41d08006400324484406805520300611840e000070765000e02030741035625400000b00c1e025075032564880d4014021420840341491070f00410704d450344490311030a41c143c001600100400310203854481006880d601105203006949220a42074203142c00610080700284a16280480c681150342110514111030740d0748144501d60030300901010481010341081c160402c1c410010720302400b481c5803190a03005502520040e15040104010424a148100700f00d030425002480b605496208100034190100ca000c00c03802d103d4401088454540d50303858a130160403440c00202e2080f1500d90b582001d80c100d41600108800320640c4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 660248192 1250 660246942 660246991
    0x50d0c0302030d1707030b06070f0605091011090f01090510080a0605090411040f0b03070f1814160306090623121207050f0d1106100515070f0605 64
    0xd074003d01003841c043e042c81000d91055100e55201a01c0401056a600400d59442e2a0740044070b413074030740002040c0b1445010349800f4000e0641110094130038040c40e45001a00c4100d401610003d43c00042d0042c10310b00321070f0038007825040c40782d0b00e03078100070082500046c283c881066806030700c1090f40e25081d0710700e40024041d050341c506622030342c018003510b000c100c00b00c1c00c54403a0342c0c03a800e400c440101d048050400c806001d8002e5048095042c041d51500140352000d0302d0070304088a4001e0300d40c03c202c20080c075690084801215808608201410001d0761104100fa24206c42600c03e050000c1c005803910301840456030143c000c6480800107560408038110075000c3c00500810481d0100740070b40c0401d07200c030784510291034040d071840c0001c200d0300d040010034018000492036078400c484810001d00401000a050440001054060113011914941249007904141c81340030f8040143c1ca95200605500780d032007954213640700030740109250300059050007800d001d4551902d050003943c0c03044046 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 660249442 1250 660248192 660248203
    0x204020c06180a03050d02130302101d0a081f09050102042c0c1b010608010c0203030f0a090218190e0d020c03010506180405030c03070606060e0603130b0907050d0c030203 75
    0x2101c00720383c0044007050010f03a00500704c42d070100200e603001da2035010301503c0c10884141ca400c000d40c48100e80302e88400003680001840c4058014510070040d428500c0d050102e030b900c003805019031075009003445003841c806014800f001c403d0708030f0300000e451036603032a03c81c00c80c0c0243e0005042d82c4600341407481020043c01003c5164035844d0803200341400c0c000783d048a45c0c802c6400d4a668000000c24428030004207500110041407075500902c410202d2081c020348a5000301c642d03110b150b0849000c0b50004803030740700e100406c0d540a40750000110042c1c1080e07441040080a0a401044940c80082a92054000d91041343c071704000400ca104041c803006801d00f64400720b030034060b0385420300300241645d0305900c1e089048001e04001d1185c0d20399040250542c400c003481241c0e01c0c400000c0c044100130003a0f01001c11125150340f4003c011030b0001c10810715200035220104a0809542c4103000706d05c940e50700030f82004450341141c0d559a6524041588218a01420b66a1000b480c20030025030400380071 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 660250692 1250 660249442 660249481
    0x927180b090c090703020a1d04020708030103060903090b070308071206082b02190809010320030f0f010e07030e0c0a030308090f010603081206011209060f060614180d0204020c06 78
    0xc040d400d0020040000304480c000007140044048a03602d0520542c40380c0e411280c0bc1900041c1c040d40d25078407404c1c10b501034020705008a00080c150340c0f00049100c200c9090b14101985a6100407068a680a003112005109034081c04216074030540000c1001040000e81d401001010081c14100701c4400d4801600364a131240d40e095400616a41e05410005d4911580081e48020030a80703800c0c030080100c0040c1648480070400280040c03c000c4c0e5403180c0e00c00f440c810580c5500008056903585030b0002c21040030310940600748040c40106003441d01036040421501c0c0d585007100c80c0b40741250001202e81c00c4035030081d00401c0740c3d00140142d039002402170112041d5000d009002d0585165203c54840c42540d022a80000170440400c02c1a80b0510407440b51510b11082840300001501340700c0000c010103140e000105150203000100c03a8010840c5252060031811b4450501e180058180c509038000100a6480b201060724413005135524800390034070341411402800790385000d1100c4400300c4032521 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 660251798 1106 660250692 660250697
    0x191403041205070506090d02041806050a020d141005060304030e0a1d1e01090b0402090d03020d14030c07030f0201020d0608010c0927180b090c0907 65
    0x2200148142d02650581c0d6015a50300b041180602c5407200c501d0700940e1130740014000d49019407106084004081c1d400010450b603982d0304085807011100d0024495000c01e6150150080d071141c800c50b43c0301c514010445041100114501c4145445924810743d0700000207010184100c1e446200c0070000b44c0411041516103181d0544848222070a044440103030001480507001180058007145545c1c02030000c03079013000b24071030107459211007003a001902000303260500c0d221070320b00801e071601a902610290f214040f000307019500c028080601c448040c000d01010300c2011007106c9042d070b410308141c1b5008000c64000d0703019004240710030034910305e0503100142c281c006403c82120210103a86040450f9240d244242ca03468044031513141e0701c0100da44510040f07845500c120004400c2c0d85059100302c6403640c907000007001c200c034444c1054000c5500480d4a0400040c02c542008050 = true := by decide +kernel

theorem cover : BRFrame.Cov 660071942 660251798 := by
  have h0 := BRFrame.cov_init 660071942
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660071942 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 660071942 ≤ n) (h2 : n < 660251798) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
