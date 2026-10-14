-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2736
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:35:21.428352+00:00
-- url     : https://prove2.me/submissions/25a507bf-9127-4fd7-9045-75f7083cc7f2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 491906474 ≤ n < 492086330 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 491907724 1250 491906474 491906477
    0x430c032d0525030e0306090d0f031a030607080105030d0903020306040204091e060501030606060e01022e09060b031e0c042027010e15070804030f0b01080d08010303 72
    0x180d412611100301c446070302003038988049031900c1d65402c920b0603002c21005030181c800d03251074004030982010f00d402c0042c0200050b225401001d01d00700e0241c1c0250300100f002015240010740c1c0c050129150003d003541d0020140c140c4a070341c0400050b02c1d040403146060720022000c64a06001c490021120131030680002500b41d0058000b0800500700740e0840c0c900907204503616044c0306c066040118107a400d2880a46000e503c03040100280920380c4640d001402c4540307001e80b185550440040d40c1e6121403a103208003190283c0c01d800c48005031507400f801040345544244550f880d1070034100080c108508009100e4012751f140d03070b51f55000181030408074030b082c0c4018002a901c80760800000f800c44128024070290001802c2143c1c440c864010f01e5050000c1e0752107051110b0541140d000d69061080d8181848019103d4851603a11401008a00846140e50680c0d4042034580600030b402998001417003070004000c124100400f00b1006030680300c01e24101c0b080300f0000e20302195880303000e12001c1c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 491908974 1250 491907724 491907797
    0xc060a05040e1305030c1f180311070f081e0303060109030605070c0803070f030c02030901020a41120403020604030b151e09060306430c03 61
    0x29046030481540f0605090102d440625291101d50565022003a01c40c06508500c0080e24000c0100000302d03e07044180104122400d10822899080400d050010b014454911242c41800c00b040002901030100c610408003403568640043c1d41c0d520b940d1310034840c10000680300384480e15000054903c100d0050b500d900d105803a54841c01c0c02447e010b0840c40421421080c00404a0b01c0d900080d8081d182d2a5203900c0c2190f55a50300a0883d52402a460210b4204007e000b1709680d000482c0558682c004081507407030340d45054403004091052911610b49501c50b401581c008071680a80b15110680703c040d20b1800c8403498460000d4170590200075407010041c0f0062001c95040c40c28154000410034804c0c0c0baa00740c2d100003031120302144141080e003008801c005a02400c290030500d4012000f540280f001d0704114034101c58022440f42c024401040801010700381d42c42c09201482050218500c09041d030a424100900481c9121015000310348004449007120061500e20403602c1c0f4a00e1881 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 491910224 1250 491908974 491908979
    0x6030a02060a0203040803040308031e0421020c0d060903170606071218170f0622081209070f080307020d02040b060d060902070b0718060513091d0c060a0504 69
    0x41030766041044040c04612080c8000b00308503008100400c040c2d070281e040b880c0c41e0f1070000441d940640c0d031070000d201740c280b1030001d010004805c9800c450340179070450b200200000400e80124600703040c0341e600325440100d90852400f40107060740000c00e10742c002d070b80b03042d450500c030200c648501c0c1c0c1c107441c0640c100c90100711045c0400c0709902c0300140c0002a2400c200341c01c502c0c0c2c034002c01c02ca03000d801910074526899503a0304444810880380081e000484040d0045207480700c82d403880109082a03c1c0000f40d12442803004104001049035891200e015907445a803c1140403075035508401e005464200e150b000d0b002c20440c0c400800d4540007035006102c03611816081d828071022385030b40002a90400000d12100750412401c0c02544c0c090002c0000040e100c41381c83c2011851350f04083c0c040014010000c1800a030f44803e41c003410305440003801c01030f03038981d02400f20461113101c590002c00010b2a08506440440b1a000004080b100100881c0c400d1105c11080151511805452001254081204 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 491911474 1250 491910224 491910229
    0x907140307031803020f0c030a030503010b09010203040503120706061205100e0c0301090f11040501050a060e0315070e090604060605040e0603011112100807030206071103010617030d1406030a02 85
    0x4581c811528036000c2015606007084900580c00304604074050f0300b00d40c84111054404200340340701484100d000702039280440d100500f42c0d100601a00500c0800060a521564000c100b2540141805411900180b012240c51525034010030382c201c0ba8235081031000a070207a58440d868082c642c2050117031107224060010000107061603400d06803640920b003290041d0343c0c0c0038402c015000703028400880d02510140740c4680c1d154054804c0740d21880c40c210040c040c81e21030801c000b0564040c3d00313207003038004c5503100002c2c504003907080710f440c45507801020000060360103052460100c0040c0c551038420b840e800100800d440050013110000780080c002000f00c181802c4601c0c6e0040b030042c000040c128000102e0319500c2d408090562001c4500d2001d029032a41500221001081d542c006403c1d060306590001d603580c880c03580043e115070102d000c00d0170749640039442100108004200c541c1c016203080304041d00c0380c000c80000616a032900707003505014110504c0841c40b43c44000e02070444a52142c2c00c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 491912724 1250 491911474 491911477
    0x21050a050a111c0309030306090903020a030f0c0f08070204051b09011b020303030106020c0a080c03070905041b15024c11030103230c1e0a0b090f090714 67
    0x42c41034031840350101d0380e00f891000208188180c1d089030b5000c0762200541c1000303800d40300e896004a80c028900f0009102183c1d002c21424a00c81d0b00d0728200d0980804000b04541c00c0207900c0019140c0c00c00b5000440400c07030060020098140b00390390030300141e41d818140207940000d2040390900603070100724484440d03100324406041d04d082c0c0c019002c00c4008940200745580c000b60030500140e4031868040d165468100c12030801000c0000c024000304005002190701d4180911a1280d0161910041000c014084040409003228a9a1403c50b1a038071703c1d19504101e0783c070030b004016006814030640490780686052424502c40004010342c81d008442225042100d4841da07410354940340c02c2e050002c0749600070001460703144001c0e9a241d50441c00c1c40d1500030340000000319043c40b0986c2c85040480041408001c480b012500e60103601440c034004460b5588503010b2643c41a115000407880301c140390082c0c000144195501e0101c2030200060108a24003920385001103150080084c0302082c1040 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 491913974 1250 491912724 491912747
    0xa0e04140c0a0903170c0114040c09020d06090212190207080301140409150b01020d0504180b060d022a070e0112060f0905030a030c05040506070f0f050a21050a050a 72
    0x141a50701690b40c1c1d121709000c0f43c40d014507002c150100080b00003d010090089031411782d00301c81e41500c542080d42d80d10704040118410418915008a00c55445503c0b55000b80010144c030030040d0364130941c070340c100178401d5000c03500c64514052a4583c00e280b5001c500c299140e40d035000b0b04807441c69007808080000c03c580042c24070f6000780c8401ca5440015010031841031080007a03040425103100a500180c10186001b6072001002000d00040146d4692400000e42c12a14950001502c1e007242000c14203502c00c008210a0030303030000441c0750075104c0781c0d1a01c50700010160748810241c98241c00b02e075240c030254880c840d881070103500148602409a0051000f5510844000840c20b1511810006480c0890320940d1103410109901d108580c060007104e006a032945425464942014002001c0d4010010090030408811038081d08010030a0846890f190300201201c100d41c04510707040a002d140041d2131030032602100b91442303480c4d00400903505d195001da01e03280e0922464501c02c441d000d141c1c2 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 491915224 1250 491913974 491913977
    0x2030c0d050a0519210e0301110405040f02090d030f0c061e0c0305100b16140303071d010905120a1515081b12030d050a020a0e04140c0a 60
    0x1146051a568620480e40422449a809800714080e6410200e0401384201e142071520076603031340301d400061500010440200350b0b58029451000007180d08641001031101100e4040d80f80c40c1c030f5a00098040c2010380b0440700e04603004c1c000c03c80c01c548503605901507282c4017900032078100561000a801801a240c4009861816041c0e000703454581c6000d44905803100e0101809018140c0d011010300e00958564000c1401c090050342019043e0014070000c0c0d120340c5c01c6014020841600d281c4a001360035501c01c1c1c01540300289034242c100d80701d840e684181d8102c030101e02c1032100074480d0540c42c9100040c1e003a0507114880c0d828582000d000c1c005032425000f140e41e014084100c0002601e80190410782d40340002e00040c0006900303420b0b4690201c83d0410300703407070348906200000c0161b505100c2102800558034401b03946210070b000f503c0c5004030907541c50154145002c1024070013856010703210b503843d51741d100503060318210240001c40c0e801c0c2e203a05003100410000030304045034481c020200882039 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 491916474 1250 491915224 491915233
    0x81903080c0d060e0105100c15022a0f060609010308040915050916080108070308032e030807020a0603050c0711031606030e120307053004030309030f0302180d0203 72
    0x4100041003100c034213400007240407503c0c00040c0325034140014100c8180d00302d030034090080081600c0340041042c0720728030141c2c910340002e030002c50761400e040c8075490480501e102e03440850f0f000721881d440c0c54400c0c840882034800d42c0006102454040505130407203030881c0e030240c94641400c10200c0a41005c03100390704055520706c0000360940b00e44030014455142c8810048007500c0041000f402e480c0103901038191a48851014004a641c040c1143d4200250390403107110f00c00c00e55202001a03c81005803507a00300001f4000061210040040280c82d02c00c45e0340301a42ca0300c0b02001e80403144151808040110140807c03400218042e9200090102c010126900c40410f100550001023458014400090b16030780700c04214401040002090341041c9281400c51510081c000c25074003500c00030040c003003100c02070403c4405000c1200fa105803000450383c840352410707040140107481d0300c0108071300040c0c0c20300511603001d00c00e10940d44281289052030581004000410801042602059071705018 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 491917724 1250 491916474 491916487
    0x504020c01090b2203030b1801060e030c3a0209040503191e0503070909020c010e0106081b06030411131b0207060e040c1103040f030213020f030c071e0c050406081903080c 75
    0x8d21200c24020201d694408200c40f85076000d05003002c61581c07800703005019421303510009046009840b80b040e440b080101804c105848035011102e21b401c3d401039000500c12080c0014840040001c03c40322840d4504490340100c00c11003118810381401690b400700b5441055050748a1052004641209051a006500e40d49079038031241241d121141d03c140e260355030301c0d1a0702104001e0003004000c1c49900091704203144d40e82691040240c41c200140d20500c3d000000404104840c1145184044064074000540c08001c0401d0001c0400c1c3c2550743c5080604800c0c0d1641c01e01c00641503040d10003507a00c1015000011041c000a4400318958205000034110b61002c000707401c20203031008200c06209081c4940c598014030980b0710020000706d003040d00400882c0e848080d07800c100c0c2c0d0007801da2a00955208500e082070103c29200c42c2281244a075166489410b0020008945060315000c890420215540743c0b001592400e0b0f01c5846940280201b480310b0200e4040c0020544c440d2034035220f28602030 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 491918974 1250 491917724 491917759
    0x18060607050d03050106020c0303130902131d0703061401350c030109050903031003020d0f050102180a0b2a070e010b041401050c10150504020c01090b2203030b 70
    0xb500800100004c1d03840d80108038550f41000744071614142540907618110090441c1e00c0c10007501c1c01009821600000d0070710180e01265071490041201200b070300704c0d80b03001000c111035400c000d40b000c0d0006400c040001c504080d0f901c00d503240710034058407005c10030840c0c03000f10445085907400601c15607445000d000c1c1401240081c562003290810009580c940c1081c118504807000a04001003d81c01402000307004800101900b098070380407107407043d106029141400983c0400d08008082c2c3d4008682880800805050004260307811548042c0303454454606521130300491050468800c000390340080b82903030400002d80360207450303016105002d44440601c5032500d801e074442d01c4101f400150070007050b00c282c5140d85100c0c0d8246042d52400c5c444210f400c0d690050109004445991002003110b450002602040101000b030010754580070300d804038900070312000e8815960601c0c5100050303410300c2585450105400c0c5080440503074070160310304070001e2038810502030300454040c2944c201c80 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 491920224 1250 491918974 491918983
    0x4051f20060103140102031b0d0213080c0f04051501030e010603081c0e0d0c0b070909050c090f0307120813051306060f091a090109120c0617061806060705 68
    0x2044a5002070109514614240d8031010500043c01c1e0030340d20500911595110103c1d1101e003a800c0c200702d02c0c0d22880a82c80000007441801c07400e040050b00d0b04400100078002007008444002e0448140c0c4c1201314400920081e0360084902c00482d18076081c1c0392a6035802030380480d000035000800020025280d0740d03503040d5a4060034180220601c2204141151500c81c0030340b440f60032140c4050215074500041c040d00920500fa80107042e030b5006400100b0561084030403074010280345005001c1c90a0411903010781c2ea2242100d075000f41e070f000400724518280002c90600302d440000984101c0c18490b00d4820481d00b007694240000601840009490780d150144402401c407241c0300000c6040c60700d01d014103900c460b4100314091007243c0c20100442000e030100204010519030039503954a0040300101c03032600c4035410201540030303a100480300380410511102c0075941c46441c0c0901090300e240424484103411a80203602208a600000c0c60150003070000c4d4200d01d02804040c02c0c201c0383e541d0307103041 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 491921474 1250 491920224 491920277
    0x61104060504030c0807031101030e15010323070f0605090d0614060a050405040f0b070e06041706010b1306260412021b0f040b010e0d05100c0504051f 66
    0x1071004a424428820b161000c81d00500d11080284035461459541c040ba845104241505169031201e49800c400010b1000d040c41c030900c5240407101c4e68617407401c92401101d5031800921500d00d80701000d40540c0005120b4166200030304084101ca103448000c40360f50f400125004c1e0003010020340040080c506005444c480850300b00080400e10300907007484a856a6944218452800c01042c00003040c0080b202c030449036000030b8a00e58554441c00203076000d445451406820210028000588074244c402d40045c180c1140240d4103e641d85416450300744c01003408840242481130030822a4a0003075040c60f101040050500c801d80164125440d0084822641607409985040d04070540c1941032119000c418070044030303080740850320790201c0c4071b80040c0c4140034040d0341e886007404126805200b0080c4103a40081101000c000d031854500d49844518620200389410200d5029100d070040307003690190341c0094841c802d07640340e440548001d0800100500180250061401c40710402480c201c0d02 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 491922724 1250 491921474 491921477
    0x40f080d09050114040b190e190b01080106031e110607081206060a1b020d050a0c0311091608061906030608060f090703080a050904050124030e030f0706110406 70
    0x40310407103410918251104249406640c0a00408100020300300d540f0994001c112072540c001c0401c0c010290000624030202c01e4820b500c20001680b01d2201d0710200c081c8014480e2004062a0340d80e45030f524240c803820301000f41a000031801c031130882c030090b0791240750850141d0080030102101001050003170b8050b51065640c1100003032034000100940780400d410036010b8555520344100e03544010010001d41c1e0040c10221821800e500c295526400405080c0b40c00406581403a6401d20704096007440074030044030b4142e22007042c020249480404075100302045030b0702c0e030fa881142010458100500600180e0b21043c0310090b2002c2010000c0640041c0c122500c00181c802d0800759080d14040c1c004110b42d1000c40c0480c1000503604002c45c0940407290300544440c1c0f10b170036016090700e0900800c1741891b0040d203003000000d1040300000d07091807031640c1d00e819045041600d003811400c1d5505650b8810b0558420841c241451312407000070481980a003c1c0084c4103000280c0c01086640558002070 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 491923974 1250 491922724 491922731
    0x204060f05010f020d0f030c17180d09140d02010c1a1005030a0807030f0903062901020c010206041b030b090f0705060c0c010311091f020d0509090f040f080d 69
    0xc103650f00018204071424490000b8880443c01ca18010441c0f1203102c4d1107000c140d103400c000c1c4505402001c06100c0300415000c620700f5403030203800c00750074043c0d03075926020301d03100724589140554040c10b04602616003424140e41e0400e40602403052211800b081241008002c1c0c41c0007020400c000c4040d10900c1c200200650356083c100d036070340821103c60300428802e40100a9940001d02018122014107030725041c0510294502101625841070340c0c2d00190015080030120301d080358030042c1e403495101240140f01000e414034001240d0341c1210541c1d40e40541c1c0010042000314413a460500d034000030000031880750649076945c90445417016200710b041c55018220a018100c030500200019040540f40700d428810034288440d51070810100441c180340c0e03581414042220224112030a40801800724403100600c401c0b005860304e00f40e540342c00140038082c80204550b01c984101c402082008160030065110861501508503020380116015003a8014600010308408080d000b4000440c4000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 491925224 1250 491923974 491923979
    0x4021f2708010e0607110c0306011208090a09020703080705041d060622030c05010e030d030f0b120c0a05010809030a0e030a1a0708070203043002061912150b160204060f 74
    0x1d03102c4e240441e040c101d9900300f40041f0030142c900007080c60440c0c0b64800c111800d0350b03d038102401644904030301190065688200072a000d10617400400d000d0703109507a400e0482e95504030440769030245004800d89030340d07001500b154090558040640000000307180e507103828800c40c000340c1825801d628900ca000b04c401070030000e0120030600344000300800c0c00d02c000030410f10b0001075169100c0e144400705041d07891000b10040040c2354080741c0c1010016045101d003402d40c0048a0352102421415403050400c150040fa0325485000d981d405241800025400c2000040c025548510544105505881809900d42c007185020f40145a0030410300d80b0702c4c0560400744d00040c01040000c00d00401e55104020812250381114480b000300601026140c0d1000c0140159805c8000e00000103035029001140d40d08030414001c4554031100020344540044d4075407442a4003d8403903144c0c1241c14cc81c00303c581002481425001416501030301c0846001c16440c0f039000400f251441c1d0070208881c640034509 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 491926474 1250 491925224 491925227
    0x4050a0b07151a0901080304081c02011e0f0e0a05071802070f080306151c0507020c0909030307110a02091302060f03010e071b0c0324021204021f2708010e0607 70
    0x5a071701400300d2102542c505400c00404550b00d030f0500b41e000312454140c42c44425030381d00c02c1d031221b01c02840d000c0650300c1c0d001e002d08002010f49400c1070040100c2e07141c0f0022607001180094581d01083c6d101c00070b000c0c001c1c0340840340005100c410120405440d0201301030000135041c0c205074a2020b00c143c20180d22410a4018014000516001c80319404810003e62810340302030309200d048509078260111b074956403104101d04042d422003407144c0206602c820321040300c0d4080091482018076a0303e01c40460307005801296501c511000c00b940042c000300114900030305000302141d4660010303010618101c248260402198001d030300042c4019104020f1041459201c0c03070301030b45c08c0c140f10f0400030b086030386403650020100c0a01c8000c03c281c0c0142c000031049007200d2818649146c1ca080b04640b10001303a1400d94601800f100c0403403117200c030001c09411a09124000000048480d44c07031450100c00c0c1d0801c11310040610640140e02400c04000188584e800d015180b00c00b00d180c00942a40c3c10305100 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 491927724 1250 491926474 491926489
    0xd23040b07062012041103010203190c050403150c110d080615091f0e04090b010311030f0d030b060d0615110105060d02091e0c04030c0b04050a0b07151a 67
    0x84000304a09103050401400321000c240c800003540104d2546003529145000100d00d54107072803180d0554004800c1042d440c0500000d07401040c1001020b001807000c2c1d40e000c881511840c080140795a60b64148002c104005920040b055401b41c18042d01e030fa00f940519526005101c449440001c40304c408000d264208548145a030380d00080a860420300404001751020000c5154018518034840209030410300c100034191100201410404c16181d0324104664168003d000940700d1507001403000d05942000030302a1103005116000e0101c003210028210701620a11103901c1c3d10000038000c40c012110184500d5005142252060b810321000000150001d503c080940c130070b5914020401c800f0f5100c003128a401a51304030343c05a52903a400200c0c0e080c98110b50300d80c00408010004002848200c440100140ca009005c60900140c0d22805101c07544201e005060300500790302ca003000482d1482001d13100d01849030100440f1042601d644000711900d001210300031000040c110611414006c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 491928974 1250 491927724 491927741
    0x9140a0516060c0c06030c170109090302060c0a020706080c0f03070306210203032505030c0106030312090201020c130e0f01151a0304020609130e01050f090105090d23040b0706 77
    0xb00140c094915413501840005a0b03c80d20b014581c1344c2001411545c0b06107171442d0a6017010302031443d2541c4a04507400184221b070720480c0548034501c0801c1010114038242c9202c2121540201002800e2007400c0343c4614000d4081c1c00606c800303000c0d020070031103645c3c05075201e01242e98000456a280c903243e00313801d22000d13016008160b12a0030354030268801204130341035180518048038007502031036000300c1d8511441202510345d00020580e40c28440341904140101c0e4003903a2440038a54000110204079448a000203000d688144c8214801d420840c0344070f048650804000030ba01415850302a05004c1065000d080c140d41d990042c15008400000a01c050644100d401c1400175201c5003103481e074070010b04041c0c0b140c640441c411041c0e0f90b900051181014000d1300c18001c140b003000301e0170f001c1c080550308400c0101020740003030b00ca10b50510490f4130a04c0c40d0300c0281020652001c1c00d80d0340340002c0307401111109145004280300c46241005100808502240e981e44444074140002100e4820 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 491930224 1250 491928974 491928977
    0x180807150b0904020d08090307080715020d050c0a0b06010c020616050709021e1b03120109050a05060102150a0204090c02030c160e0712090c030b040213060b0d09140a051606 76
    0xb00140405070311643c0c0000e0303405900014140d962410600003918001d0998010f05c03291080160100e102c401c4429a4816070721290215502c40d61103c8059845005260042c03a0a50000e8650340c0403030310802076150003081c181040c0c0f44604e921b40115580d90f0081071000b004186c01040a4204001004004001c06078204118201214612604011101240d0b41440a07001245c0103049124041e441072007162500c044a90740c4101c240e82c103600c088240300d040e008919100000345070360304a002d0507100303180c16230241080d52101c01320940d591101600c4070301142d07070901010582d04014400c4000e10301c4039030025902d8001c6800c44500d0001c0d0007202c0d031051045400304000200b10540080d03001241400e1141070140d941c215400100712104d00600900c246c2c42000040c405541d040c1401a40281d8450051555803109034095448a206000e540b000401007800e07000e040340d0000b4505407040010001d03407009076080510740340c41084169610b4003c1a1402c0c00031a8075003018000f010207 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 491931474 1250 491930224 491930239
    0x1e0c0b0d052a072303030106120507020d0507060c0309051006091104050102070612020c070608060102010f05061c0501090203030c0c011d010801060c080c0105101502030909010504180807150b 84
    0x1c6129581e024040d043e402052484225608516000c032142c0308910400c03040c003280d8aa681d10440285103a424402c0c290005180c007020441303180c40452014200b00458a5540c5890f4240e5228030040c9040c060b0f12040599038030050b000200c06002c04500100c00d8503000c00ca80e420150071804a400c02c011001001508010400c000d0341c012a90748119046800d00483d0007130041007240191145039800070550003024000f0540c1e41e000b510150184000b80c0c000c01c10103000e540d1741c104486044d5040c80e441065440c4251040c00c41c0d1120209603407040300045000c400316030219141d5040a01a6201500081030300150b55030b2000c03407106204460749480300d0503d141d800103400303a081806070004014448a03d00d050003491400c072144a0801c030000c0040303103020000701d0000d5480340581c02c0641160100c091800c0d20000503070344150001001b41c02e4503440d010400008218003012201c1542c2010111004600b1070400b1f000c01c5402841006c01c04182c405940301200e07020184d031031240c00f0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 491932724 1250 491931474 491931541
    0x301030b15060f21060415210f080703080f13030302030c090d050a020306150906101107060503220b0402010e03071a0409050a0501031e0c0b0d05 64
    0x40414840790860440903814440c0e50034000455454851010280c1007014002240e00640031910700580e2a1600440c1008540c0c80341000c0100f680c1055542152503089403400307111204035007102907511400c642e40c00c0030820140d42e40e02d603100c44801c41540e1b03840b0003141d000705054004070800e42c0301d59a40c200184500c0c000d040a03885030840030004d030030503902000181002c6032580455458210050a40300da002d25407404541d2102e80300001c9000e40070300340100e825007000d0005000803000082118096903183c0c1e05001416142444100410055625800701d1600030300c91480580f2007031b90307000d50302d1500d02d5029540000011002d070321110050b5002c00800da0512801ea040b0b40d0900e0101ca01741c03661350000786070013490381001035202c00c031f01c0254000b00700d8800100100e83c0b9200e401c1c842c56558803088030407590248800740018054111589000c0915008131541a02c038404400c039454442035400481e40060606c0030b04a5034901c1030004440706844160b400d079010b132115428154 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 491933974 1250 491932724 491932733
    0x6020703031d0d0818040b1c02010e03160f030c080610090b121e0708010b0315310b1302011e0201020d0515011713030f020f0f01021e030103 62
    0x1400d5540c0061040b4505912a0b956499018180d01c0d80084201d078580b46000e8601d41c0c22981301000e02c0c8620b1a010010718039060400740c44440060010401c00004490340040d50500c0440080e00d40c1801118102a0380081e800242009000b4030291150312504526142144541c15013181711954450410420340303800750145c4005031007030010049200c3c10800c0c0483c0c0001070340e111000941c014000010222459210003001c001440000c0300c05156817240c85070300300d51203801140e030141c0144c81e1680e050902c55620b1500300b1019480c21003442c0d165800d0341480c0f6207d0040c2c01c20241c0c100307520800e20045600654024000540005900ca01c640c0040c000d511100c140b000d050803852000090036000390f040d50880100e0103000d003c2450011a24a95400070395820307404900743d0b03901981070880040c901ca226814445901080d806036407400d0710144000d100500843c822003283e5801802c0a0002e07168080041d000583c80b00e40c5c00c0c000c2c25814071000c1045000600034801040440e = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 491935224 1250 491933974 491933987
    0x1605070503031305010207120201051b03040b060d0309170c1005030601121e091401180b0601030f1b08010f09110906030703060b130e0c03091c05090312130602070303 73
    0x2550f0f0310425075001d0454030f84503001e401f0781000500b2034402e03004c8201c6816010b400c4903124200844105460b146c5640c0003841c640000c0d035001c1c100448400000b41c40d41400310034070600d40e001e420100c02c141c2c0d44031003007104211003000640003030300700f00304000050034081080051418242005420f6181c24000280001c103248561620070b51158035007501c00d444803042001c10440e0303000a202580e8281800c41c0040c01c540c80c2080781d1740c641842001d02d8096031260682a5501101000390790b01c400c401100504408200760790125545e07601004900c140050540c6003070056103a4074400d626000b042484416103034480b10803039051440c00c0c9508540c000071a819550300f214410b849880b40c400840042c0840d410282e4090400520107444614030018103044880b92800318800d55150f94104540340000e0f04d024a00741e00814100306151f02040007100c080c80249130090429038004c00282c0303001031180c2125080340380000d40c0752402000d603150002034001400249182c0c2c0c599078004110 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 491936474 1250 491935224 491935231
    0x406030b1504140d060f0c05070c2403020708041211030601080f0c0103090c150903050610030f0206070224070b010f03030801180908131401030506100f1e0305160507050303 76
    0x2e8001c3d4101200f0080146d128214a217407140c2d080020000c52400948a64401142900d1160381114000b5000b4200d000c0c941d011070302034554059100b1101c0e4258040e4000a008480900301404081482d440c900580c10189000d402000e0b005890081810f08002068111161036000f5040c6000014400104808500c00030b1900042040060408000c0011940c000540c030410070041000d401307a00c01008010703240030f0000e0306c440d40c5980b450801c14000d1444014090002c1d118484054581341001e008c0c0d40b03001400a90707841d000104d07408600f0300341107003000b04540702103105018485150302280c0500040240c0504c500c0c203644010303101c280148034116060041c3c000a071480d0034150010070001342e0103d20541c82d900e0054071110344201c68019099140072210350b0100f198864001c2e98080c1034042e210740d64a4600300c0f0100c4003480e900c02c10a003805114444950000c1040d8035444a04141c0c0d0341c0041c4605202c101065034405000c40c03a403c00c002884014003042c800300850b80c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 491937724 1250 491936474 491936479
    0x4082d090d0201090f0e07120b0328051e0d030b060f0306120601080304061215140d0b090c090610080a09020a0e0a1b030c090306020706110406030b150414 68
    0x24040030701d10040383c1d50750054001c4202c0d41920000019001c9a00201d180601d400d80c923401001c50080c0d0301d150848040807141545503111441da0300f24440958000d00441901a4204450307000d40d448251400140c0307903161a1714200d4040c0c0c9144144c0c14041340718000a076203020701906480000080207802041c49180fa0184c1c0000403400aa407000180c4a0b00041c00040c0d400640c3e485095a440307401a2040700c01050f140328028451000d82d104440740010300715001e0403444d00b0a50851024590480b0700cbe90000c21505810300403a1030700b030055109501040c01401072030b45610130b100c6030f841c02501043c0100740c4401c07507102c402e07040b14215600c03400070301e400205811680000b9a03a82150340c085034500c5441c0707090000c10310158102580c01140701841c3ea5032640807501c210100c032504c4c42c103031000948456081c40010901d400400751540200c00200d60700b0081c1c07103541c4c89135022350b01101c042569402500f801c2c0c2400c0202080f801181141c0504040c42e00002e01c400c01c005003a03091 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 491938974 1250 491937724 491937739
    0xf0f0e0402060d02071406150411120403020c191a03130803090a0f050303070e03070503030f22061e03020304110402030901110a0c0c240507081204082d09 68
    0x40c1e4010f60f034159405903802c0340000c0c0340300d00310b081040c1d2960400c0c0c5035083d074907213228030211090815000b044848065041954a0405c0c0320b812a80183c20150040f81180213940072202c0b5545d03101031025051000080d20b0010b01c0c6044500310300120100030150b0941424020030600411640ca611a5a131300603018641d01d603201080c6906080200c00f00828a0034403505a40601c4000405544030b45425103424051854a0080540c0e940551044541c194010480c200b100c50b040c0e0007502d42120700d012000e451407440c00614070030507080d421410004441c0aa1041200c3c0740410010305103000b2b00341189142440d80707590400e4122007007100c0c069a000400700d00c50240941c001c0d1804103000114545500b424480201000ca5000e0280d0380845c42c014080f8490b4a0140ba4403003c0c41c1d5004400721114a400c07017610a500885010b540b0380f001400314012510380000303000d01c03462052841035510900200b2100410040f0039010f41c1c850409460385007500710640455816140032150103 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 491940224 1250 491938974 491938987
    0x14041d07150e03030f190206090607050c0c0909010504031701060507060506030328110316141618050c0a0f030f0b0406090506030105090f0d0e0a030503130f0f0e040206 74
    0x1556204603002d8402e826102c00141400910400b00c0903089941030b501e0811104020582e00300d07500c590550340d00c000e580080012500040c0250014007030040d041055545c50800800007580022003284d01c0645651203a04000400d54010034540031302d21000811585541440750040041c00b4006004004c1e40e034420116035550350410030f50f00c01c101000702200d4854603d00c0c01000e1848240c80150115065059540d0075803c040151074002040803107180c508541501c0d140d40d004018011401640145409840600f8030882e8286c0a49500d0311200104076902c1260411503900074418801000180110302784950311603001c01102d02149000700d6080781c0300c590a401807288001103039200d840c1100025180c1a41c1d040b40f4031a03041240200103c2d942d21003c5a00c1d40b100c0c04e250026604a01454510680506002c0300710b09400741400071340c25100c0d510103107503a00950501c0300f250141242005408110714850700a0004130b442e4400d44da01e44084040f4241026000900c01c0401140700d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 491941474 1250 491940224 491940227
    0x1e08070807031409010606030e030a0507110d1401090b07050901120e07050301140901051e2d0106020a0c0b0a02030406050f0708070c14030102090d0303050601031514041d0715 77
    0x109110400300390003e924284080150b009091520039440464180b542d02c1c0780e0340001206a0310011030549445142403490b44d282d0120114140314035601c9194845040042108103584010541580c0b00014200ca03440c140036642d4480205400b042007410059499141da005841c0341900400341c0001c0b4008451b84c1d000e070f04000054014035015840c00808141c0038002003076041c01985144000c0200340c45030b440820210162039a49100b141c408400320351494080c40c00440001f07031100e250f488c04c00300c8280c208203105c802e030711200042c2e0080f40b50400744280c07819514020405140500e15040003480c02944901071481018140300000c038000030000c02d4542100c0c03140b40d1080c000703651142c1603c3c0180150002d80030380710712401c02c60888002c0d82070500c01c0350300b094070090548000c1e095558048010f0403000f041c007810161154500351001c5602c804160103005400d0314804415400018441183c1412485030001000c1001110800c0008201d85060710b50046d00c0400c140b014840 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 491942724 1250 491941474 491941481
    0xf03011b08101a0d3303112e090b070c082e09020109090906050f0a1401210f1101030f05060a031101050c100515030d0806060d0608060c07031e0807080703 68
    0x17a4802c4031038071800030f110b0850302e4102034044e24806c0040c5055404020184001c03022040c4030380000c101030a0088854203445503140b409a859413419a1449846190704880c41e009000c00f264251610981440701c208148100074008604034400d401c1507d0f50340c4480d50304821041ca6403540c650703440080056902c0342d01408085c1181c00f00900031801c444c07500d503008041c1201d401030011800b2010440d07940c41400350400030810300410161603401e115003030b01480d84504040c1d01903507003460200c0029110b9284090042d00603001c090440207a600003509a9058030440600f446ca420104130b0700d0380e1749151301c0c42900e40041d40c5444555000005880030702c6030342184092489580034442c80321200c0d4000710304c900796554804041358900014150346141404e0780e50040351001d0b000517081e060034005800070740a982c2000c10010f0b9202941410204261140c0c128040009004018103070022003800740404442c1031181800c14040d40140896005040d0034100008a40482c1c0700c240320340c1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 491943974 1250 491942724 491942771
    0x241a0319080f041d160c150b28030209070504030f120203070f050609070f060e102109060b15040b160c0b0a020f070605090f03011b08101a0d 62
    0xd00c500c5104d030075100102c0c4800421a48a00c00c0c0744183e10b2048110700c143d00e030381b503456485481c3c00158001d490750980070b021520036203500320204881c4648111510325540d80050b00072200d20300c000c0d007180180403150300010441d01c01e00c6000c0104100288901e070141c2c20960300603410400020440000320308600c10101c0190640d040c094a00d81403010101c0c006004a51b04030844408a507109403680030880c1a11a82c0301003140014030344803506100c08120b00d22a80c0e803501c040140c0d80e20f03100c0d25011940c40618915607075170f040703d03408009031803248a904445c11109020301140714403842c1e9044c4128002c1050071140030401001e0070391078540c02084103a0200d0b01d43e0440b038031030009103140d411050001d4014400d0000c02106c01c5c40101c0d0040030f0301c000d5a652803901c0300a0050000c60642e100302e80d501503513504040d4680740f40120440d628136800740e030348144500f080315240742a002c0540010600c1c400604594904250043c1210b1044074045000314403d208881904444007200 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 491945224 1250 491943974 491943989
    0x501090b0907060f0e01170403090e0c09042f070f02030724030b010f0c05030f1306090e010e01060c0501020d0603030e010306061106070804241a0319080f04 69
    0x520a009800d90080350400a0f00c02a660301380400480010071100d50308180409408508007002941c14a00f14101003544140207081014085980b11440d00003483c04a42040e00884003046480080c501805180a92074044081c1c080304401c0034000034240542c401c00c0f180002000642d8020020444225a0300c95001415941c00b0340c0d40710241d60342410b40107228550714002c40c1f141c1461307601a106962841106035140380c11441011011703141e0810800c0b042e0f845201c1401140f40f40d42420005055007086a00d116022074980030019100c00c0036a0407011f4410003032130051000c400b102d4a603a044403828501070910001a00f44180240320349448a00061708150b804400d06410881030031000800380d9040027080da0703640003201c650340041c0810301c0ca40c1004021800940c8114102c60700240160170344203980c10140e00070011101803440d10034245071200000d020580e5544041d054200c003da02a049540300700d02031040001e0402002802c1d08000b04280c501c0c0c1d40c00e90103903000381809 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 491946474 1250 491945224 491945243
    0xe031006080606042921070305070e1003050c0d0809060a031a0402070b1b090a062c031f06051012061719062310080105190504050109 59
    0x201d01d000e980703814044030128011810802c01c901c0902c03180314800b542c15915960340c24074050100422006030256020004000704e1850001c00850042c0b225100442c400c00c014156145404025100d2110081c0159000c0c1003444040000c9800400e00c0b4844010031140581283ca5034600004107002e030411154202001241458000750180d12000c0107104101d44d00d180303000000100300a07440303131007001400c0001e13003c085801484003404d81610406030181d03407401c08821340d0201e840a084c81e8080000a4140182a4080781c00c0e043d480001a540703015074181c808403d400f090b0740c0c060079000800c422050326106c0506000550010700a4240201001243c20b454600141000154800e0f86045403070444e000421b650395201c0b9000703441c50a8080c1a01c0040b008000c80d000601d55001c1d90031649680c080200a0104504015040044e01580602c0d00b02400903020460041d000381c3e1843e85004140040f580c1c0d5620189802002000040b582e5560340c5400c6e4058415110000c02c0c01a0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 491947724 1250 491946474 491946479
    0xb0301140301050a110909040606090507230301050d0b07030608010c090314060106230c0102120703180209160306050303040603060810020a05070209090a0f060b040b06190e031006 79
    0x1a03800200c01240c08500a02c56912000c03840021100c4000301041c2081c0300b0440035889040100074150700c1802904002072059540051806490b0100c480b031001032500480404215201c0e0f0f40b030540c1d548042400c50966040c8808140700c0d0241441c00b900000000d0000391400d07100e90060070180100c08000d00c103100301500c0c040d21111040c002198490440460404003080015a8504840039640c40300c1040e0039010010842034920304c500b1040c0303002004005a4080b090005281075010b90245400500d410f43c4010100c03904a900c400f02e00380d1040142c2c0141c1c4e210180180c0000229040c6842480380d4032040d8010a8240d000343d4060002080010b80e154056101e03030f080301d101800b540c014403900c015070780032442140000d13400304009025480141c06c0c0824403d901a41040498500300c0603925007040c1803aa0204c00c543c1e40341c84a610545074241070250038150341041e05e40ea400d00310011011510001c0440c505010407240039141c52840e50204400074042071410810272000c3e4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 491948974 1250 491947724 491947739
    0x31b1505150a06201209040207140307120801120302120f09031c0305250f210501090c020a03390309150e0f0907052b0507080906041106040b0301 64
    0x142e8402c2c4250402d18090995113401c4c10104448900c3d402c5603070b0f0185000d01d0001044000c0d08940c1050794400348007101c0c203800032810402488078900070380d0039030203510154400422458058000342c0c50090000d603184000713038000a40c8808401403004180d00c1f10942d440360f020500606c0140d41e45403260002003080d04200021000c0100d80560341402a90740d403903190100d19010f600d0b0504600407a44030030307207107600c10f102141c00c40010b4134050490044580c091a4690f50051040c00726076a2000100131144a91040402c0d070b11090019106a4080c0e0f140a848a051203206040c0302501904050240ea040501c0c02c00b1015030006203d44006c0904004041140038081c200001c10318900d40c42106014048c074022804000f00710001c12005041403200c0c8600241540303083c040180890254244100400900066444944092402d03400d00b8402564000f801a406001e103040600802803008101154083d0b000745910701c00e120000c01194642c480c07035100f00543caa0200002c110030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 491950224 1250 491948974 491948987
    0xa05070b0402010e030114061201061d0604060f090b010f020d0f08130606030f0b0a060509010b0c07081b0301320709050d03050306010816050a1227031b1505150a06 72
    0x418003607503842504009272041c5402c030784513030090020964801e04480300d6201c8a02d80070f90b0000c8064404120a555460384056000d5260404069680c58002070030440d6401440302c0542d0140740700819141140c0000039000ca804a95030500b0445550000b5100640d140401c241035507001404120712b075070307904203810f8100c21550200c0b5884000004640c07100e4007402040300382c80b0010442c0e941a440d0451410181d03101200352a0703280200c41d00020b13955401e00c41410080200c411140c0c1102580e410142141c1e80c00c804040d843c0c0609400e0070703455908265401c65464800c0e104940c07030701c0c1d02c40140c0d074202881d807245034841d400c00000c4003059032003000386000700d800307880d410102e4580b1001070400d200c40c070340c5010019006216688055214034054080c2c01d02c5c444000880290780410301d11801111180450009000c604c02c0c0101984a900392914801c0564410000b01003603842c0340c3c1101e1141c1d800c160311900c81780841d6504200840301403901c000140111a4140e507101c014250 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 491951474 1250 491950224 491950231
    0x140d0b1203040503070b0901030e07080d1709060a02130801020304061d0c030d0e01090b040906060f020303100e0a0f0f0c090506130302090c0423090703020a05070b0402010e030114 79
    0x20010034052026015000069034141d4200070702a0880a061801c180242e8110f500e0403410507031038103950604900e050052130003a09206024044505000002400e0040e00220707068041e0f103a1020024000030100d00304da0403c1e0001000350340c6032050314000c44840802e4000034242e520000c00d0001304021503110100c0481d00640018400c0f00d41c0c0d070401d48072014800c65035055040030116200440c13140b1a50340300200141400039460303488424502541d001600121209a941c900a0200319004240500601c49a1000b5499840e000140c4103121710b540c411695540c0520303000c0340c080159500a800d60125903501007044000b01d940c5a8050006e0303074001d40206110074000329403428282c003124442c41d540065210440d156a003801446040180000000302c07050001051510f811111004403203c0c0240c4400b07441501c3e010051041c201070b0124080c18410401405410742100035114242d070001d006035160b0f0340e24001a500d500251140c29810f504e0802e0344c2407049e0011001c01d01 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 491952724 1250 491951474 491951479
    0x14010c0e0108010b07020910081b03010b03070501020d080a11210f0114090901060b0309030415080412031d011122050306040b040f0b0a0b0f01090e01060f140d0b 71
    0x400c0214040103480890081c042c0380c4102e00c080000030054101415002d81120b080b40078818103941e1020000d05200f07455800c0c00001170414640c0d0100d00c0d00340985031646030200d02903c2c0091038240040c1d034404190516009100c4808001810800701d540f0200384006080a01a41c5001424940701396001204c0f03648001013008010410680c0c116620381c0c1601c496070380f41454402d06070208888050014401c0820b90348601e00800e42c01c1c0007070041c0d4020000311000f561684e081200081c8003c1c40c0c2c1243c1400c004031a000c0002048154904000704600c0d4140054000c45e002c20401200c500c0824079030466081c51701520454403010010214000d40f10031034000e1404910103a0b00e00c40080c410180e05500000214011032409415142c110f84100c1c558100c94100e9960b03000314a200f1100f802c8030070f41e96220b20a10341028034075007551490900c1c2c011713040c600342a0741416480d41800380904002850803d281c106d030180c514904542a4041a20344403810100c588c0090071070ac01d1900d0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 491953974 1250 491952724 491952737
    0x1121040806090708060114120a0803090f1207080d1803020706021b06041505040906030b190c120c050c030d02190507030203090907050405100e15040608060d030c14010c 74
    0x2081c0002c0410400f040da885000508070b542d107808240c009422151143c19070051084c0510000c41008100c0b4242152103007425a44914000c0942800c21070020b181070f1a9401c070640126680c0349090485a8090b0320000e080c0d00d408684840d5402803007002c10760b0544540f0886c60b03c0503d500021020101d910035800c07100c040d4006041c1036803a040412256400401c180800d11030202092036044208615290803070800f507403541401c09803401940140c81294205040c08107501c0480690281c29074580014800050003110041c81c462010402c1140310303a40b8000300b46024400c10860b0000245003049035151045c0f002058002d60000e01c1d0781b0825800311000e080b40f54010f4040e00e0080f03415402442c20107000e60140a00e100d4000c03c0e5408020040001050b580d440c08801414001641e503541c8840728000c090000c1c0c16800e07100b03811411000c0c0000c1200c1a0b110841c154031981c162404107086065240640b5100122a401488402500c0f11880003910540c01038551521665840 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 491955224 1250 491953974 491953981
    0xa06200c01050f0601440c130501050f181f110c0909060703050a1b0509040b0108220203010213030b0405070509100b0703020a02040e0c1302031005011121040806 71
    0x151900135040f441c50415100140b035203a014018040206e01d0402d030b14405503001d00e03c6030421b05400c01c0c1224841c841d28008a2117140d05502d0148540140c5404e0070040c0c40c0ca81e0304171860165006451800f000035201c03062094642e207526030808080380c01180000300764048464060040381e1203083c08603851003071018a5403949000940c06028115400c0a88a10740351410214054080140f00c00c102da9106d1100911101c0349031455501a620780d0317a51511421074504000a03a401c1c144010b041203000014400d26090107095440a45801d0016103101503542c401709001e0700803029403001c1e239211100c000003800603000c8500d12032403260090751081520754041111400058404a0203154921000c0c4584104000100000c0d402030048901441c810b81c001025034a44540030001908070001040759410f000401c00c10401d440c41d001d40c00c41c6401c4020000e042054882c0030704204494102d03450146040c441900d15418001050100b064401e80b07068040d4401d04c50350b4014883c06001 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 491956474 1250 491955224 491955227
    0x60f05030105100b0a0f0e0603040b04211202070309050a0b07021005070827030105010b0a0306090e030702040c200a1406090d1101110c0601150c050a06200c01050f0601 74
    0x240c2c004e44100740c0070300341001d9240d0030881d9012080507200e800e0110008444030340e65541000303140f04600c82e166586da0351400e0302d40707042e4020000c02078010400149840c0d42101d40c00000140c01c48030009001a04c4240600741110754022542c0916000f480511010134880300c400c000309101d0b402a00d8183d504001040100c40724032409201404010342404082c10450101c45514501c1405c2c81005050002d008006030854000381c0c8581c1c105200050015031150701409480010041400c04100524004007080d80b01d1151490081c4119030390403102041381d0203118601842400722403100100b10124038681c0c3c0e2840260320582c0c02e00c0c414210360100310400604244282e11120203440050008042900c2c05041c60007404819503c480c04044e41202000107040103060340c00041c4a95450402140c14180301c0307012100401c00c0002d40300300030901c0040c407090413a40c400c100045095030182035001d00540f00d014040c55060000300c0e80d0b0ba1000541080f401a94001400e10541e1242d200 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 491957724 1250 491956474 491956501
    0x2040b03030a090b181008270709020313150b01021b10120b1315080307030f05092d13050709210c060203030f0f190207060f060f05030105 61
    0x814001983d914014000a04007801a04c1a0000442c6803400030151030f00217100c0307114058a01000468071002c1105020440c0069809040071400b00b1000441c14201552518880d010316614950004040341d03241c036264020f1203140d07400c00440040303107500e1905207001d4143d185803140107215024a4130890040120151200100102112407040407900c0039554040c110f610120350310340c1c440c1e540c107258031203402001c60010b8402001070381041e2070740c0c0c103c0f0340f80d80d42d00035100b143d1044c000000002e07044003100c072600c80d544c101182c8501503040004d08010810022080940c2510a5010484042c03009001406000c0f0f0300c4803c44040b025080341100c01c1119507900040c04180e080144405584202e1100000300c0c0d6138044a0189859103c2c4014107035201c140140c2c000000c00141026441d81950006403001d0103070038a04000001c005102e400d82035841a04d9800a031107401c10010394020880401803000601641d40e031440100c0f40300324030703118440c02075081900043c0401080c0e0f4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 491958974 1250 491957724 491957737
    0x3050c01050f0d0e0a1401020d4a1204060806010e22020408070807150215061201090c0e0a0c050720060f040b0703030b0f010206010306111605010902040b0303 70
    0x2091981420f0000101030054056050380046602882c80da003070110355620341084440481000243c3d0700e400c020100001c0b02c21001559592269411540031a01c20700043c005030081020311452103080d50310300710b0020314124031001c6200c0c40b40c101c900500c0c8010380040d10450f465a10741135195541d040056591100120b50741d6800015400f48800151540c0c54030b01c8080c01c145030040c2016282c1030f456181411540000c40f00d513205101c00c01c00e0b000c1c2c90000e01415200c0344041d002034a9000040506580302510291250781e03103a1541c1c40d090001d52000007143d42001c3d02105450340c419840c2c440c8002650303845502d43c03c001400c80c40502510444500c076601001203010942d40010681192040704c944d6030384031804010300c0800f582d000001d48040c184801c45580c0d13038030b01e9250107011912810000740c043c000b4890000016a008601c0c2411240c20810104401b02002e0300c4006070321910040e800050030701c03006e071014484150710030100203100b074400300f2403807164404041d0b0303d00030300 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 491960224 1250 491958974 491958997
    0x21e070f05010f09090f09020604180606050f19210b0a0f06140a0e060409021312030f08090304080d050408070e190b041107061b0503070c0602070c0806090703050c0105 74
    0x80c0720800c05c2024640c08026240541e100c009013114550740082c04c0c0f0352103503000d0040c0b08046014032945251501c88d000c02800c0c94106503140801011403a680d602071130800b019200c00900c090540a030184081190302c0702900f45c081c90003503c800208004140d40c51055006494a440c0030416251022186050710500d88454070712059000e08030406030301c00c0c0420010403007020040c65440e02c40001070006070034241005030b21211030b1310324940d070302d500e076400310311700c08120301c03000002c240c0101003500d2440407032800e406c030b965581d054580303148143d80c090031241c41883c0380040f0003031380b00e000303801590782ca403094881580d6190016901f508082e44d05100c556002181d00703848ca8420b5110b100506006000424103213000d011b5051103030000ba0091790140c5c0c49031003211603050190010221162139080407421030800e00d10003000020100c1c00102232550002d000c0b02489000c5076888010000d00e4201c2d141c502e84128841d071201c105202c125078504c50041e41c0800b540c0107a0640c0d502c103209 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 491961474 1250 491960224 491960237
    0x512090f090414060108030406030e120d051b130303140705060606210c0c0d0801030c050f1504060203070302060711032a060403051809042001021e070f05010f 70
    0x40c042006003014000c0c00c1200c400140d034150707100c1c51100380031440c02040a5406113886034a00400a81501c400301d0300e003505600481c1848611501c09420f50760100740130348000616a60750a88e085c1d070fa84202c01155440c110105081d02c0c4100c022110b10141d91003a61141e00d220090840d5049a003e09100142660011f200007110381c10a54080d21043d44110801e0719090207aa1054059103020349444446490007c4c0c0f100c01c80c40200440804100280b505000725850341d01c407030160305d8450003281d2240c000c1159140959850146043c0254100c032102640c2e04d44d2050060360301d9100d140c0850140c011a030000e0f0340700b4081c02d180d103003680394400514901031021700c40703000d000c480e66183c8501c0c010f103040c409110325003042440c0c4600d00c00c4d11503a84d02d1140c11700440e0f210b0800c81318540305001010421000031210107460b50088542131160b81a494007030010b070300b81013100000c0904440c48400400c0f54490024002040364809000f041d80b03a44c5610044420501019002d40820503 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 491962724 1250 491961474 491961499
    0x50901030201030917030702010c0f0c050c040c030603060e060a241a070f11040515030712033605061213020114070b0405010608060121060b090c07051209 68
    0x2900a8413003607100f4459040c074588400c049140c2030704107480c0c00005070765820005921541000c1d0302c00c13017490203007006540b81140e0340d1002d6a07208a16501d40c059622600b080028a000390801c2000d180d22903028080100b1404640d07039525400c070342d05403101c4d003019000d056a1131031464040b85030022a48a00f44142800200d05421aa524545c0703c201c0d010003000021a03007000045800301e10501540c410003d1032070420041c0c84015000c04140b500583c52520560303070000300381c01260901c0ca254421003286040c02d9034100c0503100c00e182d000e0390300300007400070320014844140c03151a08801c07840c4054903401401410300441c0300c0104601d1f0703410040350390703402c444440f89031080c414541218200410348a171403482e00601401c0354000910414882001403c2c05036a01910b200c01c0204030315072502c080b00b80c210301401000000c2c01041d001e0f5105000664020311030116004e0031500031030170071403288000d0350b120385001d8416000344040c000b5180350800c2110000c04000380342e1000c429 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 491963974 1250 491962724 491962727
    0x11d0a020a09030c141806010c030c23060a0608340f17010e01050c0f030a0f051501110604020a170c030d17070801050d0305031f0b0a18050901030201 66
    0x103008160207800d101d071101c00000000c0d0044000c0016000e441a1401009415401e0001510088502c420501000344c20402166440300710824001d8151804004065941c10441da4100d2204010040300000210f4040c1403200013840724001d40e0201c504026032035848c4006a2075609240802995145a02151440d0030b00d15401c03000c18412030001500c050386d60104030341e540603e988040300809078031a81c09110303442840303001502c541940091240380740038600042e03a84038040861100b0704010000c1500f4200c258003041d81d0450154003040399007848684601645015056503001503884454a44003001c042030381c2c0e001d141d001e0305600b48141040000030341424510081c103618411f0030300c2000c86a9040021a002d65502e03121169030190b03c0ea0740e000403402c020515402e000d910360041045848000460b01125054680641c0302c1c0c6071110640003062701030042c0c41b0189040d080218101c50810010841c6800d5034460101e1a043e021104665090520620343c0c071100c103000400265 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 491965224 1250 491963974 491963977
    0xc05091e0901030b013201140c0a080304150209102304030602030414030301080c0402180306092503030203090f0d02060c010f0501050414180f1014011d0a02 69
    0x44560012405803440540046181e5000c240d00580b10310b0b05038801000000b140080c0741020880c83c3c041000b210919420101110064040b014100510058014011482241500c9203050880705803100310304182484016a08251815184040800909a0201d020b07100b11011503002030081c0444c201c1445042c0da519a5103200070407150042d49910b84406280c000600145108101c0103844e41024103081d09041240c40000616a00400040c0165600061381c0c41c401503040710090f07a07400c00f4000300310741c45402146054151117001c042c070620079400300d140100480300000315100030f248400000e0301c0e51a00d02c07018002d40c0003003100c2055410305680152040d00c1c0a400d0b6039044810358003262a070743c001130b072540d203a9640740ea155240d014a4042c2c6401004121024020700c5c00d60a50184820740180c04202030742d2902c051150142800c1c000d42102d4980d0790155480b81c6080d02540c00038250000d086000402c40000100e500800e41203118066a41d4510440d00c80d518110342e50020f = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 491966474 1250 491965224 491965249
    0x1404020d1203060f08061b13030f11060a02030309060702011e110415050c010510030b0a090c0503030d0903030b06030702061650030c1b0714030609010c0509 69
    0x10180c40c0e04004c106141900c480340c0062868000804041c5042490411501e130400a007005e038100030040f11201e00181210340055a0700640002450131041c079003042660b10300c0100940203400032910741c140c00e0300800035510945400060300d00035a01c19000302d08a5034046004468a8601c003040d41040005900c03009e9100c5102100500e800c0c0c83d4144800c14403c0e1807126000074000081d030030130b0108280902600300d184240d01454050540d80d840b05c82c1c26005040c940034584d19080342c02400800a1020020f0401070240d0755199040341c004000f4045c1c1e04030980100e82422555602070a152046a1040e40c0c254080c1016840b03114800301901619010b29040054850380c0140e030248000302160307075540c01a16024054040740c000016448100039410000107405008010a9800000c8982c000c0000e41d00683d0342e04040c3d01030b000140ca03084200b00c80e10130303e500864840c00c021000180b011044003140c0c01c0d81c0d02c1d40740050030b9a071214031304400113105110180441c00c069810690 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 491967724 1250 491966474 491966477
    0x32b0e0d050f0d14092506020c0121110c010c0c11060c12280c1a0a0f0207051b091014060d1401050a08010e0316031e020601091404020d12 61
    0x100d22411303024000c1103101c150b80100b800c1c0c200341001680101508641d49000200032034001c8650b283c00c00185d1666030100c0b52505000b4003074410140c1c0b01c084258000340f0344c0c4152007041054031212105901750030601d0442c00360343c604690f03540680c0c0100c03030050340c0c0ca41c40420079000344609010b21405410804d000c00481c421110000714081502000d010034080320058420041d1100d1305010007a848121400140801c0b10240303000714650490080308400503050041d015100c00640800130480e2043d00d6840510100d030b030314100400031840c890040380040021a180c03503524104022000300f55501c81840c088000d041080c041254403034050000d00400480c02c0c05d409002041c191010601c41e00d03001081c01d030040c0400d1504407400d2001c0c202c0700000704071003418503030040d6891080302d0740a003101c90750b83c030205c040510a1002c22a0308010485110f0a007200382401b070343d2a030003805080071b210b05107000e051694004100c0c140c81507030010301c136000403181c80d1030301e5201200d00b4400d4030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 491968974 1250 491967724 491967731
    0x60812180f090a0203070f0306051008090705041503020f06040e130501020d05070c0c0b0906070b061504080d0801051c06020703020a1e11032409032b0e0d050f0d 71
    0x1070076500c028400e482210301800c050780da0300d0308090042000c1d0f82d103000d06050500c0c001051044c0d840d20720441a0081c41d9080130f00c1180c070741c140401d1070400235a00c010b41c86403c00107500c03400054441c1c4c150890f48259507480744641c4120400040380518000c401d0203030f4030200041c2c241d58a4042e01c5a001c0e0040d0b00040c41d008001000b1002e40c2e100b1940c55000c1030030340b04104200004405200300808030141100c0c1001c0c151400603c0c14030071210040d082880c4c80000c580d281d82c0350700c4420141007500718856a6640e94900e100c0d00c0f00d0000109a0101e0004000026142004d1004c040c5021003c0d0401c000d09207903903070302c0000b50082e1000f0340071072082c06003850002cbe41c05c801c500c0f068182a554039815004030b1800c28029840141c1490180e000500308852240c8a00140803540320294043c00c0650383d0800058030310b0040c80b00d07040205a005000d80c1c2c401e0343e051101d15080f0074800b030034041d4600c00411250b48041200c400b00009000b0004558541c141c4400b07400311014110020 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 491970224 1250 491968974 491968999
    0x3060e0124030920030c040b10030c1701030605041208010524120a05090c0613171903091703130e070e04020f04080f0610060c03270906081218 63
    0x725101c103c410b0318021130300700455151429140070000140201c0040380e0134410a28032030046072400603003e07400f0b0149a10390700510b0326a400f0310a903a074481881203e8010359a07490034144040d1000741d5080e18500c44040b1900c501c2d81c0310310f2016040c1c0e078000d028820b904808094401180e40e00b640741c4140d1400501c0008080f020005125000742540c44001c40d04d41401c00019041c030b03241c0c2046038803070802045401c8d20442d0081070354045414222807040c0144104141c2e908289001c40f290070b122a010340040101074210780c009080d80c07000c417041a130b40070040d0082940d0303102d8041d0701170b0307103541c824420005007108042266101c1a50316120020704d1a11000c01e05036004102c0c90f9101c140d020509025201c2c08012200b0300721ba45100800c202c0c02d005000e80200003003801074004118000b5a003506050081407900c1082e44912a0443d600304018110210a00365004580c0c4150901ca000541000002007102028032101121460501548589003d0056408075a5088010072065 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 491971474 1250 491970224 491970233
    0x61807080721020d09020406080d09030b100b0c0106060e0906030a06050a06091514010c0c090c0c02060c012f1206040e01020c06040b011d0105190317070303060e01240309 75
    0x281c1807200100d400400c82c0e1042c0c6c0304000980f413040d005451581d01001c4004907143d03200d103494007100e8000042520545402041005034130983c0c018042482c2c000451803030340a015800181181d180303035292440192900e0410050702d60544031b680c0d15911038290140810307001d03400f82e6003090b12214001441d503074410200301900c285002c8003a1491400504000b04488020003040c8a58240b0b0402c1c40c610440d80c9981e44100f10b0f00600d90120b035034107009a604d034020103100d0580b40e00140413949510410203101e010303243c40345200465560100c001c500c1d8508041000c0c182034801044181840480e514929003641c0003400d01e9406a118404103944a00a10003403103803400c0712000d03050503c2c2130b00f44088041e034117074041c402c071001d1003ca8141280c111001075043d01c9003212100c880040c00c0302c00c20301c0b00105810140110b111481c4044500402800514050b48251000e01815684603500403442c0824450762503021071038a0a00218060300c030303802941000328100000c4041081c0c98 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 491972724 1250 491971474 491971477
    0x160e03010b13090c1401170903040b04030809041410051212030403021e0c0901062006070e1903021005030603070b0c07090b100c171e0306180708072102 67
    0x40c2c030070055559600110134421950700c52005401202103400c54058960b00080c00140485d03003410045240e280810510002402140c1c000c02c1c4020300c03151601c0e100d040c00c0c00300d5846052000e10440c80d042c0e4000c1c0c2801c0c0600203a03c039510700781c0c40d0403041d450401803040c440944107100308240545808003901d8104400914000c50281d07006021000f01800440741c1032201041546041d405a818001140c3ea00c07102241510580d02d44008070180300d080400d030030700c80e0790303201a294003a40040018203948034001c011200c00494113000790441707562556005801a000c003039041004115002480c82c050b030002c6400036400307802ca55405950380da10310415000b10303c4002554003c070400304844101343c0548100d18200b240c4004100c22035000143c00003811003001042000f903984030204800c020000c1d101300e440c0d05041c40300d021003e50342c0a00f0b1076104036920751003243c10740318078800c00d6115004244150002c1d19010403d0310703000f00035136050140c00240c8070380c00460808440d19041070300 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 491973974 1250 491972724 491972749
    0x70b0406090512040b030a020a2f100b030c0409030509030709050402090a14070311040b0f030a1b02031e040522060803250507030506070c0b0106020105160e03010b 72
    0x14000504002901d00103083c92000d5510807803e0b41e0038081482100303e180116904400c05050040e91511101001d940d60790280408000c1501800c3c49601c8041c082844010401e441c1415100c4918101c107500b130840c0c10111045400d5400070615000605050f4850812a030107400c01e10300380039403040002d20b040c0305c54018604254a41d000c0c08218100000e0b00350b0060030301e074005c1c0845541d0b0101424441d0300201600b00700b64035500c2d003240c054100800c9a02030b02c501100b080d0f0b102e0b013401e66045d0f99481505c10300042031821864614500000423013069140d82940614a070400340c011950000f03143d104002c0c1c03076030020040001e6950340c8212440c00820000d6081c0507154444d03551004a0302164040e024541003006162220b6030503250f1031028407040307541c82d0f44180040c28007602c4c007040c980008010b03118000c00d0007501500011804030b0b041c480d00d40c51000d40c1e02c401c0100d00b0b8403000d4031004020255207040400040c06140303940c54a02d40600005440f541200c0010780c00c00700007 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 491975224 1250 491973974 491973983
    0x3030d0603050d0311090d0f0c0510030204260303010e100b0a030507120c0818070323070b04080a170d05012d08062e030615060309030806060d02070b04 67
    0x7590f41c03020a501401101c50f00c400708409107007009000720101d2000c10311240300070000a00c880c140020000980d14000103044090500410041c0c40c02000e00251701c00d0240000310b40c02d0b0440902454440e0f1004098640306801640c01c6034a03000310248000c00250500d03c80c401211004100c011941000e001c08202075a40802c0e203003406040601840e0b0481402070060b42031000c03030008190414501608005884003046403400303d07090160511010303400003404102280b0018240c800c00800500a840f054800d481c00c3d590b6491414036644190b11860500e5084201c500010030b803200089010405d0290005103031802c007441000c2220390076000000e0f08035075103001510080c00500000110541c0000c080541420590342a80d141c200608480f521400f807041a805152404910a1f403100210700c2482060349914140b4003074080c1640d0100c45c103146400005001b882030098080f080d8064403500e50f05d0f00d80e50b0600965502911034946402d40810000c400203d050f10f6140c0714034040d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 491976474 1250 491975224 491975233
    0x2a0a080f071218150e03061e0105090708190e0a0b04030e0a030206070b180609070923040609020411070303020408120406080c0a02070b1b01060b03011202010e03030d060305 76
    0x81c0c60446070040c03281e02c41d10200b0400035162001d509403143c4403002d44955440c020004803001e401103c40b580c0048056416000e004203001c0345010507540000b02c03220526218080daa02c442c20301030440d0b400c4491400080001c80030424002c01044501b030700240c851808030b8284105003150b4904840b10b20129031000039070b420070051650000700000d00e10700031903582000710301e1a00025054003c50002030100100c68012951400c0311500040f1030402c08130903a4158600b00110a8030303590140300b400b502d0740c2014021507205000301c4000c6c0010042d524014100e44464851200814150800300d03042035503140c18410700f06144c1e0103041d00d5442580e000d640c403818012241d0608070315070045100d6610500040c003400d9001110b20f035000b10040310240d02e0b00b0281e142240340c071019900004806d6000243c00040f00405038000d42100c8684c4000d01c40035507901c080c03400b24071003480350740c8510045031004001580702d400e0650304080020f00303d909080003c1a4201110419030040301d84e60311 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 491977724 1250 491976474 491976487
    0x3012c04030f020c030d0e13060905012601091208070306090614150408030919090f0207030e030a020907050705010e010f02071403072003010e0105040501060f05062a0a080f 76
    0x60411540d54131a8044c0d01078004a4400240a0030b02a100300307916208550108440d00d801070a64071080042c0040320f8140302ca541e42d124044003607034200e0000c04616006031000200d00105029001d2040d03408645180720203220581101d510101038001410151100400121503c05004050103040e00001085400340241c0c10420354039401b07100424402400e0100308909400070003902e40840c0280c8440346d12a4032594082180d05042c1c03c00c14101380f41c01c8840b060380320fa643c013818185100ea150703140107070002c4003095a01c08401d032009610045020004410501c19400740c80c225114400120303060007000c02090940d84458520021150701046a5040c0701405a4000304880701b0b2000c0c501d4034100392180005101708190174605c421142050418a4034258010f003030b80308542e03000704840d091a00d04507001e40320364402d8009085d4074001c08075032880e10100301c559030070149224510b810380000001200c0d00140007003800c503005480035a40400d800c0e100400c101e0400f2001d180e039914 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 491978974 1250 491977724 491977727
    0xc0109030207210c120804030506010b1b06060307090e0c180708070504060c030e011116150908030d0506040608031b0d03020a170405031c1d1203012c04030f 69
    0x440c3e001d0501140640140c0b02c0224485502010503600031403043c48032151913003400d025030b1107141d000030302c648981e80001481001a02c041d003014041100503200c90035103144003e40d1759100380c80385641600000400c2040c007080303a02864103040d100c0242c60541005800184c0d06405813902070600010600c00c001329a5405030045034814050304006083c5400e159000b411184081c0d001070130311004141244003a0b02548901c90b038032498408444012408040101c580c10252040c501d000481d61003880045014940e07210688203204000c0d8101603280036090042c2c81302920f900c0e0080e41c4c0304c1c00070074031070301c20b04c000c0070350b004552820040301500003513423031501559074400c03c1014070601c014820540d10800e401e8400c51301240859861721942080360541c440c034001e04451820084500c0640c0702c0b43e070425000a07070320001001c1d076003403404402611400ca00c1140c0c4202e40080006101482c071091552030030200c60000382406660210305840341c0c48007501c0c00e070049548220072185c01e6 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 491980224 1250 491978974 491978999
    0x21f0509130905070e090a1709040608010203060d03080a02190206040b0901050601122004060e01030b0904030512070207180203040605060a15030b030f161a04050a06030b060c0109030207 82
    0x120907403030040088041c41d480d11034071040640560b0002c1d0322404c0100300718103420440f0080d0356400c4811003100c0164402e59a60591024803080d02445c03c0220003c0d101006100b42c92040101411040e08400d60344da044500c01002010380a0b002c0d42880380044840c0a0a240c0c0100c0d41c1c00e130002c0c40141414200394801c610000e080a0041c0e060004004051341d100300c441800242ca481d001c03400c2c00351040450320540b840140f9922903040810005006944840c403221301040a072410451440070000340f14648504850180201d101004070b00c600341e2005819076404402031040d111079545448211100036030811140c451150040140028421288909a088502203901d0081680303002c0ba8000c02c41001103442040c56510865026942c806000081c5100380c298280c85007143c031038140c3c0c0c00000072070140640c02c00301551500e801d0316400044a0036104020701c4c100d810303440d152080b400380042c000e605d40c000ca800c0c4001041c40c002400303002d60340c5100e50040e1408604142c44070380f01 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 491981474 1250 491980224 491980249
    0x3150e0426070218061c0308100b04050303040b0702060403300e10030507090f080604050106060906050702060d02070b04060506091b091c140304090501050f0f0904021f0509 76
    0x20140400040c0010b0342d59880380d0880d2103440d85070508685e90703c1c3c00155050700c94002140f044101c40124000c255000d05028407400c1030039241240c403a00c84084401c030740528010245c25600400c000e1025420100c0513040640c0300501107403500c5d40b41d64404d0b0000c911500c9004145208650154018880c070800c81110000e0780381901302c1543c0781d0002021200c90b0790600381419501d10104114a1045031401c001d8140303502c0310000341b41d542c0d202c03a1b540c072421201a5141e5180c180d0102d00300c1c2c813841101b0111803203982d8003400d0003890740030400c0c2544204089031907070350308000700300c0050100c0844a101e10300030b00d400201d504e810407d104c0981c500401d41400405200320b01d036411074104060342e00300c0c4000d480c5240d4190054141c6030b180261868040c02e48003940094400007a8000010410365013110b4052005981e203005003c900403400c02c1059102801102a0072142400ca103d16440344c0000e00000324210651011403265103000c194100190002805800324248013410004 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 491982724 1250 491981474 491981543
    0x1090f0507120506040b102a12210509030d0e160e090703061b030c050a1707120204061106010f0f12050a060c0305090606040c0f03150e04 61
    0x181c0c03070301c480c00900c54000d41c419a112540d84401040c10307503e0fa40c0c442c220741000580651403410b03031110082e0031020404a02002c2d540300c230051021302c0340074207000705441d0703405850f04412100f140e40944511501301584a0007520304000380070280da40307000d8103003e8001c0c9005540d842e80c0c080ba0030f9042c0c0d5403042565442d5442140c03204080444407100030700b150800c50000b00681c035150b512500748030859002800e1141401d143c42203451414907200201851a2810841d2980b400402d41d02400340045c8800460340d00c03060707000042c4125000b650700003031514018000ca0b1040c61480f0490f04150054000108104508909050100402400b4009444032180c040c6e14044000482040368014210b003406510303540302c1004020020f46e031210707504c580281b0083c09001001401082c0407942c0344183e20451001c168503040c60f2040a07240c41c81c030380c1c0340100440c0341101580904a618807605a4041c0c200c0006000c10116120300d00643c82000120340c1c1403140d20040040d8142d6000140 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 491983974 1250 491982724 491982731
    0x150408011d061f050301022b140c0304060b13020408010609020f0403111504030f020f1207140111160801050c190c150203040b041709090c03040203012301090f 70
    0x503680005400f948040c0b0401c00c803140040c0c0c04030800d0300c0d4200d54012605036001140d0741c44e021100d41000c0300d0403420406a080740d407100c0c1c0f2500080d41c40c1c100300c0088441d01030010501c0c240d103510045901a0007200c0c0401c002001401181c071851101401840441e03001c1020b100c498005e00501d0020042c02e0b2095040c07942d00350440c65030b8852880010f000390001100140303280c0341d4000d1000b06010142030f0135140e5a0704c0c20300340405015881e0491141040100654980c9005045d00082e4108800142a071504101e0b0a0080140f582a803d0500c07010302c0a032159800f04010921000141c0860703403851900d016001800c0d504041d108501d54003080c0494066a41c6188512003c21601d180c907109420050601d42c104848460403500b00d2800081044144400f03c4d903000d0196206018421038208600d4681d0058061046280d07807094910005c1100245100701940c0c0103030000f40001101c103c07004401701c0303a403118906d031520480c80308010001d85060b84503c40101c424035000340b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 491985224 1250 491983974 491984021
    0x40b070c0203030f0d060506040807153605041d0f0604020d1101050910020c030d03020c0d050c0c040203090d020f030307120c02010b030601090b090a060501210b15040801 75
    0x90f1070703006640c0b400e0b26050703001c52400075110b0030342c11050040c0700c0904020360303803030b154454180ca0f00b0182c020040030340012103444040a10641d29203617449121508142000300900e1091810303500c43c3c3c00078034016207049001c02d4954461280709540138800310111010f1180303501c1e250802c05100c400000c0d41e0020810400542c8840030f03510410ba030b1100104514800010058a40b40a49842c0301c0e017200042504620290f00050000c01c00d0b02c084007298030703d0850380d00c12410b1713114002e0300d9070f030310f1304550080c58007980500003601004951070240c0f40030300c00c41808241240c00c211800c81482c0d01c4106420392039a014824541c400c0c4960004e10b15514100601034058500420346012680d07661080b4007016200703620408c0305e29402010b884103541c0d00d2101c07002030041343c1078261040d4045008690050710174800c5c94111407041e110403012190b1200ca07070300c82480b44106c901a542c0c8840d0642256500d44414480480c03800c01600e4172182840380a40c01c5465003501c840b6200e043d841c0b41c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 491986474 1250 491985224 491985229
    0x8060c030708040308091507121a22180803060901080f15070e041e0b0d0c0e06060d05010305030304140a0c050f0102070b03090106060f021917160b040b070c02 70
    0x2550f502c40d07018144031420ba180d4040e43c0d450144000440c00600b004c880500c01115405018049104501c840a000d019041c410382c102c0441441542640710001c500b00c2c0d1224210703c990a2625002c0a100244e8010280c91104120121500c1101c2012001082201500d0035514460160109a00426014680081069840d000b49084180150040c0d00084080e0702c90403c0b00e070700b02e01c042c1081c010000c0c00c0c100101d10160302150356106605110300445d0b81e082004407140e145401560241c000e505d405c040b808810300c0a407000340c01280800080016072114042c1074025480754000390741e40e19141c14802554201031420ba40c06070001c0c50703400086800300140750140c41040311002c444501d2480141c0ca130145aa12848840c00044208210300b40c040d400078007143d46e039480f12031800c61070480c12030305d40320515011841c2d003a4254070079012411a20002012018003c00f00780750414a1800804070175928a00b02c0c0d107080d111040004008950312115005000c90400ba030104407e0b500 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 491987724 1250 491986474 491986487
    0x80309090106091a09060d020c010501060f0c050304030b0612032b0204080309010e0303090a12050c0108010b04120501020909010905180d0905011d1011071a0a11010e1608060c0307 79
    0x100a40d0300c1d580807915000c81c0da81c104c07c0b0f81c544007002c03a0856486400041c00c038040d01c801d204040200710700c241060b007010b00130005002d44941c0701e0080c6181c2800e66071600d407500c03005400350b03402590802011319214002c02c001c00700d4001070144414944808941c036034140281411800c48103006110400ca2000000240c0b15040c0090074110707030003202400031034554001e0741c6a583d072103b000301d400a14841059804691f50340030b6420394081491000054070a02028400e03800c4541040000b0419204040c80100980b0703c140005840e2100740c0c0d0001b81e0030002030b0080d88081c0e07079035802e000803000d01d0510400e00d079040101a20021803071050290101c503940c459103061007511910758060381e46020380416166002880c01c0314013482d142c00242400b00b101c124003021700ca000fa0116000b108040303000701d1418061085850490401d108441c0f0440100001c50599220543c4010014082c081404080140008080083c1c50903d1451a101d0041e0060350030203010001d1200d02e0f540180f = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 491988974 1250 491987724 491987759
    0x60f010f0503090a0231090308040209041502030114012d050d0906020f070209070912021302071202010b0a270207081303030503151c06050901060803030108030909010609 75
    0x62040d120380d14440b40f070b42000300c0150025408010702c031200c10703504066034120048103907500802011082d4810344204450300307030358091301050300c45000034014501224500ea0003032049c910408003492159041040c0c2c0c00a801805000403001403490b00c40d41c0c00542d0302610110100b0001c3d440780f04c04003580034540f410804004104000544200b400000e41010b81c010b40d00180c115507031081c640c950800754003d01c904911903d540c01c0460b8000c0d12518804041c0c1d200440b80316610f2140d070b8200041554441701d4202c4003902480010007061641105480d400e0340c2d83c00116142c001d41e41040401c5285410030624000d920f0106103c80080d070305c2511010012030001a034400c141d003004240340c0150212014003003034002c3c01100301640710b03000e1030041088410201d13000c8126400c01c16078030700c03128103211504a52030740b0901181070798000075003061b82c400c000200e564443d006541550301c260003c003010f071310000e0090018141000750301d00604040c640350b22800d0900d400b03001c460502c803 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 491990224 1250 491988974 491988977
    0xa03120b01090b0d0e060106260a0b0306040c06180303090915030507032402031510050d1404140309010f030b0a150c0b090c031216051203040b060f010f 67
    0x403401904264001c82000000c2d081420100d0b442c1d08412031094040c220001c60308205005a000019103940950403840c180c14502c600002003503400003040c03241c00c100802c440c01a680b14288446203071828000d190041e0300845480c20b4803810b14601a04030040c1a41c81c4004600f4610300300040f13540003407640c00340d81d1541004100801620140300c0d0b034100c203400142881c080c245002041103100301c40045948007442150018088001c5010704a0104460700780884102441c14900c901c4c0500041010032035a00700b40342401880031161085802c0c41c0000080404a002880140725092020b43c541c2144400114940400b12000a2003003040e60941810300d500d4010034551ba60f140891a0042c0030824940d0070780f09010700b00100305000700c3c1000d4813008844800308a103100c003c1004144803a01900402c6a03041040b240c022592000c000c0808501c00303c0d40c4c1c100019000c2c001c0101c1070010f07082d60f130344a080c1800e11610001c0c0180c0700c03603c40c1400c0e240d16039031030340c06c68503900684805 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 491991474 1250 491990224 491990231
    0x120417070b1509270c0316240e06090a0e07090e0901090309060c080c03030a0f0b0f220b090112210207030602030403021c0908070b0909010510020f01021206010e01020a0312 76
    0x2600c034258038000c40c0717041c00e503818003824807144010021151242c0450b41083da2440d0b18454540003103c4241440c00c0180000f45400d1b8003a8580c10480001c0400300300290010428503521015450007010a8a10100003010158204003030610a0741e815000f44c0f07200020480490b55a0380030b00750014902c603030070034446403014500034404074405a40c000c000100913641d8a281000303403600201240598131130140e150014032151804e10b4002080441c101420b01100701100c010968001440c0c14011000b403515010074070744584407408124020885400b20307084036032442c070703107030807a50380224414031180d82070950655030650005140c4102c94002c80300580d41d440740c5c00d0032420001218152040300e1114000b415820360701c054407204132050307202900d00c10743d2210321194862040c03c02443d84009068010b00c290314080a116610700740c5401200c807408544900a400c0e40c10003001908100e016074100303c090b5030081c6a81c50704520074406043d50f088a81d0340507024154140308100e1041c1c1e03 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 491992724 1250 491991474 491991541
    0x151505012c0616030f110d0e0f0f060403081201050d261204030206010e0a141609080a0305090301050a062111120a060e0111120417070b1509 62
    0x403550100c3e001c418604a002503070b00e040d800e028100181c403000080008003005000243c0c2200802c4a0b01c120030036548403541e480c3c40c441001402c0e15a0505a1707800010071480f0151561440014001940304124140c0c0743c0e14114850301e001c0c40142d1005004070302c034101c6a80084c0030000b441c0d400c003610300e040b0300490841407101a01402007010424889015005002c01e050f00003900e01d0480f116405011700701ea54140841e8140e070000428544503456040219260716007400750b003103e1070210f1412900d9140d907807064500c0c1046a0406402140c4c0006010b03210b0f00b428080e1a81c0b0109003807050280c20f02d0900c84901001c5016844070341c41c1c444100180c10003404000b02e10045d0001844c0140c880298450b00c1c2d202e0300c4043d0704845072454040c4e00b0b0350302e01041c000c8008104204801c1e6040160310001c0340e950f8a0b006204844a965442103000e4007600c0c08042c1c4155401228540c400c1d18180c0c85a121142840e507a65114502d041c1c10010304161003003404040e050b41e07070615640382d40d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 491993974 1250 491992724 491992729
    0x50a060504020304110907090f03030e13140405070e0411211e0c03060c070b0403031803030b010f02060c0910050c060421050a050a05030c07151505012c 67
    0x400340c128960142c000801d10003030102c03100c0020381d4a407044600d103e26850703080060301c9200341031261a100712807c00082001c68001d1010718032101024003031940e1401a920004115009006800c0c0807401001c20301091250170000700c030141195040c04000b41c102504c0b807800680c0403406c05881b03a0031718031506483c40000044820240741d03030000c030303442c000b8040c100342c0d640b441e04021310038540310b41e000006083c91300240301800b454218400314540501915515845a0010700980505407516007220828582d034030100e25550096a001402102c468001400049840d080708210b60100e010b0162500711901222a148000c560301219401103a40035280f601609501c00c11740d004400401090085081d8108148000184400d9140c0c00300081503600d8080c039000600080d405100c010f0085000f04010740c0c0259030440d015083c0b9440d42d5440380c100c200b50000f52308039501c1c0d846045e5800b0442e94404003801c024282144620502c150039910000c4100680103242c5c4040c1e04d028846c2c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 491995224 1250 491993974 491993981
    0x80a110d0f022805010c0f030b0d0b0703020307180305030d050702031c18080409020408070819030c0201030902131b1b0803070318080403020f0906060304170f0c010609180203060703050a 82
    0x3d0740d01c1402401414080c0740003500c8005480303860310119041c413038168100d01d030940f0745000e00c1c1e50120744a01c0702c0c3c0303440ca0100c00030b400040c040024405100381c02a28600c40342010001184184000c5948070030b90601001519030150801041d58402e000a00014400102c00c283c0c82c081c0200003e01c10004142d000101802c01d04050050b0320000f4000c078522080350000d0003950001001c490320700b681e030540c26a903995491660b440c500c1a0300e8003000000d114112040c400f0b40145404104003c042e000a0149505031048030724442d038035240c0e418400401c49109000707162030305142c060144014007412002030411002007481200200281005c1d000307500c51100c4005d000243d0450031884d150129040c0c0c030901042e44070362142d1801c0b80440c50054080c2e882005d001d4440d5040d034423150740d902d12824140302c0380442424140500c952084c90400600399010041d0f00205413030340350074849800c46400410500300051302c5000c040c090f0f14001016a0070212610740081c0340c1e07846540c490004e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 491996474 1250 491995224 491995303
    0x3020c0406120b0a290a05030f03030f0c39060108030a0c0813062109020d0b0414060907050a08071208031b040e090d031415010c080a110d0f02 63
    0x16008040d175007246009110202480740e942c2642c541c0702250700c540400d56038810040e94602160b1041000030a2080d03d080840c2d041f00240c0c011a0510100c07128003419800c14510b4240381d2a07106602d0344058100c0d0900b1a1103443c0c94020349a10b504000c2030315142d01c6003450600038480903241900401140c681110000007448460142654554000500c000d941c0c4048034100000103049048440751351058494555000703181d603030b098031a0f9882c10920b000040082d5440824040580c10008041c01090310030b0390020301400e901c50600f03080000d041400c1e004054980c1c050780040c007e0b624501505040715070410714982e129a42c00005030800e00010480c00300f010000320700083c20340b40d020542c600500c0c111060783d02450100108a0843c1c10282d2403038065403620001c61b0b080c0134400350342402e03200185044c2c2c0c41d280e599114241c81e43d11102c8000b000841d40410840c0e0701c5003d00c806000d49501c0d2030060540400030340002e5507000070201408100e1074540c400c05440d4071804c5d10551 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 491997724 1250 491996474 491996501
    0x5090a180c060e0901080f073602190507021c020a08030403030c0308150f010302090102011112060301240e0c040504090b09070504200304021c0605010303020c0406120b0a 75
    0x4580b40c100c000c2240146021590246070000300106600c6004685001d4515010b0010440c20345090000c5415040e0190031b8200c0b1045940c201260001020f0112102e0419401c050303540c49111001e003600d01148100d4108000701403240d440142d4407154152005158905181521601400003420100450f4030600051100003400820590800880c2110f18040c0d20703031400c2c0e580c0d1303180c1c101c8818404031036007075101c801000c00c0b241c0c543c082d501601c503d90040c130001502d442c00c00030600c0903902140f8140c82118141c8100411445e003402400038100580a68130156542e1040c100300507480303801414202510040001e0010000d0f40940d001001c00800a010800c110b081c046860b441c1918419124001c0602c0859281442d01580c1443c41c5d489502e0710121980d2002020366403c09041282d0281c0b1090b41e0100a4015400c910300c00f5000d02d00c001925495881c000e8a019420008140501c2c2400c800f0003018143c400d0048005800108030800382c0c3e1403c5c1c40100811140349034a1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 491998974 1250 491997724 491997743
    0x40914031209010630110301090804090c03020a0804060b011b060c140a091404060b120708010e0609010311040f2c06010f23030a290105090a18 63
    0x19071035a6101031440c05801c903803008200c41078640c040030a500c800001180442a40c15a0381d00c040214103031500c04443c098a40c2e1146400441e002a00717440945400f5a007082c1c01260600010750382d80704080700103865041c1146802c09030100a01106002400a07101070754030340308414903900030748100d8000054410001e1840c045450018000c00251550800203840380c25078420303a401e1502290500c0400d41c4820031264902130024038102d141c180003e4000e5103404001601c8001c002c06402500713010304070b140d882d14001e5402080814141d20091071442c80006100c010f8580201e00c5054a0300102c0f003a29900c81c00021a0140500c071a108900342e1801c024a8401400c801210703003054070102c892641902c2800ca140e030390300e00c00c1c0a40712845921b00820400240c48102e05084940180c4044115202050009007001f90510054843c041201c03d44210560b101841c000c0c22401d100b0380610079414540411078402c0000c00322041c240c1d9412450860001880509401941c09904d10 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 492000224 1250 491998974 491998987
    0x110408010e0f07212f0409080318070518010e0a0207080a030203070203071502040807050d1a07120f0b040b01030212010533040503010c1b0b0a09080a0f1103070b040204091403 77
    0xb95002d50606114961884403164175003103914084c002c0b5030280e50401011400d580300e14002c0c0b50a45105101401c203071046c0c480019907900c682540038001c460100d401c078015071401101c000706c40002403800b840e0a1040000b100007510780025904212007030314006880790b4408d04107a10f188905c4502030304003a0036014201120b00c0c69001001944c540f902a2482155a40e00740070200126000c0100036000103810b2104a4a00307046050744401c051030003911040a5049020807500f00002c46c2a00c04d4a5900100280c2041e0127240e0b002d180c20f18085143c00045a80314086000c10b01401b4801c000030307000d40c00100026080460803005001c1001d50100540911121703e602c14070400d406542440c42c20800c060080010595000c4c0c001d52158440e0155034a0141c0ca20000f17028400650303461040d800421358140160002418035250200b4482220801610100d030300d540c10315195104004041c0003850040d4190307007055043c1e0340800e03001308a182c500d2144511003001c210784d05c40410392 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 492001474 1250 492000224 492000263
    0xb0c0d0209041a01030e0d08040807020f0612041707050607030f1509060312140f0901180602010b0a080d0f0e040b09130b01050303040b0f0c0709110408010e0f0721 72
    0x103464030010f0176207082007034010400e41035845000c0130b82c0050100781d10200040c08507110380001d00d00544028010b42400010130001007458006100036050001c0e0001000100058000c00c020b213880c05003c1c66003050301c0390f680c2d2a40c4039001007803038080584801d02600c4038692a040007030030a401d00014207001384c540c0e0105004202c4da20041ea45895014036136400d4038025584030008604122149180c4039401440d408503901c240005410020200b020101c003c584c04402006410254000702d02c0d294858100301140103140c01c0201c564101410b401c2c40325400140440c00d500c01402c107400d0441485000034010002240b0039178200070484100300740c41e81c203d0030042010b44580102c84d51643c032802416920302440c054002d2903081042010000c9080802420400307007030008a03400f103a100e080090075200f000805090302100805d0031301c4810400c1c0105000b4020301c41c01009030241c000130159030f50000d4030654024100d00c0c100f0303202180302030100207e460780080e070003494803268150 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 492002724 1250 492001474 492001511
    0x120916031709121c1205060a0302100e040f1b03050c0a110a14030909010605120417070f06021b0a0b071103040f1509060f08010e090304080105150316030b0c0d020904 73
    0x4103040011742072200c0400e500f00341d10600f8040c1c01e019286004040c150780c01e0040692070124004140a20745a001049035610f000d4400311030003419012540820300d184690a00301d04800322001d050810081000c80c424501c11340b0b200402614084071125925040c0301d06015014201901c0c1d201d07075410f036566003440000180040300069644111980e650141182e140c041c40110740340b241e058102190100d90b040c0103a01038810035400703151030810982d9a080d0201a8090110341301070300480c0084442e00f9241003c164150000064a5000e6040d40d8080007100c008003002d09028642415406002c403c0080c2c174040e050101e42da45030140c640c0c0c031845110055803449400129411000708000b0700c19040100500e42a44034484182d003404141480d00384020a01700d1703580302c244030000342660709000c0c0d60b025805460440e240c49110005241c103040a0311821602704011040820000d117040e803150b94040c8200340c0b0281c136009100c54130270103441000c05240c0d0003410881520041a40c810 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 492003974 1250 492002724 492002773
    0xf06030a230f070c0503030708060f19050108060a18110906070b0105030c0a23130906020318120a1d12060a0507030b0a0302011808010212091603170912 67
    0x100000b0490392054401c40da00e0b036074448020082e800a201003038401d40a210b446400220051004240ca480300000c1050110800e00403010201c0c9082c0421040d42c000c07214a4100e441030f580e042c2400e0a2403141903244c20414280400c944e9640343d00166410307007405403014034400400702d030741d80c0b2028100750740c91b0351082c0240ca00c40e008010040d1900e140c140001c104030b503424040c1200c1380a080c00103000d494a1b1000c01600214110039451950360544213003180d4500c514401a141e082c40790600c2c2c02c02c041c2c607201036160760043c21a10021b0041a00350365201c0800d00e00507490f43c100e40002c440c80d042441109400c8060340e044801300c9440441c0c4a1b100c2c1440b0b501c10005507940d034008605075000408100d40041242c80e06201552040d9100e5640c8403000110124232941c0301c0310107003240d00407511000c2040354501445a802d4040c0034002809000c030220b100b0440c215201e40f02400700140890b012194002505107a0340c490710482c0107440603c109032000d5810b0352906101218007003 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 492005224 1250 492003974 492003991
    0xc2e0203040b0106021b1e01090504110a12020f0f03041a0a1d0c01081302010504080304060801061101090503120402120a1101020d1704060914010e0c01030e0c0f06030a23 75
    0x4244030541406d03100e80701c1d204490041c42800201c040b40d80b121800d100c0700c0346450421482032004070b41504c0b18020301c1e545032180040c06a0301d6285250040c17948084941c2c0d032948a0040114030550000003080c1c072070b4626108041a41c80d1900d14050b40340404d000c038188400183c0e0b60410110080641c41004500c068603040d8404040d00a07030f00d034561f041c0c00c42260100d13079a1008229000c00128a4480a504c18100b26203856100c0e20300c10b2464015274080800540707084018411598040e0000144500c220b009005410150356055128005c1c4440944003403d200b00007410355403240b4030220078070400c070151a01000c1c02d0408a4440445450480c0988507005401c0c00c41c500c50111020001e0622120140d50b80b150764400010b0695080c06031129905c0102c2d07210303403860a210f010b0200d4103044c0100005105003001405540c955003409400f070300900072003000c54640381070386501508204d034000e50baa990520315a00500e1341650000495824200d24481d06000400050052265 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 492006474 1250 492005224 492005233
    0x90e010303050c100905031e12040809040e030c1e0d05030c0d02040b0706050a110426071a041a0301060507030c0206160f02090f090d1101201e0c2e0203040b010602 72
    0x4401188501e07109d11303690201e1030694000040c000c10704080140c64040002030001c85c210ba00219418910317001811a000180c11401600302c20f420101c40031003080d820a00900315000380380e403001e072141c0402042c10907185800203c40c05030b00c80c0b50381204c01420b00d000f2034540310361080c10319030f0042204560f404512440d10041c0c1040940c0801603134115030401003423148009010103000305040a19800c5000d500c1006404520040b07440c0c410102c948280700121784035841c2203103080010716480152010914100010301010740d00c54102e6903001d8140c1022a04102d880c4086402c511038045001c44040000d02c3c90020040300004801105008540840301500c3c1d008051120540c02d403882c110a600400c10891120b001d4100720b1001c10b28500001241c0394003400c0c809201d0465010070303100710f10004041c07840b081d46010b40700b00750a080340c200b82000098084c0c2c594503e8143c2e03250001c00103503007164880f030389250805d1491003005c54043d5164103203845e01500c181c00a02444000d4000c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 492007724 1250 492006474 492006517
    0x40314030a0c180b07060207080706090308041b0e010608060d0606060504031709010c140106030b070c02040f1a060f0c030a0c0302061f030609051504110f01090e010303050c10090503 80
    0x2210720f240070341e00740500003882c00529a9510009610081c0c003150700e03160901c00c11005c02c00c40d04c100145036000792210b820340c7c0b41c540740220004c0e248905400c0c0c1074a090130309000503610501c4c9203044d03800f1428204042d4440800051070440200b500030011400c200740450415031220190080f20321594400030000f100488050807401a0303540c49000402c020349003004154440c003401103030030201000103801916501c0710040ca000445440340400d80360a81c070002c40c10a40b151002c4141c80c50006c100b6880011032842c4105049442d96100f1000450f6003030300f0441c04400c542d02c407500300381180e40e642c1a03014041d043d0587c17500141e02501840e07001424580c58403544030756940900c261601200d05568401c03004160f80f6405881c107200b2070500e00d6542c090701000500941c02042c0e000c0380d2804d008104054810102100342c1004042002084501d209103041419694542070964031403003150380d60780c6012041d003c44560b0600f80383e401c20a0001c080001d100190214641c6450000e = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 492008974 1250 492007724 492007757
    0x20906360a0e07030b0d050607020a0c08150406050705130f05010f02031204061104031515081b04091a04030804150902010c02090703150801020904051f0e040314030a0c 74
    0x901c1d88620014181e801002860542c13181e800664507a10003001500042d409407210380c507094044034550301583c02007800f44240800e00c451030000b058124006c1090196403401803040780c0d0058401451551603502203582e0354020401c0d40c0a4064413440420714603030f654581008114030344a064003103202e2088070844103202004880e401c05140b1401c1107240c07503540e51030b0010a143c444d1a001d00200344404000118103444681c880c80b45074401150100d0304101d2245072020950190085a018890344001e1441c40e05200c1200f003001c5800052440d4241003141c2d4200040581010030305d240400c10040580148025014601640c054110070031b11078049012541d08941c007a01082c68082c0d01e400628100040e0b980c003000601d404543c64a010a9480b40e00031240c000c0e80381d40c1d4010074a0503907414184102c0341e00210740001c40d41130440407100030600c0e0015000701007a413090075000409150243e042e200e1501c007248925070745c900c5c1c00240c2174020682d4a480030000350304000b482c42c555 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 492010224 1250 492008974 492008989
    0x200a0c060c090f150201091a16030c09030818091303030b0a0f092d1d06010321030b1806040e0a020114130302030a050303040b0a05091002090636 64
    0xc1d0b803c01d00d0894032505040c603071580c549800f2014821913403030703c0f00240000d200c00f25401811110741c0d81c0707040f01d080a030302032202030b10424a294205860001ca0b0342c02c0c180e110010304101c0f900605a6680c49032001e0401542e03443ca01402904a0703041c009024030441c0c1c80d4500400707103010f50b90070442003804004010303400c03000b442420100d81d0017000170300110806a0000c0d0610b9841c02102014008211002c0c420a9982ca844442070b1384d2483c010300070b040710829038000144620003802d040e40c11a41c82000002d03018900b00481c0055061555099001394801c0c00400401040c0300c01c041c1d01c002c1c56070000c100c1114114080d40c00c1c246441201040002c0d44e503000c6505854078940d00780c01269150f51608080300c0c079102d101040300c1c0040503840c1404409241801200556a2450503050049108101a02021034580b070a4200500300703402203110740780782c46003000143e40c0344c00c10000200d4600500203800c6100318203003821003100035028030032244602250b40d5890034800303070800c00050 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 492011474 1250 492010224 492010229
    0x609170c0603070e1509130204050a140d0501060909231506011b0c060f140a08130602030a0c0306080f03030f13050618161206200a0c060c09 62
    0x2180d20204010140e46410000b0350780c001200c1c90300c0003451010030001014034420391a07024003040700180021060600004e540d014582d0500306500d02032800380840c01440451060500040309126099102c0d9100514540c4540d0090001d1101c181c548007444018165000d04440c00413000f0013488901074840050a0351340c100310050221000704404074006520010400740c100071010f90640207028988031f070529681d01405000b2001418284044c2103c0300360345802080c4182c600c2d0350203a80140038102d030302020880c41c2686143c1c40f46501440424603210b07006007031500100400a4010b21940008250100c90f1380901ca125980c21100c8c2e190010444891002e81040000542c03901c0e070221080d402c00a00012441030001640368242803c00c03e59450108800c5900b0b0150418020040304000c0d003410000440c940d4601421034050030958000109116158002c094600d02402000348024980544d40e0f82d956012150081c4990000300c0215449407824244180061090481c0000e = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 492012724 1250 492011474 492011519
    0x209010f031406040b030304051002010e0610030203190c09020d09050601050f0d061805030c031902160312030902120a020315151210060e07021504030e0f0102070905070206010609 79
    0x483c1d1924410f200203008081ca0554061108202c0003c9540300c421600e0140700144c1e000081000d5962841400c04070040d0030003035644500e40c07082c0050f0380c01140e81105001141902c0148081d00d1800e103126403540c0c2c1c4004449071000c0f91044c10392440390007801f0a41c0c419420f4500a82c0ca8400f005401403501d00701581048903002e450340098141e0b44001615001e142a280d240f0105656281c5140d000c98840840b5401c042640d0140d840b8407024058801040c2c0050034144112034200007003101c183c48080c1646070310102d803520707490003075000c1c0c4442c0350068880c400c0c00c0e080305041c607594040403030100e0003441186001c82d003084040b0307071490040c1140010385422422030004c20641c80710701c0343c0d01c4c01d040c0a44400c90301040c0f41c51081000801041c1c00c406040e00c1c7c0103801074200002d00d5101c00a00c94164200720010364060003c01c00300300c2c2201d4120b5900b070b524004031f10741080d98014601d101d203000c6c1031085060f0001910f0b4104c48141d45c1d0b0702100d80c1c6540c004403003000700408801 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 492013974 1250 492012724 492012761
    0x115020f0d030b010e09010605070203060c03160518100503090708010605030703030c1703090105040b06011d091003020901030b060a2c04030c0503030f0a0b0f010206220b0108010209010f03 83
    0x207680a10981001140000500d0448134003c3c0d078100280414400781e00c058041000042e1000c11030405000190b44582600c045c0c0c0c4c00c40c03070107055002c01c0100a5116070b003084400a03c82d4101040303010301e88108200602600c203040d041400c00752803076200350b4122100348640c110004a0110500580044c1e503800340280921038503507a020b80f402c804ca020b00700c44c0c090030040b00c03203012008100a10310034001900049214100303403c0100320280007400c141d0401440c12244440003a19800020030340c0403d95801d11940d40c0d101c0d181c08074030000d410003135224501d14000001d01c00c2404c070b000e0044200301c4181c40c10039038820b244070182c88140240c110f6404106042200c10005d1000154818002d007081c83d88050305645d5079045910483e078240d60724011200f4011501000d104010024100303490350342e170060324080043d41d2071070020098441d0740380b44400c4280a0b4000741c08030307200d01c3d4410111102561101e500c18040d403c142e002e540011002191400d605229005500f410079002c400700c1c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 492015224 1250 492013974 492013993
    0x4050112170d0209060304051b01050909040b06060f070f0506131a070318031206091107020d050f0f0604030f03020301150305041a0c040e1005010806100210140115020f 74
    0x4010742c2060107100aa240d09000700d803441d40700c0c030000310300c03680c45900603000302904882d848134522401e60b0300c64100503083c403911300280c649220380364020350031112590b42940c6000015202d80300388000015008008144241041001c0c29114041441203064811503a600354100302c150517000c0003c0c11a0640c0307041c00b540c003203d1424035031304808a40350105003e00020b0320800341800010007140051684080c00d402071101d840740301c000e840f03a090f00340100b0b5452481000c86018030f0310084c0c0b156100b1303018002085070030000c0151200701d190684402c0d00ca038070344641c1c903104d04460039004103c042c00098180da204e482101d06032003203c4810f0200f5120010700702c001f0980108102d850005d0250184041c0758150b03051441080b07840c000f255140e04000c0343c125a0000070340f03d00558003a0312000c0c0802e0383c03c651402d60101c000e60f84004241500e804c101e1405000c81076244026107440c040d03688002111100c503050710220101c80c0040c0c202d80700c0072641c0c0c074544c0350310401d81e81190051 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 492016474 1250 492015224 492015263
    0x209180607110109020901030c060f11070510120f05010e0106020a020604030f03050915030121051005130b070915170705030c1209100e06070e0d022b0204050112 71
    0x1c200220040d02c000100c5003607942c080f0303040560a0700180d500c80f504c0001040b841e0750160070b00c030b07070b140741840c00f5085840c50040e02a5070341c0007802154480c900041074880801d10a26491900d40c600c1142480342c0194074040100900080c00760115441c001d00010030101c3c000182d1405596002e4501490a440c40e1200300071007030b140700101c0c10803004100c040503d948400342c030b00e42409032004456580d490000b030f1404400f0310240140000b0f040b100e0102c045000440e02c0401c000a0031000b1501c0d0341d560a00610b441c0f034100004100b1f004000500ca880c41c0d210482c1c200b560842c20050781c4040e02804d017130340c007404030500350300710b03010024006010f042c811005590080b180c0140302d07003405148140031103000800c60398404103500c0b000700032450408a01403c0c0b801241c07200a40a1814103503c001c14202410030303610f00542c2809070800c11502c40c442c4007a150b1000b042401c3c040c02d0080b2000c030b5412032031501684191304080001c1010100690301c2e890075079000c03a410401c0c4100004 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 492017724 1250 492016474 492016487
    0x303130e130609060606021e100f1e0603021005030c091e060403050c03060c0c07060c030903080d05041103011a0405100302150c0111090f1c08160209180607 69
    0x8500d801d20007079509800014414024070251511840b40491080d0404400a14004901807810400100c903c11401e0000022564950409100c00045845803d180152001e800c044070b041c03038103907501c0b00100704060159202030196482124205140800b40d4021140750100b581c420310040d00401184d5000d244c4480400081c0705101d0300810600004d0000801d01d0b0400c2e03005840710307000b884002010b4602030000366840b002e064019030618885200d903035a02d1006004100c140101c080801c828140504802001941c0c00003500e45d4440c0d600105001500341075808036140000e849070b000300d40c903060084510307090503010103004044106003008042d245c05030000401c150300303503c0800961070b4544d03001c1b4106c2d4800c088565890200c0f15481c00c40d501e00e107c00d8100441448071651951303c6400c2c06a900d41d040301d10942064510f4507428000c1e0349800700070201880050700c0061a00114120070b0203c0c000c0b1000d0300329a03503240b004001601b2160002010b5001240000d0204d0b02030b54 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 492018974 1250 492017724 492017731
    0x90e0601120501120b010b0a05040302011d04060314010c1706220513051c14030405032701030c050301120b0c0705390307090e1005010f050f0303130e 66
    0x242911182400d41d05140884800384c200400c0c0f80c102c01c0c03800080c044418003240c0100048a415481d210041c20010001d00070f0780002410400321240f6901c940944440056003000014801c01007242d49191039140e48143c9011941c241d401c103401407401c40d004650300404041040d004c00c0b02651804200310900c402a44410181a007028022220b24100e00c03545101c0d012810f41c400322411207040862410b400104242c0c002c000045414204a0b4032144503403124040450113500e98845140960071401143c01d020808090300c4190040400e50b090703810300c41c2c10281c9040040599000045816202c2402030b480613150300c001e01c8000030a104000795104400c22550350078540380d0f60b03656050a05200c59802d0300803203621100040d0408088000289104000081c025246200400c0e2a48800e100d104002541c59408540e84142400104441d40d030f240400c104035a110651440d110307560b4040c540c0034244109d09400c85040000c100c1d210380000c01e18044400f440e008208010002c001c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 492020224 1250 492018974 492018977
    0x15030b09012307080106200f0a06140408070230070e0c13051918090c141c030e040e0a0c0b040b03040f02150a0309021302030c0a0513030210080106031a01090e0601 72
    0x3160702d032910082c09601408e02881001c1d0521603000d0502a094980d12406004800a14800d000000307444a048a0729a54140c0348240746a8072503a0109800b52100554101801c4040c0480c05c1c11101141c0c04003924120400900641c079000c505040900440d0300c4103080b44548201401300f40707031107c56030700e030060014400c4122503190394001d10004034800e07000c012141c980040c0010000c041451704003500080c004807494444040018000000da00c4024034252001d89400041c144241000405800050b005000503580078001c291395140b00c200555400c0341401002c2000e6034400101c801311541100c2c540d045440b02c1d00c450444181d102402c99114107001d03140028001d020001e030801c07001c1920001000c031824014024010741c0d5451030007081c0c0c0304104004070709030b404050b03412800c014070b03095494003860b501c0584000b03e5904040c0d4411440c0000c511010303401010503060300e590303960611500e0685e0184005004204010f41d01003001101d0521030005044a840c2c4c1c4003005 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 492021474 1250 492020224 492020267
    0x15010305011d0129210d0f0e100302161407050316050f010f03020c06012d0b0a030f060504060306240302010e090a0f1d0f0601030c0915030b09012307080106 69
    0x15154007071201940084601106c2e0808440c0e500c81c6500703c009000300b102141442901ca194500018040031404441801815400b244143c50780340c00903500c130285540304900031800c10070243c10564030602c6c1c0c071540d486440345640d001c144258182070042211310184c100b00c0c03084922001903413141c1e0744080300006c0550030b1020b41c0582c4001c000c414001c00944810a44502d82001c01514804441c0044160001644c004110201450b42140d0300320001e032030300280b0383c516801e010380038104507032060303510505000010040c403a02c0e501c008459620f490128452580d0168034240e035408503c4085d010918030001c908460a00c8a03060ba405058910001060301600e03100d081165078500c00b461021650803280e01c241c0004000c0d25410702e40d01c10040c4030b01e41c5103645080e003c0059000300e04000d500c1d451031100800503c4c000324051540151a8881c80c40c143c07088c0c034001c00650b40890350103180ea40111001c0b102441c0007900442c0b00ea80d40740c405a0a050040c0c68440e14101401d0032840b1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 492022724 1250 492021474 492021499
    0x10b070812010e160302190305060111150f0612072c040c03050f0714040b030f030a1206050f0907031d03040e0901050603070602030d0c0215010305011d0129 69
    0x40300181c2901900120542240d2400c0c419013040540a54402840502d0700c1000070000003242095031060031035251501190554440c0c004070b4002402c0c072049915881001c0c4800032640e900c8050600c43d950b00c0b0f0301200c095542008010f5410f2441c0500c1d03031036402000302804030781c10103262550107860b6106006551041c1c0b8001102d4000101c500756100d90520009108200d03060000507600745a013001001e5290030054031040c1c03100c111001a202d9581e802c00d003a8640c44c01e001c210f081c0c1500c2010b594507840d0400002d00f0068840001c5400d142c0307417040208045ca030841061203c484007a1810219035503440066000b403445d1200c031500380c000c8211900704d4540400c0100054105e220000b80700b820314050403425201c010700708511035000043c007030001c541e00006a0320481c125140125802211886c01d90030030004c28032403600740041c00004424403c054019420f00000c1002043d0030340340381b00340507007205c007008060200d6043d002d03000e0090119051206c11300c144000c243e44030505 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 492023974 1250 492022724 492022747
    0x6050a020f0a0804061514060d140f0709120f0305070f060501080c09010e041707062012061009090c0201110703270503030a050a110a1424010b0708 65
    0xc000030035070000a003103c010401005075500a4600d510b0450b00540c9295080001c010704000c118001117010303480c082840030000c8541d8000c0c0e0480400c0700c240140c0340c03c1001e01c41c031041404580d42000b15421120024942e10441c2c40c0c0091a50000c0090181e0840b5aa08440030742c01020203881c81d883c11403141004c038104d031055070700800302a4000d0000c510403005100d02568143e010300400d45105c404c00c00820b412002000119a040415650303030803e61809000501b88908003540980d14600c00c4000c0d00c132042c000b0203419076042c10f0042180c0d180400c12504408104000300064640f1804004201c00c03500441d5801c800e90002040759148200d00508680002000b5000030b0070520310026060750740e500188030380f03c840c0c41410741203080034042a504c0c8500450039007004800180400d80501c13401e104185c10210a00303440c0c2c0e0043c0e80c101b0b10309049404055481c41e0203622041c43c0d4450b20901003400e0707480e0041b0328099980c6494061655904496000e40b540e0401300091040c00 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 492025224 1250 492023974 492023977
    0x40b130e060a110301080a03030504081b07030204051f1a0c010911180705030c0307170708100b04060c08070519080a080703090f14100905060a111606050a020f 70
    0x51900300107150030b10b00040444191049680c6502d0107503c1000180320f042e10201e840e0b105180c1608021030a91200d00d800c40f005e1054802d9264440d00c04e50b240d40c10320b02c0128000341101d00880d414800b94482c1d94406e0000c50b1039203003054040307800441c10010412614142c19504a611000341d04250500103410300b03443c04a40111041c0601701d010803410314081c3c20181809030300c01221502480c2051016000344405000080c0741c03170000c03000542c111321443d0b001c08002040c000c603400d141410300e0054080001501c401c10a415212008500345806905540441d41c060360361420369210303920b84c400e442e817191000f59890b002e00d00700c090303048904155441e54544190320090759003885540040a6440c0980304c6030401d1b007880e5000c004154090034404145400140b0404114800c8155515080e59103c444d14042d040c113200006001003c0390180c450079400d0b20500100039403e040000d284183d030007100403504038400810109003150f1003940c4c00040c400d0018907280c0c0d01c1c400761016 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 492026474 1250 492025224 492025241
    0x60f072001021903060f0e1f08060a0609050601020a0212070510110607030203010609091a190e090307030f08181b040b0f0603162c12030f09040b13 65
    0x80342c0d0002051010260815142845040c0c2ca240c10042c890505d00c003450345002a01c60064464480c3c808615648aa280d646402d403520211060103240c2d0380064989a42d4102e03040c508480ca004070003c0d00040c180602c0d031003044e05a0207019401142e07800c0083c00c04060900015501c074078075005c03440380c5400d018507a0007511900c85807103200050882d645401c2000301903608150040c0010041d95800401c07000a82d885048040390112140121f0001103548600707559028002003c1c0ca0341217004209074030156814070b11455202d58440304c01955034401c03000001c00103034028002c000d11a200c2c0301050703005071444182190030884040010700c1e00e00d15112840356202040e8150b07580d482c1c613100d09600d8000581d001c11500c01c01100003802ea010003800c5c43c1e66022203086502002c5d1240d031071103050030072000c400c4d01f18505403010340381c0503968800094084c480d80d8119107141c07500041583c0205a098550901d8034810400340400342100c43c0d003841d0096050610300718024028020f4502 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 492027724 1250 492026474 492026537
    0xc06020a0210030e0309060901050904050103030e0315010e0f04031e0504140d0f08090f0402031e06030a0b070e010c02060a0f030c090b0d0b120a030e0102120309060f07 74
    0xc0003040d801084a032031855010700302454540071580070710318808410399107202030464146803280303c5c0f42c4c0141c0346ca205001981e40d10515004c00401016048034507030008640c05d40859207a0032148000d0010740d44280502200d07001500d0025030100380300074440d5030003807082c0782044110401198101c0a01e00d83e01c84000402c0c8042400e00103001444130307042065108541c2455101e0341a02c442400c4c41d800300c40500001c80c00106520a44c56508600c46070f91800751085580345043e401003040d0440c1034030f00440150b034003000306100340340c0080c2490b00c2a82140804843c1d4482c94400d8a0381c0d101e200b100e50500c1f260007860030160b40d4540103010744140b42d445200300c5140f284030040468800d16054000d20481da90b00307001a0015005507030041c060f510b00050311410f400c00003010412015298852807064401c1c0300201580000003102c4460280c00700c40390b161106542071918041222480303543d610003000501c4440c681c45030356410000504000407098440b90b140300209945032030040 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 492028974 1250 492027724 492027733
    0x6030a0e0f100509010506010c11040c091a0d0c021501170a0209090303150a06120b040e0f03071e020904060f090b090a021306030c1a13031101030f1406010c050a0c0602 74
    0x50a07507028050254800001d18103604c1a49c410f0f40c614a2200b0304c00c00480c0203640c1c404840352311034055004c40c005071400c19002a040360720000795060540c002000711490a0410484140300c03800082c201100b01c0003046c50b0081742e07080c02444440c03050b40300411034107849030b2505c210140e243c000440d03000380700307410286903249800403c62200088400e1503501031003005000b0860141e00c1032004103448030f0254082580205d040018010b0112165204076038002c1040d80500f1980000c02004210710a40c9000f03001c14035883c0000c001c180d6807001940181102d400500011403a5100b410041d5820701c00113007801043d12100c44080c000c4581c2a6a5032190380c1510562411030030b01d07000300305030720f1040c02903904598810300700705068460100540c1e9520418070824401c60300f5542c89983c03401511024581c1c90400c072941c40c50301d0324003c0c04640360a40c6254842890301940001000051424149481d40300046034070008058098445000d407904040c00034080700c0c480c1d00100000c0d4001d0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 492030224 1250 492028974 492028981
    0xa080105040c020a050c0d050a140f0d020f07120609150b03070b07020a031b0e0f1506070c0315020c0304090207060e0312011202012007210206030a0e0f1005 69
    0x40102d80e01000e032501554000e0075100300042e80041c202d9250002618a8131210101b4584039150048100c0010034241d10000ae4841c1c881c03000624006414114084030414003120506030713214418040b007994240c00c001c400340300540c0c940b400c0014061003441b00081049168640b02806899228005111a1100d500c4056490204044000342100a0b00380d07141100681c00551071a01d144401890740c07c0740c402015451200500b501c00030003184005001519044050001d80c0e40200e920100c0d0886010010361300e401c1c40020380d084190322048081040d400c0d0345402e180302c0007070007040d0a01c1d5000c0140c00c040c0b110a0002d00002c0c03010550150302d88241e442c201c0152883c0180d4203107103034020302c1501000c00c0990b8486044480307c818515003400c0a0004950769126001495021b005421441e4000b10000424904131403051a5110070400125219802841c0140001c2c0d80070034107102140140c80c10754402d442215a803411a20881c618841d101c6c209580c0141d40d480c4a60b4a1081 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 492031474 1250 492030224 492030229
    0x19140d1a0414071a040312021e0c0a0f05032a060a0c1e080409020708121e01050303180609060c0a0f1406071d030a061d120c06040201230a080105 64
    0x80300040c00f60300001030601d158100301202c5502852102500c450880f055090340c42e402271003507100881d000f0044003540701000220320b645041a2040b02e00415501c81c00140780d050b68150201039078001800340801008007000e802d000d040c3d007140c030000028000c070414001d83e0b40700001c001001864a85030030000050500c41800b640f8403400f50409558110100700140c1c3c0340c030445e03054600382500143c030f0708064240314041d40207910f10b00030311000560612210800c0148004001440d541c2d0542d41603880d4000c0c903480340907404400c0481503030011b0079031071854454003400c8140409401107043c400ca08a03014036000c252a000d6502c5000d107070b51181400720b0090700700e1006071200c0090400d400c011800400c1c143d24441c01035900c0e8900c0101244665050020300450b90300800244207150300302c49503405c0100b0626401503940300754618600e02582c5030003611101c61000000c1e102e82e41c0d0f00e0f001503400c18180160300c8407035960300c003600202d10800301c00f41ca84c1d900c050342d61007521b6041c8001d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 492032724 1250 492031474 492031483
    0x914040b300105010e041a04060915090b07020d0e0d1a0103060e0d050f030402092505030a0c021c0f09030c0608240f040b0f040203090a0219140d1a0414 67
    0x4451740001d07650402c40490402080201310f00c1100c0c80c5050296a0342c1842d0000381b80c100d4000340710f806a400300401e0740351180c12a0307032024010030380d29540e07484200050b0707920400c0d078441c44045030484100702c1191078440c00320200140140101d40e010b58650761b0000030540240c0040b50810b0390744071003000d2181c0401c401c6500200354102036150064420241046001c020b00007840b89141d0000030b030007102c0405180d26002c9050140303001ea1a20303641c3c0076050742c000b1590f40c000a4074042169020301d1000071001d003210005410320b400100d00030401c170741d44480c804a0006100307081d2400000501842e01440c018200740c0e4480600c1c0c00c00226400951900d05e20f061201c0080300c83d0600c5680c3c558410411950307080780c001a0101800e408901e00104494002343d0080c030104c20080c2d154400710700028003510803102409818141407002d810a0301d1030040518440c6404020049414600c2c00000200d0041032584002c1807211104c91480c44211001c0b00c46007149a003a03401c0503000c10 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 492033974 1250 492032724 492032729
    0x204090c0203120a0506011101020a0c020420070f02030a080406090602070504022701140403030210052a0f0721080109020301050303300f01030c05010914040b30010501 74
    0x80550700e8610b01c0e00703010741c07003100240c040040b071903581006ca50981c2c0a12001c0300354031307000c030700954a589a01c103003e0103403c03282000341d0059041112074250001304074204801c2100c42c42e020760505800d80c442260300c6012110483e00751007022000004030310880081c2004000b40ea50304112241400c20081c00c0a030550b0090b8000c90061280c800704500c842c1d0049800b1005c2210640880380a01c01200d1250b4901c0801c10241e500080c08024958041048804660301a00604c16a150641e500c400c9281046401011268020301156100050b20003001d0750322202c444c0324142207007516800405035a070341d03582c001310130760b070720910401078000390107500401504c20114199850302d800301c0c0e1207100b888001124000308281c1503042d092808030801061480e600c90680790710340071802c1d800c4250280419074a03680784090001d420341c03040b0f0740700b000c1e24000700599040c0c040110130b02000c0d020950b10349038090407159040040906410340510300010303031401950306c0003c03031506c0c908480068 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 492035224 1250 492033974 492033977
    0xb04290108060a0501180b0406031d0d020c1003090606060519111209121606110606010516050f0a080a030c0c05150702070e0103050304031505040201080604180501020d0204090c 78
    0x201c04004a5590b00003c0340f040b51001c0c00e05210700c18480c00070241409154020215564001c2008191598540d01c0b490f0020180424581002c103400e000c1aa58086a40c008005a00c00d120302d010505214030281a41c0c1e44070305000ca0144429036440044c0c8105400c060001140811082c14044645c1c0040008007009c2c1401c0d02d031130707142810040d2502449000c111001800103a6001c0c44d8540c1c03140c0101c0b166020080e9611105510303010300030405c9520030040001d0184900141c0e04001080c071501403032050f11800d140c040c0b400101180c0780300e500d0003a201c2d4050300c0001c1c4254802408030010380c600c280080e0b0b075100880c0c0d4028003140c08085c404010071085085070703000118000b4041c03d000140800b1a807050f0382d512030491030000f00790440c11111a2140000041020000181080e6445811909851a652400318040790001c0310003a00003a0188041840c906096029000c1130040b1010000aa810390f08ca4500307a070300c0036090000580d40000c08002030b00440c4603000040b04103 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 492036474 1250 492035224 492035237
    0xa0504080109060b09070c1109090c09040c0f050a1d1504021911010e1905031303031205070305090316330f0618020306030a0f0b090c030f1f0b042901 66
    0xb0303403540b1080c00070342d440c014003d034549d1004c14001d4408202c1c1181041009043c2c0d90030345010f142c01c21502d960751241103050f21200e180880c05d850500706070300507240b140c50100c160086620106c40e100c0c10241098413401d42c844075000b41512103000505540b4030015054100340344041c00104102403036207151500d64545041c80f02c444c0004140000c1c8459284803078001a08a410018118803640607010414403501c44000101030f040080c180800200e42c0c01004252341d8580150183d4200300e4910310700390000c01c074045044404800c0000114001e8066440e2120500755080d030414001e12420149008081080c61203002d6000b000040d16a1060a00401d484d100001e41415804400115180c0e008070004a40307403002c00423030440780d82102c030040c2d0311880c82c140401c540800340c900c1c000b94042c6842c440c1c039604001541c00c500c035180305c005004200f4546c0007040862258804656150b403119032207038007070341c03070780540d03403401d400001d004e8540000345030700440420030f20440da41400362 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 492037724 1250 492036474 492036497
    0xb0f090f0d0509130c02060109050a151e090f02040906051801051318060b040f1103072a060b01121104090b0d0f06020d0e0304051003020a0504080109060b0907 70
    0x1000c2001078840040741012901e4422a10008001070780c01104009518640001c0c20080740d80018a18101c0c0c914040821031500e03981054425900d41035080f03a440b4001d01c41c2001341048061101102d030700640c84216091b42c54444100644a40d0291000d4150300880c0502171102e291140c2070041c14200c3d03c0a00103a20241002c01c071040500c182803240e0300510f20380040764042e4000040310301e0a84220b900c00d000c285841001084c4105d80c0d00d0081e8079200448054008522030b450200345074000c15401d50740e985400300c8401c107000d040d591403466003540d0705c2d202c15208080400075511401d400325903010340c100010441c50002c90712000d00c80c02d0180c560700d428040c85c212002c0d9200006c0210305102c201b0081100b08004803c010007081c41508403e040c00030b158040d1040011040301400442031025400c0c0e80c034082c41c06020740c45a010f4003c2c4000314041e43c010007034541e85080c46400c4c00c0c0d803062802e0071581d40a9080d01c542e41c8880d2000c0c818500244266481003190800700d030740d0507 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 492038974 1250 492037724 492037753
    0xf17090d08041403040305101103060102070905070908060906160f050906090414130501050109090302060613110a180e0c190203090406030c0f0501030b01020a0323070b0f09 76
    0x340021200401d10072031030041001d000515801c40400140001100d5840c0e58a207071203030b5039213002c078140c94180d494500d0944a8208103800c43c3e00a410580c002d08146060003140001003501403d00d8003440300924001074584002c1c060288940340c01009090586404c01c00c1c2001704513144d040f0b0080104450b450091641c002c0180c0d181c80100fa10003541b034010f0000450001c080045400c0040700d01407080000707400801c0c03407089150f44514000c2c0850b9a86500b0f0b5070a944140d2001800350300004c000a405050002c03001400008800022030888800b142110300344d0f000c1002180024241c0062100417103075a60342ea0014050014284c91030710340101e80c603007a4050f201540c201da00c00c1155400702c05108106540020b14028420440541c2e00e20740000204000e01c18110365151070340c80007640d50300a1140e0a1401c0042e00a4066031140342d03811509894004101010289502038003141c4c4031260002e080ca80344114202e20940c10300b0300001c0c0020758003c240c0da08540c0900b0b0400c0808 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 492040224 1250 492038974 492038983
    0x90b150a0207060804021302030f040c06020715031808070305121302130f0608010c030204030312091e0305040e040c0e0f0c0f090d060207080715110901050309010e0604030f1709 78
    0x283e41c0c500d40707010307241c880d807002a0340c3c4c030114215104101d0000c070902c2111980c2c00407844c0124450142000100e689440582e1120182e20528030100c528803400c1035518001c1e080308481d07106810a00da03400215998840e900d8028003020313030024101259600c0641803079030100d50012040e8407119401541c40e8002000c42c4011002c01c0c1c3e0041d06c40009907884000c0e60400805844003034001c0c408100441d0009000350080c1c802900047e400d40d60305600000a481542101c07500168000c03000801c800c007442d129640140d00b2401c01804100c002100001808424004d51241c0700700c5082600d081b191800100c006412214128903d4043c0128003009100300c40005115411650311a440240010202844000e011304a507000007040303001c00c03035840002d100b02840b030702c406180103402420b9542100e20f031072100a200076040100c40d40540c082c0000e143d100c991140045042c0400000b40340c14101b0503a400c41c04030302c02c86003043c4000d1f0801c1140e9a90781c20300040d241686014089560345 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 492041474 1250 492040224 492040229
    0x12080a02040e070f020c03060910060b090a06140408060a0504140606090a0c090b03091509120414060d0f0b150f07120c05030403031707030b03100510050a090b150a0207 74
    0x5000a994010013014001d025a00d16220020180c900070700c0d090461a0703c9070b61200c2814401d919041d00030070100c0180c001c0c4d96142c400a0101c0b142036003003c9042c0c82918054110440401d0188400140300c5400c10005200700b8060f00c02260504080c80c0c0300c1e90300a80c221020070a9000001001003d0b1100012554805126480403902000312003069804145c507030419000d10304000108610ba9034001155070070801c1100039929146d95100c906610381d66108010420300000b000b007088600c1c00381000c41000c5070300078401ca01d0401b00c0b008120071994008191400e01d601d81205002e1445c00301405400c0850702000d99207800480c0329039040358850054024840c108101c0c80c00c00542c0b2600042590560100c2102d80d5a520b0b402c000d0300c1202c09aa01040c0707000c5920008500c81d200e03029440444030b0181c004d1506040075100d02c406050010b181440948003040c0000c3c032540c6620b005001000b002d0303000142c07600700505014801464185140c4004801c21412502d036500084000c00c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 492042724 1250 492041474 492041477
    0x60b0406080417040812180307050612091c0c050d050906091306030614010801060f03020603190b040c0e01031d15071b030f0e0d0302031b10020712080a02040e07 71
    0x3c02107405060b0300c1c6000b81c0e0031110691081c1000d5074070b103010a00003004001942990342405281074030805a42d00807078003d07035410100030b014803400c1c001e52401c9036070021490b0040c2d81d90040c1c006003010000c0d02ca40300c1c0000262040200030300b401001c0c050408010964179065141458030800325583c0d200e0110703c80c1c06602c40d5042504444610707400382c005180d00160a11600425034000b40f40c100003800b80035169460508002070008445c0d008000b00c99001d00990b04564403180580010301c603a5194a41c816140c03003081c9440c0d640c07032080680000060f26402c2802a0f80c1c1c0004013103941c0b280c20240b603c0405840d50816510025200c42a40020815214566520202100d107042e8425180b0040c0396070741d190004068004400a003200d5981d6a018040d1000764200090b1200d010030103009a04100041d120f060303000840c50035007011b20b00450314000026036441d02241c1c03210300c05403045682c0400c8072180540c0514050380003c80802e0035030a05090a03580145c45101801150 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 492043974 1250 492042724 492042743
    0xa0c1b03020106080d0314150d030c051e0f0f0609211308071d0f18120c07050406051203190c02130605010809010606021b180106050409060b04060804 66
    0x2040520035048100580901800d503100c1545599001e00540091060324a00e03246960010b1003441c000d0546c410201001401e450050410340c07000d0b5005000b502e0309031b0742405030b02460407481c1c4008503941030302d1148000900c00160301940103401c002c00030b410032242c1d4200100f400032070400021070101580381003905070385400e180d030059186440b450010b140c400c1d4801e01d000035504000716243c81100c141040301d1000402d02000401c600308112655041d549002011541c481e00150103140d812031908210740c01c4140b000c0411000350407856821203554070192045c00300d802c00b801b80800030041550841d00096a0064150320703801031000d104e030311164210200000d50b104104112a440d0040c255460300c0755080c0076140548070901640e80400d004402092110405124078011680790b81d000c0e10180280c0c417540f40c2d90203d04654140d003c80d81500308510f041020b030325540240390030703124030780e80300c0c07400c0100e60949511341d20000e0401d07010300040000030b41118016912070380c0301082d074 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 492045224 1250 492043974 492044027
    0x180d030c03020c0f0306190e120702011704200103021e04050a060509011e030204031707051506130905010f1404050607020105150103050414061302120123090f1605090a0c 75
    0x1c018031b150700c8c14406030f01c0f60100a0b410007007100020320f03010b4001c2c2c3c1c40840c42510603640160802d81500c00030702c0202c80c05485454070103407085844020b80145005031401d200030b5000303502121b1010740c1c0410303420001410411458003ca82c50028001424034500f82600b01001a1080b8000c1d6002c142e40d500d001040e003071551095049402a40e0b01c4150700030381d980c50141481c060303084202d003240c0302c1c4500c103c0750603082c10301c0c0412845440f0080200350034859543c45a0007a10052004507080e40d217411030040b00e800389014420080d940503d42403250301c0c0600b4190316201e00503010344c0c2964500320610408419800310102d00040c00e08000c6419200e92816100d5817030400f042c80074038010700e0309019024411440c0c0707068180c0202c624075a42c0141c1041c0508a03840c4050000c0858110241589926440c1890a910190890903202805800708480d03081160801030301c2d0086010040030310540c605045140c0d004003402c80204a10302045602409807450605007040c503030f0844044 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 492046474 1250 492045224 492045271
    0x50a0e15070e06030901060e040605190b031b1503090c090a0e1e0c0a0308030a0f1a0d0c0801050103080a08070c031d030f0f0309010221040902180d030c03020c0f0306 73
    0x1f140082c501201e82403078914203420702100510080e80e00e0414101c2801100c40d200c0d0180c041d00c0c07000100140074282110b4030040030304410700740200e0f46401c080c0d00d051f107026518a0300040c51140c000000a000500542000c101190710010103580d0301c10b01e820f4800e8420000080c8640e000107074803a0303044060307095800b8186044950b2040f154044007442005c001c000915003c3c600580100e0300034461184c0100c81d0a0a03a040c9038204200080e07680004902460503d03a07115919000da14800190b98a42000509403007090b001941e20340c0d8000b179082001c0781e00c01245944203c1614210b0080320055a0090170500d004500c0d000c02100da020035046a41c0c10301c1071018102402d000c80700c0d803407640c40015807a07401480340c00e4094001d003040b541c000601c8544c7d1520342d0008035089884c190600e0440e40c003d42290100380441404080c3c8501640c0310070710503052460181d19041c1e41c126981c54001e00c0c0041000100740070701c0e108540c0d994580c5000602e80d41104940744108880d0551035030 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 492047724 1250 492046474 492046481
    0x5040b0711180703090b01080a0f17070f030905090709030f030c02011107141009240c060923031608030c160f060e0714120a06050a0e15070e06030901 66
    0x203108040b8440e030780c2401070030340e0983e110500c0144500c5648020313070b0b601c160307a540f00c145031003003c1d00524441212100043e84182040701d8a031885d0803103428822103407642c0103080807861003200801c0c0c0b00d8000b48024588070b40740a60150062414005960840e035801d10346031000c0705d006042c031110040f40310840e8005d030784d10301030341500700121910b15544069100c102041076901078043c0c0e1301300e4034641d042881007078540d0580340c00701e40b85d00b00790000c0202c0190810718840010308010540d80c6040000b2a03502816820500034039132401c52087c03611880140d80b0183c800c002130750b40204403800703008406040300c1310303040d0b04250095201e0f40c40003802020303881885189454282aa600d06041202c40b564103a500f80c000d140c20440740800202d860354401a6004070003004110300a00c4001d4641100200d0072000355200f920045151070391031400b611825a103120046480d03811009421000300b0007407220700030b0780390b10a4071402c0410010701080d138550030710f41c0a000c2c00400503603641d00940 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 492048974 1250 492047724 492047749
    0x2030403030f1806060b07030207260111030f060d0210031a060d0c170702190501090b010627030b01050d1e0b060405060102060f0105240c0304030506010605040b0711 73
    0xe000c0c401a1a114040a15100010400c9131240d10344180031908070004006d0303032109139041c3c0041201c1401d000d44d210350110b9640d00d8214881d0302100010240e1000c3c044c007074040256003580b903200d040010700d10300c0c00c040c0280300a0054046a03a84e80240c1da8166405024080a00300000c0c1c001c41c40d140b818403440d03600e04854115a000450340c02001c01940a9010744503035546000600e841542e803841c1440040d5080d20041e03000c00c5891445c1103902c6110354000f8840ca0000891800d19590ba04500109034080404903003100a0300c1d943d10030040440c400050910503001d162070070366456262000060040c1402489100c10301410480d0941030490342d44407202e00800039641070300d030400c0003c8040316a00e000d2428000450b0a075400001c00b82e010f0f800340b002d40c461681c2484144580d081079220070982c04460000300300c0d560f000b00c2c40140fa1031001003014564440c15403c2c07607890001706a01540402208100c1000384401c0c032001d403103401758001544000c000c24100000c0000e0102c4 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 492050224 1250 492048974 492049001
    0xd030507020a140a022103120622051b070308011505210105190e04060c0e1806150301050904171317010e0c1e0d050a0b040b0901060b0d0203040303 65
    0xd00001c1141400044c6900528800c0300c0b1240041c0d6540e0740c10a1040040c1d00c480102d9100740320943d40710038982c058036807010018082e40050080d2034104290b15075901c20181b0481d603a00c061000004440c4609044400c100c0b21003842e014039942e00a0201205108040340e050000b40c56910365031141c0704441e216200200b21002c04880d03c0c01c2100b0400d030038890103101c0c1c0c103106800d40c2c00103040200401101c0481041440a0f911521900007070704e40c0004803410040700090001d0305030798240040d243c02e10180000d03070b0301d0b160403000d2154181810002050a00c0140010042c030b40d5403403a1b070795119034800c182505070214140070944c540500103a082c07502070109404a4000c900c1911007ea0040f00d100900410500310000740d111400c0d120740030f4000e4403403d00380340b42420784e00c1094400e00015000c103c46100030344405003092039048040740c3d0054410f00340814002244821504001294003c00805213410f868114130711075560030000554010002070285030003540210f4581450 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 492051474 1250 492050224 492050243
    0x2b0c1a010b0c0c010201060e01060810030804080a05100b0d03110708030409090201030c1806030b0f031c0810050d0b09011404050f1204120f0c1502010603060b0907020d030507020a 79
    0x4540c41107030140c1041c40600960f00ca240507140d42903105014440c100d070308200c040a0780d42d0911008489448005003800060140240f0000004034420003c0005090140c05001481d1452a000f41409006c280c0d01840034149032880303401d641c2e00b829103421283e140c14495030440c1040110390030318405500503002800080f40000c3c40c041180c1082d51158800da0b02041403500104d8255201c8540755074a061131046814180103050190703001082c400d0b001018075800300c040c0da0011f031400c0c1c05c024130802d80e03030816003811500a070410803150704440b60000c400d4600f402e10000c1180b2101e60300000e010713405540089044140c00f1f51106600091098000109142904000d0345d203103010180f00002c3e1241407046c84901500340203880a490560040000351100380d15050001c0c00d8150f070076650300070110000101e400380c01c991b0480300351050300013003071091442c1010f400703c81404a09502071100241006041c0e40d0105101d500c8402608000510b034450001c1246001e8400c07900400b034518 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 492052724 1250 492051474 492051479
    0x80405010507051e0109030e180c0d020f03091b0306040b0a090c0306090f02030d0f1e11070906050f0103050402030c130605030d050c070503010e07060309020607170703022b0c1a01 79
    0xc4c10340246d10200d01944488a5685981041c082ea408002031881d0098031032201045070605280c0040015084070800581041c0c410006040300d41c0c0107866024545e8000f401c0f14814284000301c03038662050490240110380340503154180d4070640101480034244d512055001049a1046814007440d0802e104000751a298a8204062081040c09034401d1051490301e00001d0300c43c035031803400203001d85c1d00c04c00c15201c4030040c2d42101c13100c902c500003840001d0304c191440c850100207200041c6840d0308003290755403505c0180b01048101688190402d03003410200005618005149075001d5801c4d01c00c0403408400002c010b0050440d50001d030740c98005c400c40b0f4415168400060f0078041030031f5040e40c4803c1d03692400c0508a0342600403c0c5840c1d00120703420032149000e0b41c0428007481c0054084da01c1d10300c1e20764130003008480a10702c0040210780403070300506250741006008401401d02c010074001c0a85004d001c6418008607800c4810081e070941c00100f0020302c03203688441980d00700c0c03441c1c001d542c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 492053974 1250 492052724 492052783
    0x5031204051305190c0e030c0a06090509040f050d0f030c0504050d08090a030605090c0301050907080604020613080d0908190b010b070206070813030b070e01080103142a01020d050708040501050705 86
    0x1c06c070b08a180c8a071156140842c0c051400801050407a4007949441940300e1600060182c00f01c0001d20581c1e07410a01480760b80170038400e100d0041209030071344d1071540c0d035800080080c085503074800c100340401000b4441403085403152500e1080d503079003103c4400e440c0c00f891400504800c0e030540000b00510b00b02424040d007500001134006c18000120002c0c0322036501e00701800d54035406449009025440307a0080303405803c19500814840c090b1442107024136032606c1381b8919003000501824005141c0590803c0146000d03c25420040350031048640e1510a984450321140c03018040c0d46241e42000804c1005c65507044112080d99078400420703501d5046000754180c10502910040d28201500400034800e02d02c01e900801610760144c40741c02542c0d09548800c107001c2c400340319022051040d2420000a00300742c1c0b090b100d0301150040480d807990790300c000081c202001003140c0c60900c441408401c00184200007030342e080d16020301c0d2044e2612554140310f454001d46410034078620f0030203c1641c541c0c2 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 492055224 1250 492053974 492053987
    0x120e0d03050a14091018060510030209090c01020714010903020a0e0f1e0703020901030b0d0f0c06020106080307140c060d0c0f050307020d11031b060105031204051305190c 75
    0x2e1621450412209007090042082030408854002c92900325168524901d15554840d800c0030341301a854144020f80d81c0d5401d4200c0b902503e00003d080d061560406c11032500c0401c265021081001034248142a40d0010f90b68000c00d0040c02c1c1258142080c0c841184d20070b00302d280056800501c1c020315196038420440c03156200b0307512010080d8100000848401038880440104040e00c50303404910b5940c00b404900a402884a00d41095242d406036002507803066004146c02e4003c084511f80341003079140079900c0e1140790344842c0643e4140a01001814404011740d081940c03c020030507111400b0f804c4a07030400580c0d020b0300d5844034001c1820250b1044a83c86503925000d5900c4002d00c2040455091780c040c0011280c0400507170101c42e0f580b00692288030f01641d105051400c5074180708d041c1201742440c42843c038801b5a65030042004000b20f01d41081351092033340f40b01e00366a2505090202042151645051054840d03803580301007600d030050b1516000d04509200780800101d0801c482c005c2c00d8 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 492056474 1250 492055224 492055231
    0x10020a050910020c01050a0c020a030210030f05060102060105030a02270405100c0203030c16060b122d06160203211f080303130303020d020d20030403050406120e0d0305 74
    0xc1d542d4041015000e900004824400020503103480d07041545080341101c040ca0711050032600508002e00c0000103031140b400307401e8071002d50f440c041103261154000100319680184818115407111004100d15140828031600044d01610184207103513140768100701c10207820510300c0112000204020500c04041160240c11069107000c0c0b10f100609071040381d5034041902e06940c2d4007000c10640e00010000b000300034056220b424042403d0b242c2c030b800039030200f007445201225a04440000564410b5045c10030891028600b84120070740c0c102c0e1011075030781a00519240c0c459009050030455a0b008005507124a440d942036416484006000c1c2000c6000c01d58020f02d86402c81603a4446800144004038140c2c3e032200011415680ea03100420020101200f0640500d5800c014420090f14540010441e0081e40400480c05442d025040310840c1040c200c403042e144424410b12002a40c0601100c04494031894142d00140310003601d44000c0c815111080c080303204403850750180ca80c041d003003e0310 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 492057724 1250 492056474 492056479
    0x30f030210060e07030e0c0a09050a140115030e0f0d090312030e0a02090c0d0921050f09150c101d070302061218060109050a0c09062010020a0509 64
    0x2814403101c2040c070644055009440c401c404060010f03400500c039074020214140c140e002c54032569001c02c040340d03644407103070007095071181c8031000c0007000c04142c0210b540a050007480301e0080c1d803400006810303030003000b80c0c644200340d1141d041d01410703d8104840500504038400759840440b911130050302c4078250307100c125442040b91117502c0791607010b072050495070480e101c0501007264007a030800c030a024004189010200382030042d4070054006d40b08078940140b007442200100c58034203810f201140480c0d400001000300410965070074006880c152051000d082c0d686440c1418a6103108100d4003450b00442001d108040d28801d01d60310b190131007102d190945201502c0c071013417000c031a519000c0034000690010742c00c11005070000d0780d07100d00d02da216880405d08446201c504021b24280502039102c07241c5252140c1c180690503019201e105050312584c00c0040c0c6881ca002c8003c0c02d811501d408002210410f18001d00c5c0ce88070030702558650103e4500c08566502c48000e024069801c0124841e0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 492058974 1250 492057724 492057733
    0x30f13170a110919050907081905010b0901120f02010e06030702100605010207060923030a030f0305061f03020901110319112b050c01020d06090b030c0901050d030e0a030f0302 77
    0x124205644000e010700d10700401d0000c0c07003004c2c2504401400f80980582d906118610001604000500030344512142d42c10800384070702d10070b044c51400c0d164840d140d903104800350001003202010720510019859405100c040880489000680da1803441915082d0400303000803c20000030f90101c0d9104458a401e202080469119001280d82d910b05000b168040382254cd03090090356a00d4528968210b070717404240c0d401d410243d000c04e0400500e81300840206031301192241426803d802143d600c48030940c1c030100450724030155603041881550002050607070005403010541d12034802102000011421a50b0350810303407000d44545044150980001200c0801841645a02048644c51180c001c00450348540624902d0300300c0040c1803c3c0001406070811201005180a0018080c005441c5400181051401408006551004481d41c2c801e41100c07401c1c1d40d20313940314804141501e40a03a81003d00d00c010b2f18040d5084101c2d030750900d034000c90002c800010484041064501d0a119070b0035503 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 492060224 1250 492058974 492059003
    0x21302091005210103020303030a200d0c0807050313320f010b030a0812070c0b070806010f0e150a1404030b070e03030c0a02060a21091205040602030f13170a 69
    0x31528003e003804025816001000420803944c51fa41013070860043c400710b4140101c0074840d079101035900031600c40384500c0e1600f0400300e91030f4219045a500c0350301410210300d180ba06004901070108141070040c04200040d007114000f07420000c040d540034a0b81c55410001450170550580c0d100c10050034402c166091500d0ba60540c1004203807000d919074040311003400d0055100003280c0c8101d00030440020890b20b80d80740b00100d001280441d000316420340b0303620364500705003000515201c0c1c1e21007264280511441c50140e00d49400c1060b42151003160046a00d50000c0b2004842e80ca450684003040e4000105010042c8074082e84100e00511080c0c4902c01302c68024028107480b4054072640c0600307a0070070f4071010050f060980042802510301e140c070045e040d41039410360f02c0321034106125960403682d0300c1e407040400000d02030030007005105052107824646001402540c1e4400d00345555110503000c9150f05540000e0b00c07904019060b101415810190741040840d03030361000f25015100824913500d038 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 492061474 1250 492060224 492060277
    0x30114091608032d07151104140f060903120a030b0f0105070611090604080609060a15030f02132c03040f0b0d02040909050307030311040308181813230a021302091005 73
    0x308c03001c44003c02200c58130218030f2810440c2d0403d185405581250b000c0100e02403942c0d007031262010f82103131001c44585034a48032a008007112800b071f2241d03024200d401c101c140c040c2e802406517054107038170210100e81c2c10300c2c84044902034000c06046c56000312000c58081003400012400a11aa480d08200c410680d920b030030500903100a10781030b21200603400070a00101d9042d1600420341400031749521072040108513220121414030841801502101c21b8201d035030141c025810680849100045003094103020303603180c18681034455203d101c4000070700c20010120a030180d40080a11a1081100d011103040a6440c0d50240e03100700d0020b4941103901210081445c161070583c0d070400d84990a00440e49581c0d09402c141c5042950f00001c9a544d500da44d000d40710146102d100880c2410354410f8240c50405a100010303510000c03400c0042004008801d00000e00c20304d00ca4048030071321411104000408002c0c0700740286c8030b41103e600003084d0b08150300800103025014041170b60000000d504041d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 492062724 1250 492061474 492061477
    0x60a020a02132f0a0507060b0604090903031a0303030703090f080a02030a02100e0c040203070c1209090b010905030616090b0c0c0f04020a02070e15030114091608032d071511 76
    0x1600300703e5050040440d003500c26000743c05041d11903040043e1a041c214001411a0002c5d406101c035aa00c503038540040542c1405207801ca400c1030030760b410f031041a540000b174030790100402e480c0805a0310ba8100044c07186000200f00d0480d00004010307590305800000075102d9104c900300001600c1901c2c44c0340a007a06510964001074205000341140341e850508000c065030001e030110b01080a601418804140501c501c031b0300f2a0082e8880b40c41251a0492100640d24120692410b0008494082006071808124a940302c1080d40545007106120f160030344400c2d02c95000b5526080011440d40004d030400590309440c41411940705c0690649401008107038802c43d507451005070094601000710816054480c1d0b0003112034421075001071711a40c00300b401c48a4030041c00000007124818000d45074028400d044131444082e100081e81820301c80003954038450110100e8140f0001c1c40c0144980f101048519046200144960750360481c1e0f08041140c210280702002c030303444c034222644030341d40310240 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 492063974 1250 492062724 492062801
    0x20d02300106020d1b050f0604020a060905091909082110081b0102070506120414030a05030c031e07080901063501020405040603140f03090f060a020a0213 68
    0x2402801e0844050f007044520103001044d00082d0218407000b6070026105100e12080b002d1f09000900c018503160042010298080d03001c1428400c1180c0240240e840764002c4075402440c28111003485039180100c4401020b2100006d09803040204420100d0b4643e250b108100b0b454120b003d801e03944904c8583d881100c0184100f804503071050140b0400c68125040d08100340a050042d1800b480c4e55201245281c8d00686d40ca000030280c00041108014189c5403041010b01c0780d100850a1210025028107240700150090400850110009031a40c060410034607140e0550b01ca90401820015406051024103590002803942440701c0480c04007008080e104c1c880b520802c2202520340d5029904800e040007202d84071007035400300400f0400e034507640103000080d40b20302081d4054a0302c1030300741401d28001000c0c1c007040e6041000140c086a607900c1849180f4541118815624400740d00700b40c0c81c051520000035000800580302c2100c004441c0e109442003955202144142120740c81a02000a14003 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 492065224 1250 492063974 492063977
    0xa2a0e0f15010e010806210c03011802011403360c030a0c050105070204270c080111040506280806030f0a05030d090c09020c0a02040e0312060f0301020d02300106 71
    0x222107440f4a5031094400c2a00b200f801740500e0500030302c0000d2103001000110010451354403040c0e00f00c1c3c25044c2407182c24a410180035001d035045c6441d60009080700e42001170181161070107c00300c1d00b5031980744100d003040007c1c0f9815020003100c1140b242d2034010403006900c0d407801034040b50800b9060100340c100c40d080d4081c10758891a418a40156131903002184180c0e04103581c0e5120251240302110b500944000303004c100e1009440602e001e501040c0146c02140040c1d0400d8850036000c1e400302e09540540340103c52103a01c03440400f2614014009400740d200801503c044030310300b0140c2114405026503401d41c00c0d036085c1000f45078415903954070f0036001400395004110b402c0e403201040d4031100d01c1e0303846004407404035070341c0d82c114070140d0308249411304490704884100030442c90305100d00d020803110f5001440c14070703120803a4414600d400a00355405170255218104080c5d40a504a034904410341d0b0b000c40d210303001d4100b035190b5000c405008040340329502060541c00d0091841d51f84c1207038900e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 492066474 1250 492065224 492065237
    0x60e06090c0a0212071a06060f19350a0204030b04020f0301091403130906050d030f03020f0a0306050f0105040b07080901090509070f1e020a2a0e0f1501 67
    0x41c9a01e0301080c1d40006140c80850254503940028940c200c001404124051040ea0300d904920039405d944442d80503100341d22400080108402c9a01c01d034054942d6000b04401c1c1c1100d00309152415202170f0101d400100f02010011200062020926280020a034070b07400c501c0280d60360100b05a0491045001c0500f00c00c606500003401460408649038084a010b4000b19102025942e100c10004050040030031a410100304410007a0005040c00000c108610b0709100861510000c9901e0b104400c0d4041c04110071100c03c008440e0290b0115000070700e0f600c0d0119900c0b148200014006d240350b0103a0752140d00060791104040d0b218a042e201510144146145040e0b926030300d102c10b5078450260a810300c0070204000480f5510804801c5c80342955071102a02d00c007900c60020041c4100d0510940740a25020215000b40d0303000030358a03550b9070f204054091a041e000418074915540d60001900d14444038030200381e0003203443c5098000e80703c900210340144c03038151001c1c01c8902d841410328002140e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 492067724 1250 492066474 492066481
    0x141c1e1a090706020f0a061e06150f0c02010e122a04110301030503030f0a060b07080c100507090b1804060303030b0102100b090604090305070f12020c09010302061b0f0f10060e0609 79
    0x46560003041081c204c100000c6c4128885118238040e108280e115189895940d1b400306001c1e90040c00800d0f642815203081600c001169002038003410b06104d00e140034602c03000503214950750412403103903038117043c0210341c0c41c0180c0155006090360029201d28000ea0904509142201d5001e0a0700c2c140c961040c091802c41d6200d052300ca1200c00014192501d41d512180c0004030b400520004121107800344980959404000c01540c3ca0b103100400c02c0c0140c1494101003101486d031041540701501c0704d0b20704c0309680d810360f25042191b10144094455129261850000815030150f0118401c02d60a80a0392028007418284d04212914030701a25045160b8030001021490180d0104100b43e10900780142041502e844030010088903490031100800c041c00c00e4460903804000c1c1020501c0110341c0c8120560450780820494081c1060342c3c3d2080717141b070004030302d03407441405500306203454041103456080010f41d64a079110400942c1d650700758940040400e00c1c5580c500c2c580d00c01c1d05c0141556a4a46 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 492068974 1250 492067724 492067733
    0xb0106050f1e07141b010e030f070b030403022b121e05010503060603031c0b0f0619142a10110301141c1e1a090706020f0a 54
    0x1480780500098a003402c0000040007211041440181406080140c0e01ca510a203000380090304200f4411420743d020071509072003d80001c0030007100890030f01e88801001040004030340b6004500151004901030804040b420f18004000f55100d01d01a038215020b00d81c2c04603a0440b00c60809000b00030030206060025003040c0245a03041d1014003201300010040007070f40001d400c07483d04210a81d00d0685800041040f441c0030040c107508208101c01462501641d844540c80030002005501e50007900da44c20420245c2c1d03041d0f0103520302c8202410080c1c2e240c20500140c611468404060b0b00800c0c1c0401c00410000381d03034000e072485407240000301d05502e02c6001c143c18608500000882d03c1d81309030007900b1080c40990041c4c034003610b4004080c6440303504005164144410559455000300210141d040040141990145031241c000f41801d00000001041c40b0040b40407500180034210102e02c1d00525148004049105000c43c01c00d8566060301d950003281c0761403441d140120f05d60f10042d004000314 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 492070224 1250 492068974 492068977
    0xe0c100807210e0f12040810050a0204050a0b0d0f0c080106031d01021c14040308180708010908040e09060402100e0f0307030303060e0f06060301030303270c060906020a0b010605 78
    0x50403400b11105000780c0c4049140140c0d0080150201541c000b080c5481050400700140141e280f07106502030b0a0600302038981c1e035035406407203401e0308490310f0398003042c41502076038121400703450003820a4038103d88400440d10f0641c4443d02144203e0b16020b0b40e0300303c1c2c1050b4402c90000310071079620b03d451340e4603008044014240c00e088800030407003140a449080c10003480241481607040000c21843c10307187c1034942c02c560703e9a28071024044460304210000398480200756001901f40714218154120b03400b500d260050907000416a90710b050111342c01e10039100040d00807582011282d4045d659207280e104d890b214181c0e0000d41190448030203020090184500d50300a00010342203021001c0c800c0b00003841c0980c0d690081d800310340d88580600c941408807103025885089540e5410040c03d010021500701d00c030521015040603955440005a03803202c84031a44099014244150b00036403506060942c01c07824071600000c24048540000c2190000c280c90b110603410000d42c1d0505e070f21300541580c0b81e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 492071474 1250 492070224 492070247
    0x302090402060f161113021303080a0c0b0103030503160f020a0803180a06060e1305030702060706060302220c020c0315100302120102090a050f0609041d100e0c100807 73
    0x30307807070074414418800d40c0090807140142c0181540081d85c2c4400c030520680031100c03441c540055004022200268101c03003208001c599009409607030700d20115104540f101c1421000030f00034501000000181980f040256000e84003940e00d18048110004080d0380c0c41e0445285500036802807001c803000b04010002039036001c0044414580d0301c81e03601416900308544041e007100d9907961a001800800c003101030250b40806c0500140031b01403101c2e20b805559019901d0000e00ca1a0b00240c20b00802410742c02c400c00841e4042e03d007042160183c40c0040c030304c00d8641031038600c80f031414004a0005100286211a0100241c050250951110142c450903c802442940640c0e9084000801078445991743c3c003000603260001a01c1f140c0a204224405085500c15441228804403074000f50340c4000481d68501d6048a0000f001d030314a00c1021044050740c10618101c0c0100e401c3c8141580a0f1382180c01e52640640c2680c2d01c0d6202042048803030201c14044500046500c00020074440c0211104001c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 492072724 1250 492071474 492071497
    0x20613051603031106010503060c03010e19050109020c0d0203031b0d1407050a1805010926340f05011409100309030e010c080313030e0316061107030209040206 70
    0x942840006502160202d9008500082c0304030340b44102d00c01c061100c0c0b80501001c501410740c0341003072540c4040302d00041c0a03054440410102064240d0f15420f0160450b0b0b554801c10f1000b5a55044030a000350095100c040c518040d0342e583ca01c41c0e5102000301d0f4801c00928085590b0b000024040d4134068000d10030f02c0180c242e6a1030309580292041d114075204000035603802c0c1d45e90f800141c004110022003407070340844031a0664140596a0007034540010f880501142201410b030550005080240601d196826801034040c002405010011416124a190250321510300b0a41003070401c114000c0c440c08003030030402c82081c02190310a41d907020200c416140d203103041080d0540001e044481280c0342d440465514201001055001818200049401d00b04241d032403c10343c44da11010710004104040400200408008145c050b0000444012002d4225030a00da40c40011140b2484203014040101c0d04403160703001440300000e0315030705484d4050105091303a15550309000180e008201401b1 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 492073974 1250 492072724 492072733
    0x90b183408010f0e0d030522061407090f0602120a0f0525060b03010b0102060411011701090608011107120813021201050a051503070b1303050f010917040602061305 72
    0xc0d240d0001d01804902c01290f1030002038200e00c407010580341040d1503e0040030705042c0000c004100c1280c64050f00700e0014428101c030010102e141001c0109070754000c002d00d440c0140140a0000e42c0100c5440964a641514000b00e64032540207983d190012160030210300e40800c050301040d44100101c040510b0307107091040c10a5140200c5d034120103583c40c00c80d006142103100c18020700440e0701540c111410194020032000222800007500c804004101500420000f501c409680c2d01c211303031503071100b900381c1c10b5a101943c45880c0f1001501461003255000e40c00c0c5644546603a40e10021202c0b4107070300000340701c2600c000703039002e41d0040c070024808401c1c80c031811064009a00c81401000260301140000905450205c0040044403401b41040e03406a42c40b410301c2009031000140c20055031000c9251030b07101c1d41410341000000c400b58000070f10500402c1c4011504010540004000030f103d00d0311011102e02d002803030419402039108100040e80244040b41d2000381400d11340f60654010410346 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 492075224 1250 492073974 492073979
    0x40c1107170717011a01090311122a1905010203030f0601180803070308072a021216030c0e100501030903170c090a0e0402030a0305030a060306090b1834 67
    0x8441109070f4400030031507035154040c02040d0705a03d5000002a8006d00f07042c8006402c61f00c8d81c080781d4102c04d0354a40101c4149034100d141500800220001c100000e9960500c0b01c20041140e1060310307140b400c240500c00c041e4000b04403401305012002600c406034011825a91a04603814402a01510003030511000b080c00844080c0031401e0f84018000300e8004681e901180d10b001080610010700e070304100505500e417866030310044c00b002d6501622105a00750050440d00000300e400791a02c0d4a0340d80d41c45501402d0b1703541103283c01024100c0e4040c14182540316503800005030080d03001c40c2c4240c1030b5080c04005012030341c003d0307000020807402071500801441d084c0c5d044e09036a08060310003c600b010302090b210218a010010f90001d07021000928015051070f901195503604050b2004061000200008034900035940c0100b00841d004a028081641903090406103c60f044c1e0b05180c00000b403207108101c0c01c0300003036940ea40e20400203800143d10b8140c0740020a928000502600f00300c06807900 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 492076474 1250 492075224 492075239
    0x1e0307180f0e060108070f0c020a0b0309160902030403020705010f021603080414010509030a03080c0f0a050d0b03210a050f030c0309010621030c060204050d11040c11071707 76
    0xd0801604000020303a44490400b6016a032408004010398108403244040088040c1d110308500d100f104182064010341c2c500303200140c0b028801c0e0b0001482007030040f0030044030840004820008001842607070500645a41411041e803004031400742c05a4412a0708000c1d55100320214000c00d10381e40b06640e07440d000b01c020540c0c60303401c0307a0003034455040101e000d00c0303860100c41c601d048100c001d0a2007450a40c0b40c00c0400d45800d4240d070054240109400040c20074440318048822400005514035951600c108010300540c0101040c8100180381400400250500191000031155600b002c4410201d05a070400241d5001c660340400304141030125460345000310b40554090800c40031600e44034602011540e00310f41d01035001345498481420b40b0f204a64000220f20f9106070540307001070120145040034000382c0f10703642c000790300b01003c0300009041c028050000d02c5042c01c00c076030a101c0b103105000101d42100e520a81042c50381c10028042000d1031420094045070821780307081d24030700f50f42e8049 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 492077724 1250 492076474 492076517
    0x3020609130f1407170f060a030507060207030512040513110f04081c020102210a09080c01020720060a0318020a08100f0c050306011815050706050109021e0307 70
    0x10b20b203005549692245a074240328255050744580540f60032000321016203108050100c000d0103440340e40c0c03d5030004c500c0b140c03211320b40c00c005550080115942c05d5a181e070029651084c0b0702c416900d81c0a498207444000306090110360840d1402000c0784018540410500020b2410900308030301204100a1241403a000e1400b0f80010700b2074002501c082041228000b520300c1c8914151002c591041121440710005c000000390322102c88111740315039965400d080c200900505038060030130000403078408a4090150018a141807103038254414400a020700100800541d036601d80d0310484c20b1104042c84c1d031081e40940c42c882c845c01e900d8141d00143c0e0300403a500d14034580000341c40f908140d0714100c500d0a14024071129203051300c03003001012031030040285180009001c89041108013001d940071015242c0e42c0001424948115601503080340d5400750290380702440480b03106003400000190700d0203e00c00c0d00d200c8402d51680105c9003c104080380856440200782c50240003554803680c000b06410701 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 492078974 1250 492077724 492077741
    0x403090311010201291804050304150903050618011803051e120a0603020118080604080309010e1506010e0d0503040303110f06040b0a0501050d05070e090304091e05010b070c0302060913 81
    0x10b40400c202145d0700c188201501403509150384880ba0b0824403000581c000200c074129050700c002d08401d0044d000040303400000d154070145c0207109840c144013200c0d4071103512942d05600c01c00204042c1c17542282411400c1016500580490b2052100019240001c4000c03e003c04e0040c0b081c5162a0010000000010050310003800326559020180304558015152010031024201d1400e202490525a50f645001c0140001c1140f080070011507201c0c4070940082e46404034030b00585149114039182002e10500c2180d4403400038040003030f820103030700707280308101c160030741100c041c51400b41140c41c00e9401034a803480000c8544520400c603c0b1408041c4195400385201e140c41010760b091807003150301a520182c102da8440c20660b580800042c1001502c001255815040e42c40f1598804160074198003031a840040c0d0181024181c0c0c00600400c03600e5184c1141401c000c21442e40c0f20003d6080c03038002c02c0b6000300b203641039500620261400f90050090f5020040031100e92020f46481d00b4207072203006 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 492080224 1250 492078974 492079031
    0x9050a1104060b07080d0c050f03090c0108060109061205090307021c06320c090312070209090d1b021f08181c081b0406180506030403090311010201 65
    0x200000540e00d042d0240900800c143d6980c0341c180015a110642680b2811062100c91079581c041c114019000300242c030029254406100e8580c50b0510700242c507103071154620b60000e10110001900b560141140c14151040da5881c0c60f071103208164220010038024281244610080c800b280050352403c4440d407801a003450400741d003a03800d107080d42c140c1b40030684468120800c00c0d42d0f0400748440c540500a01076246168104070344810485005138032403518210b030507015020518007a0481d080003020140c3c07081e142404540e0b100c500040e250108202d85000250200c078194101014642c41456098001403c4401110100300710b503600c0c5000d9001034020a10380c600b00100f41b4450b21300c000780c0c40d06c600d0150288808007400848003404807040344c801c0c07200c140081141c9407400ca040c810201c818441c40b41d980c03915800047d01c0160f034241e040361104c2d810b64011074203040c4002542d0181da410745642e9819402c60f51003080045a440c04941190368810b075000ca0280e09440541d4111540d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 492081474 1250 492080224 492080243
    0x70b0612030d11301312120e060c0a0e03190b040305120a0504050f0f03031810060b0714010e030a27182d020a1e030510060e091909050a 60
    0x2d02d00c0c4c400d201e00010110b118460820030120045003e04030001c0c0301c1201850102800c12000412800500b00c184441c2c0640c403400e010030500e0000000107148480440d1900030064030248101030395012040b00c02e89500380c40752038801c0054002611550014030030704145043c1044034049150034a0102c81e08003035583c50700b0034041032150501002c0c8041c40e42a01070070302c0d85620308490f940c3e440041e01d1008200a1901c08140c441020f0011440d0780070440000d000d11781e81c41540c0c04482d08103100607100c45115040704880310b841441011040e20400c0c02440c03c2981800007a100c0345440802245ca800c40d001e9081c1c04e40b61020001405400201400d450140300f02c4203d000312030903114101e498580700010b07003036003c0800d281103000b5a000300380940d50720700d2500c04440f0410052601c08001040003107542c241c58054000c1480b507542c00300c2d607421459039500210740c4542d11f00240c80d00402158040fa1442c0561981e000b4060140c20001c43e004486a0707440d4502840284180c41c0c6100 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 492082724 1250 492081474 492081547
    0xc171203040b0f060d21030b060408010501090b090f060103181208010612020405010903291008061005090a240f080d02240a060515070b0612030d11 65
    0x488483d590005010f0f40d80341c0c0b14030b5003030350b8100800c13a144102401e003200d06000c90094902c25008040107000281c80540c580d0381e1030302c000b4042c1c042030103401660380c03d104042059040562900c0c2c81848600d84840c000d860b1000150001d002000c0385030301c1d801d08083c6480c0418140e01c581e100940d91980c51300150342c588400203001b90b000441c24000d1600412042107641c4e80000071205894114105c21325203c0e03201c2981d219010000b0b84140003201d81001c004003082d812542d00304a130301341c00945040c1c3c0d03113006401ea0322000d00d004490340005a000071551200460f07210201c024090340b0b150505a120030507071854030090f03520015080c0040413052101a400f0b00030310b00c501c28540010b241a01215546e841f044800780900c003211401c2e0710024003116100d0700403c0040401404091030b42c1c1120075281e195510040c4d0a55644140002007942c85c1400d645540d1210b600300055803c00403089904c00141000400016440ca03080c450030322541e030400c01000c1a550885002d014101 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 492083974 1250 492082724 492082741
    0xb040902100c061526030301050307050114040e07080108010f020304020612040c0905090c011107080307121b3e12030405040203070801080f06040201020a060e1f06140a030c171203040b 81
    0x60071042c400179103400c140010000303500c0024101701640c0c4c090134401e2080c01a40030076812401580e02c9000d000b00a9014041401d03009a011816914071034020b108000c1c030b4014036000e03440156802504500e00704526161002c140c034020360803500c0f415035004400e58400c090815660141d628191641102d80c00c0210366811107228145900b1900140400510342900c031502c0e40030b08600600007d4220b09100c3e0500c0c861251304007101140040460428403d0405c4c040d060503950010300040315914240d90340050610300c80d050180d108801d1580c000002050000c42c1460b07110b0014144414000030a11b41c0d1a80081c2d8405c0c1100d980300c0c2c5040d803500380b619207010065513101c0340c507800407000e010240c0d030301007081d00d842ca03003000e008036051680c0400d0310701d0554564003010301540c0f4402d40e07400c1082c864115004071400308402d803200c24990390411050310501d210051200c40c0d40b11040182c8910b0b5901c603803108003070506407035808915890101035984200c50032220303440721600f008000e0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 492085224 1250 492083974 492084029
    0x5010213051909020f191e051608090a05091f0f080c060a1b0f0314090a1e0509090a0b0f1608060a05031b040b040902100c0615 56
    0x1e0500701c802070007a08600c034903000000141d009507a90190001441d00e804031682d4200d41003040310102c0c061404100b003400500300600c0118030b41044800700803141c1001d2040050311105012540e4100003114140c4e10000f132036010000c403c0d00050030700000142c070303a02c1e104100d100d964030180021045650040940c84402c0c8c5420541302410226401d1013100c2001411a011141c00e0301c00c550345450b030741e20a032080643e080c04c4440e0018102241c50030040c06020001700e080c8251101424041d004000d50405c0c05028121a00114980410441107107401d02060381418181d550a1816486801141c40d03104200ea208080d070344480d8400c42007010706500f6a030701000300810b808460900810013403064880c101a1000c11500b0008201c45a03124400c20004041c0207040300d0307030354441a030010308a450001e0510322071442d09a60481a081a0254800700c81e4028008501400c104605945030034403030209072100c075950f03542001c403241406820406045d59002c80c00c03040c0700c0b400344030010 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 492086330 1106 492085224 492085229
    0xe040308151201150504060605070f0620070506011a042310090e090a020d03080c04122a0305280506040b0709080d0206070e040e060405010213 63
    0x1407010560044c1819100350040d036149542c0c80041100300c4d0b0f4035200303110100701d0070003103c0005005400420b40c500e1040c000042c01725002d01690f40c0f0340c00d01685010382c440700003800034140142040442c0c01445044403040d0540740707500700400c440c011440b0300c440c0404044210304c2003100500d0358074803c94024054a6101c00d42d4a00281a10303d94800d070052440f12a021503a54807020a50081c8242c02401e821a0700032159000c80e00040300030001140054180408503908414400203080d0600511b4400fa0080004800503a035118100702d85550510564040002034408130700c601c001c035040010210501816050713a42a0381c40b14100401e1800b0f598100420024090702e06802074446554a17000c1644500800d90746004001c2c0350030140e4465000a501d140c802c455107000c20b031f8054804120314858610142ca00081500c04627026500801c0c035980010650390000c00 = true := by decide +kernel

theorem cover : BRFrame.Cov 491906474 492086330 := by
  have h0 := BRFrame.cov_init 491906474
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491906474 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 491906474 ≤ n) (h2 : n < 492086330) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
