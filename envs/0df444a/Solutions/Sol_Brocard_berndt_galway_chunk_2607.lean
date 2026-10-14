-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2607
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:12:24.247276+00:00
-- url     : https://prove2.me/submissions/3a846da8-2d9b-44c1-a8fe-3fb8d1c66646

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 468705035 ≤ n < 468884892 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 468706285 1250 468705035 468705037
    0xf08070f031e0302010207060c0e0103050f04080a1b02042d1b08190c021e01020c2119090303110d02060403050c0a0f050a05070e01062c06070309170f03 67
    0x550310802d614a0220882094401e604031241507511110401030080900c000030100651403800a0100e403800d40464401022251950711591740101500d20b000582e0808441b0400e0200d00c1800c038047d1101c2500040e6211301881d0b1402c2e54410088030421320404913070340207805841c01a0311441c03400c1380c15000324030711041441e0018502c1c03e214416031074503c4201c0765031111030a004901441e028a0000c510b0303000c50201d494440030010403410b040c802002d04d08174400c4100101d2240c0c450807514640980014040d241c8403002c0c00114100074014400070307039195040e45500c0004040040500404d42c0014810b50342e858200d0090402c502030500c041d56031a00540040e00340840458482812982004001042035000031449491415480c1c420343c0d0341004074003156140a50103001c0385c484240740c0b5090483d9041e036541140e00c403000c03180c00a8449400c1c002d00000c201d800300307113409464402c020030159100e030380c40e060b529151a80030100310460160610701608804011562510004 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 468707535 1250 468706285 468706313
    0xb040f05010c0804092d140f070c0f210e09070810080f010b1018030b04050a0b01060e03010c05040b07030e13050c180d1203091b0f08070f03 62
    0x1c02c144210050900b4050b03a41c4c01142d000e40303c80e900303050314060000c12482d541004245010410ba041d1205441a0310680380050001070001226000248543d08004078a54021045080c00f0a9850b82c58803501e0a80c440d07048196094480d401c910b481c806c07404612601c030803402d841d00e2070111103040001407014401030110000c0201d090045142501000529802010201c0440300380d84107145c0c055002c1c001c0d64403194807600e048102c844040e405014136032203d801e01a8000555411aa24038440711000350050740d03644101c00002000400a8000501030012621601c1c0011003400c109420764103c4820f503000c01034203000400c01201340780159001e665050a0088040b05480041030307022290a81418040f414441840503000c99a0300500c1440204841180c2100044081c80640038a220000745003a50602c441c01000d88640d100c1c1d00824824034000a2604014401042c1011f051304025484803000200308420b0030200000b60041c01034000104600749551180d40c0088219 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 468708785 1250 468707535 468707537
    0x7050d0503041515170d030f140103081b030403060e0c0406060206010902180402030705070c0803091003020703110601080601051801080a060902060d05040f020f030613031808030316090b040f0501 86
    0x40c00c04070700200072101207070041e20000401071704880c25140c4890340e4040b820810380100b840c14495200c8400326002d141100010459071403056440e40d40e41515551003032031342c030545c5000da10048841c0801840100300843c003072036000c184081f2001180d800c0820000009104600c1c10300204541a00030039450b04440428900580314025101114400c2010302c02469006100100700122aa049000390201d6400b61940c825015202c549143c0d40c1d104a501c4554082400060491441d02c00d800400d9502e101385418441e51068080d10343c503140c2d080e04400010b802c000e0050115040c0490024980c1d0750304c0103842111b5242c01c1d80d103a1284071850f0050300041d10789803c2819500e9400c11680c01741101c0c0c108206c0c80c500703420a07944d012840003040348180c1403c1642d0301c03e4a00061241d000d420070040e111451819030b5004c0c0c840950900b440050482503a200003150038052026602c61441d11100d40d4040c60b4800d4010310051003600b1003142c01741e0500040c01440500c1b1005401e403142 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 468710035 1250 468708785 468708791
    0x190201030b010c0b090607031b0c0213060504020a1e0f14031e01060c021f1b02040f09030c061b080a050928020a150507020415030203010203070507050d05030415 71
    0x1140700100c40075100440041d00c0140d403501030020403100042c585200d80b1082d5410008600703441e90136400da01e09001c1000008072441040405460a07601c0369661074003000300000c84ca0703a9100450242d0f00002d00100100303114002d1403107407010680520010510700e00d4500208021114050000c4010401c1024a240040002010b0110f0024034040c600d5444c80e5080d071540c1c0da200010300500050008038010081c038440280c0e0400507030003021140d200303600c61190740300ca54121400c0d0b00480c0c11059a01070b40f10b002440d20850031b84910722071940a50303202c3c2d0b080030150400b10309580810249070440d0807964000900b40358010065900010320b0301c0301250644410815a2611450b060300c0c0180f0100d00038030200241c900c0e032403e40030b0761003a245070204954079241008606103140004c408030354204642c10052400368070841001b0383e406a0540d00c0307500c03600864220f07002220a103010601c0020544103000c02000b5050200780d25103006451454030b46c1e190703001303401504400403000707071 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 468711285 1250 468710035 468710051
    0x50405061b0a2a0509040803070c0302010b060c071706100612090b16120b09070e010212040e0609010b03040206090d0f0f030504140906030309090c1309020306010801050319020103 79
    0x1041c0302c110022604455082d0200c032254600352444054503a9020340c640c0640700005550801001032403050f50003803883c5003036540e007000c140d400c030742d004800320300315541c80b20703242c10326500c000c090b01080807408000c3c90050304281000d040c0728076000742d0450560080b0100107480c8805034500050b5019850400303150700c000e4100314060059054000c284800720300030400d1002121000c0502c843c69030743e07449448600c0381d982e0300031200c01c81940d50704510910b000172a20340c0602c0f0562030844040c41100c3c001d0101d10b819000300e4205802c01c076001e2855606000c510728092a001d805005624410752450800790300003440c510a440146010716040758118080c0260700c0110110990407118000c3c00c508640340040c660360040c00b481081c2d0324400301c440f042d0f017410720245214010180c01140341590030350412107640d0000300500c01412040010b900c00e061880b900d0300090040040142e00c908141d000035000c1c500581081d8001e034003003884404099410101001419020300300025180307 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 468712535 1250 468711285 468711337
    0x8030310170a0f0f08211302010c08090a03050106090203010503070803040e220f1a150312071e1101020106140112052a070210020601030f0b07020304170c0a0605040506 74
    0x2e40702c0d01e010780170305408a0b00501003800d0304061a207940c06a10140c420b0350f14400c107103040340301544011717001409000d040e1000628a9000b4020b0000c024420101c140d541e960306800e64002d034000442c0341f5004401001a8102040316001a03c1200061404c00c1d0030542000c24000f8010710f06c2c4108443c9c511900482c0000d520b40c9010150070914040040c3d04038140403d00607140c10041264a52080000b02207802c1c2003150506100001d02070071260000800c1d0032100d400442c1d0644d041e00d0403040c15440e0b08500840100524401d03245003c4444100b0006401c50704d0581c0491801220701c074580c051680c0c41480c3c4000d000083c07100080503124686c02600f0109265040c1d0b03200c0800820b070020600400d400380c0074285c03007240c001608511207138080b0f840303800a1000901c1d85040b0185100042c0c084c4c0c0c1071036030100b100c1c4101e030b0034a43d807000249504001c41c0c2c0522501c0d0000d00c0040c2450070000889000741030700d410500d243c40d1500001c202c1c03d100744d0781c3c5800e510b884545491054 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 468713785 1250 468712535 468712553
    0x301150f0e06181e030a0305371101020306130e1011070c05030a0305030705031f0e2a180f12030c240103020f0d0c08030310170a0f 58
    0xa500c090051625050001001440007094084640c40780c4241c4c107020101c2d8030348404440b03120101401501907000d00d55415502a04803500b014040110501d5011080c04800960403023801085607101442e03605032405842c4040407038100c622a4010401c010f0a516244042154205c3c030b800001560800c54941904181d0400056140786080c1262000100d18450113000b04600510340341201c40c0e650010540d540c0300038100200400e0080c030000310704501900140da80801d080907010032807102d10f5501000241ca03031f08859401450b0300140300d20750298201c1800c50700c0e0143d0f400f04040040f41e40004c5117004900c17100e0540641281814a5034a440c2d40f8200f160384c01400c076801054000d69a0313512500200304800d83d42c40303007141c240c8080c002000070840140348a91500300d079900310740a01101c2d01400c0e8180380c01c0495503c02000145c580e9014000821406000e50740b60300304140402c0d001409544690320130520302075001c1c0c5c0c0c001c000c0b4450000b0341d48442086188c1c1500d1030100c40d1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 468715035 1250 468713785 468713807
    0x609030114010b03100906050307031b15021f090c050909010b060310150912060f0207050a050a0605090304051e0f19140d11040b0316140a06050301150f 67
    0x81d400260000585800c0c002d000d540070f1700d040c000c258900da841e00e06a0003251000c4c4141541688035020410125940d10542c100490410050480c100e032210b880d091141c50082c003885c0140e106030408001d5581c844162401002c0740fa200f80300364281910f4503100300802d400303000c4c844c0d900c841c00700b42e00190035030114403006405040e691320782c41c1849800201031920310501c0c40c1c110400081482880c4140c000d00140d030034442031010025a1a26a54001c0c00088006031810f5400c1144401144080010700b6411340b003007006200c41c0d42d192601e0b60a0310b901030320b903500660041c8014401c0c0d6850164185070402c1030f1501100c1c07066000f0008050007200ea002c550015a48048050050b0048c09520140d59007070017000e07205205070091001e0310014a01c040c1c030f102804d6400185e00d24158200e540c9058000f42110f41130200b103104084039503a2a0f1103047d605504c021600042d0401c0b2017450000d001c00d04201d400c661614035a649141c1d01a09481c2c02c0110325000c810585010f0058288 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 468716285 1250 468715035 468715061
    0xf0102030c0111030f01150801060c0804030206040e06180610120b09091006120c0b0307090302060c100509010b0117100e0a1d0a02060a140d050f0708090309010e06090301 75
    0xc0185814080b2800e0703842500c60508001e00c0e00000f03e20340047e801d90030000030702595162032583ca0010100c507448081c210071140404c0411001026030707a0500900050001d203208070426041490411091016031034610b000340d81c1c00b10801c43c45030340c3c080e200c026000c441c0c18144915804e0102c40c50040c0070303000019901108081c1403201c04800000e480e01c10500e56001045201e03220040c40c0c1d00103142da2001849542c1d9603c05100f80021400a1a0824800d041c0071340382503200d90000e01590030460860400c2e034002100d40c54004400c0c000c1c243c0082e48031000300302400b02c04000a003900071a244845e200c840035400315944000c109074404c000c00007070056294609150000b800035208030b045020810301c2100c0d90032824100410403d05842e4018041850004400400c0d21406120703100860400c41c144250000d4454500503184070b6030002016004600d050394015003408000f52618410b54000c2c001c101c160303600714400801c112000c496060302c82ca20301e800240034000c010040b42d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 468717535 1250 468716285 468716291
    0x5031e1b040e061602060907080a020d051c180609120221030c0102040630150302030102070609121b0605180a0c03120212091513230d0b04020f0102030c01 68
    0xc969000c4c21200030103031003026800c3e5009900d44d056566521000c078082d00c4c60720742000c1140c13401803904c5801c20414520030300235100b550490380c4945141049294504010038282e0700883c2c8100c40302c40402c1c010b41010f080c549101820940031580008801e80000c0c080c003418a00c410700504c10800c2c440e1740200c900c0403a82d0f04e1000c0c1131824040d400c103120710344c0454003000d08041403221030480c0e40b95403012131074103542510140034100c020340b1a400d1100c0f03104005600200168400780000c001c854054075003c154070200b49006a80103902c440c400702000400138140c088280080102904682c0042000c0707400e446044541c2c6550741e180490288904c01c15081c00100f015480d506411240120404c0465002e441e42c10b0344c440e804100c40204011040005805914100003456070385610b003890702e8103141482c04071410740c180e290410300951103401c04041d02c0782c0800704072021800c405d43c6c1c2c8070800f19036aa101150410003a01c02032040102c402103855a1b4400c0040e1403030801418028 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 468718785 1250 468717535 468717541
    0x17030903030f040305060703050105130f0b0d08041d10060f0203040e0f1603050c160c2c100b0307030504060b040204060f030e010e0607050703050408061005031e1b040e06 75
    0x18010b680c000c1c03104a409008900000d01024001d116050494802074050410520400c106500408941031002c0c210303940c0325542552034840840c41e6406511520004e65a07504020f01402048400f101c50707604070b8808410489807581480c03446044521508000011007500c900030790660040d42c00211507072a14404115102200c520154041c60007a00003000c44600301208074251401107070b0904402400308405000f0300820102c2d120800d028050215185850707081c507a2255400c108050303070b640c07110f841c5407014108035401e894001c0d021100560041e450400100400c1c08028640c00a040e5079900040030f20240b40c01048054070020000c56449440d00d00141030100c0e40300802c00000c1c6000c00030182715405115941d010006900200300c1d03903031016800c1755203601550080301000028840012030480c104001d502440340584141d6140b82054241032401c5d121a841d498240c181140f00e01e180400460203071420b03070301d100c24440750644050204001e045031000240c01032050f2010 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 468720035 1250 468718785 468718807
    0x2105071802090f040c3e0607020f0604050a0605250305011508010308040e071107150f020d1d030f101505030601140607110301090c0314030f041703090303 68
    0x1401c01e1807040303e000b06902c43d62818801116464801c10001c0b036418a98064020010030b60342000c3c410707003043e20005006062440501201003490a00503074461410301c01255010302c0a103541100f003100400340c03403030144c852982d922000d610151206a4800110707440044440f0b64460180440d40340200b0724400260080c02028248038048030208110801e084641c0b0071400c3c6c504903070700306441d47e0030103003002110882c00034040c12650501111038165200c079101405014000d02c0314120207600031410013000351400922102502c1190050a00c0c540002c4c0c12120500c07105104040c60215014040080380c60030008015801d080d10821300381500200e03480d0449003d480000701e0f454403281e9200141503a82d8028000c02c0c00000362a00118103609150010380745684c00b034240307446142da2082c0420300b141d0440c10309580740c10490506000748280030b8403802c400304050008500d00b170400d01c02c128080c0128029070401b1950580b00c9500c41038104103031015024000c040d40d9862218100c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 468721285 1250 468720035 468720037
    0x20307140316020c031b040c232106130c0905060708030105030d0e030712080d0513050105101202090a09120504080d081b090a090c03020c0105102105071802 69
    0x1441000503c160010350303450303050208040605000c1110307a2004e111b24641040094003000200703400300803c08000c4c0b1110001c00359042203049482c01c1c525a85c4205088108441541c20440c0d0480b9401c4400d01881c0d48072005000c0c00401c401070b0002c1d51608020044800d0003003684003503840f08000c00c402003840032140c0154100e403021411030b41d640005440aa400d0540001b0310b03545038010322010030040013031840c0802c07441d03c00c001d284d14200f0804584800c481050f14440c22541f450414002013107001d11030b25070061070315a8900b50061808811700519512404c000307000303202c100d02061021500740c2100f00311541c0172445d0840400c8403c4020a90b0300f040c0f1901c5214817500d80c0c801038a80c000c080c468000c042e00c0e0f440c401002c5040b0409003103035000101c41c5800404500c00019a6102c6104da10b502e0000f6540241e910340c5c800010a0940c3c0700a420030030452100700040164038030384049516407424a1801d070301c1c44020383c204070342007020680c0581000801070f020b00c6003886c0720358 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 468722535 1250 468721285 468721321
    0x4020d05060c13050f03060c0318030a0815150a050a05070b090c090f070509040e1507020303010f05030f0a12051b060f010803090307050609040b040f0b2e030203071403 74
    0x410083d0405680d10100101e80188146958064100401148181c0710601c011980312000144c1e1a400c6064a10f005107503a002084440020b1110002d2009181c81c548603042d220104441d108001c2046c112036048034802e10620380140b1400103000ba103080c1c0200b05944ca52038211020381203500e03205600302d84a411800045218a00d2500052681002902c0c0c45000c2d4205a94a0741400450424400180300c0c100388072816100e207604041008030010200d41c80751156074013864695141c400c550806e480d50340c00c81803094000030100700d10041d000401e600d8150b004000c0c994000016a8292454441c07038845040301240c181c28072291401c00507520b070007061800f20340300c5181e030780f082c4070f580701d0180d0101541d054000100401091401034040c000c10030300103200240c001c84080002e0102c4400c046080340d4141c0302d0901c2c112a1405d926400100da00c1d400c2940c0c8481c0760442c80e490403030381030004031080c958040007141420781f10b056855010080c0191465881c206403801010b0000c81e2 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 468723785 1250 468722535 468722557
    0x5060a0b03030a080402041109040c1701060c020f090a02040b0d0219030b1008070201021c05090c0109030f03120f05180d020c18041502030117060901060f090504020d05060c 76
    0x60400803aa0800104541120165a80b0b5200315100c5030308005c054a0542c1f07107410446003d1180c298240c0c1c81c0d21504400c414652600c40a14101c10304501c0c0704101648034405111030782d505200541c440300e001002006048568243e0740c1e1759519020000d00498011011100b0085018508013000b54020425603c121491040c0001b030150f00f102900d0410b0700090f0000303110400c696002e03009075241c9030028024000981400007d13048200d8070910004410415500c4406100d03401e42d0074442194014000e2810410850854640003442265a80002d0801081e0040035020b12004c4d400700c1207a86c0351440910143c109420000e180080c1a00c03602c000c2e00801724040c0d8558000200d043c401c1354081d084000c4510310040070800c28000810580f0100ba0225480915007403e100440c0a041040c0b4130007088604403545500d0241d00400381c440c2d41e807400ea01802400300d5884c6010481d10000c00208107981c0da4804640c50030361441c40244680318020501c200542d04c00081c1c6204410 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 468725035 1250 468723785 468723791
    0x181b060d020720241803060703061a03070503160c0f03050a0e03010501210501020c010c0203040f270216060f0608010f060e0c030727090e034305060a 66
    0x50a003008480702d8100801c0b452081940c40c02c480004000005d84988403120400000080c41c5074086802c1c803804441c10000290b5504040c032101d5440c3c5849000d21100028040c214505124040d0981c8005811a4030040d00c8540104005208544403041d0135070000200b1088070051801418075001000c1030701c085240c0e40041841d03424144944c3d030494000c080c4801c040c0403141031110005080c45425500e0395020841e0310000710342400b4003a6600400d9000b19901c6151032503542098203075810010216203100305951141250b10406d041e84151010010f9850441d0388210301300d4800c0000050242e81070009495075000d4551050080300c076400001c0c031061648190540c00c85480d0b02170305c460780c110140401c2c18281c814024580c441c9250034444c5900c2c40003030112602070640d010b41030200101043c140444045401140001c141440c001e41c10140002c43c411415118500411000c14030080145071100019031448400303400d01c2e056903000f0f00b103420003079100c9008880918449007 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 468726285 1250 468725035 468725093
    0x4170f190f14010b1005090f040b04060b0313051912080c07230f070e0f0c040b0c160f030203031b011104080a05010509070518070c2108181b060d0207 66
    0x1006c0c0080702e4403484001c15031441d0011810030071000704419002190070658846003c29096034440c0154042d203107603207001e05e1010382480c04074500f0842c5001500031441c01140780002450300344880d2442c0055043c0b014480d07a40e0f5108527101d005d040005000b003c0d4194031400d1078aa0440030351062100d18003a54005001c407081640ea0f500948261250191401c00154070080660ba006401c000703404046032606a803400741246230b0700016242052904441d80204000c2c0002e100c400007840d1175140b50302042d2445d00041e48078040c0011806207100041c040c603070061000c1d80100480c3c24191419504d1310b88460b1b0b84c59036a00806c20464980d860203021031848003000401c502120801400071031500600030749480b604d04050201c3d8240315480da0400001007121056451243c2c0c0b00e040f01d01c100e003d9003401049540040c0c03000450381107821820561203c003090782141441940f9071500100720032804203c003803181c01007071101c1b544007192340340402c6141440c00216650138255049814 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 468727535 1250 468726285 468726287
    0x310050108071403210a081303050409020904060f1401030e03180616060504030c0203060709050913050a050303010306020715060605040315020d050c04170f190f14010b10 75
    0x10028010241e042d445041c0811056050035103c0c092240054160786032803205204441720030b5024854021820300106040400d5a44071030003d51000340c001c29016080c0d00307600c01078400d2003a80250300c00c40303800207100409510744ea000b0300010454294080908c1d5039680606502c01440c1200c580043d041c49804034210300000103468804004030355608800540c4010009140e100030103041403513411040000108038203200e01c0b445680a61600c80555030340d44105030034054010b0882040c00a801d800740440e0700d403902c4c2241d2183d41d28501c05528562070034140d01d00703a00c4140003806480000004010400560041c0c2881446002c4080c8105c00e03124585065400706d0040e130b800607405200410118400305250448075503003000041c1341c0540300310a0342c02e58034100c4400c410107400007410041841c42821a80c140000000581014003156220701c0d111076603010f040b00340b0201200c1c44400c0c401411400890181d1003400d914200030f0315a01d581c007030f1642c12941c41c495150781540f80882 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 468728785 1250 468727535 468727541
    0x606020c010504030c0501050915040605130503160b0c010204030c080d020106060f0c02060d020c0a0c03170f07140712060504110f090a20070804030b1e010b0711040c0e0310 76
    0x1482c0c0c09005c052180d4142401110190401c0180c1076100c6414007200030b06040c0d08004001030140c681d24503668071041c1d01311541011103035001c1400b07580810744250500092200a2055030241a0101d54500120440502900858201034050004080005406100040c0d5072600c0d1003c0d030000d200c0d00380d540350241c0d6440e0030080d09402251104c01020014a408002402542c04176240103041182a040346840c01181c0401110800a10b4100b032090140440403135150040d581d120f02c1c07400101085991460180c58801046220078060a102d03013141404114003900c152900703c0c2080e00355052541c0504015036054034a90380a9941580030708000034000038424001d4064000c5481e6070300500020101c03408200280ca0030030003440e607100d208800138a000350048c9207007078a130360460815042e40d01000e0040303d4407062a503071403255031440e9107500381103520001806803607102c40c3c11300c110141861f00f0015800392401265192541c0c102c800644882001d50865403d103103504581011 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 468730035 1250 468728785 468728789
    0x51206010b0f07030c0b0f07140322020f0315041b06050f0a020c100c030216140108130c0e160804111519050a020d0315180e0d030606020c010504 64
    0x11070307108002e22a81c0071994070080841901c40d01d02465500825103c0b1019448140e800903150b04080b001d200c0728640c440144003280c0450400c6e507146040c0781500522041c4240646201424940072240175550741c03003001c2c106800e01400fa60324a0580d0b18802c0a44e030b00459088800000c4602103c4040c600644000e056468580750746180c40750000d206000ca4010b20300304411440b42c810420300548a01145091401c516103c0a103401000d16019042400c003c200305400d44c2a102d0801808912036132401520b0400c0c00d01000d04e84070101c13070701a40740c00301c103015040380c10340540000e107075005256480c032481e60100c2e01030010421400c200c2d81c4d42c0c02502c0281252190410f900080e00d00403601440c800e200500d010320309002d280748601451444e1104070041980403034016807068061085101c29549845d0400c81e6510160302c2801911840c09100001d21071045105040181030b4004019903c3c4281241c440e4514044010050803241c040c4134014060072000c020954080d00c29502 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 468731285 1250 468730035 468730049
    0x2070b040605090f0316030b16031103070f02030d060b120601082802270406050d0506042d0b01060e0a140d060207020901030b0f011d150a0f090605120601 68
    0x1142080800c204450300c01d03c0300c4002c5d410b0140d41c0051300004180c52a007001144107070880c10032450f04554201c800c42010441c40f081c18104081100010805801c0765031001a5007020b11155480c5002286580a24450056480c1c580800810301700c00c250081e14101e10022440d0005666550046494040c1030310a54441c200a084d55000c48401250445582d0316131000141044940c40d0401860401d000c1000e60116221070062070906084c080d61001d000107980302e81e01c0d88076965403186d0780d480085c0080c4c4080380c3c00710043c414404000b051620052aa021000500c2107424440700d60315082c8605c4020800c0ca1788103c40c40e040c5550303c0310480d0300860529125413582000c1c403512a020a8045503030780d508001391401171707480b200d00c54041d41c01504200124a4580041c422102c01a001004d6920040c12120003414080000c158030003031250b001d410039000030022460100d80c0d6004003034118511800428000d08aa01c204100d480480706510a4241074803171986030074003800742d0300f = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 468732535 1250 468731285 468731287
    0x619060603020412020f0111011e1a0904060507020109020607061e050601051617040f030b010e160f0908010c120f02071a071103040f06030e0c0a120212060108060702070b040605 78
    0x80c4c05850400c10000d0180018107007280c0c2a400d2100c2e03035086a408006180d100c40d0b40040502003a8507d1094401440703121540000b51000e5a00040340c400008200600d4583c54000090100d8800c2d0130803282c05a01900890b1160014030b040c80181010300c403a074091010342c0d5400242903d00303000e014040c4006850303080c40d240848011a03020b51805501381c0308145402c1c003225094401100500040c482d00b00e038448000c0c11031408180709407040c0e006086020701c80d401d004092a5402a071298103000e400d1001a0b485046c42c1551001159842880507510b0b00e005000d00750340140301b02a480e00c0c0c1140070440b480140b0000000c0340601140a0003401d000c03201c072084040403c0c001034000219040c1002c000006844142c07460340035070005403003030700145810821503030107020300900d02c62110042c0100f0751020000c070303038280d18a115000d42c86a840100c041507465000041c01000d481c0025243c542da11420490741d21441590709000600c50410001502d1580c5420380f030a4078030a9441d1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 468733785 1250 468732535 468732569
    0x6010c0c0611151e09060c1206030a1401050720060408090112021c1406090c03070c020301020c1615020c06030604060506070501060608063003070506190606030204 72
    0x1100e814102c10380e2000540f060140c041c0e4442c1555414a110741080e042e010b000f185818541c010300d1074003400750300d059030050342070002c010103540c00e486448410451100032941c980000a150101c1c9401c054007039102d0044500d030181d0190030440c841c54060700d8000da10722140300001916101d058283d14660000801326002a280314002c05000c041450414131002141c101c00c012a0312001d003401c03084103c225013030140400b07130140d0b4220300d0350707200360014600e02180810f02c28000144840311100c00000007900541c0501d00c54011541c016000f15103400b200c0302402e58451406030714170a0110001c000080b22841300c0740501d045006135001e08050081041842000e07000031b00450780c0b16884240c00b02d0f503500d5030f60141a0a602406c0041071b640c1c6484009040148043c103c0b9000f21402040c41840e41c196802c010040f941c42c4080154120120300224114000c0c070000404030300801c0c080c81016000e000c90702e030a0a0044104200da95501e400980032446207101d003000f40c2c820311081c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 468735035 1250 468733785 468733787
    0x1a030c0f09190e0d020601060207090b06120417070807060b030105071d03030d09061d030a09030206030a020702090108030703080c04050a0312030f1113080a0201081803120708040b06010c0c06 84
    0x40c1c1c561079915403004201100707842c0f4400d041c8042003501d0001640328900400003e80c0c1004a6001000406000c01c10a80e09801143c01d5100f0790034000c15000b0070801240400c40c0c03840001001c4000100a26112141d170320b0500e000b40e014000c10f0707031707281e0901c452a9610f1030184100c0340290466291180085034800e03031503901c200f492091aa16000905c520902c01082e405441681031103008009807100c4d05950741e5407260125260300800361300c00d10001020a400c00d02c50b805583c0c046429580b650381d0144918080d00c00c84500030342103081038000264107040040500b000314801d489401a6a0707802c00c1001840c0214450f1545c031030508103080004c41c00c6451408160203040c580810300f68035a41011060f100c2884480b1100180080d40e0452196001a04005017603088042c0407408042e0b00003c2008002070305082d5003e911071071081015108000f02e0b0880c2e0813038a081d56035494610009040700303800700c5081c0c900f0820240020744a6100e4042c54080355804280e80141c81d0415034 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 468736285 1250 468735035 468735061
    0x905030105061f0210140108010e0606060a180306180c0b030f0c09010315060221131e030c060801061101090b0103080a0908010510060f023d1a030c0f09 67
    0x43d0fa203095010f1132448208001c8107000e4445540310190700c000c600e514181c2d2141c00c564100c0c44003100da40014046c009140e40361021101c1c0032031145070400d1b540c4e40200031009404015030004050600c5c0140c10701c0030100b030503440c000c01c82c025a032412110381d0b80c2d4a82c01c20f030712044540c07000d008a11070000300d20544090103020f15810626000907807a280154070101003485800c074030050b07070045590211300d040d030388241c00030b00078140b17100c81c02d000c1c10744540b80744107405000310102c400d40a4103003c0b00021a2070800000c0da0082451000300b0740d650005408000c081c040ca070005219800d440220390014003512090039400800314031540e1031070701d90350b500341c1180030003204005844400041c045824022203001d0101c0802181c3c1e485d00c0c140b006080039030400b8504056400c0720400c2d014406404020360a0091249a800c429921890820f0003041d1003051101140b450136110307901d405a1403010150181d0141c0c211280902a10108820310302c3d44074005074415000d200050320184d02c40 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 468737535 1250 468736285 468736339
    0x51b1f050d0902040504060f05060d0503040905040302030f13080d050703020318120d1d012c150307020102090a0605091309060906090b09100b011704140102040f06090503010506 78
    0x7040000c00140d190700190548200f900d0039103c7c0c58442c80300c620700d240984651600420103c40ca40c440c0045907035010b8a0b40a00d00c0350340d00c807a41d140c0c0040c0905000b8401c44440b0100c00f400c06a64414240802d01444031901900c00c032403241149048405000c1c034215400709825400850900c18643d040900c0c207007450070403e400140c890798154000008010068580500303459000e0004410444a03599841074224181044890000c144490700401410009414009000100d8500b96408141803000c07200e08402816400010094034581c194007400c140d0307a0840341c1e42d420680d103000803034040c050303c420203070700c00244803440b80f580810380c1c0300e180468818080407800c0b0483e0303100c0a044804449040e61240000300c1041b44a22081c00140403c44250310304004a5910030002403c891408180c0901443d50601040a0110803485076000084c400000c0d0764403501d4902c141801800c41c8583c0d004642c00b032a01080d0707031078103004042c403450002d00600c2d640001240c041140394444 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 468738785 1250 468737535 468737557
    0x3180605071b0510020a021504050f0111011103100e06041a01031512030e010909150b0304030e09090c18060d170d15030c0503030a0c020603070912051b1f05 69
    0x11a00000f4a51180f2a9000c9000601d80250004002600512502d0f5040c0c14401c2080d0a00300018005660b44910035a8018800e02c2d01c0d061100d80c3d03440c031a00500d02c00600460002c804010000c031a031100c0c0483c011342d884a4542400d070344a9600780300c10b50f600300d4085414038010303400a15080d486540b18043c07d2400f4441240803641d90b04a1f481001c0403901c09500107070404a10004072350f0410540c000030030709840c01300034906180703007003404110850051006040380080820213140c420700200c84103240043c51003003681419849155a05050000c1c540a020205028155000c903022141c3c82a0005420fa01000c0c03415a00c41640b83d007148050b00d02c2102c1440003072101100c070310922318049030340072042c0d1000d821810005ea60300741580c04644294004c0100480640e44122a4480d441d41a5a03482d12600d48c9041038800d0341d442c4d0400d01d04c6840d801e481d842440700c000f0b40690200300c03515042c0d4110307144c035051110070f01c07081c2c43c0004500c4020303000e014010b1003180180501d482d4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 468740035 1250 468738785 468738833
    0x26040b0d0c1b110f040b03031c1b020c09060109030b0711012702220e0c040b01090521280606052b140102070c030318060507 55
    0x1688506046904a030400e2102a03507520641020030b0741180500e040c240200e04848240490340e5601541050041e04a0340103458410400354951150341010108081c02816603445103103180e07103a00c1500c2c12140880815040018281d03c80c418190401901c25459010704502400c070414800100d0000d00414100005c07040008045500400454090b21907a940c0310004540365016a01790792030100071641d004001c100120406084404403150180e060715109085200d4181440101c00c640200140030303400c0124031500b0890100f8139100a01d01182d007007140f0380124004403699441381c051250417028611401d030140c1c3d100040042141c01000440304800f960f8040040c040a44004402100c42d00d0b8180e007080003818058040541001e55140b00c5011544000080410b0340c4514800b2070017220704843d060000b00c1092040d110607040081d984d0302400d00d407859010325680700c15000034100d42c805007c642c15801542045448654981d4102031841d110f421600602c401101d070b01c000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 468741285 1250 468740035 468740039
    0x14070329150c03044505060d020301020a0306180b03030301051c0f0c0e15090c0901030612030c02030708010b060f090f1306090b09010815040327030201030b09042604 73
    0x10b0208003c00151581100c0004014400014100c00c2e504241d802d0480000c41342e0002c0c4d04116203070303900c1d030344c0f40310b00744081440c2d1100804262a4003019138007075099400041c0321610707290507401080446036410304040311200802c6480d01160041075640d58160170800c010402840c200107541c8466416002d009206201c0355a40c110702d8246000071201d001c8140d000f000340c0c0c0c0e507410302c641d40508104d8425500450110016000c1007000b01052521000400d41814591007644450301800c10b41c6c400382e03010000350030060710648110004901c43d201d0391b90045002501805021852140641030a06021401860f0280c94115000207a0010040c0d50040305551742d640c00814800107071200040d603242401d11050580e40c40e0481d090150942100400240c3d83c000340700d0314600280c1e03489031000d46807031a040f1251a1641841d04802d504000c04d16410464045801c0403a80700f605c0411a4401801c24050b1519003164040e00d0542070f0f05050040720b503000486507003190510100380c0780076 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 468742535 1250 468741285 468741307
    0xb0c100b120d08061f1e020312090303100b07110405042409110a0e13062904051e060d02010516060501050f030c03030703050f0d1407032915 62
    0x482c0e01e00c128001035032400034400c0604040b50100b03442c4566540f240c0380445075940151182403034001946850702800c107140125842442901d10041280c0300725800c40c10a20001030340ca4205a90111403c034805c50000b400c035510b041100c0442c3e0b80105003a503407080c3d403030801008000041080d02d250078a144104100c482c40d094111655440401c0000d00d580d950a100004400c2021014007400c02218240444001907440030342c0074010350304180c141e140c145400d2006d449554090420b40313160141080c1c0d52035184640314030420007907034100410b5950001c200041d03000d143c2c41d01484440040800c0c882d080c81c1c0c0c0000c1c0e03500d00604180313140610078842c10084080110080e80c0c142d0351800141300d2441d00401d5482c41940c00c800405602c0083e41c0041c0c0c8a02c00d1090050610a0000b080600c42d1200030684404000395081004100e01c1582035071019503040310107800203440c201314819050300c418a0224004104402c50b4001404003052250003106c0480c401400201803066402d19 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 468743785 1250 468742535 468742543
    0x31027110402120a0609020906070204020d0603050f100507050a1202180312130b041508041a0c0a020d020a1106090102030d050408071a090d14070b0a0e070b0c100b12 73
    0x707203030f2071503038001e40f440d11290000440340141c00400e000c1d401001203a0884d40c40360240e6402c25011a001070f41e40020044680041100790310090050240d6581c6040c4c02c0e902007010007026003024014402d0341c2d1103560440b11482003a00042c08548104aaa440200c0c3c80c1d020b00005440c51102042c50752801c1d002a10300449800106002c400000754001d01400c0800f0f80401040f8a051150410341000c0e28111b159100c00300e0b010420000d0b10003d0140b01000d291100e11a00a2100401074105044800545d5001910100c00361155a8040040701c2c0700042c05141c150304180502c64807801030041040b607500c20304400f4114402400400d0400e00789100b480d00543c413a01076195650064504480000c54440d01403440c40301090400201d0240031070b184510740d201c1e01d0701d266946c407002d401c1d40150043c800d01074a500410340400a03003141a41c070200c003401906c012039840942d078504500e29807003012004e00c0d440c6c00c500c140c50340100c3c040d0440c1c540c1d4a0700034010811140f60020080ca0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 468745035 1250 468743785 468743797
    0x510060803040f0501050c0c010e03071517010611060f09070e013804050904140d020105070212070f1103071d07080f010b03161101020d0b031027110402 67
    0x141c01c0098104480d0310981e44280040100f1b0070120f061107004420a9103400000108605101401015030b0b03050b60f007801204040d01e5a41110f81840d840750200500d038ac3c030b003c90181d901c0282c10b40086100750086d061951081644802002560ba40c042000480781c03025000034518031480300b010a8030050004624043d00c18060201c912059103804000c02c44501c0a400c89905800c001b4800c4100c408421a007e44500b80d0794500c00d41c443d490542c0329000102004500b6000c0c040036230401d1039064109500601159003200c01562030754003295035600c10318000500400a0021100020b241511309085d1400020161209580d80b0a140c808c000d0071082c51280034144038081288503504548455000140404030010f01d40c10070301c81d403d6070300c0054440b080384054034680090003440361000710b030890409030080d0f40f60244046c00f000a0407122210700e00c40c0c01001d1840c0d154003180d21480c03a00e0880003000355003c9050184140010303401d0202070300e27524a110b41450f2140c0f228002024 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 468746285 1250 468745035 468745049
    0x30706080609010e0c0a030b0f090c13060206070e04090c050d0302060702010606020604110d061512021203030c0a23070b090f160510110106060203120f060a12051006 73
    0x300925140c0300700080c9040580001881003807400038403139005e90072419102e4400c19814001258010350f0001000e0105554a5603408134403c0104421300c1179000140044880b0b40e00000721080d07d0f120142c0c1c070380c40200c618800080510840340c409160981203024500d01450384074410301d455401003000407143c1001a00941c2c05281804145c030340c2441020020b250750302c0500054142640c520340c8a104d0300c2c10080c420307a100108a400d101840c4e0025064010304a40341d4a0142c3d141085002805544800e85c421260f8a0001035000b0001c400c4030301c11019030030610314000c0c031071005460805501694817a8840c0020710f02807076404002c002c1090900401c00900d039031500c0d2207510714090100d8a60140c40d04100300012449404120f0700c425918119080a2102003940c0d0840d804032a40c002d02c4055070130400c002402c20340100041001500c15002e1394880d50711042140c1ea00e02c030980300503400c104880001c012820b0941c20b10040c6522400541c0c0f5200307000107480d425142180c110031 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 468747535 1250 468746285 468746297
    0x190504060611151005060a030f052401020a170705070305060a0f0507051303060b060f12070806060c100f1806140709180f0e030703030c030b0a1215020405030706 71
    0x50382d905000c200c402d0540000c81d804401d0382c0b5104074100c200c40203a1191074004d4001080000c402406900b00342081134011383d04014502c0c06444180c1552181c0000d0f4440d130020142d00f0f0619440802c00010f81900a007c2c440240c0d020403604413682e000c000305585074040d100700030000a00c00e004081c09031f030920902140390701c4008202000c5440c080c1001e0b0078080204070400c107007d001031043d0308980d0451000500049018003040d21445034084001d810400000d403014801d9201c0140f42c01100700707075070314401d0359922404d00842d4481c401d6400304660001040100d994503e0700186940111204003040040030102c0d00390f800103100a040b115961111f40c014a002044030320f196009500c0c1c6441b2010034036103030454004414a0b01c0701c40001e5100d00401560600581100b81d4215025049076518401c41c01d005009211540860001a0034080d0030840e900d030803420441520042c0d0001da0310102c081e0703030700b84040000d0024a4600c9800348400500d0b0355061100380c004125546500c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 468748785 1250 468747535 468747557
    0xf0901020f0604081206010305060f010e0411120f0903090303040902030712061d0a0506010f0c0c030803040312150b160311030a0e131404141f020c0d020114061905040606 75
    0x2003003541c2c402442c847c1010b14060401030566a500030141c1559000e003001c8418006680225029104002921850700030008004090100521241c0d200d0000d0080101c4540c4036001c0c0c3c5a100d21070140301c50f9050b4000d00c824418450b6641c0199006941420503070300740c0254600d000140d1f00d550348001c200c1c0f621441040000000f0b20b00d07407944044440307002c1181e4907040002800d1541e140710350764100926421101d08001020036080c5c080c40c0c00100f0191203281c24500140700c0308007014443c40081c2008030541410252111003010358004a9004e41418187c1807010100c40b04414150100308101d03855080b044018001007121030701302d80d12a2103280800050104002c48080030f440d20f2450201417007c5640c4851000f80c0041d80004545c00405400d45014a488c0f0f4200143c000041c010b0300c500f00c11a20fa600400c10500104181d80e150048040141d00b2101d0000f00942e02d140c8440c0001e0072480c151502c80d00b440090203500d0906501d960105044031000e40201010550b00181 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 468750035 1250 468748785 468748807
    0x130605030114190f06380a140d1b0810050d020a050105030603031b070e070c0b01060f020307150207060506030607050a0309031b0c06030e01020a02030f0901020f060408 74
    0x2e01040c001111905010b9400d00f03520082d00c203014400c200d07401540d1044201408441604407500514545411816511800c02800511004005030300c0364000c6510301c4000e0003010b201541c41203680e43d10340d124910740c244180d084961100e1240c01e00d20f42e64116001d10111400009000070142e0b0b9905025403405151000641c1c200ba041b40d80300c1c01f4010700d0030700183d490300d46d8482550f00c01e03c3c00984030744416000c01c2c40c5004000e10911103040002500325107000000320b1324200c442c42d075282c1701240c030341c072101303849011001d02d021340b00212100061080b00c0c01002a100c5e0840d4510441e450b000c16910b0766908441582c2d0100c00c1240c0008040090198602980d03030486000c4000e48036604210310081c10500c40d07003000406060700d524002c0c00740b500038090780f00403038030440d08402d10001914000c40c01c5030030b9010b460040f900d418107042c0076180c1442036484a48030381d0001d40c0b50140d0b8240000c816041150344504510946542d08640d00b0240800703806503104044c0369448881ea151 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 468751285 1250 468750035 468750041
    0x108071b0515131509061d0d17070e1207090e1c0e0319021507050d0f02010e0d111608071502030a0905012f030901030614031c0302091306050301 64
    0xca0480c1120a8981c06400f24141081100c0590001580091407120b24a00340c4040c08011018030b010380e40c821402c5c1100403020401ca001d01085541c2e40c030274220090903006601c1c806580c3c01c0c1c00940007000000581c03c3c0420100c044080d02011260b025035235044883c1528130321101010786420960001d070051211525800300c80b081d078104000300741d820390046035980380e5a02800030f03070344e100340313951802c0d07444042440862481462581e9a20038490a12075652212441a000020300840072492124410321a40701c00282d0741c0003400f14950040001c48044480c40c8881a40d409151103200300c00c00101c0040d4020481d01c405044828a000510a51680303044003080c00d64008000c0304403083d51180a510a9032001d00300410540c140c0c0d580f044100d8014045162540c0301042880b48503007002000d0072040100341d80610200f51a4042c8200409800240e035403d1342c0403004a0341400b030301407000240c000c414500181462481c0c00003455140244c680a1221507540c0020f0240741404c0c0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 468752535 1250 468751285 468751291
    0x70803090f1c0e09070519120c030614040501080c1216030318080304030503041a191d0a030c14030f1501030c0902090f0f0d0803040606080d1d0108071b0515 69
    0x1c890301340700d10301000094598400d0062018404045010300b4540300d01600020007480a03a400401124150140240040c070140c01031b2003001011405039003c40c549030050905130341a86000d06600c4c9444028040055410040302c0001c0c000c0031041a0a0401c02c0c20700c200450090ba68407160241203051021841c100350010310198008020a0001c5000001220122041490444c9141954008090f003d004046600101e0115501c842c08170701c1d4040c1d00803030b40c4500168401034840d0010301b0401400d030b19200c01003041c04400c2d401c1001107040800c240c032042028040d20003030040c07420081c3c1445602c4964400c840701c3c4d0b1005100384440c904250340070385022002146062815000692084a102041c038031801d515030541c4425103e01d0840c205081c1e200441545038105846c01c02c000e030100d4010b00640e40704034000d00d14201c2c469000308904110041c00a16000b80c9071004591000740104060b0503c4010307985001c000c40c00102850500340070b40060108401c807026007041281000d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 468753785 1250 468752535 468752539
    0x7050304080403020d0f0f0311060604020406140a030603080c060a0b040b0120100c05040812030c040905060303090d080306010314010602072705041506050a0605070803090f1c0e 78
    0x6004100001d100401141c0503a6012a0300881c42c01103842c041d03407103001c00f030303030007402c07503894848407410550040c20058008c04d082046d11495640d48003800105e001e1889040c0003d17100151500340c0206203401041e00c48198500030070000d8503038540700c0c403a501c51000c03e0740c103074000410820090014404c0d0780e41e0080440b0181b18002440c0002840d0081c11002c103201b5000301c001084282e0000c104407942d0014001c1e080c042c0c00000c41c00502136400610a40411740a65407150962481240891348114000544242010300b00942e09005000003030060b07806110802c1480b94a03a62403940c00c040710310610b0400d40c0c078a4a04001015105812200341c00a4000001407082036000309021080e0b854040c00c01e104028280801204802c42d10b03200800c8a107028240f1041c0b0540c450544038141d00b0000038051301e80c1c2d036070900a15000901c100d00001d0b805002c0c0701c0000707800400460308542c03010101c2d13400180e00b203040c6050221406c110000064900e010148503038200b4000c0340e0003001 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 468755035 1250 468753785 468753787
    0xc06050a03050a0b090408160605130308010e3304020316110f0706030e0a0b0403020c1005030108030316050c060f0a06050307080c0f0111030c010609060801050621030708070b0f0705 80
    0x1d1130040b40111001500c01001150f0102e00d6035a00007500d0f0107546425001107090245e41085c5940314240c5883c18800e600107000d00f00041203036198420060700034649642103000f90381c5558003218544c0e045820615070021a40380102c010b07a901d0000c2e50042441105148020007001009085100003200c407d4840c2c10042c042400524041400c800701d50b02400c0205001002010040c00c1c12000c2c80010116440c0909100900d6800100d0350003000301504d0303e601c081040f480c2a201c81c002413048500c0703a801040007030040254078944c00f11805290030217a041c2100d0410982c01e00e4011182c1c03100d0101e00c941003000d01c0d4418014440105000d402400043c0c3c02c0c4404562140000714915000d940310149461b01c03644181100c0154103502c0007900e0b21103101c0c1d000d040c0648245d114a001140c1000c00100707443c0382c103200b00b602900b002045070041d02d051403000003c08074682004403190100340040d1004c203032210300401c0a035120320b1001e070003450903900c0d560501c40060452020064 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 468756285 1250 468755035 468755051
    0x31633142406180406030c06030c02030304050d0507080d0e1b0f090606090a0f090203160f0503040209100f08241311041d0102122a0906070c06050a03050a 68
    0x303141074580402007081d074426644200002c2d000c540c455940b071085400514000d800030074440c09140e24025509039039424010000e006008994038001681c005e040364000002013800c4600690040050500c5070441c0340c24040d402901804035400040301013403d0b04040001884217561040110340d2035400c903925811041820046100c82c41c0041a0328007032140040d000300c140d5140e4060f0750050100300304141920b030300d850303140c0040c2d0030a5446012844283d1484042d043c09203d06c0703140c6c00320135a100c1e8199070726502000072090014014050001c806100420920760002c951805004000c0083c0301403049050458403c81c0084001000c01c8d5180b41844030081c0244c0725090015000290100c030341086000040051110050201174402d0407550303d0304101040d0050885020400c03218030096498a542c1d41d900000c1c501601c40e0610300c2451036030203040c0314002d803288200c09000c0c0e03805d050b425a1125540e000581004000c1400480c80c1400c00e90b041c007a5a60103d0303020014001c0007 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 468757535 1250 468756285 468756331
    0xc050a0f09050910050907061b0f08090118060504062a14030f0403150e0607020d0309051f050405070b041508040501021201230303163314 61
    0x41480c01903801d001e4450b000b28200301c0d4104240b0f200d00303a03030207410031560070400c00c92a51007040780301d003101190400d81415812100211000c104903085050f414000b002d65603001501e900880041c4d05115a0080c10079a4804c0890310902421064554603540d83c00c14001a0031000b10766494140c54042ca0110640c600340c0c031000c40c0a107907110484100344d0032a82e02c10f9003140650004000f5102d0081000420310046c041d0764540000c15242c00c205c0000c4604003551100340445071100583c0c00680340030750442c82540f01e17000040c0a0820703168440703500f80da0030701c0d64640407544641c0c40da1248140400d01c1000d0104400426214252034585864110b00704545200d4681c03900c24401c5100005040c0842901110a00c042558014000f0740c2c64144886070407040c01200f0703001c1207c204000c00075007000021941c62920488041c031104040c3d5030f81a00c11014080c44c0d00c1440c0e00031a092010b40781410500d2000040c0c0c0c072010680e400200040c1003034060040203501a4804c0c444051118 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 468758785 1250 468757535 468757559
    0x1020306181308090a03051002041503090f11040b15180a0303020c10090803030702010903110a080d0203040602090306090604030f0801150e1c0506040b010b03091207030c0b130c050a 80
    0x7030b50740442181d4480e280c450004000b20352075403000d0500c0c010034924104614890707008000b07903071080d0031280440549800407012508800c1c40101485a040d001c580401c044013400c0c199240001c1010404442040108103034545810101441d0003010540204250b103034810b010703489200340ca0500d0f035039142da14000c0d0340e074690031001405840783c2d02c005100350307100d5941c4102a160303100c101ca94a04180e1802030003011100c1c02580011120f8410440300040454001102a00028290b003080c8941050070029072020780201c0c0c0180e820400392541d41c07001e202541c8501216000350603a07103080e080c040d00101442d1184010007a914005002403200c202c004e040350100d501e091020b4208010120740d0544010100c044c20200c01c807000710401c03000017506032040c1c1c89417046035440d90740d81115040c103010542e03082c2050b0b04546a920100b0180001801c000c90103468210859500d540300d9010140f01070303800032806204002800b00788100d414002006000c103880e00c2400c0c1c0d03e4112034000da = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 468760035 1250 468758785 468758821
    0xf050915150f0d0528061401140d060303080f01080a03051611030609010f0f0209060906030903040f030605010e060f030c10020f070b19020c0d0b0a02070605090102030618 75
    0x729940810402c1090b81c5000503503601c90100c04040089003070070f9401d42c4285d15008002d05059102c810701c4045010140200001c442d00b40c01d40b125009981d070015a1041a81420005a41004e1000c204900e146010b07000c0214000c0e01d8522950508038400400085c0c140c001580c036a00100c90440003c1e40481111145034140407018544035680c68210100703855114100c2d8544a10701c1030261500c0d0640c072041d4a5146a9001c204040c1d06003151410b03401451314842e4400c4c428413482805007070480c000c2d07502803400c000f60381c40c254541021443c220820780041d9050740d07a62006000748100c10700b00c103402a0042354182c00c038070610170019598100c0d00b103219004205501c10f40125134020400d1900090b40071050390600e6407a400d25540342c1d00560307520f22081e50781584c0d07000114008922140c000d40c01812081100c40c980d100d03c140b12038042c0030140c1c03899080140a001c02c0e214031910340191200030015aa0f0f007030602c10070180958401d0380341411006007040c80702a008003103282607 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 468761285 1250 468760035 468760069
    0x8030a020903030715020d230601140d0c020705040e060f0406020a09050d06020a02060c03090715110a030e0411090d02040507020c0d14070b250203070506040f050915 73
    0x66500c01c803801003815406120700042c000380700c9072901c001c03030441a0082d05118012803010403240d4010009409a44486162040e5900d02c10f804107000354810b0781c1550240121a00721460600d07080e11010443d0401e20010740181c000840911491809001d444007d0706110001c0c031a07424869207804003020040d0008245a0380050b0a88115026501d4440207000050040c01c0074401410301c071010394405103100c3d00600070000082d00c240c1d043c0c400d49028a010304000c20900f17040941c40e11350403512410250034080d040082d0f140000003008507100061182d40c40c0c2141403000028071042c2c4608240140e4854030910040d0096201d0402c071400e2641c0448001c689926850b00c00c3e0309140b0b40001041d04400c00d0124481480001c3c0c20305000801c55400300c90000342d480c0c111071a06d0092840039145509569841100c088401700e1000001e80020182e507107041d07440000a01c0c0d44c2c4550321100c0480d40805040140b45014641d843d40f00f6410800b03040e1035500300d40001c0d66801c014200c08 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 468762535 1250 468761285 468761287
    0x70f0b0a030b0324010e1308070303051506030a0e0d020f0d08151f08010501142b05010920070c0501080414060f0a05072309011110050610020a08030a02 67
    0x1d00c1d10f940c2000a24003500e00c2c160001d40a420042c3d1180a03080e090181030401d0441700c003c40c1e11140900510b0314529008003105041400710b40c1e00310007500000d4140e04461030200400e242c90b684110003503005102c5071800041240c42c09403458244424007504d1015500701500c0740100d040081020102d0440b18600111079556862003881004090a1031582009000302c2c0d40c02d0a0005c465400c9542e2803e0311104143e0780e17030360011030352082103416400000c44240503c000e96540c64841104000c012045c0845c91220001c0c10000c54009034820032525485540c0b42c02c4100c0125485429000c074800302922340b58590b1070b0910450300e00d100c4c4a040011f0b080005003030260134100120341c8450101a1085070038851119a0402c40a407003034041030345450003003100103000b080b160850103d09000c45591807900c00100d0304540043c1e0040d410301064140300d010a4030180460100d0b1002a580001d0500f0714405000050600c2c944200542d030210a541022641000c01c2d45e601a0f0020409 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 468763785 1250 468762535 468762551
    0x6050d020c0f0304030314091c0201050702041b270e0919050d0305010915060509030f0703051e07180b0604031e020906060f030406052205030c070f0b0a03 68
    0x600081c451460107503024061044040700e40540440100100d0740a607543c0000481000500c0080d481001a9154070035070f00d0f201e5207048503070385079031000041c01410b015047c410281c0205098401f4040c207068001c4048003043d0420340c2108103020001403140f105213242171892001d142202d418010040c036036244100290920000300022505911f2042c40480125064a441543d032001e440c070b9034022900384000403920040c039220b5079104100460400341002d01e00841515140d10412540b034050250034482089620104581001588140018045600801b0808066148000301c8000380d402c07030202081701902e005220414a05a0b81e0009800804040000d40b41d102c0c0d540010180c4160301c2038a00410040040c8216050081d00c0600d504c1c2d0b952420003d40e4440d20301e1000d4101c00a0000c1000f1500030340c0060380c40700505104940c01c44c0d8000c5031607009021200c2c01c0b80c0036840002e0300701d800c203000e020701c0f0001c102a1134110344003030502190600a000b00d241c0281016510400 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 468765035 1250 468763785 468763807
    0x408030906160c080304030309060305061c061d07080c0103020c0d0f2d11121c061205030a110102040e13020a03200f090c1204050c0a09091406070203040605 69
    0x40041443c0d84651100146641ca40c14582c880e0410700c0700344c01281400f0030005455009002d414482e00c4000c5c01400c900c3c1a8800a580c3d05000c00340a07200701d99101c1a000701d1524542007805034840c858000c000d032a240110461800e020b03544041c5c1014014800030040743c900040c410802235603070800e800e00c000055000c50390004461100700781d040c04441a8001c01c4034911070a80494039980c0e4400c54130800c084019a1084407a010b80c0004004000020322490080d1441424001100c0045095503494003081c22850240030300f99035580001400140081c0c120700420304a5060000035400e01d4500880c0101c00c034801003818a101c2d26400000c0b08640d1001c2920002e1035000380448424420b00040c01c4003000e4446030580196002c00304071819241c060034161040311214001403030401003c15100e05c08401400c1102d6512500d40c1103501580c0e203155840c00b82184072030005064255040c41e14a503a030850301036449070031070b1007401ba007142e02204031001d4410904003903030f680b401001 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 468766285 1250 468765035 468765067
    0xa020d12031b0c030e030708060711120414031b100804050109021e2706010c05070f08010902090105060c0a020603100905040f03020114010803030619030b071806050408030906 77
    0x35080c140744050000306810b180d00081c003242102d0195460030319150700403050559403490750041088a40c801c40004955512482e1045045800355003501c1900c1d504402241d1581c20a07084106c00b0701410600d1091401e04010058143c24107040300b80c860000c90380070030b07103801d4600c3c0d080c000c000c001000101400400d401191340d2070ba01030006516880c1b40c0c00c038242030100b81c2d54070383e22464030440000100c400c002141c1c16010405039a24245880e00c03c01510b2220703a00004031001e00840d1400074003011030300104801400030200201c1c80e896107204003c002c04051304081d2040b2000c3c420412404c0002404495072941920030554a407503141002244100302d9204061903418042004104850041403030050b5201c3c0e0003e0022428008a10710659424000c884413540144000359151818081b080c03a8001507101e00c0008541303903110501c1018007294014040b4400f4101081480c5480b0703a404000c01c0140340150906041c07030741068691023100f00d1548200c00224401c03490a01c0c401d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 468767535 1250 468766285 468766301
    0x603040c031a060a060c08160218240a1401080406021b030d1103071b1b0603020702150a020709090510051806130b01090e011b03060302040b030a020d1203 68
    0x641c0881e81950340c0e000e41070714038008070350035405414280c40008090f03020b035209004940d0710801d1241041740342a881c4100d4400c8172016039020b0aaa01e1082c1141c01070003000380104000c0c0c03d0348017010041d0700341c0c840c2d12411038004c900541843360100160500030340041c0d0306120910b080d428585844c00c000c0040d02403200c85601d1102490006000504004000c0c408580d81503c244080486000031184030300040b1551404203061110194216009225040840e0300c14001c92064150f1105001000c07d529000440800d42c0059100c0030341c50109142d0f000d006407000014a03240c003115000f5214009840340e040c0d070702c0d02c038200d1030200718007031284110100071004100954900142c04802141520300e100c0300900078000451501416070a03202c0000c2e4020110480340d911303000c0c0cac01c801825902507809555507100401da4450094100100ea0341c615682c0104000f4118010001210410b0075014481e80c414400900140c452128554655800001a10000021100950140c01d0710 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 468768785 1250 468767535 468767543
    0xc0d1e02130f0f032102011413032c120708030f03070810030f02120f010c05030604140f042607030507060632011b050a05011413020603040c03 63
    0x1250900c201021199404219409000145070b0b0030755030a440800e0055600000d0310742c0926014001c05140c0041200e119880144000202d1103011003d000c01c01d9020354070f081002c00d030301c0c9044091580c01008110040c098400130001c00c5048076140410020038030840307024800203480d00049440034840032000f4003419080e81c0c0d0351801000c840025a100719003050220703800e0f80100d038080c40444482809e9990101c2100010a9203808100200081c0028100180f054009034410b4072003e0184080b60300d0552601500d07130901d9801c02c4180c40c0d41c407017a0103c05041104008401000e00d0880760000c1c0c100380781d940c040003651008039141040684a140c81c65000401208055206004084450140ca000c202041e260404801c106240f00e03008401c0010503c42802054480741482002c1c2c1c105050103003c20080902c1541c006088210039201608450346000c28807400780100d1031030b400c4402e46118545044034507002400c4002c60043e00450b00400050204102c01402d400590f0f00 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 468770035 1250 468768785 468768787
    0x30a06050a0605030d0f21020d181104090507120303060305060c030105040605040c2c0a06020f011b02030708030a110f0a0f02060121080405121e060c0d1e02 69
    0x4031200c44009010203100381c502911800030317184026881200c19040701d0b60345589008001a0031500154031180d030158440001740d0820000790f8400071440350260042e02c02403e104080450705140581460f0b040c02d0314000c5c1e090034941400190301040e410b0950f506e4250a94560a03a03040440c000c11240c0c00c020500d02c5242c0910030440c6681c0d02540c1280e80032101441040d032200c0601c0309440e41c145141000c104005120b82d094a100900750050b50318282022400300b030740c00d00041802c6002c0d03114502580040089081c942c03c04c1c01880d84507209143c050344c0e003084501c0000e41c0c0f80314000001e40141d001002003615110b113500a124102c102243c1c468a030400b074800d000b0aa070000d4118004511003207540a055400030404a04a40032160000044c025842c180d1065501d440800c460b6042300f00808200366940b21296500704080d40005e01c240c0e0b2002c00c42c1607200c02a81c48000341c6602074401c0001205081d01101c1900700400c102140403020f19a080c2001042c50314035005180c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 468771285 1250 468770035 468770041
    0x8101a0d0b04110607110906030a061109010909050c0708032208190f02120903010e0d27030b130f05070905150616060e16030602120f06030c040b030a0605 68
    0x40080c80501aa00074008922602180c80c10004c0b00e204001c001045c1103905d01c9001d05034a00b081c41e0a40c4442e010342a00c48901c3c0035541c0070308482c07650b4481c51a0103c0458055841d5038008425070240079503440800c1541408490364001e409500f0b40100740c50400400150280140e02003d8007440e21107aa2101030211454040750302d40000000c1d00007140b1016007280704d230741b2a04010580d540300340c01802c0c02d541d800e60907a215520040100d90559220281e07213045003420000d490501d05c0555401803e07000c40c4800398503030003d0012415044103292410f002060070310540c25000b81c0d060034402c2948049182400c02e601e02c510014220b401420340000b010070494111900c1802d5032114545050380a00400c2280c1c080c0445085502502107842c07030018a41d0303031061a140b1f8420003140c00308140c0342c00280c1e403000380b504200c03001500070a084000da945840d605800924240104415140802c08655070311111003801d480b540e1030b41c24101048e1414403c005510390006000d00848c5 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 468772535 1250 468771285 468771293
    0x21040909030801060329103b0307061b0f061a0111011119020708070f0603050114010516170703020a0b070e0a0303030b0406050d11090a020408101a0d 66
    0x80c500340309050100e41480100c59401d2514105680c0700106c4080c1d0b11024000c28081c050722100da441c1c80400e00c03514440e2000d40042004122400007510105001a04100c1001c9000c114a007140f0501a0b401014244945504900c0180750b02155010a20b0b260308141451482003071000400786c6032615100040e100144800f040f00d078000f500fa2100710104440c080d00900302c945403015810051814065400040180e40f802552000540304540c0840e44500c50075050001d10390004401043e400c0c410419650180650b030b0050544503180d401040e40700002070300c0c500c1000c10711402c41c0c00001c010820003907502068105103262a103a152241010706d00603650b0b01c0411000d89400c44101c000909691061034000742c16400904070a503003600d56a000d038042e101c0302601a034080d8607000080740035118a24220f4000d4064616601815446020300c9100c0d0300191010860f40d00402090007029400105584201400d610006111100d001001050601400d940e0380c494041200c2000780 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 468773785 1250 468772535 468772547
    0x1b0804050d0503120609010b07030c050124090509010c0905120a08180906030a0f20100309120804020a050f04140906010528030b040515090d0e01112104090903 70
    0x340105070b035074601c0c5846017410051021005d10030518800001c100e000006882400d8000d1210702c20400801c10131800300185c402c00c49003891480120306100820010140180202500049000002c000e00300b40286c00404456480c017400e4001d8400c00460905004100464143c0d0341e0468031140e141c1c0b0900e88240704880321050303224850121310740802e40c10b00e03000c03469805090b1f010f0241d045d03494031aa243c440c40802d5074003000d225260840c8914460312140040c0c603910803183c0e800110f81032070b45040c200d0948144840310802042c04108001611003c811400b50390703040380c44403c031500600016016290403028000c0c0d0410300c906120500000190840c142d030b00407075034490a4120201440d0500302d80ca8030403024039810302400c1022540c002ca400390858000c20940b61000104200c00c0c107142010340e01501154400c05010403480e40c0030381c200b03401402c00d103042c42107440b044e05116640c01c40d1403103a150f84091032040410451041d4201c800400540380180158509410301401c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 468775035 1250 468773785 468773797
    0x2c0d0c08010e0d0503100e06031c081905040f0b0a1119020105010605070c1206020c0d18050307030f080c0a0210050d15050d03030b150c0604020307151b0804050d0503 73
    0x329125403c00c0241282c062000d030b0780f08550000072029198500700d55005600c1c40030f081c541e014061807445440c03035048080318140700945601c40e40345504000705690b041520b1182d0580d6a14030f02410302000902e5034110245d120b4002c0c103054684d880e451490b000501126059840700c840000b651028018201e00d400d109162a4000708016a42c80c070741552203200d4000018481000440c060010750211903500d03c2d2140110340060030b25031a4a00d181c0360801c10028407000c00c2d150900c0400c4040e02002040261409030098480305145a44141000600f0700008041240109240c0f0704800708003e11401c0c550014031580341d1118008001e0615441544a0004541802c0d0680c0360b9105d032143e104110b80c400751981440b00d0b0b658504400a2800000c80d41d0310010750710030302d010908400040d14200500d500540140d0806104051501d04294010400366403951506080260001d480404c00d141d40191405014154500190213120315000300350720400043c8500b042c440c0c00405010 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 468776285 1250 468775035 468775061
    0x109270c09091b080303070801120c0b0703050d1d101d03070804080f01090236190b04050408160314040e0106200d0f050c03070b04122c0d0c0801 64
    0xf24203615100c40c2d0782c03079100882e4140b01251080c00104142401e0200406605000c5c005041c1c10710f40702c100d030000030340c0034660540000c0d4020070200710f110058800c0003412a4030400f50782c0800800c0b95240d48600c6040d501c0246d45988181040e07901d420011603000016071881a00d07952061848d0001c0d940d001070207800810304c102c032134511003c1814451904819002044450180003400310840e6070322090801006443c3c4d0340300340555128181003a0380c002e105002107905440e1541660300304886010415910a40c10030040c080802e0b00002207482c03015026020400f64102814103a40101c4500a0319442080000380029110150207065050b50f8036a0356005500840e521180c002040c8042d40b4049904a03526500c5142c0c0640d500c05541010b5080560402070310050701400d43c1c20203c0700b07a600102c42070412080095441e01035a10500e94103000d5401e020002e1200d460100e450a5a841b90355580b021201c903549484c060b8166551003d16500004d4031840214081d214240a1f01d03 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 468777535 1250 468776285 468776333
    0xc0c0c091112090c040c030f0c05160602030c0f0f07030905102a0501020c06090d08010b07081608130810090b06040903091e06080109270c0909 63
    0x2091085490050203140021074014508206504601540208014100c1e02c1c0030301c83c02c1054005921903001d160384044c41500c00080c1c1d9400b80000d001990034858002081200c00c00240310040039000c40501c1d881e8205400589980e41d5400d50440742c8180d02d410900c0c0c01004c01c80d010844c006100a0512500c29940c408507142c0d074800748a0000b44400e201e03004101341200d0401009100082100d000c5150842040800003035181ca031308903030102145140710b401040c10065002d40c00c119081800c507052070950320030741c58040980414010032200400c2914000380001100203130000400003c1e4018078000c0e078400301032400303101c85038480c070540000b4010031580040803c107521410140340e810458001d595968081000010f00390344e8401c9042c401881c2c4081200000b100d100d204403003e003102c9543c0142400e502418000c01603000b4500e082c1811121840d00d694120056250308010740441280700541c64000309008031034104075842c610f40303460b00c410f00c1641c0c41912401c4404000e00 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 468778785 1250 468777535 468777539
    0x20f0d050121020f01031512060e0d0f0c060507052514120703081e0f0108120f090103091103010c0c1103070503150702150708092b050903030d0c0c0c 66
    0x907800b503800c203000658481c0b042540c1c1c0d00994040d801620404007210004107140b13407241c100100c0d061107030754107031096540c504070b98001d0b00003000030407002807040c1002e200454510070000c3c00f6501d110401020140c8403404643c0c042d00840580b41100c01c2050015200d000000d074845175020700030380039101000c050301c884c07881e9840800c2608501102d00340103440c0002944007a0741c0804c0c0544000944118004040a00303481c2d240028050f00c07001075014007d516110040303290014605508440010400003440121802000c0f280d441d9001c0c02c0100c1d0b510703e07600313010007074290940029405500788a40905456800000440501e1141d118041040203010502d5990b42e460300030150075a100c00e00f10360284010100c42a403002d10781c81141c280500440f4003920308081520110080380c4040b043c880c003410309112018041820140160172034010f042000e542d560000d80550a20400180348800c40c0c6043c8100c035031030a800c400911885d4038001c0010f007040380c1098183d82a0110342c00c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 468780035 1250 468778785 468778829
    0x613261501060527120a1b0e150f1801050a06050f0f07170c0703030813050607051305030f06060910080d0e0f120d180b0315010201020f0d0501 63
    0x903070680302140d03541e50803e1188203c070a944100f058600044003c40c90b5030b2005952441d0b8110003203c4041d028210040a42c81c089001e516104102c0006000e0b56200340410842159810751100202e46055007003003085d004542c000015070041500705520045800b00403800003030386030403160280da5020303d840c1e03600c2044500d40219815091500000c0081100090b01140a0a001030044c19080104480902284030725400740d01d8080b81c6401c010f504005058100300090350004501c100c02411400316920313203031100c0009003a1800d00c80d010400421440050b45100b0280901400312490781c0c5400c01140da54800440e0100e01c1074442c4000200711a0166041da0211190301d0020200324212200903101c1041d81445a40c21900400b2441801e546111104d2001109a40505030300c1c0500c0000501195004440710700c0c3e00074402c0100418a0840c049031b902204900500003030000ca140106d002e842141100726050f40085278511080e001a400303581220005144071000c0040406 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 468781285 1250 468780035 468780073
    0x10e0f07030312090305040f09060f1703030703090309080d1e03110a08061305040b160e030a03121b0504061806210906020423041a061326 61
    0x3400501d42810f210107060709900810120b03032207402c2c05403c0c5501c8000c02138250078603500452801d03442c6c0904202c5c0081c14001000038056802003180e400a06542d0540d59100c0500f44400301942d035100030301414820800880601070700d1090300d01072085a8401800900004654841d08a03881070401105000344100000796002c40281824240d061500b42ca022000130001a000180541100c050248502c1028441ca11802c40308046040c007603182c03940144041100300500884005224060b40d00003411b01d000740c0e040c60411004010002160094101c60309110b980c0c1c03030f603421602c0813560002d01178400e5400c59520041c1d41c1001e20000034034208140b054002154054074940b038858501c9818080040360103001050104a90781d400c0c0883e4842e42c0811010000005030440002414400c4600802c04440c20700958841d00420174101460606c401c1c800c000001e8003960110020103508028140c07e5517102c1d05100d0754031581610f60b5034441d4030041d8003524010100b0210326032 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 468782535 1250 468781285 468781289
    0x1518090903041e080723030d0c030e04091113090206030108011d03031017030910030519050412030209031005010308041a0c0a030e011112071704060e04020d090b09010e0f07 76
    0x90040c0b03840c0c017000c0108141c6d110003600030703040081c003808482d4404212501d0f5480c183d58900007540001e040042500b42e600f1403180c13085003000000404034600003040180200100d0b905854210072026420003410841d100942140e000300001400c15819440b03291a035620398801d141241d08020a2030b2207101c00c0341d200e0b21701000300e9420b00c003010080c401d00780b1001007181180c0c68022060000b5000303454110451000030b8654081000b102c41e9080513107171600181d5030510407400d0680e1108a4401c1c8a40343d441010341c003280c0e510a0342d504003c07000000102d110108055612418440d12950203809510541c80c00384001d03642022900086444890901c8098841d02c1c900396002c841c0d030000c800080f410000c80c4544010b800c002484040d40c84210781c031f04155200641d00e001e459002c0c0d00b94185071400403c0c0300410219070081a40748244c81c0442c0c0040e42e840128030b00500030074032034502404032407180e01006030210055002555180030384045910460f100740140f552078180d4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 468783785 1250 468782535 468782549
    0x803091c08041202060d050a0b040c050c25030b01090b090705030906060d1412040305010e21070501090605070e0102010b0a05010f0c0507080303090a120e1518090903041e 75
    0x70001004524812540000f00502c01032405103054000107a403010b43d20103459005000e070360390341921191b240600c02d81c0001511410242e05010404085a4451b8070041c0c2400d0742c1c00005007d50020100ca64540014541c042e40f0b071450b40d40c403040c1e824010601100014001d408100110308218000e1065921488180c070040045548220903c4961640840112103022001440e10f40004041c000c140c2c5480303c1020554584e4507600740750342034500d052511940c54000c5011007003424015100301d007000c0002010303142e03601051729086004004e1498094102c501e0038080c0981aa4403601c8182400c00c00d034001e204c50a4080700b002030940755445181e002c5281c442006940b1401081c405084500030801c1ea0401a52070b403100f82141e00845d07030725885030010f0243e01c080214a4030f00c05e00c12401c524080b00b54641c0e203004039403594a800002c003084403020600c03d4400f919040640c032101c0c1c0103010000a410100e00c0140e903a00b00740960b000040149001006c1c00c915001904100ca0075 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 468785035 1250 468783785 468783787
    0xc0b010e040b07110c0301020309161a030c07032a110405010f05150705010c0c20030a2d03110f01090512031e010e0106090905060d080a05090a0803091c08 68
    0x10300d00150b0b00f0781070300c00c0051382500442070b400a40e07a400380f0142d481600e41d01c0142c4141103980c401102043d406070400b440c01107056445106040003801502ea2103100d469180b59189241d0a0564003c1c010b00181d0fa6074004010301094013440c008030303010310140714610302001c10940e40704000664600f40034642030490094004c00141c9003000c10036503035801b01c03552103290645e2030300c42d117007512a402c0c1190041605200141c0c1042040480000d0442803c02c0c00000c403030b40c1a0000c1d07241c401c4408040c160342c00400001800710703404205051110361010300c4500195141c60041c04281018045039410300801070140340703a1320117000d6007081941c001d01600440d94031200f10b9040c5c0c0c002509809007684040b85c0340e444014101c02d4240a00080307106030340c07158540f0000030281109604003990260520043c081c2e19250724016800c01035012041075141c0c46421411512130103101c030718a501c01e010a000255143d4040010a407103e010f5449071280c0e11458248005600300500040c42054 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 468786285 1250 468785035 468785041
    0x9010912050a0201052a060103030e01020303012d090c020601030203010c0c080909151507060b01110d14091c0b0a05040818012c01020606030f030a03051503010c0c0b010e040b 77
    0x84a5002086c81c00b0042000c104010414480000480d02402c2c1c0c2d0304e40741d409a4018003d2541080030400c40681c00d1004505d190306103218403105032515515808018481840d42c0d00c0c2d903080d40c407544094481002d0800031810300c144000e55030781003844141c0c001d52030518012000c612540134820348070341143d8401d1400300d13090113108d24520b0042800030b25454404052210340e64a51500d4440c1032140c0302a500d541c514181402103890300351419040c403203c020300c60200c45001c00c5040c0414440c0c103090351420141c500107041c1e48a02c55540b0342c8180703000d01040400390f108454a665a0007040e8810460380c0c0c248608080740e000f920090002601031016140070074000070305110f00d8406140040c44019145a04821060010f071403038480d030242458a109035904010792540076404800401d1a101000010750700c80c031829910350101034031940002d00a00400700040300490b8083c1c02003008003841d6400170024408500c0484142d0040400061003400c8401540c0c0196001120148162 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 468787535 1250 468786285 468786287
    0x806030d02030a140f03102412090f062d060b0421020409061a040623040e0304030b0403021e0705060d0b04151d09100507140d0209010912050a0201 65
    0x1280c84e45202c1d49036901045055046240c110245025011180f0407200d660b0618000c0d14982810920110440320385110b811546a801410b076070100004000008050445040409583c803c15001900c07a9041c950359108014054540c04071220415482840d030065420510058a11900c00c18100d10b03010301c014000f40d00700034400240e101d00701d80225020f200d80d0340480e042c0c0e04448000e07a40281e507040d004040c09106440f4810013403040f60104846420468409084103026022140050081115074000e80301c2c1e9000704c0003103628208584d1144d580340b6001a580404440460041c040c4601b00e5201c09005c1d859500f81e801c0000c0907214540c00d00c030a1059640144548c007803255165411050f40e902d40e07200307010b01100500401e802c514100f031119441c0400e108120041e4881100c1000304d002c1c408141c403440003403444800f05082d21082400c5a0f804c4019030b15100b00c0800058810940e0250343c01040101c4c42a00d40800082c1e56410900c5054401040039050342c100c104084015 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 468788785 1250 468787535 468787547
    0xf15020f0a020927030a17070f030203061206090f0708060f06060d2a020606011715180c0403030212070201020d0e0a0b0c0a050705060715020c010f0c020a030806030d02030a 76
    0xc200d4a0040f8100d21000c1d9491013403080404c441090b81000900621139907001d10f20031600c24414500d243d0754102200f00500c20020000d80d00d0426074080701107a026511480c1c80540740c4128412503100f4185a011192110428603e80310648114503002424100115510b4450300d9401c0040300c1980e9400103100c001d600015506841c1c558805650b029401c6503000d4110b00e82c8588182400e000d040030000e441d080001e80154107201001020b039681d003100124603a80031390369851144591130f0a0002c640e001034a42000c5069015038010003088440d104045c0c81100d019030700310307407044d41d4420210f205445402ca000e07006801c24261080722a019030300d0130141c02c40161000304400ea6400c500343d4290405111a07459030004034041003032040c1040000c0c0076000c1140c0c854a400d440e039407501041210b56020b0300d5415004104805003c0c0300394007034840080502803d20240d881002c00035140d000e044422408980c501c000b080ca141000201c039a001c480740d400070b5140070001c0c0c1c1c0c01e40301 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 468790035 1250 468788785 468788791
    0x10b0303070f06140f06010f14070303020708190c150621020a08120418020405030a120309150c120e03030a0b0d020d0c061425060b09010f15020f0a0209 67
    0x2c075482d032680e1040c56250703804c09440740c0b0035919140118200000010030750542103402100308556041480014800c0004039068580e050600582c0c40c8158a401d00c81c500511201e15240c01d0300c443c8000596070009225503170644600701c245050160320507500216205070041d11a041c5548003141200d511903001810f410b40000c004419071a5038603821854041c881c10031000d44c0c03001050403c0a60b9450050b8404500e00060560a01e8281070100ea42e4504007880503000310010000070b581d0078000e5002300d24558110b48850022034030082d2520291460507004000503140c411080403e10103032159240d4500d00c0c0001d036185858000e401c001404001c44070301d50050780061030b400141da4602c1d201105d5481410048400d40c9012000740001d075940001c204001400c100000c000c600b0809654920581031450300c0e014202410488001c045103c00765070020300d80400850558401c103080380884040c1022000790326480c02080303031980d000b4000c44060f603112407001001880e00303000c00f9038 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 468791285 1250 468790035 468790043
    0x203060d051002090a080f061609080a2402090d26191407080a20030a0210050106050405180c13030f1703010305030306040f06080a0804090b03010b0303070f 69
    0x548150784501c0d0030407524910741035082c2e900194444890074a000c0391002011140090f21500c0c030304a40151311000c0c000d1641d01010281e0506100e03c1c0e0280350300c3c0c00908000002c450f000b103a04d143c200d081b00003800c0b1100101081c0c0075484a014543d000b21080f400001d040e0200f10180341d5201007414000c0380761401d640e0340d51034141c0303100161072020380581d0044105105888010b5140035214400e000c0111400c54410800103020444c6401111101c10f00351808590481d0142d05049291a020489013028080001c03040d40345540010200380f80c40d03144104110690b617801d0283d0382c6d032189102d80c9401100644194100800e0390000c9544030301c4030301c074841c548a0940740c00c24145c1c250750811114848080b90500c24016001613582c00032400b0602c1030b10319411900c0300c50792400010702452046890b1f038884000c490568120303100500b0381204031000d201d001e142980c144c1d00107010341c0d0300c1903240c8804040140340500980b58401c0703015000e0340c90460b031502c0d203111400000c002a5 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 468792535 1250 468791285 468791299
    0x305240f041b0e0405060a03051509070f260601150503040614180106151b02030c1002010e12072f10030c0806010215072706030518030c070306020306 66
    0x140c4810700d0310005240086070340c1d4800b81c3c0031004004110881d60f0103040346004161201c1e040c0000341d40018100c0014050901501959885200c0540352000d40e4221242000c605800060340340c90601c101f845071030605070042d22442c80c5501c201ea40780343c240304120040c0f0320b54448000c0703180110011604680505004074090140a940340007000f0161102411aa450400107940720f602303204560180c003000c08084800703031007404000e0410800c10101551080d04035828011507504004440d0240320162185084280407200640202714043d01007485001d42d00c01a800c0c47c8502d0100d44030300744d01818400d043c0c441990425400c54030010703180039a900c5004141c10700e0b078402d060040d03003400710340e0007090f0219443c40007403e181340600918155071005858203524a00c505405501000324546a00500f0004902d8105900c0c3c00104d0300544059213800f04145506810942c400c5400203031140d021102c026a0f00d0b40e910851020300340c1604a4982880011900d030001c40d00460024400 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 468793785 1250 468792535 468792551
    0xf0f090402030709030c090c1d010203090409080d0e03031b0a0507060f0614010e0307030b130206030a140615030106140714011d0d0903121106070c030305240f04 71
    0x12604070ba0080d5070407401309500c0310042003001140c4410741c0c0580b01090003803107103511502d405841066003107061150500c03c0c0800541c1a4030030001d07a0b40c0c3c000c000b08144400040303403c0008659000c418698012401d00b0140c003002d04002044a01400d80c1d00c00e01d00b4884c1079507030200c41c075800814040d030400000700b000d100840d4081c0211480708a0a03400000c1e1070b440c0c0010b21035418120300c1050306001861490301d12030703507022650104a94000c040c1c1080790350f4400c0703181899802003c000798019004014031590341401c0c1d000d0311400002c84841d4440d5142d0b00104414000510321000844108000521585205a1803090080c00d00c0c1440c40c2444110355403000e070840c01280868103690345e81c554415400090b02c11005690a11000d484210a01c41c4010040015800040d0140f490280c2c10034401d44500b24203000d940c101e50036580b060410420003080390081d00c0c07098000906141c0070502900d100b0415a100400300100d00d9070001010b424000d800d2050004298019a96000c1d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 468795035 1250 468793785 468793789
    0x6030604060f08010203090118020607062004090212010e0f070e0f0a0b09030d03020a09230907021509160513110a030207020301060f0324061d0403031a060f0f09 71
    0x10b074015100000025032249002100f0900b101d00240e0490441d0301c0507400308001d0380310182180c00b01c036045000401c14404a220841401c8210142c80908103000180010b01400d5903002e043c56400c0f034004111140da0316090203a000c04c0c20b031090720316034542c41e01003002a0701911030450300e02005802000c2c11341041c0300040c1741203019030013004403038000681e0806602c0e0600035400c0798442c905085091103002c40009088a006019014018146910030711001c160205102c1c803000c8010700000181c82c1040c0006d49408841d0441c0a0180481c40030401040e0041042c5c20348280b4003000c29421490b00e4200302c1c4807001540d0b403140e125540c2e0440350603010108001d04c03901203240c601684c0e4103100d205250071500c1d00c3d40b041032500050340c0c040c40041d03000c01a6110410901003424001103025411400420044c7e100106000c0d0f11804000030510300b00099114034080e40f0104040d1070072410038640030000000b03459100504000e4548038419000181c48019154010301d0704000000340 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 468796285 1250 468795035 468795059
    0x10e0c030411032407170109020901110714010f140a03050415150815040b01050103020714160302091e0a15170307120203180409031205040f060b0102010605010e0603060406 76
    0x242d241207400c1082e071341480114080c1c100341d08100213161004440c460400885051001030251050003034000034810803c0e031060306501100e9410109980c512070f6689241140810001620740c0411014040c190f1030b2409020304980b4800d00c40d11482c940340c1c0030042100203100090089800c19440b0003602003048681c0300721aa801d401c04494051039060005461920b00d1030f9845441e0b0550080c2004001001c0300580c1d41110028200540c40352490729041070402d1649058480303611542001c0d040d1040c0a103d81c2003100e0080c4d07800a010b07184c085000541c00514821650884009004a6290502d03903204082107075440402d81151621003a4001148000390110209580042144003d00c403141210000d03907031701400114035051314502150310f4051a040110711560752002d01c10207041c011000c004004584a00800040c5018030384140d080300d1601d0156800c9182034002003080d40144114426500140c44108002d0606401c000b203c1d0310040195802c50b0704c03000c00081a5407122 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 468797535 1250 468796285 468796303
    0x90406090f140106121119080a03020c21030a0e01110f03121012080c10020a02030309010e0d12180501021c0c1e0825020a02040b09010e0c03041103 65
    0x304088070341c410781c0c0d890a48900d40c0099858176100b04044002800c60189400103001c1070301c0a8203038004204a581c0c207410141d002000d503004003500b640825901060f0b20211640c00c6840581e805032500055880c482d07407540440d0540d0003000003401c40790003480110303204401490500001c400300c070f003014180103456010000076440400c02a41481c1e17401403030740c0d00074038581403003001130701d0103403180c0c009035101c48050303c0d40e900005e1100c3e078040d0034042c17840d0204d08510150343e10809070400a43c0c0358812202400c0651800064500b020004241c01c2d55410840e40c44030303941a0800315910041844480184c0780c00d80c0c95109400048082c00a40812001c055800c80c114004003c0c0e0303415105206140010014000c4110340044070301c04031440c8000407450044c900e5540c49500710407182d50443c0780840140820303100c8440039400115054000c1c070079a01440100240c10510904c0310f42030190b811018002800950500c00c00e0f009140d00c10f0141001600040d00301d0046820a4144 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 468798785 1250 468797535 468797543
    0x110c0a1d0f040807080304050307021f0f0c03051804090f0303020702090108070806130614010b0c01061a030402010c030504090609060f14090403050309160801020712020303040809090406090f 84
    0x80100e0a0410660004558040340c0107019a0072481c10359a91030781c41c412090014915280800401c090200400c10f075420264081d2009100240b1000b03809018589002d800000603a10004140f0082c4502010701007960325403669400c001c141180ca030315141054100680080d03942d50181d0214403d42c0b05c50006c2c601a840050f0f0329034079030043c440f403450141c101403002c0d80f24400800c0101000508181d02c4110080f011207031186a01c0c009000e0f2004103030003503401a10400100381141c1d90401000b0707140300c0c44004c00016a6402200f8808131410318440d00e40c440070300c0020b0265011303a040c0d200040c0b207403600d0b80c42c05885891000071925541c02c003210147d43c58805001070455006903001a051810b40c0d2440d50191030005000c40c0c10007000141004008800f04008c654200007450029081500500803d52200070b524002d4010407000d44508c903802039020b00403400442203034000c6c0e4000d03482038a4014040c090050003040a8022640035030740f85000b001040d1040f29441005101e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 468800035 1250 468798785 468798809
    0x501020f090307061704080306060c060901050108010b1206041202011b050301051509030307060b1c110306070f0206010303030e0c041b0206090c0604050f04020405150a03060f03080307110c0a 84
    0x18079030625141640540001040c410b45003190300e00c111584a20960241e800417145640f5230720750002c80c5103405240200d010521552041c065141010740000741a62a142c1c0204400c1980d081000400707080408003c101e500190041070114003078044080800400d4000402c5086442101c080f44052481200780065404001880145840c40d0180600030341815983d00380404080041d4984c842d40000030400c0d50b8481503015180c49007d80c14441d80c4201c810910303a4900e504020b100d158840315180d02c64054000003402032801102c2030851340c0402e9008202e20307030a40d070b81540200107000c82d160240c070403040c2c11903182d642c3e0b0007012003e5a1300d08002d14040080c00c4041d01d0850040c0c24500c55410514074124507840b4802070310210703031040394a003041100b01c00104009200c0c079004150408442d0048542407144c54006007030300d50469404000c0540c0d00c400541140b80340e408000c1661000300b001c135503410b04c1840890074501c01d020594000591030000154090550340c131090789000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 468801285 1250 468800035 468800047
    0x80a0e030301060804050f060c0f070201030b040524090702070b030a06030b0c09010f11030904091119051801081f0e0d020d0908060c251406060a061b0b0606070501020f 74
    0x1f4056003011001c028010007550130014904520350107486042140c050340864080c056a00ca40c000600044002e4010050740c20282d680004400f8a401200b051011081c0ba445641c240130300200e100c1c1e40168007600d269030501070032081e542e001409440381981c40f403401202140d40c00c4ca5450181c031824400684c4c0d411500009003415004600ea041481f17001c000c44409240048110741410804503000102c414483c0307030050308440fa400019400880341300500046d034203401c6e4440207864045a2074060079461a40c4841001c10134010301d030160700150895031481d15241c07410780c40d0f910310701004506204848c00040c68400a482c2510040e4050350502068542050091002d4001035000e0705140c508802701002d9849a9421a084090f030401c007040824100368040b580d013680f0040840c0c040c10b91110781c0e56600c1007030701d010b44240150b0300d00142c0d05004000010b5061020a420b8601c031090742c40e040110040200440d41045040005600180080c4005c00c1034030709400605443c0c43c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 468802535 1250 468801285 468801293
    0xc090501030e06090d081306060b0417240408090d060b0a0602070f03260d0b010806010903150b0102070504090602130f080756031303080a0e030301060804 68
    0xd0040b00c50300c00542089042c860302c9000451004146295420320441c680c0b5003035500f0454842c218405010107103403c1000c61603c41000c020000c84000582071041e01401c0c643c029240ca01030400c0510342c3e090b912482400c1d14600000310303840380c0640d406034185144407020940325400070204484c656500c1e0b81000680c5440030303129000c0e2910b40f004096842c03c000045a0b88400c50002528419000c4c0e40f0400d002c5ca6a10321441c1c412414060796220400007202d00064a11a900c1d41d000c00c14a00020b01030754440c2528030100e0380c024510200c4841003ea4000c000c0c0400e0182c10f0440c00743d4880400c10f52524064291881d01c20751005980310144000b202c06654a508a010300c00d882c92000c00c00c541c00000c2c0403080d1244082c40e0303031040b03049181d20b10f80d078017883c1003200d040c01ca100340d50007504524030883d010407500c080100c2883c1600060108040c402240c11411400384480740c3c002182c0702d46030603035224010307110028070024140d804a280d504241d00807000144d107071003000300300 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 468803785 1250 468802535 468802541
    0x6060504140f0d050120090a0b0f131d0a0b011e140a0c1406091f06081005011404090203120703090509091e030306010801050114070606030b1b1201060507080d0c09050103 75
    0x6e02c3c0d1007009400d02c9841000036442075458452003500c80b0020800c040880f80001c11203120004d000b407010401541c03803424401c81c0c203025009820b03020070003001485805d07050080084d60300050399070912000d07500940454601c05003801400300541255131403107040e80b6074010549507141d91521942d900c5a4500211224038150102207140c00c0030b000c0c4148860005000c0180410302c10110350048401c01c070100040c400d90348410084d11600402800020041d80964117941624803002e40c00c0c102c44040c4030a0b9400e13080004c2d015400154401c0300c0c035000384044c1842620034a4000d2040f9560720000b01c0a0006441c0d12600b9001300310502d90544c900300c040c2241c41070031406981907107400e50001e0081030301403062905105a21085662540f00f0104803104070750310800170400b45440e81001e82c94884104c45030540c112440c00c48002d01800315041e5102c812682001a540d61700744141100c2640099404551041c0140080d04101482d03006850750800390f5076440d80700a103418001030a03 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 468805035 1250 468803785 468803831
    0xc0115081908040e061c03080703060e060d081e0d15060f0509130e0102070f030306140d150e0a0602091503040b04110f042a0306060504140f0d0501 65
    0x7400e0680403040300003070810002d580441c0d100300d0441203141d8918000c9410250120542610b002c1c100701c2810801d41c00c280794500070710311035030104503c0e9110085114048000d80394903921102820400000a010100500c690f120741841e507400385800d4401c0f001281c0003100080b90590303d64890f00d00c41c0d4007440070b0100800817407420780c03c44c9868000280c0300348180b580c0e01d80902c000c00d8201c81000c07600c2d000703800d6007400c0300002c541e01c080038107042c0c0d0702c45100c020440c0064205000080d0b2000c0d81d000c103280405008054402d0301c0340b540e4507208d0140111a09255450320390158441d002070621035031f50740c28015000543e8500b00034041101c0e280300702c844004810000c1c01484040b0b009016050350150b480840e00c010b1100c0540025080d8106401c19a401820465060740030001c2a43d9140704080045042c00141c840700e03400c1c0e040d40d00c280911000544140001c0200e20140d0b0000c907280390000c1c00d03040a041040c00400c80510002c5030070307035240c3c1d100d50b14508040b45954800003 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 468806285 1250 468805035 468805063
    0xd0e090c04240201091707020906060f1206030c09010e040515010605090103020c0a020415091b0c261b06060159130204060e0d05030c011508 62
    0x2141c40d0a259030303180c12480499031150324004203090140c810f03000354807400c040e07908040c10300b40e480080200c0c0b03000b990149104a00690909001c500e081c100070f01550400d50448002e2400c0c50718001c0200d0100800805c0a9418426100003c58548036000424003810a05100380894a01790a002d0310b008003404202031110800700041203096800415228000c0c000d2030056030f10300da8000f100e49000210f003000f03944a4507040d03942d448203c4055907481183c0600a0500002c208884c5140622014000c5038021038180907510001503c05550480180900407104a1291403d9080b02c0a500810550840842c2e030800070040a20104806caa200b0f200346410031031a4452012041111076000010714911180c1c54804003543e44411620400121758401e030142d0707410300220b00d01d046a041c1c102c0d4091204000d10b107001521038002c0b1000d0300c00503107810b40425004c40911801d5403203064252a00e003c02d100850b000c50007801080355000f0072076040054181482829400c1c1060440566 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 468807535 1250 468806285 468806287
    0xc0201050403231207110105090d0f030b0a030803060303040801180308060f1509030703021e0109060c0b04081c051003020f22090804080703030302130e1302040e030c0d0e090c 77
    0x3c007040229411118440300090407080c458441400075a0515408460031030194200420442e00c00000182403150701d03090341e0f50400e180891401030341120a90718010f03401100071344050000c40c0c1c102c0300454004001400316032800c2c0d0350b03245030740c212040e45001604807444800b00d02d082c503512030040c03a00280304070b581c0c2c48076a9a00d40094220916400c4861304100045400c410300d603010f001001c000c5401801030201001540c0302c2d0100403a000b00954081a182d84001c01d0451040c03058040040e48881c480800d0307161a103883c3c04a4004a0300b5044918060888002320b50150203054051441c03294001401c0d0b04620401a8401041c05000c0c02540585010b4010f001c8a60506048103101000002c03081c40307a0602c02040d108541001c2c0350b62007525000003c26500d6402404106a941d60003103155468104002440f2005d81d51240d07401e0b969900c2c240503240a60254000d1000b2404a03460301c14100714070303420a4000411207010038002c2161740784a0502e84034055018845160003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 468808785 1250 468807535 468807587
    0x21806040e010306110a0c030807141b16080d180b0c06040201030b012105150d150e03120a0f0603060c0f0e09041214040305031204020f030c090604110d0c0201050403 73
    0x10800b00d100c7c0809402c0001c07000115505900030500406140c8600e164166031780c41c111118502c18a0052020420b4810201810310000c568003001c02903540b4035001e01242c0341840c00403079000003540b0782800a940c0e8040001400d02003100180086e5011318081c1295141c54000541143c1404140300d040c03251501c01908070f41078070f81c51000880507e4000248a851302c0b09010520520981c11940082d0480704207000c0c002c071501041c0c05000711000178841d46852022107622402850fa480d0b1009003417601254605c4041e82200c00e5004003005c0c0000e10b10f80d203868010946d400918004007045032901e1300440d20303900101400205a094400d400700781880d9450713010090b900c43c2c007a020062806805030703010b13034040c2c2100c5c011904141142d403a001030240d40406100c055800301e110340d01c8407252020703c2c1008a456a84083c0040020280e941c818003403001138507020311110030468007004880b00850842c4100b48004d840d13a07000194914051401900299403107003441c01d00c041c13031481 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 468810035 1250 468808785 468808787
    0x60f0215010f151e02070f0f0e0f070e04140114041103040201050a1b0b2e06030b0d0204021911031806160605070f1d0a09021806040e010306110a 64
    0x241104445103003407641c050082183c4101c903801003844c1d440303c000180442070300c2807a50000700c00d819510100b203000c0b21582d40300b00c000201e45440c0700e00d000c004d018000045010b108084031a502c007599040c000070700308183c800201211001c0712488506505c0c600144850780701450282c1c4000300a680801810404007080040360100a000904010000480340c080c244210502842e20b00050071a5074400d9852404005042080b10180f49001903244a840c102c9020400c0f010952416200111480c1c10210120041c0000c1c5500541083c240048800140c441d4801891416620700301000d0045100d00300a094040801c0280380a070b00901240701080c80c1c1d00c0300e143c230f240d108640392903480364450b202c00000310b000314001e020249001c0410803040d412811183c90441c050f43c0341c0c0c900400e201d00400b4681c407512181030700030356000c00a0110790035079030052104495a8024080211803000044d44a07841600030560103040c01c0010020018580205200840341c50481400d110711180 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 468811285 1250 468810035 468810059
    0x16021f02070503071e1502210c091203030f0a02040506040b0702011407060902031507020706080604091b14091905041106030a0b1804080a0c03110304060f021501 71
    0x9884251103500180440400004000300e8541c59400140c1c01400480c18842d005900380414055035800c04091000d4030705152031085070f103800700c0180c03000800e251480031410140070041ca4500c006008020b5166207503a001c001904180c20305009503581d1604840c00703084007001428900c480b50044c4001d00071a9a40b01c1520250303410001c0264039107480c0d0004031801040d0301d10701c520454001035510140240d58111240282c003e401301c8204203d41d4101422040c2c0c2107038554010b80002c3c0f0103024180c410780c1600d400c6980180b0214169549440e400d0307030a9000d0116091114400000700064005203e00c6001c00804882c401401d00c1c2c2048440c0504004080e04500309955030001810025042401c520000740601000e8580c5403002041e4001c0c0019802c1d20b20034180e40f01e50040100c4840c0415203c1d5038020142c43c1010758080007921210240d01c411414004c104100c400d600c00300300040c0008044940d2202c01660ac00e02020b420081074141090800342eaa100601400000310 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 468812535 1250 468811285 468811333
    0xa0e12210925030f0c080d09030b0a020c0c060c060702060c04080c0105162f0303040503120a0909051006090b03280e01090b060a06050c0607080601030b181602 70
    0xa0480c1111000c0850888039000840c0c000505000c4e41a4032002030219401140c01903881440403180003a802d0101034a10314003512004260740d0303c200008090b1140350f0040c20160400e1011101303c0d200e00c0000400729040140d0740056a03000204001903140c0c100051034010400000c103034074050404107915151142c6840207030502400082016681c0c82c03603c0c54000d140d400c5000600c400042c0100541080340d40c03280410110303000100700115160120407901203550003401005800c801e220098020f81005584405004d45120000b407480020700800307104034850408172032054104680035103080d006800c1070b00c102c94144100302c1c40c0903c186410305240103001d40040c0e10b01040e0040c4000d8501c0742401031055003480c683e03508010004540c0c50090170101d8510f0030207600e404088030300780103810714030020b984110042629a4004c210040d00310030306150100300601e00201058007040e10f400381011081003c401c00c045115001d0803030381828400d1001e0020403480740d003400861030710070f = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 468813785 1250 468812535 468812563
    0x10501080408091521060103050106050a0914040216061e02040501320a020109150507020303011a04030c12300503190c0f030c02030a090e0a0e122109 66
    0x11040c10034001d000c00070745184414424210710043d002d18a880040c00c1706403045d80c0401d04282c0080348131400b6100b915403543c41552501741c1310786000d04054500c02060f054582040d420810030240c1c0c1e010a80d20382081f40558ac002c00e20900c43d4080540c980340403110704009620602061010740e0388650411307205e8070100c030b107461802c00c0810481c03000c2c07400d103007420781070900020903108040d019041a000d5078060511081440c628120b010180d51085401d500141c00400041c014181c0294120108103100700c1240c1c2419202d603942a105045504400d01c04440d00104070108130380700244220a8080300326400003080e580425441d0031402030b01407400d02c8000b10006030003120011501a550f02001c80910140e1128900078110000b2801341b000001c1c00d01109080090000003101e2000445646418402d4681030a98005078409444044129240c04118407840c0040000251804c8010401d0fa238900120000d20004000c200307860515504c010b041100b9400d003c0742d42d0600da01c078 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 468815035 1250 468813785 468813799
    0x504031205090f120d0801050a03080306010c0c051305150d0b0601120902031615080108030403060c0201090512340b040507030c0f090509060402030705043803010501050108040809 79
    0x2d0180015840c00100300c8058100031105419444008000f034500418035281e110070b500c90341c0303a000b409010901400080c1c100301040000c1485075101d076000800b180d00841800d51040d4895001881801404000c815095201c8041c05072038031118880036010101212445004041c5da03481080b6054010007042c1485641d8500b1103508000b9000300200d40e60041c255040031294202d031038031002c490b009802c0f100940f0280e5511490080c1d43c098140d80040e401542007074078640c5c0b217202402109000c881195200c4803586c000843c1002840f1801c44814803003516039400ca01c40c1443d10650040c03000302d03139603030950100349504186010f0f1201c1350802c51404c00303680c0d581000c5180203220390000707244070346002c0000340340d1507202144010f035291080144420b40314050a1130b61840d080e18003035419000707040100801d140c958402076500c04161110340c0c1030500080501c2101a0303000e030341c5450300c800385012051442e080c42843c1c00340a09081c83c0c0c0e601c0c00e0a8440710000c1c000e040b203850003030301 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 468816285 1250 468815035 468815047
    0x2030a02061b04080f07060e091e0601050f0310080c012313080a08090315010b03190b270c07082203080711040e0c101812050f0705010504031205 64
    0x106181201c01400c03240d412500308004505082d66a1321040c0f180f60f00099851076288494279180750b40a01400b11140104c207007100c0340c070301c00d001400043c260606001c010071001c0c0c190030300c1d82c000e1351158031013400e40c0000f5498031181b40d00b000c0804505a041102c9110709000d46500d01d4030362042c0480300140079496032406101c80750b02c0301c00b9400001e0103102c0c000d0304a0401405400604806005070107032800b003140a105921b42003820b00890482e00c4060002500380401c0d00c854149049003181d011440d00003c201090166408003011144101500444500030000204032500700200000302490034a41e42c88012a42c01848180c0d00014030800700001d00010f8808540c01940d00441100c0c1c4d201510b150016585548202c0ca078019400c0504e00200d802005ca5070861b89100908501d90300c0d040da040c1242c8143c03000f40d10321001011804046003c04500144003a424480c100034281340240d0b6105a1a0003260340c4840c0c10000d08100c10b0000a1604002a1940d4071a04140e900e0340c0f = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 468817535 1250 468816285 468816331
    0x140c0d0c0f0803010e0414010902060702010f022d0111251505070909050f0106050d181a040302070902130b070302190b0a0b09090d0e1504060206061002030a0206 71
    0xc00501c40203042104088004280c0c04185100a0301440c41099003007540351041c3d20b800c0c00d840c1070400103940f1000920004003d5402000001410f0740c4a1054036400300c6900144116480c141c440803060011640b01303450100401d1180d002c605403080041814101120091500f081c800740031260486a040b26000030000c802404490408003d20709001e103142c5840020845010343c841c4503111402c0c203001c5000001501031040c1a03c4495407400c1c17802d80c0f0f081c5203502070704024224111011f40010203001141e100c030840e02100314031403500e03500e600307013814004d141c12100d4201c6003e6500c1082000d89003400a00c172101140c4042817070741d4540100741000e81c1030030040d014440680e0a080080803c1002c0b21342e01502c10041414100300e030002c5c65052241c4103000f00d032a074016501800072004010301a0f030b01e4081181e80144901e2540d0000a0003692030380003503000c8801342e0b001e40140504c0b031815038140140180c65100850501d0900d05009594050140443c000d100030400451051 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 468818785 1250 468817535 468817553
    0x501051020010606020c01090b0304030c06110702030f1b03061005130209030118060507050403030e040e0708150a06060c0b0411010e100915030b09040b060609091303140c0d0c 77
    0x40844900070000169204d0010392184603e85410303002403001e80e03000c181141d049050341e0040740c259560310b540031031640d103410040500c085060046982440281d00590702004050901c01d844406440e40b044514141d440c10000392440074400d810480420280402c07414030101200d00c203d692400c0b2205420b800002032203103000c0d00b500744d400d200806807007282c4903210000240c40b48004008640c1e0b210802c0b140340c000c50000500043d4200c0c01c180c010302e09500f20100c1e20b040103066410050b5aa088581f078900303404110b00d610b0250004100c442e18851061400501e01130800b0b20220407143e4400409500003400200030f0400f6148070a030a0340320700c00c2c6294524020745850011030780b110f00503080c00310520034114a2042c0e410b02c00716892090159843c2554060b0405d40c890322107030703900441c1c64801448560044414014a031041e5a02c0071428011580d01042044095080c01d00030900d001c220888682e42001700701e60711170038a002800140c01204c81c80c040b4010007035450071501c0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 468820035 1250 468818785 468818837
    0x4050a0807020d020406120308160c14251e0e0403110c0a0b0c0c040e0d0804150633020601060c03020705060301030605250e040b21010b01021005010510 67
    0x83c940748000c035000c0e1102c114444103038000d440d071038100e5079480e242b05c0044266486000c00110000d0309200021420f40084050346124800d07202045c4d4145e019001c48050180380c40000c2107000320410400d890401601c000340465102d104a45041a85d201c6d0f0008000c1d100408200b05070030040f150f548107208140c440c070740041002e02940e03680d0310420455007000c0100c40280c05001c176020290b14080c481d0740382c1e5400c1130010301400260081e060701e441c8030081c0f080d0f812586915403650810103034443c00c006401110b803801c8508501d104002c0343c0da54421442100a10036484a001882d0000303980c1d411110a4030744544c81c10341b140f608070b0400c100b0782d01460f04010007100102c01c001081e08850f2096008040c0514031a420481818a02c41e4800c203010209035512054021401c00350443d1060800140c05890881c418421400320014040d0b40203030f4076555504030b04495a07061140001d15a048c2c41d040c840c41d410480000d8000f800c6074005800c1c82904081c209851000a0035044 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 468821285 1250 468820035 468820039
    0x608090123060f030114060111030f03130c05240f0f0708180319060522051005100b03060f1f0206060109150509040c11011a13020304050a0807020d02 66
    0x75444811602015076000944200d0300c90309800070510f40714181442000010720740c8010341042601e815006442030008034007049014002004030514212511008501484201300100c0861181d400c16110603001c03500842d11821403003400121000c0020725012208005d002959900d04166400194030311030085da51103890004503d9038140005500506881c60824002c200704140d18410961548074112104d840080d0b180c8941c070100b046948001d41c8864901c01d0100d5488441c00c0043e045541c1c3c1c642181c040e07100713002140305204a03000340d54004000c00071202c040c5003450075884490000030b0070346020784a220f00c059520703511071f40d410908852400514290300000400203403180001c8030030f036020a108010004052810000c1e40401610b00d56480b805c26440c50104000340011405840800c8040c05085140340820b101d50f4220700d901448505031003094800340803040d05107995025405106004000c04a280801e180080c2e9138020310260350307900c052002800c030040880c0003035 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 468822535 1250 468821285 468821321
    0x804120503151e100315170325172205060706020708090603100f0e060901050d030216081e010c0206070f050f0703030506330a054006020706080901 65
    0x1e8052605548102c00b02551101000c404d2511182c205842004140c00490240d0007080801c00803109090b5400c400900880827815505945d128070a0382c450329980c0c034900c58400610070007200d0315000c4000310054040100318186140c0030004019011710321000d094a500000c1b400100700a13002100e40c13030b0000030310b1140c6a0825403403514a95070a0301071403441040c0d2080119140c80e40e92400380c49008001c0054009a00300b60a1241810101000b04c0a600c03c09081d500301d0003d01e01c081c03026240c00340040204001c10342c0309101410351001800201d07458400f1411190b9404904540c0c0321001c5e003444901d240100200711b030144a4450410003492011920004150789600080c1c0030714821148100200c105000d15100c00008540401e0007041005c0400c0000381604060300d58401c1c0c50030300b607043c40702c40c070712424240c800d5050124400044180c14103440750f5881484944415050003442d001d42000400f96030389280e0301a00042c05540c01c00190400400d401419000e54074803425 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 468823785 1250 468822535 468822559
    0x30e03041a070506130803010302040b06270f0609060a0f09030f050606210c13180f0209101401080c0c010c0f090b18100207080d0804120503151e 64
    0x81d00098004250848160080d00082400c1d0580000502000ca0f080756040c5d01d10792860b82000300406000d803620f43c1004040c00200335002905900d04270741c04010528030345035611402001072a0400c1c4009620420042c0014489a11090290307400740340d40f070404c0b4058145900c0c0c1981d4401265000410708441c04220004111010078168003c1e02d0586200e90b14812031074119412204100c020345440d40140c0460040307140c00305d120140c040045400280011500d0801001c0200d8a841540c81590304080c100440c24010744041d0300c07503c0c01002062040c1009480321501944c03c00484c1000a06008114800c4d0b21074100d030b49640c4101d00070440701c5008140507009200248207000800c80703160002400e90b0416045403806060510088075419a290400c150f07181003a04803404c6100312100031608107400c0040b41c0054825840300641c5182c1031600030086a01503010070100300d010f105220070091807680395907002c60308450070b031031008103003030f480d000c844070f40d81c0c040d40c494024480 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 468825035 1250 468823785 468823829
    0x307030b0a0e0c06042103180909020f01020d0f21020304120206160207030305030a18140c0109030201080c03060415320109180207080a0503190c050307030e0304 71
    0x8411405000001503404040f245030070420a07010b40d02ca84403860300d00c1400740c481807105403040754102d84a41400d01e503013800312446c0802121180c11103203810b0364410719442035291901480d44542c009200408001c03a18100040c040045014240c003805807905400c09241d0540c0800c0c40010504c0b041191030b40380500b03010b0740a0307058410340e401600130640131070080500c007000b10000e0080c5070010131034140343d036078222090b40c0010040500c183d80ca980881d140100c200e007009a2601070b2081c12180440301200b9428006610300160621003101c00400040c0d810aa403aa4029090440180c40790707910004140a0300c1d450f03645d0400060380220200da01e8040c94840411030742c0f1110304421202c542e4008420000c01119424041240000c2c10000c000c2c0c5007010030942d105421006d810a90665140c0019410080403000032460210810249042030030303c82a40d054001401d001044580d6400303402440040d10600405884a10f00c0710140b1080003194000c09079a90080009a200c841c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 468826285 1250 468825035 468825041
    0xf161703130b0603120f130f060c020a0603090b0a110c0105010608010f0602060903030604051b07050102031506032503060509010807080d020d0203220e131401110f090307030b0a 78
    0x800c80300002d004002c210a030400045640c114900007103480c0c03900a05e01400d29150b0004a40800300c0c400b40e000c00308048904408140c0144400d0b1030f00002c0784920320412504844503000b0a0404d4070704890403001c1003004200e1504400b01c01d000050003c20015480040d10404801034846e40c20702000140080d1710030503c80c100c0d02520f0000400039101e490132615900103580d4800f041d402800411041c1c0b40980c03100f40c00006441c0800c1340e00d00000d40180c400c0d0021001640c1996005c070030402c3c10072141500c48500d9208030748180c610314003100d00f42c80481c03007141e44403c440000b000c8100610f0099006501603d8000c0200c40b042da920140f10b0345d81c101c01c0c007400c0350500582004076802800047e865001d061190065801c0486004408043c042105030748201001d20b1071000a1750b0b5080d0746480d0140c6813180005809007098144040d01d0701c88610a42e0b09a890103500c0030302241d82030f01b620208885400010703a03d90500780001d180c003401c1e0b080900321005035020f11210040d164 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 468827535 1250 468826285 468826321
    0xe0d0b010f0512060115211b260a0209040e0105090c030f061501120c020a1101020c060409050901020f21060f0105040618080607050901030e030f161703 67
    0x38156001e255254010300503150741c611400f0459520940050101c0d1000000401c0410f529142c50207142030001520141d0780131004601c9805542c42d07900c4110082e0481c1e0710804030009040c080a9050303030780050708411020388009402d2201080105040f841c00b501150a2004024020300c02e10f1504a1200d0003070000340ca891000340301d02c2c51003405c24180865017a881c1151705010305190340d224000e15440da007120510034104801c1d0044800c0c20852489051030060403580100360103100c030301d0000140d0074107010250640d48410101e003116034072402180c2c25036090500120307494403840ea8036400390180180780203407060302142c503c20380b010002c2003000c0084074400291180e204c0c0341c180301c0900c03206040c0341e0000e20108403d0210502800c0c480a00c10507801d00c0d0344005540b100c10f50304000c4c007690b0b600006000062032900355a030502549514500f0b4101030f5140107030010b400001481015401c25031401400b61400520202c08030003008000310b04035403039880c9454003039500751b61856 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 468828785 1250 468827535 468827549
    0x414010f0c030e301b030307030b180121030201110c0c090109090203031602030a0c0f06030c0206061e01022107020a080f10180804030812010e0408190e0d0b01 70
    0x1d05545105030a84804d0f15030086082815020804481103241400d5400070068079503034069030454450788117042000310700c180030913503001544021450410440160301818011600b081c0c0c0018448240001c1d101d818050203101a41c400c00c02c0c03803400340c0c0509000301d20050550004a140c0500c0940030842d0a04000101d81c0103029070380742c00b0300302c084032203018001c0c1d00b50380140804030243c03801049521415000034200c03070340702c480303940d401900d21540d401c0040303800c2080404010340764241c01140c01c82041070024084500d0300d80081002100da140441c040090b00b12400d5103203900a21010140d5207048000c82d0350701e071140c08020b005500401c0e00701c1c00b0300003201e80040d4030b140200c0d101c0d20201240001c0c10603985040d0394000605094080411050101d4031450005001c20700108015482070b8612078603074940d811000e002c11016400700c01161070a00030880000d4070f0804648084c600708280503100500c1210441b00448002c0ca1203802140703900501080c084c60050700b50480c2c101b = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 468830035 1250 468828785 468828793
    0x60c0a02010c140a0e040603060e0a031101061410030212090601061b0b06090a020906120f071b0803100b1611060a0507060b03010e031308010b06120414010f0c030e 72
    0x2507840d045802c0c031010203d40b0404801804190892403058008518111006002280c02d54072500c80204440b140803200155900c1200c0f00420181c10009582d020710010000f040218030740621402010340042c120b51196545280d10881c080c0a60b050b1a603040403040d80c8403131840c1061581c0d5840c4000e0140c0300c0454140360365004112022003075801095840752408050340c5034003051044038880900326145041e001d00030106991641005440c001100c00088005400c11010044004001408103c02c20841032010800c514400d2540005564800b060f41c0c0d4030781e98584050f1003501c903074010307000c2c040d000141141c6082030450020b00ba1405002d4070f10080348204108101c5102d03100391500414018042a0302044941e400341c1980213001d000801c114480304403190941d0300044c00614200c10564060140d50b074248903002099030140d591030302d001c84120314881c0c9484018002010301040e8002c41201200a410000020740b00000174000051528030140240210554120307103441 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 468831285 1250 468830035 468830051
    0x906020c0f1e1f022a1506060a0801060f11071401030e0c0109060c0c050d0c0f090c08040b061c050321010b19051c05040c0506030403091e08060c0a0201 67
    0x3010803e24044840c076042503104040400e03a200283d04070703c040803a14480d00007000e001801600c080c6240455110140c0800d81c070500d8002218080a4803060150005128081c042c6801481c9079054910310b00300200d402041220854045201c1480100140a02840010074245801080311001001d032428460705c6d45865107159248c140c40ba900b400100303540010030075540140c108004070790190752200c40c265102c0c0d0104410f0203d4a2003145c1d0300541480c204800015035800101a0120080c02d100010030100014042c60000d8005031806161201180f02940e862003542000664402c0c410941c4266061280c0c49400c82e200b8040b540004003801a21070b140303081124165049959040d08200c200491400c07d00808207542040c4482000861400c1161355030038442c0034004100885c00d40f400c3e00d4142381c1c5440e541c0c03109002d0b0006205000002e83c02441d42c5040d00e620000c410f40102081103201003a018a503c4460140104014016000700010080030152003580092000031 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 468832535 1250 468831285 468831343
    0x50f0d15020d1116030e03030d0e06150102030c07030b18010911040b030106080a0b0405070b030a1b050313060c021c0c05010e0a030f1101062d2103030906020c0f 71
    0x11040c0c0c84044c0c005143c1203040300001380242409112140090116400d141c10b400d4144210707207a01d00c11400561000c020499001d04400034070500c40c000384040e60038862101d24403995404540001080803203600c0004401030071610000e240e01c0750920091000c0d88260801180541441325913a000782d081c111884e0305c03801c0c140144022592128003c05108500b522220070210700038204854038010303480001000f40001d400755000c2c0001a0000800d05282e002000e02d840c01d0110800c00d004040c030403c404200d240364074094040c0c05c2000492114400710302241028100322a0015210300c071030705030003419071100030240a036104800070490400840020b5603100b061010090014449078269015284030708031117000400010300110703c003070f140c680d038201010603c1d003880340c8920a4030020700c40c00c0442c0c1031b00780100003004002c0d81020442c10060107590b00120040c05140d1604811020000240d04891060a83c03105035031440d00c010303048640344c92040d60001d45c0c903101340390840d40b44 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 468833785 1250 468832535 468832537
    0x1202091b07060203090106090903020607090f12081b03030a02220311190f090c020114090d0f090504060305070f1d070f0203070501050c0306041d0601050f0d15020d11 73
    0x320441201542010711599510000c3e61004003152459500d81d1b1002a0002040c0510b000c81440f82e0003904542c030302101c008010040c10b902c440404614520104090b400d03002c424515184c0002d4030390384e180307548402050030500c0d04420b070b4a80c1c8400002c001d00c10445a01409040c0b00031042241414600c24030000c0e80a0b80e400301130134103400111100c0c0340e8a4008110072012111001c0b080c006a40da9440501d08140d070b43c0400b00302034440c00800d50440d070a00c01c0b400c2c4002000c1000605046c0322203140d0f070340d40d02444941d052080d900d03039039508640102490002440c0c000c01c00e000940e22031400c00e8482c07481c0c1c0708046140f00780920205000c00341e1b4101058003c103e84034070390751b5603600c9001c80307a102c0d4164a61096000810400d00890707403e0107414400c1d03a070203175000d03601e080940078401140d4540340080109a40e20040e030030382d41c4000c0303015030440301c084403c6400201c400001401064100d60014500900c800501d501003010f900a4400030300c40e03100820130807805806d8680781d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 468835035 1250 468833785 468833821
    0x160302031203130609050c09011d06040f021b010207141f0b0a03050f010e0f0705010206010e0a02090a060f180506120c3106090e0703020a03020706020301120209 71
    0x456001000904441e0081074055030307011000c03006140207040d071601c0e003408940b00420162a00e401c4041415060b081400d5910300422101c02c803070303d00389440440d0303508159010b400c0c0c074425512101c40505049454040d2380c1421854032103001450a601c0940f4001c0d8010902120301260003200822903040c00710340e012082002003411649030643c1800d00c00107190715044103a0140c0030b2103000c8007040042010844d1032000d00300001d0001c1e251703551a498446042030304a4150f110000038080c90343d02048447c1142d4030418000d1054817090284e40281c0140d100741604140e610f400000c08940c001c41e03082140c80e80762203c40744c0e014200c2100400391894001e05800804c2000800e01620411001c140d00050360f400990500640105e000c103c1941754040d2601100840980540c80344080500c100504e00d0b41040d035107051401c04444e1503000024150340a01d0350118140301e010340a50100c5000b20b6010b0001c45d580d68680e03101e408042c090081c00e82c098619040010514180f100007651 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 468836285 1250 468835035 468835039
    0xf03040b07050408071206050f28021e120f0601020c130b03060c0d0c02010207020a0e070e120304051206250504081006090e0d0e22060603020c060a0603021503071112030603160302 79
    0xf8044551401d51490301c880a1022009079034204407030cd24603034050f501259034030011008650703107141010351803588010103880b540c10424481c003800444c0c2c2e00000d03040305403401529a030000000c0403c03424010302440c0f040b1909400351400b004524801803006080c00741800c001040f80c5401c00104a00702e00400600035080483c0c5a82400100030309982c25a0151080c502204428401d00200f4001c4030580e0203110350303078404a004d128a24107030f004143c030900080000c0c40d0501d861304003c2c4007008401c00c48400d294030f41d03042e2055a40708800f1500544040002c81d09016142c00504009044c1840b806200070300d400540014048086230100d0740c95815030328404c1c44400c0d40304001814100001d04005030244102c0c0d000c0340b500d5401070200420440d1401620380241c00b40d00c0f41003050003440a0f01007460f00c401880142d1fa00d070f00c0c801144a9000074240c603503440702c3e02070755483c01c80038001c14144200c05022210004000c001c504c074410940660316050b0901c1d058284408003400025 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 468837535 1250 468836285 468836311
    0x7080a180305073f0e0f060306030a081306030c02030910050c0f070b030a180804030f030309080c010b030c120c09131406010f0b0f03040b07050408071206050f 70
    0x500481d100b1005003022500480d4402c0842880056070b41d00c44c031402860ba013000d80f1803450807045042d4890003071140242c6040c401080e00c10400040c201d610824000c0e4818440480401d009480c20484c0181c4540c3c06809103075208868004030075810001d00c80c0d500000e041c04d0300c0e21649403000c002e98442103030182c2000c40c4c4c041c01711002d4400d6040005984c800d442982d0a00361000000c112070001444145103840d41ca082080c9154291034502c500b0346c0005a1a80e40d07030f03001800b6641200c0880b900400c2c955040c504906d0201c01800d8428400b030040900400c1344c105552066001c0070003103804a040b01c0c00001100b05114080c085810900e42580105064401c40e00b08030005035404610042080c200c5007255681100c0c07106010038102040c0d000b04014051000071000307041c041c0405c2c12140381418a6650303890031038800140001c2c00002c8460114030941d01417010f03500540800000d071100382d81c441c00c162a15003c8864262585410301340443d10310251401d507a030103420001981 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 468838785 1250 468837535 468837581
    0x11040c05090111011104090203041e150902030c0901150e03012c0a0f0b0a05091203010323061504050c091804080d0609060603201e04030b0f07080a 65
    0x56580d2200f031420500070795240c040074041302c4410b81c0188054890385c60016101e0910b402c040152400720040440030400140041c4081540500301b091046e841a0002c1001d403124800b00f41060344140810f0740000500001040084a501610480b144565a9900e0402c401c0003018203030b401000003d020100100c0b0000500100a1129407000b850070081b28909074466031000d1f1403d200c140e065400204001c1441442c41c0c450140e02c1d0040c2c1c01100522603070703e800d0005ca0306880184401040490085040c0c48107541d4a2487d00100304000247c6140e490086000101003001c0c0328134520892400000810007240c03003043da40250030180c15001c46c059030345c0b6a185e4102e0003401c15540d0a00910540d1410841409a007018241c2e290000c24031901c1e101c8054103550a0818500904014081001040c1c40e01d6059450800d007000c8500e401000e0400d100109110b55003029185140c2401044215820b4020081c010807050b92821400d0351049681c000702c4150f40c4026008007428a20 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 468840035 1250 468838785 468838787
    0xd060b0a231e0d03030b090c07031407080301140f1203042108041205030d0e011b050304201216031407060804030f030b09040b060102120f190e10050711040c050901 72
    0x90f00c108a00c2810001203c45800c40019541c880c02c46403041e1020f00010094209640071b000c20040002440d12a81050015a14000390307010501a11404140200d00c0155584d02d00f400c0c021803040c00b42ca4000c80c40302a04d00280c0320340c403078025410006290b02d0810804443e5031503466051b50045030444c105030070454003010907080c8a0041e6014071081c0140c0247d20501d04c80c01d244901c4000000404114600d03100f90804412108441404001c1c41003001141e4404851100d8804255444041e4032250300000c04180380c0a1003940544510251180c101000f40c82200580c1d0040c08040c034141c6000e80c9c1300d030799081c070ba000c1d090028104401003000640200c14a00001e030550802098202c0c0d840c000c900f0502045605980e0002e083e0184441542c0501901d11500e403070201c480d02e061050304000c6094454810f140e004111020030030341055100c0c0312468a00342c0010540580d900781d50310011b04a4000c13020581328203a2560b1003071082c1c9024070a50480030383c91b4036018108120900 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 468841285 1250 468840035 468840049
    0x5221817090607080409091208060d020d03090f08060a1503020d03140f0d0b100f1710080d050706060605031909150501060f0e03060103110d060b0a231e 67
    0x220180c2c10200503c2041c0014894a0280010305405c410000303c42540f402c0c900140e4110203000002c3c800c4500901900e078070390950003078440740c05039600411030850f46011030f5240d08030382c45070024850f004000700d070481c00030030010f00a0300402c0d0140400e41d01040507007913001d001c0c40000d5019000c150b0328800240524071450000b4000c04185007803440c5081b0b000c9595210114501c170142d41c0d250403544500d06170b04000c02240b031a180803015040c181d9400342040b05a200c200b148050703220000340d0507030b42d009504e0700905500010303104007140e1884054400d8010030300c00c44207103003001800308a00388904180c9100304190300c084080c10b0300180b54034004190301001a03425201c007086c0c902c82d100c024095140200980d40d00e9030040340c0090802016020686d100300c0c844d070442c00040000c1108502c41e42030120f005c44a00c180c1d0603082c60144000d1605e909500c2e00300e03010610005248502c00038400030802c3c01210142d112048004024102052074042d20540314144001121414074031 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 468842535 1250 468841285 468841297
    0x709080618030406110c0406120b07030b060418020d0c020610081b0603070e18100506030f0a05060d1a040b070f0818160905061009120b0a0605221817 66
    0x3e01071b035601c452028007040543c1e6403a001041c82d0342e52a0006020400d0701e030b81503903001440d858200500181400042d01307034030403440f50300141c03907071001d5240c0d40f5000f0b94103c2381002404803040041c0e0007109000394070b07084111421909030604c6400000c0c0c0d0314010400d05812a480c0c1c1c00e68002c0d286410400c07103244c1001d050a01001010319080c410781c0c807110300c2041044201030702d00540d46400800805041d00f036812213170013602c0501c00e2110106070001000d80001c88031801042c81d58a400206002c0230101e01c028081d1450516100300788007207091200d0042e80035060a0380c083c0e40b4240c095850224071040d003800038451900191000c02180f0f2486001420a41680c042c4444181c400f99440120b821018045540c0c10030301c00740c1d01d0b0000786085128aa814481c0b4108e150900015401c4600c43e006458903410b10005000752541d940030700c0260030001c00828100341c0300b1241c1e070a000c1000c03042c506034914001c8480c00445048043d8650f00c2d0b0310a0400c2101038101c0034400d9150041 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 468843785 1250 468842535 468842567
    0x3170309070e0c091e120d020303060402070303140c270d02010c0c0803041806241803020409050307020f01032721021b0108010f03060e150709080618030406 69
    0x34098000c0560760304254107404c80c0c1d8860298000c5c01060100100381e55010544a801d600141304034078a10740103c1902d9212204840050729042c003410f081e4042c20790030820100c074440f20310801141414580c054100180c161122181100c51204605440c25a02c0c000c0c55200c9000c0807284015031091070109182d034459140b80241c00d580e542503d1850704a07800c00c0c02c840c000501130351415080c0784078500c0140140330103c42d01014035005c0c40301e4030b0498040e440801c2119880556200d2150500400441d4064802c00c031911203030502640301d030081041244202d80e200c020359819813280c09614a641d03620380080300a01040062442d1502e2102e40071241c14000101c800055441083e03000301154460300030700610320028880980218010805605110310007006008600c1018988001e0760340c0110f0010701170962040c010b103011a0001c0005100ca81c2d0000c019405a000c1046811a0283c108440d0140c8405e403140c0311485440959118540c014031041142d20b11441c418070281e416 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 468845035 1250 468843785 468843787
    0x20403080912120a02012007121b08070b1f0b030105040f1d07080709110403020103020705030c010903090807080102040305061522050f070f020c1302130e0103170309070e0c 76
    0x328000320483d0f400420004001d40d540d1a1302d0031107144001041c1c42030107400d008592038482182e0302c8000e074040f001103c03c20400c80c0910f0021088030a072980c16140e400252113616241545400111030008030752001d48d14414404010080728010103000598106162880c1568284001d110041000c000301c440c14580310000800c103002c0740303880307000b00008000181000c54145009107242c1003030780c0e101030416441e04404c00101c038284000d0741c0a80781d09180140c2d494506040440ca140615103071440c46510300141c1204140d00166150100c030041001c1e510002e48c3d0384c056500301d0150303100140498010303400003000e86040583d8190700d5100100104001094544a684200b01c0101400e145a42e600c0c00c1c030120030b001004450303020382980380100031580501d20094940440403003c5004442c400c04c464404503d64050300c1b15182180060480c156480700101c0c149a07086c0f02c00c2e900d1000800910325103503012001c480c450b464060040010328507016090740f400e58010400c0044d104 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 468846285 1250 468845035 468845053
    0x120106030506011701080604060b06031006080408190804020103060b091c0503040e01060302090117070c060903050d0e030417010203011212090504020c010f1401120809030a1406040302060a020403080912 89
    0x1088003100d5019010900007007c86151a02c0d050003110660b890492261100740100200505552a0350058800c2d6103003481e0f850300c580c5402c041030700a142c1c41c80111480881e0041046600101c000d114038003d076414001d030b0743d0365070098442c0d1060902803504041151021680144a1081d1180f02c03803040044900c3d09603a89946001004281c0049000a8000640c003140e90b0303001c0c1c2d036a44286840d10000c1d07400c0c14003020280c02d140d0031080c004e0080740c03204526024076000e002990311f0f404c03c1510621540b41c000c2895078a81e4464012004440ba4840e00d40003002814401c1d01d05a5412403c0d00108101c0b82c1c0f82d01460000400143d410040c2e1181c022499490750700290440501810020801c415130450510070b6481d8070f005005420140d000422403c40b40c001402c4215400a06180e03980c2910b070046410400500e00c040c140066020091081e1400015a580300304d01a500b600c3d0552030380701058050344218800601310000601110009252110804000b8500ba80c2102d201c1e02d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 468847535 1250 468846285 468846317
    0x10c08220e094323010f0f0c0204060f05090a060e220c0b04171506040c030902030607080f010f061d0102010b041a0307050303090d031110091b080312010603050601 72
    0x120600ea00c3c4118201c001e4040003c4120480800c07104001d000210422101907070000308100004d4001d03c081240e80c0d171424030703e140180c400c4002c007a0080d1003070002070b403100c550303015650a030300ca81030044102c03100080c1d9041e864464001030316440295a02d9680742d09456003440c07044803000141014580c1440300004100c09a044018138440011603116850000c22405c4031701c031103c400210750094030701d0381e0680040c803d5903544000c0c100c4000802e290140c2c0f0403030092071401e8009401d403280d40281701c61940c04c030b81c440b403117103244480f01c1800c1e0380c8504084083e02158030802e408110000c01c0b0b200f600314050800c07140000184000946110b1560004058445001c8940c455031035054401041c0c2c10140402c4010780000d034011031030050404040381e42d01c0303600c540207403c12640b40407005010400340040004d003908c89405020152403420400e01e8480c418020401c5800f550000080f4071801006a60000c2e400050f601c82e640e00e0094268082c0000921641c100030510205040c84 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 468848785 1250 468847535 468847633
    0x11a04090c020a060c0806032512050a050613030e060319150302030c03011e020a0207031502130509041214090a031115040b1602010c08220e09 63
    0x1400e80795000701a50606400d2400448410003508400c000f016801c10200361800140c21501c08224541c5e20360310195150b40c0c00d04803069800204c450710507990011b0500800249800c41c842c091002d0300d0698035000d20109244442c04001070105680c62440100c924004c0081d40c0d00600c44007400074081e14104024080700c804c0c1640710b52a03101c0d10381c00d00560904201b85427800c88160001c01c0f8003d8041211603c1c0b9414140c150040c035000110809818401c0c031001d00156407049000d000300402e002c040c40a034225481c40e8101c000c0384000010b10789480946240559001409030700700c048000005c41d01c10303540b1095103060420030440c81000341c440a13a08001107005007484440110604104186110764065904030300034107020a011848010048510300840308000151072120303440113032020054294003400040001c511031070080190105000030210345000b0081d8141c490781d0385054640290b03844281980281442001c1c4a040e04062840800c00605145c09562080c030800358 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 468850035 1250 468848785 468848801
    0x610050310120f03170903040b07020402040b04060801080607030911060d0b100c17030106170a0f020313060506010804050d1d060d06172b030b03071502150f011a0409 73
    0xca00e0407580305a091503400017444d2824a60310490182c40e00300a0b072800c1e40c0340200c0c014096182c0c80000d07500115500c41d412900113001b0117a003580c40c1c580e103000140110341c091044071454010741e0005255144030b0312807006440e5000041d100703000316001c2400300f250882e0303200d10800daa1350f6406404581d02e4800c0940c00030a9603680c40a0000c45140c202c5d8000340180302c8580051007480144400303508800510322403403000c440c0600c107558030b1009101412507000f180c8101480003045c018040310030b4141c0c500042c012902400300351100f100460329100c04071409481604200042541513104a4130701c8844110880820806880740000542c00da1000000c0e10445aa5203c100a40340b006066146a1130082000d0000c41e8901c1c1005421001e016900300f043c5401d14141150b941e0203540134400841010b8100c40560b03841e12001d021036109110034401511900d25100c00e00703140c4100e2140300f81800d41150001e0303445e0091180c2c1d0b41d15000c12054020800740400329a0311102c1c455000 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 468851285 1250 468850035 468850043
    0x72c1602010c09030507121e0c0f080a0c0506030705090301140f07020307151e021909051e0f0d0b0a090c0515030f071202071a060603061005031012 65
    0x4000a121880a42150340c11400c1c1c07002e00c1007090080011070340102e0100b04031001c6a640c00031642407442c2841d41070308810307000740c49504d40c40700c240c041c050900b0400094034080000768201540b20a005c540e103d1000c20001d280b01c0856806210500b4600050340d04210340d070070908d0900f201d080c0001d0a40d4280101e078102c8401d035401300400d03860100401500b061003800038514283c2e5644685a02c60300b444411420b26881d41815588003205442e1410380310a225800c41d03c034081d982011044a440c0d005d01700004003100c10200c0c952600d000000310b145518104c29105001860502100d594040701d0300740c1c020107460411001c030303144401044c422100c40500007244003847c680b55000c0103144e00203d00424603800c8240f49420405c1c1242d400800c2c0c80c40201581d0b465100c1240c0101402041036692070012442004108000304070900e80d084150302d20f42c960f59001c0c1801403500049850b42d5000d8ac0510007200300901540045070000c000f00524040961100744140e0820040d2f40300326 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 468852535 1250 468851285 468851311
    0x1020d0e070506040e0406022101060512070e0a03060902150c0f0f01090b04060513050321220b0c0405040914010f060302010f14120a1b020c03072c 65
    0x5003092050014001a0408644640c241030401c13000314042c41c2d0091009105660005141082020110540c424a80e14200346d207443d40e11707800020016044008224018a081004501039901444007115116401ba044807441491905c840002e08100c07082641c0210310f00591400705850000100f0a44541d10000c2c070040c0c0400d0a0b0070701d4401045401c01550b403400f110200010301040e132040d0003031703085000404c0a0b143d400c0c52550074800a5001001440000354100790703840e07551010750070402620010001a03949040241c5403019100001001140c2e100c0040c0c0001c04051b80150441c0e42040d150b1304181c0c03a60082011100d0110040c1c2c2e440350004030103089040f0900444484540d070a80a010091460740040c01c0d090070f4800c09000c0c0000d8032881944901e490080e648200310446848086084c809480d00003005800180c0c4079154440a0b0130404600000311040310721001307002410601e1074007031141c1d8140c0c1049803080701075801172114089207145400003402121460b01d44 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 468853785 1250 468852535 468852551
    0x60605040e0a02090106020a02090c07060216031e0203120711071517150a09020c0f06040b160807050f0304080c060a0510290306030a120503070212090d12030e01020d 73
    0x101040390140e02090031980142c1802d801a2543c1402c0d82cbc01c0740c13880d0051074885c01146002d5010b030141064004895449010071020301d80e0200b050324884051403035900b0000d24042c007ca803244100e03a07198042003402c03404030364250721803481620703420190030644910303c1e1107035900d00c105403103001d80c40d00180c41021581c10300c80f0014041c5d50442000000000c883d80840b010070303460340b81c074810481400c1c1d0100301c0c03020078401400380045280001c801d80d580b0340703071515001009030740940f50305400c0820447d0303040820b801202820b00403256030310360130f060491540349030b404e0b54030007030049803202828400d20003000b40c1041018000ca004010200341483c0040108206200a40c0030101c1c0032000d8441208020601a6010400b8419440c0c40d680e6a10103000c01d181c22641322006000d410501d441410942c0d00101550143d00e072a400ea541c0300300801890404c40c00703100103040c1d1001c90202640e0004415400d6424031042d03900b40400c5900c44044181e00b207801900f252240707645c4400704 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 468855035 1250 468853785 468853789
    0x81503151905072a03120e0f1b090f060109030c240509010e0103020f04080601180b0a031e060e030c010204030201090905040c170f061611070b09010c060605040e0a02 73
    0x10702c6074865800d14011800302d202446210303c07202c3c81c000c9240e00d680c4030010042854452203403100030180c0d105041c00761a803003030a6a90b4401e16080740d401300b401540b8440c2da490320614021100b0368401011402c690b15908291220410080c0000d070610104440010010fa0b40d07802e680b000b864181036940145414541d500200d01f0302610031420840100107c001d16a000280707200455002c5c6001030b19812220b07803000ea1031185e900501030a10a1100001304041f00300c0d294810801074200a00242090300c0c05d00c8407880c080d00004050340c0300c5244a203010410800c0c1d0a0041d1b010303080100d240c07101034500ea0b0465100c200c00303400320b0750001024819541c201514100801035010104524649a110020782c0c5900713011302900d004824082d1400c0301c0c0e08000150001e500041074600b20b08024190752250070240341240c0100e040030941c0c0d13510032070200b03501c4100d9030303410341c0b142c0f5200407040111117200f01090304a0310b450f0b950300045000e450702c2c0b203141c600c5410100204210318807401 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 468856285 1250 468855035 468855041
    0x309031e1a010914010b0409020d020408030f0309100510030b041a0a0b011803120c2109300201030f060906120b1602070902071401050a0501030606060f0815031519 72
    0x44d129241401100400000380b09000321405c42e03000e4203005844850340861100642302e07592051800748004a040c1c0030000725800114014801c0308121070181c105079051805407141200d0609040500c0001000130840d28600c00b40e01a11170441c54907030002040c5004074104042e9101012207540340304c806403950b0050340c4c00c0d5031004d01c00302030302a081c916517821032810000d81009003005150f28610003000901d8007406400c3d80c0690220300340700d410f02c400600100c05840b550800038251a07550140301c210a00b0800f103801161300c00981c50001d60010750103018602117034064196680e00000b1480340a10890000d07024900c5c030300c071183c8028146010f68560151a19055402d82c4a100d15000e400084a1040342c070f0420001d40c942c069410140e01c40c800c0c204a404065080004100188100d50701440c1078034418401000301c135403240002ca40804083c5947c8002ca04250082008041c080c030724600f0040c80142254000500f825100d40350f1401603d140c507020348190220501d0b142c0c940 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 468857535 1250 468856285 468856301
    0xc0f0c01110319021c030b0f01030e0a061a19030501050a0c020a030c020d1e060e0c030c04020d0e010207140c031b0603041103030315010305010e040309031e1a0109 72
    0x440c1c240c1292a46184035030b228411054140d014038504501d0b060307820b0080c000d15440c00800041c8866031a203041000d409081e01c105c80c1449a51a09060302c00c6600034802c0d505002c2c02c1900034401c0801c6951100700424150401580000c9850401c19440e40c2d84c0f44c01810924a0307803d401a000d10310716009095400c040c0cca04003060400910511082e4005030740301c4400d800d0720385150792a4150001c070f05480590b2034081c103001c000d0910b44040c1c1582c99150074101c1c0c4103c4003042110b451101042d01c42c056015001d80c1b5070850403c081c6145007540140c60112010080001e070025030440c0c50782260302130081200c125200b6588021444804d00c400c41100105038003030b1401d07003c000030152242020320b00842c07041c5000b001080501c81451204003031814060111fa03900c0c10314102100108001c2c8070424000703803c000000c9810a400e5280500030396050310782103081c070b0030b598407102a100c3c84001385402a010900010105e10b000002c1c8840c0c200d45402045c4070f5041110000c1920300d54 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 468858785 1250 468857535 468857537
    0x3200f04060b071509020907210609061806060516060b1002010b1201020a080a09030c17130b12160c0f0804140f150c0705060c030d150602250b0c0f0c01 67
    0x20202190158440441c1c03258090b0312884c3c920044127050000e00300320185035aa8003080c514100340484c21401d03d03800340042d5945d1344400700c2c5040c0c5140441d13040d140b05001e801e00290382030042c0d08640503240d5012550f49d2040e2004244030071601d011510700c13441d03010a40c0060703440e400403c039541070442c0c0311461b070b071101e0f4000d42c0390068142c00584400d001410108101ea5640581c1e418588103190081701c540d0b22120016501d9101c6c03050900e20f0304088140c211811000c0800900c40d001a0104e4885070038501c031142c1c89035a0070510f42c03502c4818400e803100f4042e09041ca05c00013013180002c0119241301d504404d03115801c05806200309121220001d00500743d0a200030300d9641e603010810400c000c4c81c6806903070b4100c1c4801e03c42c24005c0c1c5030302141e0011804a1081a484404406040d000c50b544808000200018402440c125094420301000d03030405250302d680c0f001d2091110b4040954007048072500c039640d268400c026031100440a41c1074110000a0080641c14060b4034401c0100f = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 468860035 1250 468858785 468858791
    0x50d080709030c0e130f150510030317060303040f06050a02100218120304050a03051b01030c0c061515050a030e120d0b0324011401020703200f04060b0715 68
    0x9560383c03500307005800e0094581e44200100007440704030141c80f07040801580800d040d6100c0303104c1d20304800d0120705510801c580c1400d22000070501044845003230200d83c1c1603a6010003502e50041c1000c58000090826034040c08200f10100b4908070005107000100210355855654802e103060003070038a04406e2111074002e00402492030b0402c210f40b0382e592105021900344060360f1164001030300e544640c1d0721294001400c9140003003030040116a1000e0100c0941030307030304040c0c40d000c011002c940d0108101400704040e881c03090007043c9a60300c4200c0000b0380040c000d04958940c4d00c0140c040040c50f01d0741000550000301c101d006a414045e0340703800300d0340d01d0080030494041c0c0445800c501071942c0c9400300981d980c0040d07030320740d8080210104407a41018803030016017800402150018090280002d1000a000c0c180c000d03520000d486003c485d0881c1c0d85481d00d103503005039180703000042c5030340c994043e010074041e000f16941c0e80b00b0b40c0000c095911440e0390b18005442e240c3c2c034840c00c10b40c018800601e = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 468861285 1250 468860035 468860039
    0x4030c03260a0509010c0c08071a070203061f1a0403031d06030c0901052203050706080717091c1d01140f09030a06140103020a0b07150c020304080109050d080709 71
    0x25401c00e41c1c10007906400c1c5662181c10072401210301c901c440c140a0198556810001488200410a441070300e03580502140250220368500119200d4440021b4150b400500005c2c1a510403040390400003d0710f481da034502c1980e4682480608452001e00220468001410002c15070055992000c0307a4200306410a11050000060480e01004011400f803100014182c01c0c0c1d81c0c400c0301203a40e8451100016180f4400c440100c400144143c001160783c1d210f4100041540d5004205080c41003204e5a5900011018030306d000640b1400644440100d11810529141841091840740f07441c1031141d40381511310500c0843c0ca155070f4911581d85040c01120380b00c0c00c0c0002e2000040354543c42042010969a0342e01c00c0203e450401d514001400c41d628202100840c41040d10060341201c0c0225036402c0c1e8207484000705480780c403410400074a05480b9a078440c2495034560085100c11500380140c0307080594a0a00a007076070b030f4080d402c442c02c0d041601141d40d102c2d0440f80043d041440c610b030241e07041e4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 468862535 1250 468861285 468861353
    0x180102010b010c15020418150b18150706020705010b09100308121e0903090a0603050c030a0906020913150806041a1005040603050c0906060f09010503040f0804030c03 73
    0x3004075005010099221000804c8410784e404440040c500d02d10140c2000c105c20080138018021214209214019048006054542c2e42d0589070504440d1a08002684041d23007042103d074107024142c006000144103210104081c0e101401c07030030b03025200110b490019802008035100300240300c9401c8011b000801d00c00f150a941c1030f2401070340c2c0d419010080e034075584000e219414005250303140e4002031404001d06441d0100290540b03401c213681d41503095460754001c3d401e80740d0072500112054824000110304180d6a04500d594034060780e40103281051703d4011402c5040c480c400b0702d004a0300c0702c20000c000158070300a40010705401020f44160700300341c1c1c3c80403003881594000e441c0003800d440110301103c1d0340046c01e10081200800c1004074607904e189c001e0b1682100344600d031150750140c0024015040ca04120344039205862071052903d1811401500c80780c201400c166501c3e0b04010001000032178003802000a1070203442400d07030b220302e103241406444001c00000c070300400450010445034 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 468863785 1250 468862535 468862547
    0x6090c18052205040c08071206050c16030507030e0603070507020a09111c0612030f02060a051b16140102070b0a0c050307270b090406060507080406081008070308180102010b01 77
    0x2e5054100840c041c1c8441c00d081e401600a0b030844c429602844400190b6145200703565034084e48607040c140469610100d03042c82c54015010743c038440031203a1900c0c40000381700e940100307001d61107420a0200d034140c100100d045030300202d0350f042c0490790004003e8150315100d40f01c10000e0006010510110001009030354450140700411000210445070b44808200940c000d08007400d2081c81c203e0411010b8207000741000f03200e4000744054011071020851000150040601c03d22801c0090541000501b09450460f4000d0442c41c0406202014000c00118650b201901e4007a591001688581050401c8030320f4a030f0180c04020528581110400310315040b5043d2a030084060900000a2040401d4030707242081c1c0014844040d0b0050902040001c1c880014010121055504005a68550714152002d07c1202005041e4810602003044141c0c400d0f1103a59100c1c89813424505032680d01c076619440c03c81607400c202d441070000304110b800641003d09036040004244000c0c0101822140041d01c0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 468865035 1250 468863785 468863839
    0x71b081e0c0402030603070305100213150c080d020f13030606050616060f0b1309120903020a090b01091703040603050a2702031207030e100f080109020a0306090c1805 73
    0x20b940c010000a00030364003440136400554102040e00c1405034101c06803402940a8007007440b010080300c3c00030034414820108100345107440d0700c0f800c010700c880c1e0310340c41220303044409031000041d02040100760840006002c0c01d0140300d0512464035541c05d610f003200c1a103c49400403401003500b0701c5995401d15503c6e004802c52a00107a0008170b040c0d8803c1c0c448040d09910354015081340c0f03800b0030105010025402141340c1400380c07004000d00c42502c0002c0350150200e10010754081d6807104144140d9003035912400000e401410a40000c4d0381e1524191266540854000711a41011070f0400c1100c1d0180100d82d031190480c0d0303040103c00440c201c015030540140c508940800d940403924400c5440811028030790f40101500d05844864500d001000c030310b81800c090703014215249403207480d1401180004291076290704c0703c0201f42e003000140e100a4001180030010503881d1040020b003c4c6092003840e0345083d065a91000301950b0714003088000311a0340c415130152100b07400c7c0e481031602c0c1244001e5 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 468866285 1250 468865035 468865039
    0x5040c110106080f061503010f24050a0612050a0603020a080303100b0702060a0507060605060c2b080f04051903050d0b0a1a070309050604062703032102071b081e0c 72
    0x241c541006e00031900500208076051441403a142030144208214081994124604d00d0b80c207403803540301c0c414002c81400c544121400b00350b0311405110a01c000d60003c5601c1515520005282560f07900040c14070f0030594042d24254100005004a80329034080074400f0b042d1a80380c1d41e01e06180f03640461014420032050000700070340810f1050810400b500304a0003448020070084d180d140c0c1d98250340c0c0f1000311304c0d900f0f401100c54440b9502c8001d4002608600c18503a81c032240c0c850f50381c0c54600302240303600034811181070044001e013101c407060105150b1040c03400380c0d5803da290307807040b840c09044410709040c02e031099034818000c000e0301c1d030102101c184042007141080d031038200501d02502d80d0f12040d0007003540b1040110703011410980c499441c004010403142000e000c01c0140d9038041034484bc6000290020345015081000d07030554540351160110310310001850302d0f1081e00c49010b01003080c401c81d20f85503032900b42008203003401c000c00d41e10340d0724200111503c80303118841d0580d0386134400341c2a4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 468867535 1250 468866285 468866311
    0x1f110604030e040c020309030601140109080c0a12031b0c0e07080610030c110a050f010501051f030c0c020d0506040302070602032d0c0f010c120513020d050705040c110106080f06 78
    0x441068424821f80f10341c0100941214510b503110300c541460a880711443d540080e5030355000182e00c41c4001281403d040c2d0181129503400e0a2a15003d020101c0c4403058082c00201004011081c00c444441c0f03100b44c3c0110203c0e0800e40c200280b402d0f42c2e00c00134001c6400c001c0210248000f030350b1070780c500401805003801e0024907022401e0081e10b180c813811410300c040c0d004041d140f001b480404503074080400d201030000c0042c0c2ea294000c11002280780001c40b8804908600001c401d10300a500065502c0e981d402c086030000c0c51a40041d0410200d07940c100c3d0303580c00c08814401090340400c03081000e1316040c000b40d23042041e030404030070486400307101d0485540401100340d9130b500b001004554031051500b0691704030a00707031022240a400004681000202003205804842155105260080125402024060b1126020040e51100000081d5880e0280110001d49a542c1d44540201003500c1e860f5a0701d8892070f1400c160231a1030b00d5001240c150402c00c1a5184018041640c1d540324200300350035 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 468868785 1250 468867535 468867551
    0xf0b0f120702160e01150503010605120901060b030406092609220e03040e0c0f0405091005061c0b0a0302090609070302220306201e091f110604030e04 66
    0xb01c1c41c01c61200701082d541c68a004000c20710007840714626050395000140d19100f0b003030a21040700c203844240311f0780e40040e105020b056051440c1c81001c0c0d8011b4a40c900110b00aa121102d80c1280e90040d10112010b6035104d40d50820400c1070040007485c40c02c008420907801e8203803160b10b520382c07150f484114400c0c07200710b400010304690b400400c0202954107200300001c1400280050342c070340c0a405040f143c200400b0014944c1c0b04020b04440d502d204071501076040500e008280800c080d005091001b044800b2040451551036480241c003942440f0808004840149040311040391203c4502074082e000c0031000340050b840d81c4001f03607000304041c1d4000305a81e444030b100710000d0040c40d0044190480126089044ad40d94812100c180c1c1d0185404003c9050401c02088564172030310b05d40c0d840a42c4c1032040307094001c0c03280480b0000b90102d03542d05107840c0c02440000d003000e5080300000e0740789081c451400c0320030b81e000d120071500f40035440050101d0704150302e000d00b074540c0315444503110369215054 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 468870035 1250 468868785 468868787
    0x221040816080f03070818031317010f0c031a010e0619120f201206130e07090203010f0f0f031101030605030118140d080a0f14010308040f0b0f1207 65
    0xb142c100c050040e181e04d4490074051401401c0d400180c641000e40745008542c00c00c011004801c035400d040501403940c90243c60700100c0c8560006262020300c2c1c95598000210034020700d40554803108074240d07400681c012495401c0c26804071035180c40c80c100b006104c03075041580c44150890703801a100b0341032900001c20b0032604441051006400001082c240059292480107540283d0b444c00e82015007418810b08111150504c1d00900424040e49002c000c00710f1803600700310701c41e65120304160402207056840e402d601c5180410036449460310b15800401027003604401e8030280c000d882203902c480017403413030580f50307003002592030101408640350350321540e800303a0085c3d1100000f00340140080c0038500d2101c00300b05803070684071401d4611002c807000d0039001032804900488485041d48580b07240340c480c03000c0400101210100350b00140d5a81149240f94030403045610b00844c407400301e1558540c10811004541c3d01e0503403040d560032100380701d00d081459035001601c280d590384c1a4590b0b2540e560702c40c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 468871285 1250 468870035 468870037
    0x708090402090d0f02040f0905030a141e09090601020106270f0e010c080907060c11040e1204031505070503010524040b0c010509071508042103022104081608 69
    0x808154404a01c0c41281c013048411180d070702c6894000c5a0030007070440c00c2201c0e4820340e6440c0703100030000c0d0000c0000400300780c0200140303c03041345000c102c9802c041e0024044134080b10101c1c28140340403c003045e42520f62501041c1103034451401e1000b4403450b4038024044400300b140c82c0e1088000b46c2260450700505070301e5407003544413020303401050020303203a107402e554003c0005044d2100000c5c1c0c8507001030140d5800148101c1241c4c070710741c0c94546c40006130f00c40792520008000754980c4a44c50b540c1c41c0c0c01c4440c00700903c01030a0381d200071700303a074032817440c5024207902c010b24020b1000b00f802c2004002c00c207904441941d04640056401c0d00c2200010302d0102901c8008072060140c80c40b01160105410424038042d0400d601401d000f0002078450804003565000c2c3d074031907880f00d079214050000c00c86216107200354009105048083d880d2000e15044c07454400e100100d076001a901043c5002000d142a644140b84000071000d2419404c2c15104c500c0e42e445100c140c002c10b4020a9a030008000c0001c1c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 468872535 1250 468871285 468871297
    0x1b020319110307120314010b091c060c020609070e040317060609030a060501090f06030209060f01121e14060a031103070317030105030c062503090e180d140708090402 73
    0x60569944400034034207901d000d840706010100003450452203e12001b0a01c040d5030688040c02d1105003041e03090340c2000b44018542070151446595030350300300002072040c001c2c030340c0184458000d801540f80903280f443c5494110b0780b00030904900e00d02072101003908400b09520401c03056001d00c43e0b0707646030008a1040e1003103000ca83c0d0944640004d21080c411716a008034180c4100b401c2c14409036884801d81d0040d6005408040d5201e100c44011a4442c07a0a4800703401c0c40b201030500c00141d41420700804111040b54056080c00e10005004c40240340c030f00e200d419140740c140910380040b4103080d00404d026800c0ba00008200310b060040000141d42c1c20000040250340c015041c0c81c2402e8404e1000c44940c00a00c0742c68064440c203001140c0724508542a030303a052841c00011300c000481a403840c2080c20080d0004c0e024000000000700d0440480041c003032103400104a858002a03041142d00e14180b2803181e52010032440c0c00c0300400e4000d159044031280c1c2c0c1c015900a481d2681c0c280064001d126a03 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 468873785 1250 468872535 468872567
    0x91b0405100e0a0516030603051009020a0b04080304030203010f020c0a1104020d060609080705030c011202250515150a052b0c060f0e01050f0a031d0c041b020319 71
    0x18000f00081074541d50403452186624118608800d0801d00d810f4040e902d080c08000e0141d000460340f410003031840e0b40300d8050700d800205210102507946908049590040c4c10940c0c41d1f0b00300003030030700560800340140481d001d540002103140400807060991185055a401020011010700034512607036142c05441024005e0401005010b540b9a030207040ca2000344185601c50150341700004981c9408540b1509800741a1140c480c2140c0312510310300203502a800000e40e5a15088800c40841b1000c919900c04610880062008108400c60280d071104010080b0103400b40c030240324205070304c40304c000030b08660003601d58545054a0000d402842d81040721100d03600c5400050300411700552103d01001c40304144c075400030238114014101d64225031f05898a0216104000c84014010414010b0004c103142d458001240e104442d860b00a405545080074000c1e408820303450002c0c545446072030081d0040b01181c6200c00c1010102039207034043d48403100ea00040c48100f82000c0c40c00303021030030080490 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 468875035 1250 468873785 468873809
    0x13030209060f12070602071d011e0e040f02010806030a17070203070e04030903031106010503030403020f1216051002030910030504030c0506070f031404020112020307030603150c08091b040510 84
    0x191040f590b507500507803280030010b00c0341c030000190855051400107080048440c01a13074580c20b00d80c0e0b20303182030843c490290f617180800d02c0c0091040304685050340030328807036000700081600234000184141d038080c01880c880e40003811114001240d11000040340b80b2810010f41d110071260001038205201d82c0e01140100e40c4c070004010405500443d02026a40300713803500c044a46000740301c20b640e40400d014070354160380b04100510141c946010f0701c5d003807c1da005065025140b091f600d030b103080540200840986580c00c02d8248075500c0c051382941e000080510056080a001c0300011b21552020018101450f540e03801103014903120301803850f5100d820400300c44660510a01c010003110700c203c2d5800009282030701c65241d40d40c07031900d414050b9030143c0d0f07034007100f05003903105100a42c0003420b98824075a03a040000700041c441031511000c0307080c0000016121400b00f20240225100800c3d8141d40e0300304001411803080070f2000300300e042da000e8600060300d41c0d03a11180c0a03050446d411410207070342 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 468876285 1250 468875035 468875059
    0x80f0712051e07020307110d060f020a0e0f0102010903200307050d0c02030105060409020d030f0e0a0b04050a0902070f17040e0901020a02010c0f051c0209120a0302011113030209060f 80
    0x11408481442c0482421440566a529000308980f24020380f0320041000f49810340d8030580703240c41d810000e6400d008510000744003030601c41d80c2c0d0490f404907204c2d601280c2d980c1280040751500c4c000480b0085000c0c002400f00c485a03a0b802080c2c2001600d0401c61800099280b040301081001981d040507031250844191000115001d804035210043c01c81c070035800c020010398142810b02582070a2a80900020b40585d0150b8065480c048403140200c02c100c0003250007070740e03552440391140041804612060352390b0304110510680c030b9501d811440313070b682c010031030400061040703089110155000700301c81d0058800125004490b01c190352108800d0f10843d81401034212040d8018144d154103500200008035202c1c5050718061030352805070300461030a00c0859080a0070b2001203035003100780c203c0180390070000e80c000f4030310003050611500c080c1d004999030b00030142c0910626441141c600101342c2400c00c241d02c6021820030713a0100a00501c0c019002c20300c282c54a03408091000c0d001008546801 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 468877535 1250 468876285 468876301
    0x1120f062303071406180301060b0409050c04080c060c0c04020307030b030d0212030703020901140307031b0c050d0e0f0918010c1e081902030a020a140901080f071205 73
    0x5409485840515601c0d1403480009182c0002c504003203d05021010719030300403031400c2018540004032186a4001a0205400039640a10a80028020860900c0e4490b41061800000c80d0300081035840090300421090041c614006045031551000721080c030b684003040058241070000103020190050f0020043c001171039010380251190a030142c003192502c00c0111000c03a40c40224109012103100108042031259109070020104a1418106074801038603207840402c481c1d0080790048002660341142108202071071313201c14291349440c070b014842400c41e5152143c40f0060b03800d00ca4240040c1084100c4241c41e0000c140d10030b441c00804a00f00d92400126541000c8070301c0d0440c7e20b075035107001b85680c002c030701402c4680c40c20040c2000e0f0070321410000d5811b560044019084072440b401d29800041d512225000440c410a8000009615903207110000b40c091502c0e030150030314545081c0180340150340d0016510b54080780b04045850b103030b00e5500068807000b405030442c400403070514003040451 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 468878785 1250 468877535 468877559
    0x7020f100525141903050906070c030503070506010f0b030718080f0f061303050316020c15040306060e06220b060d090507060e100f2001140109110901120f06 69
    0x401d000d4448021441070f0320f039007030383c40d071021480c3c40c1e58500c0500c0501000c80d1180003c0c01312060003816143c90102c1c2034481c910b148805038411510b5a02c0014884101310090201038010401a1990781c0c0c46400d1000e501080e000042c001400c01c00000510800318502c0e08041c802850018181c0e81d544059074041071311403040012001c40c1c1c1c46000c020904c1c9203000702c0c3c03030024150542c0d142401d40d10b605508000d89900d45840e141144540c402c02070003a0794000107685482e40300845507984900e946401d40a4400c964014030107280707041c04110540d141c05c031201450401d25602c0d4840c40d4104007024004091346507580b1380201c0d01140e1010756454543c020b040c06401801101c1101c1c0d90b406080380d1502d060f90445e07800051544004074064010f01c440210400356041c02c02e0000700912000075110714280c2c248941342e4681003040190310744810035901400b83c0200c1400004922000c0c102c1c1032007141d101c02c0c10009510380d825882205503012600d0121214404e000d22070752003c640d110 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 468880035 1250 468878785 468878857
    0x9170906070f0b1623090a0803030c0c010f02030c0f090d151d06040503040b0c010204051507031106090606011b0203011b09060309020913021809100e0307020f1005 72
    0x14135001c207904044101d0085000380e4904c074003607540c503001c2c00c02076600d01901d80218441e19045108148007017010038003400030354800c1101e07801403501c034400d40d18054252241641c103420210705c10000d210541181c101201c46541041d0f0010759140e401c0b0000c144d41d1444100054290510b0a0148103e082150001d005560b402c0e09940c1c52641203460985d2501000d54000384103900400c41000f00c040c903040903100c3e54000000040c1880d40e2032011865100c2d260418415100c0001109402c0603002072500d4008044000100b0341c030300d40118002d0f5a1a0003808845c1404224a80e10107541d5440c0355013002258098002c2c4004160341d00441810011440c0d20404500a0300300400c840d4840d1207030f05031704c039001441080692103540b50110a4150f0401c00d83c4c220f0000c030305a14080700000201c41c021950100140300403c40903600c40e088903410602400d07650410082c290259450190300903c06508494542015a2403407050741e040c415080c61100001c1c50b001301900b164030038a0f500301d03 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 468881285 1250 468880035 468880051
    0x31e13060608030306131119050c030d060314010203040c03060506030a020301140124021b0d120e01030b04060b04030b13051b0906010c1a060102031b06011809170906070f0b 76
    0x41d0300c50300c6e071014151104906104030304201408105c0303101c950346c5404e6042c40403031b00b4800d2503e0246610107003541d2000d0080011140c45072020010460f2500440c2044604a80214203500b45036541141d80c542e44c1c40090b2100d5100c1300400c0881d90140055030300d09074028020002c6a18205030107540c8030007442900d005948e404201110803c201c002000c886407070303038040c04503002c000100244a642c002e1080f500003003000840c03c0096448044070703402c5a41a00d0b40301d041166140010252080030030098007440c01d00b101001745031251803d4a0a40340d002c580c0d41340e255a481111075640c0c50121b03000e85244101180d58240006c0300001460358442a10729181a507180c0340107407000103c1143c0200041840c81032010031585a150081c0c00c00b00500c16685801a05020041c4a10b03a40c40d050b6600e400410040000782010440b0240d60005080b05103d02000e503142e003132400d00c4900795150780c0c200c00140e1090f0341d030303c440840da525503004003200810038050504003154002203400300 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 468882535 1250 468881285 468881299
    0x2c0a0f0f03051203070c06200309100b040e0c1c0b0c0a0908120304030815030706031e0b0d0201081f0b030a0b0306060f011211030702030915031e13060608030306 71
    0x10405040104e034468807450300d1302d4007051110703580c50000b01414624502c66078190b484510924050318011070180c0e00a6005142e00e4240700199000c44042e907004520a80c50503000300c41240c000b0407903e0080c007040301c511040c03100042000c403040b00321b8a00141507283d240c04001c102145c3c0d201501e8582510b5503140b040715266401c3c240c6d1f91b0b0000c288100700c074005000003130000b4861106140e0208016003801021000640400d06d00720207900b001001c0707522219a454241c09074028040c0b220a05070041c48012041f0004c1034110702c500c000a81005481c4c1d0018002001d590701c102070240460010f40c0ca95603480206203043c0e04240c82020300141081d600c0f402510b000140309000e000700402d00e03420642054015248424011101d0300c0d02c50b01c80d40c061207100940c03c040c40c41500241c003c0c698400c0d03540104032000c0b524600d110721011090050091003a00c42c008500e801106010000c229294003c0c0039048075405080105038908081c004190580040040c40c01050162180 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 468883785 1250 468882535 468882553
    0xc1c091e0b1801020a05010906240302091f0f0303180605130e130506090105011a0a0504050108040f0209090a0b0a0e19020a0503060c12072c0a0f0f0305 67
    0x80c811451907031081181d05401484800ea03506481480ca0551241c140110b070a110426a40c03c1d007914100c80050b507003e561524002c0005103e500e0040c01c2501c00101c0c00040c2e402c681c0010303954203000e4900f0514103408007550340a011180010005442000070a00e02c40d945c034600100a22461101007100d20307550100040d201c2d0080e4155442403001141005026040020103d4281c1d00280181060401880d0460210b1410702240340200c2c0102d0012540e0760605070071540010051302112588001001203d4581b40d000050320140c941c246091b2a26031214241248007084a0002a41c490442020320140d804002181003a030343c441d640d685039a0b511080034408448450703070601d10640054400c0d1103d4008102010a054401800e00c1d8130305071204003217840d14004451840240a000400102d40c401c2880d4495004447c0e241240c10101c2d6060003c804200241c07030b0401d032500140c40071409980780d20282001d0103003407030a80404c41d9612807081003025140700954281c000c030400307 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 468884892 1107 468883785 468883829
    0x31207050601030606050d08070f051606030c0f1e0315080f030414060301050d0201230c07030c090606140319060e0609090c0310020c1c09 61
    0x804107903066144c904100e0301c0c0c680003030f4440c0d813410100300c0028988204440400d9441000022003290510344030b440c6c1040c5040102010022580110782158180c0c04030b4513007031131f03561184000ca52403202a510090f080c2c0e000c100c50106160a040300500a40021100080b1821703545081541d0b07000c01c50030400340010321280754100241c100030040b1070b03950445e0303007100480d00711389594503101c0014003050107000d0003414030042410b01d00500d0f00110410203061006007030b032603032041e008038039544510031804102c49000d01600d01082c81c203001d00c00e40c0c00365003041d1628076690851080c080d4098100400702d414900b00034401d41d17003d104502807034000b0640c40100090703a081400400a0111000f003201d407041c0c0c000c3c600c441c410f42d000a0341086280c1071580040c3d9994400c407000313003026440c0034100852030030721200d88107142d4003102c52403c03200c0c201280445d19141d216 = true := by decide +kernel

theorem cover : BRFrame.Cov 468705035 468884892 := by
  have h0 := BRFrame.cov_init 468705035
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468705035 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 468705035 ≤ n) (h2 : n < 468884892) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
