-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4488
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:46:51.401401+00:00
-- url     : https://prove2.me/submissions/730b8a0d-f633-4bca-9e70-b90092753994

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 807014388 ≤ n < 807194244 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 807015638 1250 807014388 807014399
    0x90b0406050d0b0405040b070e01030e0d03110702030105010b030a151202010302070c05121518031c020903011815140a0e010902100c1403090a060302072316140a 71
    0x1800b0b6030391100d002041c010011004501160400c441c00d03200c865516003400f00203070b840381124031080000d00c2e0500c002d544800400b500c543c50610018103046c0d440034078040c66110031082e204856002002080f80e580d440102100f0703540100c4220030701c0b51400808600300c1c400c2e51801c00540b500d04e4031003040c080c130aa00550080d40001c10550b44400c218a000500d50f6a216800030b0240004000d0840341c514403d01c0d0f40c0c1c00d90090110084084446901c004400e00003098946c0080071a0301e440708030050110500003441110358140d01542000f24901808040c902c402e5900c6102d030072448071144034190101d046554103114440884101000304290729401d42007000f820101400004603445a40d0025104c2003110040c030000c24401d404034011b01540c03842c0280c1c21f0307188001540ca00f20391800080d03811019801000c05141e8042200300510200070b140407403100c3c001d008001e000c0720707001950342e0b00c1041400080d42c4030041d40c408928485007010400102c88043c040024003400c0c903 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 807016888 1250 807015638 807015647
    0x3100606080403140d0e0705030f0309090f27030405120a0b0403050c100f0b0a120f0f032106090e0307172d0309010501050d05030d0c030213090b10090b0406 69
    0x684c20a004400c184505007002180c0d109000c1c000d003210008000140c1f1b81000d05013041c900b00d110b8440c9410601c40c3ca189a11082e002d00e40c010850f5191140e20b90b580d008081c150b00c081d251818982812070070004100500000034000e80303500701d4076050700c800c0200d0070b030b0fa84407040790000f00180d109201190000f4015406881d0380c81c4080d0030b80c0d000c10a218001d1089502c02100740044a4460039010080d0030207908031000340400d54041c00f881c2c0a5600d8070451401020b000508954100d680c0c0c1d0103052107042c02d0b40c00d0a0010341461181d00441040c030000d801d807030044100640c542200700701007950010407240c625a00c80784442820040304c14084281c3c014038175500300c085503403c901102e01c1d030510003856030001031070b48982c072410701400c0a0b0031140140c1106006581700101d0202080c0004291020101101c0c00402d6284011404802a00031082e09801ca2100e56402040e1a02d06400024848400395000030001415007001c80348201e0b540b098103c401c2081209100c9548913 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 807018138 1250 807016888 807016907
    0x100c050a03110f0711040f02030f0103030e0409020409080706141027091a0c03061503090109080c0106081b0109030807050102160b16031e0b0f0904060b03100606080403 74
    0x218105030f0800030100b800d085141d02050045842c41c941c1c030480e08092511344100d4102d180804811030440c03400b00502d44213640180000b60500c012003003088550358860b08141802c650240c0b051104802d00e1410304410f8101040031a08d081c205000e400444043c5140c8a01c0348001002c44580d01c3d00e880d200d002d9491080401c1d0301e20800c01e0380c0c4a10080b81134040e0008141c4226441441544951561044008003810a00c1e10748000c0007400b141c1d640e1810100030700d048160860b607490312400340c82401481c054100902007600032071401c400307000640c0403904035000c85003503d03500500c541001000304c2e2001c00144c08150508401e1012075040c1c00039140c0a841000014035001040d4007078013900ba802d4070708450100305141044a04189041c9500c09803e10341401d1114404011016520f2030388189038400741c1c7c0c2d8a4551140e1507403107000900107240054003d04041c2000d0400c075028090b8002401e000e40f2a11218402202e0248035842c1102c40381e0703541040c42d4859135070480c0c01b00b14 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 807019388 1250 807018138 807018161
    0x110f0a0813020a050d08040e0c09030708030403080307030e030c010608031306030b060703051b120405100810053109030807050f03071b051605100c05060a0504171b100c050a03 77
    0x7072002003180523411101900810a40e811982c4588030362013094641240b0307400c400885d8000788030030400520081c0640e80c128260b410003156000440150358514050302082154540c03c010001903601000310051905511480c02080d11540b540e00640c02e44041d02d06880c0c01c14410086c01c0b0101e0722420140035060b00d40040c88d00d442002d80709403850b220340f81e40381d00045500014204214a001c442110a0410504141d100d501d0075003071141160340c16204403030040040210351b011030250a2032008d00e05100441c914000f52800c41240020990010100c002c20118408100403038051020360f0180404e11130701620b13555400c041280d000850b03048440d180542911980b0004c0d00c18072140c842503206004441c6014a40300410200809018520b0140b1894540c044003007000032910f00c1e803184c8003100104098460313152510308018007048495203d040480c0420503400c0c80514aa40d04c1e100341c0440d11009025580e003001c40724200500b03004110108860514a4026040351030100b1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 807020638 1250 807019388 807019403
    0x304080a0507050f031c0506091b09040204030c030506070e061902070e0703140a060506090402210c040f061e08060a08011d071202010c0213110f0a0813020a050d 71
    0xb000c60340c035203107400e144043c03d000715000419100c074128803103407420002c182144420f100c942032407408580d214401520b80d0141801c02c0c454501142d000800311034140201070b0086595035035078101140f46005501044800303005490124600380c0c4200351030080141c000740300ca0b18040306140d040b41c914500305010019401a00c000144009141c1c0501d40308617519103010400075081c1c080344458903402003031041d00c540b51090070711250302c4520556002ca502030703070010b90300c040d00ba1110030f00f4421280981401071180c02040300224803c6c6c09003084404076103036100b200382ca500c000d07a104060242e01401040c1c09040c0910740034840d091154202d0400f8008011807078507461b0742d50a42d14400d58603241b031000c0d03081d060060b00e82002030000034048a11811031103200c1c1d5000074044182407001070310071400890021041e01451f07021840c0c461030070034100d9440c0100d840503500b07500301104440100f1032581c00a40540508a807104029a0041c00340681505020410500f41c42d0701c0f5094448030b = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 807021888 1250 807020638 807020647
    0x1e0c150e0f120301120c150302180a0b0409020c151e16170c0d0c05131a04060e03070b0a030507030605060910230c0105060906190b0a0c0807030804030e03120304080a05 74
    0x9018880c2c0c1f01c1100c0401d07a5003d40d8806821080e03900302c01064418a000c0c42003071030100158050582500d0030f5a0b270546001d81da0350742e0103414a00d082600d00d80000a01100004d01c0b00c01e4040504403c1c4c0b0480038022024550303076010b0345280c142804015040071460008071880c54000103c54640e000e01d03510700d00c50410803a801103200300c80c00c401c0c81700007144002038504024801000300342d00405411541c12a00c4412269400142c041c41c8030707500078002001d072000403544c3e043c0500405001301c0f89020380c0b90034511000801030701082e2031010109180c90400704003401c00b03c04039002c1b448040d11001c2c0841d0050801c4405444110309440c2441e2130035440b4803018450002003664a14020000c2074a0074a8020030212010180c076103442201c02014103100c041c007a410a01c11500c6100d4015102c01c90b02d0400c0e41c2000e10341e60b000340b8100001644ea410075030807040e5a40524042d0351441c0070400c007030043c0f698500c912112010880c0046c800500007034030410007001e04400c41d2174110b040 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 807023138 1250 807021888 807021899
    0x1e090109080102071103070503011107260c1006060903050309092205030306040e01180b0903071a101a0412020d12050a08070309031e0c150e0f120301120c 68
    0x8980200404448000c0c4200c003a05c041d00c1c08120750000b4101c2100200a1500c040c503888000e40700e200b00051904038203400d00c090b80200000c858141c1c11140005daa03071040300984098403006118500745c812480c20101041c458030400c15101525440401140b410001c8001c101270742100410b8100b00c0814200508904d4002d480204040b82c841d0005503100e082010400040d10541011441540c0c54400c44145011000b00c0c14502150081c0041c1c103d51101050742d415413040507009081414035045203c5022034000759035100b500c0511810300140c2d1100b80c01c41c00f4286801c099041a00709200034011444284444c0f80100d2000340b62440d9841140c3e61400d10708090390110300811408581102d6154000b09420346c45481ca10702000428401c1c0c1e005807441c141c69401c03008400e200b0038201e0b00e11b8020080300300b0994102540c060052401c11545c80984141c0c41c90603240d0260342c600c05805400003428183c401c0100003581e06580c208928100103911040003920400043d0600084 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 807024388 1250 807023138 807023141
    0x8070603020405030712031b03020a050a110102060f070f27030f1226180a0b0613060308120606040b03010806010905061002120a020727111e0901090801 67
    0x400803a00c0260312203142200301814a40075520031812030420804581c0041d5010b040348904114041c5010200b80d0141030480c61b140d15020000c201d44208145e64040c407080c005503070340c1c50200740c0c22140e070381c0c1c2c1e0b07070341c21241d201e0702a901540031400d040c1d1540036040c091011202031181030415441040e40340a075800310803805a0080d1820b0740d0303406400b014800b200c15148440e00f6281400e101d10031941e0b4941c1a80f460030213190f00d202c1c00f0040411000254503107c034071000c65020480d0141d5649040c03469003000d003619034510590700d41c60090b0f0060001c0c0104421280c000194900748441c440c00b02503101e04c02000b4603030000e420480030600c00070a00c00b41d40030f040108000d00d625810b000442040710b402510980c03140208505d50f0b040d003507001030a89554885001c5050f211040311005a01d0440d141d00000118030044d0250005031600d58000c1030501d4820308280881402c40b814010f49105550301400c0d000c1c040c0d050b00e403241301d45800a091401c8103141035008660f56420050 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 807025638 1250 807024388 807024403
    0x1c081b030f04030f08101203030209090a0c020706020c010518010522050a090e0a03181a0c0c1f18090501170c0a060c0f11030a150501080703032708 65
    0x80784108800b40018154020b403800050000c50515000305c0c18440310003005082188104e4481d0b68202c1d0402d01010f100f5011703160040c03c00f9024030b0003800d04038000c401421b420181e041c014441d010b000100c451002610200321081030b100c00d0320300031480300204181303241a1030700c506210003008485801d483d0080321640444200d40f01404090070201001040301c00c60748071043c0e09040c032282d5481481c0108030007110340c2c1d15042102941426019405411005a202642d68000c94400040d40c521803401880c0701900c8105a4441e12200d03000c01403d60003e41552001c9501041e2000e0141e000300000f204a503004c4007080445030390313103e8240680b5030903042800003210b020241c00c3c1c0090100414030f81d140040342c50364038250902d24002d0401202d001c004d07100d14040c0c0b4034201803140c140d15072100f02c82c010301958044038942c1450f00640420743d240c8d0032018900000001c05810201380d0105403680359486040c0840e00e284800020941c1c11103860030040740f40b5000a25400c20017510 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 807026888 1250 807025638 807025651
    0x903030a0203040602010c050a2001092a0b04082a0d030914180720010212190902030c040e1e070f1703030601110708010c03060311031c081b03 63
    0x6664030344c208940203003910030460464040c810706002541d1901d8000c0b0020451425010840d2009003480311602e0140c0341c0000090070180074040f44070100480d0b4120000c1007000c04118040042c1d03030b81000340b024411841400442d4100c1c58030801403020030908040c1522141395000c00340c1c0c82e18070014540702207500c011404113000110402050204200d1b1b07080383d440c220769080300042c040080031400f600060100b0f040200084d01d082003076507442918000d0721070b400021916140800030020800806540603040050107840e1b0310003a40d800d00510702e0880d400b4014001859039401404050a032080c13011880d4040d2002c000080914100324004170104140201074035450301c1071458403400190401c46502c0340c10300601740d07108800001c890f044202032034460505512124481d0408201c0e40060000c2d50912035aa01c01c1031303041d0083d0054074083c00b1800c44281c070030010140d0700c0283c0501d0303114102580211500c0d10b4002c980540d449075103040c61b070500c03408522403d145070340b046441 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 807028138 1250 807026888 807026893
    0x10111e090f0301091511131503061a04090203040c09050702060604050a06080a0b0405160801050702191109060613061d030604020a121b0b0c10020405130902060903030a02 75
    0x1524400d290800c803241070305400ba0020450005691981c2c2c007101c140e00074182040d034540348840c44031070200040b265590030640c08241c502e5110000803007010000000c10000034182100821003015083c171811031140381208280c030f010b283c040824047e410003401560440c0030740b140010104258020180308200c00c2d03001e8140740c6001c904000c110707034000d004ca00c88146050005c3c000f146c00007441c101039541050103003084d55100e280c01d51170700c68020951013488018200000d481041504044d0103681c641d001d480c200584011b00704100382c3d01c0300003d8a9000d2500c4002c0c06400c01111315504900060030079480c0400460285484034243d5002100080c2480e91100c0a94459503c5c2c00c04040c04a0240501d4106034001554241103406880788041d103841c149810007a180340551000c004460b0304841d030584d06c9240c9110b075000903201d44400d008035101801d4091a610032203059650042c04501d07007030910030700d00300104540e403000ca030411010840420f09940402c0585941d81c0603500 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 807029388 1250 807028138 807028147
    0x203030106091a0904020f0a02150907030609020312130305071e0e04020d020405070c060506040e06040308070207030b01060c02010305090c031c0302040305121c0605030a0204020304061e0c0905010c0510111e 91
    0xb030ac0d0940c810b40c1c103242d180b9100144818480c01045000840b42c00807030200d24990940002820082c0c0c01102010030200018004d0460456485031002c50380100b0946030704d00e59545080c441141c1c00c2010340c40d448400074050215002812055803c2800a0054004c100480c0d0108045540640700b050109402c0280441007006500809500490980303041c0081c0d40c0700300b2040e60358240500000c06102084001600d100e01c00c0114400458007e0358891955075100b0001e0524140400c0581c0020709200c001898960001182c1c1c940300c20140061071584c203c030002644503580c25070750204050f005c00002010410802141c9040588500350b1039581c03541c0c0d4090100d40c10200f4017684000e00b040d000300050b0f83d01081e40b14103140c0655002d41e5a41c0c551500500402c50b00c44818440c82029104280c2410309501c51708100703289880358039019031503130019942c41a10040042056010a00e603940400454000300482103079444240d0800503e07800006881d02c6080d1108502d500104 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 807030638 1250 807029388 807029407
    0x50915180a0b03070503070c0b0a0501050112050f0402060c1006080c1906080c070c090c0809010c020a080f1312030c17040308070b06030304090e060a05070203030106091a0904020f 79
    0x140803811564044500000c00e80c0791041c0c2c2c0d5440e0000070444c109100000c400140c0040c0034201924109510011410951500e060540000d01081c05042e00046014880500c0c9408920400c1e02800f107100701210a590355900b0001d003980b1000c242070030ba000d009a0002c64107190700556010300310f00350151a07890301c4034080c031841e078500c0700708000c90f51400b074001c10000382c03c803100a40040d0b48807100707035070741c2c045041ca4041c2c03e840c0d034003020240389001c0c0e04070703100c40d8483d0140d07015509038030091040503000481241d8a90140700042c0840703100700710b011145905100102406240f103010b40a07041d590f03250046c0704080486041e00455501d10305070040000b01714503042c0d242c40c0f4821041c2000c0c2144c580203880d015080004040900c54004900141e904009071001048815018007210304501e072110b80358036050341c0484c0182e044c403020440380c600120507a030584d4440d0344c0f1002264a000741c0c1814104512070303c80d51600c010495500d0649460005100209204a965940d0000b14 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 807031888 1250 807030638 807030667
    0x7061a0303070b0f04020d0c0305011e0516081f0305030a030f020a05030105270c070510090b0705030406060b040f030327140406090f060314121603050915 68
    0x1016160300c40c0e001000420300241404105a401c51078142c807030646070369a44013150391040c04e8000a45080c1d44000008100a815000040030f104400d000c010340081201060007940d0050300c2104403454039001010302648210b0400380d00005a501e41c104d4035000e981d594040a0907034100f652160000110645590781500500d04c17003000084c02140740003290f1100501500040c002c40d4400c07100180114926441c0c8103808124000c6042c01c00706500f0018085c4415610211045420f4040e2851124a50141e44200103610f60043d820307540c0c698400c0000c540b5680020000c40320203660b1040070481020b034401501c0900b0b50184540006403c0d070601034101340c4642c1c032804c0703c1d00680d40181401d01d4550421011601c0e0070220556009c10074000034090507240d00425500c910340115060000151b401c290308903406a0502d0100c062041e4015496890710444200d501303c0400501071031301014201140800d02a2518605018210000030007a4004071002c0c051300784042010045403804 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 807033138 1250 807031888 807031931
    0x412061d0d023309010614010302072a03060203040503070b13020d1b0b07050c280b0714030a0305040b070c050604110a03020310050a061403031b10020706 68
    0x4500040040780000300c4020b581e80c4a01d102030618510068480c54400c07110340c488038841002c00111140f900c0c050350510300902c164820243d03510407140040d2519406032003180c1e0400e4110840e8404414900100781022140e140302031441206c0a000101041451000d503009521400107560f84009034145484481000340c0210051180071000b580140c1e0760200746050242e02500b2081c1c642c04001c800801d16203544e1100b4860365001481c1020000003141020b0100402c840d004180d060030f000b0046905440c03400ca51002d050300e003007808440d1242020301001e610400340c038120752090000c0b050640d0080d04010000c0303905c0ba0280000c009003400e106601102034941090868815110250303520380280020340300848001c00400c0d15258a14610051078010313040303440f4001045058001010204d13158030380645003140110b41404080a031000c0700c800107000b94106100c1140d004041101c8800038200c074407a031202401c0d00d00c4180090006140124000108110071348070442d50b00c45d5 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 807034388 1250 807033138 807033191
    0x20109050901050616030210181203060e180712140706140a0c1a01030b0f06191e03020a12060f1b0804030c020a0312110f061308041206 60
    0x160200180f150b51a030342c055035125118001d0855808130541016070504444500204480703080408078241c00000810f90001e0741d00c10040d2150705914a6011800c070f480300e00034036111410741c0e0003117424512840c0102c031154140d881034403822959544444010410b142040f1001512807010381c200f0340c0148200001855503007000b88140792802c009589a05c00c2e018408280f100d0007800c6801c1c003141c000001c0f035003007060b1802411540c581c1000000d10b0400c56aa074191402580040c60b24185503202c000c1a8040c01d4424031864104552142021101540b1a40748401c400c0c000000d42d58501140c4010502440c1c00424045207003440016109801500035000c0d040c40a8481072400c40300041191413100c1c540044541c0b19490b0846490901d8007010394040d116010101c00c0c081c0405080348104a1604c0340c0c10300c180c1041c011905c4042080c1c0101058000f10000b8010070400000d410342c4a10544120345801c0d22052052260144d00e8025a10b00f81e613041000800c4e0101381c4040d26030759 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 807035638 1250 807034388 807034399
    0xe2d010918110d0c050909010209120c0f01030f0f0c03150b04030218060a030609080a08090616080c07020406030f030807090e13060219030515010906020705060f210402010905 77
    0x12a95202c0c0b19101c1034034500341d4001c0349200241c40a1107030042015020f084018081016030400c841d180d0b010b034001102c40c510902c6020604d030400c550010b42c14064500c05810703484501c03503110042d0000c1c545510101c4403030b51607900e0088004160311451020503e40e1b103001170b20301c1c0300d1160b40d180004541c00406800034108014005a07554882c070700b04030340601055003055501e00c00840c44002c82d9074802040181002030280800007c0301c081d01c602011541c41060310b9648100550380c869054079024145d4800f040009850f901c1880c1850344440707445012864480340d6030103d4103c1c0c681c1d6100f40c610040405041d010540d0120b1220303003019181c50040703c40d42c2880d0f076000822402410010055504941000c01c0010a4059600b008080c01c01000c1140c5503001c081c0103090700720703002907171000180040303811980225408829180641c3c000d00c0803030b052000740f108641c0403800707090003d0000e129008a2080c0502c901ea800340d44074180030301d1824188005040488180c00c810300c01d8 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 807036888 1250 807035638 807035681
    0x5030a0906230106140304060f020c03070c1409040f110f120601140301020c0d03090302012705062805060604030507081005060402040605030a02220906030506150306010e2d0109 78
    0x4000c0c401b40c0307401a4010b40300061280b0702d02c0164000b442241c149890501012072504240800090329108a40102103800e001c0494501007060044044038000e2030307a1035200b064000314a4603005800141c0000d40544d01e01404071002540316103410903080c0c40361b0b00800040c400c070740c040c0e8003550302c001c41130b8001c2d070410201d543c001344c413071004100d4a801c150b610082e00c424980b003500041c0c012904200d00040032120240c040c201155a90340513601e0b4812003005c00d010b00004100208000f044c0c04403658000904013112018100240540d0346c040000d21000c40401c03414003001d0001c1ca0100f0040c180150810b1802054580040040748100d01c180403c00416401c03004580e031008141d030300103079900c60040748640040d0000c107180c006465021808680c8220036800741c01568081d00803503000c1d59a004400019a03031601c0456056008080100140704421a9054106841c512400780620f010303400f8006601c1c1c0d40c21400b100c0c2103008010015414903100751000d0050440590940 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 807038138 1250 807036888 807036917
    0xc09040e010e250902040308070218010b0301050f03010f05070327210507053403120804211701060507110603070324090e0d0207050105030a0906230106 67
    0x118841c485034098440b041000c2000e00c0e80c038000343c140140030a60011512140c0300d0070595099004100c04030301401000f0501c004104154021714103c888500059185a00384024481140c5440d010b00740c040d900e68460420b141118091640300e0030b03d550700051124900e6980b5000000044494244000b00c413803540c0c00703c2c454000d0b00290340f09030075031500304002103041110944903031070001d003050080c00000f4074503030790010346c00420b410a003030300d103101043c8003044050000b014232004003240c0e140090100064001c1d244150701c42d000e003c207800b860001c0400070325803a900c0340321360780050700783d501d13100d10785d04081da0041c00f50489240c0309040c094250750381603171403039000700c028440c9402100281103a8802e411004060ba1300751000440a00c4500c4401c4501c6d41e107000e41c035007050405000c3d00c006000010035200c03904441e401068120701d05001522142c0c0050300c8100280e803103a408201007400c60258461141c0103110403a1103a01200c2da2858450f0180c103c0002c000d160403c20b400c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 807039388 1250 807038138 807038143
    0x12020c09010e270d0c0c0312080a050c2b060b0c0601080601150e040b120d030609061509060e1f02030a03240501052215030b0603010b0f0d11030c09040e010e 69
    0x14544510705020f17400408605040b500760300355600041031000f02d4018a045198812121400381100325814002c03130700e601c2101d4a00d0b0060b2050280081030003091302040100401c10301c540004186000209181ca401070030904d90711885181550b80c0c0720500400c180382080210301d00401505008215071312000e040200704540708030b0003d120301d0f01c43c4102d407007941e2803194002010044c02c0460348403403070101018029010030f00c94224810710b41540000c0000e40341c20f840d01502d1302c69072031100450070302e14161014081e020480d0b4001d10084917030024040c5040d01c0094480c4180c000350384503002024024180c0e0400049503071282082d00403c000341e1500d812140c00e0303c00034240b460b100d903040320103102c074004140c0107901d03404071141d00024000c080208850302c440e442d6a09102180400c018803d49100a1041c1007140c00c007041541010711507140900314034440d000700403c081d80324038036030303a000e4006403004028401d000039900e4032450548103e5100060f0b500003800400a00f05050740c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 807040638 1250 807039388 807039403
    0xc090b01080a020c070519060306081507050a120204030818240c030f0d050118020a0e0103230a05270a020411070506010b0a090806060d12020c09010e27 67
    0x30b0903000f01e0b040318030040c103209041c080c200150210585c0e0648041e0a01c03a00c1c854030401d0f0209241c14000325040001048a02000d03004000340d900035110302030104da0300c0c4e002140420410117022007151100f20b260004000860041c0151511400c06200c030000703107035401d144140300700407103405140c080e441885022071140511081541301c0146401c92411842400380d00c44c0320050018000f004054a94421810b88007040c004515880c441140c180032841800304103404921982d401c900d0a41c4240c0100010708200e034081800605c850645043d403030310954030808080d444030100203030301248070107203801b0308100940f140581800d2a20320780c440ca0700b500d010b40195140d00f031f1100740c84082012203a8665100c1c00300d070b42543e5100466105508000c00e580c001580968002604010010301d06000c2d0740001c002405040a96440b210250070b103994000039030048100303001040e515003038002c0c002c0c500380c985641180381900003002098880e406d0f1110850001103421248140045d104 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 807041888 1250 807040638 807040651
    0x18030c0b06030709050903041406070c09050c04080109060e10060b03010b090609033003070e01110715020609070e16050c100c020c100914190806070203070c090b0108 73
    0x1400c29865000209040040c55001030b80802d0030030082c003480c4000040140111042d05100c0103400c01d9403000c002d01803043c003030080c00c0503000310010701021609034041500019030034000780c90140d075220740398252211100b05890180d584c071320701c45c9180c4091000c01c600180300b40c000c009490600c1a1400b0900040c010300d0208680800c1d004456141ca0045a030301c030400804035500008601401c0d12042c801c00d0394035a50a10350000c5180001c80002134a006030417030780303800c000c2c5041c00b0011201000110606103551150b07580010f04070409115801210041751302608442c074082c0c84072443d000703030783d48060b940a04030340810200427500004030b03405245603c3c1907655280074900661511078190044107042c3e01c2c2402c0042c403a600001d000c42d1134034003a110007410b000e14580544913030f241840389528554102e0309030607442c41e0043e4484a07040007029003194064170f40491624205c8215000d4003d80c0c80001c201081c800d1414814000708004007082c464055a070000a1403140d02a212 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 807043138 1250 807041888 807041903
    0x3020313210602160203070e07021504080304080c010b19260c091503070f060809061006120e12071506120f0609201002061501081e0406020d18030c 65
    0x980c013040300340e05288030140d9001011105526201c00001d0410700c0c003602c1c807101510441c09071003410410340301040c1c4181d40082d40c0078110380d20f0791079043c400d40c01001c0001503550380317400c00a40303560707002c910003208600d03201483c3e039050502540140e1900c24031031501000081c00c10704400600001002c5450b000c0a85e0010702549400a4850114480403030f0307070342e25000d642c4010034845882e1184804a84503035440342c0d11500e4006416071180c07001e491384015046603450a015039801041c0706150ba501070100015a81261560741e41000808900d84c207005038001020803d0000c00f00c1403200302c0d24240010030043d0728004085010b003101000c008c0c20030b803a00f84004140000fa91006c414107030010407414900c180c5065010340300150103019449901c54001103030300302d480043c06a21030910320400c07101c2459032200544410b600104546040b0107481452078151819003480c0b401288511005600c0d0f500001503c02911582c17442d41c0c1c50181902030007000300c0c0d40704c40f04600f00d9400022 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 807044388 1250 807043138 807043147
    0x10b0103140423010c030506130b311103010303110706021f0e2e02091e04200304060c0c0809041d01091103061b0409020a030f0903020313210602 64
    0x100f09500e8408007025814a519000200040d50f4154001a20400007218034240480300443c800c0b08a460b409a0f144d04a0720b240c045141001e14110044188180400540c41114040f0301c6c8400355000000f415869441c04401002056000307090318100e007502d4805440b90904240e0000e5440f15060301d19004031441413000f000c03101665000c159000c4924064030035090014415650041040d040d046d00e207160b0158648040d851407090f14034480c0b0040204106480010210008191900001da802039031350090b14108030f5140c83c100c41842503804056102d14140c1056001c9a248180035800c1c81682019007000410f10800c481400c441150b00040308201e01c1144180c10400594400043d0319011458092100744c1c5449101e55038102d00302c85245e81d80280548608801c4100d40c2160901400180402040ba0700546804200c515000441990078a100015182c13400c101b540940c00c00654000c5910b00140004041d220003800311940c0c581031001070308040030110002d070416030b0204 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 807045638 1250 807044388 807044423
    0x609060e04170a2d080901060803121b0406121803092d0b1c14061002150411040f0c020c0f04090b010f151b140a020d14010b01031404 59
    0x140b0403480840703ca200ca07140743c080c2000d042620100e41504e400b080000f00002c8204605000710419520790b90091403c00b440c020404100041c0980040d950380d4040c00107165048012000d04001e1226a881c0031003c010a0084c804a6800d80744040d942e1201110443c042030700410940c04a81d001142c1e91800c0c805041e6074038403c0c880c03441601d0000007600c000501008048060145510320002000345070425079900b0040b07410f051010701030544010300040c0f0604c0c02c602c0091030301d05a40152210030007083c0d240002e40300d08903422103c4c104042103103c642d0400344150203600c0c2c1e6001c0c040009e5800e000002c1e641c0c0d0070142c0070034811b55640500e12019222030300b1600700542d001505480e0340d42c443d11007004004090003400c80da200b030381c0f02d100c400f04c1c0715100c0d07907580b140c080c032191242500704e80307541c0b004601c00c0e0070741e154510a809140380141c440608840030140a42c0844003042410030449095030004107840d8100360070094540c09003045030504540090340107880d48411000d10 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 807046888 1250 807045638 807045647
    0xd02120106090219020c18070507080a02060403140a021e16180b0919021e0c070501030e0c0114250b01051503010b1c06050301090302010609060e04170a 67
    0x2120411542000d8001400c4009900079083c29841d1140d40080a0b1501c83c3c2244d030b4058081e407055100000300c402e682c3d5114141403160300442c80f407030310704d15020340340d01c071580b8a070f000b00d460400590040303040200b8160320030048100d038040d0301e061030b240481903000256101400a0700e0090400000c50034983c800c0100500400001c80c0010030008690f0342c44800500410401c59100780303410f000403240c941c500b10411034841c0304030708c00c03454441074408520300081d001400c00c842c910110300c03104508039820201824070660340d000189a8039003401c00050540d02104040c890503070114512100c16a08100f00c0d68402c400b030582e0b035440b0b0300c4400300b00c83d0040302c2441210b082e41c0d500401000707000000a070b05040c0d58003a60140e0440700d94031000032561100340f00e040350180041c01180c625a44814503070070580c00711400840d0280d02d4038002800c55180d40001c0f00941c1d5114010042c40110780100c60040c03180d19030340c840030716254585040c3d42c00f50180c40d0200384030000d02942c405008 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 807048138 1250 807046888 807046909
    0x1416090801090f0605150603011e051509040c0f1b060f110c0d09050105030406090303060506030901140619060516060f020c0606030105040c12050705030d03200702060301050d02 78
    0xd4200922150300d071420701e00b403400c1e94000d0558030207040800143e034400d040c0c40c9000344680040e044e00d2840e860041600c1d586206210114128800b0f0400005e056685c0c030b4102ca0441c402d1495144d9802e0304000b048103c5100d902c09078180100c030805003880741e800031a074a4109008151180e147c40c03151403c04000c00710400340303614642c07a046580b140e101005c806000316101000c1100d5143c100008281c1d100f665900c01c46000400400000d400500e1300d400c14229030340b290a0100d14983c0321400115140c0040302c0a410f070340c0d9182c91540d0016203003020550884401c0d1030200303070046051503140c0042c02c40c1c0100d4061040000c4d20003040541c2c0e02c5c58440c0e01d6040301e07040186050080480300a948000200600391003040082040e40c501032103058043c80d44a403072005618500750082d0100c4889800680c2e09000c0c01a00117402d807400c0c800d41d44500015075000a40103038901c40504241441c031001d805e080014000c510058440c0d00840f8190754045620500e540c80c244000b4150b030f0728 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 807049388 1250 807048138 807048149
    0xb0409030807050c120c0f0f19020f120a05030c0c2215170102091513092c0703140d08010e0a0b0d0311010f090f06020901050c1b1003141609 62
    0x240001d80201101c3c01083e0701081390102e50a50f040ba04590340c1003a620304140300100702710250443c401c0018504006d41c1c48080300d01605900900d01001d14182c2416a5030300d05803441e4000080e516141d081c20b00032251800300890b02480c42d484070048040c3e903039541d800030885003a650000003415081003035407100180003c045120314106c100f40b155000c0d412800c0f5031409a0040f2110700210309000702500c0c112071a010361082060300d8509503002074035034a04c050684090300702d5050b902040810807100c01c559240c0041c03007203500d540ba000d00c007030000102c6000190081401150320030340c0561441e044032501ea01300130503a20341e42d180c6402031484408090384044055080c0b0101070f0441040088a240d0300000c00c03428040031118001c0c2c81114100910403030305415203c00041d03185d8064a0107060626240d401c01c07003140078107031070944142c0d0324190803c0f400b000c0c40313010724005486844200c01c0d0b180500c140035000e00000300c4082d02501e08080304401035101a5242c0c42070a0b190010700 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 807050638 1250 807049388 807049423
    0xd0e06130b060d030c020f18100609090e0309010311090a090e060c0301180c0327050d020c01051c020409090803010e0703091e030e03010218040608030a02070605030c2101090b0409030807050c 84
    0x10189c0307040c1c692024501c20140450608100020f98070303100d2051036141c140e0b078400303903207007003024001100103220320070f200c0000c3e00b010301c0110340a84804482a003d0039058600190b0981d08400103031030140028088400d080081006215070704121108080760385810764081814402e409003070700a81200f1040850088001500c0010300300b02c0d103040180c0318083c030f084d922111070b00803003241c84140c3c0070b1140c0e022030300820402e0b03102d035022039014000204010005003030541714022907090b0351010708151081304001c001804940c001c3e0800d50303003120050a040081c6221a0b80307140810b0302c5041c1a0743c2c20480443e0340c0083c54001d82003482003041c000c0086503910801e80c500c000c1c50200700d05560003107150602c0410040000005c50b200d83c900e5400414010789800b0003180e269200400c1041021000d11842c030314403203030910740104a101d4141d8401d80f0344c1003107040001c85011129080c82a801c080d821804a50485000c0741c010850b442d003039580714034011026140503240c256008104 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 807051888 1250 807050638 807050641
    0x1050708120f070305130305030105010507110a0915090207170f090301050c031017030d02030919050a021305040f0204020c0f0616080106050408060703020d0e06130b060d030c020f18 80
    0x10b00c4415925115044584082015455404030240c441c2c51411009010440400050242d0341c0648e000d0700300c442c800c0120740c1c21501c203400440c0c0012032590002c1c0c82e254640300c1c40180000b807440180c019190f41d9000710b04100d081c0d120400d400312800c840d91008900050a00e00c01d1594034100c600c1e90101038000d100c5420404090816503000b11011011040d452002042041421044000300f194080042d410210381806441c020351003d00b40708002d204030350111042d050b5007a03042803800e01450160040284500511012512650480ea08640b0b0501004000303280e0000001c0c03003e40644005845500c90001146070180001e2001901c0c49200e08000c04604440e41403103680d202d40d47c402c00c0703070790781d6032400e03a9580200d0258000307540064000a5003188a68090a0703401d80c0d921012407014400c00100d4140f41054800701d05048500c0064014401d0001d0752a4000703205036112442c40a25490080020260010092058000002100165440301800009032004040380c0002d0f = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 807053138 1250 807051888 807051901
    0x80d230d110310140301060b030c09240304052b0f12060f1701020a020a1106041805061e2803120801080d2a170313061104030503090105070812 63
    0x6003c0d561141c41c908110b41602080b6509041c0942c0c811540c0750ba400508540710341c0302070605074202095482d000103c0f000301d0542181924502da440d00503c030700065070b90500341000350400001003811841c05620301c0d01c141c90090074a0103500d05481030328100c42104c0b40b45074210b5001400c064035990042c00c00c100480d03040e8002041c00b045540f01d444d4056001c030f0403a0030900f44e0240e400c0d240d01580100441c140451085800c9404200004006615103038886c0203a5000c0402d0b150369071780442d45c2d2020840c3c50700300550390004030184880c00300d00030313039034503000580003491890b01c0030204e00c40030507010040c0032100100c8003541d448203088204c50031070315008080305400d1140111500c80c11a080e6000b9014801508000c0303c003500580445850512500004490300b40071a088040149480801a0980040c5000d00300f03500c0c1642c0304003224109501600d8174502a071202c030808220800004030f0000482d06000f00a08041e13890341107905051510340245004140b141c0c4000040000e0f = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 807054388 1250 807053138 807053161
    0x1030c0e10091d0609060d1a0a090b091f020c01110406030b011211190203120f061503090717070806161106101a0417030301080d230d1103 61
    0x107442e400c030040c104220070a80c0350200f10f02c0c1030714410b4001c0c8120340800c203a03007000c21484180701c0c05249502181c00d040b54840b1000d0604070342500304561344407490410001440c416640100c040700081100150150300340e0078411081c090803550316030014981c200c8210a4000986586103045416180c40d030702c217000344c068146002103500286981d441114100294480c09021100300040c8a0828540c510f0140001d040408d6880c19440184580d05041e071580560300d104500f030720b00c0c0030140d00b0010240000c0c0d103801648810741e413105204014100c0c1f400101c3c00200c518140c9440300c44180b4100179400c2500941008800c1c2c042c410400110103907001903042501c0541d0754041c10b000e0b010040035100c02c0251501a4001e100010070000b404020050044412048406510b000d40d034505014800e580003601c0211741d0400300c01044202002d021141c0d180364541082d685c062031034141c90700100c3c090040e4080c45c11300811095103411030303548a941c3e072545240c1215941c1c01e10314440308 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 807055638 1250 807054388 807054407
    0x711030714070e041a190207061d0a1e020f030a1a0106050a2102040b0a03050411061318020d0608030706061410140c0a0f0b071701030201030c0e10 65
    0x40351807042e20b10000e03004001511051207507800c250202004107a000390311210303130f0700a0081160412983e5089a48520900c02070441c1445104001080f41c1e07460b214148aa00d660702090751038000c191010081401900b060700700e81c91801d804250b09956100203156000c03080012500b500c00c141031001001885001c0551030307408941d4041c841d81e66420111110b20980043c500041c92542c20303021401ca4410511f200481d0700100076003002c0d1121180c5045801002002c00060f8075403080c070041c00f4032036000c00040c00c0f00755405450041e0454106101d01c80750b1180984007507105407640c000b91255410f40d160740075024014401d990355515141c1e40e0b500030300420f561081c0b07800c030005070f0406188411084020082c0c41c190007006101e10946039090081550240000104681031f008401440000e001e10310906d01002501001c1c14032142d44500288464180441406030815040201042904407a42441c0201e140e400c1c40e882110030b4880c107240c19070055a022a81c401803a0032544c5034 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 807056888 1250 807055638 807055673
    0x51510060e060301060c030f2d0305060405100e0a110d05060910140607020303070b070c0b0a0e03120c07020d26040509011a040f030c031202060702060601050307110307 74
    0x104030307022010040103020310080c031445001ca203201d290b401c0080c2c0208009417910950741007205441c040700e600c0720701002c04040c2c06c0501c00076080502d9490b540600c54203400c8030003510100054502208041002051801034080c0301d101a000944c840c0d40070f070407041da420250060707181c03126200801100502400d4034001d10031120310001555940d0b461055a040780c05040f521001c0300c0b580340134003500b070340850360a0383c150104000c0e04010074010ba9219003e010240d88444100004c0e00b01141c0c0030030060048a611400e0008800b010741001050b40d5140390303a4030480510703032140d4542014038841c004000350002007152200c800e0200d00070051034840f880302000c07841c00403c0c044200e41841140200c60707108204400500618401c4106040000c4820540900d01621242507500d034000a40c41254041071401c018005c01a00c0104c2c3ca027406058001402e49041c02c140203074860380c0041510f4100000400021012481a00400043d504071002d0f01d9892200b418000c1c80307506c2d00c0080 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 807058138 1250 807056888 807056897
    0xe01060302010e09250909060e010801050105030f07030210091502070311060c150907211a06010f11031303030c050105060d050d0f090b04060c2f090405151006 70
    0x9800c2641407641c0c04620030084441c4038034082c6400020308a040d05d890000c10f042014800d07010a41c6d000702d11508002c0c01c50604030080e2585480005802d583c016080700740030790072990b13030488035030300010343c0e2401d80c3e504842400400503914011121540700ba8840c20002c0000e61125040540200b02002601c0c0541445000c5240c0c2e0070902079075101e19020b011180e40100001d111403420bd50900340c000407207001780c4103a5503031742000c6100014210a10f038801c0d034003600c2003000c102888441d0103940c1d04807070043c0810700e41000060500641c0c410b4039024450340e4900c840c00c6850610844140b4900d41ca11024140c0e240e090080a503007111034100c42a61801003c43c9d05841e000104036103441d8040010130540310301d14000c650400001c2145024044180000710328000810040c1c00984034554074034400d00700034100391035105034180c00619070168000c003c4960f8070524000445840d81501c006500740c4a41c64600d285c0041000c20035110303803441c1c00f80400080c1c1210b42d4000c54010b6902c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 807059388 1250 807058138 807058157
    0x30605040b100803092704031d09150405040201020114010b0a1101090f35070b0711070920030a02031b09090a0f1b050a0201110c030a08190e0106030201 67
    0x500d01e400441e000b040f840d680144128201482c046d5046020340e607000064020b9480450013400ca010340c01e640803400b289155500c2c1a1a420084141024810031103054030349007000d072603460740816049001344c00b85845030006015a4002d40011141c0b16612081c01c1c0d00b903950b0040558190041d00b0b1580c001140a8540e80754810140540010150800855100801c8682c1c56414142c1180184890b128072179001c03000340101d030440806402c0340100f0040d5508503d00d48400380510081c8500b00f4440c04150300396903003200080010668540240004007842c80120140170300c80d10600c50b030010100041000f41682560b000b030342c0202800f414019402a074a4140050382c026000b415400540b22400140c00c10b000d03400403442038850990000351082450001d22203a04100d8066010980c005820351009a091140400f444036200c592800d1a629803603460316031040c100070300704100c2c5000129801e43c17003020403c1e10040024408000e03184040c1042c034003812842c4000d9010504214 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 807060638 1250 807059388 807059401
    0x50102030708161e0303050a0516020a02060a0c1b06030e030a0c060504140a0b06010207210f140609010b011e052b021206031209060f0919030605040b 66
    0x6580007154419041424242c0c1c10503103c2070a0071281c41074400c12458080d409403060b00603413070b441e134078040e50300455545014011003007951405030108400049031403000c3e041941c0410030122096040700d086585400340e10080792654580f25024001d81d0075071894074a0902240d0000c1c0803980700340c80070300040e030406031110303124041c24540102040701c00005000003a12540a01d03407040c49250099006102101194030780b00403000106d80404111080c0007041d0780420291000380b000b0009801e07655907400c2d01e8064545185001000c0c1c2c10020199400c00c8082104000420039404c01ca602c03070300d041001c150207440d0341100d40340800c0004242100344030410701e441e080f103002500c07002e260600001c0c3c0a2034071290119000001091902131030058400d07130000780b04103d45c034110107095060000815040c0001c460882c00c0b590410401511261120401d444ca40c1c1d4201d0442510307028505c0c04160101d9020122003843c04010320080104450b41d80082d00450260f8a240e00c1c40c1d0300c04 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 807061888 1250 807060638 807060643
    0xe010603020406020d050f04270e010501060c081605011e1b050313150c0c0b0903071208040303110d09060b04290103090b0a050f070503040804050409031707090609050102 75
    0x1402080f00507000f000d140d03d01d50707001310000c0411103981801d20303281c2641c402019061302c48859110001031550844600d45540e240a50307014082000000c0041c4d51500c17502421840304c0070402051340c030001c54411295041001306005064100300244000102c1c05500491455a10313450701c0000d01c1c2001c102d88a0342d28415414007071845851350f03465511441003050216040c0c10703080310a0000150b5007480442c6a008518400717103940c4071480c202ca218a0005440309000380b00703000641c0240100400708000c0ca242e0030800c4a1418800d015032101e007400c9003d002181e502c048480c000040c005801202c0e82c0c050201e540c0940b00801000c86100100410b40d1168a40070094100d0360b005050140410358010b0382c08581410001500700b4a9030360b00c2000311045039049002666074080012140d640102030740d00101a14003d451442c20b83e1750b1000600031030140c1030055545081c042c1c201030092020407540900511440c0da02e180190740201031303101d80d00401000030b1000c080010f155000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 807063138 1250 807061888 807061897
    0xd1b0c0905160c1130071d0c030103020d02060f0f1206040c020703022b1506080d0c0f03200a05120403020307090c0e0618190506090d06110408070e01060302 69
    0x10203d44222011070701040348058208100070102ca2071048083e600918881c2d0140300c03184020090b00500c0c3c070f0b000940e0030007c2c80001c4000c0c20314071801080b072400701c81412681900e6044030340118000303141c00461524003901014250100c2d000408009142058001c0d00c0b40c1c2800300310f040307410b03503a28091100783c4640000c25005039009a07010300041c45c0c02101d0030304c0780f6000980615061410a01c2400818480c401621081c050039030009040003540981c1d03000d401d03080d00600b5480b807202c0c401068104c0b60a070141400d1110000c0c00304040c0f04900c0d40c00b1360001c403580c01c6030b1010b80008241e11044820001c41e86403194803082450340030884299403c681d001009428082e25140a600c00f402804c0c80340c0d420044158000800707035403448050222a0002c0007040c580b01c0c80a000e0020740a0010102c4080e00880201044030740e0300c000880e60b10f84d00544100756114440d10b0500d015020780d800f1203505540c007240100d01c10700d0000c4c0700301c00c45404400603111640d0b5440c06504034841c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 807064388 1250 807063138 807063143
    0x303020709060b0909040212030d06030305040801110903030d020717030712050f01050d110411160605060303030c0d090f0204020f0a0206130b01050d0305091806210d1b0c0905160c 79
    0x3421000078098a0940d04408108d404038041d41d1034602c00c80e004008462080c0c00c11808a10040b4040c040c40c5424400d03020681d04000074203181494a000190740c034000c41241000c1d50703070002548400c00210400403080d0008851030799032a42403102010300702d0101d4503003d40c082890000058a42442135180c18101c0d4805040d40502d5502c07510340005070309c3c3c1e043e40d868006449464040700748928034000d0000c0c0b8410801032241413124a0705905855001d4a11846980140207000d400e01080c0111040f614103030800107200010f526003144c0c2030304c01103000396125101141440c41ca10707008004203c1075100390700350782e81542d07104651000208801009402d00b41110b00521007400c203905000c0c4103a0085c00c050f8141200e1100007440940700400c0010038607400024000345081c44440540712010114100ca43d8a40c500c50041d51080400c010070108460702c4184660304119899201800c3d40046000b10f98680b900318100107018103480081c08118542c58a5455910031b000805a00d0b5 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 807065638 1250 807064388 807064399
    0x50103060e0d0509190b0309060609100b03070507050f0a0c14030a0803061002071809030f0e0904120e18010509060105070c030b180a0311100608060f0702030f040303020709060b09 79
    0x41540007030003e200800c1000712005522070301c020822070814001f4620441d0a01c0040189103070030400d100c3c80360310103041401e8080b00440280041101311054903482700341490803c1e1683e0041c204a860148101000081c901401c4100c0b0306008202d003408090b5110325a180648803c04014190307141c14140029181407400e001003400c0c0d00e40607441581c0801c2038030441c1d0b010384c1ca444810108601001440c50115642c80f0100304060300702058050704405030805a41d40a0032101040294100400081007000705011110049004240e480c0326500701500c0080150304030200c8800401c8203001c1c0310700c214081c100041c0c041d84a0710032248040c2c1d000040702c42407803443c0c3c3c0d2100ca00300080d09400010b40800048050b21804010610507540a80e41d008090300c0c1c4200c2082c00c3c07007940720072864114103221043c0902d850000d00726821480010344540a0780d80e0b2001281103001e0280343d1903034500c0000d0008240740c0d0000301482945c02a030f03420881c5a1784c030380002400c0c0c82484a200d8001 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 807066888 1250 807065638 807065647
    0x20604210903080c2a0f01031b030f1506030501180b01171e040503030a1d1b0307050a26011a0f0d02040c200102130308070c030c0603050103060e0d05 66
    0x41c40b014050003101200c01300300d45030006114603148070002c10b80780d03a00e20000c0c640c03600442803600c2c0e03101c010914020300b82004032403140b580e040301e5001c9091280040c19116007444e071101300103600842c5401c3c0044d40307220301c864035050700801501c420702c0b410300410b00ca9070070040c008a2a00c500a81c48074140c407545030340e40e180760903501a68002020b0410902d100000a44041c420035001440340344110061545c178602030144030112902046041104039a981c8003860240f40015914041909070418040c254054030009244c580b90ba00640d40100080900040c100c0c142590b8a5180007422101088202085600ca08a403505600150b00501c480314240e0b0a0030018010a45248c001e40700185110240d00410140c62081f48040700203020328510000f2030700b016440594a92801d0300a40c0b51180210381104442c0390350001508400b0300080c520100b04444903210015544070703144600d01d954441c006001030509110070b440e03a500b0032498914000000c5180310750400b0a0300c0e02410b1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 807068138 1250 807066888 807066893
    0x150f092409010609150908070f08061501080112020402160f5115080d08040b0a02090d050714090105030d091a04090f05060406050901030803060609011e020604210903 73
    0x401c0b01405c0038001d1083c006030101d048030050216070081c16004c44140e6441c1e1400246a28002d001026580e044c000e145584250303a80c029586411902c4040c0101440d100500009000744501699040f40c40c0aa10283d030400c600008001803040c05201c0107035248541c18419010782e0224885010021401c2e00c1c1840041c0a03507400f1026100030004e01d0501c41d540e111584100e95035501c91003025041701d8001c01020b0310401c0740b41d4006c880f40c070f4500d01a04155a50203010741026041c0700c92250041403401c480c0d01c5003100d03425402c2e00f007000c03501490351700c20810580c81c02102d0164040c035103020002c100340c200095141c0c0c030200580d8414001518154002820030843c120300700c1142e40c10000050aa601400b9000800c0290180002c0906240302000203c0b00719600c01c0b40103210340401080810300840990350301c030341e094610b19903503884580100c400410510412070312880074841500140d50020341c15102c3ca1094001d84014010039003070419109095902030000307645180180700 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 807069388 1250 807068138 807068159
    0x503030a021303020904150b01020d0e0d06090c0e010807150e01030c02100f060e0615030a020a120617010f270c033017150f092409010609 61
    0x24004100326210409a165130004102c2d60003a03900340e07100c40b03103100e5040c2e640c2202c1c0b0400e00d01000c24002451107940c20b14003e02811501d070000c0c2c1c86607003c0303001c205c2840300c103400c01d170059603006201071030f016159242a1366003242805104011706c42d4136008142c0355071f440098102a88540c45490750004500011001340820344e0981c030441c004c030442c03001d4082c054041e211051743d00e505c0101d407444c205034504007420740017455107106140701011000d00d05004811039400c0b80d10300b40007507521260210113803801d003001918400418074000d000210325030070100020401c6402e0000b405101c0103011400c013655001012000d90701140c0420601040c12100f000c50464440e602c40309185503243c03101000300c460800c421301105480140358841804035102032000e010315090006042500b100000b000c154001d240d0f405500202c2d5480310540c0d141411600da00354014041d80175483e0001c1c05c11110212a141040c440c18003802424461621a8a6a042e611560340300c0400528018030006c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 807070638 1250 807069388 807069397
    0x203250201020a120201020904050c03060108010605030a18080319200d0905010c020a020901060903080a0c0503071407091523130606050301260705100e03010204090b04180503030a02 80
    0x203042d841030707244120000d124802060142c0c441c81d000161581c003a41b05000c20740700010b00c0031224400800400c05c05a0300f280605040d129a0310708642c1381d540b02e8201400505042c1c803290400455042c1007802c008454005521503000d5004000c507881221010130180c601e08851003002d0030441e880f03540e400d4242c1001d01403800030600007042040b070316203071070b42162106c4a001d00141c0100c1406000e45c105404124018000d52810340c6085d45103844581c118040c1551134000c10210424010038004104182c4110a41000701540c05003000e1000598402d41480f9921002c0c5c00c110030025405a5120301d80e04032025080313644c45854950748044c007104084e08074a6401800c0700711a1190035494401e0303001404150f18ce1698030350410000701c540d140d00703110030340303512150401070541708101103800d0703048410903102e40040e075550f014140c484243c1c0481040d055031005c90005450003541e00495030300d0380b040d02d041050726004501000e0002e848003001e00294020804a1380c101c1a0b58000c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 807071888 1250 807070638 807070643
    0x7030809030106050909070302040506010f09060c080f0a090510050c10090c0e0c040806060a06020c210f1605100c0803040611041d0115090501110309060a09060e01020325 75
    0x5102c3c0d0716600041e00001c0142c49850081e44004414803c505041c803c03244c10034424204244080c1140e440100040c140c1d01031034041080c00400542008030040903220800241c0d1819500c0c0ca11641000700f03040420f2241600c40c05d501412500851b00450454880000b1035000c4c003e072020171504d07040540ba1445040380c0c208206100041c0040c1d1001c41140503d8842407000d07603481c0740822081c58098007a01452140c4800941004038a400203125014480d0544198080c402e1032640d10440c6101440031500c5409055a012a440c1c0040f604081c04035882000b80c0c032440e11042031044c5045441120380c080780c0086540302c041140311000d150700610440c40440c0c50303a10820000000e0304aa806500c15511002c15104140011000300e400b40100505885e00703207040d10b40081000c0803602c245410701100c0620440c40d00418000c46d001b1500c041c4c80d007075458000410081503000140308a0000550131402c40110350f1011046400e54040400f41007400d110860300503c5440300c403c400c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 807073138 1250 807071888 807071891
    0x309070302041e0b010306050a051e030102030a060303091502070e0c07050d0507021c0203190606080715120c02100209010201020c0114190216062c1b060c070308090301 74
    0x590b900d000b020703041041036a540c1a902c800d0031109041c2c60001d02c0403810302d030920740700340301a4031404078980860380e0807180f40f40200e40c1010300c80031141d001e0010030f805500000400c0884d01c1540c010f042104c1c802c3d5201c401c00356440c02a1213000b050030405d1001a00035070000c00400f010265619044050302c2035a07813074540740740da076246419030040052000c10008034100003941b60070403071191010507445500301d400c0c005030b001a03140c0400d80c01d081d09a20000381d8174030500c903144d4400400781c0003020884040c0341d00c85440141400341414040000b0740f800ba0a0102c8412601510b110070080d50002c01201042e800703c034000c0d401c6202c0c40b40c11913500f40030011a5010900844807403000c0c5840b151030b141010650720003540300d03110300c1c1341c40540100a0081c0c6581400c850303110b8143c0201e400610403003007150304403000c040035060094461302150008a12800482c0120041800869046154110005110003070142ca21560b103107800c02c030000c0000c240e5034002095840d074000c00 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 807074388 1250 807073138 807073153
    0x80d090302161d0c070b0a05070908100912410a09031712150d0f05010e06010905010810051b04062309090103120e27071e050309 57
    0x24080320402032540f000a0300044124070281c80781c0c50020080d000440f084526151a0722a29000d01101000e40800801d070390b01c20004600e2446070303043c0406007100310241d81014041055510140c41d400f80e080d1940720010900307449007400703004400100d500c1d00b0310045e03072040000410b035060b42940e4036082c06a0040170010205c0842c140c010000309441d0748032040d01c2c6045080107800d1f140131414580c5090b0082090340703041804480d0030ba40c8040803500d41c400501c180c03800b0410072890700000600c07038072044030003008000c030641065105403040390031150540c0e6a16084c0d000d440c07080c41040141c2d00a283d400202d08419041207601450614503038a1081e52030000368819030080e8414000103502400400e504400d2521481d00c07203140364843c0741488004800a80016010b1000910107206550301e01ca0240c09840d501d00441401484c0350141c000f1310080c210076042103549080d1950a550003d002c29003c0e05403c411100052422502c96074956015075555101074029001391042c041e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 807075638 1250 807074388 807074413
    0x9130807080a0c1515050d020d140a15060e07080402011e020c031c050a05130b030f18010501181d0f010608070e01080c0103180b010306051503010207080d090302 71
    0x10410001c955880581c83d8101d030801080452082c1d507495041810826a104012031030301d00001950030840b050b0400f005607100251441d04207100052151000c03480d104001540450785c1c110f01d5000c3c0c03100c2000390428070b9114080300c1c128000d0009800c1c10901007080d451054917855840740c4181004014200d03191003806885000044040050340f0007440c004807410140201242200c031074a05d1080b334070085201400d1402062042c2e07080007404940891902090030000c40140440c0c9400c0765242070100c420544100220350141c500d05030440021555501442175a040710516032403558141310146c41000602a08420038039034925030300d2081d030200030900008002c81404000000c125142180090408110f0341c444a021400d10004006150340444c2c20605503600b464001013190200d01700d0500c40c0c5064101411089000b000841002800d9001e11300540044883c10141246102058240e2050b410000d2050b5030a108111003481d89030081c2000a2290040c0d6447c4582071 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 807076888 1250 807075638 807075653
    0x100e03040324050c030108120301030b010b03102301030e0606010c020405060a08100b0315090d0503181605030c03072615090d03150605180301020f0a05130e0609130807 74
    0x1682c04084c030900000040242c00310402c1001c085444400c43d041c00d40d8034640324010301d20310501c142103203650000b0004950700c0ad14244480609a2640003218008800000c44580008412064046464002040104807001805030310640d030503500c1340c401440396401d0001815000d80303410340066107983d0104000300180051205080c40e280001030045207102003601e070a4100d10023000c40b00d203040601600e079001042000c0e8001c91800d0055807601d40d40b2001d080c200c8602d02c1c030542030007040c800001d1440700109113411a07000b14200c4240403c0801015140d01840c1301e0418070040d00c0310084010040000030140c0d43d6014400c1d1400064040c1000844000444101d0341a070402030750910800d0b05031090a048400320102c7c9132100782490b602501743d02c0740c071005086c0601c08051407210355070309404540388455820801da41b5841314007000b6060703404c00401c1901446c810b07c8046580e10210741501d202c3d0200034029011a140da00a000c4c0380218010185c40004081003130b000401c00d407 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 807078138 1250 807076888 807076891
    0x201020d02161a01030f0b100f080d0206070302030108030417150403080a0507031107020108091e071701020a0915050f070827010f0e0609030618100e0304032405 71
    0x88602c100c1d940c1c010340c9005541e1111031142c6107152003000d40188080b80146685c000f5242d404040701c05540c0742d424074501c01c00ca9950200003d0f03813120b800440c000c07a01080d214000c0c481a001c88d00030f0384450409074160b000c00d00500115074002d00081008520400d14150700e072181400341c48910309146d4068008a00c1103800380c003c207504100740900000350f80f1580c1ea1054561504000004c1c403001d45410307504c00c189010b030421005002186500e0b01c18030446000000c41c514846100e500c0291007070715a0a988503560010418402003111024103000b10303154848a50380e001c180074105166561100814220344007009070a1003400d40d0b00c9184001401058050307503030b01d529141d4a1016445c02c20b1214031021104214602c26011070b41c020707007030100d503040f1400e0407802141031102003012409008031855051003100c040c131a1403403111020b0400040d044050703410f00c00000032218142d80c210391092810b03503c1040300b080410b40d013401c80c0d40d50111000074a102c803031180044d00142c2e42c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 807079388 1250 807078138 807078157
    0x52b08030901091202121b01020c060f09010605040b06070204090302030c010501060e15090a2606100608010b031e0c0702130c08150d0803091207030215250f0201020d02 74
    0x544615110030b0085130350362180800d02d0b030300c000d04c0200359007031140320710f03018080c59411100c00d140c1c0c0b00842d1850a405581d55014a40115079161a08500c2d80e1200c010075948000380754a450008a290306150141448080015140629052a80d400d020040061000c04c0d404c40c0810b000c03a000c51a000c0c050035008210a0391442c1c0c17075803203107010040c8031a070488010803058400c01407081a40c469800c080201c0c1d000c2240d000308550394001e5040d80c8008034500140a020b060101300445a02d0b22940041d10700e81e680303119a6070303201c1201c034040388400c3c2c6004460100140550811903050640941e025140045550400f604ea41c0071401402d0310400c0e8120180c0c8600c042810346a000701c0c000d9205070410074951030311003880d01246100c12440b00140c80b082d0b0002c00212459010002c103028059194441550b0b0301c0707540bd0003910b8000880d00aa08224814003080d4401c0908085800340100b92154a080e52020700c0195000400790418400f5550203000e14055041e00744058040c7d010b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 807080638 1250 807079388 807079391
    0x50f06010306050a1a0f0109050d1a071b0803040f150c0f0305010605040e06061e03040c0503061501031a210705030a030f050313020604140415052b08030901 69
    0x14110314040301552401880b00303540a2524014103c1701c008000b4205801c1e030180c4060804010748001220f06951941290703030089899400d0008200f03015400084190b480c402c0003081e42c5408000711446d04550000401c2e40040d070101e0f00104551000658205202e80c429a5000e6520b603174001d50700c0086903160301c82076656426a00c60640000342072001002514040000b9810308002612078000c03400784205c0c81544100245280e203441c01100c04a03c010005110076416144031400036030700845044078041d01e1843d0001c3e46044c00200c1500400405410011007040b01700118024031503c000d01c07001c0300c400200355486403079054803002141d40c01841c00030901900d100d0107113408065449240a64000c050760350110307920583c1450080c02d20328041d0356039190300a942c1c004071407402c4080d502c54000100006e24540301350464001c8901a278050200e6880500081800012407080540040c40305030b8001d000c1170000d0340c0e0526421720303044030398030041d5503190041caa400c205c038480b050741e = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 807081888 1250 807080638 807080641
    0x708030903041505120f041707050c03070f080f0118060c0201091b08151009020a111203150f0d030e0414090d020f1222030506090c13060302090f06030a050f06 70
    0x141c01e01707400b60700c80b1658000b4001ca003070542e40c40b0a021070702c00007009042c4000c05c9102c00c00800307110309011014024102e9801d1030b200c14450b00c07001198815081d152007000003000012406016840c61a210368450b440100f070300b911042d0141c10310041160442d580e4080c6800003400c0300000107205076010041c01e4000b810000010b1400600c4000108020b0160041000c41e004034803880c000d036807006d01c0140e101c20358194196920500c1c1c03080040c03030340540c40074034200313962600146202d02c4a480c6c030390f80034512240500000039910020950000311113508800424080c82d401c002c05d10b0041c2c80018041c0d10044030701c606da0400d5842036040c0d0006e045503002968100608883c40046101404009040101402c2903101d11564101c02d0302d5110320300300ca16108a5020030046801500344c170910301d001600d02d9120002000030300d124251080840003540b01c0c610a140550b54080c007000c07070715122420301420ba80e40007802c065043c0300d03001c10340d00016003e0240c480c0c00500540200000d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 807083138 1250 807081888 807081907
    0x70f08061b0c251a190c020907050c060a0b0102191e060b040b03120415120c1e020f100f02071209030308061e0d0c030506070c03170106050708030903041505 69
    0x1150a1513120228041050030002280c1c103c040455807401e081810000e00780d50580c500740c42101c840781029520098820400c08043e820400610018a501064071a0b80d500c2c402d06108446a4492190043e03104d105501c11742c901455100d001907010b0100f500280414081e03030504640135400440f801034580302d051303503e41428010b2045580d400c8018042c43d003003141c01e4424034000e9200e002100c0204100c1500d09a000c1c0328101a0395940480500c29460395000c0076100d01a640d0004141c0c00c5440700507608107201040c48110800c0c0c0b24003510740004450740600c0502000e18108600690800c51140084c4100c03200c2c0c1c0301c580071501c0e1240030300c1c907504014001150061946008610784440a40541050320407980c9610044032800000e000da03003040008c1d034030140c00081031403040c50180a221034000c010500601c0c8a903440740160400e40800c000e851780c080c03040d000803510a011800010712014003455000c0b40d54411a81000d41d1014100541c95940d955800801c60014441e0b16 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 807084388 1250 807083138 807083203
    0x50903070f030b041b0509071d09010806150604050301020703090503160b07030c060f0f15051905360703060e091507030609110309070f08061b0c 64
    0x2030444000d054600c0b4659220451030b1000100700030019440c25104440b404072442c20708002c3d04001d04402c0c458a400c01010788141780b901d00c2c148400d20710301c5044409140880c07000b4144c40160b0042c0000751605590618401d40e0107000b0b941c007040600c8045800d450901c054800315020b90b603450b9255107003034185400c1c84142c500f40044890703030046c1442002c441e41c0c1198005070b807510340052807144600f0705100501c1c40c00c1e5402105414800ca8610038020750700300085602420740c03140700305036892080154070400c00003203640782da41383c02c0200507900c1e1000803801c6240e07440d080c1c0140c00c01029822181c68840341c1c184e00d003509005090151107a0302d845084003410a8124580e518100700001994840e480003103015280903120001e56040d200e42c10000041c50400402d111004215450b08440d40040b9450b05017845610340004490392819010301c1100c804502611090300d4010254a400a10380f80807080710744200165030051004012035411060b00350035941c04c0d542c01c00b00005 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 807085638 1250 807084388 807084403
    0x10b0303030a0912021207020f01030f0218120d0c0b0403020a0c0e01060813080d0f110403060614030d0c08091f03020d110a022e020c15130c33050903 66
    0x50865000f42181b10f108030f041e004607204103030100d81603000c3e5100a40100c020308080040071040a0012070f80c80c24079507100c6444a4141030488203403a1144d1101100c90307584400e08c55600c000f0f1a03031812540498510f007440d5400c2070281c41a188072501540384d0710100d0381c0e582d002c010115810b80042101d55030049400e6004015812030301804085910303580302c2c50142c00c1c00c600030b45035103031890845100c1c40d43c000707003c1200c40074642c0d841c1c81d0b803800d2501c001c102034800c1e50300001481400c0701c0c40380380104100b5204dc00700d4646000c10741c02a110900150070074400780d82c20010340d00c810818040c0001201c101c03c0810364000d03036100392060400c41900c410001e40320700c00e40c0c14064502016000304003019210348100c919804228025414150700c181e4900d951100341c40013031004654070000c43c1d05440114600f043c008183c51719000e01c40d4492002502518030f0070752010a1295100b0603204000381c2c003801d0718074001d24144410034001c0041030050b030004a800009c48600904003445481c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 807086888 1250 807085638 807085673
    0x20717120f01050d03050c0c130b0108010e0408030403110a0204020409052d06040c02012405090c090a060302030a0b09090f01270807330e21030702010b0303030a09 72
    0x7000c1e5450240402c514021a10004061040100f80012a16802c11042e062240002c141c0381003a0302e081c41d07800081c02100070f510700203141a40086204040c0610b25401030f948001070a01d1a86c075514216503110304901e9581860013464480c2c000340e41c0c0c6002900140181c00400111410003200da01100c903030b094059804800000d0031103c034000c90301d03900350344260b081e5400f0508114441c8121300500c00386a005600e4041038684080e280d40c0a41d540040e81c000b035a1106194480c01c00c4561640912001c5981c00005004140032081c4241c02035a005049980007103941c4003001c0c0007404420080318035452962003002c00e40c4800c0c20901840e20204c2e0b400041e110b03401502502403040071841c690240146c00c0c006001030420811802e55103484480100c8151a410400c00d115101d1040701801001642441590841024049400e8815041c00c601c0c0751041c0c810701455039182d820041040e02075560381c083c0b070101501d040c002948120b800350000500d000c17041c54044000010156038 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 807088138 1250 807086888 807086911
    0x5030426030a1b0c140a0605040507080c0a1a0d0e0a06090b070f0e0d1b0f050307090c020604030806150f030402090a0b0303030a0f020d0e0109110609060904020d02071712 75
    0x1c0f099075582001552200580244844005541c040c3c0d00e40d241030032160000700f50f82d1402c8200b20601102189030810f807401c02040c0e92445040c8002c000000105001c0c0010070440d000f082800c0d007240000403c3c2201203004040351802c80b00503958103261101c04143c8200b0303110b0200d82c0800c102904220f0f80a241424012902d510396940200003440074a081c50003110203140c54000d002e981c80140265040301060441c3c45501c0d8910707604044218442c0314040e00c616034011030000001d00400170740c9001035004102c0c039075450704d00701d074403c1d07020301000c0c1c002d80058030010f00b910600000b88001201c030312007207036030b0305141c818000d01020080604c0000c07071404603000f80b9030b5000b004580d04502c2c1400d001c0f0750403502c980006d00a208044d400e0b0710b0145030075901c140c21401034002d907800b02e000d20140f410000c0d00700300780905403050804240e4040f01c1001004030394078065016014000d414400107043c100c0c42c0c0c0d40d1a05101c80300d40340c0354140744d01141000240c0c1e01011820b5000180300b52 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 807089388 1250 807088138 807088181
    0x91e020325030602090f030303071706010914100e09010b130807050d02090414010c0807120506091303090801180203060702120711030a120906021015030305030426030a 74
    0x340090141075030000410564001035401125540c1c90031002e5152401002e2307d40d07a00b4401800f501ca002649540344d582d039040c1001a10941c090b1b00302c001103032481c1c0156401341b00c8000c00c11000410780c000000030302800c0040c000454442415403800f034200c9034045030b038032200c0e1a00c10400503115407103540e076640103030028402911025503021320242d0694120502e41c84510f0f0603058200c004c0769000a940c40c15101c440010391010100d401201036071038041e80d05080140d0502030b95401c45035950480310001c0404d25554009202c800700d03601924181d60515150128607083d24000c2078400c000c0070310004800b0542c0750600565800c030140340003c141c410f003d550b031446e5a00901002401e900403e500000607a2024005100c501c3d0b80507811082c4c0c2070503502c001e00285424042c400052040348400204a11301d4805c03290082110120311000b01e25558088940364001041200c400e60300240d01c0e1518490360080202c4240442c241640724a010301520007120007001400c00401c1e511436 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 807090638 1250 807089388 807089443
    0x2100204050612130b070816050c060c0a02120d15120b06061b06090d0f09030b1b19210204030f0f06110705030d14060a090b0103091e0203 61
    0x1c0f01e2101103c032407072500590300e00340f0320095441c2030074015010102c80400c01803115070264009128800760201d00c000401d01420031560782c003c2021041855100c1c8010580002418002d4002901d1a2044884a08045001d100e8a8106110f1003a00644400400f40c03640e00c040302c5040030788621002e10080310f10703645440d64003100141010340078030710024620b1108001c0b00e40c2c014a40030420304036400d42c100040d07029510f40340c408105000800c0c142c0550407161207540413204481d00b01c0b03800c160703a444170304000303544d0700f50803805692110042010b03581c81001d0342c448281071906522807d545017a002da45042e041164180c001c3c00500c104400d0000a2090100036101038110b084041c3d0034541d45040c07801485640041445407101065100070420000010440500d0504080c03201c18804900c0c5030411809980e01035200c650400c0c00d00c1044003e40c080c16042005150100c0e05101f151a12649402d030001160b0500d5030281030f403010340c1000c0020328500708482c203000c0300b0400703005c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 807091888 1250 807090638 807090649
    0x2130509121806030c0901140a09060503130c080f060718090e011e0207060f020702150a021507054306060513050612010e060105042406050405010210020405 69
    0x2414001c01e412001c104071249003103942d500301c61103601624155a03814401000b200c180c01c1601041c0c00100b40420303080c6040040400e40c0c2d1004410380381c0106403400c084003541d8940004108600c942c5c058000c4102040030801c1d404002c0c40caa001818002e02124001424910b00030200010301c004407000d003c4154002100c10f04854152100054416600d00c0c0310380548010100d1030300d04160b030680519140d0240d0300414000344502801c1054080c12954a82030b0b0140c818080c2d80078056000d03000030780941c18010b00c0e5134205441610030310340200106040c01c11007030302c2d90700003e9008145240d00c03030094035011510b40c12000300c3e544038215405411640d0880e510111506104e0141e440301003204607000078010740782c0227000c0300c0e0a5042c0000b800042c00300312800351103080041504140c501041c0f06801c400c201007405044c0d960f08088c2400003a1140700d07a40010303030502421000d94044000c0001c00500744a98403140e4030b61400d8002450714450809402e591803041100b00000c0c1d0704d1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 807093138 1250 807091888 807091903
    0x905060f0907140303191d030f0a08090a21030e01031e0c17090a1b06080a0203060f1906091d04060b041e0504051e030315030f07080a02130509 63
    0x1480c11081c0d03e4032800c007090542c0110082c408541d084a0005100c203508828485044004152503511020143d001c2581d0342080a01c9821650040381c0000003050b4200028500010041c000654441d0f44203051056039007200d100404a000e40ca22190030103910807000715440c03100b442e01340700d255400a0342001c200c400c1c0400c231554964800035411030500807010f01054419803d0b003440c0c0d6140c505280c1d0f4a5494401701180c220100092030f40d003c1200101d01c0301030300c09030340e600d440960f00c0c0b011030002540007508540d44201d9004108056548240c0b9942c110703002d03810702002003460b01c40003601c00d44181e007040d458048220a00c44100342e0602c1059032003600840c0c0070650010b820301103801050015135000404000eaa5410906441904140d004900c14411143c10000c00c0c1b050780c5400c102c031444100190420130104a12400e0b40802c5500150001d003542d50001205485074601112a40140300701d0f004a4860419450800141c00ca01d592020061086282001c60345031241c96 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 807094388 1250 807093138 807093149
    0xd0201080609040606120503031b0309120f0d060b0c0c0a0602122109060708060907140a0306050a091a060306031c0c020301090b0105030607110615010302070f060905060f0907 77
    0x8100000900f4046030744c10000c02406901d0801d11b02406500749103449500482d20103030810701c86809110f01a00031811288a403c00a001d464030680d6440d0040c55030380410002c2031801002d014100002080b8458000103001001409276a56440301c4240c0c188250f88051600c115800c0c04100b122075004907281e190740711441e10041c2d032660010903111148444018806c81074100030304101c10b001c400079496016045640baa100c4564070f4600300031440408541800020705902046100a802070000d4501c800d61801e02064183d215404504404205c1d804003050039141c400c0c088015020788408004508240e51072880c1d0710b0702002007680c542c110010b141c0c0100b841d640d281c1c0c444d485042c1140c1c00d5079004000748a00313219410142c0b0350b00c100f8001d842c800d0146802250440c0c0c0105030482c2e184500b00c02a000ea640c0300c940c2d100c24940d6001580c0d05158082042034001340b44100400c0d1003c0c032407500014400304604100b4a40103009002501c080d84040c1406280e00340000c40c4804c403407 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 807095638 1250 807094388 807094399
    0x3010501050f070c0303020102032707050603091509010f0606180509250804020906030c1516060914060f0c03042306180d03020f1611130c0e0d02010806 67
    0x20220142d541140b240741c5000c0c1c42e040044101004040e410b400a502500390301c12604c0e540d1a209088c2c0740c01484042e420106588107441c20411410500040c5500280150035034244c0c80d400c4451a4840508a94407802659500d220f00d1398000c07944075041c060080c0b0701d0460302d400d1f000400c9068010240c002e103846502c40d48005100448502d08a1400800d1000c0c01e5100407101d10004d1b10191054170704a10807204d45000031140d0600092000014000900c0072070042d084040c00784d00c0d81c1c003000200108603d00310546000c18040d0040300d0341a485148809041d42c0200529400d042c00a001d0503070394003182080c4188901d01c841a250041c1c0c0101004c2c1340c1c1c81303580d0f44400c1184040c98080c00540035150401881b4003c0d95038402d041c0b1034880c181d0301d00e1003100341d086080b0f00c11088041090340d410311101403144260700c49207241600c0780700300503c0855840000b0b01612800c52045000d83d4030380507241e0941da0700c071042541056043c0c9580340144104c0c0c1c000783c0160002081c40d8000e1 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 807096888 1250 807095638 807095647
    0xa0311040905030f04030b011d16090f030308012315030a09150219080709140f220b0a0608010e071202040803070203121306050f130609090f0c02030301050105 70
    0x16500e541c08144000e0b030000460395a21100c030807096071500f041c8020345c0d072847c104d80002000701044400d02040e001c003107060400b03030340c60440c4c03181402140d07101001042071984c0081a144000040440998001e454480c003d6142056001010395101030201d80640304035501b946c140c45140c0122118481c46c0141500d942d1244130040081150307400c003515541d01140290420b22107a4010011010760580a40c3c1650400c80b041e02c0c40181070f1000c500140406d0410000b0070402c3c1014400c450004020421054102c4000f80464400000000750007a46007a40400d00300070b84500010400192071903200c141c41d00e039001c0c2002c0414030a6081003803c0b240007910300b510500c18501e410050784021900c42e6240e0001a84e20781001004a0003449941d5140c003510131a80241e0300c0c2d03001c2c00c07800340b0303c6942032410480c3c203070300410a00c0d0203000060014400d050014103041010300f4080c0e44071030000f840c0c075a854040d11649045038400d10320f02002100c006030b0110460b07054400a0070940c1d0748 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 807098138 1250 807096888 807096923
    0x3060c09030f010603080702011d060f18030625120c03150f0305031b0c040c1d01030513030509180a1b080f060103110c030d090629010c0c0909050d031a0a03 69
    0xae4001068007544007000061000385140c0500180c05003c00c001d2148034000e445070b05241d42c0e80c078140c80310401da000321044800040549000d0018a26035032800216036044454400e090329925181e210200b602d400008018034109402c060080004e092075140b200e285032039490b2a0300c160360051807404c10043e04002c240104100b1034500c81400741c4100107984081760001d02c00b071000d110600790080303445242146d940c17081c01128002c43c121900154600d040d660165083e07401040301da90403010a04044d20841d08200520303100761003484012417415840c8545181c140c0c9400d101d034003030160940070320001c001121180c0e03a00c17075028280002e00e141c0103200080c1c28024620301003000c0c4000a0410400302c42c1da0015100e492240c40c0501158949160688c100706010780c4802481c1301c081020800e07580310390b101301510385c01803044400b1280c446200d0400e5598041c4143c0d481d07406101284d8a40e0750610814900c2801001700b000e594820400190b0000f1107484040e010030307180d0001c94030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 807099388 1250 807098138 807098177
    0xa0b0d050105010e2a0d1d190c060203040308180109240e090408121b13150f0c03080c190509010e010801051e130216061103100501051803060c09030f01060308070201 73
    0x11860324a0110340700c1032011000e012640c000e001045038542645240040d20312f000006980a49134050002410f081e8401000320b44071444240751410826950381c00548a07400484c003555110645103e40c0d040c0482a501910f40c91804201070f004100e84402c0002041020f819114914166201042e258a0341000202580c00700c640801c080080095010161000c2010f141d00300e07410b40e80003005519407600141c507038002c1d4601d06004105250002e60001e841080d841d9807100240c00c0c801c0c01d10010300740303c26200240c0d00d60746c0702060000420700c0710fa68101404942003a4240382c440741c0c0b981040041404860002c0c4004076a20540e05926041da46010f0341d940c2068070b401045480309509040080d5100c0c0002040c0c800724a00012204840c00038002c50b03100f040c245001244283c42c1400440d602d60140f000c0d02869200d40c069880c29503420b00080d80901d40c00607801d521401810308243c00c1c00c1c00440c0c80d294a81c0740c04410000144400c043c0c0b008a9024207060500c060207641030740 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 807100638 1250 807099388 807099431
    0x604052b05030f0d0515060304170705070906092f07050a0807061d0f031b0c030105070905040605032b180e011a030702060a0b0d050105010e2a0d 64
    0x41c00c500001c00c43e040c291140f4000b03401910780d009010300039511550211010428aa180160800400c000080115004070100340c038500031b80d10b110713103081410b80350703503051031803e4210908581e141d1004004002060041c15a03400c04050406030210303410315030000041e0300c1c05130060b60036070104050080c00307070903c00c80c9151078118444607a590f08038a4100c005288070b1072403000b032800c4280c0c07441091200140b10000003001000940c50315130129001c3c1120144610610158410301c1c0228440e85c0302801201d0150409490300405103082c2001c03c01920701c190400760080e4041701c0d038900009608203000340003040d4807450003402c62151900f00c4003100504000c00626121100020f15412050502e60407110140e80b80c11102c51205004441840140e400b4130040e8031400100b41200c030a40d0011180c0d46000b000c0856242d92a82c1c2c0300e0940f1402d9203c400d0030510502001882258101c5d11110300c9a480080d0050340c000030b1480f000c074040c404d00052241ea03204c512208103400d0034000c1d07 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 807101888 1250 807100638 807100643
    0x1814010630090b010f0f0e0f0708040c09020703120e0f0c210304030f03031409060f2508100803040e130c0e0a050a0b030d0c020d171303030206060604052b 68
    0xf40701e540c1c456800444094880c80744e007180364018800010f0412510114034040d107804600703540300ea210010110b96408000c1c00a079419880f4000c0000c0120311031004120f800d1003900c0d402e01801a0070044001c440a11402d08890740120300401c03c40301d004a03166000001c101c5800160100f566280c2c14030f43c092004011640c44009400300034003414078800c020140c840d590900c240d44082242d540b040c242920750408913070185001c10010400d40b505c0541c00840f00d600e40d014444c50043c401504c840c0d544040b0301040c4500c0c213002051380702e0b401000107401004003d40c03400c1e280025880121070700904075a42c00c003203440000200540c14400d5030081c40e40b01d030351100604000c0c1c81000200b50991b200f4000300e141c9081c0f00450700340841e0a0a4061131502d071a00c3c980002e40030300c000c1510b0f1900c1180c4000f1b8001c9255030040742c400142c404110044c3d40d03a4038150a52901a1404d0302c0900724901c60380060104219641d140c0428005000c0328144d040c07003100e0b00c00e07452500703a107221030b00 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 807103138 1250 807101888 807101903
    0xf0118090525120f02070b1302221505040905061f0e0c0a08090c060d11161b0602010216080f070c030b09071403030909060109181401063009 62
    0x200c2d0355a000710030411100c0c02d40000c20482c040c00c070031031049204a02005045507901d100046188410800421140d40050301030302e03500500091a1240b070302c1c1241d4111000d0342d9400200c21701c6140c8000c04018100681e010000c01c4403a4450940d2100c000349103070010b400002020800c0f00e21020128000d04421180c20124103141c4543e0300a03401603c40d4500040c80540000c40b900070014952040303c40280201385000758443e4040b01412811a25048c400401c010666000160070905503c0a000343c140090020b40081c1b0300c0d040091701d0380039408582c010f1100c0c40c4d8001005440c032100300e91040703d140d41c034403020300551014000c040e030250040d500000c1c0041072100b104640c1d81704156140550382c42c15210140400101705072800c6603010b030301c1486405040e00f0049089504030505040000120382d0342c6604950210a10700740a903815115408150080c3d2401821809030100b814202a4a038002c02e00c445900001105481c284c0a51440129150f119502007840550030420 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 807104388 1250 807103138 807103201
    0x1020c0105191a01030b0a0302030a0809030f0304031707031e111c1407080408060403020a1104090f0f2406030c2111010203090913020f01180905 64
    0x44140c001c01046a081d66500c180340303404a0101c140d4030032101210466440780c010b04507000011002000031410303590704800007850100240c3e0b0204042c0215034442c13500e80380c1d960380c480305042c149181c2aa88401d41c0d0700900c0244006001420132015003c08050480d4413541c840c203040ba240418414040c01e8400d400c043c04920945c420b0b60940101401070445080c900c0d140803030303e55440407841381780018100c2d4240c41503072401003004210741030040030080c6c201511410318a04080e400d075001c90250340725020034020800a0248500c581750122020481c20141e078031041140084050000d150300b540340080d40c10070401010001810b81a03074a0308140701c00318411480208118041520442030408002505080d098004030034100c0c2081840c0014140d80e49680d0020482000103055000600c90700c43c5644030564101d20403a80b014a003e402d498500502420f44c1d06920b03520304118460030600c603100c4c0340404000884100c6200001d00e5a2200c0800300c506083c4e1405880076805e004 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 807105638 1250 807104388 807104407
    0x60f12050403020c0a0f0609061b020a061709060709031101020a060629090607080a0908030f0403021f080601180803071a0a051b03040204150b03101e091d0102 70
    0x580300113680d41074031405801d64480c031003803460000c944612000142c0c403850901c51184184035100700e00d9003000d02200010b5195000464096254101d04000b0318a1042c11210400c048401038100c0d2108004d030281e1f040561009100000c50b020152000d0b50b5510500a107074401c08c159120075130802801c100c642d40fa1507444118010003c1141c0d440011a0130258072000000c0860b0540072004102e6032901486a03903180c1340b81c110150003c03c0c403280b84000644007100340010301940380b032074030f07003503540c0d81144104080300a59500184101400020712103026400c0300c40950806003d007082c00004244445141c561603490300300325054040481d5810410001300051030700c0b40c401c1e0282c4411a0307246060031044900880c1c0300c18a001c0842806001e10000e040155085400944082041c94900d01810790607039880d03210324410b0200104000b028601c1580c560003411840c1c0401061080c1c0750505aa03c20060003110100c0b596010f902c00314580185074100c1440c002c81c02507480b0321410 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 807106888 1250 807105638 807105643
    0x50702120f01050601020c060903192a03030908060610030b030c1302030a0b0108040305070b180d020d0e0415140609091f061b03030c02120c01050411010c0b01060f1205040302 77
    0x2134580b1809441200107802c82460184140c40f80d011015005042c101c044a64045160742d101d141504c1d9152018080381d4401e40c2600c0024002c1c4c012244030501c00d1035441c0040500c000f40c2e101c203c1d01d8024405100c01513843da05242c03c80e8105c0e14020440f0040240040c0c14541003010042d40468074000c040c000750200d030040c6200710b89d02001000301c030140303000640d000c0c0b0084030002c00095040020100051404008a401501100c0041d20a08003100d201e4604140110980b0140e0b0260315900400d55000d1030b0b80001e280151001d1081d1007440d803200c58164000d004003801c603000700b00c00c1c94007a03e541058858241e8000c100c2021802d0129411100c241c0060241e000080c1c1e82902107406401608640141084501691515a4103480460007401480381c2c100440c0205441c0d82d4180c102c810203003031401545800012036080c949444028100d1060016047c011130b007100c0c3d4041a107408010b4119012400c01d41c180c41c41c1c1c00310480d008090903a000047c249014144010705a00 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 807108138 1250 807106888 807106891
    0x212070c0302150f0d0e0307021215180304052202030408030a050a09020f0118050316080f060603030f030717040605010302030624040e0f071401020607091401050702120f0105 77
    0x343c440301880b82040d900d0310031500c54001c00750102c1e00d08001d19881e04106600c40ea40a640035402d880c14181c02da4001501248400034460490348231501e500b2501d0520510160885201501d60f0b104880451090392240560322a2611504001c848400f0a882200070141d00310006a01103540f464945801c250381d80095508c50001c03450040052041050f03071151051050b001400341001d08602001150442d5071200321904c4075820007c001030035141001401010b078000e140c0500700e541003071250351825500c1c1c061007189030710003000e2003481c2d1004400c40d04825014580156a41d81e4000251507005030010070040c1c0c080400208002c0c06120b5015138141c81c400c4090341d2064a4a144c84002442c1c03010302034090035091100c8400a14256114881c400040c0041e07170305030044800c500c3d003001d001e58881669080a219410344a40c4d0500c902640318445040981605041442417504045144e00ba60705024001030240150740c2c0319000c52070003003a0f1100300c40c0c2c0c20580030182400303042c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 807109388 1250 807108138 807108143
    0x806031e120928170718020304020d020a06390204110c0601140111031317011e0f150e012702160201020d031e0f020c0312070f080403020d0c030212070c03 68
    0x702c0c1180140744c8140861410212a00c4020700e088442441450740025440900200e910010342544d41300140c54840c1000001d0190b6210541e0080540c622010708101d0a80420b915111000455406542001154101c1380d01640c0026400400e41c1c1c6142107441581603d100c584035110001038003079201d0511131003201d000e03610301603170202992440c2e6036070058500e01a2290705400381404400d1108150500c00000ca80000c02c05141e0b13400c5d00d9214580350701e10009020340302c0f4110400c100e080e0007405100080b01001c5182c10f4a01a4032543da000c06000b8101403504a81c3e101110b8952184980c0c1c1034004102c3c1103545a985101401c498022001c00b00d000d40074094044170030b02c0c020712890700003001e91003685d03104009641507003008000d101c0d124000785501b44060301c0781c500100040d010b552440c0c1b044291500301150301070001c0d00c250f86c03040204041070303040100195011a0004141c8141e0501c403a00006500e001d83c1805596441c00f00c1c0f07144d002c9240b40610082000d000c0482e030 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 807110638 1250 807109388 807109409
    0x10e060f010c1e1719050c0c042021130f0602070f141b06030c0906070501061703040609082a0d0b0702071701090314030c07060203070806031e120928 66
    0x1c0805c030f002d07141d501404804c0c8101d80c102d550020304904280e000381240c280207480d222080354240c01c040c20250010198080796205081103a0543c0054618068010004021240102d0072566491042141c7e0030300c01042c564020800d40c081246481e084c4012030362111031841203000f01c0003620350310800c1c050000c0004a07140040001418500100c0e8002c0130624240b5140c043d00c007040c0b0100b03a1045108840566131500001221001c08541e00740300380c0d4020245d03544e00c9c0b9012004203000810307004a006a0810f010190b8030b0086480c1a516140c51060546020344032a4005000c031504000c0c09800e0803405020030028640c0410880c2c00e840c40502e0115620702501242800c0f128040f00043c00300d461260303913201480b049800f8540c032040e8542064604011950382800342e030001e80b10400801e9040060010a1a06000340c02802c3da078542480b10a0103c5142541d803258a04562040329800065088168482c54592a00b00c001d18480503880250012107082150a81c440c0317a0840b03 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 807111888 1250 807110638 807110677
    0x30c15071b2706030302120f130b1e18040f0b03010f020406020d02151803040b130e011205151909050c010f260601170906010e060f010c1e17 62
    0x502d51403154a0640c0d0701907004200800c0404020680c907803011010810f40c1906008204d0a01d0590a00740f024140c0c00020700e45a451020b4403141020072110b11154401062001400c01c061801070542445001c460228050082c030a070880140301c07000740a5059400e1400c6125084040e4004004a403d1a4201c400700c4c5a0140101c3e2100f84031180b000c040300c440000f00d034500729020806001105d1180c2600d11f455030742e503603248446e403110300700c40910b030304403401008003000490722a4010030390356055042022450740d840c0d40f2107100b0400030031000c1840c000308080c80340503440800c0d05480c1110400c907200460501c0e03640e030442200180e0000d1741488418403914451400006e030740000450351058050041084150600c00815050401c18501003000042480284040c050400f503c080e0150394108140c3c9019044000c002e81d011380383d02c0f000343c56075907400b84542c80190b411080314210780c500c1c1d05501c005c0303000c1c1c40c00252825031448028086803903207100800c0d41c1010003c03100305c02c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 807113138 1250 807111888 807111959
    0x20d050403090f1703090402030a27050c010e010e04090524040c050d03050d05090a0c0311041a180a090602040b1c150e19110d0b030c15071b 62
    0x90441e11003e404d600140041003040c01c140c1c016542002d0030131000709444210b4918441d0110144064040200a09654a09002d0184074168045c2000c5c41c11001c2400d07100c00180044154691042c01140d44003005001d0120920104205040b0000b039588040700d040181d0006000a4405a074050090b4400059501d00403041000e0a641602c94074140301220185e40020030005002c0083c5010b10071200700081d1b521600700e405540709040f81503507105108240030803941c424011001140700608121001d50b1044125130078003014103240f8441d80d1f12418854040c060a19009004d5170001c5404102000d003c4054034070140f00d900000646404600c0e090305a03a400342e10100c40030301600b0188654a901703140e5030752055020103a102c416034428003002c1140d050a464480800001c82c4810182500340290a10a00704400410400d0426000248210441000c0905807000041c0d88d034100400c41e601c041c0098480915804010354401d01c450000000502078480c103001140410403 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 807114388 1250 807113138 807113159
    0xe07021c020d08090d2001091502180a0f1710060e01030b0f040b0f04061b020105060a0f140909191a0a09030c0308060622031205040b0d020d020d050403090f 69
    0x7100940d80c4030195451102d04c40c8179856140e01d1000a15500e030030323003040400c035000c40034181007030084001030f59021503903c0c146040040f2040188180d055581c200602c102011005068803904030070782541195002400746440d00c00000340300c8550504c440010f00c0340c420007005040700e0203200490081d54810b0000d0900700002c4400421090184022800c40140f02c400c65a016114540c0020340c1c2003400c880820b201030000801c00103070b4680003002500e00700a0042001810f00103580c5141c3d60400c8004443d80119180030360280415000044074a00100192506100741013062070485400781041c000e48404c29940304a007070f90100100b0303042d030168468920201d81503074031407454016507501119101809400030782d001e40203010f42401242007030a2a001710750280c9503501d149245142010945004000300380500c04140000c00ca010392100c1201c048003507560005945440310640c2c0c0000740202c03803201315024502402c1108058001000c071054507400c0200c204000c0e80c0300b42030340 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 807115638 1250 807114388 807114403
    0x90f15140310090c0e09040c0303120c050702100c0b01081c050702060a1425050118020d0f03140c0607090503010b130905010f0216060b040606090e07021c020d0809 72
    0x2e101d6454a010010341905034005642e6003954a03010050009282c00103400b19419101a11092610b110802c10150000c60881c203103000501e0911000501040107020f5006a002c041c2c040c2240c001444a10782c0b0608100e21442c0e8070034083e00ea60b5031681162582d4403022410000d1b01e034000c3d01250301381c600440c19525107544c000c100910700610fa613421152255603400d007038240b01c3d081c42484a10500c000451017200028204100420448d0815a0a488032913844d0f20320030310b0f024442c0b409600ea102c0c10288850f0000f0300c21030b80c0700c3c8918040380d40c44400141040302481c00300308402d0019020071991f0040c01c5650354601115192002c040c00c90b00070203143c5902181d0340300f500342742085030f404c5055038900550000500c0740c1e00e20342e488144d0784451000c15000f103010207480b08002441c8913000d0600f00a403402c100103800e082d000351400c900c3d805280c640c1d03010040084c00e00c2d4400c02c0400c01250000e00c00785840c4852034000783d03176282c41040d0400441c10f00400680c0c003820014114 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 807116888 1250 807115638 807115651
    0x1b1504080a0f1a270709020d09051212040201050307050f0711010e0909100b0418260a090306020705160e1008030903061303020a051f06050616080a090f151403 70
    0xc1c01650407813680000d85184100300300064000c0440c0090000518805400041030045022030804024509242004e6403004605e8001c2c42c140407142102c503001c00420762180c1c2c282042c3e40d41e81c07980e13881510103019540f100d032a08540007a9440811103480703410041c105007a00c81c90b41020b001c104107d0034540c1160074000c5d69008034840d0001021075000b10441281c0030b00300207800c0722802e918440d007034a1104d0a9030320068072440303004140640c21000c4407640079030a03124100004248000c001280d1884060005a004501c0380148a0180307c11003460100c1c0f000021069966003910400030300413602520f072002640c1d8009020b8401008540346004c008025140a565448003049043c0210400342c007140324480101c00010800c00400350078600f0310119011b501b502c40c0c03002d8182d8640340c0205010f2002440044090702032001f440002907440780186858103c0c00c41c00b00d5400324160311501400c0e110743d00025500c41001e1250101c540d50b592003e0b108070459142d284507100a9520 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 807118138 1250 807116888 807116911
    0x30e180406180213062610020d270303110408070509090726070501050a020d0e1518240307120f1d0f1b1504080a0f1a 52
    0x140001d00740d0b40c04a8000b105100300120b2144942d004912088440c101d055849580d54005209180c0a05196290141c800005800c0b4545007140e080e2103210303501c42d14546039004218414003000e140c2001c40140c0c0311034490000004e0600004228030095a001c1c0d0129181003100d41d6540c4648007140c0a131050000240359141c0b900040c8195000010105a802c0c0590f580128100440c0400507540102c01400308010904582c101402c0071550350000781400b400b00464000725070003062205220003d4104000e108440401059030305800c40c601c0c0c0800c040010b08080b00c1422041c04480c1e0007016220030680001000601c08268404403840460200c18000a43c4243c4541075805541a0301840401c1796554989000107880f0794030000360721049210508120402c04100b00b10003200c02c080107041d05400030614a0b800f4043c050200d02910740c00c07404802c4c9a00510842e00101880c01c101e80ca0307090b1506207003a04042032541103519134105017204c04120780d1140c48074001d5046104 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 807119388 1250 807118138 807118141
    0x15090d02090606160507031104330302100521041707061401270506090109110c03041e06050304111c0f0302030a0306090e0706030c02031c0603030e18 66
    0xc201807110020092644004104410343e40e225055080d122101e00c113600801b446815032511030150078811540500491410610030301e9212410b51040044194600c2d241c8001c680381041e01080040c2c0d08080c2d04201f05044416810b5803010040c011400c101440000f0715400008562002c401941c0241c81a0b428000703003000d040c0001c005048940c810320000070850a4001c100d1048034090b07200d18103442002c540440a211201c110001e041400d000410661405e500000d4180ca8180203c0001607950b4182c4800c03050900704444400000c0e200312a21169200d501445640140140c08030740c1c1c140003070024055000c0ca05982c0295485240c134039110540505000d003d228550741d42100c0070b00e040104003c00e060a5902104500035800f13503a072129001c4003d025101550f0149420324030304850319002c56000705074403095940720300e000300349080d00c0d8000300e18501800e0303001303400141507070032200490020740e01110481c2e1080c1c840c0b10541080904020b190540c030903105506080060 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 807120638 1250 807119388 807119393
    0xc18101a0703030c090f030c090c0206040b040b0604060f0b0409060602161a2a071217071112030705070506040303050d0902010909020c030301080f03070203030a1805060706020915090d 81
    0xf0400a241300885c6003101041e41c0d14905032062607074a500c29030381c10b148400103001c2c1010901079600c2d60044c2c1c1c0001e103114249a50b03a4040610024800780c0300d400741e540403519945d6960401d84c0180050000846010703154411115aa130241c401c03101c143c0d203094800140d803400807400c2594140703003110790740d2600d00d40f241e01c19220f0058040c294a000341000700d0802c4084650802c0052440f2028400c500c1d200000782d80d01d4101e040e00b00011100d01e02034603030300284140103010178a0034014003182c5c8070611407402601c452240a440b50344440c0070402d0881c84e460010281c0b400d140201c0855142c0380d903400c240181c62180d0b0002800150081080d40c0141d6650f17001503045a1040c5484886030743d941031108226005101038108036003000004101201081080008555081010b180b8054075a03001950300e2043e280098184030002d01c8647c0c00001d9500d061000f000d020341420b6a403e440e1030000000d60202100b2841880300103466402c03001d044056407980c00010b010007840c0da0068 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 807121888 1250 807120638 807120641
    0x8060117150a0b04020309031c0227061201120501060603380a14090603030c0d0c1e0c060315061b06090609140f06060a1203020c18101a070303 63
    0x2031400d14030b10b0b100c41c0da440c007075160b82c402580305003600d4014589902076209400d03120400740262040a50040c04091260101441c0c00e4401c1002140814084011000450b41c207000352144000c0150483c000000c440c0d080c40ca105415501c85c2c402003046030f072241015002c40e82d04080b8001c1b1030031405048100d0b6104103d500c04202021140c80054141420006e61700110759044602d11032128040d503659428034803001900b01c00c04901075810195150324003580c44182001d00001c004082140c1c07000d0085030400462000c5d10340390315040c0d4a950b418500d04508280c440da40000b46442c140d503403103260382c049001c00d85100e0364459940701c0c81c06034503c0300090117160594503207a80380840d60004a00f445007440941c880c0040703505008404201c1b90401000603070b1542c0d0754002c041044119507540e801d0321b040c0c0b03049040c0d090300d03455a400e04070b1a10446c2c68419422180044101401d13486201d210752040141c03140603241291516001a506001e114107250041070511060700024044d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 807123138 1250 807121888 807121891
    0xc02060612011b020c270c030606040b0d1e0504020f01080a0b090405072103230705030c0604110a030309090c11240c030c12060f0414010806011715 65
    0x4800428180d00d240030b03144030f1203004540103025034802000f680040c1820802c0104404803c00341140d540002000308072600001000e80d0741c5031000100244c0e1075601c840a440292495800c0c0680741c0c4450100803009081c41c40c3c80035440301d100300248004280d540902880b890340940b2518416114000548609901800d41c2039019203c1610044c20344440812503c40c80c0035400900105140485e40e2059011a9807200e003804071560490001c83c0d0408134031580c203440004064041c0014541c00ea6080c007a0460050080c0030000e21805400c20008080307002d5402030f403241c0c40d040f14480c2007042c40c0400f48001000b0511200c1d04002103d51130f4407003031100001b4185001100b8a00344400d052849404803107a050030700c040c40011a040c42413015600076130003500c0e11714600f4070100c4030040e07004070148068440080710005699403155450380c1032580e00030b00184980480104000c024400034080c03983c0901c20035000007200b00d40079900154848012020b403044803105200702a56080 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 807124388 1250 807123138 807123169
    0x9021c0e030d140a1103070c031d09040305120c04151805091003170403020618010201060905090f1c081b0c06010f050415082d070801021c0c020606 65
    0x81404045000c400360301070b00c0f10700300c019460074045140001c4040100c400d070700401041c2c11010310811040c81d4201442c510500e4041c203002101030602d20600703820312112201e03140c02100c8034080c4803c043c0c000019100c01c550740002c4181585d918107080c5554004c5104449207003202c20140140d4174003918aa5800e440519041c0c441c0c10703124000300d0249a03080d10300304240114034100f0824010040910100c4000300e088603494289181c0004070580584500504c0c0c0c040d1343c2000409070385c000d510001c001c099804040c402883c114140301e4a5001403081c2c41d182d40500c0c0681050b0656012114021344580d807503209003070312a80d080035110380c040c5a1070856110104100c151410042203902d0081550701c14440c12117090800303110940e0f048203141403020208440c103009200e8082822890310f00516001e40404c664404040c510400e4001135085c10301031005c0c0881e0401c1e042d0000c0401e001c01c2180e0782501001d520204044515584940740147c20030000300da440d01c0c3c1030680608540 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 807125638 1250 807124388 807124393
    0xc240204144005180d0e0609091807060e0f010306050a03060c1103120114030613060506060403020a090b10140403020105030403141201140621040512040b0301030c09021c0e 76
    0x480a40d4804452040e07569801186031303040d400800c0300701045140011902c07403030503801001e0700d58040303501801070111a46c41403e1030342c005110300984c00c0c4214840703140b5404a9810540d554809440300007581003c0d07000707c5900c1d20001c0c940d4003a010700000c49002178400701980d45181c035201d00415054150300100040414000506c82042000e05110280440090015450300e500301c80204420050203010307400c030200304a15001c441007002c1d0899005400803031a40d031384c1b8001401c2c4d031040c1e8000a42c0103842003804104d560240d44a80b40e0200b040d6951140c600c0011019a05180300d2806440100401c0106000551040029580251280c01e14001440c02480015595040013044880c40c42c01f8500400510301070114100c440542620700764075101039039844200100c0d910b40342e00c03041400c60000c2820002e040021131100350200881c0c545444e12540155001d41c02848195021503100a012070454114821120000c2103d51311910b1411401c2901c40030b42441d440210560 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 807126888 1250 807125638 807125749
    0xc0e06040311120a0c240e01080603010e190b0108030c1903031503050c010e0f1c0f080f0409050603070b09012615011803030804030c24020414 63
    0x200b041000c00c00c8584101102c81c1c442e170816541d0000c0103921140980036000c0340038585011900b07c040012250f900f803a00c0305095860201290240c258030300030716014400c1e00f06602d526110148c076010414400c0c480303200c081e6070f9a480565a4028114408802d82101c540000300c1c18000c002200818482e0130040341210341400804015051a03000381c560303421068a41003e583d1102444407580780440c2c03100038220070003011400c030b24200c030f080311b02d0041503410f0001070103002d05035141c841d030744850785541d10f120130090445190461300c10300d28502e00304000b00b442480c0c08640e580a842d103078a4094282502c00004503100a1403500301000356022906152039a485a0304041c492102d0312001c06d20403000303500041100740101091003074203c4911007880001d900001d40c581003038041c60400c0b140980c40c00c02100c0100e40d9070111008000040d065548510070343c02070000c0303900c8420605041228101400310541400c400d56821050000140d404009610045101c0505055102c03000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 807128138 1250 807126888 807126919
    0x60f0606031b03010603090204230c0901020715020106030309120302030f0f0c0703030f0f03050c0901140d060e040210031a01051b0307050c091602070905180a14010c0e06040311 78
    0x80f40d100780c000e200040d0300c480416055083c24000d940c0300d900070341c3c02c94002100c0d80050256000d00500320000341500000d21004c2c41c1c0c401c0043d41d003c3c003c58054042d03040c0c0810000703402015644800c4002c51141580000c3c1c080340c0a0310700000c41c0d0150061490705010301010400c40d40480c1c80d400198605002c2540b4a10003000060003440c4039884510030031000d28409004491400710303030400c0504240070000d00301d5544090b20300b0074070207003805060601280d16805a5010381082c0719491407800c83c2c00581c1043e0420f0b0540100c0c000c0c0c900e00e00b00e00524000320260785404000050f03220303003490815a154440c0740144004c1c2010840680a2082040902c0c1580c0c0000030648031507004c2c450704000d0789003214290350040f00b0701c148000115610b02004e52500081d1155500c4e0383da4910014201d54080d04040480d11000402d9600300c06481c41c242083c0ca01030390030000a907207443c03410a40940180c1640c202c1c807000400c01810a0310310b585800c001900c000c50305420040000070902e5 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 807129388 1250 807128138 807128191
    0x30209041b030903080901090507050f03030909040615060c08071b090609020d150609030807022715010f2708030a0504150c020a09021b03180909060f060603 69
    0x10211995400f007400261030038000c1011101410f5000c45034541100400002c4001a07102d04940d03065070003030070b00d03074622000a00314001c0c40c40003078010010004000800000c0c0c1c1c081c1d886102810100204c80703031504011601e01484120040401d10104682000300311115980c0f0a0212607100f140c0341d0300d44900300710701507800c80e41c8580c081d580c0105001d002c00105015602001c0481068005058a401d100800009440c403000c1c0c4103010004659081d92680205a21441d200c4181038007100d503a2180030501c600d044501449994139180b0b400c0300da603c201c08c4100d8000d016501c0d10400503090041c4070300744c0240502c0d01405081010300045402d001e05c060904890039442d9079440d50704c1e02031114019004c054010042050115004d001030340c5809146c3d0503106a80c07001620303121a041c2c404503600111400d03403020307c8040341d10680e44040c0c01c5802042c980c2640c0310402c0e44c507a4140b1940d64181540c2028810518034000340316424030501840d800099044120400d0f00d07030042c642c8 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 807130638 1250 807129388 807129431
    0x10b0717180f0607020108220501020a0f030507030e0c063601080c04030b13061401300521040e070801091b020d0f0309020402031314030301060e0103020904 69
    0x100884a5004000291518a102c9100003030300343c4665290410f01c0d40000c0c000c0c10014406041004500001c1110200c1c426035002200e500000855895411110241a07000031910840000c0d041ca40002d10403071081c060100c1c3c200c0f0746001440d0340c0d0b100108001c001d400083c2c40016010026441c200a0801c0308440554054164558003c3c0b9516100041c00428000c4c4001e40c00d0700100700420000e11030303c50702a80030703c501d10f80c80c1d4100c6891130b240016040340d000708904e022103100041103034084d8110a01c00000016407a8000b6602411605040f048004002e02240c2026900c0114854081010700c10400c01e02004c61070103403900004484103105482e11000181c200c1c00502c450300640c410702d01d6564201d90310800b1129540704c004d42c0d964000704c2050400c250380d14110800d03800307a0809450f0070b50040040d52a483d295900c821490705807203051b40c446004130f9452401480200849050b54402d560b042e03616030114005402940c00030150542259403a90a01c206a03a46803654 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 807131888 1250 807130638 807130657
    0x60d0501141903060b010e190905130f060b120312010510030501290d0e060603010f06031e1506060e03100c17090102120c0403200603010b0717 63
    0x140950400300010401c90182000314041e50301d595500c0010b82001c003491040741da020134040b42141012004841c80380111800079000130492500e011105110012102543e1102800300032990780d0a040c110950070803070020b000d03c82018030340000f040741c940140100c61800346c40110f10302c000c0c0344058030b56805100c40701005151500184090716007003425a00000c500d26081c4880c3d410710004500c41c1e104001201020303440d2904407042c840c1c2c50400d940042d510150100840e051184890b40c8407001150950b00ca07500e0203029449102d628400c03101501d4009200d9030656480050340c034407040b43c100082c0c9140c5c3e100d01c131031101000719000c2c0c100585410303501d05100c4c8a12505144c588030803406880c0301141030541750000c0591107502d1010f1070140d100b1000882d1160300c5114020710880100b122064009010031030407003203200c010f10449215110b6010398040c01404c00c00c045a10180c1a50f228508000400c0602c00c14801791003183c0c020300c0b010b0000d21680004019039807084540 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 807133138 1250 807131888 807131891
    0x7030c0f0e01050d0c1403010905100e0c030d0801061b0b04060f05130512090a030c0b0a110f0a140f070f05040c02010504020904020d03020a08070b04140f15090309060d 74
    0x900c0039251100c440780c01044103858a02852289079104080c44a05024a0728007180f50b41c04200c80b5502500650f040e60381041c20341d20140d10001c0102d0103070600c030000ca1480e106092070f101c190f0034006822a100d00030782c0d9075080141d0a101048880d0242030a002c0301075038400c24158003180d9151075590145204060005844580000c040c09441004040380600410141e0b88400325401248400c10f24904101d4140d0314460b0000040d10841d441d0006007410100520101d0412060002001d00150b1500c1c0d040c08240710040d4242d07100d25001600d26a80c0104159a0003e134656007194002000d02c8259101b040711980664030b056442e03171221700300b8010308008001900341485007403007405191000380140c0c030f016000b00383c500b030010344000c0c082c1c1c4a6006801c01e041c0300f8004401829402052640e80e44164107000e44c00c03940c01d0b10151240311031010700c910000c800243d0010060442c8018080010b40d501360103444070b50007010300c2d880340410442102c269036948001d010341ca400d07140 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 807134388 1250 807133138 807133169
    0x406090609080a170d0e0303090106030203060c041202100c1a160906080f151509030c010f0c15020c0f0102070507050307050105221203080a1103070f030e07030c 71
    0xc0100340310015804601542c002d5001c840c041800c0000341d0040912003400c040ea140c12011003e4010441000c1ca03200d280004002d00542c00c2041d00101c0449008504a502544600310106a28401c911130301282c1e903404080103006003407131a01c086841c50750b070501ca030000c002921070b000c81d10000c2e04102c55400c1120200910492481407404000e840d500e0321020686c00d0840203460f40202400c940c1c1c60490f0140080c85201680303500c1504044042d1202d80c04010a2402058070b8000884040c802c2c0a484100c5405503c0342061886000c0a40d5908202d4040c2d0f444001c101c005040c043c10201e80c007046408214181080100d134030f00703403103c0016500c3c1d0050900c0c5041490303541007288a074015000810082c2c1c3d2050654003402c4503041c6144140d1030071280174020348c0310f5510400303028111a00305000c0c542c204c109144126030044c0d0a00240300d400458248a200803281c51b004034039400d0100c580c0c2c621903032241c000550341c01c044450154883d25030701195421075008604102c020203 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 807135638 1250 807134388 807134399
    0xe0706120b0607031e0305190209120109031224090906090506090705010809010c0e100507020a09050609070918090515090109050d0306030f0308340311070b041e0503040609 76
    0x50000d081461546401c207c1414900086003d207510003004102e0340380c01040541050f9215071507812a006030600810100c021403402038003041100280860207460641d601c11400381100088042c43c580d10400308006003001c0c1000d00034162202c0580301039580d8920800011400c201003801743c9501d00c02401e9051038000010280640102107074807690500c600c1d80b1081d5044500c4020014086580403c2c82c100ca0340c04903154090346030040c2d4081d45949000404200951001c1e015650a03036141500b40e50300402a6100c00383c5200d40c6080c1c0d107821075655001c0c00d40764400c4440500c2001038842548003600007056108065460400a96540b002c0304200501000038134518101400d062014031300d9602c40d2001c2c407081020250601820900180c15007800c009080f05090210782e0000e86692040c5048002e0710007900c504010030310700307011801070940d0310043d01d405d00d51110b0f880c04541d44995900e55241041c4039002d03909011401000009003060003e4006803001c1d64481c0d20701c13072424 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 807136888 1250 807135638 807135677
    0x60905100306050f0d15020324040203040506180709110d1d0604150b0d06060501030501050105130302060904090f1a070503060303030a0b0102032214040e0706120b060703 75
    0x6101a05152400301c0c10000f545807801d01501c0c15008440e41c401e8004a42414184204907840c3e54828510002c204450322540c4056400705417040040308410440d260107200482c07109503000340c2507030302460002d00216188506402c0d100c0c650000d03900c845031381e103820030300f03981900302c3c0b007180c4450110f412024a40107200325420064802e64201c482d0007403680706c0d0b0711050040c1001d800c080290580007202c46903030300312402e0850b01410000b03c1c1641418000d000344400e000303a030300203400c0c840002241e61042d404d444503416030318869004603183d582088500d40c13000000d99001b0b42c4464840d00441c803404601c09845001c0c003500a201202140141071704400200300340c3c18000d0600c103000003600d00005030b0340e004000000c0010031001c0e48006070700d180030341d8100c0242d0749110404c8100250380c9409200c01c5803032600d00702c41e8200c000810401501e003202480c0c80c156022201c10016948034002d8400d0450702d002002403040000c034081070503544507190640111703254020417a1202c4e5507 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 807138138 1250 807136888 807136909
    0x33307171b0703020c0f040204180e1c020f15090d0302090f060a080405010f06061d030708060c0d0f0204080a021c02041802240405041505120607110d08010905130c060905 75
    0x107c404602d0a81132245000080c140071f201441040d40c0c0b00c1c200132605504104884403480c54101400d0f84140343c00000303550b44c2c528010f248960107062101ca1409098041407401009108007506580c100748804070001d4200c10b502075030011640440e0111512004000c0244603400d81e00c011280c42c080c1015070070348140d91036500c0194a0301c2ca080280c2507000d041030b001c11615550b8500b4800314280044e181441e56003103501140101c601b405a0040303220010310040c0f013030319418041421003203510003c83c000e07840b801801d0b03001580c01c03100614082044400d902070084078924401c01c1500420103c0b1600500e0380640280b83c10850b09518000740e9002d9a0004912807038843c0c0703825514944c85005901c038040c016a203c07220460030388030120651003d44800740150080740b90b1404019640c010613244070012030500c55840e5039030080482c60314480c0c501c5450f449241c2c1d00c0c01843c1c40c01002c005140b48820017119141d900028480c42c04403009110b140e54842e030207400c000c204062540c1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 807139388 1250 807138138 807138169
    0x1060f09150212030a0f060b0a02010b040926120406150803090a0b0307050904051014102715020f100603230c033307171b0703020c 58
    0x300c4440c88a111030340040c40345401000c0c0c0f00d18070b8494444901c81000741c2103a0300183d000d5803e02a021944500f04006001c00d004298000e001441600d42400101c1e41c040c41c019019060642c041d08101c039004258080d4202240c0d421460f1801c0e0080c038552115041d90201d4046488004003d805082d202003d0041e0030b01c14059403406c041100081c90215092007480b10103c1c0c0400015031841c0201b09940100c0c0f406001401a0f1030314592025075004603000f25281d2040100d10121242061140c0d14140707165a1104042e8200440c50320b00d81c030000031041c0301001007080c0041f0703654200159903207016600f50014602e81540200003810a85030001c0030324120703c2e0000130004140024503040d5007442040b2a40340b00001e509245091800c1040081e4040c80b070070001500b60a0b5601302440d0402601964840c4140803032000d411812058860f075001a922a12900103150f030304040f1a00406a03030445070280c100110034290b503800503a01500581c1107400d403540c09003030100c11480c0021 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 807140638 1250 807139388 807139409
    0x1b0f06041b081f060b0a051b070303120f0b15030f0f090a0609080f03100f08160e091e01141e011206061e030201021b010f0f0c080301060f09 62
    0x24201102c250f0744500400d8030481058a201c11210b107400c5540c000f40160580340005a81c8403104000039025502640c43c904280d61242c124103000f800224800741601d40c980d480440d010080003c000c050050285002c1005545413402841962281c0e00070f6100c2030002c013032a40b0303460594882c000e5020b00900306c40b0081d50100404c0503058001c0340b141300640d0b04c079400040034102400c1402550007203600240d41e00d41c0000c00d220034641c02109020460b140e0344280c9a40940369203002e500c40c0c1c49141c03c2d000300d80410509104010500d00590382c041300007803c960b0300340c07980c090305030a2010070711a94849035994000c0d602858941c0c141281d2003400b0440a0105024421a0074004030051181c81b0000c01c07a02c10050410210b41c000c0002840c1000d020a00c01429034007013650780d03980b40f01c102e016126141d03400102ca520240e52403038001c016110740305a5141d1810645405810322840003c0101d00300d420302c000742400703000d54043e12441c1d43d002c007441030700040589614102c0d0450a40031 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 807141888 1250 807140638 807140693
    0x23030f0105220507110c22020d02161103070f0303050315010c05010c0806030d0c050d1b05010e0616080f0613180b07020d05040b03010510030e0307050c0a1e0b1b0f0604 74
    0x14410501c80784c801b42400400142d0f00d848900c0035900074000c8448040d890038bd180b2a8000f84020031114006040c000c800703490005603542207001c005085440010f0208805000003104080f4014003041e40c2c20040c10100640400c507552103085510310528036011030078007000c1c420141004c02c8101c415103140d040031080980d00d500d6160ba1000c00c80d401c0c02c10070800181c0710062000d10f011205405a01500a00c070111011190360344610040381c0c10b0a5051000d0240446a40320364515401441201600324507030301c454083c4898100904054604281ca50049040d4840103035164500e440c015540c4000c40d0811000007401c0c100c1a500c0c00b0304001003440203101400ca044110ba0441c1c4041b0790184511074441d1058005d84484515199a070001103803d00c180f00340461050600c07d400ca40341c0c40110b4441c0ea281d0220031055901d4070020b03441c003200744040356000004040d42c0035148240c0b164051411084c92401003090303049405604010140b0040040190550319000550041101503 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 807143138 1250 807141888 807141919
    0x1406010f0e0c030402010e030d020109030f050712121e05010305120a1b0507090207110103111c1a1c0b060904030e090406091223030f0105220507110c 66
    0x101078041c0c40501c21020000100b400c681c01581c0052000501030261440101ca92101a00811402c981a4040754141c9200c1c840c1c00d2041e0300b21941c090344602209000c50240e8402c80d1172400c145005801c86590f14400c6480d280d01180d0f0100c42e844a00e004a03456056207000f6042c14000045c545512000f0f01810176141e81007c0b2840d82d1214000d03044012451a0a10301d140c40c01c55800350b0403491000610b0024042512000c1003007000a880900181b440f10850103441e215003940c0310720300a4a010b0b403080b040e41ca60040d01c0d04c01107030348880d03085100f0300340004d400c0382d25002048101e00070008404100089aa01541c2c0714900325803c200d03d143ca40c8000d0034500080802d948580080800202040398541c07011210304c1d00721001ca002800301341d0002d454001040c0031103501d1300c07185403605c90001d0154111b9200b6543c200c10701403264038103800d205000307240081c00d40d8420f500044e001950728440c4201842015150b440328100fa03502d5100307505001100450500550994000285 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 807144388 1250 807143138 807143159
    0x15030b100804170403120f0e121002220b03010812091813050105010e060a05090c090d0302100f02070b09010b100e1c21181202010302161406010f 64
    0x1405900319960160410310701448084a00c541d420050418410044c0b1118456024030b82c0d142140f0903131103038108c4010900420240a000b40040360042c0d00c01005803849034401c4c0c016203102e0525603032000c40103581d0340c1d65009100750381d0420b43c10074074040010040034004010400440e100164034524140c840c4001c1404c440d2b9041c06803120903d81c8001c0f80360b8500741c0400c1014260004020006540c560340c3c416951402620400d1045010310400b00d101e00d01001c02c83e01980e1048080c520b0480c0d00024008042c0c1004801c0d4258010078921102418450084d02a190740d48440142d4880c1589071401d01c081c030252000896030314000c1c83c8040b54503040c4044c02507001e030f810309a80810310580042c00340c0c000c5003001010901107444000422a400141c100741d400001c10400030a00c00b03440c01c492a01c402c8044100f40107407600c4c01c2140d20004030500c111709006150151404d9028210480d400c20705400449590400c03e500980401d402d110035409403000080310003940740751201009 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 807145638 1250 807144388 807144391
    0x160e090d1b030804020a18201c050c07150f0f020a0e0910080f0f0f0f060c0d0f02030112060605040209030d0806040b150316031401030803090f0715030b1008 69
    0x10140b210843c046000c0d941c4524101c001003091000140d10400c50500400140c03040340c1c2c0d408c40084c5000d00380e0701031720869800d071a0b00400000d615058100500002000340001400100f04200e080103210080f44c02080309806500c0c0f210380c0400c0010440209800304c846da10700c48070103244144100700c1105d901241d608010141240c1900d06621005140407443da85030707101482d02d00c6101d200b800040800b180740a8410750403c1030f25400ca102c031284030380f40d003101800743d85641c000c80002240d090f0504050502044108000203040d40c1c00c8210b08102d038070030303040303520b03006004192842000100d0243c0c501802c4c0c01e40d000e5081c00d030000d010075910b50780a10f404051022100c002601a2200e5006414a8100400110103032040042448581c3c0c410380384100510481012101414041c0c0501c01c10203000d610325520b1a80703107031100070031a00085e001c221540280e280c2e040100a0030803c4501402075a00000001041164040e084905070400540100c464141000c0c910f42c02c90102d5 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 807146888 1250 807145638 807145643
    0x90c0f030711030c010b0102060a14180a0b0a06081e0706140f040e1009050103030c02010c14061603150e01060f0203070c1805010522020c160e090d1b 66
    0x4940303a4480c103100755860748071041581c41900c00400c1d1080c0e085070541003d658900280c0039204243c490f8900700e01a64645e0f0b860035500b0b00e1100101c1c40d0401d1942d45090700e0700c0e0680698800d03000d503607036044101c0b4042c2c4119010030346078141480101c0044c801644c001050008160f0000380c40a51140c88003120700c01c44003800110f280401b0024043c0d4122b410302a1944803065445458460180207a00143c80300c070340b4602070903004909040c0c0b40c03040605036a05910f80640340c8072194011118000ca02c002200c400070f4640701c1c0c0440c22020000240a41000c2d00c84c1300788014001e8004080b511100300307081d02214485000c01004041c0c0c01c003541920800d103003494402c2d000740c0040c0e20310300c40c1c003074000c18001040d00d000131044044007081844c049994824026a60b9520821041401180001100070303c01d40c003101c10740b0300d5a40100450900c0b407054400c1d01000340d50f20410740000703902944101180c0ca0800804c0b810521880c1311f00906070504040204000000510600a50400 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 807148138 1250 807146888 807146917
    0x1e1802070c170a060207120822120e06270f1f0201020c070602060403120b1e0a0b0c0105061c1e0c090e011506030b060d090206091804030e090c 63
    0x101100b0100a001c03c06a90340c021809650b40c8181d031400d02a82140e00c0c20100c00102c000011442d60b040c2d4088100075484124000c0400e00025107800d19601f02c20505082448041b2200c000592900c0c0d001c1c101d070310001d040c6c80203044a03501c03000a01a0145859921643c000425440c050350b404521400c0d00c00e02c2444e44941c0c460034a070682c0248200300d900540d86c440d004000031401e0b0700154140c4903e1003a5154100517070740d02d181409690040d040700c2c0d407001c0946245441e201c4614800c10b000c038801000c0c02d00b0b041c0c0e1528022503550182481010383e0351542c0c10000c1702d05000003800f040c8803100107070852044058541ca5110369407080c1c805048074107112900c09000005c1c0012000d4005000200465465054498020700c1c92031403070b01c02d8045402c400501540644505040742703d0103817640349008030040082e0018040401c040f40e00075800c0c07156410a841d840c14102007241c450700044190700301414080c000e0030003040014070600703881040091542c0014140c1d46114012406c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 807149388 1250 807148138 807148169
    0x13090f110412081e070b0106020d0906090b090a03020a080a0b060a050303120a062126180a09050705120a0e0a02102303150409050c09060105041e1802070c 68
    0x140481380c070145a800c164075410110756402400900106107040702c2050f000c40e0032502414005030303a403041d03610031600840e805280c10440c08103800010b101d1032000404c00d1980585075400a2803441a42e04007224650245469408025000d0003445c1c0240b002c4800c41101480c3c00d0010395248250740500b00c0341a0054085040b0290315003006000e040d050700295400200b403410400344103604031042c0c5810615410308504a620341c400c3d4000f008050400529006000c0d8201c03099920000080341c0000c601d4400080c20082307845014000c2e80c1a54a199592001d00800e03030031040f002e07000303074001403520b111409041d1000810700b0220750b050700e0000c10b400c0e07201c0d016a007030010041014005417050442c90245400b010045200d03c0a41716800d81c02c0c02c40700b040c0804c0700e541c0c5030014119441284409030030300e00052110380c04001450090b00d050341740e107003c50000c24103207225031071a030381d090061020400c1440700101e034407000c410850600d0701c1610703008040c1ca0b00f44180403500a1b41e01 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 807150638 1250 807149388 807149407
    0x90601060f0c021c0c030b07020109030f03021305010e060706061e05060f0a140909090d111603020613150c03120c0e0f030111160507080f060c0f13090f11041208 71
    0x405820046421007d160b00c9480c1c0540b010b800303054091400c90001e2480002040054000e100350b07840d401e484109020810304100045d58115200626694043c00c24013074800000d0850040750003501d01500304103944031242c0c0b60110641416048584109014041c1812100c50310059801142d0030f441d215403031510304407070b400042c410580940c0e000f20074003042003072001e00024083c0040c9c038280e8921041207042004507484160260410489a042450401c054604200a040d40c402d001101c41011139681e105212140301c03901180d4049084581c5800078580c00500c0c004001c4003003803003400010b4942c00020070303444200040c0d5224004d041642007050300c003580308181901040c1c00940ea41c40c420303080031400206140c4125030504c540c410210382c049012072903aa8145800d4010285500d40c540d000078240c0100b40c15020900e010303c00d000341d5940301a01c2900a000103030002803510811045070060f119082800d040203001000200819000c0b5a00018a141c0101d00591501c0001 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 807151888 1250 807150638 807150653
    0xa05060105041a030612030322020a08011b022107080a170106111204081c020a020306040b0403030e0706050a0c03021e011b081527090601060f0c021c 66
    0x19003243c0003d5610f00681c6810a6040b00118002c00040f94103984083c840313900a42c0d40d11040319812481c12a0748a41d4003102300e10b880202c14140300070b02d441d21840c2c8071000310b803c54000400c070700c3c8600c0200510304d00b0f554050042140f16040f05101081c0a00700790300d08040751203441c034014040c242c0001d88600052040007281c142d01000c150192030b950359100000c2191505014511503401040030902c03211461400f145d0845032003002a1510b280f0105003148411941e0180a080d03008184034200141d900344004c2d4403a901c100c1c5000c0c0d86043c1414010203c0d05d5903101d0801c241e01001040c0b12854200e4152042114107180020702160185812424204490b081400d0b5191841b44004041e0041d0404403610080c0030078180c0d003c0010740100c80841c07068940d94400518202007048500b0a40d8042000d0544040d00707440d41007507880d800031030607802c6800700703d284c1004e0010310119074801c501e900741036003618205c501070240d03400254408005240c004d0002c10001181c0c4200301d4034 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 807153138 1250 807151888 807151897
    0x602060f0702010212011503140f0609130519210206011509050d050d08060d030801050f0d0b0f090705030d02060c1e0d05270a110f030a14190305030a05060105 70
    0x110340c2d0785001c07541c0d03c030f07503d02c1c8070240341e0490b00200e4227240246030700c036080e4144640b09041c1e42e15200904e4641806016034004060320100008000d072004401146080004140c0c1c40056201d08880b4407282c20700005d145880640340115825000340003041326400101b01d8151002d0005034601d00b0240390303003901c00d101aa4030064000d5001000c800900c103000c00c800c000d881c0107442d01d066a64914040080c00c05c1401402004192204018840c0d03090200a00110b294007400818401700b88e504d80c1a0944401c03a000702c0000403400070403509400c18031250008080c260b008096203220f00b50085e455003402440f071810340b0808116a00107841c40100c1c44144c89414001c103685109004261024050455101d11203480030b04030094560503800c0f8070b030180c640361000b038024400380750303101c0003405413142100380d01418408001c001c3c0d41e0103206032041148502d075901c105000080340c0718209280c810301d250f12480d50010041c042600602101c1d486102c40400081c5903550800581e07942c0034 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 807154388 1250 807153138 807153157
    0xc0c0201120b181e01060519020309130906060602061b0327030d0e061e042f150c1e0a05030f0405030c04290a09050a1b02070602060f07020102 63
    0xd0600c800d5203c60001c03110900034074003440c1c52010f01e02000c0c07405088071000e104020016000b00044428524001300b5840300e1006841501d24024480c40000c0c6420341e0315038950307402a0b40740d0514041107058401d65000301042d001030641d51501c1c0c0440e00a00d0380c032841e25603c038900000014442e00642c408590328540c158601c0b01d0340c990300302420759281c126550700c201c81454031041d1202840000341941c441e5000000c2c0005844500008800d80034010344103c5813450a40c820003100440b078241c0c1c17400025104080d100107020201004511030b21080100f82c011810800c20310803d20100d528003c1f110380300301c816038a2046110b0146070100c040009040d900020540405a44440b40100116032044084401e44000041000b003111601507910881161f030a5020101641603d142e4501b00c00c020007030102141d44820085c10340380222103004580e43e5803035540144c0465200b0b48410000f031403000b802c2e0f81e4106480a136803068003030007c000510800740040c4400c4e00c01d4044a05442 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 807155638 1250 807154388 807154399
    0x3072c0c0c0d0c15110903010501060f1211031303021e030304060b0f0123071401050a060b180409080d02070c05030706030908030a0911060408030409050a0c0c0201120b 74
    0x20340108010000d0300421101d40703580c02041091031210b889200c2060320203800c0b0040c0c40e070070002c0458103001000104861141d00348184002520344e9001c0c482d05000f85500d4540071035048039040001c01d0003d0003010244c0041c80c0c400ca500c8607880c5c0c80b003030781c1e4440005030610f1025240e0b400c00b03920b42a6400b100310354100d2082d80078181080d000c00a180118031888051060003101e404000c1039003076a42c01c5034009101c1c001010b40310380c07800d41c0200e11100380d0034402d482c0a140e612007540d51000502000b0603070791107905101074111075105910040110028160801b05a0600d5500c03e24189503c0740c841c9440d850200c4c180480c61049807020b80c2100e40c115691151490030b00e104020a228451003801080390028000f40079004d580201a4070005080c6141c1d03400340c01c90010900c05800b907a0b0b21001c00c1c000b1f146612140e00074000340c01c0890085031103a103060304120036584000c0240c08007604250030080025082080c2840c04c9a09080429020049103031132030081400095090703008 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 807156888 1250 807155638 807155641
    0xb0f0a14040f03061104051003091e0c08100207020d0b071b1506060f05090409050f0a05060916030c030303091109010f050102060901061a030c13090b031b03072c 71
    0x20700d04200d81040780d204d4141800108803030007a48150780150310030075402807020941403030201e00c40e034051580c06100f4011041c0b00303500c11121841003e04654210b9005049240501c0b10401c01c0011400c4422003040a5140081d10ba020031050290707520010490510440800e000c9170081d1406100440f000588811004032401e0264000401c000c03480b140524100c0c001c10454400c4105e04040b46160311454684610f003824000104a50721080c1d61a0242c40e54070000c00b207003440103015140c0517000800050038404411802c00c132047e0101c80c1508050714003040021200405101102c1d018107000070b11003254204002c05125600740c0310b41c00180c1400100d800c2d010781002c501912000c0c1d01704e035503c0c0e56a514050881f0340c1c2c0c1c0501c484049803205441441d419039030055600980704480241030010f07414900380c0d100f02c1504070301481c94941403114018102044409056500c2d080424280500303e004241c482c1d4041c080e40c001191aa02060203400c204001015400c0104542c0b00c2c05 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 807158138 1250 807156888 807156899
    0x30518030a05032a19091419030b090601150c030c150b040f020301090b1c0803070210090c05090a0c09060810171b060a0e10030603050109030f14040b0f0a1404 70
    0x200d503c00b203d15004554405594680a84600030b000147c550f103040710b290001405041260090301560001c5c0c40c0307021254081300068860350084e0003101c0580040101754104001225240a8800c041c002c11400b14170700e00101e0360048407030014903041030114488054204000c80039218024078a41c0041c24080392000d00d0b4031a500550480d9805102002002c1c00c241c1007040c0461103640c807090240c0100d0080c004914041c000b160860442c1c01140c2c4d00340c42000d04003040d80c01d401d00a40d14150781c2101040b0509001d851703035900001007101049031038001e81010703001c0c6000d030140b0400c102c0802c0c0003071250240004030780090300c1c0300ca0401d50914215a01140d890022083c029140180c80c951180710f810400140d8102440c1d9845000344010f40b8070501401c1c04030b010110003016204d00f00000030440a12a940507580207075211a641c81d018a0050100740886003da4901203041104100fa15880e405a50621007040010343c0c0c4e514110800b00c0345115035644d032880c22040040e0005030b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 807159388 1250 807158138 807158221
    0x6031b0603060a0e6012030408010f020c06130201110114100902091e01030b09131202030405181305031c0c050a05090d051005090d030518030a0503 65
    0x80c640c80c01750054405070002c0f2003000c00f60795550300034814400c4200301102d440b02c0940b40394030010f4408640c24a1000000000d0200f42605c0703100c01041d0800102408140028001c40184800c80d14041d442c011012007442d80d02c0200138941620300d200c0562400440e0300c9508586400c25a00e4005c0c820020843c040c0020100f0a44041451390f50100700020490098002d990000c5c1d80180300c1414010014407060200803410002810190b8a072208440ca955003844203010b0b1020010811060301180307020904205c00242034020b66000740000c10041e91000c4105a0300310141d40c01900a441d220440300d08401c2d40c480003020743c000411740036441c1107141e4040b0f41400c030004041c8120381c000f4000351203a124000d40880041c404001c04501404c04110720119184190103d401940145120301d00b1141d003519030f9032968005540114806506020780c6801290040703079040c004106050340c507074a00c60f01a5160900102000082c00c44201913850400001b4041c944903c85882e207440c01e8 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 807160638 1250 807159388 807159421
    0x20306072d09031b0803070b0a05180c10020a060c11060c13060e2806030f02030c0a030b060c0601032303090f1e1903050606031b0603060a0e 62
    0x5411000c25031240300041c0a080703014112010a03101d035211603045403078509094819202c03c01e01c1c1e1011050025544100704020b00c110b40c010b0780400a075003401d102820599030090003510b402e400352030181865060100341e002da1071a045031030190684080b04242c0c18150080b001500441c035240358070100d541c11001e500c0c0e035184007005442d195070b81c0c810080e0050150703144441d0341403580d060600180d801030030800d8500d08000c1150b4807002800c00d541c2400c04000031124482c00903c0000c212880c2c25014000700844101815800d600e08018100c0da603020385600c140806072510015030060f210039080300d885c2e41d00c440603581d40d5a101d0406c000740a50b040302c1e82a0300c10071304d00c918900003808011360340d44201c0100142c900c41404010072509010000b0340701c1035041c1d001d0405803566a0380784203d11640490840300800c0d440e509000d82452401010b6a00036001082d128a51403403008070940031060441d001c6840e07407550700100d14003032000e410000c1c17100080b0b010700461040444114 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 807161888 1250 807160638 807160667
    0x509100e030702180705090d08070b1e06040c051602180703060305060f040201020c13061d04021003110307180e0103060e07050f13050a0b2e0f08060f0d02030607 71
    0xb00c48132000450300b1034005508603088030005030706010000c4280f90085c06840424042d80480d07080c0009070b2200c00701c2210588124080c01119165044c006001e03005d502e40c0098105c60070007248140c440094210700c5008007150b0020900030034042199110282040000c1c120a4158003510b40070a024004100304d010540b014442c2800040d00c039000604201d11599040e4013900030302e80d04005000d03800e0402904052565210074010a41c00e10142801c2043d448044003903140341450300501051180b10b141d0354080500b448000707030104858100f00c079081070084c40c2610389400c0719004034036490381c503410040408c00424000000e0044a4100308810b802001c01e0301d9125989208100070321100d0102150030002c82c81040060900303507800780b41c0c420710519000c02e80310241000a1124105051480c0000c1001c08500c05d40989038800c0004200c95400d002c1d035400d4543c440500701d694001c100c14032a00c0202602002e5848880d42210340c00d501800710340081c240380602502d03040c00400030 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 807163138 1250 807161888 807161899
    0xb070c0806100b0405060c150721050c03160201380907020c010309080c0105010611160b03060d1b0b2502280f0b04060f08060a090509100e030702 64
    0xc641c2803142c4002e00821034004000d402e140c10300d00001d00c10542c2003042d60800f140030741074224028000c0315404611480703950350b525144100b0544500841d2220706400b5031040d1610040140e1285040100ca4004c16800b50f100340c00c10b40c1e440100d02420841c0200100f01009000e4000750b150304400503074640c4501300c1c0c02503c46400500f4030040700c40465103000181c0c0003256101d031650107a80030b4a48039028901180c504580d0b1b0740d005080d243c00b07a200f613001a44590080a4031201440103101c5030150b030044016862420715504414040079003101e200e00000d11900e4108807080d1515a04080c3c5800d00300051075585900c19080e0f04851b510300d00c880c4507030b0a264400740390200c2160a0039030007480001c01c1080e03159969003040c000d1030b007060700d40d100400114504c221800300314010b10007510425030761801c040000b80283d00c03000c9180280920780080c04081da854691440560300d0fa80e0001407240c1c0e885a6051505404168182c1355030320f803002d10200c4c1c0078044020040366009a85 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 807164388 1250 807163138 807163141
    0x20c04060501051314190f14010906140f040815041118010905150d0b070323160201020d1d070b130e07170901090314032703040b070c0806 61
    0x42d2a01d1140b2654002074502c2d0318028405400e50304517004100300050b09020704042c018031102d0a1030031580104200880c210307800c00c0109042c2003a140141300030701e02000c14500c2c0001c06482108410b803070100d0440c002c10b03aa4504042882030342e0050003201d040b15182c01065280c8406840207a4081d1078500d51451510f9560070300303540031010b1742d60806944005a1902a03020000c0c080a05020400c1d080245508a0ba0b61102c140d0008103004422a00306424510380140c2150400303001868200501440c824015010625007680000b040c64619060381c0c00c01c00c1240284140041c45040e24035108420a406980018038042c280310403003202c1a46440301c540b46118040c6031003540403503038200000d215000f540d2151b16044041801c1c030890130498072100305060340701200ca464941c0c1d550f045101c14180d01140a41819590104e064518103040074480b00035112503031158440318100420500040381082154010300c0041103840d100e0340f984c40d00da1103100c22449000000c0c403030f00c070 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 807165638 1250 807164388 807164399
    0x8041412030415080901020702030708070f0f0302210f1c12020408030703050f070c090203090c1005030a0b030a0b04030201020307020d02030f0a030c0c0213150603020c0601120f080a020c0406 84
    0x2154103070303510225541001d10030020f044460000c014602000c81d5002e000f0100144c84c00c1006c080a02455005820540d04004605c5016103040d40031400280100408201580b40c0040742003900e01c02d80480c0a081e200d500300e0a00d8619985003102c0c00344500f8003408001c0800b46249144103282e69201000e40442040c20410384c0507500410359140c1080140c6400680903000500c210703140d15041c1810220513840c0c10b10031480c16480078843c03640000030030440480902000e40c1e03146040b1120308800c001d400c00140580801014a0042540c4000c0d079015a81c0130040101c03170980c004101e0300c01c0c3c6801c9c0340003400317034100f56281c00c0944110007005c41010300100036108c44100b002d5119003000b200800881c0607005040e62007042c848908050070140e120034500c3c00a4501100011420300d0b11000c3d800f0010341c0300da0018040501c10302405800200114000b41190011441c59480100b0340c1001c050001e10701c10020001f0000043c11109583c001c101c1a040405c120b07000c0041c1950b0340f = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 807166888 1250 807165638 807165643
    0x1021b0115060e0a0905010603053411160b0901021e0607030c0e040509071404020a05040b0f1b061614490501050409020d061808041412 60
    0x5400780301c004407000e109001c4a031180403c1c0541e1400204a04803440d6540111011038400381c20030800640c503103040040405135809848103005210b400081c1034800764010790214849016450100000a601c0b02d540980c104030005d0104164035142c03068030f40e00c1403920340795800246454094012042400101b22002c400414683e03080b0015000d5a555036404900a0180c0c2606109104811440a40f55140c134400c1c01d1142020000038807000e400c0611001807540342426240c0325500402541c1c4600341d10100340c41c100c900060900740c0b0b035003880d803c07440306008881012100182c00c0c021140d030300b1400a03085006041500c035128082e10b800008550810003a0410280c2da0000c1110081c10000c07007414015a04160600e025034110a20701414031841264540d03038a1181c040c1d01c40448507607841018010300c0115001c010840c2c0e00d40c0814000c154408002d41244e546640c05403048160809112040d58440c0c56241c2e165200c2c500c021000e50150459802803200b124082401c4100 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 807168138 1250 807166888 807166901
    0x100b04050907050916020102070f030c05060a050c0d0b120604030c06050a0204260106080f10051303020a020d1a010905040b090d0e0f0a030203010906060510051312020f090901021b01 80
    0x7400520190fa0307882c0c051000707086449841006c540d820005400400c007180400300300c00b807107070b9228500044107041191406c3c2c801b8007210401482c1005200345140306c4000c5039807419140d140841c890081500044000c85030403080d0381c250290004000415502c402125034042c410902041592101d01d043c00c202e00980c0600c0d9a040c001540f030134240b00b100150015845030160001ca801c2d52035200705400c0c4800501075052a0f84510700c1005802910b0107031f50f5100f8000e80c140c80c40d410359914025580d06030f08001a0040c40c2882c00c500074002c06140032840d001d5442685801d55270348604800090004070790640f200340000011034100b44e40415070030440280c43c2e41d041d02c1c4044032420030400c80d00d04101c0b1940608042400401030700c080c0100c4000ba0b00542c00001d000c0d26141c1405885040091003a08000c0d04110305410126015002415581082c05011225801c0e2022078511848242c1850740803100300204900348505400a208240c8407401c01360b0841d4000800714241c3c1c00 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 807169388 1250 807168138 807168149
    0x2031002030411040216051e010b0d02034603110a0b0c031801141006050f0a0e04390c080706050603011103090708151e18100b04050907 60
    0x220f803400701c095460140c000e8010022040c02281028019a4070140b40c00358183c100d03082c00d151101340744601c010030f1160a0001c41c080e1008072031030b16550b00007038a4021181005030025501d44040442e1541c109a50104000244410000301c80700050700c044074040d004200c00084c0d0210f440e101a100204250401c29404401d805868599070201c032072580008025144000f80c8410b25400c401e82401148180c00507400840d12a0074513004030201c01d0045d400040c2440b004012400c540c00d505d1046034501c182524002c40c0040d46c0e180010042c2070030080b80d01c5825010821101605115480c0f010381c04010441c0d00c08284010304103403094454058040c1950340188900e10114000da00701c564400c46c01000003c01807000a8031030f103150001d0f940c202159014060a00900c0801c10000345c0801051304410301518100c00411200f94100a640c0c160107205004180715107180541c07030081c0c20440090740d13000e0310980c440e2002052141c1445100310b0a000128903c0100414028280c50 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 807170638 1250 807169388 807169403
    0x209071b14100c0309020f03060601080f0a09210909111b03130b0406170630030307031a04090f030f0e060d0c02060f0708070f090305010e0604020310020304 69
    0x252035444106944288000c45021030152800c01146010386100e54122666036444c001000c9407640103000110103c1c40e4968082d038000030910055a8109013590b0380215000c69910080d80e80c0000d140140c0800400107000400301f07095000700005100407a0380691b040e42e5002141c070398641060703056405ca02c066800a42c81000155020303913a011000c010f0902d690b0487e41707050111801e03880c00001c07950040080744000309090109580c4441d800c9842c16018040c00d0740e0b810080001031101b507100340e180c0d0307003403040350071150708064402c0c01c100e070421101b01a06c0c0c4038030744a2005805011100c1b800810a02900c0784000540303458860340c0490303034002c1128503c0c02040d0381c06481c0743e10041030000c1800b81040d40884903548a00041522078039284000c545030b12600c0740603203000c4003d80107440101d09201001700250b44140c200c0d500598a2401c58004009840f069130314800c9500060800d500f803034040e0103007000c0024800c4c0500d00c240c044a100b8118807004070201d00007a40c0081c40705 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 807171888 1250 807170638 807170687
    0x3140c0412030e09040804061106220204500115120c030c08010b091f03020904060306090302060105010c110906040b100806092a030a0204080a050307020907 69
    0x241c0035603080e100c450b8483c0c10080f00042d002d00000d03524240071101103c20480000c0c00f40041e6a221543c8510000040014440c030709128204000701075001c008021010700c2b403d80c0a0941d6200c1d00211100d0281080c1d41c02c0100308100d00c1c020300c400e8011b0300b0341e402140501035507120384403036111040e24040305200601c907402d2412064600d01083c0700401044030010501c2d641c4901c40c4140804500a80c41c002101e50350050041c0c0303810016400b03500c04040c18046c400254032844410842c0c0030b590b43d0b081409090a079000d40c0240070349545180c106150110100030040c9036880044014020340840b8001d0b0303a214011540319100f141d006003060781140c000b00c040e04044d45826000840104049482c09000d40410b9540c080c150400c000611035805000442c181081d8450308600c0d006003099601115524009103500c0d58003890301213007400130004580c07585503410348020300104400c2d1000400542404c0d41d40741c000328001d83c420401c2e6000b00d51404e009402d661090502c00c0c3c16040b81c0c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 807173138 1250 807171888 807171899
    0x80d050406020c100327060b010c021311040b0708030604060b1c0504170c100b0418020f0414040b010312020706081f030501060602100b060705191a07050a03140c04 72
    0x680d038034203804e84203154507018904900c1d020681290f0f440003000244050401c2e4604102095850a000c043e041c07080c46130920700543c550303031624000303504441c90100c2c0740040441548400e109a0344024001c2501058180802c41064010343c0551800c840c24058240c840700011500d21440b0581c46503000b08800030200181181c01060780f0901908903032004030096106996641e0000310701055a4002c3c9940d0082e0301031502c14907404074000e80c0c0c10098400c0c940020803e00f0024203020340300362007030a0482d585581d1500030000101c80c911260740e140c00c06140550030200280811104035643e249041c450710300c0000c040003100c0031691046029102c01c89241d181080300d104248016071031a0002c408910f090081c04000e18059006018a41d42c01d081c00e8222001e1810706c611506003000446d020500c00900503080d070028140382c2000314134901e0022081500c032201d0143c0d014103002049582c0e50010058181c02e9072540701880006000712035032502440440388651990000d0009002 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 807174388 1250 807173138 807173149
    0x607020d030c0602070305041e0303052a0706050a0210020f040b070602190207140114090919050a140117070e0a0209120601031703090307020f0a05090f01080d050406020c 75
    0x4416000b401c212034880440e0322503034140d90000c40150080741e40040d00700090301c600d00c24640b011030200c000400e040e00f5a1b40c0100544070b03201c81d800c00d08a9401c1005101c040d20f520785606c07050040c045801c1c55517100030290858100c42c2165000d03000310000c5c6103451445000700c030400f240b0341a045103060709080b211111508807010942e03200f942405110741c4160309285038006480207030018500360f450301022403001e84040c22000e04100890b40d920502d11010000e070b17160320301d08440300201a0740c1c1c400d64114100701900360740c03035850600e03041c010300c008150b1181c200c560174144e40041c10382c0c860310010422082c0926064441d840342c181000681d154248190b085903a920f0b026244c20300120020312800d442d4100142245c11000c010003c0001c03551800c404034001509150035840d1988503a6168010010080e004900720540c10929546030180785001e4500203101820b6402c02203844a1486801d016050f103070321642011005842c040c60540307085500e91741c010b044803441c010034081c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 807175638 1250 807174388 807174409
    0xd050117030408031606110c0106030203010606020a08030a05180a06240501020316020a0f14030d23070302070f060315050316090f06050d0807050610030f02011115270606060702 78
    0x110f00b9550303007903001c1625203254014210b14048ca000483c1250030360040500b15401548290150361201400783d00051056040d698000070f0b4000008041d51120345056044901b40d1710700142d0301403c901041088055070001d81841e0081018000708680026014200201c4c0d000d81400740e4005d00c5190003000c2096160a1000d20251682d03800301e644050b0192030341090307007220000c901a60074402c420704017041003091000c4a4503080c2d0120046000d20f401d03050389000c00e00114580010b465041c14000c00105004203480340344880410b070b89c1e410003030041868079440c1d60891013820740000c142c540010000c070149546005c1150032031410031024014070504c1c4d4003001c9591254400215940c4290b0000f00150080a50955070801c600d02039007025802050805102c100d0882440031894403002006480c1c0e0a08282d44641a4840c10601c0d0a002d01001c10144283c04100031801207001020f050045a1350f842034070300d16109211030f4540300101c80c030a4200c1414460040546000307503210 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 807176888 1250 807175638 807175643
    0xf010614090a0308131a03132006030a050403170c160f0618170a02030d020a0c0f0302160b03090c060a1826030c100e0f030d0501170304080316 63
    0x10051150f030396031411419001144003810718441a070b0304100d4410002d14040000030006925860361603c1c1090040c151142d040c06441903101d012480d0740d802003114100404007000380075a07203e10301641d8410203404225004c40c00900011a2031315204102910b050003140a802e502e42015111598229118502c1d003080c2e45a0072903003900c0e40401e6461044a07840c50410204581c0300190782003040403612030071510948000c00700155a9103540c0403003991118903008101594030103002208460600c905180544040307101c0061608040d000a082c000301d8105d9151011a96600c1d0f42085803070104440034200b035040042001c0003481c20400400c161503081c10141e60303404603203071308008d503011981001603510982e000039612140021034800b0b40c050782030000c2d8640b8040d030034415201c0c5c1a00010003100c40c2c881141001c500001d01400754640030390b900712502c07243c8015240700605001e20500002540100310f498080001004441c00c1d11040c0c00258903003444044001040c0d04c01310340c113 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 807178138 1250 807176888 807176899
    0x20f010f0c0c03080301090b0d0b150a170717011a10022103192906040512010f1b050f0f16110f01080709090b0d0210090e0f01061409 59
    0x3054009460002030b00003a5024a880030740b41d43c1803681800031514214412480341010441d1200007516240304c032944408280d041c82c60031402000800c00300c01d095003210302d10f0003940c0500204100e0004228003150854141200a14a0b19444038201c507240d40c0011a9100da4000d20b072103500b0022040f5004a015204561640400814a2030038000000381111060400824085030800c444507045000d00403c50030807040c00a15054650f11001c000c01440c08003036000d500200395208015039008010181850255a890408c030500a103261203400c03842c945440182e4605101c00c45003c0070311078203909d03024a020409441000785410095860402c81810441c00c0740080c5100c0d24000d2a5201d48070504502c081607082141184aa805040c10411001c0401450b1b50707001d28900100d401c2c404001800c44070000104000c0000884041e400c814140c803c0c00069a00c0804441122000c406030030498503400c802d0f5001035001e104000010f280102c01001c1c0780380b090020020f030f4000400703 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 807179388 1250 807178138 807178157
    0x6040509070902210106020d0807080c040501030504060603060e03070c1a1b01091e0b0906071b050c030303070c0c061106070e030a0c0306021b06060a06030e10060f030c06020604020f010f 82
    0x404c0d5140341003d801c10001a00b00040d421705c06500310324001e8000945080401e81860022072499041c0180c0c8940b504264503107000c1402c1c003800364000f2000e0340e0045801d01c80d0b101c070b941260f9501d9104c2901240e0005e0082c03400503020001206d940541400c800030186480c0710074004c008034030310f20600c01059540c2c414900002610b9480066031040502e40100b0000410f414032100d4000b00030281981a00704108000c40d880e40374041c580016818403885907000240d0411364500b0f040091001e0700f6200c004184119190070000800c803007485031241107a001d07150380d41240c1c0702c80c000101001c594088400b01d95505d01500703068407200e0700a03040314410001c90301d5800400455034010b0f42c0160703000803c06024a00030101070b04e84d00710380300200242e091000204a4800091264100b05a40d80041d8100c0003800d00c440004030358400e000344000707074a4040c800c12500d564401115440b104010000c0c2650022030344511070b503001040017003000101700041d078101400c3e07180502044044030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 807180638 1250 807179388 807179437
    0x30605130c0917060105041109010207060807020307050618120705030f09150d0b03160509040803100b030705040501030b09011d04030e060c1608060108060705250f0b06040509070902 80
    0x399a2203c43c11001002c0350f5140c0414042201c0a15110135035800e0100450305c100c0c0d030000765103811a4141c6c40c000805a031000d000703e046000304403006086005800074888071044030820803045098560a450001c000785041c00002c0c419a90002c0c0160400c0c010408a201542c01a000c2072174068916401e00604035074028040c0e120007a0340c0c0a0665075452400c0e1801c042152419000f21440d03580ca51500b0080000d082c042c0c01840108a0440000000c2d408031500442a0007000c0300b0560396101c0c144800058403e8009006860010745414040d00c00e902d800e85089049580180e00000300301120480c03541007000040055051180300002000103403919401400d07403604544c05081c030640111030124540d9629070111420358070540062203110004101c0c103410244500b01140e680c0c1642483c101c028042002e50310f20030051030000c40c1440400030790a50200d110f000042c0c01071707580c0410442150000d036000d4540d644110014028414694020011248440c0600c481c8a40c80c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 807181888 1250 807180638 807180659
    0xd110304051002030307030b10172a03091c0503041506030503040909061d0c060c0c1f0f030603110d06020f040f081902030616050d0c110c01030605130c09 68
    0x10b080020059000208000c0540c0e814030070b1021a0030204c4441c1104142120f00038007a000c880d5103c44002e810b140414100b03c99422410391a401c10041d11042d0700000c00b43da0a603410842d03c001d40750240801c0015540022407844942085684925044d03441d680c8a400c103071140c0c48130441c501a1381d071a0201c0403d408202800c0107000c03034075001c00c0241c404c0c5000ea050b01c46503000848030418020140b540401e020801e04502d030341c1540c9860b200d09071500c5403072412411201085c1c01a41c46044035480703011034052b00144034510388134202d401d040d41000314116026440082c18021156440422030303c1d054403407125007402108050704000360b120038440e05a000307911006c00b03210710780b404003c014010700c02903580b00001041e0f004011036540109848600013071000d101c0c003600521011303c490090050310301440801204100709020441c01406200c0301c0454980144981101030280b0340c071902407441540d2000e040e03500302404504880e8041e105810229003400460340703012032000082c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 807183138 1250 807181888 807181909
    0x1206080c01090501020f0316050a0b0a0f141003060c05041a090a0518280507020a0c0b16061107020d06050403080601031a0907050906040f0e010b03090d11030405 71
    0x1410180c01000a220005440115903074045815904070610300c0007480c0b000b00aa07108900342c81114082100540740c002c0c1001c41800b0300500b143c6071030040c08500c5d00e96a102c0c0605c40f04608081101003100000c0c100101c0d422129082d0400302c14405100040c050f4001a071250b0240c1407107401c0c2510784071188010701c01c03d00b0800e0804c4010a042c000c0340f8050811800918060b120b000d401c401c0540072810101004105104c40c210130300c048000c06000034280d80d80c001d000c0c1000c10103030804890003526143c0c419001d5820318046500491580c070003800300d40c04100200680886428603035900400342014140440d80400c0503c200809622811048155288038410014240c507162030003074040207001d08005e04043c40d020100310411000701c40c0c42c82e4100c046515012a99502c0803ca40510403e0641a0008004100081e5044000c81030805803949100e07920f04aa0b29003541c502c0c50b01003219403008580c800340d0140301c41030081004001d41031003101030340d14107600c1d403000c1003100b0b08 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 807184388 1250 807183138 807183149
    0x2d1501020f01111c05010b0304060b03030405060f030a1a1305040218100e100515031b0d0b04060b0304031b0c050301020f03010513110d0c05041203020304030201120c021b011206 78
    0x20002240c4c08074943c15098502481c0203007074100300035410701400802d18040104001c081d181c1d03441c1586010364082080d18024040142880da070b07020000080f504075081502c1141c1c00320305028640e804001980d00440155078040c212841c03100544441a01504000d882030744c00c01090295205900114040c981c0728020081440004a207032071035407010004d0050000712004030965040c41580da9110382e84020003081c160464032034543c0c054808802004008010200358001850854200305402424001340100c40404c001980c40501d00310a10040b20000c0c00143c225520700d12307860146400011440c0240b0b43c030701c0c20f03503110030100303007244d010032800a4601c0c4040f004100e1031074148140c0452074003444050017504000020104240070b00c952048000352500d8440d00403501c0b803004e0350024860300c0403c1c1d60702203003810040d4607940140000da0005481d85e0500340c215020780200c50700c0012075401002003150043e23101d4262101114100e040041d4205150383d0000c560048102610 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 807185638 1250 807184388 807184421
    0x6061905060d02031f08151f030507050a0f03020a0902280c060b0f100e030a020a0905010617040c0b0304080c06040308010810150e0603070e040b2d1501020f01 70
    0x402c09980036203005040c1881314800c1c0341704014440f902010905800b00318440403140030326100c01804099107070007508042c03ca1140d00c0000814068006500022103805540102c003881d22001c1002200c2d0182c0000b0b900203100040c20000c0e12203e9008100d90720100b00c50030000d0001021107550f144004904c5030024548040d6a8288040d034824140100c00c00c40700d40c11800c0e620004139100034501e51131034043c0044902507640940b003d1140311000340c0d0040580b00555250041c038030040c4000e01604000030f0507408933500400e2400c1500380181e4204044140e864a00480348055510040080381c02c00c03001c0c409050144410019a0b000b540b11fa12204c0c07440d8102040d4500d019088001c444940c0e080210003040c1030554001d100650320011040909950703031b040802d2078a000790b40b1402c0c070703003200904010900c284441d40f140503040041c800303032004401c116403030843c43c810701492140c0c40f840400304607003040d141c034040c52100043c010f0300c0c080c50001e601c035801c46050245414820 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 807186888 1250 807185638 807185641
    0xa0605030f0a0603032c0a0e010f0b03090a08090a0306021c050604020f04120f14060a230c0703090503030c070608090727060e190c020d0206061905060d0203 69
    0x400d81800820b030701500800703040042c940b65440061501c4800d0940704400990b514500501d40b03c00035030003c0d4244040e100518170b40e611440da492070300091140f209505065040130420b16000004c42e401010a640113018942d0035840e80c0402d5445060f03d15400f0840e0000040001e06038000740002c500040030400c00d087d40041c2030010798200400552003640304001071100b0003105010b903030650300000e00034115082d0904e8549802d80001202401340d54886031307524070300c0000241003840303015160420302146089582008100750f42d01005c007221040d880000d00c0100b11170300903100c4507003e858628400b940c0c500119003168081c03025000150001c0b03006104485d080460f40b600841400000d020151a1012404420b442c0c0c02e11010700e40b04c10100d004801c403680e00104050003041c0760340002c070f084c4064003d6440003049415400c007030801c44c3d0304e00e002c0d00110b10948448034907006400c0640d034040401805841491241c400c921200001144549a40c3c1c045d02c02c140c0d004a00698a = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 807188138 1250 807186888 807186901
    0x50409030306170703031d04061802130e040201050a08070e12071a0405090103021018080606130c020c0603270312011a04050d0c03061503060e0d0e0d05010b0a060503 73
    0x8030309080603203036140c2c4c0b2003542000001d5121a20900c3c0314009a0103102d003801003000940031b0309003580120f4400d654a81965003070400c56004100b2107d00c00000c0b1640341d078030b0030000f01c00e090849029010030000c2c8202c814140c02501c040b640161341d46000c014040d500e000050101d003e040c456102513103c032105010126402c0c05010890b1812505e06061503e4840092440441400024017400400120b203561070b004c5d2490001240400c1c00224a06849558031903a42604803a50342c41801d10284001600d282441900f0b0094001d03406031001103079800900032244d101921000d17003840f0040b0102070104c800d0642880810200b0059503407217400c5040781d400e102040c0c1088002082640c0c503811042d2520040b903080b50405c2c1d0309184e2040c0203041600088900ea0300181c1145c9c100300b24119000640c0350041c0c26640b20325030070030100004041d00c0b5a140382d20400d103008210040195030161421700e4404040d00c2c460000420003906840108440718900d502060118070b010040c1300e903 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 807189388 1250 807188138 807188159
    0x7080d0b1003090b010909080f09180a0c0e010f1b110301020f030a0e280f020405161e0c030507021216030c0b16020405040f05061503161a0d0204050409030306 70
    0x41c5150003087c4031964441e25001050f100740b01f00c0c00143c0704005a400718a031200840f01c04107a6002200d100c140c58000d20440142154281020008445402080c411342c050008100600c16a94610190100319400031421890442c41900e08000d0080100915039090009010100540050617107905101003804255144034607621072540007c041d046000e0b010f5171401003c42500f08020440b6134060a000c1d00d402c9c0200006900035003010100110211501c2c18022240150b90352000340200100406501a000b210b41400050300c2c0c0d2035034070100e41715401400800c3e0004151858100206080c01d150801803450440e82c01a4030b0f40820078404092402c00080c074111070802d240030702c041e1441185041c0410028402c943e03d4002c00e090080c450710030320415902030102c032828140410100315400b10f010b9554071038490000c5d03d880b03036564000b004080342d001140804d0340b107041c41d16200c0355800000700d880c800c960a110002c0e455a69005150440d400307514001100707410041c4555 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 807190638 1250 807189388 807189391
    0x503042003030a0c20090c0d090507060c0209070c020306130503090a0f18110412050a02030f0303010f1d0a051e13020a0801050f0a020a2f070609080307080d0b1003090b 74
    0x24880711941c84d0207217070b5180c0c059901d6000f503003020301c143d85860208086004084003c0c0251582c0309008020402641101c45c0c0c0701c07941c0c000c0313982e0b01c1e190f99400000c488905080300000c3d0141c01010108401c0c2d540320605100d4584240140d0f0f0404030080d01003950806c031503110306201894160100318a0700c1c484480d15148040280a01102400801d015441d124070320550b1f458000080255043c0b01081c000074580c164003c043e0340702240c40300622070303481d00b0a004080b42c00c680c005002521907201c072170321403c000400d2440c3c69550380380b83c081c00048c60002d00c0305819a400201e0340311103401c400b40103489030041c1a2000e0002c1d1584c0140140c01d0b501340c100c07074103070381c988010310400301c124a07821a40101401d07005a80d448140314202c40b14100828821074201c005000c4850403070f8aa054411001140401c40700a10341c0c0d00011a0039445512458509410402489010035500070062048200320b010105807482d029000c201490381c1d0052000c0080d81d1143e448040122018400307 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 807191888 1250 807190638 807190673
    0x150515130912020a0308070e0a0308190822060209040608120a02060a05090c0f040e0304080303010306142202030102070803010311041b17180a03050a03050a06060503042003030a0c 79
    0x201031301c030f0713003030b80c000e028140c0207082c0b441808016904003949544080c1620301440c1d100031017603215124000e02d03200d401c206e580b0010100e4084000248088100c0000441c200d000e500740c0351400b8015219030b03009500100c0c0c0315411a88400703004c51810303000c2000c0034184140144195451044400080c280500030701645045820702090100c00400001d040c88110422100c92005091040000303000f0b00c0b01034003050003404080b8001800000c08000307941201d0041c8c0d020b00841740c028055002003030040f01c04000380180030221025040301c0700001036803d48003500040c9030903500d440d901c0c5030341c000364412a406800306101307103018100f50041003810001c011680e844000f5504001d010f130149419000400340203400004d00c0348181c2410708805140300019609200258140205968007125103280441e0410020443c0d51010344203800c102c8003181d40309800c40d2035940c0c2e200802c0304018100040ba40c0c0300034030100f05039010300042100d4901c1e502e4460b0400c05e6440c15102540c14403008 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 807193138 1250 807191888 807191893
    0x50f0d08061305070332161b030e060d050403030b03061b07030e0414091614060f07050106060801080c03010501051507031808010609140415051513091202 68
    0x280030722a02c074101c805409003035480022030f45582c0c8070320480041c500c218010751a4103032134543c4082d5051071241060308402c0b9a0441510755141c07510411110590062500024522000d19803011102a84c14400354441c0c03405502c24000140040c6054004451220202d640c3d402072108160300740c4104c3c141d03038400390f001c0d103a10300c1d0903882140c124505101082c0d100d603000540358201480340001c100c80c490001e1042140c00c04e04440d190045130100c400003030364820f04c0500200341042181c1041100c01c0c2d401c2c0c030303c16002048144a0190400039070040101d60900103100010420b0280b000038007007541d614040c940c0f501d801c69262a58040016000341d2410b0010321080e16402c141c0c101030051b20703840907500c50241c40c049404d5182030000030341a881e035000200c0c061406400007001c80310010300030300400c00b5005243c0510748058600806104162460340c482e00d031142c021540c0481c3c0c50021744442407014001c0b4a039020030300d180c1618550b44040030010025009418401d02115100 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 807194244 1106 807193138 807193141
    0x70606090f0b0306012103050c06070210062c040c0509090c100e010507020d030203131806090501060518150a052a0304062703050f0d08 60
    0x7000e90440d04180b100031291400185081c181e840341c683c200e0002e101400789258694450000318103110041c0070001d440c480a1001034400c030a50f8001e0019040da841c2058201c81568105204108070800407865203546085285003243d603034074010003c0d4940703051521900140c1c3d803045074013404150401004090204041c140b0100945611140921030101034a07000120b10350305000840501c06a80980b07040f82030034581e90301070300607203182c03600885400c1c0254a03150800c04405903070ba40406150520351086800400c58024200555410040002d2040c841c51100c00703032074256003103500303215912070183c0300e0080010744546a458040c104058180e0b045807035042002c21000c5c000f03682c4800740310b50340700e984a162800b842c60a8100b60040e40c42c680d20008400480c1210070340f9a00301000c24002d81c024500031002080c0c07584000010b2842c0c92407013003a94080108030030 = true := by decide +kernel

theorem cover : BRFrame.Cov 807014388 807194244 := by
  have h0 := BRFrame.cov_init 807014388
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807014388 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 807014388 ≤ n) (h2 : n < 807194244) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
