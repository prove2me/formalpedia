-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5062
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:37:25.032981+00:00
-- url     : https://prove2.me/submissions/149fa735-7fc7-4445-b113-b8ae01169219

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 910251798 ≤ n < 910431654 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 910253048 1250 910251798 910251809
    0x15070509030f06180109111005040806191a010e13020702090a0506100207141c080a21110720090901060f061b140f01020c03090a050a1a0f04 62
    0xc46034070350b80c0d40304280d6a04003076980314441c0185840b032401040050041656030341e4040c0ca08000720498406000390750384008010302c1802002d100201d66882d042101d5407143d5428510200c44107240850201202e2000b942c100754401c501c81c0081407a45c01441d0310602c00030507240d11201c1c00b404840b01009002d0a40b00a52050414062000070600c1c4d41101c0d000b040c0490f4203045640c2c0c1c0207401c5e40d99a409125410390b81c4c8001e40802c8884c5071102503405420100480d0826541c01d0741c0d2029a1380c4e10000c208800305a01c804400e00c06c3d0032412001c8644051308208000085c101005844507000b00c0c00c1c01002025104144114220882c44225004801605030081c1e030410303044541c06441c0c00d01032003848400c900300004a030703071081002c00350410702c4030b041003055442a2a003e04940075010010340b40e21403d481000c0203e400d2005090800700302d0091500c1e81d00c04010001ba2203a1680054490303540c140c2c09004002c0a00b0070a039030b600c080580f40d60ba079252594151014092035102 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 910254298 1250 910253048 910253053
    0xd0903200d0f200a050d0309030c17040902030405030307080603070501055403061e060f0603070504030203150402010519090801060b09010210111605011b030c120903021507050903 79
    0xd100c0c0c0820005100018284030b04107440302d050346e541c002c504450f9150400350003d81c10f191400046800340e00082c00300000c001d40e03a45000c0d29400502c1c1030360320988049449900c00010401940e40c000c1d00c1d19001007089000d000700d0351500300001c0031030045804407040c0d14007002141061202003180c15000924400320741104c840703181340c00300030f0003207d071120300b611007481c020b0703011914011441e107200e070545103041c1d02c4501c0310107524108200010009508828018826041503031000003551040d42e2995800b59a5410b40c410b25003015007801103911507108031400c2c400181e07000400c0c3d0b008110340040f10100340000e240300720f41c1e603c015480400d1070351070302034049041c5014000800d081c000070303000c42d143c480e8110801e0085501d00308980c50080ea09005801140111003110038106005000100f00540c000c40c40d145210010084400403e5030343c0c04d41410b07940c01200d0060a200e03d1441000b804001c0c0d01e000c3e4076a8080b96211410083c02c02c0010612030245054601d5110003608 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 910255548 1250 910254298 910254347
    0x2606061e070c080703050f120f16020a030c0f091b11120f18100c030f1412090c031504022101090c061407080423060d0903200d0f 57
    0xf071180c0303a110902050300c060082e4910303d01030030000514481003002050b00d0038540b54004c030052003d81c1050b081040514080030501000d030350380304880070140d4081c60911650518245000d41ca45a0030b40c020032400b4142069000164021500c503820300c5100d040064407441204a601d05001e00301c055841a07143c08a880d020300c00b1003001600703a00c1940e40100c81800852000c02c100c428010a4070700018020300b000000007881384140003100c0322142400100009207104100c21500310b440c45184102c802c20400c4001981000071040c65082034002c1e00c1101240b40c4403560302c180090010780242d0340100901410345100c0d02c0031305100c11140080280144600d403c0d9445041441681c0000e00300c5001004e801045804441c08164002c8c3c0c0d240c0b80a16020402c402030f41c4990000000825507040c03040c3c1500d0302e00040010403868503000540001c130b40340203040f044880c491005a01c1a5014200e061800043c190500000324100740301048191103048422041d800f1403000d40042c601e2 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 910256798 1250 910255548 910255559
    0x7110310020a0206070306181d0a06020c0714180910181110050711040216080d0f060b18030c10020109170315120c030d2606061e070c 59
    0x40c040c10070551198282d40c0c480d05d5000c01241511114010380c800c181c400e034140780d50a004e56000c4504a400020a0440410024011810454007050036141c1d9600000e44110040081c4020300c007500d64445084204410700000c10060081a00184c1b41031741114081126804200210790511072003000c14400fa0b0391a0034400800b40c6041001ca4401c40c3d0003088a00e00e2404040303285880306a50307102c506080d80c5480314030310440d546c4541a0441d41c00c10840480c1d0040404065001c0e0181d00c40944d0760816007004e000b00c90303040c086018160f242507024403804051104540341c4a045c0a05078041300c469000090500d00718020a80d800a41b40100b084681c0d010340000691500560405000025010000000b4031044610391001003940315411442d00c3d050f9103000702c2c2a000030440f4031000c48030b0046403401154040c6d45011441105038826400070070441d101011081c0c228242e45800d2400205040c3e001d400e080103031b40364110a0f040307070a0340843c00b135030341280d08800da0744000c90b078a4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 910258048 1250 910256798 910256801
    0xf040303050c060a090503090d0309050d051e0102070309050105091804151119200a0b01171c0e0f180402030c10080106050901110f0d020d021b0607110310 68
    0xc400d5150603003e020b00098520307140b8450b40d800c0c01d400001440c41d00080d02c0412208050500080b000d02c1700c680e4012031652940d20a9164581c402e0b001450f1910a0320030642190004090074805a80104804070020b6030090201c0c00300ca000b0f00341a601c5280c0e660000b0030400b50100700c1e0b400b803030300790302004180500c9904103d01241d030b0400c1000218203142503880148600081c24480c0da00741e420440c13485202d420200014540d8448609400050662650600040c4002950100c15100050001c41981c2c10060780c2d0586280090a2050481080714201c3c4210101c4405003c505024044951600b0300b201204000007450480d03861540340c0d045044000503602a40284181110341c481030618104240c00b81011307072140d9503160728200c406c0303d080e880840c000c0d0401c850390440381c03101603081005000341d0318480050a11840800e4000303180c041d0011132103007154070841c0c0c4884048590900b90150350b105980c0150780f0051801d0444c1c070380809040390f58141c0301720303500c442003081e00d07 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 910259298 1250 910258048 910258057
    0x1f021b0106050f010914060d0b1002010e0705010f0f0f0e060d09120e0303042d0617091c050c0f070f09060b090f01030e01140c0706111614030f04030305 67
    0x1c590b0035103c480c070300f40110b601c0d52040c041d81c0025003401080300f203680780110207071034001d88090780469034440040228000c4d550070900c20000d40c0d100d22203411880700038440d01c00a410207103080c0c10b40896140f401010801e01407664414483d00030301403000d0038403449101d4818817002d0411a5540e40c1e85500d040207041d11207080d1240362580758508035140c42010350642c0c02c0d8005008604040c107254101890786404550070117004040342c080460800d0f41c0381d00d5401000c203030f10790413000740425a40a440700c800600810b00c41e041100ea0b0041211624a580700102151030030507141c00752020254501014034070410018861228001070681310310760f5420507580c010005008295807031070004102d00503290740d079070312071500050f684065100380d000c02c001059000001ca11242e80030b0060540c0001034815100e5640c2c0082d41d0010700c03900780a200904074558610924007110b512041c04250a1420010540320100404452a0b00c040042e05d82e8907011419440d919580c902d03000e4000e81c071 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 910260548 1250 910259298 910259309
    0x601030b0907200712034b0806091f0b07080a12020f0301120305070f03021b0108130305070503130e040c0608040506010b0d14180f0d021f021b0106 65
    0x943d411440c40f066008035014048501001c41083e020002e503409803861541c4000010341407400c3d80c0c0e10f10018180c8400056103c000e50804c0300d960700105189494409810004414001c4500c02e01c00142c4446106c00d920080088503543c0707500243d0b00c02c0d424a406075206002e4500d0220308501407040c4c52000300241001515602001011491f80005034051110031009003201440104803802541c00030044062091608034500039603592100316101442400b035006910071403100f050449001202100c20383c0074200204145010808400340c1800450000e00300b04003ca000380c2001810010313200c00e004039803400c3c00c03500d440700d8000003410400c603070a413140c0c00c034844002081801201c010340503e030401c02400c035a0b0f003400b007200d0030b503444000c04012095803400b400781c0c0b50124444032401580c04a00b20110109488241c0e4500203400b889400d094210700754000d60700e9000180b1440c0003076410244e113011504154440000e01402c0c0301c454842042c01c9094840365010f611400c25110b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 910261798 1250 910260548 910260587
    0xf010e060603061006140d0c090503070f0315091a0a091b0b030a200d020306040518060f2a0a02101802010c0c0819110d0b0c030601030b0907 62
    0x944100805980f8002074507140c00322410340308203025240c8225503492859468107085460000041c0800c02216034200020000400c55001444603180911080000304110400c101f038003429612154140001c07040556443da6452a40008202c1e00c108040468a100010441e051420609510280800160444441c152480201d40307003a255803c510984034103110032800d50792601071100090550300c40c0d645103180510524040d040d2048024400c54550020158803410418140015180302821948141030141c90302c030841d68001a003168011220882035006442e000c10600c02078007000c520341014203c52105000d200008001001c2e015080d60807505416001e0754060100c400c4044803099011081120402540c032a48602a003140500300280c60315555200a034034107a8030125503014400580c205900b801a007285200e4103010540c0c800b0303880b00071552401041c91000388198041c51011000c1882644250701900d8000e40181600d406070610580151003205990458101003 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 910263048 1250 910261798 910261801
    0x30106030c0f091808090405070905060d0c0e0418020108040312020a031b0806030618070e0f01050a08060c030703180209040305030901060f080715230a0809030a090509090f0f010e06 80
    0x88000950009401c5c0d00950801d051028601c2084050003010704648104400b00340041626a2940003c00c15207401c41e800050201041c4005001c0722010004944141c0c070302442c07500c09000a8410040e02542440c01e1207080d600d034a000c1c0c98040500301c119400038400304003045210b07095409559009016035088681242001084483e00000c0301d0160309a08554040340c2410300125224050a220300b00340c88a0741d0302c88410306044242260b40c0110000b44900411940c28108003081c085d0001c4e4000e0890791030500650191880040d0061003015661510000d8030820008020390040c0d008010040c0c0f0300b0b141c10020074030b800580c0c18510075440c5c0000000c9100c480d5800e50300329101c0d00d019040c3c480c07411140e1030034489115030840900000e904038290050180d66450406808142c405071102d0a0352001400e18130001c0c003980580d0700421a005145070030070b814500320303501128284280d42d66800b40c3e904080701400004418440d10248003001131040d04880b00300d0ba070200417942c2a = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 910264298 1250 910263048 910263071
    0x90c021c0203042105150c0919060906090e0105010c0f061e05060a141e1906030f02090306061302040504060e0405011b0804141e0114070f1d030106030c0f09 69
    0x380c081c88400141950310102030203011010a0038410f910504887c50b65007046015408201010100c00d004c00c0a0854030700c0030301c074042d040401d01000d0521460403007002400c081854052400601503035041c03006000002d4200206201c2c6100110ba001005000e00c022964451200e130002000a51a15041c10300150250402c0b110701c0c411070744080c6a101e01c0d04900c6003441004000d101e440e188440d240d01032000b0a80340c441c003044503d001e86001c440102c0c41c140000b8200d032030704030b1072183e401c0c010840c01c052941d00140c4139070820402c40e440d6110740c40c0c1e07404443c020301c580e41c421a003007820702c0b1000517010507900c0060b00c960b01580080c003085103950842201c07501844101d00108140d4400714003c510011101ea036034101002c11260740e004555090700b000e02204240c01816910b0307001da009400030061003580c0014240c02d081682604180d07010f0005031504100200f0702c80140c0300b9189039039007500600015500b1150140000b51240c14181c20981c0380d0198004060800843e00036 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 910265548 1250 910264298 910264349
    0x12030f021b01020d08191b0e0405070c1202070f06090810110304030518090c0d180b1b0919061d01121d0f0105070207050f0604090c021c020304 63
    0x18110741640900304524620006555161003d03040340810344410440700c000e00503c1c4280c40c03000728001d440b4006e4418848004003902d0481c440c0384d01030f90800b0140184c3c2500042004080c1d90310004d1340014100745c00b022890103c0940c032010700109040c90000748540c1000020050b1100201640c0204810105600507200c04985080100360b0400008021901c55005401d0404d09548025120301e268000503035440401c0c1c07082141c9060000f000342e01220f0501c2208100c42030100404c00110300c684840c100b8020003030000800c02e80f5064020b00817062038088846234a0014418007520784140c100c00450000d900864001c07900c0b410f600f1000544201c40301800b184165212440440414a5074001d080109042c044c0c100e641e1030310210401090103c50440d1420900014442c508400e0080c40c001640d4003050041180d0b18209016031100e104480c10341e1551880490b981c1a0384504a103003c80d58492400d039224003440103402c103940400180301b150003245500462000d050054035 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 910266798 1250 910265548 910265593
    0x30906290415052223010e0f0f090a02031f200702011d0409030c12030b1305060a03050a26090f0909070902040b0904050108011e1512030f02 62
    0x30100c60034040800c0b084c0b5002c1e03c0000c81d01411481d00c51042d0041d40400140c501d5041c85809003618980f40f41107940c0300014050044c0b0505020a41c0303428890500e00540d00f02030101c0c60f40c2100080003e000310800c200c8050718940c042d0031280c50182000c201c5800c4100100b804c1d20583c1000fa9906642ca2103c80808407210303192030030323480d02d8155401940d0308100c5880c51500c00044282d51440c1d5502d511641e094180a920350900f83d400b685060a000031044900401f40f526200716040c141c1c840d402254142880c800000407030745c59000c005a0400c0e810782c8010194494a202001005400000409405515011002c00ca503044c80740700d44900070800b1682e000007600060380314a00e0440a00ca400c07001c1b8200391040661180e40c1d0400366449600801d540311700000e135082c15814a0310410340108141c0c0c0081000c030407540444204201c1d000d000c104441e85581101c480d01301d2028504004000e20301c00d41d00d241100c0d1502070503d541020000001d4080e00b24251461b0746481030320b6 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 910268048 1250 910266798 910266821
    0x30c01080919020310060b0702101110090f170c07140d12030b120c011b1a070e04021b010e0604050616020a061a1003180303020a0309062904 62
    0x10031400c04a4081c81030b011440401c280da0501c00c11000540c5180035119240c084d04465080c159143c90368010310010180c0305403204d040000307024181103400c0c004030301d86c0010500c044000c280715000d81401604d1640c101d502030032210111a450f8001341240d00109041000081501c1c20b0590310080700c01e0109131682c03404c0d0000d540c0440d980c0059600003402001e41c1031401c4c000750a8900c2c802040f85400c02c441f5003812584404509050396800003c01440d4400400305080b161956588800e000036044421808640411000c00c0f0741c14000e14840d050b84c030002d00215100c118a500c480c40701c1801c20400046075182c00b249a034030840c0420040d1007150444000c1c51b5649039510070321380c0c6540400d003100441c010406071000040035401619030f5440400e146070f1200242d4010050380c80c1a4101c20011315243c0b0003606103148903080402c0310250103040050720703240d052100b60301810269600500715868000203000c00034158030940f00b544407480c4000b01045090060204807040f1070b924 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 910269298 1250 910268048 910268053
    0x110d0507020d0614010f0f08061b071403030f061206130b1815010305120a021b013b010203160618020604061707360b0a020c030c010809 60
    0x250142c105442600e144a10034200043c900d030f0b090030740244802e000e80000181d0700c0d141e1800c000300b2640d502d01d00c002c3d200f44405860701d4200b0741d070300d0b001521005001c4010304101040f6030045c044d6000c0350301c0c0340c80e0260054a40d64500101e80c2034181c0c00460308244034000742800100c19442c00a14107101300341d0000410b80c081452745801c1c000400051482a84456030140c103012028280508224404d41590608032541149001030606107070070012513030004107002856500350700041c5560091038480700f007400315036800012208810903040d0340e81003024804170503030720b4500700b11141c01a1a01505201c8980409001241c40703208400c03125019400300c481d4078000c56810740c400307460100341d03d006490b914220b07030200d00341d5080750f4408001304000040000700325030b200b1816940441f161a0010a651800f0a601081d958950250100b11000703414201c0303280001d41e24001400e140d101c1c560720b645510000030f655200c032800300c5010340148045100c1030b50040301c0090156114001 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 910270548 1250 910269298 910269307
    0xb030c1602040b060f0306041a010c0609030e1513090b06070b09010e0105070804051b0603011403070801020f0414041b0503040302030702060d0c020d020d050d18080a05030601110d05 80
    0x100011001001038182d0b4859942d07059464560f860900600b650042d24002c19220700e069810002110009002485605862070504071300f130381d01c07000c0ca0640360391002c00003813686410b0900702e038003200e00064142c00a071000d04250241ca502d001504011040d10513030b0341d8064a0380c10031002e50380d1141209403c60744c14001000000c0302603001581c051040f00000818000c0c1540702c1b401c7d5403051f80c41c84007150500b000e1105000080c4400743c00d081c01044030503c80034440c4042011031105100d110341d040d40403903684000d035405111200041030700c80b0003591034203105840351540b0392091003080741d14002001c0c1010241000d02030480003858035207003003210101d0b40c002a00c965100030011000c50204000c01d00050f5121000b0b8100c40000d100300060100900401a2624070661856000d650008255610503036100d01101c541452103c4042a070241e460112503031112400b4004014590100b83c00380356650001c041c500ca12001d90380c0ca03111103c1040c01e10f0b15011071130b40b090b0000e0340410 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 910271798 1250 910270548 910270567
    0xb090d09090c14030103030e030607030e0a0204020706090203070902210c0909090312100603141015020f0a051005011703040b0315090a0614010e01021c30060b030c 72
    0x3804202e0961450800003007151840000c40200c3c0d000740c100710082900c41d5422000740c142044016400103041c2010480c1c10000d02c0c00d25560b80d104000248225000a10082004240d41009800940c0501122282074403540b01c40041c0d000719640b01d8828117081800341c41d030709030300500c2801980c0100210785804000800d0144010f00113000301010b202c10800c0d0300c0040d0641c10b42611508070407078001540d6080c180c008060b90180080414002c0d041010700500e9801f44940c8021501e28007550300111160004c16801c01d4166104615940106d155080034800c0110380c0c440004082e00040040307070380b41d101581c184407032100c1c4800550302c180b00504c680c40d6542e000b10b0f0410740d40b03021340002240d014005101c10904464a0700966102e4004100700302441d41001e0140f8404d0805094603004400000e58908401c6200082120140d10043c481d50042c1d4001089005480e500004070240b400c1a902c280c0581d0322021b40780f841d00b01300140303848085040c2c0f40192038006580b45410f070080c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 910273048 1250 910271798 910271801
    0x2010b0f010509150c10060302010201050c070305120406180501050108240c0a05070c03050a030315120b0a0914150703090b06010e0a08010e010c080a021305011b0f080301030b090d0909 81
    0x8080d14904c0b208108407842d900a002c1080369480c121581c8042551415440020f083d250b01901540500100b80201d000103600507054800081241021a6035581c1d513040c10302c0604085101c8440074a9091249414420190012410303220148102c0314003065044803040400c0781c0d04500014400c2d40d1011440140c501c03801040390352200c0c6001c0e4104880e98807068a1315a0b0b035802284e136a404005d84004040d01030168480010020701d003100914034000140d00000045a4024040c001c080e0008003401d040358051003440703400180c5122081c034100003803a601c0e80030f5200204072000340300c00a07560303030b21034020044025442500c200c1d240d101c01005507001e0381903020959002d40d82400c040b6a610091140c032509504000020865008445024211041c080c19400803940100180c0791103100034486d07401165000c0ca004250000e0000c030b1030540440c0d20000400d4421098110405d20010f10080d6040e039004a01400c2651a600b007120b03a00c41c158611000401c541180804c66183d09 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 910274298 1250 910273048 910273069
    0x705060f0a1107080d0801030302010b01110c0609060f03010308130e04020109120f02122d0a0b1b2b05270307050709061a120a1104050d030e0102010b0f010509 70
    0x42a04030b0f074281d51110706440c00c240c2c5000c0030b14001141d210040050590900544602500030b0130400355445080345840c0d00c070400016000c1c0510340004040748642c9804040300c810b01c503581e13074142e203958581c50015100d500166141d010850050404100c1c620b030004542d0240d50b05840e0744041c00d00e0070f8968140b02144040685542882c1802203000d030311100140c950085590018113400c100454002d8200900c910303c85140242c0d020301e00c680440c0000e031402940e60400000380103582c442e002005081d158118074031040c1070115210401629030303a106022515010814040207000c00010000c80c2c1e01212400c4a1080a0510400d0349144070f403400181010b4005803850030190b038172210301d819440d0307000814141d80c420080182c00141c01613407000306691217a4501c1e2480303982c881c42d0602801360035100c00c1d5907195a041d002e45200b01c2210020320018028000b0410f260801400c1000900140e60165003040103407c04c6250900007601640f005844442c1000c4c03040d000d11814a50 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 910275548 1250 910274298 910274327
    0x1033b0111041409130b09010902030706020d05030f0903040b0c0601083702031002130f0504020c0706080709030609050c040f0b03121c0e10060e0c0d0c170112050705060f0a 76
    0x8010a910045031b08141140c3c480c108241c0042014203c0d0b00c18540782001c154050800c54122011004620f81d001e400c40b40c02030540704c0100d1464031003610442c2140308030382c001c4803842e000083c030000003040492814100e0340c0c404d0550b414401d03205844034140b0080118945144851200c080000f0f0203603e8442c142c0d8009002c6807103504184c0c00c560300302c1e8481c41d0307564403000109000300962006008143e000e0a030a480550a0404465142c1d42d00c403510702684084c498990000790a1500c101104e00040d5041402408046078509110342c80e960350005003400355040c0501d0041075540c41c011100010307400b5006007800e065100b070b07030081c0b030300114001885250105070310454101035000c1d05080c5031120010f01048010107803c0d03000c680c00c0341d000411000d05001001103080d100410358410b5404000c1c0842d0041f405941143c40b000004981500407a02600110300010580000e0a84520400c1111042074135441080100d005510b5000f100b0102000080740c22032284500c0300c040c00 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 910276798 1250 910275548 910275571
    0xf0908030301050a0b210112050c12030324040501140f04151e0512070e0f01030b010303051b060a0e1005010b1e0c0109060b092401033b0111041409 65
    0x75020842d0706c4c1c18103000e912003000b004a078000541809400d00ca0004100c070120380c044944d2000c0c1801f03545a003c000c0610034070405581c030310000b440c0e0030080c010146400030000c1001e9a1194410300c040301d819000b0078081c01100341d521a080c2440d204d10737403480d210360f401d8081c0240f8105d1181880a5404c843e43c4942c80180300004407070302d07800000384c0034809840c003510a44c3d04180540040c01401026028113103402001007021400c8081424103486d05484d2062b82e481010240e003007603402d04210880759100350700070001580f42c1a0300400880f24400d00756080000421009820b03603000b801461020041041140d495504044405282b00911107045013031074021042c46007115103a90003916580d8584840f1600c604d0440019a480559100d5054031415142c031508000006003074080d040c1a0341e911101028006032a0000350401c203007814940c06070307084480c3c5c41c0c05901041d031108030f5824544500303a404106c0080c2d4060351014031048a008410b00100007880034080c106154a0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 910278048 1250 910276798 910276837
    0xd1a031c090b1801020d050f09090a11120906010602010e0c040b0301151d06060a021e031326010b100c0323120a0209030d0e0a080d0f0908030301050a0b 67
    0x80100b10040c005030710452001007480418400068140b201100031101041010054007182c400e24506541021500340c0d4080c0c040d80e1440c41c07840040000854501560b0000b00d940614414030b26005441402c0490a0b80d242ea662094242c1c20781d0035131100018242c00c981010758075820301e0b92101501c090010000b00300c64416505a842c013041c1070300605890706140c03514102e00c6213807000c081c1c1c0042080e00c0c0c0030314044078003400a48448070100704c0250352080c00303c20380c000c1d2000c106a40d41002042c0d00281c4069440c50001400c82d8551807500500d19500e02c00c400c2800d0601c200390460901504141d2581768082007242c031811140400c0702440440e850802c4c120110b142d094002114001d01e5a40e00c02154002c000072a8000340020400340c0100044901e40c0c41c00300c3d1003000006d00c2d0420b0a46070790080c00140b009101604401c1c2079103c2c41554101c01a4131040750100034100ba210100002c0c0c44840d4561207110902886400060515003041400f0801000309480032a07410030002c003 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 910279298 1250 910278048 910278059
    0x70507022209030906020f19030806210c120c0f190e07200106180f06080d08041b0b09150c0a030509040c030b0f09060d0503030a020d1a031c09 63
    0x2c0300c10390041507000812411040c031900b84c0411640a900d050340008107581a410881c1039201c00f00003800400700b00b0b1040109001e621410f4074104449480030055002914441200d076554006201803485400d0140d584d00c0216404141c50003401c40262070300c001840100203000141608102180e009400c00200080b020241c01946024a4a0765114a81d88041c5100d003110143d542345004002c0c2d25142007002000f405e103900410400f03032004085070703403285800f401000f0106a44464024010104401519075016120300e209611616034052000c00e540b026404194640c000e000a44204010596043c680b2201c400019080021010702d00385c01c162402c3e040440d00c40f0100c0120342c002c0b401400500d00b034000c0101030440b6140400c010b03004103001030740c1140c121345c0985c001c00400000c00c0c0070307887e17031800e40e5465600902100d039642800b42d00c0500940c003096070881c029180138a02400381401e906801001100200100703e0a850b0b5210364840f444241080e909000004030300084 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 910280548 1250 910279298 910279301
    0x12070c0501080903071e0c05061218011d07031415010315090210090509010b0a20010e060c030a15081f180b010e220b0901020417010e0f01050705070222 67
    0xd98003840201b10b900d441a51078003289120540c3c1040744900c41c00d00c2140704031000c500c5200c1c0e001c0d2401c1c030341103c2c0d0360b060301c2000d0040000100001d10254070301c0c6605000103000840c0c0c0c0c12280304a440117840040b42c50402e03254291f440750282040310000041001c03501e20032080c4005443c0d09030010341c130b82c0139a0008461040f400c03d004007180030034101f04428600326460900611021141a203401ca0069004041e0710381c524008400d0b140d054041c55040f4025400042002482d2048135403070b00b40840240002c0d0021200740e110941840000d0138144440449002280d070020020040c0701b030703418400740c58a20018507000c2e2056032441d41d4003940c80081c44202c2500d0045400d032400e9410500480d1400800401d161840f00012203200602d50a0084020300c26821601740025901c601c40702502920840c0c1c0310b280d401038038002a01e5021410350041c5c0c501d0360071504860303024030220300e02400d0342c074103c0d0550b0104505100b10009410103503100310110640c04164424201c44000810 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 910281798 1250 910280548 910280573
    0x40f11060c150c030709120807080424020a0b0109203c09060f040b070812060108100504090309090c02060405060c03100311040e12090312070c050108090307 69
    0x20840c0c0e1200702c40c0740103072908200c810f4111410094080ca5441c021002800c060b4803486000c0030600303020504c40500a241003525000c503408220f603681c0704c3d500d21000031341070680031600380052243c2c56000521400020a40310103584100b82030307a90781c6400e03019002009056044035034074100b0345141720122400d40040811900301d00903da4100f40d00b44280e121007403607015400100413480b400100701c82c2804107548000900700d844980d1004a0303d980182800740740e005403288203001c1101d804102004001e055144071000e1840c90981d600c0340110303100c07201170721101001242d009080c80f181c1040d802801c42d40e40641490404141d5404400b021550940f07540801600400c09200800c2018419550800c603502601411410200301c410640c03030940c03000038040d0101c01880c1d50355494540007180c0c07650039041076515414100d4003941c04da0384031400081c801e01400104c0504044400107449596410040350f4648908060040d60710410181840b629803105014000010714590b1a14 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 910283048 1250 910281798 910281817
    0xf05030a0e010c121d1e0f0715031b08070318020a03080706050903040e060f0a15020f210906030406060302060f07050706030203060105120601050f0f040e1608040f1106 74
    0x340a154007001524201d1700445082d8182030b2403240000140c0000141d56044120070030f0032035001c1c032001c1e0301082c5082c2507481119114000e85900140114240b608901e102035541c80c18400f08981c6034980d4401a413040e601d8001c070340d0400114030702511030750000c10402040d403010000908a42c000422000440c4e001721440c40b400544a02041030a0107101d0300301a49500075414541000100e80b2004001050903010b60415820312025030f6500a16000030b1003511903c1c0f03101702c1e80020094030b800800403044483e00c908071201034800311591000d5904405103000c14100442e910801400340d0014100b07030b8846895120100c00360b0b0b81c440041070f0014009102c640d9440913480d1840c1051000c1c0e2201042c10303c1401040002c2e42c01608940001440807a02c0c3c145555001c01a581d0b03004040c080c0300028070208009a43d86168001042610300c03081c107002c21075031540c01c0010008084403000300003648400200340080c40d554000a0500e03c680d005c0303202007101002188980e0848200f8 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 910284298 1250 910283048 910283057
    0x4031e080c0f070302180609072105070f021b011b06020f031303030606030c0504050d14120d0b0d0807030f0908120304061a09130515040c0e0a05070f05030a0e010c 72
    0x20411840e105103509a03004800b1142c072841d280031f50000d02200002022141481106c5680496111f08200000414540214100524103000e40d000700103d0008840c0d4016102d0341d8122111044260500c40101c2c5c1c050f598a0480c64010200002051071010100d030065000e200715114010540e01a5209900314a001c40c007204150030f008040d944164882c1c024545032141d25180300f40d00604035000e03600d081e14940007030245450207410f403601b0f6001204542c0114145040c17002000e0005000d2030210900921000101100708411000180b00041c9011804c01c5038200182c002c1566015491241c03c181805980e01d0500c1418a41040703844003c9800000400003040124440d042c039038004444151800c010791750104886103c081e288001c9034215000c15020000100090b803014038100035501d0780c40c00e0a25040390140040d000d0074042822581c00502c0041043c85071030712400055644505542485500751001c0c2d00285c01c1d4041c660b1240c0c100c0301112001d028400d86d08840d43d56 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 910285548 1250 910284298 910284313
    0x9030601060e1306080a300503060f0a05090a0b0a0b030f0a0606051e0f091905101e080417070510110901121107150c0806010504031e080c0f 62
    0xc009104000043c1c00e02980e00d400710074801c0131400074094404aa10079a0f40000250f00c0301140d0070302040300001540f0020450f0814140340d403000165000765010b0322490101403082d030411079074071141d0180d0f41c1c0200d140000281001c2c119003010100c0c103005004009451f403900741001c10f0768000c0b540c2c0c025132100401032000c1c5900e140b043c01c0041c2114038020381080c0a010414180918488018407440c401040c3e0f8081d003d181403c4500e180001008980310035440401c04c1003429483c0719184c419070064944002c2e041c0250760442c4841d0000c0e00554260446910070344a400c0080c000b0380d040120290706c404442585801415014000c000400c50868407911340403d03101e0081c2120f0100c402070210001d9a6000308070a666054172010100702d1050f18a40c0c044140141e98010300490f0b26908043e681140d180d100300d0020b540350b55511071310766504005403401e10480c4001480b9080c01882c1c180343d80195003810300c015114100d2185481000c0e030700350346400b0000042c3d580b00c1e0030801 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 910286798 1250 910285548 910285577
    0xf0311060f070f03090503090316030b1e0f04030c14030316020c0303040b030a0b19290712180807050109050306090309060a1803030306090f05010521030903060106 72
    0xc26968420400403994809203400300c00140042041d081500a05440d81a64401c014080c010b40c0d6070804007a048501220700c0188500d040d4405100a80d9028200e00c046000742c00646c0d1008130492954040b544c160716448601c2004078001402030b401c000d0783c502c2050008140c0075161040140e01c5e002103442c0d04080d80382c2c0c070302e40012002c004155441511198081c0c2c802000752070890b0360002c07125880c0ea4402c024a405450700b4000c0036844000700c58107480201a164051050300c202d00048450015101ca00a0341004650100c0000400034005c80000030144000700e2520801450324881d0b00c5001c41107028105850303040703580640c01c0326209011550780b09140000800c030441c01450a4106101030791744910a480d159030060400044c100d100501076903082c83c49510903140400d01d03641d20309000380140101c1c014200c0450600ea00b42d0701c010164011346050300c400401a000c0e00c00c0c00d90b0b0302c1c1110b640302d005d041000d0200b400b0003000b940c1c0911034180244825280e8071010b01042 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 910288048 1250 910286798 910286803
    0xf04031202010905062706040b070909090c12030c4803060e030f12160309030f051c06030c05102606062704060803091e0d0f0311 57
    0x20440e42085a16000b06100840e0707002480345e42240c94006001d05100c0f02052203000112010b9610175184201c4091004010b80f98074080c0c0b08000e540d0b02d20405a85032542001543c550074070250040c42808000d00c052244240302c419482c3c42424681c0c104911581da00c040000f85c02c801c80720141001c4145002c0036000398803862640c2d0300400d02e840c3d289600e0064070748443c03140000f501c0245d5440130940c200711704004803108020303003091a40d2601d54842c11110784090444440301c2440b155a0800d00307050107802000a800e605d515042051815942c0407616500009151b0180c0001c0303942030714100c0c0c214804c07800a58040d01403c4402814030003072202100c010b15000d010844d60104d00c18102c44115003984000c140312222141c80d48a800c0051041d01416220089495920121200c4001c0300008900f00c1e0b00c00761001d00c036040d503030380360181c407401080c0442d6001007000d080c040551140321010012020000d0400c3c400d2205501c80820342681d00301c0403804110100c0c0000c3c80340300e08 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 910289298 1250 910288048 910288073
    0x7051c09020a090c08011a040503030c0c102c0a090204060824130911061206030f010c0f050c031e030403090902030105010e0405070207210c08070b07140705060f0403 73
    0x10002030083c000100310062041170f051141001c403000102c03d039289400080111002002e006041b0b0f41c80b01240401d16441d4162081c2c0c2c41d101d00c55416240840d42d0003000c490240a544036401050108211a01440e244102d0b15640e4480c0c080340011030340000e144041d101038001650f40d10f034245040f050380d0f030f40020400384921020381551015030303181e81c450414140c2c0b0380044001150402d1140f03050440c90440d618001c2c3d10460208800031804078038030009103c1c0380110105c400100122003d14203e030031000c0c0300303000244e0000d000c440050040c8010300c449820b000880786000c0c04c101c40c00c0000f0110b10800321101e4400002d120905600806000c09440b082ca41107185500d0000043d040160182e05c81e80507640790400590f9060081c0040401015034214074440520a15405410080d00c02c0040782c000c44c84c0030340442d01d494001344a6080c0c4181c401c0d00361170580a5101c4c0724000400080c20b07042d82c410b62401284a499100103094404030304000d20b611b4905600e005e454407843d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 910290548 1250 910289298 910289309
    0x1216150305250c03020312132603070e0d05010c0503010e010b040f0312110a0c090e060f0c030c1308100c0f0f12060905041118040302070303050307051c09020a 70
    0x2107a104041074000c80410b00000300b00b850401d04144149482c0c103a0460007031000f031550401c840030030000501030804800707036028458203514480450040b10030008030b4005012060106c802d000240c1a180100c80b595000c12004102e0700d034078111941c4180c291000307074044170000340c4007000410035080804119400741481c050310600b403074206000e9030300c0e0740f91510004d0603072401d101c0c0400149000300c4042d201c442c03100064030b48040030b5090031580d0342820310071070030000d00e010344c0010700d134101040711070107901005008000c940b038086040c5901d41003c0c00406184604202483d22401d450314984010320101015281c03ea0440d5496800c449142e40c0b03440c14080c12640002003580e0040943c0422911400e10010300d10b4801500c4000b030620b50458518289040d0070300c4144a02c409901c0c107428000c9603280c5000c0c607100100051410180c80c0180583c1c0085000d10009016501440e030042e01da24100342006015034003038425a090381340744040c0300d0b6106c4d000025824020b401001906 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 910291798 1250 910290548 910290571
    0x1e050108030a0c1e12020d020705010309020f0f060f0a02010b0f010306080c12071e14030f06070c2d05010c08062b02030717010b0901060e1216150305 66
    0x810b0004060480038444000a00b40301624501d50940d03210119000111a08460780100c0c4545e00c41c8007a544401c09500c1070301503c01c09a002410350f1081c01100320550b806015481e00300140b6003404482e0000a02c019403020f010f01502141c002001e015100c54441c55001041c04a0040c3c10700090300000f03400d4034101820888144000440000c45c07400034642a40e10b469401045034803a810304005070030001c0b0709804a9140c2d107840481d982490b0a03901810b0480d18440d2110b42050313590300d140318a804564001070009400c01d802258520a22800344090164103200300407900720302aa414040c855421010107080180710b400d202e00d68402d800c07400d001c10340d810100300180012801c07443c4c0989444460480c5800050109a01d414180c1d01508030349029442d00304030594030f0802c002404041d8604911441c076403a1500280c1d04036107564541e400500c61101c14807a10341c0561400a1892080d06020102c480c0a80343c0306004060803613114400c06100c00700142070390310191001c5c2d17a20b07 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 910293048 1250 910291798 910291807
    0x1107030f08070806010f12050a1514150a031107140f0d1b03021614130b0a030b040f0c080f07050301150603050907080105070e040615170601050903011e05010803 71
    0xb0f4000f4800303a04040709080410300d41c0910030044070b030800d491003102000ca04100c1070124048443d00a84e100000050030300d00c415442d020001d00a64650700610340c011405d443c0061100b482c5402449101510310b80412060921004c4031000da0100d0b5080320216601400f0010200003440713000c10158490014016030500d1150007419030010754541c0b078685043e8010802007500030002210500c0003188d00d64941507480242490320342c54002568014407000c2c4101c06500610712070040c8031700d00100902d10003400e40c3c55010303203604028002c135000d40e848100c5202080c00440a18000c0180320003c00c2c00d1440c1c080c290342800d0b00c07075010a010307038100181068482d0b40030003441c05071102031400080c80e65501826500c2d2906560006e00154606828050910307800b000d1058051001c1d40c051264650b10603807607882c48114200302000a00c4001c81640340e092180c409074102005242441c101228540003078211020a1035000102c0310200c140c0c5190300d0030703001d494014100c071806942003 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 910294298 1250 910293048 910293061
    0x61812120103030e040b1e0112180b0106080106120902040e01020c0d03110403030c11030316080903072123070b03041b03020d060902150f07150b0303040b1c1107030f08 74
    0x403047c085042262030380e040ca160000c103034407900c0d9042104c0a07100040c0200f0780c4000714a010300100113029554480c0043c0003140e00781c01485854122440c5a036a011558411104ca44c0200003001c3c040b03a1154440303100a9a0740700034005083e4885514001d010705e2090284040c04446442510b920b00820900c02000826004028000b417650004442c1c42c1d0344178280c000a0441c86072401d03046044590110180a101c10540a030003140c0c8198225201141c841c0040010204015050048183c0040141700020045030f001c09040c0075180320760200c14503c083c1e55041100e070790480026004048200018401d0fa82142c0885458100d070302c0780c04604540100d007260845640140c00c1782c0e1209002c50454070342da00181080b080298000c0e0f291540c841c0d2210710f0703a100d0341e4180c0f10741d00181481074008156202c0c0c2c9141041c020000c500c0c0610306000d0712540d4002c800400c040c5885003002d0080340820f402048594103c2060072580c440a600e400b80c49012101803031000c110008040015 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 910295548 1250 910294298 910294309
    0x303081501020712020405041a010803030106080709122604090c12020703051608070204110702040f0509030d0e100c11240f04060b100915050903061812120103030e040b 74
    0x13059501990042040ea4850038907000c4010030f0380105c64400d860400010745c1500c04005181610301942d00c0880c1e82d15032080849030007060380103516040c50401c0700000001c28041b0411091916544042e245071030200301f1160a400540c00486440d84030050200441c1d4880940c260768290050118100580c50724020001d01460f2000c140303001c462540c00d170a1000702d000360f848c000c0d8000d00074410400c0548091601d03030401d0344200e005600b043d0840c1114030b4280582e622441b000001503081048044150001d0304500d06a61468010640038111109450241c41c5180b010790f02d94800d200c5900d1292850000d150302c00f0382c01e07000f60321949800c08000d002e405401545501c3d04802c90340310f41c2032a20041c100e082c1125402a400e100b45680306800c81c0005c02103400030a1410000441c10800365858400c0024450313164021000003a1204071003030340c041101166038212030804c0f2070428950000d074820070786c802c010b42c488001082059803080c03050b60038901c01e450510034011603401207072 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 910296798 1250 910295548 910295579
    0xa180f03020d1428170a1413020f01030c05090301060b0c071a09010c030e0d0303150b090d1511070f050c0402040b0711270411010e100f050f0403030815010207 70
    0x2a002c4046450a03d90240300302e043c0540c51782d0421400005082c55280703c0010301c500600c00c5107090a03a000030f40300034900c50042c039032030707030050700701d482d61903000004500500d202281c42d028400c0c1446039a1643d00c0c00d110f00000303056450743d865a00c0000d8041c1604d0319103a81d02c00242801414810a088680301060b603003c0d110a00f051245214645029291403840e40f401e203400040803030002d070500d945500500c40306a5000c0001d03580b0703515044880d03024422324000302d81100f444403401c0005154034034240d564610f203010001e20400414010032403903210b20810f40fa04404410003006002d000d01500400c4a07048508525041c50708034401101c0c058181c000d40342e420300079500b110a0319440010202e40c141d030360010514041114442d5903d40c8161800d45141c14440c40180003540502d0040100e0780e001485040300c4d00d404002141d421505884d0f804c10004144003d208148028010348082d40c400c1d1581181850070900d81500c5421f0f0114860466010400400420301541c00310f4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 910298048 1250 910296798 910296847
    0x8190c0605130b2a010203090a080c01020910020f0106050109060801050d240603050708071d100b0a030e060f160e010207050d11031b06030a180f03020d14 68
    0x80d84424a560b040d10203800150312001c0080750010740c58544d410a40d07040303003a00054003466420002081c030198200c1c0030486800d4041d03401a460380000c40d04200103020704400c858005880c1210300340c08150b81d0441030814402507401946680780042c0c082c0500d0018010038a42510503601d4210001c1000c1410300c1140d00461810100b901800001c02c0c0402c904449030140e21400d0050000100003411644070039283d60003000004501c40c200441e50200300c400008408803074010144a0042422001d405502003604203a00040c040c80701001402051201d510f00083c0007040704021030500900800550880c4d089108100e9206522a121880f0701810f26166600b0014400180d01e096040d410a551037860046d0071010071200e07000c0f40a0381e440580035240d0038500c503440c0051001681070510b03800142400040c0f1070b640b460b80700d0450b030200c681030030b5003861940d103882198565101c000d8005030450100c44901c25000b50030042200a280c142030b1409140302e003002d012a00c0346985 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 910299298 1250 910298048 910298057
    0x10090903080a050c13080303090d031a011110060e0105040e030307020d0302210a0f11070507050411041d04050111090a030f050a08030106050a0905060903150406061203020708190c06 80
    0x120f4031002411017607440045070100d01c0c00082d5141d0388030036071f250030440781c44001d0312903503004860482c07082c0540c03040500c81c4c407203029070b01c43d4131f80040d9540440240c07940810b2150b8003c913500411309004000050948400b821519414a014407003540c2404140c0000ba9004009110900381c3c00240200b071818203142c010f85407003800c003034541c0c92809082c038032101e81d11040034030041c00303403941c04640c3c407800031207082106d50b40407000408103024048003e8440c2e000403138100403d09007a04204040d4180308421841c0a40b110b02c50310303c04030803c42c1081c012000724104000c12000344980c0102202881c1424284000d070000540c004002d408018032404540c1c0c003100030480c0401034200d459034002100d545968442074000c000350084840400000c0c2e03481400109820080100d810301c0c3d202170b0103003038045a1101c0303480f030740e4001030812038072180c0d00c038800203100080c91070049141d8866800382c0302061030241041c0c600300c0101c004001c000f41624400000400c6800c191007160540e060 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 910300548 1250 910299298 910299301
    0x2010e120321090c030d0f030e16080c030c15390a05010b0108040f0605060d06060b040e1b04051215042409080906131d10090903080a05 60
    0x10309821401490388161080114001c88003009035480810b0344104900e80c01c0b1105900f40342c0805d170742c81c1650004100894503000002c1c140790f120f5000000003c283c003044807401321b51880c640c608080302e6849854030343c0011540305c0721880c0901c150281081d0488848400c1100c0811003019031140c4002c050f1710800e031050413120164403000c1c0e08a0b0381102001c1580d80182000e8140d120000d40b08116015480c00003080742941c0203081b0326001e0381e0842c5a00300ba00b80c15076aa00000c05014211703a0380021046d502c41d000540314000d84004e025134041240e00c4901d03082c80b2440c0340d403001d045144606103291401c40720344040c2065504a0300100d50300656250100b461a0900e500c6400401c06905500d04101c1407003001040c1d1100000c0800500e82c01d04200c042450885508480c010184001044482f0041c41e0103c00742c02030525503060264019614051840f10006c94a062805901c580081015011880481400400010303005000d1003042c0d540092101c00c0040c4032190540c1c1c2c500 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 910301798 1250 910300548 910300579
    0x1506130c0e030d031d0d020a0201030b0414010906060908062a0f04120201140702030c100e04022101150903030f200601050301050c040609050d0f0b2a040302010e 71
    0x3494030500300c1014099071092062020000e014200341094000600311008401500c03c0000403001b54145d07865003d2320b41080203030f00440140c402032481503070083d120b4881d03030120000004120700030070083d2000900d0300d1801101400715441c5601c01c4800e03030030040c104540030311b88058140801400001880030584200c0c841390301401400c2c5044a02d58000c10041081040c1303510000720b403070007601c900c0000405101d1441c1648201d0b000250150001c031211201030400e104004262412410b0000300030b5035000c0810100c0e08560032043d500e280201012650804206c0403e01510100c01caa00d211164004041c0404d041781c48010104a0b8000c0240300c4944500c40076080382c03050f28040101c3c012280c4175aa40d4207000c3c0242823095203030201160f551042003085504490907074581d084c0451070801044003403921001c080d0b506010100e200307000501d56010b81c80c892441e152903003650346045c0100c0c0c19440c4596180803801c0d04200014800b60f13802030f02e02c0740884011580602d107003d900 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 910303048 1250 910301798 910301807
    0xe0604080f1905070519080d0f2d050705070b0f0603011e0507030b09010807170f16080f030f1602130e0109020915090c03040f17040302031506130c 65
    0x340312070140151814801c15050f404001003074918003800445038445c0c00001c00034a00f00303205000500c0600204220b4010100306e8101041e6428002c00c0020303006011500b040e103030440c01d42e410400400c40b500d98283d13000749101c2c95800002078a8040d0518080d5500c014186001820748140780301c8690024507181c0c0c0035046000d01c0d86040c24601d404034610551400900310513500140400e003041c0c2c022080b0304040094074103d907000c1004248492504001d012040e40130070a050550069000b155a004010000f000c00b00001400007665146001d50060410500092103030041d0010000880d03c0ca552209494201403101c035081d140c0001c504c00070341c0050050903080c1c461810019403403010a01940840880c9000741c41c88a8a40d8405001c0c026614405240076400040240400d10b411201c07800b440d40144100141001c1e680162a034007203800c005011a852038200040c00d20031800c0034080300010b02d0080f0b5a0703c44506002001550f00b4100c02c00c401e40440d0703283c92442400303205 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 910304298 1250 910303048 910303057
    0xf0e120313230a03050301060813020105091509120304033806030f100516030612030302070321050402130926041e05030d080f0705130b0a081005040e0604080f 70
    0x4103403c50319003003d945000f808940091003950301185c10080040c001001c81800e5202042d4147e407040d18050024040040c11101082109814241442403c0f1141c032034420038082c540c2c0c100000d43e100c0f891807800c41640c1c05143c0035141c030a20140034481625032000207003001c1011a80030300409a5503000440d140584a0340740340351a22400c150000f00200315030015000d5401030130200c18100c90040242c05452881c8114041500303082110300109220b50701134010f252003441d1000d0040810060249507400140c1848151542c41081c80114504515540001408020148420300841d00e8550600c2d40e51005003440c620110315141c0c61a5400c0d00700c60151548541c403c030074000d1401038400b050101e0162a0080c41503551500c4141c3c010721a56200d8401a420480d082d034401c0021030786071300507002c0740040c803a0607080812141c0940000e4074140c200d564a03480300d071a061440720039102c01d03944528003451421174080c4080b0b00108807281d100e9085030388559a1100b00c03540b003070746124 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 910305548 1250 910304298 910304363
    0x1a040f12020f040911010e010f090e1b070309050a1208070201112401050a0e19230106020c150a020c280f06093f060f0e120313 56
    0x3521394100e040202403a8000304907502030362048514000c10f001940c0525102e401080451003006c01000602000c0f41c0c100e034444500f070503020034002d03400d89800c0150041c80046002c03454201c01401507081c01da0550004219142c0401ca8203200381d19140003c0c4100c00c000f904001414407070f40d00d50502009031151104002c1c111701048441a0342e80b590b003002c00c0c06241cac4190849000010318181404800e80503910000c05a9480001c4c100c9050040c07a8481720501d90140b00464130303882d08079400000e03008007403980142c180c0d2410700080100710380712040031452149040c040d4080081d0300140c0286807120030342d2501d102c0703034a01c80845842003607103002c0a40da1056040215075210f050000c0c0c000c981c92500c0c0e00d4105a122091905003c10820f015440d800410070003054107000710500104c9070b184101d00c070300b143d0183d40b200c2c0240c0f804c400030240c80c1c1d5140d04500130b03404820840c071001c682040514600f1410820840b040003000307940007400c05074101c40f840d000481640c068501101 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 910306798 1250 910305548 910305551
    0x503090f030403410f01050c07020109210f060509010b0a1a0a1701080706111506060702240910030e060402010c0203100501240828061a041a040f12020f04 68
    0x903200c1d0b8a17a5521828242400c0755085ca004203200f491550140d46100368140c40303d4103030750b003001c01c1d030740c0920003048030b4201820a075a00302020490700145200003038040c94000c2031034607080c00342a01303542840c8101f42c020002180200545d03041c8600c070420514084407140c0d5207001c042d04c01c4520480c80041a0600e0000d070000207074407800016003800310f551075191402a01c480d00c89642e2510f00041c2c0c0a0401d2922000050003468804000d001162008040c0468492991b80f403104851007030710900c400103400902c0c035000b03191000c080f82c205101c070710b41400403000300080b0a881e0103003e04002d041c4800381c2c5104085603818041d0041041541c402000b856945210003802c0304105164041d0f40c1c458105c4481c213f501c00e240180c07052603a16148110110300401c0011030034207440c0d112960542c0e0f003802150111240c2002130785030114640840c3ca95051042000201c50145000b018000c42080200101d0039407001c80c008941c400d8170303540388454890000c60041900303d840f099106 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 910308048 1250 910306798 910306913
    0xc011709030f0f0a020c011e030504080c010905010506090637030209091f020f030411120d02070302091005220b060706020705060a0203090c061b0601060503090f030403 74
    0x3c140800240801d41240d60840d102c000c0300f480103513100500a140d5040c150300100a0400c124041d03008250428407440705a450f042c11801807908444440700201d07441d0b51264280081460000303103030b9401402c200c5180102e40c0154910600c94200003c50201c0800c0914998121003080c40002c0011900038000c500d407894201d210036110584408a103007581c040c0c41002c0e4113000103100362080d0ba26204946807075034603aa00e1314801072002c0b040741c9070700660043d003003504070343c09004092181c002d50b00185070780c43c15481089490480144000c164044000041055581314049001040301d17a20700d10f034038900c601c250030010700782c0c207103866810260005d104410000c0a40c024101d00340500f00303458007512600c81003000d92009542d503170381561100805030700c5413800100402031a16141c0a0002401d804012107003014802da1161022400100c2000b81400301809814400c0c00754101a51800d411690b81e4800b14078900c11040e04803c882160080003914029022505002030705d948110 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 910309298 1250 910308048 910308067
    0x51203160c1502254e02011d0109060f03090b18011d070612060305070909031d1c0809030601171b0d060507020a080706021b0c011709030f 61
    0x481143c0301c0d001d2135400c120828100c0304110f180b8494190b402a100360140b401919070365640e00452810a41c201135a84440d0b064107480c41c681c000440b00b0b1480c1c985041481c80d00014020345e4402000075402e03520701180100b140e92122070a001d4480130b00304901c4401901078100c0040203106002455851020244410318101195589490030140001d02c00a50401090031480000c035031001a00e5000d070740709000e602e005004080e2081601a0001000381c0e0705e4603002d280c41c03500c0d8400745603039a0f1001c419050680c4003c84150702c250941c2d0074481001d01c0300101c0c40c0d40d84401940c142c10001e0b035010000300b103c15400c885911030000e007107910301e50f110125070101281c02c80b9030100601c507030480c0203209482112110f084c81f1004101816504003078440001618000f010141140580e10210700059503d0015010003400703890b00507101c2510a15010526020000c580f4417a48645c0e09048140ea100401044108104901c10310580b640300443e4614040c100c0040040400810301044 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 910310548 1250 910309298 910309303
    0xf062301091407051905180a0e0406150608040f03032a181a0d0e0703030e04050711191103121c0516050a020304050424051203160c1502 60
    0x148400004182c0580301d044003a241071055013006181005522080c802c5240280042d218680d86c029400c21080c07c040c00040c128615500074a850700f000400b44010b01c045407080886e860f40000c5100021404d040c40517201c18001000104661120b000b50300c01c1522170b07000380410008a1081507543d250076400c030200b14000c2002180014070041c40e0002a508011189088882c40080702c0710400700b8140e01a16548043e800500e095140c0c00c011b5166481003101030300650180d560100301403c5a8108419220701900b04810082010100c601108001c03a0170001505290f441c0b810701c120500d448400768603201001d507890b00800340d250152400700001000040f05014074406686030b01c081c020202c0d8010f031100301c480800c80440e40241400f0303900800c809000da00403282015620800607054583d43d0074002e0071521942c071341c1c00107074413408049070141900311080749120240c400041d5a03030050902405120a5010002d8103021005461002030240b00e00a0140c03d00d1081002e503 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 910311798 1250 910310548 910310561
    0x507020d060b1302041d100b0c030d061e050f0a0923090d0804140111040303030b12070b1c06090e061609060203070803091c02010b1801030f06230109 66
    0x14010f5142c0080c050000103144215015100c80240c0902118145902c0001d8901c000380020660103d100c000b2802c00f4111014100041400c401141d40c0c0001e0010030060799582d47c45203020700c2c0c000103000211503850034850250340d01954640081d191100000d00000200ea2041c13840d541741015144039003c511081c190689058800300e25181c640b03512055852208514140c00a01032402140c0050001c085502d41d07402c90303100104800003004507072091680268000c03000f10b03640720081400d0703041030340c00390540034059405003100d00d1901c9001c00251050040303400e1080750805401c001c50b00706600c071344003421002408000d01c1e0b4810500599855066841212100c84c00c11a541d0301403182c620101596811340c00ba60400d1003aa0b1a001c0340e800107065008540100c4548144180012000c00c050343c00d607500218805291400f4010380c00c40b1300240010005d04000140049900c20b80560700341c5500c0398002941c0e40018000c0100c41c3c0103541c0c0c41c0204800c0b00000954114141c0000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 910313048 1250 910311798 910311821
    0x15200d020d0e100b06120f102c070314070e010c080f1209030c030a0315171e010926120f0906010605070f1b05030124060c0c0e04030507020d06 63
    0xc000f48020321040211750300031007160540c940c0c5140001041001d20710142c90300b180e22000020152070b04e0750a1001c2151080826181e140e000c41c00304081c820b0300003020754024000c4d003000c02c4555585000f0040da420000c2c10107081c00768440c0d081510b40d02c0390070745829039a048655540c0f0f03030708100c00310303046503010266068170401c4040110786038500c04411660800390041c021032800071540d900360064210111000242c002000b0001007807240304c000010322007410070141072141c420b03443c03d80071100703481031180a03a0300d441d0a01c80061403008008089807404440003001c00e596464081c3c591007001c1c1b501d517891102e007007400b01006500304042d01402820090340c040e40e0b261001100c40d80503903000a030075858180e14120100788000091202101600040801e464136040403900b076560b0a051410022030005051240811809a84014010358030300026941c10548031a140c041103030043e1306012800c03101040405020750229503d982d8050141d400b43e030100e0074501d00410601400 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 910314298 1250 910313048 910313051
    0x302040b040501050612060a0e04121d010e13061a07050d0c0308010537090b12150a0e07270e1b0303070203011815200d020d0e10 57
    0x880c091410380a400d040e55405480a4102001c0404850011304007038860b94020400d0070340460200034100e50180f190380203070740c014407829007140010019200000584d500c00d80c0112000f0041c6c2c2c3c814499040c00c80304903210507012002100580c02001c45601891058554285031080001c0708400b800900b40548151100c90f01000c00c01c0d20840ca40c8840140000c040301300610491404003130081c0c400442014618890a400480202220040d00003846490000904100d9000745016030113410406a035035107889054030182e80c0d034480400c601009190848030004403014507660040c02c01d12043d404a6102603902c4da0301000715105010311040510001200000450039030051001415410004100c0c05904450358003400d00d1404009a05010401c90f480c0035076001d018250b0f40000340f40c10300650000074034004602004800400d400181040310701403100c280140103050380603610020650f620f1031501404002e2284540860206180c40308104651900180056040411940 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 910315548 1250 910314298 910314311
    0x40b010f05030c011b12050301052704030c032d080919030e0f040906020c0f0f030409150e0906090d09050303070204022d03071e020a0212030408010c0801030204 71
    0x80308484903090081c25003507032101c3c0d111002940314481544010006203160f800801190b0350703030750802c0022040c8800190300400144281c1c0f4006078a0340e4031042042080c04500102d016980540310018406401e000f0300442207400d150041900700c010030603d00b03156920500c00c1140d55040c00180c3e912100041e440800540c01400020b00002c82e9006940841c074000003d5900f00c41102c0540080d540100d05008200810745490183c5008035114620168407800c510102c03d1030700841e8425032186500800800449031004000c0f10203070703404641c001c2490401c000b000780010002d58864845521070400300004d0617004600316000c2c000314001e0340c400c09203180049548030707040d02030982e054008011400052a10342e000b001803140343d810b81070703021041441d8003210200042c6002c883d080e0010402c011140c0c003481c03500784004065190401d6000a1000035070b20a08540c009020741602110129051020820b86000b00800402484211800c0a004040345c50a220480c011401c044 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 910316798 1250 910315548 910315559
    0x210020f061f1809120c32011d0105060409081207020c090a02030403020124140f03010908070c0905010f09052e0f080a05032502033702210c0d0b040b01 67
    0xd11101d40c6580003034810b214101d040344072150220200d02580028801f03d5030820903540b00f8050089129030f1804a0034085003100308550079188020142c0c2d00c954585521640010701150a84034000400310b00c0450341d0303880c940300368500710020522079031140b113500820400c1c140540095114a00c00d40c000c1c082a059041400a030348541e00c0d04042c149129903062010007281152491030020040005090b085c50001290850307401c1501511441301c0001c5030f1050000d104510b000030084550108003d41c505110003203425214092035103902d032244d005c10101000b24441110300404c1a440421440141c66040000d6230244a04200301034202e5000030304440c0419003100d140c0d008400341d40ba00c0043c0d07084248441079a130381352900f011486000805a02d042280c0c00050b1071410194440d80c80c001e0910502d501428803490004c02c0c0840020016100c40317640300111a90440c003c10303012a0000d4041c00e240c6420713003054107c00000f402405000c500112036028501070a10451113036201c1e03 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 910318048 1250 910316798 910316807
    0x80325050a111f1e09030b010b25030504090905100e06060a0603020c0c09100f14010816021b0a090e0102090f03061506070606091401030210020f061f180912 69
    0x800d91140031441c84684c8003060107004001030b51a0026117800c0502c1603c1e5928102c0d2000c00303800010f409a00810481c0316490300901d0014400040c6203092416820750fa001455880707140100c8545130703195685101004070070461102e01d400d0712441881031022090800b0303610f50045590038459101c4160010f520b502a200715040a8011006417010545444c2449031003a009412321601c0c102d6141d001541d1000c21524401402c80c84070481214503440b0001801c840c0302620103040000208800c80040e90001504160030b14042c608942e00d26210000038518481980070f182180c0c03c2909044070f440065008005410b0116400085a250b160500d691250100e600c424200c00f002e40b0a0440d14280e8003400145201e0140800d032b01d511100c618043da02e1a4030030380075044280005001b1442e102c001800da10701710344000c0c1441d0b05009821651100041c20b03404050070300300200c242000d00d08005502821804103100460300c0c41584600007040c0325074096645161101003442c01c80d04c01c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 910319298 1250 910318048 910318099
    0x3f020a031b1b060b030705090c0a02010605062b0e0a0c0302041a06180d0c03050f0c010807090603110403020d030203040311030706050a03020c0109020a06020d1206080325050a11 78
    0x41022110000b9030b0350f0310001c042c1a54030680c188501840066140d6441c1d800620031501c4000d00b9490304a0060040e081d10303c2c64001c00d21401007880948000c01d080305511200160317a12203044100f0200c0300702002880b5154042a460003940b041c5028000d0715030bc1031088070f00c00d95041042411003841204001c03842e0f2440740e40841d0030020440382280503000e00405201c01400c1810b4050305948840a043c02944212980e8110405558800201f44540107992000f82070090080c80c0510005190030758034000c8105069031084240e203e40301340300030394000d1503020700b0840c40b00c6a141000307592900188021158481c001c45801e1107400d0105100084031000c2d25018105042104150082d4110700c004c001c0941da240078440c0540d9504246000819031034001e8800002070103402020448902d01076015a400c004d0f04216440c000070440e1003541c1e1200412141d601d4000d040d80001290703540140045c400c00e040c0070144048402200d0454100b1103010780145102000b0550301c400 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 910320548 1250 910319298 910319327
    0x112051b01020c2205040f120e0105030105011d040c03020c0f0109110906130510090e01180b040203120a02010213050103050f01030803100e15010f3f020a031b 70
    0x4071031010610b0401c040405181300780010320000f42206000f00400b00c810454040e131701002030501c20000e122100a12140040302485d0000c80200b18800180251006100c0c0364100444004440004003031041c4600301c80300020014003030210799010040194116044944c0c0500844000d04010b030340500c56440b1301c80e030040c013410489039a00708000c00714030010601500140c124001e40003485640c820144612100c50800c02040d0910310608122511911300301000ea24203459484229018169002a1540069000040d5966201003420310300d005540d41888240030451404403501034000d0321003842c43e020346100c4555a10011000ea5030240c42d65684210003c00500215441c0d20045500030000c2581e040015601c1419032401402200c41504013000c00403120b0311582e028110425480750b51403c440d501c614010b03283c030281d004001c527003284641c1c20910180e4075445035a11000b01905a01191a20348014020f006001d00442e1070b03142420495598980d68040c00c2a51450003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 910321798 1250 910320548 910320553
    0xc15160219150b011101140702061e012123100516080403110f0102031e040b070c020406090e0d090b1806090604081618060605121506030112051b0102 66
    0x85480c60307040014000c3c05601810418002c040c00c4004509002d4960001101144060540b4290354020704011010f002c52400c54503c003d03402c03290743e001452038155998030652008000d20b0900d850072406502c10001c2445412a00015885c807000c0c410102c0203100c1e0081c0c6174481c9140c1d4003072040381c0d012611401b40b111001c440c2e5140c0c0d485600c1050740a4030909101e0610303402ea90500741b40102c40790030300c0320980d000420025104070040e0081d0940110004007030140c1425030320900c0030f640c0140310404006140c0c100d0815951140c0041d0300528040c2000c00000b940360b40415241d00880c0c42c02008911507440003d2640b1540c0121072404200c418640380d5822480100089039028680741c9500040078800070400040074408081c0c0f001d0300c6c02440502515000c2c10a007080f1108c501460401d10b0100100592030700241100c455086a000069150382d41517010b042007040208110340010f80400040b401c0d081c0e105820145034010003c807221b1241405661281c41c40500c00307140180c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 910323048 1250 910321798 910321823
    0x7021903170a0f0c02010e0a14150703020c101e0f080702060424020d38090402060904020c070b0901090e010f030f0507080a080a0e1e060c15160219 65
    0x900c21340d20f0500d007031710526115054040860004138280c505401c2485515030700b0900d0a180d1911410b510805903480c2c2e10f103030400c61551030203903e41c0c003025035140c064039100c1c904000c803600c01c1d20710349140a2581401d5003000b100704802000c1d580c1010702e0b64003044407000820305150001905520880e800340c0b44000031b00c500c0c041321841c030320040d90785400c0b65003d000300c8001c8e0441380685646442c000c00b111860740f01c44c2d400b4403a090a11007407a1041301110100701c0141e1548103801e9030280c0c06036415561042c06202180003442148101a19402160f00100e2219007080003090300002c2607030f070f070101a9141c030003c40c03140c0c50a20a10040c0200910100001410603400008c100d00490546044642e20140300d030800030081022121811300103032200031550848d40c0c2c09002e44d8180c4003203007010003180003403045a43c618a030038800d031004500c50002d00800c11038540010140c000890090811001c152074030414850684017601650080602208100b40704520858003c0602d6109 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 910324298 1250 910323048 910323077
    0x20910031406100e090f090715050909180a06060303121404060c020c15030a1515030f0605060d0204050a0501050f07030507050a021c03031413030e03010207021903170a 74
    0x18032002010103414885103084c0101c559550071010b5104000049041240f0300e0101603d03810040c0e5030f0010760030310703034011460f0072010742c070200342c541400050341c88100300c0e240c801c595020150700d005110f60b20f105a5a003a020000c040d0055070440380b207a120070700c40410a90b4060103440ca46050000101010000107010841c90780140040c05040d0065582c040800004141c0d242620414020300070000020b025401442d44520f940303031500814503141503424160104203261700100d80408044d252142d001c0b404046a00c20320052000500d81c130f0b42d810700e08030244003941052041c0c0e88200508000020194021012a202d04607500015440c21445541c181d4058004400546282c450070112a0050311141c0c1403040040001061401e038044034a4010f0650341c03c811010b030403140e40c030244070004a00d00076411440e5030505018941a501d0070109009028152019600107882e20f0310035034401c0103e00c00c80a90b401554200da07100645080080c091158400600001c0c0d0740d024034014 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 910325548 1250 910324298 910324309
    0xc02030c0f1f05040c0f1d150a140114040f0302030c1e0118050301090b04150903210f091b090501060c0b0604200c161a0a09030c060201020910031406 66
    0x90052143c084955886e403202000c0200f140540c0203052012946081c8101c1044c0801000e5405035042000c100701703050300000301e03a00c0c615a204508a41200d4500190035a008014050400316090052600c540d611940700c41111207602c010380c001d008401c403604244c01d102c072400111000c010400c1d00540384c5a0f0045a00c1c808a20340d14466207410a80810256420300422002c1070042001c2c0d41030b4101400d00d1030100b80e5062100704228600001d040c0040d400032052408802010300c220a050810007882d8040c0042c0302c0c0d10150740b0f242c91968000c006852940044c0d071f1720703102c0014459030b0301d82059104451083c01a20041555602c80000280e10b400030294042c201520110b0038442031416440d0b54030341c50316003602010010400b69035041080240d002d04651041030024198541001c12018200924560783d040400248854089010309038a00066a10410140040d0b50b1a07800034001c2d040711000074031803600f5852602d1128417a000d218405940d80300078002c0c036241d4004120 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 910326798 1250 910325548 910325551
    0x30f03211d161703070b040b0105040b0405070804060507020124060201060e010b0403110a0e070903020f06271804050601090b0d0317040201200c0f0405040503070b06030307060c02030c0f1f05 84
    0x1c0b010f1000301700c0580040c0c0343c1c100031341c0554840c10121000754100f1041000751a403400b011401a880c0004200420b607110001540140d040038001500d42c817240b40c2240540422210740c002282c600686001d50644550000d00b190142c1d40204222526504890b0a081c400c1c840c41c40d5001c1c00380070501c080384d1101e00d05030071150f0050000725881d55806004590110480e42480480e4103202c0810660902c084040405d950407070309149084076819201419191800346001d20202003c44800c1d02d80300d04031099401103004560324150324281c5841e80c5e0340c040c240520a401da0500e10009000e061512042d00c8640c2d040c1c807001c000401400480b0005080240168108460900754219201054942d160a641c1d0030300544891440781040c00a5030345e0f1a0445070150740b8000400c00460004800e5651065004010b01826241e0000082c82d501500e00043c201d9483d115290300c900c4e800000030400e489281090f2245441e128691075121038802c0e0341c0c1d4010021000702d0160700d007060750199 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 910328048 1250 910326798 910326839
    0x70201090b16140a021807050406030e030c19110405010311190b0c030406080108070b03040f0606030b0c030703051005100e1318020910030c030f03211d16 68
    0x50840e98600e440e4440c0d525801c0f5201622508031121403029810302c1d0070855003a486945518000e030501d400700400b00d00c65441510b0416569440d011208441401212035607801407040341d4041d4070200c107110f180c0d011001d088030240e1700e8500300c40711400c2c5030080034102c03900012054405509179051100c20510840e502e116207810005c0030a026440b1000740651005490003591118141703400a400030702c06030440d591139401003c0130071503042c0c090120303544140e200c0441c0a00d1469854024050305480c3c0000340080c51007000c001c000161507010394403d1310140c3d030900c0103442c0d80c145030410710414000c1c40c1c0c110080c80300c0c0790080b6005443c03c4c907020340003030820311100d04450340303942c110398090b00003005000303407031000105518080c02c071103070480721008001c05030520390b648800c0e1210141c400208a64280382c28902454001c83d1001c040c440c05961a2047d0504884031500030601d180001100e80c04800300f00c01c0c2200d0004800800c4103500c000091100d0600d01e40051404008809 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 910329298 1250 910328048 910328077
    0xf090a05060709260601050103151d15100f05031f080102040303091a09040903051b0a02090a140105090c090a0b0a030f090f121b05031206030102070201090b 69
    0x500000903001c201d0755128110326600c404000e0700f403881940d810581c0740603140200c114406031402c030501c0401d17007604545007401c0001d545100b40c4103102001030305a00000760100c03080d98040d0f003030156446c018844c041035050400d01c5100072040010011002d5404400100d140444841c058042c200940c1c00220703840303000c1d01d0304c1514040e000c1c040c641c0c1d4001c5039199401042c10800c06801c40d10800150000b141d41c0759410000200c958424007801c41001e1040340c0b0b56005e07000f454003500c11100c08828204050004024000725a507036244203640c100e000c1c46031180000c1c030707000181c80b48690341c01101d01d401c0010307481e050411000b032002401c0c1964408040025101650b5484140f0000381f40000c1e000f40c54401d045409000c644c207003441540d46a040400d40c3d0005500b00c00000c03c050b90200079a1040d02d540384045580c0c01c1005a29007600030410450f03001d00800002070448008451240300490303651100307048c242e000780c1c00000d01081e030b0a08140407079250f440c040c09040607502c0d003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 910330548 1250 910329298 910329313
    0x140a15081e010b01080105061c181b060810180e190b0705030105060a03020a02010e07170c0a0509040b0408221707181a0d110a0e0702060f09 62
    0x2055420401603401018028a00001c1d1030840d4034280219a00d01109003010940c0750b2402c0041500c40c4101031b10b085904403481034a030b80349112907204107140c900648001d41030348002d00d4101000d5007000d2804102040070807000a0b05072092a00a120344000480c0c841d031249403201d000414022a010211700545130442010510010024291034403160783c840e0500c01d8803410121b924060151800707081050800040c070480e141c0c88102e0703500d00c03800d103001a40c0c2c40702c0c00302c104c0c01090a05409101c81c0110300b00003038040d01d01410031704c03500d83c80c4050340d90130303280041040010012481429045241c501c00140840e50300030788168010b002d40f0f50b0710719081d03501707640d0001c07412510075400300402c440c0d5007407121441580501c00700c075440c41c004201e0f117401c041c0f4480c4040020b81c00f41900c2d9440340b05084035001c20b1303084059402c0d005003101640c20443d00e0040800c0b540490568041c05030800002007181064011728059001a00030f072a4585440484128000004100503041c5c480c0d0300c03 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 910331798 1250 910330548 910330559
    0x200c2b0812061206040819030902031e010605190603090f060216030909091a0601050f0c06070816081303140a120510031a0a1b08090c04140a15 63
    0x60040031901c80070884000145080002c003e8070691101c40c900b40360340602c04100c0003504070380403284901091014038210080d80c0c081100a0000048000d4060150140e80e8000213031141c0003202c10340300c070700003407000c0340e1242c0c2440740d0b0061443c202d0324070101580b410021107029602041103980a64542d030040111504d515042ea8010b105602c880c012102c1340c4002d05901441040241640800601c052410f0351520944402c010315050300f01d41c0e8a0b000b14555038054000c54004030b841c000c506813038190f81685c0c90b80f5076a04680c4034000c81d0300034001034001280c0c00422200f124031900c411400d51a250309000c500b20314000101d00740a034061140e0300698145000c0c00d00000c5236901c4202e10000004800c003611405448044041c201c02c50902c00940001780c0c00302e2001070007040d03903150b40c1d0364015003004d40300d407040c00009030141c6028484290350000219210301051001c0348e001010107000c0c0300840c0d40c01101c000e4038010400c007080342c2025640000e0340101c1d0070000c5442640c1c0380c0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 910333048 1250 910331798 910331813
    0x2041d03040305030414060a0c0b0c04150503011508011d1b070b040507050a050609090c07060504211e050304110406080a0b13050a0312021603200c2b 66
    0xb60415601640041030400040022024034505a0010303a840e60503c6881200030703019000707141004050075807200000310541e041070151001031034090302c40f0010110070107002d005540f0a0041e4426003c100100c0c4105a005260785412074210740b554007504016200b10421643c0050901648031a05444c15404c0e8603040c00a4445140a01c400b06120308180c42c0032440c100392507001602800d580d6604010b25920031041d901101426201c0801507501c142c40c4034003601c0f07602da00030b10003450202884140844141200c003031145440c1c082d04945040d020545060214400e025880c00d1054803940d4540e10403005160403910450441d20f031000c035600060191102900420200d40c0030f040050280440510046d801401c0c00c007400000c14155102e440e103541140354042c0a219883c9020704100c6c0d0345504903158011000c1e0f100810038001d01d401049400180a1010000321268106503001c5020540d0700044030700034080c01252051003094030001000d0305a10100007000000e000100e40300 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 910334298 1250 910333048 910333057
    0x90206070b090d08090c01050a03060b0705240c0307030b010c12020606011407020a0b0a05040308180906040e1509150a0506040e0609060406021608070609020102060603010b010c02041d03 82
    0x4291240903442e20a080500d86820703c080c40d002c010300700d0284142842c000c11a203900140a181c200e9480341940000c0d406445140c0c800c0d02c003080300162440a2107404a601102c004a5540d04850100c182000510407a01590a821603980c10004101098001e90215034551810304000c0000005500c941c40c0d1503540d454650f0140c0c002c0c008120003507a004842c0c3c070b2981080311205040035481d0700030035441103043c01111030340480000c2040045000d2400c2c2c40007180d10030a172030340d20500782c030310b040b60b008652140f80d0041d004000803030007a00d01402142e40941001e001400200e17880400b840c9691006047c240c010301500303c0c207000c0300103e84040d900c641c0010901007520b0502d101403004940301240608036681150080c0140b040c400b20304140c001390403500150300c8005245245900d80c0032000000c005410001e0011300b0042d003034214040d001c0c000d80070340d003851351303428241401c0e551502c1c0540d0000d814003041c100186441d0b44103034510310040c8506000903c0c07505449245501 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 910335548 1250 910334298 910334303
    0x6060b0f120a0e100b0a0b04120b090106051c060606030920150a020615030109050706050d0b060307210b150c01091a040b0a0b09070309030c0203030a09030501050f0705030708040609020607 83
    0x80b50701840c00035003040505c02c0000c000d0101c50510303027403400185840c02d08030010004e10700d14022022a051400940002000d000000e0400b2441001c003035411400c521030714021224141008400204035019100f0b00550300e8100112440c020280d00f00788107046075043e15980d12441484800d200c1441100c06440c042c800307a0010095403c005583c1d9019500120405100e42e0412503c074000610120701141180d50a080164448654042110140c81034144994104102004110041398001040d1507000803c16080c0034580c0c0c030360400000d80d95810301c015000b0f01580c03040700b140360880009180900707000000040c00c0100b03944105413050b42e02d0b040720f039505000c1700b80000d1000201849810454810740ac1100042c00c2c004180107090041480003855600c0b0700071400e05025891880c2d415500900303803540c03603544200117018004240001d031159860040007401072910005898001c03040d80d1920350455071781711001c0382c0d1544001c00840d8000d440e5040301d401a141c100162100f00d1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 910336798 1250 910335548 910335551
    0xf01140c0709060e060f010c03022b0e0d0305180a030f080c0d02030909040b04080715050709091a150412050d080a0b010f080c0f04090906060b0f120a0e10 68
    0x3880d10b020072007642d0880e081005a515103100780700b625500da03003400d206100c00b8200b05081d414036040c10b2342400c18502c51000e48070249504c0e11035000194140240d44038546d160700088040301018803060328501c00e00100855800c200148a82c024503100d4042d080c1c0041c04200c800352240d90b0a0303c02e09080a01b00c0e01c559000c200c43d0241a0103105002244001b44011800c9c441303018006606100007810141c19458854045000e01c8508400c40c0c0241d81c00c407000307217071103142c1c1d0395048005c0404580381070005400c94004038098172a4092402149860010b00d09881c1c40c040401c050302120072140002e0101c1040b00181c1103d680074480300044c011000382a410020080140c000c5070000e0690603220714240e4a009a685c00c481c440301001c981c0d04e04140c0d96925041084120711400c040311510742e801245c0080c040d002a041068481d02c0f4180038014180d840760b4284e4107004001501d03c0c01c90082c481e1610ba00d054603c40c0340e0005c4a003101003014014052280c0c1429100240b411051b07 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 910338048 1250 910336798 910336813
    0x50f04230a140705033310061b060e060601020705031506210a11010339022401030c080c01020d0302090303040f0303120515100c0c15020307061404110f01140c 70
    0xa8056100d02d100103031810469130210300d0a19503403110034480e806080d0a1103409801000e4185100101e401c8803944090208010040014129900d90cc1100c11a005214078040070400c0e050100b6162015440348280b00d805444100c1001000e42c0d000240075682c2c0c120100041c1d0050042203079524060280c03040d251324594141c0010180e540e4180907401d0010800003060044411080c0b910a00c44a10245080200514422810298084881d0700c40000401e6998084411110f110f412039108810361528140d030384280320f4071282d080480741e0250b0051007020256070b0180d0011f00015000900f9a45007946600003100c0b1099141c006078005a403600c110407448009106003600003113044400c948072044480007030b1b42d4024042409040220b2842f0841c10440501740c10b01c0503044c500c10405101c25082c0000356a500240c000b40c82d1039080c800300d0001e41000f003003a103010f16000b6204000c1014004240f0801070322000309141004440c0e024001521840e40290610185240c05003214 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 910339298 1250 910338048 910338103
    0x115030f0203030c1f18080919030b0115032f13091e0c08060a05040f0906050703051e060619120c0504081203190b0d06050f04230a14070503 62
    0x100c840f0303481310f824a04070411001000c190031f4402d0f0780c0c01c0b10088880d8401e4100280810b410f940c1c041d40006d045140031000450040d036100e40c4a041d84100b65400c001120554888801402043c40218000d0300c0114041c0741c1d9001c040e00401071000c04032a9903090710f43d05e580d4101210814040c0e10040c0c403680c4800c0000b0101e038007036145650700614001d83c1c03604000c00003c0980b0101c1c4603151084d0341d10941c50030120096001022415049102041070346003075400a005420220346240c1c490515020800501e000c10f40058040c0501814032400d100a03004901da56100300c4a0b900180481c080341200346a1441c0201100b0300340c00d0f078802d40c81d50319100c291490a043c01c0102c07680e0380710900420078030000303025030740030704041031000030561594000c08504c114141c044064011400d2504000d50b440000c5a603900171403103003400ca222a0b01e10700c4c0510306914241e1809074290007880e03442c000706140f004c0010000f4582020b031041c95664030002490010300c04515080343d001e04400920 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 910340548 1250 910339298 910339301
    0x51308060714120f0612010f0c0314010308120601031805160801140411120604060b0f01031406130b180a06050406050a06111e061006020115030f0203030c1f 69
    0x8001c00003525500f00705208140c106256401010240b444030340c5400a2255035614205016200700d002c001c118010740e0122940141128403040400300e41807050704d025808148138090f040781d400049031810715000880f4078006100240c145810103468030041c040c4c81c071921108044503440380000345210020100700110310f080075400780000e640350903406010f00302c103829400c0c0e00c0340d400308440c90343c01d20600002e403208800c03040e0080c4510070f1800f0401000501d40c444c00015004440c020a0841200011000d03200e060039901c2842600c200840e0f110b0902050810b01141e81c031034007090503040e5a01090000101d800c00c501c03c0d60051051011038525486285c002e400d00380d409002e2541001d0116070f54400c28818103081010084c040517404005216904000c5642104500403520160307980c1d0382c442040d540403014207251040090854014410022075108400c0c03440d4141d459910341840ca183c58200aa801d40401c001c0c45620050612541013400c0b1880342d032303480c081c018555910 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 910341798 1250 910340548 910340567
    0x906050f3f0a0c020712020d0602040821090a030b0603070528090501082e0c090504230a0b060c030c010e2404060c0507020d0c06180b0a0f0513080607 66
    0xd25a143c030f035810690550100e040003e5503200e410072145016584013003641c4034040a0041c002520100d00480d6007440820142c481d1204100034a108690344403080f800d6200303040383d0300da015199034030400001e03008504440c3d000900070242e41029030344001007800b218020241440114140140b079120445030084032002c0d090440c0c2c10007441d8104a511540c858101058120108850305500300305007140d10541c4641c5140d03c0140900240f2050140a8400a001e0305106a040032517080260b110900800650005046041c01c540c90310b00d4114000c00952810b00e8000d8820000010005000c000034020074090400004081e00030669881c10881c1c00d01c60003d40720300340000b0b101d0040e8051142e94001e900040c00103541d00481c24195014824018025080100002c08030b091240c0d0440e91000c8524545801078608003198880d00727005d10038011802400c90a1095601c95072040720240c0d04900da1342040c519010600300c0107074003403105501109141c0d01c0310040040782039000b80e401 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 910343048 1250 910341798 910341811
    0x15090621080f13080f03030604050703022b06350d0804150902090f0f0105010c0312020f07080c01060801360c0b0a1701060906050f3f 59
    0x16040d1aa140d034444020307205400d141c007622000810007400940308450383c0340042c08401c0844403154940b24400ba01c9810413120030348618500b20008220078005e0017102d011660051108980f0103426500c0c010b1642e8581c292046c03250b94001c042460030700c0ba81d02c081c0302e840551400320241c15805a4404600703040c0c542c40700f035030050490b05198a03000585103800c26400843e6104000b0703406d81d400024080d00c08046d41c410880f10900c000c3c081c04100c02e501940300c2d1200394a9503030f2240b00548000d0560700b400ac0c000307411031207250f0300400c080c0c2c007900801204103410703450b002403520b038182940c01c02082060340341d56a9104000c138040902c01c0703183d4000e078500354002c01001c0442d00c041d03244803002040f00c00140b401c2c945e820061083c6021016014428403141c45502849008014a0314200c00303102c0040035030004500d06028000000446080b9910b080c42d008003400918096003142098060b48669140c00c5054441603803000c100700d6a103400c0c3c2100b10200002480300560024108 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 910344298 1250 910343048 910343099
    0xb0a0f03081b12030a0902120f0c0d11030601230a0b0301050d0f02032a060f031f0302030706050c0c01080f010605310f0f06020c010305070201150906 66
    0x304002940315003075581800c451464500b80c096121405810710940c001054406a000420000181900c2c1e0010b036034103000b5660480364100340040c0e45c2e51402d108650441641c402c858021b00c80c5806a20b841c4170922400da020b009030600d1010034940700007a000543c64110307400042c51032041c000c100200384c9e40200c40c10f0f01958501a90420f03a80b10600645000c0c151181c2c5c08404e210040340d0080100740e002e41100c5c00c0c81905d1490300c1c07145841411007034100d00704158043d014030306541610b10700000040b880745541c4501c0404503100000d442051481628000c001001d81d905002070801082c06031074007030740c41035440312450410f4044480c040c140110341d02440f0380ca0b035044640a040d500036007001e40e904c210168030700c00240703d0440511095294484031500d0024090105412240d291110030202515030305168210710302400352000513440059081c1c030543c400c0e00300540225031030000052840081d42004403800c074980001510b41e0b15070104004d0300704144111000314035203205 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 910345548 1250 910344298 910344329
    0x3110f070e0a11070c14150913090f080f04060905190933030b0603030304350309071a0c030313060b0d0c061419120f06090b0a 56
    0x220310780003240181c00d4454459988983c040d0b2072800d441142c442d182c101c160100d0207542c8001c40604040c0c01000b041c040c0d60a4401d08844644030015520154001003040300c10072258000d0b4001006820300a8812520044100d80480c032958010458100340c0d2000580d92070402002400b081b041d603001c940140d02c540400000c010501400b2010b0350b44640300071407001c210301c1d0f070f040006a00601c2000a86403000e00e200031780c4001242141100e00c0744c0b40b03050f40365039078104050312800102c1d0007401c40342c2011103029440d420350001660380b100304a01c003250f4030360f00715101d00103800c2210051220303407200790b082c020429203445004840c004101e1241c0703010010b4200648034000540040002100010300c601001a01d4018010002c009020007074800c5150030306414160b254070420001c0390715100c040484c200d85030101c4100c1101c10103400f000c8942400102d0b01c070302001c0000c0d43c0c0c83e660350f90308040d209890301510006160010340402d0b44403102040150041c1d030369100807100e555490 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 910346798 1250 910345548 910345559
    0x40b09010b07020301060f18050a1509060302120d08180a1401050a14130303021b011130070c150c030b1c0c0b03041b0303080406140405070b0c030c0a03110f07 70
    0x48003542030301b02412340801d03113455401050010b0501104025103021700a031021030b050265501003012640200c0f21004080c207604481a11400303418448000140c1500c0040d00b0351101440e080c061003035101c200ca48410b2140c03141d042c021201058800943d440e6818010508018000c1c802c07460f101c0303c01c40002d420001c01c10f0540045480009060540104e01c41000000720801c0070010240103009002000203162560040c0e8061042c00d0044400441c40e440b400c169405919015801603040038010344602109807a02e500c0d0000c203d601c10200d2400c09003945250248100400440c0c07008904800300d5410001d1080801c000c10f401030761003150841c0492503092969007212110a06c05507203485500b0036800041d03080204a201d01e140c00d60000070107500242040c0f05900615040000e5200809540039044055402602d503901c6200c051025403144401841c60701101c0d0201d03440d051382d40d00500d0501061140c141c000c00e0f441b090303045000c5001e2110b442d4454188020300711450030305 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 910348048 1250 910346798 910346819
    0x304140f0f0627060406090305070b0702031b03160b0a1106060a031707050f030904060909110603070e0316060e0306130f0f0b0a0b190605040b09040b09010b07020301060f 75
    0x1840b00c03a00310004503608009009100007035250f40c1c80103808260b80303640311031010f090500c0e5440102d503280306081c00054440101e20940d416554010040e005407002500c0c800d1070303001c00c001c0d201c0d458010340c03154180044544040030010b0600c1003496896044904028001240f003510603000e45d0028000c1003e2591a44245000d0300c6c1e006e55100c60984014114034118000c036076000b8030a00c1110031425008100002a00d52414222024084c030340e110400b44d410388039807010003003040921840d81d85c1140740000c051a40440e0b01e207814000003c612000900c0d00044402c417004074410020103024bca50700100781440c4c2e071303000c1d4018050b50500d400c0d010a5101e1840000d46800c50b0f4041050400407500020b0b040d542e0864412009400c1c1034010b0001031042c0350b40301d480727210701f480d03600c0850a4030510b403011150203032901400c1c00e24060041a0a81c0141c0415034041d5458455503441d0352181c440c14042c02104080a40300c103414810b16084401903042900c20f400c215000304540d403c00c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 910349298 1250 910348048 910348057
    0x9120f02031624020309030d02030304172a0102090409060f0b040504050d0c0f0c0e07121b0e03030408060f01030c120809060d14130b0a0b0105071704080304140f0f06 73
    0x4001010f032074100030030707080b421805400368840d07050090070000c6100070360020145000740d000b4a507080204110103200e0f85c00303129000e09100900429020f421068403c422540f4564011000140c906030350400043c00716081c44900b120f8030383c1d880000d100064274031301c06c0003100b00d0f09490400c142d00740ba07209c0035901d40590f0f02c448108101a001c881c20000800082d20103194800c4010540036211803054520400880d411000504001e415005201060081d9514610303061502020380090030800c032514041802e20a07014401000005003407030080200714840e000a0448444079411460080d103a0440c0317034016210681450b0200021510302000c8070000f0000311039041d51144a0b0f42141d01501d01040c004044035050390410081132481c50385944890700c02c1248400e55501c504661080303a02403580540040d00c00e1080900094400002c00850198409124145a07413507807114038551158010311001300705220081003a0030989422840c80301c08590071001c21a030000800d405008 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 910350548 1250 910349298 910349339
    0x3c06070f120c0507080d06050405100603050601022a060f03040b070f020f0712110d05071e03110603041a0903040609060f021218031c08091504020603040309120f020316 74
    0x5c000400c40c01404c0c095100c03078000d100150042c011450b006c034011035512494890000820700307110000d00305600c0410500d105200c0805490100c170a040014070301480315019440d0481c40030002e0424204045010314840c5204030038011803403820140060a50445006d003000359406450380400c240d0f400f0030b501c41a80e81c400007011030503c241c10100c04c40e4150205258000c003102c59078106100740840d500090321000c09144e1804920010340c044e4840141c03002502807a0348096403955460318500441d041401500c0500c40d00100d8150f2024040c410b0300c03079071900d40c00050100280750304032100380000c1c03206040560040070700d0b40010703403901107449220348242d03400a01d2030010307648816001d200c05006011115401e80c401e4507060404001c18040780460080800551762410009101c1d8410500003042421600e07181c0c03d01201d604043c00031014881095400b03e101c4504100704031540b40900311002d2010202c0c014903042000c2c81d0140400700d985020f0500c03a41604103203420b8080b0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 910351798 1250 910350548 910350563
    0x5040c050f190309080c010603020a23060d020c07090b030d03111c0e030a02070e0112051b01020a060903170a02041a0f0c010213090c023c06070f120c0507 68
    0x20000c1c1c210f00411394000d004229490104806041c00d0055000605880c42611181c0c001d94540e181c511441c900d0a640100c4003047c882416650304028001d8840180c180a015003003816200c00300d8209505a04000340d02d59581502c20400d00d01044103000c4400c45080403c518250107400c11014451a00c0c43c1e0a900304440049110b1059540b12003c40001d2000782d039118001401700a44420582c89080102078103c000072480c241c840c0f07120320850b6400300081400609034031800842d040011507072030643c00392003a860089a110b01400c030b207807071007640c03071158031604125581a01c1c00080c4c2050b00305803051209010140c1940c1c0c1c0140d0540f00c007910503481740e1000a2a0b0003030300c51300607040c0c410350022814841002d004008031058420300070041c85841c01c03480d0200c1c3c3e05c0c0f2401380c20000d045040700b00c0386c0a03080e90301340c4074120f288280f40404482c5185004589081c40640d250000128580300700b4148960050341c1115880e40c0360414480010128002400760180b940c0181c51103 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 910353048 1250 910351798 910351837
    0x10e04150503060a06092009010c110301020313020301050a0b240f04240507050601270507050310091428050a0b01080c071709030a08030405030405040c050f 69
    0x4000da0340480000303000081c12039403a03251900c8108090210341c0b0958100504216840e0111b0010101c0840030f80c0c3c142a42c2c6007800480801162281c52080b800e0302c40340c4c948407950590742c40a0000f1442045001007900441810303105040c00c4032002424100d030549028110031070395a4a14a00b0211074418003d129400504014035481d40316140d5503900325880040d0018108010401654a400002040c0e14610881034803e503840c0c40f032407074001c240b03810070001400f0720000a1401c4110010a01d22001400243c600e07080c09c880d026100d01010801c04001c00880f008011400d40250450316024016081c503666400890540031b1318144860300703070503505d00151103d00782003042d041d0381034824410703810b00c039160b46e00814180c2c818500043d140c0300040c642d20302103c100c031141a885030104080074081504002e00e070f045001d00b50303854024029500082001c0c40040c1d0700540c014405180c0c3c0301d14040400c800c9a82c3d684c2c0c1d82050140500c00c05022001500079960b01c40103801004044 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 910354298 1250 910353048 910353071
    0xf0f260a061a12250e07030510091a0f0406050609280312090e06011d0a05030a14061806190912050a02061503031803101d070b0306010e04 61
    0x22591035064458011460140e03c2102040c0003030004c44032050a078500b9014000c0c1841151081d20900841c684c00c030a00b800f10703c4540c4a0f40c403007644001483d804409040d15071030802d003568150312100c2c076190640384120040b46015402609015030813901004403e01d0030021402501402001c1407080304032448502000b40c040304d0030000e456030888000c88440d100c1c0303454441002c2140401c03002401260f00452141c100400e500d0054005031250004448662440c004000784034144d1600000300800c0001c254600700170000c00c07584620900c2409881d29080240760070701c01441c000230040d1000c81e15a5580e4042040c903000070b440c020341d450314000c04680d68060070400350010408111480c042c20050341c40030103018540499800d80341d040e101d45200250308044110320981c50340080107003e040c004141290202610301400342c40760f05801c80c002004451401400859245030012800440340060011101901c014541e00f4258144100001e0400c0802c5858034000c544e031707c540c81d05 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 910355548 1250 910354298 910354331
    0x204050d06021605070b070639090e18100902181f0b0901030c020604081b0f16170d0e0907020309040e0c0102190b1f0f0f260a06 57
    0x30f0407a0044110342c0059610200890340d0f60090000341c0d8242d15081043c0321a00d400c45248501c2c45000300001000713074001102844001581005209001c00e090001518030080070340c2510688200c02401c1310000110b01d000d040552908a05000502d480d00060040e40d4007404851240c0740051042581d80d507841e001c42c88510101000406000701d10000a0244016001854414030aa0f0103000741c00408600380e95a4038107481c01810170005000040362078440c0030310700720280d130803c04450307400743c118203040d0900c0005d0440d04014219034006220900c012050022030141c240000c1c9080084028020407a084000000e4803442c100300124590601c20420ba90201c0c0d00100b04021180580300000d654101b054015400350240306510440c02010b22076004809800c448503514582c0d43c244d11002e22200115010030b803614000c00426402c22801c1d10030701404004100018140c105204640715440140801c482500351180d203404030038022035108006035004e900403d196401c42008070 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 910356798 1250 910355548 910355587
    0x50304020a0b030901051b07020a05040f0612050606041d03040605070f051516020102180405041403030f10090506011b0203070519180905190302100e030a08010602010204050d0602 79
    0x94603070b603000c020b00030b54140650009004400b130b0100c052803883c1c1d00c1d035151030b0360190407006980151001402c01490409401c490342c09d0012010024002c0e0321075240a40e500000c503825506540028208461303810503100751600e0081c0001002d49914907049030030354038499030103008100080800c200c41000300c10008070003103a43c05000e559004641c100e4592144404940e65248030141d0740d8203206644c01882282c031540b129200d044030403941141804003400014204a40044070800c0d9112404001d00c051030188100c1540741c0501e042010a4503100c1d401030300001070180c80d00050100ca60313045109120b65035403e80c200c40c0c0c00c1d0018000641800c945a11658000ea90204820240342040850b042034610460040e801401020746410440c0c2800000a00a500011984100440b00900c140314144284115400400400c1c10003055a0800f40100002d038004100c0c03900c2c0c540c001d4417850260005200843c105844c00b8006a200212036001a106560015903c2a121000c0f034400 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 910358048 1250 910356798 910356809
    0x1120c0b1602040b09090703020d1a0403050315031906050a0f0c020d020105010b090a0b0d020c01022a0d02073c030218010b0316050c0109060b24030106050304020a 72
    0x1140c845051100c08030003440581c000b244034a03c3c000702c0d0051403500c40e00c154001c01400c0300800c28281580d0038400c0d850110340381910750f4021b40e41c1c005c0342401103a07201ca209610942d21f403922420800b02000303007041d45c0564284a500051005d0101540e8000015411a04400c0200b581e4a4080b136101c024001600c4d04500d5034140404a11160b400003aa451312880642c02000180e03039071070304030501d40182c00507507a000340602000c1200401310f9010380400d10300050b005181c10000c2c2c038803e0880c0d00624004080801246665030580c80d079005103105d001424000e42002c4031554030080d01d400090160791607414202012120040044220740a071128108140002285541c5118600c03102c1d031000f240302e801941c500247c2101c052050a0480300d05e01b01050542d1200d80240d135000d144082c48808200e030503c00e03000181800d0003890314160181070000b0350b140f684420b0001a00341524001004004121000c00200e0090222411580d01e45003064680e03e8510001c4e0f0f0140665010 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 910359298 1250 910358048 910358069
    0x7150912030b01050d15060f020712030309240f050f0f040b10080604050f06010b07030207060f05220e0703020a0219020307120602190c030e131d010b040e060f01120c 73
    0x1484c1b001d2400f10446c42c1599a103844014480300d20b0304080380d82e541c4c1401210405040e01c105c000010703000382c2004200d1031189104550034000041c0c100c1514044078005848651a07115060071100c0b0f602c2803136040240030807509030601c3d1400003d0758200010340018a014a1103001550411003451075101404411003560004d0130141002c640d100036080070030a0b980241800081c6400c021411500c0b5030b40c0c15000b8061103071400703c090705c40e200c00f030840b04103110741042564523041c0914031440e41c6085401118118608040e020b0403040320041c04035041c90700c108280c1542a0f000108040c207200994a0303901040054404242402d80076813001c4070100444000e0070400c03010741c003e0030380c44d5401031030064642d4100744100c800000308a409400b00d039249a120300c00c0d042c16010350340036a01d500b00204226082d00c000076903026100c2c40012041c1d541d00c12103911071a00b4001c038003483c2c00341c00040105040ca00500c81b140c0806206203a0600e00e15400041081400c2c0c105500404941c0300303 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 910360548 1250 910359298 910359311
    0x2d02120c0a03060b0a060e1f030f0f09031211090d02062101081c1202180a1205060c071e0303090c0e010e09061012050f030d0207150912030b01050d 65
    0x7489006010044130300e03441031400310008100d0034495040041c0d80400140368034116071800c41482e200402414881e03003003585802c07661840301c526015003001301c1c0525a0010300c401b901c1c100100041c00708801007003010304040b10346010006000943d298002c00312a1200701042901c000358a03881400400580714171020a00e882c01104581c0c224101c0d48800152000c00407040700758816410a82514008035110300d00c12403d008040c0c0c003500503400c45400c155040c010140010780c9448150f071055418400307a9601200700a000d000b1180c200303110301841410400f003a91104180540140340c0c3c80c0c141d40b034100400c14103219801034008250440008012192280da400d42148001d00480002d81d9074880800c06030440010a648070710101c210401b845410402401c10f1102103000540301846507086c01d02c0108400d100401d83c41a603400016a00c251074500400c25185d1440c1c0c0205079403811419a000ca28103448490021800d4a00005c841e80c51200607030340e50044500658201c1d2a050 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 910361798 1250 910360548 910360553
    0x30f0a08041802030f041e0507152c0907052118030c0601061110022a0304080a02060d0e060a0605120f0a0f2d2d02120c0a03 55
    0x8005485114424a645140c1401a58140c1c8810340305d00d060105c0c020001404240403841c90380036240345007078055404541c2e40340c02d40741070056000091068134030051864216000000643d918002c3c004c141c00121a208480002c40c1107043e105000b06c04003400100b5061041c0c04580c4a140c0002c080f00500381e8400300c1100d83c81088500d44030403840c84c001203e01c0d400010a441c00090850001c200316820024201c801c0da10300d1241052038440c003111544802107500183c10341d130220f5280891810720b00b20000035a02d60701554442d50b80c02c1000180311408000c250104480d406560706542c420040300a5002030400012040e01401502d0a0010029254100d0021180b089074a11601e0003020850764507041c00c01005031456004000c410700048401c080b511802d4045d28840143c0c00800e01e03807400c807001c000d40804080b1001c56494040040304200050321848142c503d4031002c0910303049001078541d6040103481010306c40740645484c04204182040d48002812041e005035891 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 910363048 1250 910361798 910361813
    0xc03021309060e0606030c07110303192c0a09271202060f060310050603010e030a0f08090313090504050f010c0e210d08101d0405240c09030f0a 63
    0xf80079000c0500707000d02c003189552410310280c9000301503207811070380703001c5540d0b0700d608400012881e80c1d0740501042c0700d071802b0401c0c240c1402855038081e84409680c0c500c0a0103030600100e0911b50080c5465650704010b51603180c6078040c2c0b0603601e4080c40000ea00d100c004141c40009490030480000d0400844d03035204009000c1000034401c1c486408a0312152502540810125811107020350954444000e200000c201900440d0308890050300018000c1c403140c882d00d0540d8800303190b00c40411401498040040e40c01154140d011101c3c0c8065400d200400c0034240d28003556100ba10040c42d2104080f40c1805014440c280051410030020094040880e00141c03075000000603c4c1d21a200100c0c0007054050034401c1c003220000b081c4050010900300038001c2c0c0e50708038041c00802a4400c0c0c01c0010a030b03072449001511030082d20324501e002c02e141c0ba203400361422030100308a58030041c4100c1c0c603001c01900d080c0c100750000f0305815000c0e2a1400440800d2034190019900b154510501c2d401d0b800b0300c2540e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 910364298 1250 910363048 910363061
    0x7081e0711060601080c1c0f0501090b030f120927190f1e0507201c1d0603130503040b03060a0602030c1207080d0f0b010305010f0b0306040c03021309 66
    0x1404240d669907543c0c0401591340c10000c4030100400c0208029043c0364814080007029107200400c00041d03100080b00e024800c0f100700360807407600180d8030003001010f85010080c160130610703410014500c4c0c102002d01c0540c24015044417502031140c81007846a0b0710226502c5942ea41040030f19a0340c1c0380340c4440d181d071820382c18031030015085180141d4416080303624008c100c00081e80360942d0020043c0ca41c01e8400401c4001d12400401c0052182d0014040700013080c2409444c004008002d012042204070042d03040e0304040350184011100710000500c031390050a51400c01c200d41c003e880c0d95911080000404803090010454000000e01041901e00c1102860054a0a039803526a03540c440381d05980e85d110352607a01d0015400200303940c0e186603000001340309044c801d441c1641440c44200c0c0c642e00742d4100303c080c01030058840c0c0740a86156494490790f801025103c41d4045401c0c501988039840344409401c00b80120345840703c01c1d481e640a501115078001404d10300d403100350f50791040040100300 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 910365548 1250 910364298 910364327
    0x7061b030501141c0b06040b0a060f02100203040218040201020c0307060306031703010602190305160f061a0a0303030f02070f0803071101110910030f1a030f0706050307081e07 77
    0x1d8907803007110355013400090688551a01d03105010700e500c03181c0f01c48944030002007081e03500ca80c580e15014813644601c0500c0c00100310035211601c02042d05200a4140800a51202c3c0240d00c10720400025075190380d8100408034403500050031a441d00d000403803c098900c01710341c1e018854510001140c42d0325074401d1007128001d088622104002c01c542c1c0b544c2d84420301c92240160f12a00c14080301460041800050f40d109060040c5841d8002c20300b0300c829004040240c410090748001f043c1441540d0243c0d0b800413601c41c290b01403d000d034000007810b150450002030b04040d83c46241001100159040fa40b446d078001113a031a99a501d450800f041d503104495500014401c00300c0e41010800500800d00c40c081c1c40030083d07042c2404681032140c400880d20f046c1c000c041d2a01610200c20305030f44034070b400311017054072002d500c181444241881e1208102841000b9841114200102540030b0b083d0380e08030131036207404070081e00c402a40d6900c1060300b01c0d00b0081d1030000b100340b202c1a900b000440c0060312 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 910366798 1250 910365548 910365569
    0x60316120c08062505070203061905070e10030b0103020d110a1407020312090303280e0f03030412020d050d0e0108061903060f110f040e010e100b07061b030501 70
    0x58035446030750380714070080d1348203070b50303035403038030341d02d0307104000e5002008450b0401c1c3c40c1c03e034100700032600020301d13210003a5446415110941c0160b5040d8031300d4041c50341c0c044c6803420103070b01420721075001c10384d01075502c3c0340d080815995000300c80843e03200e03804a60711160328200a1040309002002c030907240d4004c500c15004940c080c509203124030183c6042d03034440e03a00200505500c0c3d61b11031540d025035210445243d891b0204121201d003c020804010404d80051020203514901c031000c00f07090070650088551144a02c0840c12040759000400c031406d5401080408012010510110b19000300e410802040350040008a4401c1544200d210b000044240e82c1c042c01a12213000340310032180f502c0745405502207996000c1c00815815000b45030070070301128000a02c018a010b01d0071007900590b914024004000904001c60a10070303001c10302400031304940d0641c0d03042401c8034510681a034403070459032043c0031995109018503680308220146c0342480c901450100c40a00030020442409843c0007031 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 910368048 1250 910366798 910366823
    0x21020c0d050601120807050d0c1104020414040f09021f030f02280e12060a05090111071b0306060909060c08011419050a03030207080601060c030f0806031612 69
    0x2480d103840603000058000018002990030118890401490442c003503a01c0f4804020020006004200c0c00345420007076910700e2416201c1e4544030b00c1483d1030003015445240140b00030f00502814400900c0014011200020701130300e00d42c440c2c00074101d90403007e0340c0028001e072410b982c1506040401400ba0b60b6550070040b91380c0a6a8900890094100c09000109040c030281090b07071541c01100340c864403a0600407811000e600004050801c200011070198002d0300034401380015038054136800104140007803080a10a850321915070241030740c05400481c07400d0b644880d01c070070404028007444d00302d01d0a08c84035466920341c0e0047c2c08020b42c1150454a01003500d10301600c60064103041c0c0300a82800405540c88500b00200c905810481395004982181d000580b42d0b81c0d8122000194482e03000740c082145080081820300905900c54820312180c01040f00c0006d40c4510144540b04036403c105945440b5500440d07d84490409010100f000454012418080030740b011080c040c8202c9018408 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 910369298 1250 910368048 910368073
    0x281502041d01120c12031110060503010b2407031419120b1e0a0f0e07090819060203041103070b0904180b01090207020607120309110f1e030106032102 66
    0x24403040c054044d0540741e03208400d22040080d001c618088502a1408400420f40400c0442c2040003403406241801d5840f54108140c0c10203008d092040e174411101d005074410840350b0b0307907071400980a4100c000c0200003068020980075104240e5080001000141c5641c0301c451580c1d040540d908003000801c02180a295288150b40500303001c8000142c05846041c9240301c42c00d000304601c4800c1c1c1d81c407100c0a1300100e5001e8101030720400a1248900681c844d00b800340000c0c0514003070741c0021141d034110800c0201040040100500c105502c983e005940340c6d501d0030705050010301070100952600946a0024581034020017405841d50200da081044010441010b0000444080010720703003041c2c400100594003140d400340c50714500180040b460008141d4030798022902c07807220400860340c0d070142103080c400e07400301000300844140e80030820003800070006486d82042000f4080d000c0c03440b41103190140c50a40260009651041000d648a002880406002a09001c203040103100c0c658542c00c4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 910370548 1250 910369298 910369319
    0x200703080114060a140913050a0c031d0a03050f04150908010c05040806041e0b0c030a1107050a0b0709170a0501050606040b1801030209120606030609281502041d01 72
    0x11703210380e81071103218210003c042c1c1281d04401d60058800c188018174a0700c500a0502c11503c040c4001a83d0400310b001030210384228002100308102101e01c1034a041c1c000442030707081134044c00d000f81c884002c803444c00321600c10758121055540d0b07102d005c0380740107410000f0002a148008020701040300000030480300c5008074440d11607154000004100400d12500c6441130205a85600340303000e15039522201d48020064130040022034000041024003911481134a220402c00d0003503a140c50340a8540c20b40d6801c15100c0646085d40c404041040c4500904040000741005c12500340c2044d001b1007000c1d26400111000d6a041d400e10300001d64600d004c1080b5026102072008ca0340c03c1407654142c1c07200007010b100040d4180b690822072100242d8429114004c00d8402d07400610040c0740c10303810305042210242009109900a110000240021048888904020301102e4056800b181801c18401c0311800110211610004010880c207051254a9842e014211800d00e12660f80306001c16 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 910371798 1250 910370548 910370557
    0xe091f030b091203010608040c080106151101201c0e030f030403030b031f0e01090b06100c120201050906010e011a0f090316091d030405010320070308011406 69
    0x15404500110030310004111000c038640104840086940501c409101c180d5140e00a0300810f0208403031070208801c109490684101905418000b4450245891400002c180ca0518128140807035600e03a107501100035031011084c4000c0d244a8115003164654a190550021610f14064100c1d60048449441940180c1c0d4070511000e005520705139040c2100320150700090b0049080545411501d41556004c00122107212804050761088030b940340d00e20400c0350020740028403583d06242200005c588402103103a4045400d070b810ba210543c200c5002c0300c6200d04440014003200042110340c0d400c940c150701444c4550488001c85032966202c0f0444140904240711303000c07030303505401203014200c04280c01600442a5040c4150304000e076000019041210b0320081850300f089048007080301c894903001d4107060042400c0803407100c001c0e00d500f45440740305a004050525440d118508089852a03400a403101c0100321170540341d0305c40b0f24005261030000c0c81600d460000d8545613003203910380001180c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 910373048 1250 910371798 910371841
    0x90b0c070501030905030d0912120b01090b090a05090f010e180c0d060e0f150c0a0509040207050a02150309070b0a1704110d031e092111040c0e09 64
    0x106803032494a001140a041102c20444250100303014286240182c0e014109100b4400c281c564014515408001c02200c050781040c02c240e0f00300b048203403103640c0081036001a11078441007103544a407803c000c1481809241d010b9a0002140f4080144443d46200c00300c0c107990000c04c012481c0c0d103d031821903c0c4504007032044051a08009103200003446c1200442d40313840e01c20700340407607da000c00c02c200381400310848491f140e6410500d201c03101a014940384560201410307901c40e050043d41c110041490046201990286900003014020f000d01042480c0b0401ea0061400715844010740d001046a0403e44008105114404010445581040c2500d2010020390f56051611a030a03090310351008000d402a10300b0300c0d00c42d1101e04286c4036071207400485c034042e4840d5941d0115040b403000312000c459030f08000300400e00780e041c000c0c3d8002d419481c958040514212a0201d9907040140040c48016006076000b071038041c219007000d4000f480340e481711104485a420550700c485004542c0d07450310408 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 910374298 1250 910373048 910373053
    0x603120c0c0b0d0b1c0c0503060705091e3303060d150905120a080c07080717040803120a0c0c2d0507142707300c090b0c 53
    0x1404031100d8800540001c0f50045804601080840c0224440743d0102201303564428081d140c6200340a20036158000030002617004244038541101d008010b4010042e040d813041400d4106004160507600c40004000c00080c02e0b40c1509281b072100c01030108036040c440c2d00c0201c1426140341400c001c1130560744516006070140d042081d007680e801c400d11410a0305000c04d6035940c1c20880101c1c804004500b91041c1901020303550f00f04015000e00403050080102030b51030801c00401e40000ca281082c2c1b1000c562108003c03488414002052116004980041c211407101090b004111011680000c0c040d0400039000c00056001d0181210034031400308024000580048002d021403031149144038110802c01441c80850007107588984c207084066110404841841c0d03c1000036103055608a02d40b00c071500003214000f441940304e0100074200600000c00d00c07429107043e000c3c500d800c52000c00064940c004241c44501a00c888500500c01c1c014400001404240041100101e04080b41c02c81d6450b51b00 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 910375548 1250 910374298 910374323
    0x3011214071d0c04300b1f090917030601110d050a0f1d100201020f1b06060d1a0408070506070206160c020d0803060a0b07060504060b2b020a0f08010603120c 69
    0x41701c050008503501003800100c0c40c220740030080f030b81d80b16031507001e513804500084e003481030b502c883c0d0035502d019003152500c031b0701c0d00c03104800007a14220f2000810411030540d5403a503503088010fa6850603018918000ba0003251031500c0c406a1041c001c0c203284000c0d46803025500364101c011122040c400000e4040b030032122045c9044d03031800c0c0c07003400c481d032a1620002d854540241c4031046682c2018a8000b4581140000900040345c14802117a200c4410385074048450156117501c02c0501880044282120702e0102050510a0101c100d9200c0c640142c1110b4482c1401d0000a5944900300c1d4180b000790814100743c10014400c9030480c500e1900204140314540494032400e1580e130014040c250310040e002d00005610260f003016022180c002d490000d003134074150401e0415150b6001d225881045c0034109017400c4030303900b00c0840b01c441502d18a84000007091000c14407216168010b201d028403120400510204150081c1c41500d2140204494502c003001017540e42003407181c00107041800021 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 910376798 1250 910375548 910375589
    0x14220f140705030a1508100e010c021204030b060303071e0c050a050a1a0d0903020607090b03010f0b0a030e030d0605030f0105040b180c060403030512060d050303011214071d0c04 78
    0xc0010032001d06001150b05501c6d502d80c1e24a103003024100d07850020380d403180c061300c8c0b01d0712080c0314054003803120380040c0c040341c41e4000c036010440c403a6020080c43d84a80d1000705e83c9a0f2410400c0e6100c0c1c81d4004441e5002100071030342c05a43c1c180d1301008640881c0301c0310f0086086c3c00c002c5940d030100c84014101d040c1550409100c00b03990303d00031004041590051080094011507400790044060094001d010b440c102008001e0001c0c0b083c1d00036102e104c20400040003111800100712040b911404800b60311000d004004030003034410403640c800300d40310110b00c400d082c6541e9409a01194012001c42e50000310b80d0b00501d007a00c50440b006009141c0d868001030510301724902c40034030184501c09450b0b038254080c000840c4d0703810035007003980003c0c00401d0040f00e940d00304d20460340090003290030b6249120700b075542c25500e03c414020f01189550003a185420080b0040c20100d51480110a889089071190a030301500551038140d11100d03c00200811540c103c148219019600c00000c10302180c180b58 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 910378048 1250 910376798 910376801
    0x120903110c0121020d0b06220e0408121314281e020312041d010501030207050a030302090d051f0b090f010e06120d020a0203010e01060f14220f140705030a 68
    0x11030a445c034242c441504c0c888550f18080240b140c0180f084610502450044821400a1513a082050200403510a0001089001094550808144000503100d54440d0111000740c0300111000740b0341162182c48015000b404210454000b00c044601c4480e28140d03074074480b0700d85254401601c45121401c4140508540c0161131081c0b0740003904442c0e03400a0030f1b502c3c582541c825403108a036080880151580c6200210301d20b80180401d280540c20805039440e42034503450708500040a055000460002d50388811914440242d0420300303603130f14409581441480e0001c0083c541c0c87c20740c42c191856800c0d24044d41050301911214014240c80d038205050505411006807440b503002185110b81007034154100f00301c0e40d10865550150054180c02e00c1407500351240b00c40c000105074100300080c807400e0141c0a0940c22940c01030041220b0901e54004a800c65034048515110589288d00082840e003081d00101c0d900719032030f44208803402e04090300e00f0000300b00380e58100028204001003426628507 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 910379298 1250 910378048 910378057
    0x1104030b060f0a05120604050c0a05011d031011130f0e070e130f1d060108030f030a02040902070b0f0f01030308040809030705040c020d09150c03050703120903110c012102 75
    0x190100d03d1007074590340043c10000740285514181d0344083d0030001000388c1406a410401c20aa600841a60030700001800e0040c074400e89414001e0120107006060b68100314400c0350080d200801c010240003010900020740c00801081c07000e503100840010f41d41c03428201d110458080316000d65040e04c071400100d61510345490503661109800403c2180a003091180940c1140400070000e41c2079001d4020310427101c01403d5a5070240c010f000104850240071045866003c02c082001d581c0e41e680101010081c0200d40014400d24404506c0b241000b14110340700d80529907004844840380e942c2c084a20000c0400d000003000115038202040018840d440501020b580080079a5941c3c2c0e200c0c030120f4200c50611080800581c00380d0100d0300303460740000405019050041e001c11051002c40c2d405003d100c02e400d00201008400280c2000b810702c104140380c02c01c403c0c03040034051f411660400409081103074442c0703440c602580d44101055801400312083d00e04890fa5480c1c001c00240007040c009400 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 910380548 1250 910379298 910379329
    0x9130204030209010906032310090203030c0f010b0102060109180210050d1104050f0405011505030603072301090506030618090c0301050a09030e1504030b15060a020c041104030b06 79
    0x40038400803005945140c0401d01070002c00400081083c80e6080603100d040f20489035030b4404c1d019028090394800e0216102c090080311a90200340030006202091652041c0104011180100d446003490400190000391030801e00f40d084071401c0c0d80703801c5510b00704c80040c4000520702e52910440c0d401410019440c00125070642025424400d1420004045d00c080064071002c0c80c01c00a41030106140c01c119907046d256090380c04000310b604102c8400d0000001c2c0300300b1400e1141c04800a60a0350b8104a594040e00c0c10b42c1386004000400c81b884440b500b402603c01c1e01094140b80d0102d071504105042c2d84c421740c002041d803010b420103c00e40005004014011078254003489861103500d85003401868000c0c140d9030400a903d100300c6c04d0080c0110500c005251161140b090039150120b0f1800c1520180e80d080850030000c0c0d10b54490b280304000e11141600d80000d800720f00600c05035008203a0440810042c2e60502841d0f040223100940d5201d180401850860303020041449401c250044c0981d002 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 910381798 1250 910380548 910380551
    0x206072c0a08031b070902040803071127010501020727090c0902132315160c0e0406050c03010612090c091e0b01020c010c0f0c030210021e060c0913 65
    0x16140c000043c02d40d8080d00180882c1080d04894092400c8100040c000401405c04114201130170185007036141e215101014241c0383c110000c1c1e24a035a21403c101480003003210290400c10340004070b03c841060300f4802d0741e0160081d0040011440c94003441004080e8030110414210700f0200c1c2c5680c004c0004810980d003d0015070408202c4149070320040c91001d0700c070307018460520b2402201c044202080c50344100760503d607900030441512690001a011000c0c060000d44903094585010040110000050800e084518001601d2400c1e0314a0500450048005000075900d0080f580780390711003841030000180c040510070000c6100b552183d4803081c410300c0d605205513070325146a01a6070103224070f007078a44090070648000c4c3c00684241c1d10311400a0001e0804488036000107400c0c1451000003070b1040340007222800821111051078006103900820710106032942030390003940c82c021801c130040c54040c001b030742c0c0d030300385100003440c1e882040b030001070303c1c50700c10074006200a8400c80314000240340d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 910383048 1250 910381798 910381819
    0x1052b0608030405040e0115050108070e0306040c1e05010e010509060712020c03100b0f090a0216060515150901030207150908090a051806090912030a0c0206072c 71
    0x42401900c00401c605001162100c3c00c1000b00310490300024041c1146a1410f41110012840200b084040b6282420085500c0d1340d400d00c150b4511038482c034004d6150280c10108002c012100901106450985501078480e98507080640742005580c00b03124041512500c0384007140d03104600078100180080d00d45400c120040e62a00e90b03200d1211511301c090f81000c0e090700c5440c03e0420035140e602109805c140900d1070940701041410107001d410368061665040020540703840d90b01120700c940042c0205200d4080e0a0030500c00800e4191504001064240b007414514600103410310b410b8400011000d180c03501620054000394804201240c880044282c24206a0102e1040285c40e42c020031085654403d00d04c1007009804540c0c100c02d04c19825031980440710290702000300c1e8440000d94010350b142d190824440c0c900140d1112141030703374900108000c205601e030340224403c02001d03003c40d01680c0b241041500c0041e8403100550104801c0c02c90014034014441071400183d50150100c40807 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 910384298 1250 910383048 910383127
    0x10b030a05010b030d090f0605090d08071b050604060206010918020913021305070824102303040203101a0a0303030203040b0106091a090613080609060a0b0105 70
    0x410340c4031101a075142c3d650720601c00032400c0601c00590161030300d1405903000b034100003003490303045040d0140d070040040c0859054030b99110010b14098240d0062442c90b00c850461400081e95044816401c200105c10800080c01d400c00c403042d182918090340141c82181c0c01d000050000307009000f26031880505220100015032105a9898011403080bc00d00c28140d8980c0140443c04d5150940c0845081c5800d0412007143e901000080d000b111400200c50404030388038280c4030803085840340356400b0f07440e1218000c8098102640030040e004401c007034100003c0c5100d5071480385c00704850207500340c1c10812121500c24805e0303010b080004c240854030008440940085190510242c108402199001040c4030901c030300150703d2801005e00340340528006082c0005030b02c8203850002d5440704082d0100700c02c0c01d5950341000743c900044003051f20003406680c0c0d046583c1e5404041d5941d111501400300441c464542c540185c0d490005c0c10707182d130f914000642322008108144280040038485c601100c4028 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 910385548 1250 910384298 910384303
    0x81b040f020a0503090607020601060804020f180a0b011206030308012606010b0711100e040908090904050319050a2f0f0c1203040f140105220e06120601090509010b03 73
    0x102d4070302e940c0d415440345090640f49103001c801405d00001c1d1751041e00100701071540602c0c0320303900540c103440340c018035805500403925040c3c1e1101a21400c1901c00d04021000460380e0140c4114002660b4150a40001141200c12a0006d000c007400040703090006002c08902d0031080110800409407500b00d14410313040071130400d082a0001454040f0014001c400c2c4164a06c0000007010308641c54000c2d01c1aa100250201811200301c82c05580c40e1010304051144000070b580182c0d9000d081036a252929141c8240ca031f50140d1243ca10110361000c56842d02446401a9424000da0303031102035130345d48a0f03001e0881c1ea40600f607640001665800402d500e075030003408401105116000109010f01380780003000000d0690000d00b143c2544240710402031241c1c2d035038414007260b1101c203e00703840c2c80102d001218944a030810020140e00c1c140e10041005000c404281300702c43c003018030f1b1042a142c00f820454000074601d800c0115034030000040c001d02000d603101036003122440d40001100401080400d0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 910386798 1250 910385548 910385557
    0x507030303050604060e10170c1e10080906310c090b01021b0d020a0b07030207090623011134120206040314160e1b04081b040f02 57
    0x380000d490303800b406500d042c01d003d000054081c42000e8982c1d480c001d808204211450710800542030705d40408040d00c1041404050909000500001c0701c452103c88102460070341d80c0765503802070102c242c2441d6001d106030303102406800d0403c094690742d15803100f83d92040041c0e036403218074100200d01c52521301c8426003414080354450b00d404150103141401403000c65401c0300149040d500b255031810104900390108a4000d00110380c50f614410840c00032520f508550740003034160300070020303081c000e050b00090520111080280103024054039505034856483e02803c05080885500b821000258001c403200e0350701c5403803441144e60021072941c0690100c40000901021401d00403441c04c10000c2201c1084007038109460302450454032070b1302041081c411440090880d8842c401000c0d81c8000500c11b640e40c002c41b10920003541a101e10005903c0302055036410010100313600c03c03980d80300140043d00c0c12151007102034401003405c0060801000c040c10708166102d82d49003811001400c2c0d034805807 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 910388048 1250 910386798 910386803
    0x60f0e100b09010918090b090a0b1012030305041a01060c061406090c0a02010204030f03030b011d0312090307030210050a0815150a17070f090e0f13050a050703 70
    0x1290504080c6080c161103000d40d005040e8a07001046401100d90b00103c40208449080c0246440411030080c0c1d0340051241480c0103040a41d01004c7c01580d4100007503e412460007803c58100c1903c03410000c648181c1c1600c50300c24002100c650080210303009074082d80e170050003044c001c4500d0340c0804a030030000c502600f00d040400c0d801040c010a110581c841c0320403840840c07104814509221f000221000c2e0014200d24100c2400150b2480c1c0707a1003074040c3d07001581e111003040c800c0703809881c001e4054150512418001001000c181241d10541d1380c9481c402c0c480900a4401c00c80000740c0c8016a600c00449190540b2802c0400001038641445034102d40c103035965603a0310f0b41401c243c010100d400141039005100341d41420b80a6036038902c1d20948440300d650342060365030300100700240c1e8580142e2000d44030405055041040307542c0c000064052126a81c2d40341b5040a847d01407941070403400fa41c0c1c108500c10340d00005261600342181a02e0228059800c940482003166607071890440340303030002c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 910389298 1250 910388048 910388069
    0x50a0309020907080a060e091011070c030605011809020f12010e030316021c12090c0b07051011070302030306120705061b060604062103050d090f150c140a03060f 71
    0x70002440c52031b20a02014268500c00072070ba504062040300da460701052400803009a0b58195046600d0600089460456000a4090340c10b0b68a0a04c00b0050109200384841c54680340d5071045451028403034038000355402054984210501000c0c0560f510301a5454406076584101040c03400c0c004002862180c991011011752041d41000024104955908907a44801060340c105016079081010b50b0b84460340d0700c1c00090450140d08050b0744454507940012480500001ea0505018010591415220142c08188201000d10403d80c94500c42c0201c05401600140003140040c030b0b1070320001c803041241c1c01c221007a080e203070400500e0503071001000000550030192405103401d4103000c00c42d03000c04112420456585420703910282c130f0100070408403110003290081d404141c026401e45003a00c0c1510410408544c061a000308188c151a1058402c01ca4480c1c488809110b00d000716020b00b50740790b0b1044141e602c401018006070b0048811001031584807040841c0d40046030b0140401001d079400e0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 910390548 1250 910389298 910389301
    0x120e0a0f1a190504111507030201060b090105090d02030c04110c0c010f0507060209010c05010e010905120c0d051e1629150109031a0f10080a0201050a030902090708 72
    0x401c040c51a07042081807449140c00410400c1c1c04003040020b5005407061400814256100d01e4040704d0707892042922a03100281300031450a1203800c1c0b01900f0664881d030020807066440321080510350051000d01c500148040241101504040110003880d0344064216882c0d0035901d0f00140560301c010b600703c141944040b4001000c90410440311920101c01c0c00c25041501ca0004010003900c01e14802810141d00000c0ca41a1648500c503161a444e400600030000100e1040c900c1d401f038408050155854481e0050303000503003a00c82c0071518028005001000020b912220940740d681010140c01c0c6404418000210190310000c000c06540d541d42001007030702902803410010251100d180c41d0403c205810b84006c0300303a201c4c1074032904000d040c03450101100d200001217503d103445810007400b507501c00ba40740301101c0d1944c1c4a04d004002c0d40300400d4895507540b6058641850038855852103502910a4001550040000f003507000c4540c17a0102e01c034103c1d41c01145400344150f0312a00010b21040 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 910391798 1250 910390548 910390553
    0x140d0c0b07081201060f05180f10081008030f09040510030b0a020d0f090c0303080c090a262a062802060a0212150604150801030c091b120e0a0f 63
    0x198102e024240324200403071b0700441c40800a20070b0264403908a100c0c420007a0505507680c1e00e8070210000c4000500c860034458290310300034903aa00c242e401c154904400e5001041824011040c2c0d8003180403100400d04282d5010108000341002409001c0b4650000c1c501001040f802581644581d6011101607544e5005015000890b2041d4126a14940c64205c001d8001646178111004072038040c9803040154458041d013000030b214085880307501c000e08240005469000300300062a60300d071401c2c1e88111119544006032200c02c4031307c2d0459401240c0c0042e4904581e001540b064061010b449941030800c06103614402803080039422103d101030842c4c07100b42c0d69040010076440320f07090341d09505240d01c104200f503031007401070801008184801c4501210340c8840f0152401041c10720000c0080640d04440503041750020300003501c40001800d804074603000380d030285400403440550b83c4042011700580480301404202c1c0007420540d21902c2440c0481270800888641d0f0340205000540c00d0340d1032 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 910393048 1250 910391798 910391827
    0x31e111006060e09010302010c060b060c0313030c060f080c0f041502030d0f0614060904090f0b0f0108011104052206060f260612010e06040c0816140d0c0b0708 70
    0x11000c3d88078101d81001400181d03031248400b240d15510580216840350fa0f04009200d078041e5032107c452030b01c4041b40c0704100c100003d508a04403406100804d18203a02c0f650210b40c022851000c110208150001180584511600904030740f4501c1880908080c4ca41001168480c0d014107400010707400030902c00301070701403031050110711000d1010803c4541c1c44e28210000704140b00d03c3c403a01c0740002268450040e10349400c040c11460344080120800c108a244c030a0030b604040d1007030410f01440300e00210b6940ba051044034440d03801c3c4210981080c5c13411703040101c3c090002c00713489411554030042c0d0017103041a00400b0040c080640702c5842c1022045d5000700b54410354400805c14407030201d12040c05c10400c101c07007034010b039090701c0703071030381400d90849441c0500328405000c0424810001084140110600c1e0041a0b900810a0360a108001c00407a003020b9a5405111802020100001054580401440140d520034882090310799039501a41038540c11010b0140d4003e1300002d400031090150 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 910394298 1250 910393048 910393067
    0x4030f12080103110609010311030406020705070b090f090601021c080910180210180312030f02180f030703050f03030702011103190506040209040507030b030c040603031e11100606 79
    0x21440d02103010b614585503440c861142c82ea04030702981c0c1c001001c10f02c0c0e0b40702c2e03000640810098101d4075640d043c9440e00e08000d5029940541d0300d801004030204103203829500319a210600100011000b11003c8104000040046c2416041d0310070580c0000d0000340c001c080074200a010f4850780f4151610244a0f8100082c44040d295000e1500380400c4032980300341d001d20304083c1c041d04c0240079004d030040241c07120402c10185102142441d0400001c201035035203c5039504015076014030260f038460b2035410070fa01030484140c0d5629080c0128500c4c6081100052506400040449503080c1e903070b80f9201e04222689600c8403a0350000810424071a409000b0032001005000384249185040202c202000d280c40f140d140c4a140c0300c101040312580c5a405032181144003e03c104224281f070b000207801021810301250003801115510840e07441d041c8121000c482c0c054491629128a485841c5040d4400512010602519041c51101090b080100300d07442c140c1c03260002602810a20040d000e1030a = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 910395548 1250 910394298 910394333
    0xe0f0c21060906010c051203130503040e06180c03071d041401081c02060a0e010902060d05060f0a151404170f01150506072030032104110604030f 64
    0x4549080b81c0c0000d03c001841c4003503c5c40c1101c03194232612811500e00211140c000040c0041c1710105012803100c00410b0058050b9070b084400c180ca00e01c280718a081c3c003050494800e1260f40302400050719142c0a40320710302c520203440e04403800e43c154690024048074001001101038114540040c80304007405c01220075045205400500009481c0038001e607105001006401490744401d204070540d40c007508900003599006004903150300d02d0090784001014226a110310031000044510b145050100080003a10030b54420800e0510b0445800d40d034114840551410800e02003200180910b141d0a02c1084590300b90080d003802002606418252000c050407071802d0001882c0801c007a0750703800c0c21102a250300424200840004002500140e4103140c60355411555541110808070406100781c0074514040c8403002c0f9105080034000d650380516482400d904034a001007582d65040020f05541c041c0c4208107036400c44500402040054200d41e00417105810b44402d02c804000c903e0b40140307085038 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 910396798 1250 910395548 910395557
    0x902040f03050f01020f03012105030708091c050c04020702010c020402030a0b1905090f0601020a050708011b020102070f2406091b020a240b040905070f0b03010e0f0c2106090601 78
    0x2c0c04041040d60078801807040c1c0c03120a60083c140c0c1c91003000031606c1c5412a401002f81c9032503039a5402c0101080c0e0180c6801441103084250401c5149102c014403000f41e03030020f00410600c1a080180300007503000100603418014003642c0c2c0e0006030b0f00c0d400158485c8034085008603016220700c0034003079000030489140312036050740344062100d0b07150100a00d900034200c204240c42a150302006070704010044201600500500d0004034000c801500a02511850b005a03c1c0ea0381300d10440407400c074041c400c4001c0c80c8160440e0a10041403002210016100701b0380307582da4103042c4004050049551a9200c40001f6403503000034580d00045a102100c40c42032400a401000d5480d0303113030900c00090440e04c40400101219075150840c49030300071034001001803c00c004a01c940d040c590b60f0b401143c4522b10540205642c045040c0c10b14205a90480303010f85901c41043e2584030f503003070301400c00030121600454184040c25502e80c140764034002c0340c241404036124a04001040c081390711401440343d810b02 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 910398048 1250 910396798 910396807
    0xf27060c060402060315030d0305040b010b0708180103270303060b090d2a03150f02130311040b0a0e0915010b0a0c0212060408030901141306150902040f03050f0102 72
    0x114001c41c54540c0b095040750038a5403652004901400780b100c00c03030030681511903046821034035038040d4410741c02540520b6041109aa980403000c040b4482e8840042000c0d90521441203a030301e11006801e01c0110504001c0380710321580c1e074050305100c920f4041c00e070340d9881007400106140d01440b03900c0107408943c03509407510034014045901a41c0f00384c0c006083d10048031080e072a5940710144001c040d440700024907019a079a0401e4042d2521008240480910300790303498800f200e192080790170210b02c2d1845800428590381f20005005a24859540c21544a0340316403d40e5540c510040c014042e0b00c00100e1440c140104c0d191320388200ea10300e55024241d0840180324008410050f01e195a42901c0c02e100000d9251000c1503032500a0034001010f441400e0600c402c0140302d0025512804000c0d00130030812020121880c880c0c0810395800309038411001000300480e0703550b0008141600c03400c03030a0f09e44c00e654807040030890307005501140380e040c1d481e041032080145c28803400c0d060080b02c10096080 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 910399298 1250 910398048 910398067
    0xc1221020319120f0c0504051207080c10020115090c1101050408030612031e22060504062607090612090206180a0b070303320103030f03020f2706 64
    0x2c0280001840c400e0040914880044616582098100301c10190007403000201c41c071380140c01c50b0814060700e84140d08440c455040040000b0718001103805000050940c82860383c03d0060900805a503101155212944049140320703610549004110300040001d68240f591070060401810403c1c0081c1e40e410242844003050422050317981000d401c0354481c0d2401c25200c4101c1ca1441030340c4441c5070740d00b1015894102c140d610030245c10b81440d42040e03100803000d120361a0408034464000e0b000465000e00c01804040d126030380c46020b103070001c20100002c4100d10b0212425000488541c030002c3e842070b805020040e4840041c07481385444010034450403100313a00080c0c0034040c490004c0030b1030903a889003041640c1c0d4590010010481101c1c2182c1e40c0743d543c24024064098480c240d4181c20f84600b1841002411102d9132080150a0288540c81c2c0d0a654049542500800b05842016002d01200d54900c0a1000912859200024500f81d48642c004125480b6104030000f610495060201d0102c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 910400548 1250 910399298 910399327
    0x70c0b0705070b0f1f0803030402090907031208060109090905161a090d05011e020c0705012109021917070902071e03020a0c03111e030a0209040c12210203 68
    0x81000c05406890669a24000f4009902100003a21707843c0040c501e00c00500c0d42000710003140603a000750388444566a0b19050107985040c81d1100900240c42d646102e50880d1107040f6240c0c0091052528620007507581102c2c005481841d041500c1c1c03500b20306800c07468141c1981a160050000c0d0180d030103218250554003080d801011500380c0101c0103041c2920420000798404805841c07a0460055200c2c0341c914220700039000784150a1403407084640c0464950b0269480c900071010030380142104000850500d4040c040b0a601244c1280341541c445d40b10003d048201d501400d101d980c400d080320329a4010303514060040c0c0c414140c02388100946000318241c08805410111811703075081400383c83c0d1400300d14142c000d41d07016188014038070011080041405001c014440115070208041c50341ca5140c021404c21588480da05900c0100c0e8840181062000c1d2944140520a00040250366031000c8000c0c500c0302900300c0313405100d614420308012150038030096600485c0300030350400055034120003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 910401798 1250 910400548 910400551
    0x3070b190c17073207052a030105063304060f09090b0114031803032401022811040903020105091207032c030d0207090c031505010507031205070c0b0705070b 69
    0x11305903072410641d14030000303c0100301ca4075aa48541201d042141640080440001108480746040400d41d007d402d545014010b82d802603200406007001c1100c1c00e50354100e1188440b4400309040c4000c00300c40700307440c0c01034007030801006240c652400103880c41e078000b8402d10140c0c10004d103580c40c05249007680d0f684120803644511550f00c00b00d5490700c0d0020403500400c86550361300790740d2000204226000103580c04080d10118031801041c0c140b8808001640c5514404102c28220002000d007003030f180720080d140c07024160040c0c0682401042207800701d015200b0294041d000350703440e14103001800d402040354040c40450b401c1c096003800d0541d90000c1c03408005034007001d1860030011440c150243c01c0c000400e5000002030032106000b0990744041c1d181c1c602d610401e13188524040010010a0003409080000740a062854078554102001516180c004071015020414184443c0f8404401c4d0704c981800782d20a601c0b0415110341500d0403071041d100060255080000c1440003000140140d4080c5 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 910403048 1250 910401798 910401857
    0x1051501200a020603072c01030e031815041d160903150506011403090a060b0a05031c090308130801050106110307020405060f032b03060803070b190c1707 68
    0x140d17079443d8800d044904100300111290341505c01642908131943c00c01b84010b141ca800e8030107000d80c010322000c030380e00d90040b964904040c41d10481d900c1071500d406c0000e075061100c1c8190041c1020388600c0320010b0082c8540f00400d2a1122000381f00c80c0549010704203401031031620b0070081240c11540c4c0d94a94900c84140b207210b0b10740303c0e408500c0030b03801003030b03c081e110384402c0d51192079150129840e42e4070224580e0076100c9528115000f021418140b0305503040e01c02c0039004001c510882d65810041101b2401e40301c0800808081c04800248450300405800c0d0b840c8050078034082c14010020b01316441a40304a0500220541c1e022481030040107981c010b0f501210005440d56039030011071ba82141c01001c00e6814021a4208188018420b02d040201c265446000d000581000000c0c1d089440c24001c10542d64414002280000e003081c18080d40044405013042c04284101c0c0000d055501c08850138000c150340303001c7c031001c9060300342103998401d01c00d1070702c0040e5845510b16101514113441c0342 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 910404298 1250 910403048 910403059
    0x8010b0420030402030a140d0305061e13060b030907060906020312060909070b0c01020c060906040209180f010207080403020405060a0510030f11040f150203180d020f0301051501200a02 81
    0x3d03044d03503418408062860740010100c0c1d401c900030b4241944070740815070104046490320b00802c145080c00003a01401581d0500410641000d550801480d85600e8800c4480c0546903000801c801e01c0030009503014041c204002c0032072608000700170344804025008402154010701030001c600c3d051020b031030b4201505a5a15060340c86086000b418070440e40c0202d49107060004426504190550003044100f01440658142e5103500122645070075041c0d9010758010000d01c04910080600501c074000071603000200e811079803141d0708031402d9801109091b1a0314401107803c005500b05405079030b6202008a9072920154200710000c0d24001428210034100350b03a505c8081d2440c002a0700800641400110342512140e403041e0802d042c0302140200c140ca1000c010584182500000c00c0e140c14580d82e686007440340d1140c6040c000107400700e51040c0d901002585400d1020b4408ac0700341030150800d42410b2940c902128005061a8140035410541680c010300210300d02c0d90101c0d4600025a04031003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 910405548 1250 910404298 910404301
    0x6050f07020409021903031d030c0d08030603150f0709050103050601020d03021818060103110304120c11090702010b090c270609060310030b0a18140313090608010b042003 75
    0x401c020084200d11021100b180017070210034560000e07040598212003c156100d41410401030580b07403080e0350303031860300b18075804d010380001740c00d060203142d020b00c01900712098401031018400090034107503160001070030194140001c2d19032116000e0b02400c02800c0910403414a800001d541f40706c4545294101680401c0900995101842440501800520700746800c01100110741241000f92646804039181c5500c0d0b6552414035400d4910480d00846450300c8490020000e55140741410001c0742c110341d41c8280d560907903650211490060800d540002480040300003031180c1504003422a9500388014010402c03039855508000e04041c0109880132030740240c01e40800e80f17a014800301c0e10307403101e000b0041000c1407000d02e840318201c078000c602e03032142a1241c403007540450717100180da0021200c4010840001c039054031915004c40310110b04072464207c01c103001851050703294001f0102c503500c84a0400101c0001d0184009c1800b048808000f510004081c903480002030301c401b4450040f0110 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 910406798 1250 910405548 910405553
    0x61b070f21050d051b1e071e050c030303010b041701110a050d060f0b190c020a080109020f042a30151404090f0611070c06050f07020409 60
    0x40c824070440c68590301400403005140081c02c1600070088020304a850000081d1aa6404120303140a160205014500d081651840284c00926020392070601c041e0070000140024140100a16044501d140d81044c20800b840d000c2d0034601003c28040c80795005200501400382440102c600326142501e42c00d0704d040c480c1d00114050b00022480255031203010480350f1400350807400910009000510070411941c59404000ca48503050281d6194120f09200e002402184407250082c0030030282040c842c000840e07800280f065106800c6545244d4681c1e15210450070108581447c40c002118182305402d007400100e1480c2040f034242250608603074a003561902e0080002c040d03031090120f444019280c0c44002e201207581e082810307501152802800052460308100a45c06a4080c0e1541c4260342c6017840401c005820140020f42d10b2000d581c2b0702d20001001446508442e4002d00c002545a6000c0c0c1030042c050f10195001c0418880f04204e40c0c00c51184100854618941c11640000d0004060 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 910408048 1250 910406798 910406813
    0x70309020102010e0a030c050601060f0207270e010b01030e0a0203030304031b0f120e0d030935071401090806010315060305030d05160c0203100b06090a090e061b070f 73
    0x101c1134002c43c02081040717010b055009404060250240d811206140d0341c0300000c80e10507c02004140041e084188144410942e02d006000842048d82c280360320104200b899404440342000e060381c0b01e079541c0c0f64008840d40c144c001c1c01c0400c50203d014011344186031b00444d440b0701c03000380010104240302c1117418030454840341101070140c000d40300002d10995450b0901d00400c65842c08004616200c00c0314402d45444104040c8559040d5152074aa614047c10f03034268006c82a8200d02035400d04130302c2e800b24035039119042001102d080040030114641140354201c8020109107a0410a003030b4000c1c444a000019003c1c1182d82c85410041081c1080c05950000e0100d0342006007280400580c1080c041c4150304068011302d08074000c0c681c48001c0c408203440781c46030ba403c025015003000700340101ea505c0350380c80107041304400780ca42840c02c0c8040c0b0010304800f5141d08012505559804c908200c40001c010b03076540f00c1070701107150050003030001f82c1d15900e0241d904000d115101010003c010841705 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 910409298 1250 910408048 910408061
    0xa050f0d17070302150408070b06030c030a08041805060306070525050606090c191209021801060315030f020d02181911280309020a2706030b07030902010201 69
    0x2001d0310740000d12000341d080c11980035180c160014401d09840010289103080018003565011603604d00d0207020795030354403200e8002004c25a16000d40070101d2015103061000d6000d00340f0030f50410342e48608064400d1200c0301c0b00310018a28920b09810004192030000e80c00d41c018415003442354807407550078045107a020707403140811509000b00131403c00304480002e80c82e02412003220440c003da0b5036010303004210f000324141481000141d0005040303060042c0001070a02518540202c0e409000742c01207519810045000041c1200c40d000400c0026030502c500d034103000c481c2011035030092950b15503d00e560500c03c00030b4400e5102000d0318045545110300010140c2c140e032505912403400400c112040f000c0781e0240300140341005203c0705203143c090201c500c281c06014a42e032100040704603c007007440380c00c3c91840c103040d5160000c00144e9100f180c130200900341070401941d0b400740b049990074094260401c00e588142460000d000150450184135800440751a00045002031800103d01601c035 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 910410548 1250 910409298 910409303
    0x6180f080d09060218100e032a0301020408160b0408030d0507050c06040c09110c120a121113090902131104030b090a020406050306040507090c050d0219020c0a050a050f0d 75
    0x100003001e9403034100c00b48400170324a0085a40c00811020500300355040c69160382000c0c3d05402c400c2c0c01e946002940382c616040c107200c80100308103a01c2508017103030032603102d40c000702c00340e40c049001052104407e00e00038000c1c019403809241800d14241959569002e001030740c4c0c0c0d8180d121000100054031810030f64030584042d900302c0d165030909040082d0b07001c00900503403021900b0020b01208220300071040310340d1610140000e20200b0460070744000c0c00c0e0020030071b0344100000902481c1406415002c0c0070900c01c2d00034000f07a69031110704144050b241055000d0703821103007030205604c050b94400c81c0d2541880280301d40451701c00742c4081001120306c265000208940901d00902c420004000340b03500d03520340700703a0301040a5901d6908240c3d80317075400c6400030115400000140710080e0f0741e8101c0800c0381c02030b00703106003090031710100c01c0242d800c188941e8208008012a614140c1e504001c60281400195035105409051001046c1900e116001d101d0181040503030840d096159031038440701c980d8 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 910411798 1250 910410548 910410551
    0x70e0a050c0f210105180103140115062601031203090c05030a03030b120c090112060b1825020c012a0c180c050a1808030a090306180f080d0906 63
    0xc0c180d401d0140f00d420704503150342c0c88540c50000b103054200107000c3c0c0700440d6610400d40071030f840d50765501d41114190211254075500d6030307000458504981c162101900d010b4403040700303502d8480c10304494410766030302031520b03901104010408100b8190703050200c100d9500d808514081d02c1d05002e02c00061035800700d82c00d44290345000050607031550100212030000c80d100c5090011140010b680d9040da00f40a03588026003c0040014208080000c01058451200861280102d0300050504103104242102003421541009004000d044da0b44019500c06c50307450100d40b0425100a47d40c4644100103810b0203035079454481070001070801252072003103040c1d8003840c0e00f4062030103c05680706803180070f142020102c9049411403440c001c10107080c4031070341d40303a05091183e4412207100d5030710340348034202d101d804401080d00e0300c00313200401c0400099141c1001841c61840e050f811030f1058801c6030008554803400c41c000401d040144000d0341c2e080005141c440003d061000300900803540b009010701d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 910413048 1250 910411798 910411807
    0xb1503011d010b07030203160c0509041109060904111c150b010906080702030a03020d0207141b0d170c070819030e09063111040512070e0a050c0f 64
    0x480324203036448180361440c03590301c0980d90320b80848540380101040140540c000348004000712081d060601c209501441c11002601d60303880204a44100540c0e0640748180c003002000c0341c1e420602e02260308050155481c040f28a42a200d1045040101c640d003480340010078041500d00381850006240942c0108942c0890001090344000504031184418003191006000240c80c1740141000340c0b00e13610603000380d49002d4070114110020750100c1c8403802e40176804d0003814007003071101c02d142c8160480c0301c0044c002440140b40100b0082400c2042501c5401030109100001c2d54a580194100c00e2414500361038003604400a801d040150300007034081d21841c680c9600a56a0020000009000e52556130211060606000b50707003900725031054100c0a9035a4070b5080e6010b1200d003140364100c07441c0702041140300144400550b45070340400181003001140078086860481c5202da58295600020000503191900c0f0802180c40140440f441c075541d04009119152880304980c08801e0708100036030388 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 910414298 1250 910413048 910413059
    0x6010b03060105120117070f15050d0207140c01110c01051c180503070c06030204230415030305040807050604081e07050d03050a0801081f020c010f05040f060c0203070210030b150301 80
    0xf00101746110422a1181f04000540600c50f20022400d07182e00d10308942c41c0788004031054490303601c01d00b07040100303640c00c203c1070000c11818244403420041100c060b0081c07000f40c0e0001050a89003034006211074008020074882607811104031049031425045054000c141d006294009007400540b800060131200c1e091000c21001000800400317114550301d51708682c50b000704900701e02a5018510407110076882c41c2c981600c00c0000d004810740002c1000c14610301c00c03403162510b405a80d0085000c2900481c0c14400c4103414441000500341c240c42941c14503180160159498454110b6140f82a050340070354452900c0a02c15007001d0311018018400b4185030f4070303008240780d0001030740b40c0c0040d46500020400000110fa5000119904030000b8003040483c0f003000001d41c46032080f564550341e105001c9071803130300d103001d031a00c01d50107091006a4010f141c20481c0a48500c4e100e181d013150001c21134440140d0350740f024503800e50003500d80002d240b218440450041e1241d104503412070480480001038 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 910415548 1250 910414298 910414319
    0xf0304030801031e0c05300c010207140d0807141209090f0f070f2f10050f0f04050a020d061b050f0a03020c030f07060911090906010b030601051201 65
    0x101c0348111844012280840d41e0300302c072075500010091411170303c03000400640c03802c4420700d0124045a41d603514410100c905c880307520741481410f48120341002070144560741e010302030a0001d0045d4508408a0b40d506c100041413443c42e000001d240302c0e404200c00303061002c00100008401554000c40343c88046840e00e5100c290001e1802d548143c8000c400179241c00301c03841d403950049508541d60140c9889200d02510310111b504496000c104046e20340c1422401c0c20758074441603c5a02300600c032901040c6201606100007030070f150b0402c0741032400b800154040541c0740e540c442e80d8907441c0081615646407044c1050764961010354010101c034548820702c150395104150320b400d44480041d0381649901c0c1502c16004a038010010454240320031240780d4080d07002000d00303454440580303140480310100021180c0042500303665081d6207010b180c0401440c45001c80340d0800484030500c4601d410030110b41d480a0502900100301f6012010411a0340650f00352450012002120400c41d07071500d50f0550b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 910416798 1250 910415548 910415551
    0x80a03021c060801020714030909010306020906130b030906070503010f0306150902031015090810050703060e04080d06090b100f03020f04030501090b0105040905060a0e120d0212010902040506070b0c0f03040308 92
    0x1034240002c20708102c601f00c800000c440e2000d20140030607849030f00c1c42c1c5843c80250004400d0a4028200b008003081c07030b801c00e45480d000340c040280c9894917400d03c011180d181000042ca00720030302a0800050100c2400c01031000102c1c0d500c150003141c000700842035621071040c07a0740800602c0e40044144015085040c2c0403605031101301042400c00f264600084840000502ca140403c2e00309400d022005a01070308419030007280c0e803c0200d1443e03a1140707070ba0040c000c11030341613a554030b0203d81101c041c0b00c81d0048100500c80c0c41410300c0400d1107035001a0200b42d02d0707601007050007042e0302d405041c1c5d402a010795100394101e806894a556890a1141c00781ca40c024007120703031901501c0080759a1405100306540300360480300820850352442c1000c0e008110f2018100792500c214100031161080c0b850003070849014216000da00c4075176200300c0a00e01c0c001a0421344070710340184024000da480c0c0206965015400801204041d00d43c4010040c0a10031151100f150860010810003810340028006 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 910418048 1250 910416798 910416803
    0x7030606060503090c0301050c1b012003040605150901050d0312060b0d14040c05060c070302030a080d0b010908061b0702031605010f091a0318010920030604080a03021c0608010207 79
    0x5c801000709441018200c8408035003450703400350240041c80810390041414840220040d000140e19104000302d003080c00440c0140c1d080341c103000010070040103403500502c0c0e000030440d0b0101020502d00c0002520200c03050080c1401900702581c010b0905201d10a0b0f83c0381150300800c10880d554a0f140f0b408400d50104c0c9103040a18100380d11072079401ca50010440c4142d0300702e400d2250300341c280400c2080560010040700f003184141d00d00071025a0301403100c3c03d8150301c03403030300c2c26542c2021034024000e80d82252251414070550950401110102180141c0e1098501c150f000d04a502050145c025001303a000281d098802c8002c1c40078001b09030100002940c2003621540c0b22204102d100302c5030300301c041c083c09107440b0100d03194128851000d4042d5401010b10b0030320030390075810711a002d400c6a481a0061303986141c0c0c001c0702d00050b0302141484120640503400350a1030b1805440d036611510a060103c8105903001900481e0708051001d00d04402522031320600c000d580d90001107010750000b4405 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 910419298 1250 910418048 910418053
    0x30108010e0309130207031e0c020a0503060403020d0f021e070623070314091806040506011d09060d05060108150c0903150606090a120b0903120412020703060606050309 74
    0x82200710307800010350708816801464800f215426031803081c046d4010141c21003d000ca800d01c3c489403101e0400b00d030350703849003165286c1a00f071445004004081c7c42641c082030082d001039050001196002c0b800018070441030420005020091104a00c0d00041801540801407040b81c03080c01001e000c191001102c5141da034141590921598114803040d49459101d120982004504d0000380a484044012803510b1100c40c2445180300126405580415013030b11070300340c28010031189240512030540c0181e0207103003443c0141d0802055868040704030000b18481c034144000200c903503030390100d1242403c1d0301506903a029651184456070f200703003250242c100044101c001a440c40540c0c001c1c0c1c0c1003000b00900400d84202076000841e603004010344a03c0e00000c041019240613181e0b9014103005041d0b04483e80c0b1070203068180b00107442d1001d071880c000d9810401c441c0c481c2004140f200e58005030001d44103241704414403402d034503101c02540000d0519041c150700064442c0c204bc00f031880f40913403070305 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 910420548 1250 910419298 910419311
    0x3020a0203010e0105010605120910020d021201081f0e0102091c0611090108011e03051e060c03010509190f0c0314160503070c060e0f010605181e09030909070503010801 74
    0x243c2e40c01c0c2d0f0000d0040700c000035000c2c410441952000c0c0142c80c1c01441e61401d403000500003440740e005030703844008201e070302d59000610056010b00d8400064018420240034041000c110380b0030141c0480405000c3e01542c3c1c4907132508030300d1070302941110b41e0070300d0042007088034a043c20582406105240b02c1960100d2800c201225420410000c841c503030b1005075213144060f801e0002c40311410300c20a01624a100a424022000030303420440120812074050b00104107103101c2c0d007560700d4824010030002078a541800100802e444600c495030300051501403009002419805000c0240000440340081034140820780c0b00c1160503501c10382c255070301e04104060f03680d5080039100e5142e601030311550000d0402c000040440f440350b054848840d05c98100420a103001d605113600d0080c0c0c03d44403080c1c5035502c0030100000c1c500100a01c0720085856100301ca1854210b24003040104140b40b0b00110000410006441c140d00b401103c60250004207002c00504142e140140303250002d0140404940c64000c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 910421798 1250 910420548 910420571
    0x24092403041a0a0b09071b12091401090f05040e03271c03020c150c100b0a0f21300206130209160311040b031b070b1317040303020a020301 61
    0x14008034040c02401460344d540b5406c0b4111a2468007140400381a0600c0811100040b0010220034000c00a50744101646041827003030700014111003207080c14001145420024610581504402c488003120f000404800c241d59060071403252062000d83e01100a0032049010348489c01c2c85c003245019940302c400748002c038094003041e501c9000c001d40541e00c207982006441c82d041c41c900c6000411a10b440b400c1040565138589441c0032414460011a03d561481929042c00c1c100da8008000c0034840000103407410450021140a403000c1c451510000c09048062010361504001d901c07900283c002e41066a1038a0022900c9120b48003c005000300303030205401c4a05841c0e210b101540051844080d510b07421021088000c041d01c41c0004d168880160584041c40600604010319107105070650301d207040305c2c15058080096070f156203448400d000f5080840c090800a56000c07002d07078205c10005080741404e207460603803400015911100005c0103c01c04da4045180310501c3d10a4009000d03004408 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 910423048 1250 910421798 910421801
    0x2011a0d0305031303050f1206101b14010b18040c05011e0509030c040204060906020c060f2b11070303151406030c070c060e24092403041a0a 62
    0x140c0007900081052002c43e0300240240625000305100e400c11601c1d00c03210407005c003a6038100c00e4452059031510020003006060280100c60350080a15207610901d00d079a08079030a81003029406007904038041e00301c0451490961011050703920042c00d0114450348000c1094040c1002c940859049003030010005407035026403214102e1114524511000041c10203080301c0301c1d00509001b607407621031048000f9081e10380c2d01c020301c013501e05035550a110b681031250103442e089880d20141e001d0703041044142500840102a00e240d00c4071481c9414003056001003081d000d041031141441c4480c501010041e4211800008004040c803d880c2400310031103a001c0c0b030b243e4547d684109020135245103025080782c0303403a40c021940848034490040c28104030f81c80321561070b003043d04002d001c68680740c0306c1c038501e00d8031840c00d802c0c0e81d840d000683c0d40380394040303c684014001e24400c1401003600c1c81c407240102420840e14205411140f03d016280d207814140100040d4404281c200c216510328089100e003140f5 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 910424298 1250 910423048 910423069
    0x1415040620091203120c03040b090a0803040f05031329090a052110090627030e180a09121403060108130506090a03030627020705010e060702011a 64
    0x7404800d0420148805200050304801c056034120300081080c05a11070503000003500400a0411140d12407409117130900001c14090416070382030748000e1102d13001400c14001c45ea071041d4407064420301c01c10249401840e41c010b00e085407003191400c1c0008104044040701400a016a520094411640c0c01002c4001445903007a0550080d4180d0014080ca00b0000442074104240b403100d1140c0d00705072845a42000342c400c410701c0095855030208000d002c1c090255003108059400c215601c035048118191268070441c10040c140050a007083c0055914164038944800444260380014071b403541c8200c00070b05e1844001c03603041c2014803403400710911844072001207082c0342c06140c0c55522840010340b02f0407002800302c041c00042d0b250140c0082c074103002290148900380f00a0010111914028003541c40c2d030f410207080360f071522040da1a4400e042c12409698100c0074801a983d078400d0034024058441201601c50303034868242808001541544081031031150502807400b8001d504013041185542c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 910425548 1250 910424298 910424351
    0x3060709030c03060506030705100305060f0f090610120204091b02010e0318190602150c0f0703030e031e0a0f050f090f040b030d03150b0f1614150406 66
    0x141c40405100040f5154041e507000200102140d50140d0303038100090210012b41c6101000035100d10a0185070300b090700848052560440b070295038425a14046609000010181880313640d60502d01c0c50700c180100d15046121054180030740d9540d40b00d0300345401810b044125004081080007000358014810311888c4d005a81b00c5d0003070752900403d183d0075440d111700c0d04149540000030310807950b0400c945060030030040110390090200c0c500c8400c00c000424a0051980101c54400c0000502d0380d81402e04498409a240c24002110180500780c6d6185000340c1c80b4840d403810312001075049641c850006444603094540c0c80c0300c0b10190760941110300b4010306084007210801404120f00d185002401005941b202400004440c2c030031000192400b1903da4051011075903400400c000e00328094803800141210b4039109242c100e20744441c1032184640b40f0314400c0c06001440490030050049540c8103c02a581c08480c002556041012840601940c003128482e2501601074070348050340312076007244035 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 910426798 1250 910425548 910425563
    0x609021b12042d090f05060114041806030b010e010503060705041a0a02030c060a270c0605030402130501180b040c0f081005030102070f05160f1401051603020c0306070903 75
    0x1e207071110030818010050220743c0b50f000d160701c081500c035807103101820090054130008545601c25090034421140040c000c5030412160898002001e8089011281241d802c166000002d440302ea244030b0003400140c0004003008511000050048241c807801416103208070255601620342d105c0c29986841941b0401554049421240345040c01178400b40c02101c0c0180141d07480c1c98a08003029013080c604803200c08815541c1c50b80c041e520f031802d00c13040e07000d1516113038000d520304902d03168455000030728424441007000000002e000c646500b0742c0440c4075103149000f0700095840d5071030031840e20004400960744d10719118404a90785424055212400c8007501d0300c545005040744221804030008010a100500c0c6c0d0000080c262405d01c010516503004482e2801c0304a03227450b100b410480c80000410020603507803c28848140b00514140440d191424420200c1403042d0040e83e240c0030760705400c42c00f040f807100c4030310a05402103080a02c0c05411800d45003c4c0c3d407010016600c1c2400c038007005c2c0c080b2 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 910428048 1250 910426798 910426807
    0xc01020c06161101050705011b020f1204170a0c0f030b0a0501060c3521060319060b090a02070b31020d02060c0d031404210309060609021b12 62
    0x34900c499103440e07503c41031600900d0721115850746400d543c0c007840f040040c40c07060b60303805c05250b6060100c018800002c0d0058a280c05180d890318065000318010043c10810306840c00a41d00fa00300500b40c000f03130b444011810701540c1c0308100c100544103440f00390781c42c011220010392071101c0e82c424141661220740310042a1001503c40d0031031007a005984541c0328031103281c3c0c0088020054502d540c19102c0d071400d9542d8002c032110760181c004003484245040e410040900c1442e5401007446410840034100300d0140e003215042c0040a0103c11209031b4000c02504144a801030740e60f0001d0201c1c9010705264841a21740c3c100907403542088421281a2001041e4040d5951141510783c010701400144401000700c0c403600001c11a50000d00880c023564440ea039000c5429806003d8499200d03a0303a0924150b900e4a603c030701c0c2c0041039011404500c0c501ca003840c1f00741203000b54448000c1da80c00100412000d5242c40c6050025440807810076000d20f8202d80c141420a4000b80e00c1d0414440e00e0040c5080 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 910429298 1250 910428048 910428053
    0x2371e03030801091d07090905120430150203070e180a0e01110d020703081602151905041b0905040f06050c040b0310090c02030a020601060e040b120c01020c0616 71
    0x3c1400120b45d0700e400c1d401c042c62902d01e45042012038068140c0c1440003611030610300d8940d10f09260b204018100010030300007000307034000040a1803102c400200c81c0ea0324000600c209058650555040144418000341c2003070901152540514030482a5445080043d104942044000744201e8010f03441780040100041c0c901d801ca030000713600030b200800003241c03140300680c42c692240c020035441c030301d2560b0100e02c10b41816032084020f60801e0721000301a4095842040007511800caa00300405410000343c0803d08010103100a41c041d151240320801040c202841e180c10a4007803d942c500008040f00d501088007a018418980526800b5081503c0400e107580e5200c042c0034001c0140311428000e00001078101580700003584907000d10740085000904103c5107808580c020341030441194000c1c4142500550001041030540f6420304042c40d43c41c0e413500c00103000e0002031800750b411454035a40d900030341000040c9018452803d800b621003030020a401e11070140075980043c2110001e01e02d00202 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 910430548 1250 910429298 910429301
    0x606300c152a01090204091a0c0a090b0f04080d09030b09030c0303010302040b01140a05130b03071b02040608030c1b060307020d03020904020d09050a020906090c0702371e0303080109 80
    0x10910b0700d500c00460354050360b40024084031120a02900d202030504503d8040700081c2d60015440610080c0c2207007404c09140000b0300250761405080d014000028000607440194800d8130000c24260040b0380e058203c1860003810341c400c92000f1201e0903044000b040150748044140c80c0c40c0c10380d002c000c50a5138a16020000605540350206040c0030f00140c3c0e4a00c4090408018050181c242d2601981c0700b0b02a04400d041744140d0b84109505507090050104481e0303c92040c3d8090005809011086022400007400500d0b403544210814400000c40c5078002c0804200e0041c2034a41101c0c1c105491185401d0210034841280c0c204016000700c240110f82c3c41c0264050031804501410041c20900c0108501e002ca038031400c0240ca6951041e140f81d000c5140418a0550010f0265100304a50900c2c0c039120300305001d0b1560003071081002d500c00088104d054280c1c1400140c940162411107014801041441005030091041285840035503c40149151500b40c0c00c4a90603600c200040e03203810140c40 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 910431654 1106 910430548 910430617
    0x10201020313110f091f050f031906060b030420040605091621020306011d310f0203010801060f080606300c15 49
    0x200c042c2408000b00c501d40c8002008011103200000510304030b00b01c1c50450f00104110304009a44140b0b2031466200d550350242010a2900c402c18000428816007040ea0194032824070744c0c03083c030a10b411000750ba90042400140403510380e85910760740d9105841c1510440808020440031040e00c48295440b058203d9007000700600c5d00b008140d40e01001407051908a80703000851003682d010f10500c1034081000510799056190601044000f0b400c00e80380240015960905131b0b40c1e50b40c4c980c240e00501ca100808800c040c40d001d5000b030b4155407158052a0560a00414403030700080c8034000e00405c00082d00c2c0c05a165810081045c0c03c48090741d010740309a11a401c010003485a011030b40c550805403c1d1181100341041002c20030703101600c0c21900b6056400310108012518010401c0c0f91141000c8414180100030481c012200340a0001c140c0d2528045404c941d880c15002c54200 = true := by decide +kernel

theorem cover : BRFrame.Cov 910251798 910431654 := by
  have h0 := BRFrame.cov_init 910251798
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910251798 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 910251798 ≤ n) (h2 : n < 910431654) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
