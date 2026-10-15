-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5061
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:37:02.278487+00:00
-- url     : https://prove2.me/submissions/957ad550-f155-41c9-8fc7-800416c95463

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 910071942 ≤ n < 910251798 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 910073192 1250 910071942 910071959
    0x8090111181018091a09070c02100c03050d02070201050903010509010230010e1e01080706030e1903110c0406030b15091509180d0c060b010309050a020f0406031b03050106 75
    0x70258407440442c034030009150402d510300800b85c6840e4001d44c00360b11600700da090b40d0303002c414602c109802d88828189010f41e10400c00903460b0070000c6000d01a02c41d104902190340f25003504d03403601e60100c0041e178814413400162494080c03284003030351660802c000c2142c2d50f80190082c11a20000120018001c2214061407030080c4006008015401e00040100580609100d0098001c010903039800000943c04070714040d15a000d1700070140550040400f000980d9162050845c14040b01010b00300901c2c0c25000c0f101a40908103014041290320f5120b040d440b4004c1c071100c40a50401041080711a03070341d01e810a80100c0031a003404407088960f400207250304090345000c1c85010348031441c0e0261840b002c1049150140030745100250440e03105001a0103800304030307000d4584002d40700d0342402c440030b1400038251008116402d04040c10101051b000510003d8244445070f411240b1480070040d10010500030040345c0d00c081c10401034516080320060007130200906880c05240203100c0c850f03c4900c0c1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 910074442 1250 910073192 910073207
    0x90f030b0a020a0c05120a080a0203130f14070e04060b090112061a0406060c0c211410021903050108150402040b0f040c090f0e0106020706080901111810 67
    0x900380d412a00001a001c0c103296004044403880d40c10b240b00c02e00045d8031824903020030ba0600c035072500070005189020036040354015501560110043d4a1848c012009000d00b80032088024401200c01c500002000610699030003c400c0d140125400c02d9912212422092000d4070192501440c1508024883c140804c0d85070580d0031034814007140740c01c2d581d5088018582c51033301d074601c03031030030b8128003520750301c0b40541c00040c07045544030008460181880e00d400100d40d8010364500400500d00b46841c1d4561009940003a007281a441c04c400e045d0001604240300ea440203090544001104050b140c41c04150303403001007c550b001c015176138803228000d9441d58201011441440c480c4000782c014500b40d00300b003c500b503003d08241000c01082e00071505880c0035082c83c102141c4000410710000e01000641001030200d180b641c00d555140203006501c030303030751402520204055035002402e000c8007500500840e401d02100e44c5e030b80314500940314091113030080c40d45104260113101c9840e4648203001 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 910075692 1250 910074442 910074449
    0x30b0102282105031b0d2c010605010e01110a0501060611160b030612010209030601060801090b011d0603060a0815190e15130206210619030f0206040b19090f 69
    0x8a052440c2c031401c02081c40c0e00161010140960006c0000b035200c000c4030300910a01d5241c030058138410b1244400801010709492a10300e10700c1e032500d441080642c0e0300c400c01582903d0282040c60200022a07a03aa060400c81280540390358204140040d40a9012522a903503100c04000e4821b20106039200145003801445407002e010400d20208000b45461204640001c0e10200014508006500802d00780f1000b47e20000101d900000100300c0e40c0e04038000e030260080e09180221058421810140390003035482200c0d8001c0b034009c80061850f481d1007021501602203074040720364205929012403400f41e801c84946654285220000030a031400c1d000c1c0c5061181180041e129540b0740d0741020f000b6840c020081007000d44503d15010141c0c46030300003001c0044c807141c0c401046a80d01040300e043d054011705110f02807209118240c074030f048003100031016a03a1101222404010724000920f040c0640d8000d403034981d5000482200a08202c410070001401390389030420600c0e0b686207002d150304c22a10 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 910076942 1250 910075692 910075697
    0x4020a050705340e0c0922060311030102090102030301030b040203030702060f0d0c0c080720060a032913050403031d01050601110316080306061e0c070e010312030b01022821 76
    0x30108140d17500c0752010f03283d03800700940005101020388000c3c035604034081c1c038041100380c3e540b0003d009010340c01c90880401102500254540360507103000035a0303484144005000800020080350440da001d0003103d04280d00101502d440e4030b01001b011150f40d00202800d003400c0d00e80741042c0c0429000c2c8120301401034001080c46d06144843e283c200c05c0b1200780c803241520703505120400c0c180da03070760070003030a5222071554000400081c0030200b203034078244e1a41c401080440c95000d0038440c0d6241100c015040707000c42004a030503102da140079006818411140c0f4580f0b8007500350310000400560050744a240266208921031707100f504856203a111f80483d019008000b900c803040824610030046410005c0a07104524040801031240102c1e0703041070440c4210000021010740000d010082a400b81c03107211070414065156a84815071600054842000e054495a07200500c0c1c1c024032000d410103401800c2d8000c0307641d000b0050700c80c1c0d1514410841d0042c1c4000a50700c0311040615480c00d0700c0b01d054 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 910078192 1250 910076942 910076969
    0x1101090f0602070c0f060e12011103071b06050106111e0d180806100f0b032406120a0e010f0b181003150f0501080102130504020a05070534 61
    0x3601c41d44007a501142050b10121800003000440760110714003040102a1544c03080b00700c0c10882d04100e4004002051108268100f003180103500100100b140d803c8552400d000c1003030b040844038000984103400000e420103117440000100700750406080c0d8001060b56007510702500e100200c4202124040c9600e500c26841461030142190003aa2020814074160f030080d15416a50701c02c482c680041215030408076442100e04210f11881c5803031540c060001440c0301c81c1940303000042190601c02da460390f00710b502c024000c150705039298281120281c00c4440d904500381e24000c6000f002030900340c1424000740d8a026003050825217140f080051f060702c010542000c11856032541d501d00000a40344140815000314000300040b045034854440e90100707800410744140c00428001100c0c016840286242d0041043c0d42c0351074a5003007910161041210016160401030b8802c95850190100080c910710490318180680c205503400481c4907401854100303103200040445080768840c9100c3c0c0380301003000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 910079442 1250 910078192 910078223
    0xf15110709110d1b0e01080f04030c23011b020316020402030603011d0106050315090d1805100306050f1507030c0302030708071a010603020a0e19091b110109 69
    0x1d90001503806400520b01410700a078448420300301e030030440a910005201c80c0c644c2c2c08003500403943c10601142420540044e2402c10070641c50800c0003803004040090318a42a0201304003a05a5031410b10001410001d201040014078001d000861310120a02030300c0c00144882032000017140c2c17000995800c032511018180c1d0922010703400280800390b040d500c907403900040072540082d0883d038200480001c2030741c0c0c4c80e003c14107090021140a1040c0d48244408000c4400c0c0000b60007164180789103056a501c0040494112a94042e40c00a0740e01813008100798609641c560010016508221440751204000208108100d540b44002c00400202440b5401c0400d00808848a5079402401a28903001c0d0035500c0700e826a2207203004a8101881c1d01c25092000810f40425000d80b549042c1189001c200480140000d00f04048051064201c4131815904140104c190002070080f000b041c00107007008071030b95100b01c09074200c1c0c03000140485101da041200500407a5002078110b121034651404 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 910080692 1250 910079442 910079459
    0x902160204090507031e110108010e04140a020603010f06030f0b1503040512030f09010b150d110f0406020c012d050306010c02120102040503120310060503090a0c0f151107 75
    0x10b10010a0b41d56001d500320010104030801a41e20100d64038481d00e1010015074036004c0c034071807041c071111810041d986d4014822aa9030307086032a00320381c128112011507511604007501d4018082e00003900000040000501590410401c10545550361011300c5440d10580c400c80072600e0004045601045480060382d102210f4801582c00c58003a10030341d0704100d0b1130201d9220951081e108101c1c0140b0360b500700041800d007171003a81c542603003c44020b1010142c17100000ca00380072341201c801e20913130b90f01440c004070020380003120034181d0724801080e10f941e65440082d40350f61050075800c0c04544c401c0a1842005c07589504222100380c0c94180c4110441d481e501221141c2009000a041c0030a48240c0009a661005e4a0300c040310a5000540c0c0d40c1d00f85001d0508024050711000c1f641201030091060702c042000e580b0044c4c0310685000380d165031314074201c10b24003810510701038403480301c6d4100810300d030a1048480c1c05132840d03270014440c407181c0f24030708a841c4a40804035000c16042940248443c56 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 910081942 1250 910080692 910080701
    0x180e0c03131505040807030e090f0a020f16111807090e07050705010e0604030207061d100e090406050f0c0a0f11031312060b0d080a080402010c0f0305090108010902160204 75
    0x14001d00b20784040d200e50404840450b00140c0342a640c0e080040342c550101079002011074400c5034217441c0024141481803c49275130a02c0034145048464000c103004440030410300603100140c8101b40d50010f54165414008032054443c04524091000140b8030806e11001003022030055403035580311070b2050b02d0702c443c0020b4400c0282000d001c10000300983e0700071031000d00030740010f14410000703002d00d41881d1034003900e42452940000c0501006815003030580418030402144901c01b40c8090f40b54601c107010854460415511003a40111004184810f00c0701c0c2d0b030320080c403503021441030788200d8940c10701070082d501444000000107083d206143c2c0140384a04007200202440c1b00480741881844030035681a888507070049c801c031a800c0301052040c0b0455000d054907021003541d010300001082e40b14609a4401c3c50700031001d0004030408174046900c9024922113868020750b0012800c0610302c0c00820030b5010303409060004d0801000030800f03181501c211103a084d4903000160807010668280400380 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 910083192 1250 910081942 910081981
    0x91e02060a0c020f150a170c0d0b03101e0f11160c0302040e030d0510050a1e030804030b18010b031b04020c070816121104050c19180e0c03 61
    0x100c1c0d07030102c0403826205d18160142c0480c10304111030310f4036000c4c8402094002c3d04400e456456030202d05102131002018100e80405903100740c0854801001d4011078580100d4011604e9014984171252030780c110741c600e502200320040b844c1402016076480b07481081d55842403401c01a0707002042052843c0c1c00b580d0400803114450040500039a9032500041c007128002c40400c900394000140c1c1900140c0307144620f60b4082e55a40c03990803290b0410000c140300b00c00d24041c0080a40d98032502010961400700040010350f40300028075511034891400c1c004a80c8240c5406100c01c019200d034a00380325041c02240c4030b0b80d0340034000b44414524860b0710345114040c4407c40c4c0c5c004d5420051201183c90901264015180c410000e201111402c600c80b41180300e16440215a11608001038000a40c002078079406407804440200b62a164100c844600b407003042c40319000709030b0703c0c0e05800605400001000648204ca610040035175583d0090a03900c100840d4040c16141c020400079524002611401092 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 910084442 1250 910083192 910083199
    0x812101703040b19030b030d0203130806090a032f0d090e1339080d020609030d050a0605090a06030c0803040605090922030513060e0d11030c0d06091e02060a0c02 71
    0x21310210086400e201c1031a00b00230050308001408071261400c240e01c10001c103411030003031030b50380f030b184542c141c0b00c103003000b802403c20684540f0224414001815001113a241b0325054400e603038060b1400e03564510030240c40d40400c45807100041d09480801000c0d200722140145400310b403200d6541c0003201780c500d160b021001c88541080002841c40070407030000c410048890081030900b0142c2d51450111a603218030115480001004000c01020082d10503d10381c1c40300125240d00e81d44901d074050710031500550b800c0784c02070741008403424846d001102101c1c000d0040282c01d0b81c450510a489205070300400c8042041046613241e5420b0001c01c4903440503101904103000c888107506d00c4070b0400c04a00660014001061980400b404182c1d5040103040505014038030b0000440401c807102140e88029110081d40c602d0207150f600e00348050070501c907004000011180080c0b5000c00102513442d000e4510000901c6d008501b81b494910010110b600182000e0030200120811100c04031080380483c0c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 910085692 1250 910084442 910084451
    0x904050a060f0612080301051f02070e1315020a0801091109061c050414010e0c0a05190906061206092d0b060d050f06030705060a0302070812101703040b1903 69
    0x207690903404da40508262056488a40d03c3d450101000f02c0900d00e0300c800d84002c0c0f8800280042c080e000207132078003141c201910b01203450b50f541e00c001c0001706400201901582c10550070048200380b982c01811650703842c0c0c4902e841039807100c25030812145074490400d06003000b00300c5980039150080103490700c00388080c1000d011072515004441a0b69050b14103c1c2c41d5404102c04d07018208080c043c1880f5004254010703d048081103000400c0c000441c07040f58025609119880c1c4400082448403000c0c045501007400800e0340c40b8001000b0409403c3c154222a1802c140490710111600454000008007445100c180030800d241111071045210b1404d255591074103590342a1301c070400034001c1195903d40002d601e07d010f52415141083c0100107038426000b0000600c41ca5655500340c4070030211610f8016200d010350300d80818a0b21410070303074510b01446d0004116403010340d03081c220190381c5150300c5400000d84040505a581c0500c2c0203138403c1305424800d0b55504ea508070342a0503615124a03010a = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 910086942 1250 910085692 910085699
    0xc09030f01020c21031e04050c0d140c011805040b190311040f0b09040809030304090e031e0a020a02011b0602132606180c030d031a0904050a060f06 65
    0x1d00720780c00f0441240301604110310315014501ea440f41c0c1c04242e000050401e1561400445030715000d02075200f00810042d104000c201801410825a03a4141000e400c401d00540c0c50704005108081d200004500ca1040581c2c0c01a1944a030b00d9040000e18480120300e101820a001c01c8058003040802c2504806040e11800da03c6001402000044d07010341602c145005031a0302340400d803031001e196404400d062040d14003440e1280f000c401d60150b0080700d4a52608000000281103108641c05890303660700340f5074001d58514002c4001c0c600e2000c0204500c4800b00c04204010660107030000090250f0420003041c0e0140d405803141c20300d50a41413141d0102c3d40101d69400040340c000c0e00500134031181032213050041610407583c1082d9000c401032074166240b100c0b00382c0303541c8a100400340c402103070141c896512032800400c0400714680000b01594030300002d8150081c02803440b03649965403c03008484602c914105410158000d981080240c452010071351034003405000351150340c403442c542e241c0000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 910088192 1250 910086942 910086973
    0x10905031b0f0d0504060801170607030507030b030d09080f0606031c02070902030705180405161101060302030d1101050f10060518040203101a0f1209030f03040b040515040b0c0903 79
    0x203034140e15103840e5562500d0811b100241003180503000380c0b80070090380400c040c5038900001c40c90342c002090f00c0d0204260f50b500c5402c0380034141040c200f9406d4440d2401e040e00079900301d2101d0090701c00440c200d40d0f05030f000e807641c0d594440c41690111781603001505011f504200e0b022031a401c1c0d0f2101c1c012036510300c1c0c1e603030158400c9a00480d29000003c2c0e02150310841d41c513400c0104a1039500445042c01542030040004546e048020800c000348108000c00980c200400e4001000a54000381940c41002c04d5000242070b06004004c140c03499440d200003d80c030001c41014240c0281182d810100216052120549156000c040180100c070910310351004150340e240010f42c4070b4420440e58075a42c51504241c074140800020150307140300c00c14441c901e60b0031882000e4a104445107c515101c540380d10300c1040c11403190503d0f03500e408100008100500c20503252843c0036511800886100880b23030350141c0544542500d00400205041c0e0210b0301e0000d002026005003a0000c050f18142000c8800c0c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 910089442 1250 910088192 910088203
    0x270a150303110618060604090f0501050c0a08010b130b0904200a03060602031e07020d0606060302180d0201020c0613240306051509131e06031103010905031b0f 70
    0x210000381e0b403aa0103045011081c82055005882d1540301c41000440c4a00c050b00c030100281200d0207240c0d00c0b45c1190174400c074282c0c14074440f6007048c0204524100f0b4200d00801c1c0d40107038800c00208074200000101c4000c007408540f82ca0b0fa40c601540c0059042005410051348180042c50f07209844250380660101074102c13148111810b68492580d980d203034070018040d40e020350b110005640003403066201040090103034408080c5807026039690b86106100040f258a45014042c020610b46000403c5481e05070303000300ba02924920031004030159140c200400c80044560003030050700501c9103403140303040c40d0300a84580b40c0410b0b260a086034440b08a50a242c5c8903554001000390001c0c100514640c0500c0303840090801a5032004101d04095440080781c4100b50304540134042c480d41d02c1000340350701d601001d10315030b201c0190442c004005011102410303803800241d803000c0070350a43c4190384c51305204040215500c100070318104040e0040a01006030100140c41060161000c18a03500d50207005 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 910090692 1250 910089442 910089449
    0x130507030e060c0a0c30020606010212030103030c0b0c0c0d020c0a090e1e030d050a0207020f030610030f050703020d05060106022118150d020a0e270a15 67
    0x10300145038038140307802a00d05500508000c410100400002508070b5010222058007900b1080c641070b03422040d41e0354000100045401c8035540f00001814000590114955004000076400c940d00400c1880344103000c1d11007840000c000c94141c100503400110f501045903404000850b500d820b00c012088081c1c208002081c0050050704680d02080d20b070701e80b03020b1290242848000400c103000030034201c541e4440c150802c01701e04ac100c010042d10b8100080003200d240030000601480740d07051410041000e500404c0c0d040f4840c000b00c0c91041d81604000074403610904500048140203491500c8010304103d1810081d01e260190260100c01f42e1610701141100d140302d400100382c01d40c500a002410203c0c10540492000401c07501c41c00307501001c4003951440036004048026103039820f000544034000c2d2000c203195081c000b0460104543c50f80d4090005041c05440e8866001c1464041000107022241e10010a00c628404044096140c0c400c107075004108840c009503c00d00d0149a01a14000342c1c03 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 910091942 1250 910090692 910090697
    0x30204050108240615070c0f06050403120201052a07021509210a080a0309020d031e0201051b090105070b0103150b01020c010807350106020708031611130507 69
    0x30f103c0309012000301400c0024112205601001d060440000c0d41108400c1100150f01c1d20203d040401d05c500c11400000500010890710f00c0c0c00d035105006442908140f001b80d440e0002c010714051800d0040c05840d21525040c001e58159480c1441c00c11180c0d81442d105003400b8400f8071681d030068685640d200740c20505145400d07140c0c000042040203034241350102c0318502030405558000b0070030006480344003613030103054941c5401200204a004045501001e076111014544600c1816041503105601c040050454a0050401c44041e0b00340c88058500600da42d101c591030109c55070182c0f002c0c0c0503941051424500e0040786440322290002d0a800950750745051403801404481107200d03071801c044080c00645041c005450020f07007003400080404060110700480b450385100340416031261007456042d0a805091000d0f01d0750b5180100340116005449100800b04646800106031560500b108000003007241003a45c030034000c2900e030401c02d40c00c5846441801c0d607a220502845108841ca036 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 910093192 1250 910091942 910091953
    0x90f010e0601081615120b0d0609150603020901090504110607080a122306150f2703060114010e0d060519020c07061116030308070f02060114040e07030204050108 71
    0x1110190070409a9890884108203c04040101d2002c85c450515862020b05006040c6d1007124400781c0a4039070101d00d01d9100c0013105c000030420000f503004000c0c503805000e45104181032220084101c95050001940c8080b01e90010414256290000d5a002c5d1081485a404088900211b0155000588210b030017110118000340020340c0030325210940102900c3c01d0006401203d029885000008030240e82040342c80c4c0010b00e19200d03012095070a0008200ea0b695803441010240c8107508401c1d0b89211004014243d0084840701e202144907200f00100a070425920f81918030902281100c002c0c4e05100080c951001c942d501c0f03074004e0203401d0060742e0124082c5050080411080d070b010003036551907441405000400d0703200290403010307160a42041c0401902e840d003650314008442202011480e505c4078080105070703000c0300303080c094840c2c0d03103c5d0341d60410a084140d071196000d000c0c44550180c2c034500301c00f691074107400c038156035580380301038031703583c9443e43c02080a032442600000019400b4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 910094442 1250 910093192 910093199
    0x3203180601030c0314031c0b0a1517060a080d081e0a020703020c040c1e12060f030b090138090903190c0503030c03100b070b07030c0e01020a0308090f010e0601 70
    0xa0031000700741c84491402440c40c0c000c42d03118410900307000d40046d085c0d42d0b990380300c4010303140c40c9d4080101c0a40b0482544110015020900600c00c00d4003850103000342607908089085810f041e001d001c180d1302c400d030281c01c43c8a82c100741107881c450000c085010000054641e40d90718120800d8031400b44080100140c3c0d41c0a49040182c54440b44554070b82c0240d240c030410360030031680600c40c0e100000b2101c2800f04184103aa13002c9480280b2046000000762412030002100e01c407200100c0102e92107200020401e0f40c0b122146422900800a002521000f22840218400300000303200c00c0c45405003071040700b121801000c540c8a0000320742c3e02c0d16507032000401c520b09400940c0c03943c0e6000310501c0c0452000c0d00036a260781c0c4902028203d1480c1078008004104441d0303041d01ca08000c1c0c2070245803541c07106081e0400c0481c07010196070780710100337182100132542644225800c144148068004200c1080107aa045800700d4006208905c2c0d40640260b0041c5081d081c010480c4a000f00c0c8024100c1e03505 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 910095692 1250 910094442 910094453
    0x1140d1a0405031e1b0a0b070807090e0c070b06030a0f081e1303050c0a0302030a06110412200a050319051006080703140624030705060d0c3203180601030c03 69
    0x50300d14041d001b60322035045031001801c1400300541c411054030f410200c1e901d44400c295050880e54100064210041c0c0801504000200240054a000340c01d1030843d41c40b120b0a040d1a18080040500580d200100c200d010510740402082c2c890704000c2c030402c00b032050322902c426940081203200c19418684600300700380041080901d2034440c0c22603007001114607583c000f0b03a940c01802c1c00100896200d24603c070321490428107440c000d00a15408179a4408645026004458070a8025045901c2806003081601304180044c003600c901400400304161010f4100c0c0e0380c1440301c1d0013180d00d88541d440021901078a40100c40082000740002e12045003549020f00c2407103800444055036501113402c0010200e03803080d0242c9130803010740b600c50141c40810007184c01d2003c260042600701c0030010f40b42c4010009a40041112451580e62000788100283c0c105c0d2400b0004102d2000406040034001ea5404082d00868000d98003013082c241e01d00c00c40d2903040c1400400da2041d1460a000d44c0c04105100 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 910096942 1250 910095692 910095727
    0x23070f0b0a02030910020415120e160806130812040f060e01060306061202030d0807020a020603010f0510020c0102060115030603020d1202150f01120311010608030301140d1a0405031e 80
    0xb42e00507806c0d4206030a061035541c1550801c46c40b10100461004c0e940d0304113482d5488903140440e84800e850b00c14031002e920915081844c400d0b803803184200c00009820303100c84151a45210b030302400c0d041c680548114082080300c0d024005980c100c120748a0000002c002c0d11980d900e200c0380c2000030403640d1031820a88100c0d0801d034040c041d4500c182240c540166004160040c1d040340d5402c0003c0141c440107012440c01800100081d0460f000100210701003031402400001c0f13481c129440041c446006000b241c407a4041007405000d6408000180b1000005090351123401c5024030300021580e032389030001440b5109100069601101e0a081040c110350f040c051640091341501c00c802c19428450998460060148110180c549062048000705440f401401c018100f0710002801000e4907601c66540b09d40c000e10034825540a281098015401c010400818050b00a240703041010508098910481801402150301d408108030a0149600090313007111440c1c080c0740ca66031107407501c44100c4200f5 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 910098192 1250 910096942 910096963
    0x9090b0319080307020f160f17100c050c070923010312031e051f0812030a1802060703020d080c03090c0f030304090e061623070f0b0a020309 62
    0x90300400c01604081c580003100a50160307111910300d541e075a581804a05003a0502c2c4080190b004144500f100b150000110209035600c465120424595980b5040c480c003130f0060100302c05030821800d140c03404003150b000640d103005030b00303045180810160381242803000503000842c21940d02c0042482c0b07900100e8a0805028140078a0300301541107490700300914001d15440301c109a2203400443d0f00056044104030104e0800c4401e21140c00c050250b800300040304080201d42c0b02452600090f0803400141000500c0e0321900200e00d15280c0b06075403030242c00f86403030381d0515550800300703500140c60f042c0003481000c0c000c0c0d02400b0038481d00e02008000d41c1000c1c100e1005034ac030500510090780e2000c80c5072007207078804580312044030403110042070560282c0d500400c1c410780b50000e5407008510200e81184245000140042d00c48451003017500c0c881440d04000080b540a83c0f994807518100700000d0810500505800d09030349a2550382c0c185480003201c040321816004030a02020354810000601c44 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 910099442 1250 910098192 910098199
    0x3230c070503070f0b0309101a03060f150f0f090f010f06020c0105030703200c0304240e0108040c0801020d09022d010e040f05151801051503150a030309090b 69
    0x143c2e031030601c8079000011a030007400141c040000103c0d4400000b00540340c0c010780c42c140184194116075040286425902e9401030003401004006901102d16002c8148100e03102c1003103100c440103410501211200410407160450705035070682001d03503034510394144203002e00143c964140d03050105100c240c4915600100c01d651080d210101142c0e042400d903507000210785000500c205103215034002c000c991240e900501c40d400690701b242c60a001c401001034402c1d000d0071060110304200c00b02036452400841c4400a17401e032000c1403180d84151840c1303821900034680d101165441e409403900320f9014404a1a20955071414031f0b0071401d10070800305100c810344440d440629207603941c0380c102c00749500d841810000140e240c800385603102d600141e81c030741c4104404c0101e0700d42000b416103403041603019a0311408180b40d00014400c40c0300c1c01541030380d6000d42604a1051240320480507500060100c08a640d4660300c0d104a649030302c0702650046000f03903100c8001500e4070301c0c200201d400b24441d0070700 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 910100692 1250 910099442 910099453
    0x10c060e0c120705090c18101d060f0d180b0702010915050f010e1308040e01031124070f1220150c0d06150804060f050f060d03230c070503 61
    0x300c0d907601c000c0399071205500420541c0c81c0d60319044050300c1d40350055035542c00b47e0031010010001d0f500c220095209c100501040104005030810402c031401000c04a600e910030030400b50079020820780000300c0b0f9030011a829001040b481e0b031207400802c4110307908070060b0344d01d11071034041c40903a80150111448a44041003542400480d4011018050080e2911039504e88049022448425000081c070340c0c1140c0065200c503210946040c141c03c0c04e20099448900c0e04a0218181c90122100948a48207066a0103074034406464000c19030410314040e5008003040c04000d010a004020358609101a642c40d0180c50b19241909041a11055000101d51340f060b07418124400c1080c4003950041c5030300285170f132a140350446100c003501054100795600b40701c200c01c01000c1c0d0342180d00503004a201e42c4040c8821181b4468640c11100211489115800d99901181c01810900542c4554074040c0c0f4107100314156410340796050614440e40071114100000f80b50030f84a00600000007d072004601601 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 910101942 1250 910100692 910100699
    0x1203030f020a120504140a0b0609090313121e0b0405100b0a0501180b28080f0f092109010e0f0609090a0f0f0b03160b0f09010c060e0c1207 61
    0x621000d0060f450b041c0441e0384070081020f00503003040846c2c02078440d01c121659111145002201031800380d0f8080d00512a040115014000210603101049801c229001c00030b0b180440c0f03508004070303000b81079070310070070152204100c8403142e10610503031401070401422038103003480c080e4034003400c1d005020320907840e04929007100c1d594250400111182444d000328aa00c1c03031000303061a002c951348000003694000451103108000c805c00c41c0c0ca100030000e40001501504241074842c16800c07640755044c550355800103a030348984400343c1c82d00920050111681c01048440140000b0a0000744e17100c140404610f44049603405071801c2d182c450b0035554101c4500701c0001251060017800c1000e0702c00c90509001443c181031990140c89010100d100502c0400b0b0341c0f04215000748100459903010740216103001d49a11905500c600c02c0303942d00c511080c50400e440b0307480d1000e500440c4030a81003102111544000c583e06008940400300a003003d490080300030410080300040508003280282c02c4001c080 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 910103192 1250 910101942 910101947
    0x6030e060f01080712080d02030103030206011d09030d050705070506040506061302041203030e0f01142502071a0c011d0c1206040b28061406090a090207050102040b041203030f020a 79
    0x14112031700d05104248030b9000d407030300481d507002c0d80c021807144510100001050650006007a0304956a621180440140d128080390641e042200e94680700c1d40104174465209017070f0380c0001d03884065440c000341050040e503285400c210054806a40c517900c000103009040c54041c09100003225110320851400d4940790180c214004031540190500d6542c0b9140c100d40401480040030000c614802001118051100c08414090517200b803807c80081ea900e40d81901d54580c2900e0b954115600145202482e1504010380c0900ca116111201c00041c824001d50010900400344404500c3c8000c250004850b040d072450010002030711032040c1740300c171100f40d1780c2000850042d802a41140010885030303900c945210040320700e005490140c8250340742c0691814903590040050321201000700e0781c61140c09003041414000d84041550101c82e0a41c1005000c80c01d60060000b94131030750016050554441803c1f07a1500710b81d00180070700c0c071004070341c000301945403090048407000d121007182001d0308031000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 910104442 1250 910103192 910103203
    0x102010c020d0206060d03450522113402100e1807020a12140a08041106130801050f0408090d02040e060a1409070614030a06090606030e060f0108 64
    0x5801385000250030410b1621450310030500c2e98402301800000c0c40c02c00711100d8040d40c10300d8620f82c0591440054240103940c6503a01c01240c0005201e5a901c031803005e81c81e5880100ca4014541d80c81c6d5650300c121a20290b4800f801300002c142c01d91440d20090761188030018401000112000820b803881d02340140c1c0e03501903ca40102c11490241141c80d0158040f5a0300101c0c10041c0340284210b004010400da8001007540305a40316145208007841324000039100310141c580c84200e030035400e02c10380c0d003018880d04c1030347d5009000d41041601e1000000100d98194080d0404207802c40358004148a2510240281034101c10000c40742c4e1014036080d198134000e4098014103600c500d8041c200102595202d8000900e600804004d07600e840c108440c165000b81488040f05605817090000600d40e4007011a0600444206498204051103031442c0e0103003ea0008018800955543c1c00c08540688a44030310001380450303890008000c0c02d04480d243c0f0740b0314010000c20165462900600034603101042 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 910105692 1250 910104442 910104451
    0x20606040b36100513020f1b07051c1109060907030c0c14070e07020c010c060903210506040606020f030a030e1e15060d020109051c08180a08030f040302091915050102010c020d0206 79
    0x7600c8c6100c0203440c1d0046c1402d000d54032646c0d0002854000b055070200307a072a01801244641c0d40d4103040f404110500c100d5510488207298400000000500c183c1e0194011045100a03441c200b603458503d9650428254620a0f08002641c007442c014421f200170070720220f07084039540c001050044100030000b40703d805100310084c900d40e12009004100350164080200c4035501103103070740c0d040302e454800400500003124420312440c24800000380c400d0003c98110015a00f00d0041e514000c070824054016140d0b10845008070b104120100043c144030103c851010085031010b08103010f00400d0b41d665545001e41050711070a640696000182e80140d60704040f140240c81c003400c03104540d00d050340c0207080c920b4050031807000060404c001c1c0f2800080320107481001ca800b070300800d4582d14141d07501e000b81d201806074850300f008140058901926010742c0042024640c005011000341e1344400d0300d00f03440d000925802000b80a012946c0c080c0200b01101010384010941801800130095035810040c2 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 910106942 1250 910105692 910105717
    0x203060c2517160b0a0902030714010c020402131206150f0b09090c130b04050418170702030c0d0b0a06050913080c01021e0a020606040b36100513020f 66
    0x3101c11251080f9505072110f242c11481135005841c26140c00c501900c08110124801d018240b00030490542200c1e040c0750042042e580d04803800c40c644d003840300951104e41c04805141d405000040c8580360747c4540381c940d0b40f140c0c030003144020400094410b84221504480184880d03140103115038003c1400b80c1e034840c04101c4919046884a00c5c2d284078130300c41c1310760341880c0510b10100416a0312215009000302c2d102070f030307080186581c404c199014021980302c004144405c511440758103004901e01501c41c0b6400102030741c540c00d001c1e01c00250122040b100844100710540b0070004504140d00c5418000c00c01911a6035880c901442c000c0c1d811803a08034010001d45010401c441ca4070001d50544062007042c0e1181092864950300106098101c16184ca0051052800083c0b46080c180a4541540400703807010071701d921050400007800e001c00d45002d80d101c0100d98800c0f4004250202c0328010003001c040d21000500341424800301e0a400804185114010840c60134809012400ca600100160 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 910108192 1250 910106942 910106947
    0x3092f3a031404050906100309021009080f06160f020c220e07150c0609080406091e031115120c090a060e0609040b0a0803030a1a040b1503060406030203060c2517 71
    0x1c0048d401012402d078080e401224100607804460341007003094040c6c9140c20b084800c452401d0844a0b0365003c200c900c49034454020821801043c020700e80c405200c54136005030380844074160701140048041c46110b00000c005040344002160544c41007682c0034009401820700b140c10108003030300b20440038011a0800072041030030000d10006a1201600f10b90100c0b40ca0f5950707130341d603c5c010242d09583c001d84003000c40210000c0b5040d44400700060860740d004031184200c140042c10040341001008000883c5c09040081d983d05c1800d40c94020301c10046868210346810718002403100c1d40d070301e5401c41005d00001e42802d0b03d01d55260800d42e0300003002103401103401d407510340200e03c90030100d52000480b48004410711013514102c1c1c1000c0e49401e130505181c035000b05440208000e4580904208d40c2010041550708456182a0000d50740200c0180c40410110360f2580880e00d801c404440c41c0304d401001044901100b0400800c800e41c0100754513199000c0016920380c1c3c0c2055071034141003010398200 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 910109442 1250 910108192 910108219
    0xe0a031707060e0d031817070312022110050604141c03021005062709121204150b06180f06070303092f3a031404050906 53
    0x4180c212903030198000ca00380315204451100c2651050101240340110f42403034401080c02000d010100c1d86c20b40c21024071103016542800f500619445400240d00b00320544000e084042c1550004000c2020341311442e0854a01c00d03040b224403c10060304204501580446c200310705d6072842c003a2070035200e83d2a0001c0e07541940c200020141d4881415144080c000540c83e8002d041e000301310120800d90108082c080e650301c8008208400050b50014401c0c3c40e80b01640035105000300c840e5a622246140407070302c0e41c0c030040800e900c294020000481c1000d034041c08002c20400c0c000d003944a00507960205000e1a0042d80008016014407120070205045400901040f59a1810844410600039044c541d840906050040c058645140c007035811040c059503c1044c001d20038412803500300700c40748240700790b13481000f00a0b14028400c41c682e1003c00c0710202071441c0404095501c1010008075000346141342c4c5240280a0110510585c0c03c070400c140310801641c0c5505012543c03010741280c2c000c0c0901c50 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 910110692 1250 910109442 910109483
    0x2d170c070b0f1b1914070603060303050708031b0f0a030e0607021c030b06040312030c0f090501030c0212032a040b07032f0618070302031e030d0c0309120e0a03 70
    0x2182c003c0c0740c02c8207003140700060202c00192403045141c80300a4803019521f40c8815019152107100050010703500b005030501040000001d182c002803c980a03948002a644030300b0b2464001c4483c50800002c0003803c0586184c0500c1080b6607810400003600c480c0c608454047e4484aa048483e6650044100742041c2c0501c44c0c1e201e154003a0b0020801521036440303050203028003003000b00b41c00103e45494590086c0d503011310340c1c0003407425466035000103031400d00c0c00440103400741500c2c2c40154802c0c07002070010b4146c1c1c42c0c007039403180d1400072075000d00218400d403142d101034486d0005001c8100400061104070040d20482d200c458160401c9240740c828199071810fa8204001c00c032107480e010503000c42c04580007041c000c2c01944c4029510268041402003a0744880355440f0003036140d800310301c10312469401070240a002545401c01d07130741032040d4180c1c5182691071915000b000240d03a0034118041000b0420b030709000000c146066010b80318284045040f02d000e03404094880c4070700800441d403014 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 910111942 1250 910110692 910110703
    0xa0e0312070c06050109090b0c091c120807111525020a050c010504080a020f0f1806090c040612050c0c0106030602071406042d170c070b0f1b 62
    0x38140c0015001840e015100411400b14654100da07038a007401c00000e81e0614034060202046c1d00310390310704480e4a508003405540e500c480c00d9107401640021100f1507440301d007000300840b54017850002c0c001c0c0d0050900241080c0000304000103212859507085001039000400c2c0e00100c00d4651000d1103034a03003419002c0b480c0080c40002c20310400d035000802c40641d0200b01140401c1c03043c0c04503034200d0740369001502e0a005602401603154072000c41c07880549410724014880d81d2018000304411000100882c1e03081c080c0c03050002c030740c1c0c903010140a02070405051407903025400e4050a41030a0428000403d6440f240c4641c01450340c4072004039941d00180c004070380041c10148020403940da501d00c2d012001c5d4104030420303038848110400740c41c01c4400c04079450348100e034841c00d11155100e150070100c070650342c40f41e000c8110b80c00d00030000001442c05212a40740304544168580c4644418015a14105007604580c00660080c8488a03100e00b900b402c0d55019000708600751289100740c410586080f = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 910113192 1250 910111942 910111957
    0x1404090615081603020c16080d0e0f061206060403020904120f080c0306010806010e030f16080c0d230303010f0810090506070c03031401090207021005030c0a120b1503090c03060108060a0e03 83
    0x1f4040c00008044000151407201891181c494800c0003141e8420001000c8522841da03400041c2004000d600c40041c0e030403181e00c10340003041d8505041e1280c0108001d03000880e012180e00303802d184146c00c405d0b0003047c0d4400d50700d0640703040501850200c000d080140006400c01d030501040d040031a5184c2c0c00713000103000c22800a01100d080040008031281d80354200011b0303c08070f03100c180b0040380500c00452180c10320f842c0a00030440000d143d6076511099040030310002142c41c210f84218007000c505100850003846003066151029080800260800844030b540403001132529105100058020501c0740d40042d9031b01700100c4414071810141c0c0548500000400400a114004a802e80c05035025091060003035840c6850301d592000c0544071444280c40c07851000a00b402044c58052003890140180308800d10302154008060f00406c03140051711a40c6004000003004000001c00e0400100d0140314045004008552400640c1a118440030700780c050450340b0381d0000e0319600000c20468001 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 910114442 1250 910113192 910113223
    0x50f0d240906050a030f140a050106090f1112010303120e010f05090c011103041505090603070e19060818070f0612050f07021902011404090615081603020c 68
    0x11030200d4055100d1400140c016480c54034908407012400d4105181d4801c00d030380d44081000340d240b540ea102c10000e03044100d10540ca9100c0d01001800195003070003080000c2c0b408000100f60300700d4900c0a0025141c4248580c4405c0000380280000c82408404160440b601030800500c0d200034241210050001d0405540c450b40c00c2840c5141801d610b0307842680304811810541d501d8969400044030300003540c00f0a0b843e203500038441070100205e1104008040065800c01a1078a00c9e000c1c0414402d810071151400421210760034400ca50410400e00041140c840a00d0088142020740c06803d8050160a180401e40c442010120762141041010f002e0074244078044882503990000404c2d10000d8100c0e604603d090401203104403040000c5a0f00900540e00507003c83d94030908207240076502440207a04000800341e0340c0c1c010303901c44401000504641e00c0041582420012044c4140c455503042604002c403041c10030401d004603260b003121414040c500540d84604003082d40f0301d4007000311340441c0d0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 910115692 1250 910114442 910114481
    0x9050c0406031118100e1509150301060b040f090f0b030109050607030f060303080c0702010c1403040801110901140708040b030f0a0c0f02060106120f0c170f010303050f0d 75
    0x5102415540c0c0c0d40800c0c0c12a0610303044c550099000b03015140a0321040000c81d0184002d1005000c0c481c1403e42c404904464401109440c000040680b0003e03607a220340800031a0111680d0300b402e01948001d0f200500f2140d152501e08010703104142291b10031442001c0e0b80b00045a61009550064010904014024085d0700500e0800d036880c0c078400e88a42000c207260900b4540d80e81d086006490442c7d4041e2500c0f07441e9501c210280c2d00300d44c4030000c00c80c104194a424040080c00307010001e038078194004010340e1141c0c1000107580c03c56000c031080441c82c000c05c0c443d022050303a02c0000800c2c1da49113415400d480e41c0040ca4119100c1c00740b030b0404042c0c15404010001c08030303040c0c15250b1049540c100180b0603d91112703000d9804c08541610380300160400401808094000d8241c0030140742c1044c40014078412103400002194003500030710b000580848980740c0300c00426445076800c008a090800d01e15451590043c0142c40344a001b04164403010861b2030068200b40d20032807003c48040048031 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 910116942 1250 910115692 910115699
    0x3020d020d0e160f050603010323060901050912030103120c15020a03150509040209150f1207030210110703060f0b0315040c080a17070606180f1a030a0609050c0406 72
    0x80d120340c001c801000400c3e05400c4005003d101c40348125044610142c859481c40c0d003140c1700c943c07211b0083c0d503020100002c0d0b420010180c0300c00f001120710030b01e030b85000020942807413903c05d800e003405a5502e40c0141c405000510103c1e41d1052840000407040c103090001d0401450f001400ca8400840322a81c14800306400000ca17270160041040d2420755102040c1031074a482c1041450602524069086092000001c0b50010a4802c030181c00d0401002c500c000d10010b0005031000c540c60020342d00d6074018050800c00c6080a8505421000e030904000020018030000f107a0f0f2080c0798032001d00100d40340e040c104506038a640c4072100704100034041e01c0500c00c44c50143c0d07c202c00260b03022100042d84c444002480030380480d10b01e40300c5e030b8040000f1410600c1c41e0110341c11500203c0e030507100156590301c0017400c1403200003c1c02c0d41d5050088089805100b0a003a40112080a2080901d601e50040c01401035a40800c0714110f40e07501010001d1040d946e070408038a08a00d440c0c0503500146402e8011 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 910118192 1250 910116942 910116971
    0x20f0d0b120f0714042906090a031406060d031d06040902040602010c02100612020f0f0303030717060102061302041d030d020c010609060501080610141b0d020a1203020d020d 76
    0x8030142d40c0c0d4809183c048001c0a400c0c80119502180308886100d45c04140e50024400b0302032041d92100014401f600f0032440300c000802c1c0340e1659004030303140c907d0f00c0c0b00390b00960b000b4402c00b5404041100c00402c5400f840c4c9001e44004881e17020320041c88c000d240700c00900c1e40c6040a44001d08880c6000310344441e15000c0180c003c0c642211080701503c12031000c0043e1000364091002600c000401346000c600095092203440204d5990840e800b034010400404e994400b000950721070081507440c1e40c0404652001c0d2800d2940103070145046400c84003c101001c0c015418030000d541d41650300042c2c150080400030154011400040c203180000103508480605035000380240451585c000c102e116502d400f10402c80e203c034860540841c2003c00043c2c51450f0035210b5560720525410022075803c1e1070a424031482d030180707560300c0324040c1c044440c80d50000100f00c00094804180010076084900c1e80b521318010300d40d25954010150002003114400d100d41c2c0503248a200e00d00c83c00d000420701e54818 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 910119442 1250 910118192 910118203
    0x6090b0a06031a09030d0f1d21090a17030d0e06070230131223030307020604110d0203060408070b101401050d1404050606040c03020f0d0b120f 63
    0xb62050b40400380c82e0340e43e883d241c440c1280034610031002540380013411078020b805010003440980348503030f55840d000119101c503404124070804c40b0019040040300c000b084030050703c101c403012407508800e01141c082d45d11801046019038141580d042e4024000e18055403851240300034184070242000742c40304006030f00050090042c0c020b45c003900c85001804c120844002c00740c140702800202c0317035a220070404008a00509800b0560000a5601510b81140c01d480c1d81c0143c0049404038000e0a009400f441d800ea842107100b080b12000d1461400c2c94079000356076650281000c4c210000007222480150740e6548500105035020b41507451602d09130030f0001c00d40d04100130a07141700244d1400991400c0c80e410a44094401c6214080c0b0300d05c0c515401120b103034103d0a04020300607520701b4000c40c18040c0140240c4035501c20001802c007440c0488c244000d4405034411070080c14014001e061641d00c1170020b4a20b48480610002800c203651000940c00c1e000da150844118014030408002201c8003082 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 910120692 1250 910119442 910119449
    0xa140c0d0e1f020c09090307171903020403081e25060501050108040503040e040c051507030906031e0e07030605090f06010626060d080d06060221120406090b0a06 71
    0x2410300b4440b2001d00311410321080a909a001030f0000034220355246848214280c0004143c0d08590820009590351031146800507101c2c51046804038001000341812540e4541006290be000c1d411700d49035646080b1a8010822540a260032504604c01580c40450586103800180346c0a14001c01c202c10100c58841c44041007030301c06504000012a0755405400d16501490307200004510f010318003034620038500340140048600400c040000200c0395118014000360b5a031500109556000c54034025101d41e1007540034106050408200200c0b1400c500c21202c5030440d019404a54042684042400c00072140c100400c00381c50102881200d02b000600742c031500e0004000c98046903290b000598011a80c2940400e509007003424900b02c410111a9803604158050020400c0103601e90b01c10005400000b07400c00c0c0113944031000c010071030b410031200c0421741140c2c175014500242c400b2000c200b4410180c20f8400303c141000401d007081100c4d800f068449411000f203941c541403868a02019045510 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 910121942 1250 910120692 910120699
    0x7110108091f060f0518070f0203160821092a130209090112020306040305070303090b010603020a20030406180905090607030b03031c0507230c010e030f0a140c0d0e 72
    0x44c0003254506040d000691203100f821550b0100e65500d850031560714070304101c0c0c0004c40c041806030400200000050b45200c138400e45000d5282c9035a00308480241c200c545888a019000c4c0c0d06000aaa4001c24980c00f00c9203038001d402006260107055801c8021280b4540c0d4214044418200540801d68040d000b560000c460300f18031a640e40c40c00c540f4a004401e00607516800110104000034014802010700c83c0c800c2c00c001c80c8103001a00e0b600c8003810300340e205801003030300040d01c0d00e40785902a000701000e6812507500042e241c2c444104980d280568011841409203041a21501d4072110304400002c240c004014001c503c0c0945085407100010359994000c44e041803140243c42c68088260703240d04040e840c0ca07100403000104c2d00d03130190401030120b0050104543c2112504220020f9140c80303207109083d9941d0f118182c80109003110f035102c0180d07860f9003003401200c81058a01c02140c0325007103180b81c00e214000600c5008032240c0310301440c1c10020700c96115488981c4e604282d40c01c00440048 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 910123192 1250 910121942 910121969
    0x12031e06031e030509010309020409081908070c0807060c18060c0501150e06041d031201030b160c081e0a0210150f0302090910060303080f06010507110108091f06 71
    0x4511004602c1e242980140420428452000c0c41d510030b9008001c45800100081800750103a11168002d40c000d42d040c4c6181d050640054031800e40244c035043c0c10a00c00e1405008a00c03143e00c0d5441d05009000c1c005007110380325225442c04074850078840361792a99003e070382070200d542c50074050402610382c24100c52a5084c2010f6a171403910024891040741d07068080c00107a0b6030f030141004000c0080c25064007022080d01103642100b90100003170885000c41c5001c82e0780e15419404d002e2080300c001040e04a082c000c0f40701c080001c90703111118242081d4440c04140d144d05d2103c0140018005c2110b110f00c15100126100741c0755030303000a000600c80840042048020442c446000b41d07a0854051b03115498002c0d001003006050401d1318590050000041d02c800042280da40c9099030440e900640c0013400d401e0900000b0120043c1d031075009038003401c0040c500709060760b50701c16035988452842e0502044400007501008184096501d80c030202e0110001005400340e0400141030500404000d035000 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 910124442 1250 910123192 910123223
    0x204051008070915051002012004050a08030a0f0c05010b0603040f060f0509070b070804051203040e01091b030b03031b010e121e091f0e040e061312031e0603 69
    0x1d511a400550301c00c00384107084d01d0700b03103010300495010b8001103e045660b24101d010000203050f0500b42c0d0044d44401003a522860402000702d210016000440c19400410041c101140c004048289280060500b01004000da041c0a03005080d03c80d403032500300070300000b08070400040341d20090300c0620a0340d00308074509010407090100c2d4011281400c56038070966041c040c219403c4003030950b4a20800c03115142030740b2000407030340d45039074046a1060ba5001107014401d2551502100b409054a61010800a043c407445126562014201442032503a125044d181986051045488800f0700c40d0510680941500c2158000c1183d500109014000d08c2c1d4000c8a07100d4580c200c07040708031004040e20140c05003500103035041d440300c4181d69000110b1030242d06000300c598441c540403103050303c60b00d4074100404180000e5404514900660b6040b8808024107074020519034000d0319000f0613004440c00f00d1500c150000c18640a090402c8000d146844819100075005401980c1c40b81800c250b15019 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 910125692 1250 910124442 910124459
    0x712030c08160c1502040b0c0f06160909270c03020907090302130b01020120130603060b0313050c0d05010518010207120810050901090203040b010e09030f0d09020405100807 76
    0x2c0c6046110009050b00201d02c0429100c035114031520092070001403825646080c545c0381c170342c800c40310358605401c44210079000e9081440020780c42090302002e0b144440c05a1002071002409001c5c0d6451955070b03c490300480c107091020300130205c401580d9004c96080f542003090180783c8030700c4101e02c05c400c99000079240500c00c00241c01100c2c1e0103171043e26101c0355a00341f80c004d0842400060304541d680c1a0400f2603400c400c0040c0110940130740001c1d40c1d60003201c409055000c83c1d400100a140c00c044082040790002402c072940603040b01001e0310b00010600d0240d081c00c1c0d0707500c086a400184007200c003017440419030010307005070141c0c00c0c28098003190403996401e1380220507020f0b021150303012800d05c1e00f60144000960160342d405428402540360300000d004500c080e0402c001c80c45e8003008120800040580807805040d048000b6009031504a031115601e00c10b91303500048a41c0085001c0c03050340a2a04615130300c5a004009120601e00444450340394205031045090501c9103941c005001c25 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 910126942 1250 910125692 910125721
    0x1b03240b121b030a0c321e010e040f062d2c04200d170702010e0a06020105070815091b1306030509010605120a03030902060712030c08 59
    0x901c0c1d0400303080100341811000300c1c038580c0261502e03054080c000c80340b4001020015000080c214460341c1c402c9500540303445040c061070341a8501c003e640c9004500089544030b02c1145440c0641d012690a450003190040b24800c004030b021a0f046410a4100440c800a41c2c01c1042a1130070503480000031107080e0803801c0c1c14000701e4244100c40c4410002800f40c0c00010840d0a24408da0181618030a03035080e1310003903051800c90b015101550742004042c80005146401400d20a00303c45815100c8160b4480100d070003850304181420703c100107020411a4001d000e40b02000070010300306000b036540c50401a0180c00100d403a00005060000024038000340390504401a01018103540340d42d6950f00c460391341c1405601c800c11046030041c841c1d801c099820f0800c89014208694010685090513000a400d603002e0350480741c8181d0100b103401881c42400100c8600681d018a000702d800802c0740041075043c4100080039090881c40407500c055640c00d50044030016800c1d50741c4001aa079210161b40a25 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 910128192 1250 910126942 910126969
    0x60b03060124020102121f1509030c060e09160e040e030406081803030a02030a020904091220030f07022b0c0b0306030d0e0406150e090702030301050d1b03240b 70
    0x70350802180d003940809447c030349006d000b1803415000603241c0c054442d4020072000d020002810301c000900c200300e1400c01520003405c01b81000c80807100309800040c40ba640042020350b06010140a40700710500c140303140300c20302c00c000c1c00c01c000502401c4007040c1c4a074014028040450103400105203000314406495214251031b0000d1810358030b400240c40040d40c0040c1c9403407842e0b45c003401800440e5803140700c4d80b001e0030303c1a01007000901c91000050803004503141c0c1c6c440d0403203203019221031050300442151071800d203150030f0540d1045544001904821444582d810701c24001c0071004c1b071201488a4030b80c1c60f41c041c07818459200e0785c07619000c1c4540b00446680c1d4060b042901813003541d0f800b950018080060041010800685810101c21400d401c06095000200b18141401190600d0348105400411620103980b4560401000c51411000305000415440200a03004840000002001c000e07562200c800c3c546a17101c04c07230700030868144220000b02c80385070401500862510b8070054022 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 910129442 1250 910128192 910128217
    0x5070b0c0a061104091826120c070602030412140a05040e0a06090e0c0f0301090201080115020f010c1d040c09140d06020f0a1106010803070f060b03060124020102 71
    0x910070140c1da4007014040c8250282400c500600000c5810f5505000741c0e55106102003034194800c0c010f0902034000c00100d04100320404c248848010764941c0e4104485014500c66060302103600c82ca905442c1901c1014000303081caa1012060008120200e5400560700e00a95192100c0040c43c0b000d1898a1003080380450200d070080100b00201c0c480380c108150712100c01c0c00006901580c40104100340c5142044030075107034100d215004c045141980d513041e0203140c2607008008034021540040d04001040c040c2007801c000842401171051700c208072008900f42d58000900c0f0400e00ca06002d040b00102d0481410384801020507000d503801c2610500b82e400540c0c1d0303035490046103030005904207001100034031900541040780180c04684540001c0c4450300340038800603564500c0b500020240c0501c03d80707959a80c0c114100402140c10b00009452500340c00c50001c0c40700e05840d00c2e200d401842c1d00b40130a601406082c00005501e020012206c600e4590800f40c4502610181c0b0304038200d2040c05c0c2d01411 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 910130692 1250 910129442 910129453
    0x1c02060c06071103091806040e01090309080d0302030919170414130203070909150305030f090a0e040c0e060402161407081501031202030903070902030105180114041a0d03050705070b0c 81
    0x386103185141980c0040d002340c8006110311500e40ba190075a10940e400750003154001d40c6c10843d41d8010040c030b1000b20500d150441c15806d02e01e0041d6110740740520200801c10112030107c050100404803800f03050f55020016940d90303a40c100300c6924001805402d1710902d00711000200ea00c400f07008581c465000b42e0341d80403505081610340c50040c120200622543c102210012000580420051690b04881c45041c0d450f001848200400ca241070780000703211801410610000370300800002058400c0e41e00030200c035654903404035009003d050f49541d2060948408001400040d00c98403105030005e2042d1055a9113a030b84141e41e034115200b18400c00740440c00104041012842202c44524092058a00d02105180000e10b001d819420407120300740e000004014900d0b140b0a030700b07403001d09080c02c0c1074a507141c600110070340610b072039040740213a446913415142007a4910700e9460109004000010b80c1d450780c103005025800215007100c041c482c03441c1c0419141001416180301c01c108400910 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 910131942 1250 910130692 910130719
    0x80f090c090702120406110c0a081903030906020f0c010e0708120d020403081c0f09030518040f06090b0414160c1a130b0f0f061c02060c0607110309 65
    0x610380c0d8001d102d0001c5001c1c65680005803104100100020084c0d642c075440da694181d00307030608000c012512a881813003000c00030020360310301051030001500304100d0f2242d40902d03820180c003d803181200040100b440011548044660000500110600071000700850f41c0d6018031250b441d005400342c61002c1e0301c4144554210007401e0020700d03c001c0c238501c000d810142d8a07a28040340c1d80250820800d000116820a90304440500c80c130511030203c40818004211141c0f00688548503006440038800031164411000ea01c4503000164080d48489040200c03946da8070703040e00104031225240b0310880c100310703040340ca45420079030bc180121044030703905100c41e1107404140ea506469207800c81c0c1c542103110300c2c0b032070785800c03101c50318440c803890151000810040c0c5401d424403200140300c0d659207004401441612815030106551045040c0c501c02c5043d003020103c80f0207401c907840c5c005d500400000b66102c01c88004181c00b4041e5000380c40d54014283c10264a03504d9004504a458100c1c103914440b2 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 910133192 1250 910131942 910131949
    0x141e210f0f0a0c03090812040210090303120504030c0b09010c12020906091207030c0b040e180a031101090b01030c30020405070c0b0405151501050405060307030228080f090c 76
    0x4021050b02d0a00145c000d2580d91424030a800038502c0d00d06600c42c520030001541802e48041c0301400c070383d107032881c401401c4da94050036081c10903511040603a0368600040c05c042c010406118034641100100d40240b03810300301e240c0641000310003d00003030071003801f062079251103000b902c19204001341154109122031092181c0302c5585d0f1a6089241f10324940000802c2c0740d03070740c1c54028004603010150380354282a11a01c140002400900250b03140c0113146080d0b00010510340c0740c0603414540b07100c1801410724542e02500c4c000c00040c20150981e80000200000c0c4e00804c000c8401c81c0c1c18046004035000904246d1400c400700000c2d445181d00412801840c190b40601e900a600781045c020401071521052003200c42124105c0f5558410010042031107001407201e91301202c84c5014076400096038000820314082c0b8070409000300d6022010a088a009805540a1082232491911500320700341da40e09d07041d0414080341000c81c031300001040c01e08881101c40c0b4443d4421900401a004403607050 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 910134442 1250 910133192 910133201
    0x141507031d190c0b07050f010b0109120b09010e0f100b0f011202070f150e060a1107030819110706050c03040f080d0615020a050f0d141e210f0f0a 64
    0x12141e003410108085880c040c004085c0c40f00740d0080005105845e6609843c0b400c44001455050500500c444100030703e02064102446195100081c081d454480c0d1107400d003d843ca0a00c5210716001c0c16408061446002a8000c900c0003c03a80901c644107140b000d2207403002880c010180010580c00c2e202d4610213080c1c0041c025180b00d10310300500b072403868940340c0c60314050014015000f6102c10190b84200010080582c1014260704108408043c3c104955018803581d000201403100100029800e6080b0398603852480d0100002031048540855880b005607005100890b1524507001c0426443c1d81501c040e03074499a0b01c6803040110394101e4076151040e07048480300589803038541d400440c0101442c5c40b080c40c20a941d0b0010030449507646019424106a0010500303503511000401d40c44640c080340c5000c8031707441ca4000d180d480d4a000504070035a07290007620294a280010f5050f03885034041464240101d0340700b110300503511543d0f0032220084080c1d0300d85c419804640040f030102c8406500 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 910135692 1250 910134442 910134493
    0x305030612070e070e0111070e010510021507110d02120d0b0d0f06051e0606090d0c15050d05090c032a04140129030a09141507031d 58
    0x202d4080a0b558036546070014001c668060002e41d5507151038559503044040030a2560b03100300500302c1d01e410302d0700858150388144219031294102008001501d8000d00c0400426085406e844c0810324004801030300c003102c10b0140280510421602900c014404140d003117102e220754244501c0d000741060a440501a04000715900680b43d1a4901c005117103040d1840d025845a0400300b40d601e4203104126401c1800b0f2210182c4021910800a00c2e40e190710480c0c88880d070403203130f02c111103159081980c02c6480e203230450079200c91018030000b540c036045006003083d44410403042c0441d0380d81c2d105450f100e030800e118280e0140c3c070020139402042c0c80c0c1480d21075010396100c00030703480300700340400602903940c547c4c14607a00300e45050044c800072030030425030300c0305080c80100e0101e0120001c548600350b220041590708469900e0401508000c010320706401d20081c18400c442111520b0180b514540c0300560fa0000828078084041400d60403011140309031042210103014088800c90301030500c20800300 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 910136942 1250 910135692 910135729
    0x509060d05120d0e010e1f020906040e10080708010504020901060c0809041e0c0c050f0607080417070f03022a060a050c0a080a020a1511040303030c0c0804091e0903050306 75
    0x4444d04c450040901c50301a0020707011004000f2041103480f01da00d089114036040489038010403803400c003610f501d0115030445020410340202036446541c800399000c04d580151405003c0c8210002d8000e105401260043e80202d401e4101c0741d9880c2803c1e41c1003c40307100c00030041c29090050081c4d0746007039400301e5000b88011020780512101c01001c001111210b016010124446402000504c2010001803518140c101c00600550a000801030841c407030040c0014168070780041c60070f90f6144800d042c2d4114960040b01722007107130214a006900c42c0d032101e14001e50445000412001d1a11524000c40b800c0c101030b1407585400c13181c40c030441c1d5540c407958595045200b1300c810714000032038a200503c0100140d0780640b11005082c500126520201c03808441094203201d41060a0341070102120102c907858240002c04600a440c03d440d004084140940346400c0810005030400154003c03110280f11445090302005014044400f29440c0d80c0d00500010000d10008405040c03016484c2c05102400c0d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 910138192 1250 910136942 910136951
    0xa1407030f081303060c02030c010e010c0e1203120705030105030f01090206180a170304060215160c0203150103120f0323040807050136030f08070e09040c0509060d05120d 75
    0x13030300c1e1807046e01c00010720368006900001d0088008402031041103600d40181c4000e00c0300440a28004003c030207010340c118414000b0001c85110360030200b085505001d1040f00b042c5c1c29241461010b00150000d01c01c1c80c0c020300850720030340c400c600c0600c101c205440c3d0041c4001c0c1441c0e9220404000c41ca00c6031a03898004001907808124030200900306da0100318440000c41d900c9081c910001e041c1b0742c800031400400051101400406410305021044940940c64003c202e0485400000d1038100500988802006042e00100c1448081c5241521010050300e4540d8402140f200c1203080b250055040350300711807107000685441ea00000b03441c1d0000d014000042c2005d005842d000e0849070000c3c0314402404c0751125a03d410712030524100c10b1098480170751000c140c0c403528060074000c030b04080c8500b04005803001485944c06900014200340700a011183c0524007403402d951843d207280111440341d010341000945030f2070080c9103800404d42c000007230810488200c108124036000301c7d2200c1c4084d501c6 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 910139442 1250 910138192 910138199
    0x10207021201050915010f05220203042a0509010b0309390105210c16052103010803040b07050c180438090a0606080a1407030f0813 58
    0x8a440103941d2040320400024a81400c003011850203000c1d07090b81851310410801000545807481c451070484000f91140d5421003410410030880c0b5510143d2010b080d407010040c803040c01408012500c10340030103240d1085002101c441d500c0700e814a0300c50386034852a46c8005102d8040f10030051a00460303810201c55480100c1340e01c107180d0001e14080c126410305080c00b5284c4562501c0203a003200b1074203080440c507080c6038100029040d072048c0e05018000000c1000b00e541c00c42d000c8103c403200b0500d082e44081215442c80d00307903102c00c0c2c0c014009103d00410056600c49505110899040740e40440086203050f2519100c58410f80008030151140d00a600d22024151110001c4d010961000d242d507040c5d40c5070a140802080100602c000029036083c030351b0b5000c3c034000405182c45020705100800c203503941c000c1111300c1d00c05940340080c0058102400060742e148009181e561451007150101403190800700030640e940c0c1c942c4809402250b181719064003044005009004d9030120540c9240d00d41e40303 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 910140692 1250 910139442 910139449
    0x20103090227041208270f0f070317041202010804032102030601200c1c0c030303020408060a0212073506010e030c0315270c011101051605030901020702 67
    0x90b00880c004807031100d5001c1000f080030049507024400c48900380715044d821704a02020721a110403c003060b1200910140034012041003101c500009518412a04c1e10444462030646070000c620040340c000d40c1c00003200b030000c42c1150650307040d202c0c071007035840c0350a40035001140c20039806003040d014404c0c1c900d440c1c4041a482a1602e440ea180b2500169480c10300c0070005003110480c0303c400d515282d150500741c2d00b80c42c0c003155a2200520850301003c8820300340c406100c25008101c0001c004c80e404040c00810150141c0180c0116400031080d05e10070f0751250341503001c0c2e20807448016421004c8a00040c0050701038114900140c1d45c90420782c1d5080c076880e4420114a40c01500d12403a00c420b00200074080d80c3c45820f20311944000d070082e0a000c80d0940210303668011450141014481100004021814a01c0410b004c040001c4a01c2c8518040070081500c07884404030050004900c2c89e4461414141401018064501030245d00080d0f02c881c0320481e241d41001d0902c2c40a55001c1110401695 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 910141942 1250 910140692 910140739
    0x1618060609120b1b1305010e090402090c13091409160303050304170c0a0515010501050711040f02070b041214190c050313090f050108010903080f0c041a030a0f02160201030902 77
    0x91440e5040341c0d090b0410001420b1322302d4034500d41d489030424030108070040c0c41c0d49010b80d800c001040c14042d201e8458207180c010311106a0405181b0341d18005140c12084a901d9250703014880382000d85140b40c000c000f15260880c80f500016000c24801c0012600080d0302103401c4a81c05040c4811501b402c090042d01400c0941052056500380d105480c1d88c1d0700c6050314011140100b0007400e00514280741c50f41c0e2000b81c05103280803036210700c1d500c2c9000310368a4261b80449200c0c591240340da55140c506480c000b50003050008000b000141c880e60440b04405c0960122401203041444c900c0c07103400d09160803a02205071802c100c41c43e0000744480244080e2600c1c1c601d000c0c040013003022501c41d01101000303007200c0050b4400c0110b6030400e582c1c500842c2d044480c054200c002412070f000142d441d0703080481c1522544d448101c04159076016520240140d8001c1c1d801040307070359004c0c010280c03400c000d50240d0142055900d820700500501e2801580258408460248042d001910205d10300c4000340750364 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 910143192 1250 910141942 910141957
    0x3071220060f071d0405040f06090b09010b10080105040c0c1203020408011a0a0303120908030c0309010c111c140f0702011404060806121618060609120b1b 68
    0xd80c80707901030040520781000d08036404581403619801e052641000f4504e440c0610746118061a503880c08a020300040c040200203203604072000b8800003820340b91003520428201c42a042c694a402d1036011707a03290031503a03000741c1d401ca5651411283d00b082c00f000010140035416509103d122070850b000900c44000e600d5a90550b5200161102c1c5840e03045400d54029031101ca81040c00000c601c101945c031500004183c941620b0b0152503100b6a1003003e000b046443c00103400c900e004410401c00b0707cbc0c0c21000b1440741143c500244990003440e04291821404030111503c1c40e0000300c2d8158280003005007810146181d49044611040b62000c004101d60042d200401078150000f01603066503040144415418241d442c0c1c14545460120001c0040d440034103210300c10300454001e81420381d8100f00c014030009070315800503541d664031a1255001c216103060b1141d900c1c10b25000041c46802026601c04880c4002503807042d00792541c0ea0020098401000404941d00d03c291213944100c0206c01781015 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 910144442 1250 910143192 910143257
    0xc010507030209040b010c021e060c0a380103020427060507080606270607080c0c040b030f0a020d08070b1003060f0c02030a0e0303090d0305120711030712 68
    0xf078071011410300081e503020000c240e0520801c00d889000603119010003500398156080114001241100000e0b0365114000d4000201d1090402023018014a16100502101c1d070080b00180c10714482c4c48851064002d24980550901d40001040942059088070400020986050580c0250f0550342d0134540c200e50701c199440c039540c20412024503040701c94030b0303044541103540c40d0402d89906c030251010316100602459080200011100b1601c5042c107550070641d003c1c4155454543c41030400390340e0320000300c1042c401e50400d204020581008032b016040c00c62507801a1110405a03000c1c4490300c000d500c000c8401c1442000400701058100351414040c9a540d501708100c41d24605080060318450300380750360310340e24001d84000000e030000b00701c501050040c2464910030031340000103420760040c503600c0c50b04001c03070079082010990b001009249202078155041c84a40303400904403820307003080403240d12650007005904007250040d150700511190510b00342c440343c00055054080031880c005034020 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 910145692 1250 910144442 910144447
    0x30f02011506051e27090108012a0203040506040305010b0f011b0f14010e0a1403090109050d150f09020a17070501050708091c02010e030c0a1e0806070f08090d09090e030c0105070302 80
    0x9162406c5c00b022401050720500901c00328440360400c0c031032400700c502e0b2401d60381070f0710401503121802030044d14024840101a20745980c3d990620b9400781c00b1080306284104480c140e403190a6000c1d400303004aa61190714002503000301c030303a00c2100345c4005070380503954101c420a00f490800400d01503551044012070107000880c9007884c042042901e9184005029001840f003c0341c142d0740040074200312841254400c1040480b8200004c0141c01c41680808a90501c00d07003204152190700440c03603d034400d660b10518540d54502c01031b0801c280001001d5560000d080c2041107600c104090903c66008415842c90082d42400007241d1540311001090391001c102c103010190768200000719150030040d000703442e4942c0d02200094120794a030081d01210b86141c100e104000d4030b42c0c2c042001424070b80084880030304111001400d00c4140e50303030142c000307920940000e103100b134007241462058005031641802e49082120725400360800352807044061000784501c030760000c0d00b4040d5038040c0186480069 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 910146942 1250 910145692 910145767
    0x109030206011d060103021c0504031e02070b09040209030f060a06030b0105040c0f120f1e05070207060806060702131a040c03230601031503030f02011506051e 70
    0xc1c140300d01640300c030480f8080410344041e00d03400360241d154088000d00e401a0f41d0f100101c611003c40300014076580da0075207071400b0071007056084141c01c9080c54421242c09032402c0800400c0f40e03240c22038022503d1001c001d100503000c13400e00fa0050f04202ea0014103035422003c9185501d80b0b8908110384610390356407262010018444200c041501402c015502448686004d010152081c41551880700810414a2501c4a4480a540110350768408403100b40f100040420718401c410181c08030210720f4a1500380803074222400001d52078101c85042d122b40c000d9a40d0b40e801c014194105000c2070760082d000b20451058850035200345000d022a18800c084c0080024041c8000c0b1030201c0c0074a81818030308100661082d000e88400004110040380ca0404d503920000120050140450708004907101744038003108160304449101140c0c0e0899000304011453354a100e100d2800f6440f8a201045c0100086070481d0301c842031600c100c4a80d070b643c00d8584861494911781d0310000c91400b4010403100c55400 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 910148192 1250 910146942 910146947
    0xa060c2d0e0f030c1e060f03010e0703060302150c15160e010206060123090a060206090f070f0b0304050106180f050c040b190e1003050f0603070e07030f020702040c02010903 76
    0x54050010582e01e808821100c6400310f65906441c41000b0f108680307400c184212080140b00905410f40301a0400742c407000351101880043d0428000d00d041c4500360380006100c03c0c46846400c04503038000700fa550320040d4105e00040554002450310013113001c1c240c01b2451007001c035074406008401d041514005011242e00040031250300c0f03a240c81c11500320506016441c0c3c6d00804044c90f001c40510501101c0d038810501e00d60314450410611382080d180c039400105546c0102d44c0351f20036811142580d090300030070240a911901031b40180c020041e140709090140065801c05958820f100300c1c0009095502d6042000108011500c8107421640321105500f036410380d030040b260003585540c4c10b1400c2038200281c4240d540126116020884800180089514842ca418405030030001e0480600d420003c07800801030315080301c840b118225201d001c1000c9050009810003203035a0100d502102d074481400403009820038000d5103220075001d00101000d44c0c2d56100b1448504201d40002a110700303580f402 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 910149442 1250 910148192 910148207
    0x3090d03030f0920150306041802150703140a020a030c08130f0501030c02010204050a05060c03120f18030a08150a031a010e18150406090f12030605120a060c2d 70
    0x9500030844910507a00d17800c03803e401d994201e00101e501140856070148181c03114261f01e00c001c0d502402c9042d6551006005800500049000340e1b6044001110110501340e0740c42070040140040c1d0010035440b0100b407081c20380000e0907101e025590720708056810070704100001a08030705100c0c0305080081015603058440c2403074085444c0020b40c02d183c41e0500041d588940c4e41301e81401180005000c00c0100002d0044401e1030b20040c440b454541000007201c0001e4804070360301a07449002118843d540300380007054541101c0a9a604800c41d580c903e900224003108502e2250020709106001c00040e90041d07a000c01c40b10394414480c1c11350300d00a0500c0c80c0800160461000d19034180f90f4440e00388001c03481c507940c111452551002601d40d80303040c2d0300801d00c03001d01404001148031900c0401c025501a545248550b170390900255032510b040082802d0b03100541000c07588078000d5a000100940c2001552400b5801e00c1c4004985160b04100da174141c50900d450305001c0a40d0709040c0380d400111 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 910150692 1250 910149442 910149503
    0xc011415120601030803040501090816060c0c08071407082a1215071206031110030510260102030f07020715050708090307030507090b041d03090d03030f09 68
    0x100c0305801d01003062096110704042c04050070400c0c0c001b0004044c0402508844181540070214a9a80c0f01400302403401410b940390840d00c09041c25103012a47d0f10504508040e69000054036107031030481d13941c002041990701008a21030081a10008031840d042c440310b4400b0301820035014040c10741d0b4502600300d980c1c00c541e5038450030ba2010406820301001074100320340c45411464464a445490301074a80c02091702d401e14107903040450203c00c1250701500d04209400a46210021010341c51040c3c06484d42158000183c408481c0100001c05500c01081c41c0900c0400c0c1640510010780c5405007680d0088a00e4100aa2421300f4844800e0b8100410380041c2a83c00b000d9184080b00340c0000c086100f502006410403402140d880d03c6980d00384a400b009503409000c0380e459503690001d070f0003c4c1c0950016144202c1c03034104150703548190584d10313a1002130003a014601d4902c1c510b04000903008803001c260101562550041500b1159205418186006078029840d516880602d60200c2a4074be4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 910151942 1250 910150692 910150699
    0x60301080d050d0204030b01140103050a1103070f0e0402040608180303041a04020136080a170a2006011a090a150203090402210105061e0f0c011415 65
    0x10040010150100d00a0180c40051a00380e5071903c800e079112001c1c1c05141c10207002545003000010302c008036032506800c403040a0301e003800701340c0d40c1800b0003046541b14880c901d0144410000581c000b8482d01d03103a50350001d01d06008100b40820408101241c005400403404a40c00000f03001c184440c12009061501030840110b14515260b90344c801011b020714911081e07045140082011607008403e504903e02c14441c1000004004028003805943e10000003404500c600001044105011542d5080250403001c4840b41851000c524216a40401140750030003101400c3c0d410040130404060081c21a20401440c00d54103000080a0701551142c0074481e444042000366025141c0d0036480c07003155002d00e4502d03207291000d170069086100d20400258081c0c0b0000315100030802c4c03980007102c40c85012113020100e83e01c64060086501c18420074400c0ca0829140001400608000400d00308003a00007160a00505401560968501d56003940850307811100b00328031411180300120701f060045 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 910153192 1250 910151942 910151947
    0x705010e0318040203100306140a29060c010e0f0c100804031205101a03160f0c060e1e01020a0f05130329160909090c0e04050f060903041406 62
    0x701c003008089242c0400c000e000d2074001c80061528407a07210900010354108400f4884220301c20b0313924180c0002203404548942c5820740b48103031a0781070901c0b10341404222580c1e0138069050410050745401c03846100400350f4072500898071070320050040103c005803501c020549201880e01b04550410115082010404141308100119900010011104c600c0200000d02501e40d4040c80461001c00e40000a09104003c20714004140403002148148100c20b480b1084c0705000c0b10858a14142c0c030744800003d13011396002000b00b1450750000c242289150200c0e14500c1f080700103a8a01c640388102011140d50102e03200f15041d03005041e0922040080c0341c5146811802035811071444840c1c003014000c060424080c0f4200d00500400c9041c076a08200b81ca0702d0380c5814810b118a44101500361000181d41e8200000c09146501400e202070303a100000f10b05090400040031040b49008106030388911481c60b444500c0081408013038040d4403500083c541e50382c14030300040c2580e12001c003c5805030004 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 910154442 1250 910153192 910153207
    0xe0d03050a0513030f111e160311090a060f24030c270902030a0501210b310302010b15120a2408010f051e0c0a170a020705010e03 57
    0x8503d126907099240c1420100b81d1240c4600311514104504001c02510a2840c0c019030100e0b000c6131201d8018600040710001061a031041280200e1880010900c0765147c005400d146400c20728950720003109200024503a64504031054064020762103c0301e031040c5440900c503a0040a26580e0755100d09050030700c80c00444008c010105444d00084844199a010303040d4008100600910700500e0134204c1907480c0d041c424107480050600788035008002107840c000c0544682011400d600c0d0310b800403461040340e0354041000c41c0e415020201c4081c515640c00c860907410500240480005002c0e50000031064519001e00000d03102e21400301d45078600a010026100e00c5071240d0301c1e0722109109000c0740582c0300c0b40e400000d500a1094034803151355030110100c1c0d20340055009489120240c0b80900480d101c480b1042c080d002200064803480004400041350706050078010300441801e454804040c10720400c0744264500146d8802049a030006500000e101c801d01584440b032540c0c1c0c0145150500 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 910155692 1250 910154442 910154461
    0x20d0903120509120a030b060309030a02160e160302040e0906061005090d06020d02070c030f021302030103200102030913150b0c1b01030b060703030203040212010612030c1103010e0d03050a05 84
    0x2141c1032183c0c4400d4000031000d00c4175200e82c10443c110000600751944074203100b0003041e201c0e0001c03454440144207031000c050909000b144080b00325a10354140c07204130348800d010303032000444800242081c55020000040c009441c614820b1003240c514001d4070941c01d00e5400c001c1581032008220003040380910080d03080c2e94407036510f00040e81e4000c9005036102d16004421001e8080c114000c1c000c03400d5040000144181949602c08151007220046907070102c0c80b4804007203004c203001c05410018103440c42d4100348103040c0c42094000741401281e04045c0d40c0400594141d00707420703460309201d0725408501462011985040c024140890010307007040d24242982d9510960000c00000c4003058415076503007039019078000e04010002406850b654051821301801035030068900f20f01170b40c2505285007103044180300d02d030290746c0c0c29040c1102c0f51700940c604464640c6820029100d00c414480d11800302d40d001d00c1280c0d071180c0c0b600068003422003c0e00c130203412100d00030540003125040408001605a = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 910156942 1250 910155692 910155703
    0x60b24160c0f03080c0105010605070f060b370b07030203030615090904030e010e0d020906040b01122a020703020f060a050c070b040f0503031c090f06020d0903120509 73
    0xc652400c180c80360310142051000100c2a03441070014540707200c00070007804141d60082c1295900040203101c1030740c4e01c603405c4074582705070440a03122251600c0000d0000340d1580201040c050000c2c202c0c440129500c2e0582d000d821400d803540c02c410095040801100540c940313040080c501944400d0600c016914069100e00c00101024495050050f043e104180240161404040013802c512085c0c641850041d00e141c82c041000c60104051107082002890000c00b03115001d5409841c0300e140f503d41c442888043c045540d502c80c140400d104021024052070301c9450091012450640b4943c6203c0380300020211619101c0000c40d0483c05082c000f6884007103401fa40c00c0c60543c1d6190340d5440307803038040324075000300d420300d242d01e0181c0100000e0100c20000a0001c2c0c801540c420b4401950342c10400d940c0344070f001c0030003c021010900c03c08924141d80e11062400c0d0141918203004480c6540343c604a03405003010482140c0d4446210040c0f5078403281407042012249420080c40c14100316265a40 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 910158192 1250 910156942 910156957
    0x705042309010b07140f01051503060412081005040f06030b0f040506010b1608030711060a0603030905060d0617010504030e0f01051c061e090c1701030305090f060304060b24 76
    0xf000002032000c108207800c0b10882660094000359050324a04405050103800180c400c1d520354105403084040038900860081e0080c2c2d4001022441007500d05001da4012500030581d00303400c2804440013070341ea21907000364100c040d0720440000e503450451030303e0340c1a08809401c086154000b1402c10002590018205055900402c50396464502c81d001c00c10548160140c010070040020080c0280325401410209107000140196501681c45c0f0090000320f030203910000d40014486d04081040e41400b02c006c04070070010900c0030400320380350102c030743d0511500148000c061f03641c0c0f0208018103520600c2101451001c840864507110028002440da000d6480380c45070411506400444505c900c0c0c0c010002840030080d00c001001658008507220300071482503402ca03d0400d90203c00041c401c2040c3c10019880d0021581e1690840e10304441c103030841c01b906604143d00342041c01490380c42402561285101d80c038041500b91a003001c2c0540c003021118800c10095040745c841204003130b40016690300 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 910159442 1250 910158192 910158209
    0x1a13020d051303270909060b090105030f030a110313060f080601020c010f030f060e0702071409041a07021002030a0e25120c09020a0c0317090604030302031806070504230901 76
    0x4921450103845824800d135842100030900d40504ca1b810007003590020309540348101e030903001c0c1d81c3c0d0314420303d502d540c002c0b910071100340c004110340c00d41107014520b4012407403400000c890801001d4481c10403c0c498076008013001c201c1001d0311384081548401026480300d42840a011035421034070000e048904808445030505032600511400d4184544c00360000b000d030300c0d2450056081c0b8000c0652114903c0c000d040401c0070404224610f030800d0401e10340202c1c1e11404000158842c140141074107440503020070118001c1b20b4011000981c0ca0018500681c500c1c1c100103a01ea501304651403400351040d5400e69941001d0a41c22284c6116581a000701d8442c0c0c02d801c001004030780b60000750760416401c0a4503042c40480c0010380603a00405480f4200c1c46911407041c038507040810303035401140c1102c4d406c0403030b4000d800141c00244260007454002083c200800d030041d402a040c2401c00e101103481d50005800031078104110f07503502d00746002c141c07030303100c03981c008419410081021040140a141c20 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 910160692 1250 910159442 910159487
    0x100b040e04031b1a100f03020a03020d050a06020a021c030905070e15030a050a060e0f060703090f050607020d02070902090d02150906040b0304110a0506070201031a13020d051303 78
    0x180c2000310f191a2a1007a07004440c1481040620070310030301a60706403030351022440612404100e0b07a150603d400e00740c0b50000c107960449842c544c200880500e141400f15098000c4540d00400240c0324000b928080d03403290054501c00d0b041c164005080044034003408201801c04d00880301060b00490480b0a03615024515006a626501030100c080f00004c0c010342c0520030580c501042c403801241071021544070f200d0501609611040c1c1c10b59800071900300c841e083c0c00440c00702c0e007480c1c02071b444480a14407407042d9001201064071082e0401008031006005600205032004d0030382d6040c0103c002410040c4411410303c4066004600141c203125402030103190595451503030a02e420060f140181c400824056480d503c1d400c03401c500703800954044641802c183e0301141a031030300551a074242d50300944072034200350454004401401003100c043c40b000c15080308251040d29002c0c000c6e0403140d07030300001603034411010040404890f4004c2c031b408448107034128403600080d405022422041c0c00e49a2150 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 910161942 1250 910160692 910160717
    0x30b09131403091509130b01050d05040c030c0b0304030e03071a1b06070c0611070308040b0a090c060e09150f061308060a0e0c040b0603061e090c03100b040e0403 71
    0x61451242c0f0301c03403642c07040303020303a501011000c0034005100459050310f206601031109030740310083d1052086054081417003400101c1c455902944890784c4907005000203043c455a94407038003031011050300001803044001041109154018604400345e10003500108459840c012090284692660030400e41807800030f43c84000e10703089003400030342d580d8101c162043d50034041030107000780314000c03c112801403c060030300c0140d1103c141030300c03200c98068480b11f40682da1540c901980d9000140041c0d4140d0b41c401c06840032071242125070380a4000313034031011050494801001350700c500080480d101d1198200d000d130496100c3d00c101205204050700c641d5200c00d03096801e0304807400b10340c00209841c41440200300f180d40c03258000200a4110030160740701d000109080c082541d4640c00c02c160801720400100d060350030000c05081d40071111032181e0480c20042d600158020030151910b420340310003c0240800f0044200d1400010301500001501e0180b5290002811910041c07000d01400112607514 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 910163192 1250 910161942 910161983
    0xc0a050c010b04020301060c150203160309050109170d0e03070503040e06010527210d2610030b010b0a0206060d141911010e01090512120c0706030b0913 67
    0x1c0c1005000070f1095482e582c44040081852402c038070b048d11b803040032008600b4985401d108890054070140c05021055412070416000742c81004021102b543d80d50100d00d000c91616500c14020090b0128210340d034114043c2e04106541e02505000e076580c00810158000139000030844088424018070010156180c0700142d80c0c5004154221608440090102e08100c61185030901951b0381111098504400c468004034501e4407070b4900040b80e4031201d404079079940282001c1c1171340c070a071685012450540316101a407040d01507400f1031400c11000014001c00811019035800351104012403402c0555207800250350f01c0c4040c01090103a4040016034050201003813030f00c0f200035003a104554040100341308072071307035240d001c10295405c4600d032996140a6202d07010012107900142e4441c00c0c214140010041020005100d039401d510407011100ca01000343c1000d040f03918000c0380500b030704500e00130b006020369071713507810041c0303e070030200100103009101c6940b01c1182500b184107071800c8020101c20 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 910164442 1250 910163192 910163201
    0x1c0e030714040f0b090c070b13052d07090f0c0e0a03080d06031a040201020f0601080307080f0903062e062c041d0106121205030a0906060905011d0c0a050c01 69
    0x120b41d0030445c0d40c0c3c03c120100c3c004000520a062003140d60322490f641e00d50b188940195001c40041154128650700004e90244225150940c140f8007491050103449120662a0141c00c0e880f000c84191641040e10020b40c0707521030911034172002c0c10009001d898110000b02c0094480c00000c10200010520f041e41c51856030001c809180e200c0d00d174808a681500c0340080e680c1c4111012401803044100301d86800030701242c0136040301c913074034000c0d07060081316903819038180c010030900c3c101e40ba0107001e555100d0342e08100c1345020302101400b282c03180700718101d0800140c0c400510906002c00fa42d2040140d26407142500707084400c3c1e883c84002c492101c10103104800038400f41d0b5a48681084500c40c004000244820588100c0340300800a241d0384480c40000d6800010010704140401c5410403010743c000c03c01194000c00e4803d00094540c150742c0d54004031801a001300c1d600f142d4034030050164058440302c442103080200b8111a8500e011f485507011886503003001010840040350410000c40250030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 910165692 1250 910164442 910164461
    0x501120b1b0f031902030c0d0509070302030607050705010b18060108010e0f010b0a120903110d0311090904031110050403030c02032b060f09020c0c150301050f0a081c0e030714040f 79
    0x415503a031f092100302d2402581010341c41a040c245841d02144490340000340440c11130741d001d006025107944245c400d0b2102d410000080e20595240e030100d260f1039440c42c14902903181c19200200803401c050000620040b416040802ca9401440a00816081034407926044800c01d1210036a109000c4c03004403040000019101d190504022602e01059088042004084201c0086030054140300404074249c0b90710810030103030710740100485403040c10500e2107590311501034200040f80c2100007400c2845c01d04e000001561b150340d01c9091104056150044401190003480150304144030207021842d24210321009141c503081d0141c121205600d80e411000050403010603403000c0640d40c0803031901030b41c4400e2298805005400813031540d0700c1c15211044042080c07404403401c50b03080c40c0c00d0195a520040e0100d034008854040051041410492922021515003510305842c141003000b4000601c19a80140300340c001550601c1991002c3e13011610b480012200030078101c0b03441c0d8919000780b41480 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 910166942 1250 910165692 910165741
    0xa12090801050a1a0d020a052107080d0f080919050c130e01050721180f121e050d05060a05100f080601050909040f03030e010501120b1b0f03 62
    0x102000f6401586900400c410495031084104800c03000c000c01c04900d01c8400d00a40c4041007102c1440340c1c1c200018507c40705200d912103008c080842e500340500d4002e10b60b1103c00d441e440218408499548203c05034000a12420143c00904001880540b104050032040c144071510841d09030030320a081058a0135500c1c060846040d09c0e03500201c0f0f01c0501380c5000e6502480d82040c0100342024424100000c400c220300c8100c2010441d202d0800e40a043c0380c2031514203010400c0814000b1822803064000010300c91140c0340c0305529424005001020903005074076044a00d0f043e48071150b50000e00301c44da41002d00e5000581a5241c50024095008a03044260400316070350072802c1d019001440c0210303802d40703503d4a4444c1d940f40030045030030344241c080035034100481750b011500280c200b00d44208400d1003030401103542c0404006550031580240e1000000210420f80c245c10302034443c802541100c440010601c1901741c40c800e2220a100b4a15240c40500000000a00208241c0d0202c0705940015 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 910168192 1250 910166942 910166951
    0x60519060803090117010b07031202070506070903020301051503101508160e160e010807020a0f11010e0d0809210f1f1a0918150f09030703020a12090801 67
    0x803400c1e180c0d242c0019001070b000c00c1d81d91050180100558800f5812039000300c480d07030301e070101c29a41100c01030001e0240b200309a40034050400024002e1240d2440b0384d10070382d1000c0c7c0c80c03480d5004041c2500c3c405064034011415240074001d10340c0380031520b00d20380120f0103408510039212035000e086201c4a40c2c0441030324058811010047c1500d2984141144e6601c100700e05030303880d514400c03d081c028940d030369408100b6416998040d940a4a603460f4044da1034010327604403a07007603210030580c8182e0b1901280c2081d240070300c0412030340c5c02c008010805075007503d0711000b000040c0e44090540c0715440585124102d08c180101901400c440600d16042202094405608450359400d5441c600724251100400d140010840064414841d12101580412404a150010100340050300c5006040c40065032104480c0c440348070402c11540340d08080503003c00640e80b0384031503071100e154000342103407407190000c0203610042070380062420525500201c4850040d220444242c8210342d0705e40c0104169403d0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 910169442 1250 910168192 910168199
    0x2280b04261902070824041a0a090c1409010902031512060603061b270a0b03060a06051303030503220b1503012906070f12031505060706051906 63
    0x112107208211840540803950078030f81701c0c5c80303d43c3c40d903024940d030086106c0d050741000c980d2842c0c0c035800c0e07800c180900042807111000c40724120b662241128800c0c0c00e1500d5500620030031400c2402440180340340d01c012081180003c0008009141c1807091381106500880841e84d5a0300003581c100f682c4100800d407100780680d00b004146c440c581290340d28401d00882000806001c11a00c505030a00c1070540c42501e40007112800d03000140b102c001540c060b100c440b82070f40d007684940d08004098180f04500507100d140c8201040b540c0c1403640c001000300301060041201c000744d1411a0025aa4142800e5850740d83e4800c031042d044504c0c2d4084184004106009018005070f0082c0b14041c01d030484424800a46400c141420b031152044410300d000941c1600f00100022110154000180100f8035881d00825842d072240c8401114000e4404044070b0029030200c0fa010301c100b07440c0c0751076210185285440e00e000100da5008962018120549800c0041d84581420b400441c6209481300c040000c20345 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 910170692 1250 910169442 910169467
    0xa0e22050117010b0a1202011b02060d0f05010f05060f0715060e0a050708101e080f0f240403080406021201090204140604080601030807020105040b0a02280b0426 71
    0x5682145059503c1c05036244818200400e80c042a1070354006e900165031300700d07401101c10101c590082e01c40c1c09a10210300e4010303640c80004242c2110005004960100c80c90194001c0b180181c1c007041922041c0301c0d00308495119141510910b041160029890300f1460500c00c9544415034080c80b4003601d0a000420b000d05440096030154980c4102002203584d80c20066800d55001d440d41040c203031078503104000184460100c41928610549455203080c1e444000078070340342444031008543e80150240a0212104120b13018035079250404000480c8008080d640e103c0c000540302804020628001805001041e01101d00b42c5102083c4010a0741e920322116000f50418016198884020122007150745451000c2e501a600010b02a014070f0346981d82d07503030b0968480c0300c0880c144142480300058558500c0042c0c0710400058000e4001c5001744001030b060907a00c1020a94000c40000205000c10000c0c65440d030310943c001003003412000c0c04c01007401c25440c1120060050030001a81030392407138 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 910171942 1250 910170692 910170719
    0x611040b2d07171303060212060315010e0c0a090b2b110318120705061905091e0c0409051b03060f1603020415050309070602030a0e220501 61
    0xa0054428900c040d202080342140c2c80355207400340a1a00c092000c41041c4901d0008200c6485040f03100d4960680e05d40c1c0e040c0903608900b4040c00c0f5000110304005060409003e40070020b4031502000000b5810000201d411190103042c03c40740d01d0000c80c030200e000d0700402d05200030b440031030780c55600d80c0c40d40c5000015203c0b68002d03d1000012444145080000e240512220b080c507000034641181e99040c3c1c0100440ca00c050500320340d2041900d9000500b14040080903024081d02c0a046580f90241c2041c1d030507250494408517107840c1404000c510203010514400b201480700f100d15048a0b403800c0907140ca500356a0369a071191814040390208080000c440c2c9010f15400c10141241000404264454070100c9200c0488000940025400c0711014114003a019442c10300504040e00c401008c10389407404c0c503044000c2940003003840f4020904025007002800d96100461030484030403001052001016100ca0052140350b10410010700107407200300c0808641c000801866079607404862012 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 910173192 1250 910171942 910171987
    0x80715060605031005010e0d0804291918090501150e0607170715052403072706030512071509050c0f060d050106031d16030611040b 58
    0x21403919a001880500890a99100d407014a85041c0c3c2e1514102c015900f24641d6104290301840569142000a800b003001c1d101414040030807580e1104010f4190300c4081d02a001080080000d01402c14092154072040d00a02400d240000e4044003481c5c80344850056500b0030030015041000114840c8002d220030548000b459031000d00e5010000d0a01209201d028000707020000b464041d0218504444000c00340a44200505201090a20150350858400352074821754940c5001e5440380f01007550807640c0710a0320442c05004404d103407080d401080a461b400b5120b1601c45145c02d450406500e40c0110f00440d08401500c0f54925031446040c415404601c044801503402d03e10000041154410940172076402002000486801000c010b100c3d507084113010b610400c1006001c5c204181409540d003342190b450204010840041d01c80055007100b400c11256072104e00c680c40b04241d640d0740c25086a4101d01c0c00903138034500307510f8482a0302c2241c0001c0100c6030000342e82000c000b60340d91680c841 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 910174442 1250 910173192 910173233
    0x1203050a0b010507150e07080109051005070e130e01020706140711030a09061805060d15170303010306230907030c0b0415030b0604080106030f06110a02100b0d0807 72
    0x1415001d100550700c0b801100800380414071200b00103000c40c4541c1d0b01201650780034408503052030390348243e0300d420f46960040446540c0c01c00c0c1d01e0f0b060003c00034003a59802042e1030401500d40c6160401044bc00d02c3c0300c02e2030758030094070740c0320f5288508020741c110307102540c100c1403d22620040d80508060382c00c06541c401c000408103e07628600b40c0000c4107494064981e0b03580c42d56090300d4030b9403c882c07517402d81c1d00b0384c4e0405201c0c00000869603250001000040d00e2100301080040c481c02c4100c54800666010303410010070001c400b070110402004507030541e0744c0100700040d0204e403600c05c0110502d20002e00b1080034102d00034411191000100d0004407440f610711521030b162980d0b1103503d1401203204910240c403940240c15004d41c000d8201000d20080604618107150740c5001207403d5130700f0f030751041d2404031000210105111442c05661400b5000d040a41d14040c8440d070001d56030140004400c00580d501c2d0346040841c1d481c4002c018656802000300c0361140b0a0381010710b41d28001d0300010f0704 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 910175692 1250 910174442 910174451
    0x408060a0501232b150b090a202209020c0c011b0c080604110a030210080a11180f04050402090c180409150516020303061201140109090210090e01050d0f1203050a 71
    0x805c0c01c0c15020b6020410805050101262a510001009042400d00302002a4585039600132003060031009841c003041c6410052002280c41007080c21101c1c51500200441401009803202c80180001c03d49001002803130208030310b01040140607a00149000b00601050a01c3d85c0061008000540b25004a00030100551003840300c80800060803250b11000b0341083c080d2040b0251507000b409201e50150300c07450041a0180d00c0c4541700101e0740642c9801e0382ca4501144240d00a041400040c290380e002602c04100324102038000070801c0030000d1010403500400101c4c00082400f000e929422140e010b0414021250b0a00d0030100d80103011000d403480501e80400150009120614040022002e801851440c5c95020078044076481a114124a0759203e60a56400c90034001c0c0040c002e141c100c0d0002060903803841000346403002812030f03500300b0590200078042030b111040c04d10704461701150361180100f0310349042c80c241546d080019003a058003480c201d00043e01340d04814800c0c401d940d010003 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 910176942 1250 910175692 910175723
    0x60f0702090c21090f0f0d0f080408030f1902030a020901140703140f090316030b011d0a0902040912090f05221a03030706020408060a0501232b 63
    0xa5060148042d0743c050034000a07208100da0105074a4580c20690a009a071520880c00d40010300d00400d8a4a071800703584841c90001300c1c15800808010403a40038034214420b818130b03403501c99450102824043d40b0402c8a004200010307101c0b07001b400803080300c031815501e074940101c0c0310009400c030020040c0425101c00d0b40300414110002201c110a61688a0414a1500360032078035943e0407181c403d1550b184200100603950b0f40c00c024038140c109980507801115400e501c3c01151610069120b4007810403000b1046688801c4003090590255041100081c4100e1034000500640a5244050804d071807904c0041c400a50020104080d03647c06040100410b03601d10900c036548404e200f600480d901c2004038078040c0c1200b600300e695180d0515800c0601880f051001074203580c0808022900e00c0d600003020000440c00b0700c1117036444510b0036000c1040b589040c100b001078a001c0390512541c041a140c4820259031341d514003000c110204c45000ca00300000030304028008007050780980302c0120090641 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 910178192 1250 910176942 910176961
    0xc0507141f1b030504090e0318090130061e1a01020a1407080102210a0b0a0519090626010902011707031e0203041b0323010605060f070209 61
    0x4075034080c0c2540c0300900400300d18451103054841100840400130300701700014010000e4080e0725a46204c820140d541d511120305000000019400341e140a100d000f00100714802c00b00c0d8003010f03449101130a02083c06004102200d08040659000f015645807141e0316003444000c005820300d40c60b110350100581030b0420100ca90411485100034010b90100c8212800148070a4580308204225811540d0701516118010300b03903000143c84990000200c44403102c0284c043c10b103a604507200700d800300210301e90784011494070381481c02031500502e20b220425030402c044403004801040c0400c02000302584601c0b000e001a00b00c0702d03208095a144130382c0022044018032880c020a0f40c140c4498403803001d00d40b000440000c00804000c18155a0400c013084102400c8100c800e042078004016503901d02031400c024100c40030380c0d040c1c140c80c1424406000184020850031504103d0940028003810b411400d54050107164000607040b841c08200003840d03241c60380150040728400c4070b00c034a13944c1d50000301 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 910179442 1250 910178192 910178239
    0x309030b071107061d04050a051b03040c05010302160f03120c02070509010302190906030813122d05030f04080c06030c040e06011704140d03020a0c0b070c050714 71
    0x1030380b8158000c00300c1004054007401001400c0c14610b0900184200c1c4000040c0440e001210310076031454842080184403810b40302d0010402c081e04c1c0c0214218202511424071003001ca0007494103241d80000e0302e49203410315102041c0c0281e03004004070034007402c0c1d1030f00030155000c0f00e0115844908000c1c955800300d001041c0e14007038034000f40405845030729540810030450403900301d9243c11001400042420030b0b1601400d0061030007580e80940d40e00c4034001085101d14540e000d2005008040080000a06803464490283c00d0041c0008440d01140c4030703c1500800c00b0304010854800014490030004041015004403600364058643d035082e003006211446c4012075500d0003100c000c00084c01107030b1404402513040752042c07411662000d00101c40410505003981e09594081007480070202c801d004005a000c400718a14003541003075000c3c4406011012014401403841041c0000038401a12584002c00104d4209080314040f545c0d4950300014200900280c3e4000c50040b071241c020f0103581c485 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 910180692 1250 910179442 910179467
    0x22d0a110405130f0b04021513080c040605060304230a1a010801050c04030f03020c06070305090f040c090e04060e0a031d01020c130506030a1403090f040506210a06090309030b07 78
    0x100c41040c100c141e98102111600801c00c80e0300070301c08e442c1d503c860007168000d8a00310260340021141701d41803c40362880e040c1d28089a034403c40c14031800f0f200d251604420b6030341003907101c4800d000e46140041115030400107285911054800e9a41000070301c5408080c1071310140f1b00041828480e41c9450070701e4281c801c2201d1a841c1c0400420007080004c2c11401e8059840780640305442c801109840002c480c0d500544081c0c00080c03010450903010b103400042100e4950048404000c1c02e02c043ca000f0f400c0035020700c207060b0460310910000d818081560803901e40060794134161141c013170203841c029100402001103100f500b6034801560301e4a5000007081e510f08071000b84500b22942d410644000504001002c080d0035014003011880000c8416102d42da2000002e000303035880f20f01000c20701111442e17001c0094030640c1080d00b0320046888810390114450345050b1203410703a07030310074592a20304a06003100038440c40c6071140103018180d00140c035030117032032260401c1803007502d65030b80881d0441013021 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 910181942 1250 910180692 910180703
    0x5150405030c01110f01140603100c14070213050406270b24100819180204020a05041d0a05090a030f110c210d050a022d0a11040513 58
    0xb12268140d805211140403051850302200c4801e500842d1850a6900c001c0903030b01401040b1040c00940c0c9401d1048044050848508000140200c80e00500c541080c1400f811081000034192055446006000300c05010004060013a81420300d005401803a00d2603403a603c404004000509404080c420b0581264100c0031001c6075441d5100c4456000c3e0007002c09011801c00d864004100e1b88030b180c1d1030113111030980c8940c9140d15211040b902e00602001504002c103260140b550444c6c50000b1101e51501c2c0c06450045c1c58094898055174544903941046540c6081341d00700e94204c516001600c1d10401d2070300d0302488207403902d01e0307500d03903980103550024041040d100d250030f8024810010101c0030080c0d002100c601000f0113003c6055a02041081241e0a540300d00002280f0000c003c0d001122071707139151544c42c09480c104000c0d203038000c0e98020710303036202091002e80d0304090700304105024001c0c0c0d10030f8500782d07590b0785440070039891544900c80c081d0f400d040c00120b0031082d01b000c00400c90f8000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 910183192 1250 910181942 910181953
    0xe0307080d0216050d0806040518060c0304031709030a020d0c081b120c010605041b08040b060a091407080f100501030b180106090f050a0617070915090515040503 71
    0x5010900180d04a07070501c44001d55041c02c040041342d0704000754841c61210761a000c0c5030381000e40c00e20059600040001001c02102c007100038030b1170400209694820041c021b1307143c9a48480c030b400c60b40e01e4600040b4181d0000041d0a0100c441c501100401004410b40c00301d40c1100f400f490140d070140e40d220b50140100d20140032030107528040d02664000c2103942c5041d210040310100e03029040e90803242114502e41e565401c14070407814030744900d44cc4066401c030201c1203c5c00541c80100311a400620040482d400351001c914262280c4a1a8001d01940e90301404a55190b081d102151074003101e10a002078602000f14001011034008140941c1714510050301240c10030006402601c00d1070300c816046a1084007024203191003003441d44c00703400d180d981c401806181c8106102041c41c11307001300e48a00300c1114100300a98024a41d06148064180e2100803540d803540103035038008503540300e0030001808112907403105521003000c070190340c8115401050303c0d46a043d42d8103d40140e000e460b8056211 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 910184442 1250 910183192 910183207
    0x60807020f011a0f030a061a0406080705030604030f0e03030304060221161413030b01030b0901180209060f18100906080318130908070b090604030c0b0612030318010e030708 76
    0x961350300c2c15501c2d00a000c4840c10740103650303003c0c00c540c4812244a6000000c108400d032a1600380a40c00061000b50010445141032030000390b25140050300080512080c00c11400842e8018504081041001803d50340c4030b107081e00307290700650310408032003071408036401c0300107035826070000b42c03c0c066041a14207040416100006a5950544080d00b0210358810300410440451901140f070140d0b1141d50740c45019455460030041c4014058a100c010340d041000c0c41622403502080381804580446010640d44ca40f81e000c14140c14951403441c3e082040d0000ca11b0740c58601c1c41d059406103000c0c0d642c00489590365000c2d00102c441a020b8916260400c000d5034890404280d1014810300000307207070380306080140e484501150001c580840f65030390081035400c18422580115035012000201030982c46c0b074a50390040118102210042006400e04080341d00b0f034481d0040754580000e071100b100c1c0e0300d0801003807800031080c90184065442d070170082c1011010001005403007019601590f4541003151 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 910185692 1250 910184442 910184449
    0x308090a05013617070815010b16150c030504020901290906040503030a02010501060f0e030d03050408160506011427060f04110304031205060109090e01060906060807020f011a 77
    0x850849003040d80000c0360116460600e01015101c03c4c44e50380c020400c1ca03150003201401c000410391140800440a40108807441d1218212840d803001e00c00500443c481616080c825201b0306e26040c03500c00d00d001e9146080302c1e01580018016802112960f102d0b0381d03545d01e07170009030604850244014540c3c0040c00c0510440c90301138480c2c044010a00e508050b120307000300c3d02c0c40d00030541103801070b07442d080100a40c2d604541174050f81c038410b00e40880c0c10141c0d000420b0340c41c50b100103001c0801da03a82d0001010b01c800e03101900c007006050b101e40300e8034003228103015994150a0055030805c0c212003901c0011480c2c0591002031945445800c3c0c64001403400f42c2c0265004014003041c2c00c41ca07561150701007039407a07106683c00d82c40b95810a648a090a040044c40c0805440c01d040b5454500024800d540c0e8021043c2811600c070903001148a103070030121140940311550081d88010f041480c04a0760a0f0400da4441c41140c0755400c1f41c8103142d040c1d44140c26510039041100d502e5402251501c1d142c00d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 910186942 1250 910185692 910185767
    0x150a120207060b030a0804030309080c0a0e070207180209180f040b0405070801090c060f0306050102280b071106101413021306020d021506030615030f070308090a0501 73
    0x80c095480003d082407200c0c082810f0024034081100c442c10000703024410543c11080610260040d0f1001b88008003550f404a40190594010034174162042c0707000521a9100f003144d80058601c01d041046221207844c0342d900650000e603100b138420340340307142400010b1080d03100030342c4281c2c0f100c82e602809460b01e0310703600e0030a40081c0081e15140560600803034589401d0003841a83d503ca41c00c41c030b000300d140007001441c00901050f103004040c2009803c04c01030b81d0000d422481d0b560b540c809000d00b040115080d0310480e079000302c0207101203900070410a1443d00403803440854859081038a21031303958400381002c01c460038002c408401d90354551440c01e6051203101c0c1d00b12441c40c584010316181c840038802d440e036102c82d0311000060340180f041da100e0307a90500603000184207046a00500d400c0090000361580002045020310761903980168a03a40d804003c0e082c0070840201c281c0c1c140c15202d040c1030005600412005004610419000519522840c0d00c01500460450031440140780b4444102280 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 910188192 1250 910186942 910186957
    0x6090b011227020d17120105100c1509051f2d0b01111606090f0e0c030c070213090606050603040f0b0c09030d08160305010f06140409020414150a1202 66
    0x204c3c41000321000183c1016201001d0320388240e12984079032069801e00107008058000c07d0040a480440301a00c0790491004d112540d40071380c01c100080400b218540c00ac01d8042c0016100341710300d45000721620a5200408100c0440180a0102d0014842000a0b200090042058070001c044e0744c00070b030600039444001c88003414580b01f401b032910080054944242c1e02c010000785010303a80200075064100f2902001040c51070000050103242038070a403042c0000500b41200400000300160f2a01190303802c07a41150350082811031150061100100201907000041382c8a900c1c004002c20f152400600b81ea10a035480003e102d100d025035900c1002c0b1b8080030740103500110702848034887c29942400181340100282d0765406280c586030f82200785042400c01c2401c00d040c03401c0014802015140840000d035003042c24a00030194000b0038440e2684169404094503d00c00b0801045232492214030032030b01c0804950007010f10794070440903541c9120350310030000811a2170124180c04c01f5503402400e0070 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 910189442 1250 910188192 910188199
    0xe2113050d03050403030f120608010b0f0906031005061917071d0606070c0b1605160819030c0b070c060b030607230c07120302100504050d030504060f06090b01122702 73
    0x8d40715036010300903103425401801581e5198601301c0c1c25800c28800c000c01104044501d400030342401b80c00f0a403940c100c2030312200c92940b00d1000441d142c50382c43c440c082407003541140400c11603a409071b40c511400e811150003590b0146010001c1e140c43c0d8204070799064260060702e402c039901c0701e00410901e81c1c05036804070343e014164940001d8802245025118024a902903082030724220314080d03050580303406d1070b0110098007100032b2241540014078080301c1c01c414078560442041c04c1c1403d03654800d981000600143c5d8240812008640c0f1480c3c0d4000d2078410b441c20700100c140c81080648500c02100c5c0300d400948644c2c40e0001c0c190f507070f2441c0080744400c9084c640c9400e01c0404828145403141e0000400000f400c410002010740c1000000034609200344108118101540e80c1034889100820500805855501040a0081d140e1000b461484e070010304110307542d0380b100200050b00a40d100140810385400b401045107105001310303010380b0666110802040c94408112000004481041c0e82 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 910190692 1250 910189442 910189457
    0x6101a04150f1808060901060b181c140109021f0806091f081b061c0c110f060601020f0d0e13110a0309020306071e030e2113050d03050403030f 63
    0x2540418008402800140b0050314241c0303064074105003505d19075848101140320411250302b0310b68040d814203806500c21602907503c505880850b83d210ba5000c4800b40000021128481e14840150b20502c5903903c00e0b0b8400c0c0340a4008107404c558442c0e60b0600d180421103c40001e84c2c41c0c9402c04010341d025030036285415803495401181d10848009800c4200740fa400348611284000c03511a1700310604000310350840ca08860b030707aa4200b0700e6028800108440340c54060305071509000e840c410071051505011580500e1011a8580d0360340010b403646400b6024044142e44041c1001c83d800307048082d41e807030703215071541540280040c88190700d80141c1626070324a291004400c442008045020087d44c1c0401e03d005107004160415074081c2050f001d1004911200150300c3d0390340c481c065880014180002c00602c0001f0842c1807418030908401015240011000740b60b100102902b080d40702c0344002c01c0503940303039800d20080080e90318014010800920040000034400c000c01030982d55246080c21 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 910191942 1250 910190692 910190717
    0x1906050d0203060f0c1b03090a0816120221060f161d0a0b0f030106030c051911160602100501080105060a03120302040b2808040b0604020a02010204030506101a04150f 73
    0x5086c1d410304143c0b90782000814041c1c2c0c0c90200102405442c0305800303003811034120050710350304400c107214584a070303240143c201095541f5000000450f003d010b240c050384d440040e08003601d6040032141d1b40c8100117880040342407408820980d0401d45080d494030f811003c031a010030310407500d91494099009060345004038015241d8400f8111805250f01d1181d265410000043e040d80c02c94081e0508100d0240070321340036140c3c00c3c107514542c01418284003002c4102c060b01d0904068041c402203030030490780d4800240b055400a0b47c401c00040d61a0100b050b6604e81010a090300d2080ea001688800030560078000300e400d0159402550b44141401480c003592a2400c0314190070041010220340901640074044603041240700046011030700e0201d10504e030950303625000d070401800c0b442c041c41e4082034003841c0c98001d6040b10301a41e084802c584e075a10304015224000700d018007640302c0150f80d441034029048407800580e000d40c1e04001e950542040e0442e0101c95401100c040002004171324038114 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 910193192 1250 910191942 910191967
    0xf1a060915120708011e12030c0c27060302060d0b13110901030c0e01090b09130609020310230d0606120c03030e100509090a0b091906050d0203060f0c 66
    0x42a2050a800102c0050314280b00041c09031441607211101400c140074031303031014030180c0070ba5505071400004c00340c004a245040449000d49540f0000741408824400442d403e540c198805070101301e0040044003030f05980722480180c1c2c3d6075210007500f0800a0050707110950090308449104500a0909a032080b48401c509080e11171180c00071503c45c000151281c00d03564507001d9030000807010b0422003242c1c21311800003815911603200701800d200012440b40720940d540d140d41060071300c480c402804480d4544806c10000c2d0701c1580e0000d4031341100c050004441264440344422000042d051b117100321062002c3c4401865104070880300241d4403d030124406202c46c4500c01d03110301032007417140720a05528018260b1020f1030303c02c9100382c1343c0c031001d2a1603ea2003422904407200603070f0001c600d525000c289402901102060310b43c80841c820030040c50401400080c03182810210b4148641c666030010f210039910041d44c060340640151000400a0030b80c1c405407030308804510344061a010690804 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 910194442 1250 910193192 910193197
    0x9051c0803070f1722020a1707050a060c050a08030603030d020a120e01180f0c09020703170c030112080c101b030e0f0304031506120c030201030f1a060915 68
    0x2c02c0110b01d1611010040d258070618650f51088072010050a80c00c00300c4164205020480b2800c04d40d020204a40d011900c1c0d610f900c00c004c0581d0a0700c1301d4580d0142984a407201b91502545000e500e40c400c0020f6210b00c2070b6508404030760014050200300b40a601d92461544c8000c0c01d80340c00d07110400031403600c0035803031000b0507100200f5a200a040000c6101040075520602c0c0070291aa0500503000c0010b501c145070a0302c1640d0104c0721403822102da1070704185c49507569202c0030165102050395028180c00c0b031340366120102229400710b100d6031021003c952a01003809922501001109100e0000e10104000d0400c10f100c101201d04400c0241c83c20020344401c2c2d417140350900e0181c00103180f8a50107002c0c2e91a980d1713003074028140c03240c0180e05280e668055448050211248496000480c030b000b40c1c040b2020f01304105103151280400c0c00d14031100076007444204d0000b854403014145000803841100380880c9031080c0462800c10a00420140c0c4d00900040d550141c4008103c070144441c0000 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 910195692 1250 910194442 910194451
    0x2030c070b07060506031f020a090e0c12010617060d0201020a1b0f0f030f1b08031201031a131104020f0c070303030c110703030c03051c0f0e0c0109051c0803 69
    0x8071199103150b42e1400d80203481c0c001c0c000e18040d91124030044500040c01811400c2c0180b031001c01626498100c000700c41d1560700e88c0c0200d922403920030500901c080d5000c01001c2101c45900e01c00d4207030740d23103040c101c44025140302d00c2d4100400380c4c0003242c580e02e0111050224180140304940500300786490785001c8103040c4144141c406100304003000380071240a036503401070100d4070500c0052855038464988000b541800240410000700f07000340ca010608140d40b000c5c1104404584d191488c0c408240801c0c0404c3c0401d507800c122568580382c40050700e407a501d208034101c2c0c4060888142d40e64030b1411036810220f024bd40241c00b401107114034003065018051407000480140070151550a000c0d04550040c1c8000c400c1018403104c01000080004100302103d51621b803020060070030b402c0480e0140105d14212440d588901200e501016054000081c000351500c81000b0140f03c0c10403095590307004028050104001c944200054035000b48190b555540b5500d901d42401c159a40798000c5500c21107 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 910196942 1250 910195692 910195709
    0xb0f060d1a18070305030906301e0402060d0f020912070e0f07080112080f0a02011b050a300207050d030c0c08090904060b031902190e011502030c07 65
    0x41c1040102c602c91a030b803031904500030b405020b040b825a2070b0181c0300c0c8100301c5254040c840006400200c500c55a0480202d403c91000401c09080040759807210102d05a4040d2000283c0150400104003030448190040303038002d041c54580341408080c0e60140182180d0b1400341603080c410b0110079110808070600e81000300d405484000d0804030045050a400f900101c3d0000c0d01c0010403201c560030072020780c190791004038804540c11440c41d04a1152168103083c0d6100c0c003022a01a407841d40541002c00c04480d6205c1008841c8980641250580124110600050b01c0c1056140c51442e40006a416125800e005401404561031000040c1d9101035000c40d9503a1050503c0b001203039161290702006030013441c04c01c40c0881161520300e130700e008030a5075a1217400030501003803c100569204600ca014040d0954440c580201c442024045c20309401b43c0c0100e00c3c0d000c000c0c15041c0d1802002d405e440d240a44040307141d081c0180405034110140303a074030561104004c0c3c0c400c0c19004100039001000c261 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 910198192 1250 910196942 910196993
    0x7090e090708010f0c020a2d150b0306150d020a0e0705030412021606050a1205040c05150f0a110f01021305040608011b0e19080c1503040b0f060d 64
    0x410a40c00c41d01d480b1328205105141c0811420581d5020410031295908001680740b5018410402d4104a1210301035908000885607540c081003140c4c3c0400140e0401d10b0b030304108008901092640b40e00c000c854001100c80c4003048046145044120b00300c1207400a4042d80384191180d400c041c2001e070964000001c80c42c048100000c00c044030080141c10460b5102903c000c20380303070300d90b01c00d074100d240548070a210012500c1c18030a4454603004445500109007070246007050b043c4120100001c0c00346a000301c40a241c144106c1443c241240c0d07080186500c850715210010f001214000e03035030403828001d40111001a541003030240003605002c0f8200035200522850041080100c940726440310129034104941110803c890a03a100b503ca01941041c044070340700600091845503034103602084400c0305003008641c1c4800011040790441d01581c000142c8010074802260710300003190010a0380000200207520151604125500320310060703c0880751241da42d41d2007174a081d20000f4404003c40c0c5 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 910199442 1250 910198192 910198199
    0x40f09061d010b011d060f1225020d120b040b030a12081005030a17090402040e010806060105121801021621030501080c041508010c0c061b1707090e0907 67
    0x20b2051440442090810006001030b1520020004403000d08451050402040c0544600e03007007411548c98001c00b2601800c0b502e06001154084a0640050a09001062200f4a056000141c000d44406180d11295202c0c040c50f4a054054201e0030034054009440d0580100d042d142006205040d91044103c8104843c4080c4007e120041c004c000074494106008100b0164901189030209075802400280c106400106001800e1088076026600940b0004000590621802c02d07281aa550b81c81642d00070b4440000458441c020b848400788000c1000313001c07070781c50018030103c102600441c0b0005418003001460545a42d42009401d581001d40c601c00c8100d22a010304101d80e07221500c2c14100201d506042c04503a55015134442d0902580e96110000010140519048000c040900003403211454029008042c2c0c2410681210018101074046410114540915a5461450b661281a426500302c000300c0ca16000d000801484641c000201c3c901c600c600c841445078142000804c0c10b00e28 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 910200692 1250 910199442 910199501
    0x9021b2a06070b04020616021306060e0607051216061a120d02071a0c0a0c051906020a080d020903060907080d02010b030706050c1e060a141302040f0906 67
    0x3162a0035200326010031141c40000d500c000c0d041c0e0460340680d00a41c0b01c0181f122903900c2800490b40c06940112600c1207144412480e40258090303500c01d07901c0310900b650a83c2400214003c56100410035080402800c0c924ad03802d0307010b4013919100250b000074075440782d2604400c88800c581000e03109840c00000304614188020203603040f40c0c6201c024107a010810310300945550050064803190100c044481d200a041c1c5004e075a010b000b2501602d08100c21880e1242c4c1c10400744c458203004100b01c0303649407001c02003000e1080880d0415000381c91080550768032190603a1241d50b1040a02e40c1c00d014410080c1c80c200b22040c811a13010300141841406d010f00c0342e2501c4111403840e002c586c1403403c2c03029242c6012581c01d08a44030350904507150140c10662a01b0190285908190320a901440822020b00016454001c0c1102d040030003c00c942c0c0503c00039112000c40c0c1c2200034100203010345005041560080c0070b4a01c80e03540000701c0e051b07690350709015503e4000039508070005200c2c410150743c5 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 910201942 1250 910200692 910200763
    0xc1b031716120506010521150108090d0513090911010e1c17090303031033210e07030c0f1d090109170c010c0201020a0909021b 56
    0x500100184000c4040100400403411605030100c480c1e01e660100c1e403141d0181b41504e490082c68582442d02c6443c071800005107900803030303107201e03c546140360a001550261408602400301040a0928002c002e0b40c1900d0560002c2019101c5012882c0005410328080c421140400d124144080c0d545039200d00041001c0c0e6024101c5100301481d90350640d8500304840d50300d0140b94000501c2d80310201250300c049240c045c2890080d010b000c0001048181064a0356000643d0240f4513907002030f00d4400b0104015203020301d65110030700c1105520207070792400781d00301c0b20b4a12072644030900f03142140c103220410303200d81c0c000040171a48001f40901c10010109514000b6051802d030b00303e9500e203406c040910044180501c11541c4a0301c40119414000a400a01029420252003000802c000030320070310b254815106814103502c0c002d1158001352060003112440c940075520004050304001c06d0784020b40c401d600105000b041078001c181211005e004a502d88211488004031403030320b194640c80d402 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 910203192 1250 910201942 910201951
    0xb03130b0601030515240c0703030210020a0f1805060a02030a4a03061302010e041515090e0f010807060311030f040f2a0e040c03060c1b0317 62
    0x98202800c016110002000005c03091508075000302100c124030151404402c2d09402c2481c1c48480052090700c0ca11000400e2001c40c0c0c843e40c03c0314032004074810a60101e0003070013290400211084202c8007143d1044401182d0b0f05a9104034a4036550f03039030006001a40161a00c20150704082a4205503580000707410030015031920703021903581d00108450000307003403119001c81980242000e074590b0190200c40450307102409021540d0f00e0415449001d660080360380c0490010302506004800c50406000342070b4551010710590403140e003070105a541030300d01420341d103040189110000805420441c4214007a55105002403101d504105c000c2d41131807195049841814113100c0f03144042000c0e0b2040b80e1348030b01c403a500760000d5103407032901c100144440c0d0000342040c00c0303400350104502c0410401801c000302081400d80c4440c0d0320492106420004c4401500d00109800b040000c2031003500000d54410543c5425085400d00540b010b404104044003a03000428588401c032102d0710704000d09811 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 910204442 1250 910203192 910203197
    0x1101090b090c0937150e070e0a0515070f12090b0c1002130b0a03050105090108070b0d020f0c060712271103010b040c0314070c03020a1b0b03130b0601 66
    0x4520340f0b240f14071a0151141e030502c0560240c041d81c4503421890a40a025001c004101403010245090f141c070303003a2591b40150b69454450902054505000c0c11000548410180108101a14010800103042c0d8034030800c80910004002890011301d414560310b0150f0f214082c0c955032002d00c070380c0062040c0ca03e50801070640f07104000c046e198020016281d90014082100980d85100300142c00c1c2c4000d2041d403000c0150040400c100b0708103070b09138100c903040c1c540c19162141c003070ba40c40c00340d503a07100c060b80f040002e00d080401c4602d14041c01c1c0c0d001040d00400c03982020f49003010320b5910b6880c05070f04840d4200000e15681050100c0311940c001d0360000303d1480760001680065201d00a00304048c190000c1880c040150f1049040c0c90030340100612503070040080092075201c0c80003030050000582c1051000810764001111540140039000321145c15038010a081141a503560107815031400e1400315104852000089003076800c0b00441c410701e45002d0140604500780b034001c68210024125030305 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 910205692 1250 910204442 910204459
    0xd090b06090408030a050403091a12061f2a030c030305060303070309210501110c011409071e0b0f12090a05100f020c0f15100e04121101090b090c 64
    0x400c0c0c0c1c103404c1e6030b040400c007a40002c2d503446134a001d4a05403070304da101141075007007981d020410745603803006441b41680c0c600b0125010b6542c5e030100f1074440d00c0002c885400200c1e01017413a170f469210310b2072a03440f4000004400248040400400201c40c9080f10480000748091500b80c01c0690500030301d500901700350011402c150306694090032452540c003d0007940d4a41090304228a15035031810341038227070400002c00642c948500c0d500a95030090004600560800700c0c0480c28801061013103124074959000f0b0103109041805c0d44110501c0c8505504e541c42c1101804141d442e104002829154060000746588580000c01c124655000074a42c941603008049010007054011400c0c080c52070809000040c0c9904c9031902000a015840c000c00d075500c2100c00e03113000000006100c40064015002550540d61003124540304810703031f8040d5200317007050729012600044e072408810107038035540d0074581242d8040b406031a003110756417130f8103850740da00c41c00034400310510500100760b402000341c50910 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 910206942 1250 910205692 910205701
    0xf07180e03030705070615090e0d02071805100825081c050307030e120903060c0a020c1504030519020f03031215030703080a03060f0f050d03120609020d090b0609 71
    0x94980c00010f00d201c061003c0040c01c0803c00c0210fa00044401040001ca60b14240e1225450402024101e100040341d00ca03150222103010b0001810314225034440e2056882c90b404120800301500c0d014003e0401074240c0755002c250454107000e080c800540310342c0c1c07d040c3e40c01500341d000a02c40b05540405140e800821b5400817004000c0400c809481e11418029920380728030324100d00034840b8064190181c0070380a0103260400c1c4600c0103010200303089084548603100c000169210f84a1005c00038003581c04060b000b01ea500b003851048900212640b0761900389aa01e445241c10104a4424420301002800c941011890413041c2044151420b4005600f4055022401c41400c000640a81c6d000301c081c6100c10800c0c0c0d4100f00c1100030b1a48208481c0d1900e601880260180410780281c0c0040f14451702c010820017400c03c55030048480040410000c40c882e80c906507243d0080c4034581012030f488020200c0ca0718004d0001f400d0200d0b13920300c0040c0010450a010907a40d00c040d11207480341d0880810b00 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 910208192 1250 910206942 910206971
    0x1b090c05031618031a0709060804030804030207150309050d020f0a0b06040b180906060d02130c14030717130b0c0f0702040c030203012603041401050c0f0718 69
    0x2a42d2108444121001a120104096030a22442401e000030107100c9074011003046401d04403c02c025a80280d0210151110602500c0b80d010074042d904c0010800300004010034071442c6201d030000e020380184c40416031a0035648006107400800440843d460780402820001c042000412500092001d09240c0100c07a00f410385500e03030703400d002d460038034000081507656640790701a4003901801020911490640001451940030440c1c05448601a02000410904040c264074840b00e80c01407400b0001414080654000c214450011080000c1029200401c42d41d85e00154014031498403142007400510040d8420010014000452000c40da1381e401c0c0001c4801d0070054200c8803a441c2c1c0c40d00d60404003060b55180c0203400700694042d00b00b6000504803501070f0300940c1600c0c1c401d096801788110b06050b2004a4000900076070550f07104000400c2401c103080c4000f6500742c5c05240c03451601c0d03407041b0001e150240302c4400f449140c00c0820100a4420302c00b581800c0400c0124040c803450000d101074 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 910209442 1250 910208192 910208197
    0x30e030d0f030b04020c01021306080a0e070506160b0108071a0415140c0613020405090c030c040203060103140103080d2a08040c05060d0501050f1c060908161b090c05 73
    0x30034080c141c40f40884511561641c06079181480300d000215158954203007818920301d40f81c418a40441d9414000c10300c45490750107520510071300c0754000d1854034580014030403a94014911075024207200794041001030000300780c0c2402040900300900c1003904016007414100101404200f22400420003040110826169008420072a0500c100c2d00f082040c1011114800c4195100d414014401002903100b14000e05240842c001e0b00d08101607074804141540d502c0904041c20351541c01282420114074140d0015584020189008038071450740e010444134542085c0c104580c120070226075056603046a124541e50801c01010005820060718865a401d54074944c9240401180b1000102484081e2140380014400038100b03981d595800100580107010a0040500c99071034008032a90915007400785289418800700c203036510302c0c2107590311001880b032040e0880d5242014070040d05c0800140c520031401034010b4160f00e802d20343c0d154000101104507001040001c7c507000000d01c0441d401001d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 910210692 1250 910209442 910209467
    0xe0a1407091211040222150f0c0219090f0e010c03050c1204031403010602033c070507030611180a061e030e011503020109051507121416030e030d 64
    0x592405455025010401030312503180c003d0b5402c0004a0b10201b1504100034440c2141c005400ca4110381d500c03020200da640fa241d4507441d00154640d41d0f01805841c2c20329240d9080c401040c0382810700d503601e000718803d83ea445100c4451690f6208801211008280145412204180340422441c5880ca006103050b00807444140450117440c000901010300840e840c91928084443c40c5880703680d184002503070b81c6c0c05501e22040801708240c1d4403004c08100c0300518111882250710800e14081d4000c00021030b0030190003614503124a00001001c640c3c83d20908203c07000c00e02613140d890044a9010224000c2204801d0103103180c00000c00c1201ea102165040408180b074962041000546085001e0948412440015480c0c50241900403000c51801000c4a200b03880300c440b41d41d0780d00100071894050280d40d40841600304a15000070380c1d903804102c105030550400043e111000b800751481c540001c1300c0e500d050380300c68030703980141901f003c031b05030004104038001c1c0b41c003600260006010400200 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 910211942 1250 910210692 910210703
    0x25030609060509010f41190e011e05042a021902010518090a1b02070f03020f060d050c030402040509190b07050f03040c050111070b09190e0a14070912 66
    0x4410f5040d0040c1c084e03080c00303c44074404620fa40d1b55624104061002444c44c0030038816510140801d2218000303a40c0201251541212140b07181c0c07818081004241907008030118800700c000300070503107603201d10511403d6524070800c428540c041c503090703044920740c261915003558081030384038021402c1c0c90b068212031a030a02c0d0454485452003440910700c4400c0c200594440c141008000031034409034800003210105405181600b07049500c20b0341c8642603801006140180580309101500f00525000801e5101510322440d00e031170703115032000702e0707c0a88449510410020a02c015071400d40200b517001440300c6c026090300d418520000c0c85d200b00070f100007801044408000780c90300d030241054030489451900065a81e141c1071501510404050142c00d003c180542001d5035416400511481038980d0f8045191405440b41d08103c540c403c90000a0503450085c41e02242401484c064036010f140408000f14001031800300e000b200300700041a40c010450007040402c85490b040100340700d82508030 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 910213192 1250 910211942 910211969
    0x9040f02010c14010c1205100f03020907051e0a03050a020f030a0902010509121e0303010f17070f080d020c0411040303030b060c1912050a0e040525030609060509010f 73
    0x78a40341218620000d943d0400d0752a10340710001c5260010140d911003990803400300069551041d1030b40410646015030f280c6481400310500060405015981e01710f082410300504041608100d0440380e0395540d556400040c0201e0b2075034209405020303068000900000075030614508a0401c400760100601107401d254a44004078190b9000701d089910a54000d0860302d484044440a50342c0d038049a40d14201440508003184641040402924165400001d0b441c005c20319002c0d02000035100f581315000107015603040000c404104500c034100501c01200500400040901d01038200010014900d0145080c030302150059403002c0100d50075070381d044c00d0010b01c0f0b4148201084290090f01d112480c28400e130780c0b12801c04c0004c003201030304580c82108050410714902600719054042c40c4044400700b4200395450006107442d40080d5441001e0f101e1110017503d5420b0300d50b06041c0c0301078070309010a03030307504050010030b03054014540540010354182415501d08044050001c500d0f1207a5603140303001 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 910214442 1250 910213192 910213217
    0x1e08040620030a021c02160807031103030103030801080f010b01050f0a030902040603210302071109060d02031506040c1809050c22051206130201140c0708060106030b09040f0201 78
    0x41d500040d85401004150300c900d06164004000d43c4500101d103a03403080741c444601015800d000300c6000028507014075943c0901c1c0c0d540c0340c29030740214404a09022030340101c081401c1d01000918000c1d40a541c400842c1d5160a501500b001d04201510700180d040070305900c0c550741c00c08201d92210050b828141d65a04142c00304400030030311403400950141c1840400004d112441c0361410708460800b0300c1e40203405c0000004e4080b4492000028810000100304a0351854089686684050040c121007500103899000071300f000c02400c501c3c0c002c000320105210313040c10a4810821641081d090011206d190309864505542d601d100304c8040c035440c0c10000e00d1213040001500e60055500b200c9401c003502c56480c2000c2113801703002c0c03180900001c40452040d2800001c2d0300303005007a40b0f1104c3d0784101154004481d88400c0b20280003501100704280c2c01d203000100501001441048054081c40d41004802070548241c0c1d131002d44a526000305203c0401c0a00303401e126903a0342401c103017417400e08 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 910215692 1250 910214442 910214471
    0xa0f02150c03030c0703081303080c181009060201061505031501020f0703080d050a0203041a182409280606030f03051b0d09030615081c1e080406 64
    0x14600c10001c0340e00001c000e0043e031100040203400000d00c291202d1415540e0300e00c01c0c006005030300c0b1000d4005801c04000c034070f02c0e5800344e0003040b02c00d94203050180403607400703000314800103502c2c11075100013a0815000c000f10791b4203110f103402800122101c0351498104074070042050002606840c035000e070b0094002d18903030080003015500d039182000e41d81c5031035483c102001c29401c6101e0b4500440d01340400640c001542d4401c0701d1040768010f42c40d81041c2c0389030741c203c10842c000500169621420b40d941100d498420440d0b45000c0b0310b140d6500280d0381c0a454104803100c00603140050355404021201251500070703503054202c400e40300909c0d46038205420144c025105d19070000e002801c60152810074507234020010300116412510b40b10220041c41c07041c0340d55004008200001512808060002881641020103440500581046499140d041080c00d012100c51506d140036221110030707034801e4100c8a0200c0c1c41800714424001ea4100e040b0181c45450000c10061240b5900c903002d590340302 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 910216942 1250 910215692 910215697
    0x90d0803130f12080601021606120b1309110402090d030c03020705040f020a0216030203100b0411040807230922050d03050709050405040203030d0e0f06070f0f020a0f0215 75
    0x2a040b25422110010074240400e10074610741400d000921800d00290301d039400001c4c002480886901d1044000e40307000c40845d800780e00c3d202011200703134036005909455036880c49000f105442e185030015602549241209060107800180c500660052040f02016a00c101c01925907580509003444d40c2401d6141c1241440b005801003036101b49080d00f550002e000c11b601a001d900856021249400c41207104e800050200303100096065001d0004a42c1d5100c080c1c00c0100a28805480440c0c81040c4080400c280d401c940c004000e030703510a9000f000000e02402040c90411103c00220026061072004540642001400c40903070040d04441c1180a101c07421000f4000e58114080d241000481c02c4000d01606c02a0380b03080006a044201007000d260911070b01c3e0003254001d004501c0d04c0c00e0184072001519854601503018010401c181e440c41c8002d01040307108101c280d40d0903011102c0e40d00060f01c55044020390000319445000e2075000036030040f00005010f901103c01c110031140341d4890913102e1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 910218192 1250 910216942 910216981
    0x6021c05040b06012a080f09060705150106050301030c0308030711060a14090708031215090702210a05031b090d050a051e030d021c020f0d0e03090d0803 67
    0x140c5410200010300c10b041c003035a805254240e882d80d222406100320740081c000c400f80c000c01407424040e0002c4c0020301420003480d0b14610712207890b0074400b020000443d150001042510070b41c0021070104c100107040c055103070140c03c40e4101507003194115180d80303502545901006003407500010100d0a05402401e003100111302e880101d034844e18081c10702d035000e046038542510028000102260810101044010170f036101c030001981000c000740200015001d024002c25418404e010300051680c03150f04000d489940745800600064222030136660303415100e4400b04490344401c0c01540b541c50b41c803030110780e0045400b1050502c03c104120000a03640318412080e46d0060300952140200a804205421803a004a0585201113400b1901f01c0c14183c0f007207144006608100084801000ea9502410b1400c0070341c00c1403024101c12110020407a230000480045030100400c0c05044101e460051600d0100b806014509000b0304002007481ca20100760014031000001c80000c0d111031240308421604c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 910219442 1250 910218192 910218247
    0x405010603060204090c140c031204022404080c01020a030c110f040507030c12060f0302011202040b040b2d030109020c0a0b010306020307021005060307122406060e0a050d0602 77
    0x152642c0c1e4103400c0c0244800e010880126002d280070561554030401070b21040313231003040503603e41400ca00d16045284c40041040f81d200c1542c4810a007000e1403074400c008a60f03074401380c5079500da0502ca010b40ca04000b0040031411940088d0701c10000950110f4400003103544034800c2d00003a01d1600014650b403242e15030054000d80b1307010030480c210768103400c5202c508095849603144803000e114000140c6140f409011488241781c9010001540300d5050344488400d0381c030006060580700c0941d00d800d07074040d9220075007c0d100880d4100d400702400c988516500e20918100e90141229034140031070703000c1417050711030b100d9002c41c022203c00303001d00060030280d0748207600c040c02d0341c0c4a2802000a410079121500148030302c035811039122085100300e43c021000180201141c501e841501288030003852012110b0003017120f811030113807080616000c60702d042c0c010041034250420000410039003480214900c03071070030340c003040209032180121000d01640100e00583e072480321a40c441c480d031200c05802c511 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 910220692 1250 910219442 910219447
    0x617130f12170618130b15180f0105130e01050c0a11031305040c030209030a05060708090c0a0506070606150e0918190303061d011514070b04050106030602 68
    0x10040c4400100141951607100e84070003260300b001c5940244012500150018245900016142d0b9020f0311541d10025080c00741e90302004565480391022000c0e0781003e5500e06800c0070700203c0c0342c0001000c02d000001a00702256281108200340c0808043c07141d107020304040c2502c41240c0026801281e4403404110082c042c2c1d0a01200c0c0e0b99041d401050707010b00040310104101c0e0b00b80400300880d0704007100a00344010060525040100500c00c01b140d0364180350b402c00410310640c4080c040c8448441c01100034014902d051800a0030348940280039940c00e07003190030031403070030341d50706120200b81c1d4003d40b00b031901c540c3d0610b805801440a03420082c1040850107108051035070204103c82814400e03108910583c4440000b42960282c0c4011002280c1040c82c42c503000480200400c039505000340f0300820010303078840400201d100c0c84446001c0b0400850f0051045030542c00410102851070701e800662440300c00da02c01c209005504d40180310344d60520215040c00000d4020300003a640040e411035 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 910221942 1250 910220692 910220723
    0x8060d020a0f17070605070c03080d14010b09100305220c0308030c0301140406050d030315092c062511120d05070212032206020c0f070f061713 63
    0x950a0f42804101d003004d01c60307514080f811a01c0b0b01d05480d05190300041c612052410350f9a8559150480400000d1080d66420752604d0100c0f8084030a00900c4005100d9545001c4d41051000c01007a0707049203002d060820081c0f080b0034900da981c20011540d0280102000c0049191030103164525a1001c0d10060001c01801111032160000354100c0e00c8007400491442a00c10078403007a560030f481600d80c800b4181444001183c042e8000d500340f98128a0030170920b5440b0862082182d0542004501c0c03400b800c010318000300c00d5810003014862b00030700240150f03c0e12003840303084141c2400380da00100c021007208840c0c07140501080700c800d0328a44165a0030350300f1300b0215150780d0800e0f03a034030b01030381d0422021444071800840c0a04008200800d0680b541da82c11b40c065000c51034185100d6842403484280e0004100740d80b010742188031014028095020400c0a040e10304101500304001c0503004079002c00c0401d42145151218680f610503101e03c03036551840c0b412045d80305c420050480d4103c500b201c0c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 910223192 1250 910221942 910221959
    0xc0a05100e0f01050c0409020906071a063102091801030803040611090a150c0203030f210708150411190801090e0705040e07030c080d120c08060d020a0f 67
    0x302070302656004450203480c00c500c41a00303039503043c1c844184500d0108000c0c0200c42e01da4005001d91200980317a0b504c1c0000e195548030712203042c118401c1c0e0003a1044148207603460715064a090120b6821101004100c20501d510303c145480101000b0342a0300041080458440d88000d6a40c002c0d410f00c0d40c2c0196a4030306000540f07900855080324044e142c0350440c00d100c01d0700810703a0b0b00d01038082c1c100e951407070801d14004a25268504c004060101c02075034040142c1e410002840405804072820b0303180e210010012408025407249018034508450800c05034607070210800e0f90004030790081d0704080d98442c1c003242c0104684940c00c42007000008040458070584040c0b01301d034100c2035a0740c0c1c45581c1e0303900b100422200c06164070740098100e64000c11442c40d0a41195580060450541c2c03e2035a0b2580c40e03900e140f00c140d0118446810a040c5440003941040021000c510094424030a1210101d001030103d0f4000308810f00c61501207041800790340b940c6c81c0e01e001404120300e5078100c05441d03000c031 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 910224442 1250 910223192 910223201
    0x4091a1005100e030c0406060e0d150606020a120302030606122d040b010501090b0d0e07050a0807030302070617130f12050c1e120c0307170405010e1503010b0c0a0510 73
    0x43c2c078000e10a81918030140c2c00c19104a0003203840e42e580d446640240001080040b04a0b00c00a680c6003581c910011288507442c418400100f540c0e400405800d5413610f880c0f2200001511524103240c03040c01048842d13281c0c1c0c2c04503206115100180421a0380300600a454044071001c40160001354400300c503c0100301c0d1005c0d9001d540114500801682d03aa0011030307140407107001d040703549041407002c02c0c003454840e006013103501b9071041034036210354907203001c191840310300c2e40140c4d85030380540340420034036405110100241241c3c0c0b5040a00701c10b05840d904080001414440030000d11005010a00180d5001d030000e07140d00c20404c580c0c0041c00e40c0002c02e150451a20451035000d400207400341c0b0b00246076100e102d00c18003006052191a07a00e0010340c2604405000c1409000420020300001c1102030040f43c1c914212490649480c1841e000402c601c0c0e2001c00580034103a03010181b4880c5d0b0f183d0042e00c3c1180d904004035680c81120030085420308410b0a40141a4030648503a00313030b1811203410 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 910225692 1250 910224442 910224467
    0x16030303050f0a0603120e0d0209090303010e0c0a050f0d0f091b120203060c071b090501180b030c090a02160602042103090e040c030227010504091a100510 68
    0x41c0402c41d03442d076185100445920344001840c5c89154804001d41e18096080c09810280042454080180c2500440d014040c200c1c1e000c1147d400000041c05104100058640c02c41c103100c603207a08004840e03001901c944141b00360010000b40200d400c0e144440142c10000603111f054005000b9468030746444d141e02d48212440309142410102d000c502488400311600c0d0241d0002d0090800352203003000c07400a6480510140c1d1850341d04403a4120305400e942507940185800d0100107055803410560018400c807035114801221b00b4100801100c1d81d0010724124107142c04c5801009644404440c10020310030a00070154070703000c1000e25400e001d807550140c4115907024006410780c1401c2c11040c50b09500181d001000320314042c5061000c0102e0f110402e80c0310707200e50354000c100382d10b80e00010b200c540a01d0f0b010101c0c0400005a43c4031104c91102a03006105c15142805503040d5a0f85581c0d414001d80f1101409460030760000d00c90601c42040c403002001e01070007403141c05140c2d100040021f92840c1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 910226942 1250 910225692 910225711
    0x10e0703050d030c020703140a020306040b040308010e07080403140c01090f050d02060105060d0b010327030f0519050c030d0903051e04050603041401291f0f050c1603030305 76
    0x1444215583e01030302a0111152680c0e016008441c19035860103a41c0d01c40100b5031840740704801c01c210058030104102030050b40501400260b629261400030a0300c10140c01000801054006010300260070283c1d0641090b414280035141e00e91005005280d40a078000140c615800d00720108148912070070480803440c021000d9032400035940c88181c5c2d4549080c030440d07800580c10080713038281020030b49c41101d1f4814140742c0030414a204124000ca0220340d000b6100e0300c42c80501d080010140c0011408c0340f04d01e9075041590414805801091502c015031865005100b40000d000c0c010800034411a081413041480800ca28800390600030000c2c0c20a181408500060400c81001d00b45030070203880803280d00400c50740c0345603201d6407102201c0c15244020101503481300c5040e80f07481003003041c0d61092280440342d240c0442c40d03401008002c0900c4045607054402c10f010b0b0125150b4041e280341c00b4569a41010740d543d071404041d2910307002000c10003446d140d24144000c0205a4181c1081d400340ca03404 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 910228192 1250 910226942 910226953
    0x10b0a0b09131104050d06020705030310090b01020606100f1103030414100608100902061b060a0b010e030307030c0201090f0602070f090218011b05010e030c2a150705010e070305 78
    0x1c02c141150b03419401c11101903010b200820180c946040d0b6014034074410040503041454a50302e8515507081a5505c1211001e90b543c2030003941d900b4440d400200f0b00900c020102c07401c001c030104050085070200201008124010040f01c1d0f0b02a41206448140440032130b90f6038681401d00c414002169203003030016014094440400c80342c40e010340403d880000c2c0182060000004c0845c004000c2801300305d030402400e21489207034011904e0500410007000c005000d551400c107000340207c130180c41030307241401560f1468013660b44002058480540c0d0504103030324082124001a030302c1e42c0f41e5030301c01d031985501c1d04008543e460f03003ca019000c80301c41d083d04c150300b90b4407001c031036041e40541d400080301225086001d00c15036110318002400d044403140030136031490690302c0313090035901c140e4410b8080f40c1c000205040076110070005074232880c03042c0308400400e13102c10241c2e29540c40d00e0039001e4410740c044d03110b00307107001c92800c11550003907402402009040004010684c82c0c00309031000361072074040c1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 910229442 1250 910228192 910228219
    0x110a1a03040309050d031e0905040c030e120a0507060908070f050c09160807080c041d04021023090f0406060305040c05011d060d0b030d180b070b0612010b0a0b09 71
    0x441c001d1308591351b1589841c002c0c65056500811001030801d00b10040040c50031000515440b20700c80c044038003100350341c089071b1054510125854500b1006407403120031420818007250607441300c06d44071403645c483d00104214469052584c083d005100b405407118a46803500020803100146e0100110300a4034001001c1d40d54003c1642400f0550b6191ba01060034100000ca150f841181c0003680a10702c40c0b611410140c0300c080d4030b2000b0390384030b026a800f018807006100552600d16108215407181e03140c40c140f41c842901102d6030500084040d5610703520b01149401c5c041e036408540014009014004102103035a0300c100402804090300c0035100e46c0b284007004605944070f00b115074001c040701d25220076201c2c030040511600c0d6210189503000690780c1e42e000c0c1115503052050740002845590340d003a41400a103454480100aa1307c0442d49400c00c020880006040400244e40b109086485a03092255200d11a000d416030040c1d01d54003800300751000c070360918001b000d010004020348502599861 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 910230692 1250 910229442 910229449
    0x3061c020307081633030e01140903220f1715160e0904020a120317040803160302091807030b0333060307030807021503070c021e0a03110a1a0304030905 67
    0x2c1c4080348071005c01c0749011140103400398000680d503900760b80000a5010703080038a400701d440e040d01c110041e9000040d18000700b680d1b0200c01c4104000b03c9403000b51040c6001d040180c40c2809104610380c1c00380704920981420f100f03101c000200000420f00181c1883c2410030120205064810380c0c1c0403810314a50042d480c2440081e0a00c5580d010b401c29010701d0800f00d041d502090f40c058210100611a032445000c0741c240c036407240c040c40c81807400d59203070f0a102d128584201c101c0e616003400c01d841400310519580d10384110341d04416500840850b25242c0003c22070140c007040c015117030140310318a0340d40c4010031200d603003c0c2100b506404850004002c14110b8854030303001e66406e40c1c0740d03010a40c144041801d007401080780307502c001c00204580400414594068004882100104000c00441829810310711200e610000d911641101c2e0465120700240ca0003c0a000107802200843c000507a80d49405480c0b0010b0a25044146001d082d22061604a540110f50840c00103540c800001401e08 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 910231942 1250 910230692 910230749
    0x6060507030804150e0a150c2318030319030c03090503120a09020904030f02070e0c1c02130b210106090b0d02130e090f0303061c0203070816 62
    0x7907250340c03541c126480d00e45440d82084101e010800b030300f59480d804000702010800075618042d01ca441c05035402c034044541ea130200da08500508081c410340c0411040302922034150b40403251608038096480b03000c0d61040d816038130724041103c0d4151200090403010520503410052400d0020390702841065210402141541c102c18402442c5038018400b28040410340e8050740e6201104601c0047c01d81000d8001540f84001641c0580c00b048800105411040c1d05002ca4030103060380030300c180868201510b403000c482c4190750312074081d103420080ca0306021000d5011102540b99030f10140f070542d1b490711841071081d80094001d002c480c1207480030080c00c3d80002c0c00703913040340c0305d9440310044c1600d0004001182c3c1e004001d94070041d036003082031a034120246203041014080c400404091860408116885c066018241c0302150f030081c8100085039841005030010381c20341d600301c0d09030388520b84042440c12034140c0100060340149203119003002900c85501007200d80c11100a6070700f8150351200840c01 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 910233192 1250 910231942 910231957
    0xb060a03140c2106060d0204030f030f020102030c07030f091a180d080f0d061206020a030f1a1908030c030903070f060504030212031603030e160e0109091b0810060605 73
    0x1c2034400c540c41240a06021040e0380180b005d4041d520b800640c00d01c1c2002c90303215400441d5192440c038420418558070441e030032084282c0c0d0008520f5401c1202813842c1c030f0b00030000000c0800c20050f9800d10914400c22065004000028000711800c0ba03a47d24404907070062003001d00307400901400d4007114603103066400c00040c0c0250b1f0080c40c00c0b0020762441103075841030740190101500ca40001032192100382d01c806c9024003d09006072584811440101035410044120ba11541070035401c002440c2c00c410003003100369040341c80c0c0314403a1020400ba00d04115503072012100d40408904012806004030080800c071204405407040e46460742c521807035203c6680110400200140002d01c0142421610354a0384401002203a003030504014a03100c000c0d252041c2100000d844089004113010f04000c01040c0c03c141c1b289403100c19080103180c40300c804051180f5440b41c1d4403000720380e0601000800103101d102c0f000c00520749554552011070341e80ca02d6401050410b80c90a080041c0e43c0d0b21450a03030701c01 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 910234442 1250 910233192 910233217
    0x1203051e060d141c050d05060f090f070c08040f03020a0806071d0a0302031f06090b030a02060f090319050d051606200d0509060903070201020a080a030b060a03140c 72
    0x1c2001603124084084202c41d8920583d204004c81031440c144e03242d080c580c0f0074085568084e91503202424803030558401518050045070310704080d5140d5078600280e1580108418000c05041c1da402d0380440b032034440305d0405891060000350201d240798140c605907090380d0084d2f804d000c100e81c1d151000d50b88d50108441404c0024003003002c0007411503112980381c0340010000c103042c1e029900ca40029040c4032626120100081031600f003c0702d506d030b00340550030081c22100820040c12524502080e00c83d00310320002482070340c00003500d06a540c100400c2d80c4085501030119642c642070640100c1c0328a04800094596101c0c441e12000c17600d00c80c0b8100ca0713880012601242c4203000c9552500040e02d01c1d07540001908071072400402044200001904c01141c81c140045600d050003895030341000000780601c50b203a00f00700031074005030740c000a910000c954170445084c1e403603070600002c030004e04d0040142c0740e1010b0002500c201956068001c401d11444e451050b1081d51144454100340d80711300046941c0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 910235692 1250 910234442 910234459
    0x31a0606092404030b09030306100f020d080624070308061c0b04020d140a02041406150c030c19020f0102010c120e011d0304030c0e1009020904091203051e06 69
    0x800300d50a00128103040042ca007a070b042503200d0b542c4100d88503003101c000a2662001c0f0400080e4546680c007400c000e000b60920420300c2040c0440252140d00c0b4002010620512a0210360740352102ea01045104014901d0302041e48107030b4003011115881000c003a000960341c2ca000c92010b14083e2040300c60300c8268140c3e86504400340d81c0f02103003410001c005990207018154042c02107110015480b10140300540074001858607441007008680351210000e04603000c1204115440c1c80341407aa405c0042003e1609031180015881103185124050394040d80c3c1c000c58000b4100480388038440050740e0310071610100c42e00e801034012070032103860b1503a050000b0840b01e2020110314203640800c44000368940041003004000f500700000042d2441e424183d81e000140801c14881e10800382c00c0940408103801c203040c1051501031450300c1e0f05001d400b0f200d42d0f002030b694005580783c0c1d1085a2280e13000070540c1e00c5000c0400d024005001c21070b024034183d503090394842d0007070045100d40c1c0e01c0340740b000f800f425 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 910236942 1250 910235692 910235719
    0xc0f050a0e0403050c011401080f01060e0f04020d060e030904111603050c1e060105031606090501050f0d09060b03280b0919202b05011104031a060609 66
    0x144200d0140060f0103121003007000408140080c086e9071071103920142e09811651520322154030704600c0e402441c040b0b9150400500020700c0c01608641c02034030072801d81c0520f442d80e00000759680546007008113410f1810104201c660800303c09402120000c5400f00201a8174040001a130702ca1400d920407120503c050160010303009401600003034460508844601e081e000c058a42d5841c1c0c865041c403940d01c41d100400c600d190800c0030041e15410b0345c1030305040c0f0b840c110b4017400c1d6800a0040a05101006c2411080340300410151098200d0442050104110504140b0000d0030b00d85003284c02401108290990441080d801803d5010301d0b0304030700c000208513140c1104240b4054020486030007200c00741910103030303440442821603000340c101242c0c1010a8846807510400101769900807402a00700f054009900d03089501c088844030708203030241d141c51810381d0041c49480d112422030100840d02100740111698522030f2040107190841068607680204006409100c50301ca03030000300c0b0800302 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 910238192 1250 910236942 910236959
    0x103050606090f041e020f03010314030405031c140a23160b06040e06010b0d050702070e040624080d09050409262703010c0e03121b07080a0c0f050a 65
    0xa102a202c021900c0d040745d000703480408241e07071040e001b2950400000c0014410f00a541c04207081500b14030300118600743c03401002c691960051009170000c614400c2481b25800d0154880e81c021850103080c0700e61b5075046190181c0b500351000da0281f40c90400c3c0a9011202c0642c40884681620400744183d100ad0b90391f5480b80ca4840060829070081e07120064100c03019800c21280d40600b103444440d540360b4200305250004c4030703401800305045511041040004034142068141c0090700720310041101001242c03003404592015408034000400c0d11780000310501d01203018030318020720380e80e02181e080e90381c2d007040252035541d034000d00062204c020b0307520020b0b4402c6a400414001da0307165401e12030300032820400000000912130302c00c140c54141418518003807040c805115443d003003c6903c0140c0c080420fa4a42c01100c0142c00c850001810181424503580003564054040b022501401d407034040300c6032240c03a0321108840c80004410046160790006404006958001c0d0942003024079100f102d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 910239442 1250 910238192 910238201
    0x903030c0f0f1813050c160206070210050301054e0304141c150b0f13020a1701060e1e041d0c1507200303180103050606090f04 56
    0x3811003144042044402c100b001030003400510545205850000209000f0320034000801a0f403148140d19100812030b481214100341d805000481c0e240307800d405e40601c042040b52240580c00780d070251041d550f80c0b048580c000003c50595a0998288090b050b90101040d00c034030b01c030041c54899240d030040b0144c00803c10b958846000c0c2c12001901e0f00c0740122046282182d1068012146100300245040d4450a0000d41d014640d104000180e0040740395455000c0d0444201c00346400454541c1450385090303607001c0650201d0400180045807010300c426440001b54000d904500209403007034101010040d01e148041d04880c3e29481c3c00d000f040c620000c20206070394428206452000000000002d501c0381c2c8030b0078045074202214407802c0798824a81c9890301007c850034622a8880a8400b0041d59502c01507500c00c035440641c0b00001e0f4044c540e01104200c1361803d207a014440800c8490f407003a03840110b0800031030281c900f080310b03807140002d02c541d500c180b0b5909a00f054034aa2110740c2c03414560300 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 910240692 1250 910239442 910239457
    0x2010e10090f060e15160b0903090301020408030705070f0b04120618050d080603030a0c3c1712010b0c0c10120612021020010606080403080f0903030c 66
    0x20301000c80ca842d4107040000344115003100300014001050b040c40307420b1109450041c1e83c034040c089810120001c10210103810190401005d0281d00c60200d00c403074600304150351042c60010000e549030341c1c0301d0410503565008110300f65900d00c1160b41c0000d00700d211030040c0055030040d402c01031400313041c410200d00d00143c14008440040d40c585a1f03420028100c1041c3d40c0b51031050020346004451140000c1c0342c0c0c4006400b091103900b04011030310207642c110460b007030013550105031504071800b1a00046a501c400109400b001614040d0102a0b0614041028012486410009003e50000141f41d4550040b401d401e80282511401030209940381c034040c000d0b0426404c01c0b983c4000b035000c0031904802040c030411010554429840030044100c0c000e54020300703c58142c40307488224540008254010881901d010720400304094038018840d94144589142d00c10003c1c1724440d0783d80d000a2003000e0855040d400940d01201143c0e07400001c10307031640101086d500460540d207599140d0491a1712008 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 910241942 1250 910240692 910240697
    0x11210609060607030e03070e0726130503070b0703020c0607080f070c022206090608030c120a090e090d0305010b03090d0e010c0c090e010e12070305070303020c0102280201060302010e10 81
    0x1000c0e42032a03501000400c0180034611310050031400d146102070304034800c0b107154071080c1548620070550310a50040b05a4040c25809402f420540c0500380542075200d02d240181030201b1301020801569010340040c002012481c046030410303a64458100c5a10800b540e0010300031072144042094a44106155110a03000422035856031440c500003518030b01207025113548140c1c8880c402c00021101d407044200030021100a0343c40c0020380f8000e180c036882041a021100c41c00441d02c40c1280744125529005015080c00c00104c0c0d082040300255100c07508a40071001a0900d800032401c080c2c0e4105036405504000028002007900d004107840d520f41c5c0d0803059040000180748400030401035494900101100400050711702208540142510340548440030341e5445041040c11403400c0300c1c00c031004240c2529085494070603d00d42200684105031000281d0340c00403c070000c2c0340300e000b071a10f0744590000c841c0c960020b060396400e80c281c40003840040d010580d0320040d003259003442004400884220f1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 910243192 1250 910241942 910241957
    0x70f03030503010e1b03090c0f0a030201020a260703020c10090b070609030e040207060f0608030c060c03060406180c02070e0108300a0807090b0322151121060906060703 74
    0x3180000b156400403200f049071544070041d16482828002494402d8020540c0c540d544ae90460b00082d5a4034048200103000481c0b03c0038a282003007135548110440c01c030302c40c00c15030b844d030310342c00c0003990349407c0581c81d845020744150b28110300740603030100401ca82050350708909102490710b500005000c0d00100340c0030310820310300c0d2880c165a607200807e1400e02c110000603550412089080840303072a0f80040c0301e15802000313a8106640b001407000c2e400590800420342d6541e4030070110300030300095800b01d65020000d10302185c00d401c460b0030203004081154200c0e40da075a0384020030100800d01380326050319604100e00303052a008a24842e13420341640400b1a04004c155000d840d0440d0b4007103201400000c2d0b070071041c0003281e6400342a881c01003410840c503604500b8007001100d80e40520070100c007150b00d076000446081114000c248100d04602c010100000038109029401c10750203148090405104d4403090b181125400c00f0b514041c1602170611001030390303554240030656001c0c09040d814080ca2 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 910244442 1250 910243192 910243231
    0x1a1002010b03120c06010e041e0c1e030506060907200a0b0a020304021c03050d1d1b03070501230a110607050d0f1a0105210a0905070f03030503010e 65
    0x200031402c0083e40b040151907980c0d0500c2c01c0d450070024103070420303000e02e0071020a00000c0b40034540c1c00c044001359140005c081080518054810454613403110720050301090070703240803482c100c0c0c1c0c00302100c1c0640e043e54029540e920400005c2e50b4100d60443c04120702451510301d1038189038122042401300c01c12540f60032296150002c503014101c7d500314646800004000c21418000c0755010000d196a241c0031050140b507501800c24060150300300c034841c3d0760b8038151205808040400704400c20800550304039408040f03000c0060364003482241e002c1d119400c00040c81c1e500c9800080749075a1070041d50380b4048501c2828003642d602c400702a0303040010000c914000d0320303800e0100e1406034402e6100c941e510120314040400303680301511a07102551402c0840b9100340400000c0410740002440c0441d1b41d1002040407213004407010b4420324000400408111802c4200c1d405814aa4068000c84142716601c800170400c3e003482d4080200000c00c28401040100d0380c41d1072140d00950f048a043c0d80744100c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 910245692 1250 910244442 910244449
    0x10140a410306070f2f011b0c12120203090a0c05030c0d1104020c15240d020f01030e030703020c03301e1c0501080309010906051315080a050a1a1002010b 67
    0x384401c0314a031a04000301116042000d105034010310404440c0d01f8000060300c0c101421000401c40c02500c02d000414542d00540d22684020105245000d070440d01c0f4101511160303030f526482441101c4680c1e40403008552841d001501c8060054020410311100e01c0d2a900c86641c030261803519a0066000d002d002890346081c07141a480c0c07110700322082c03405e103070442d0313090208400c210341c04030810f204890b60442c60700c841c003031140300507010303203181d0f84009040004038018246107440340014000800ca01c4101a4003243c015000042102104e065030310501c801c9407e03d100c0882000700344074040010180307000c440c000d85900c0d5050050300d0386040082e20b201000c1e5210019040e818603810003040c0c02000944030b81c5000d003000c40300131800c000c2c0303034400070b0042200d40c012901800400f1030740c4c00b0b074112030100140c040e089030717101c01d1440c000301c0c20007030100d50081e60914415400d02000504904051154146582c6010305114024501038280420310070913100c0c68045540342c641020b050746 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 910246942 1250 910245692 910245737
    0x13110304031106150d1101021e01090b0105030c0904030819020d06240206010b09120a0503031909020906060d151701060b0310140a410306070f 63
    0x28000e403940c041c40b1600341000340c00d0902c020030724140324030340c0320707070780d1400d8907070380800060345522803182403130000c03000c0050f8a006840051440780000844094a0400d0190414000035100740f41400b80c5076211020952200d000c8050f039a00048694001000709100b6100700d03070000000655164510701c00e0481d0010b0703a00c40c03103080c0d070400e40b200402c104901000841c00b8200c50100c2c1140c0c6031a84140e402902d40406104001c0c42d2400072a42c41110b0f40c0b80144814070720000c000300c4a0350103491401e03948940048820b0750091140c503044000801c101e01428072441d500401900e915500d0404100076a04680e271000b9000ba5240c4144c8000f600d20101e07000a03203201d0300304200f900c070202185803d490264008580c109418001c0c0084e0500d02a40c08043d0f4421905620744400c0c0301001c0744415040e07a001e11904549803101002600c400c5654400c15000c010700342c44420007489180000007610640540c05a2121000556880c415020160808400d00d440303500c0f600c142c902055100b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 910248192 1250 910246942 910246951
    0x5030a02070608130b0f06150403211103040302040207060b0603040f0512120c0304020111030a030b1306210302160b03060a150f0c08040306140411031902131103 71
    0x507400144180005a00215460f030700814900c00242111495035482840720406013510302944114004140c4036550102d00820840038180020784480d507070301306980c1442c3e00d12491303481c1041008000c0c5240e48104144503084031060f00840c5010318541c00c0c04000c0d07110074010340340c0c141d0b1182c801c07a056641d40019400b0300e0013007100600030710160400e2400d0034040010912800420000100030011140031075a209070604100c0380c41c1c0d55940010f036085c070140000c03034246000000d43d208103d43c061703100080881040c1c6840060303091041303132442124400c1c028182f00c030035554010001482c0c0c518174080c481d07110b07105070307002d68004c1d03070661404420391380003450344041c04001c100c100e04082c040400103007125040c8047c200d04d0904050306034550030600404019885442206010400d01203a005641c4424100003071b14010b018010744850a440481703100700c034951106030740c2c41d00240401089101c0c422080d40b0402582c200108006280f0403110f0003074841010340c0000726100003440c4903 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 910249442 1250 910248192 910248197
    0x8090f12060402040f020a0207050420070803011719080304030309080c031b010605090601121e020406020c010f080a1d0a0303050403090e010b0909090c040c021e03031306110705030a 80
    0xa080500c100020780c0c4101c1c601c113245d548148440394129a0005051085800584000038000d80d02920054a290000310701141e1400c0080c0709001c12514100840c100c0b00140100740340001015600742d05e410300230f07840e084158641c0c1034000c04145000d00440c0c0240c424100022182100d60f134a050399004000018156040496004101922950010104003100f00200425401d0000040402d10041e01080c10420814103c20750a01c99a2050550006060040da03941500f2a1064043e62060261000502600c10f0b040320550081100054094907912451407079981e0100410003444003008542c106009000c2d00302200e203050085c65035540c082e41e402704051405041c046e012203540d61180070708107806c03401003201460030029981c400364200c1d546185502c8880d1164500482d0200c25603020307113041540c0701100e4001448594882c4506d00409481c584100b0041d1203010440b81081000b10356518040020302c5940423003090108047c03250300305101030b10341300c0c42c541128094001 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 910250692 1250 910249442 910249453
    0x7051b031e0d140103050d030203090313080604150c141615022206090b0f0d15051005040e1503070f0603020301050406090902011707020f030a030213050906010c08090f12 75
    0x40c14843c0200c0d0b102e00030300000030405500d15650700d46c3c1c0b00c08007059401016400300c0414020303901030040781c440b52911805c0001060b02e0b68030342510740c00d042e50116690150705008042c044028081e09a26640e03c0c2c0b1100e00408000c500e89090340d204070f000c1e44655806484000c00542c200003609550159080c0058449103a5030400c2c0c4100c950f16000080c14100c4042040800da212000c803054a09242c1000d40742d170150140b401a80c020b078051501c2d540e061000a86595060000a508444044550b8100c06075002c100762114030070b038052045201c2d4114005140310039040700508840c0000380498041d1542c1d80c2c1090001540bd401c0400026000070041020345468007460004d0000b801e820001c80d80e10b980080c01000c50600000d0955a000d030008085900030310100e004c0401070002c3d281c1d9220301d05070090007548007011960b070b0201250b00100340f0303040c0f10902602c1240181c44031b10307021b072058883d5a9550403a441c0198030030030000c440300c0e01e0f0700d51240d04520015900003c10 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 910251798 1106 910250692 910250707
    0x50a1a0f041503141f0b0f04080601060c0528020405100e01080a05070e010e010653060a1a0c1e0f0607051b031e 50
    0x4201007007460400702c100f5007581200110400340000c80c811507031501080491544102010302440f100d8510078041d6059100c0280348601d030006001e400c00707540d14400b6203081401d801420008103048419020400c08001204400c1e46960181c10456060350807030802c59110b1201910898035000402e50103001004401d02801000e2000b03000b5607140c030241d503a150990f48044502d0300c1008400200045031200301c90595004194141007a40303403500480d00340020b0715034615204a460641c0c072041c1c1c0c401000d1503048060241c0e02d402c05560f03042c030000c0b03650141e48805d01c101060080000594410701e03450180d454000058940000d48225100c5038007a551654544d4802ca10305480441c0a401c030050509040e001100c045c3c030031050f11706480300b030b0a98036440810be040c85107041c50390340740700d071902c810005404607401e03e05d15040c3d604403519640c1c14034044010001d03610 = true := by decide +kernel

theorem cover : BRFrame.Cov 910071942 910251798 := by
  have h0 := BRFrame.cov_init 910071942
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 910071942 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 910071942 ≤ n) (h2 : n < 910251798) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
