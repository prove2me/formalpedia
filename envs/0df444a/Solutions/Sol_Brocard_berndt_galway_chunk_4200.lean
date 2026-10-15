-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4200
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:51:26.873244+00:00
-- url     : https://prove2.me/submissions/9218d24d-6f16-4920-8bee-726be8a64181

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 755215827 ≤ n < 755395683 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 755217077 1250 755215827 755215849
    0x40f031710050609010215040b090606030604030207060e061b0a0201020c06040b031330140f0d090309180501030213060305070b07080405090106020a023c0a030804030b15 75
    0x101012940c508000030f052510003000d540c01c0c144180c2c0d00101c2d420465032041541130301c0542e05030f94150204861541c04200302c07600820308400400c030f18034003590000e60314403045c0502010400310201084c5640c0340e050a07100110715900d00320b44079186040a140d5119250344003a4010300c503c07003100b1003504000080b40c0c1910200203c0c0c51965852010000c02e081250400301c1d0f90002e0140501c1200407100076810011407440e020440459000c40c0c002c0107800c007100094100b1340c0410039403a900043c00100c2c2d4a0903080c0b54040707080c3c02c47e81001d451a801651103029a85c40c2c5844e0f070070700e00f04e0395800503052764400caa110341c50701544010001201c0290000405550080e81c09001c401c1508002d0400d070342c400c107502e43c0307803c2e29080420030b40042a0300220150740441c40e40300c02c500d81025003201d8030402029090030561401c018482c2801d00440815203c04400a036215a4440400f1203001c0c54005001c580d486669290000c5009003c0300c030130703844041ca000c40c1046490641c2e40c4003 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 755218327 1250 755217077 755217091
    0x20d090b0921101e0608010c08040318090203011d0901060f12140313150810050f240715021204060203090c1e010219051509070e040f0317 61
    0x20106119446803402540400b6058410744603080780f060312404036003e04c0b19070303143c1c1d4202483d0112002803a0070a4494640100c14030b82d051440041c0501d5000804075400713030701480d04c1d0000c0c0650283c005c92409880e0810b0100741e000000115004144080080c403102400d0180d001d203540b101003060880d261800307140501c0038409020844040f5501003501e415009550f00d0b000402c1506c406441c60303200308204500000c14403810000c20b000c07628001406500340c01c2c03145561078181d110000c0840e80c1e00a807481030301d0388142c1c520f10b52a849240340b8110040204031a50141d860380402581c2c00c485822240510280c80c150f07502c0c88507000b910541400030000c10000c0d01d403551800087d40001300303030040078864400360180680c3c0740041c0b44007022b440404600e40c0603410000908000409000500301114204100c0c0040c02c002007114052074202c030080c54640f114200c4a0070410307158010011000484248024800007020f00c510135882603d03890900b0041c0c2da08007540ca03400701ea0341 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 755219577 1250 755218327 755218339
    0x10510060207030c090e07090905070e070c02090106030c051201030b010f12080f0706020c060a050124170406140411090f010506031605040f030305042c1f03080a020d090b09 76
    0x10005545950088041b100b5014242c442641d102c00c0c07210704403a40180207075020740c04140104510480c0303042440d000b46c000c1c9403078010440d650b00400c041050610680381010350b1390158296903403003201510030103081c443c1290351950f07403030801604840c402c0c007a0081d06000d41034009a1945540880c2c00c059030f100f40801c0c144580440781c504142c1007100103075480e075020000d085441205100003449180d0400c40010b1035418050f1a90340c9032810316252415101c11181c0048164115060952101e4803045100c80707680c3d14500b0001410080715000030700500c3c1c4090004019003281032020625090b941000d4540d01c1c1003590484103420720505400c01e10410110704103009140d000d281d0301d0344030300340a031904e40c1e50306104800789025402500024030104060014141d0040a01061a020a00038001c0600340503a48090300001d45458400044002c18140940a58880ca4002c42d00410002c0d190010040060b4960705850034560000342c540502045000f00401644c1d4184005410 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 755220827 1250 755219577 755219579
    0x4091a011809050c13061206080c0105040329070c121704020d2112140606031f0302130b0315012402070510030207031b17090f12010510060207030c 65
    0x18603002000094407008141404100d05500000c00d0400c2d42d000380800d558221001c022141f1400c11109141c002d12403941241001040d04c0c0c0e03006054030252a041001c0c0c00030b8510407001e681c6c2001014606400d2541c5c3e401c10003d03a141c2040542181e80d0054540314004440c00358111107a41c90f0380172010030341101802060241c1420701c0d5110b442445443c540b10303585a4080406d0180c05469046400502841c0c150340b01d41c0c03214000c0710110011030802040c6d43c10120005080d03800020030500b80c50007070500c4e04507201244c2c1e02c01801140c0141020200c2e4280304070719400780001d1a1018020f10419240030006540c000005040321003428804080d11000150300e1020514a60700c038045100d110804a081d40c0ca01079001c1e003083e1991170040c1d80b0203a92802612341e00741020020410721171f031848207001c41c12101c40001c15200e0003070040d07070301d00124001640780f00310114403a0b00b011b040e10801044810540c4458080d20081205010035035403000103c0e9200ca07103000007806012032980c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 755222077 1250 755220827 755220839
    0x509030d050c07050a0b100503070305060601050c15040606050109080307020f040c0e030610030b010b0c03030106120915090b090c130905010e0f010c0909051e04031404091a0118 78
    0x100103078000240880c52803030158141c030b40903c2d00810040c143c5031b07074580d001404029404126070200603c4181d01030076145d4a161940c0c3e03181e8000a09150601c50002141c203990322045c071410403525200c0f0441032441c02c2509000001b0100c0e402802c0c0460f003500800308000c9000000e560220b54002c0c40d40c1620035604c0306000c0a015420644014851900d08001d510399080c446503100d0f01d0904084a0f41074038500700030b04441c006074000990300c601088a00461080481281c4c107544032070511568107180c810025000700000e003006040206403058001041d240ba800c140d4295000d41440035140d11a00a11070b10703040b07480c0000d64040b190f048a80b15120341034010b0300d2007601600000038122081280c0c03a06240e04102d804016035540c4003240c02054102d00c0b080701419401f00100a1858110b500b401c0e03440c0009070104521000350001010548140c3c0c0421032140c0c00c0304010b880390341d502e1000300a0400c1e924001c2240710403482e1a1442e5126075a02c0041c40c00f58825111600c0c5440c0b = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 755223327 1250 755222077 755222081
    0x1803030601120b0a06081501110a0b090a151e051302041d060f0f070e3016170307020114030405101416020703021f0306050319150509030d 61
    0x38207800c80b00361100f040c00b4903a524100080e0080c03010361203200039494180c42000804121010140c10302500d880340d250956000a45a01001d6104c0800c1c01591a1111140d10b003404010004114211034080c00e408000ca6402c104800994031461929007a004d00004040d62030495000100d0f02c041c90300140545801e400c0300f4040f0360340b545003103c2000201c0c14107062a0301210500f03d60b1803481c6c1482400d8450040e2198007094500c0c1c8852510501400134442c0010049071a60118811850031085030154103444904c5407260210796051242001d40360300480c6921848500b5546409000d1420002104843d0f100303a050f0340380200541c0e01030807105250070242c02034900e840b9254107814050400d205a01c410604251178007100d28003c1032681c00344520442603421904656400c01c01a16080840c0c440245400c500e2845484002011001003500e5400b641e030620070742d036541c290400344807105179034035011705240b50350706d0b021101502c1618425900404190b0081004081c900b440d9 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 755224577 1250 755223327 755223347
    0x3050c190e030d0207051804020906090a150e010f080304050303070609080f0406090302100e0f04020d0902060d0e0f0703030c020d1104020d0f0f0903020a021203070c15081803030601 80
    0x6424280403005512012070f16001c141c0e1007110150f440844280401d00e0440718522807154058110506460191b0201e840d50401402c050302039211900801c00013241a0840d1441c10425072140300401d17591460700004003070038890200e58200760640030483d10400300846080d500302030000c601d00011656000700502c0c1e0036100380d540716024403641045284840003400200115030740c0c0c0440e03034114010031078000016801c0c14103000c2502d0704c047e442e4a030305648114030700044900580f41c0b1018596180a4190305800035444000014403032000c561640c040c40304000031070200c418546008084a50719031640c0006404103024a00b10340061034160200c0300310a2040d1404030110b03c1d100c01207001da0b040750000c0c00403251141c116110b010201d1007684040d0b000460300b0301030740a8940b00030303440d010a440040c0c0240203402031500f031590b013002281c0c841c03640304203407074212982c504460340e00010b0160010001452500800c0b034120491040300d80048024000d5071960302c035003005407480054 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 755225827 1250 755224577 755224627
    0x30717090a03140703031b020a030905040c020606130b0301020403080309010f0603081912090807020f060f16020f030607050c0105060f01081f0302030d020304050118080d0809120301032103050c 85
    0x210b4030402007c0801c0304000b00040e406800911060005242c068032980303450700014095407801120000307207030b4001409500050b00342e824007040e0b40a2095400075018100b01e49030150300000d0008100440700c40210320598a4000030848200103148050075a001480f02400c02c4000b0320214800f9800e1260030f441286030390400c1500052031003191003e42e980e80b5001e403142080801c0c9001942001e1045007561030045610314a0900b20714008040c5001c0c0034411541015034003114002c54440101245002d00d00400701c503207034601600002d04c40d5204c2d6040702140e5003054080341c000d003040b87e641c9041c0d0b00141c5131202d107a41c441c82c0000d2000100b85011003c580e691800002585091080d034048000742c0d4060f43c1e1312810000051709083d0160000100001d180d1130422007000040f40645564101d442e10070600c0c1c0f180b500c0f4030300c1d00074201c644418603a0000000020001840260640c12214401820104c0c14040055007183c90480c0c0c000500c00c1c003008140301035080b1480c41c0300c14000f = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 755227077 1250 755225827 755225831
    0x304021507051219140d0b1c06051609060c030e0d0c0b042105030f070503070606091e0506030c01030b030a0c14030105090f30030717090a0314070303 66
    0x7200341c80d01464010308081511050900013218501340710440c00303031081c070401c40c2004a52210350700c00d01c201a1003203000081c141c0b50740f0f40d82410103540d007441404507016030020404103407142d07003019801410309661105251030300290b1480050300500c9070a04540381c54a80220f000c22503101503c8500b1501c510790750101d480d20030b07000042c5114000300040c01c5000c3e42c0e60344542c14090380d61384c101d0003984c0c0089070298000c41d040000b90004200e51514102104d019241e448628020340795000f600c0c0000c044074203012000c01c0702c0703d40780d00c284454003802d0842c900e4420400e0300541242d206035801c4e03425801a04440c86d06501a4200c0013044c2000303021a00c0380603040d100c80d010325200340c107c0b58000720b00c1c42d16112031749024050181c1140492002d006500003240c0041e5035040c011200c20f41c80c500b140502c00409100000348144201e0883e000f075640d2600400040c03032010906090100c0c4101c0340041011030354000340c940e42d401c0d4952100c403030a9800d1003641c1d20707070380203158110101350b = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 755228327 1250 755227077 755227087
    0x20609120f040e1305073303020c0f0c091302130c0504050607060504120807021e0709181a27011503121101090b07030507090f06171b03040215 63
    0x10002e001881044910352552814a041c90110301703003105503004407d40003101050018851000165a15801780b41e541000220300801c0154064003504c0b43c8170701d081c040c040c0310700d40c0260b001c070301080e5886080300d18001a6548001149044070986130194000350001c0003207a0900c1030340d100000190603400c0003401c043c0c2c3d540c00a07031140d02141d400c44400351520300b40010440c40c240001051013076400c01d00d04034509204000c0d0390304107000001000c004429003044e880700d81441010301a01e0240424803500d040c090040d02ca40b01d94050440b0024040309603e6410380392003400314060402186200c041034803000c0007003420008099680015580c503c8000c01c82c0d11b900010b2001144a8602e100c54040302c1c03c809000c290350061603e480f0390401680b80700081d0b1141059a00c40d02c1030400160903140d101044859070100c0e0000d00c1c80d00f04484000c129960803000160074840380b100803121036919081040560035402c4078403103101d10103101241c0180303041503c1c0000310761086d5041e8100 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 755229577 1250 755228327 755228339
    0xc14030606071103010f020c01060e01030308040209070e1306080c01020a030912051e0a0b13030c060504030c14011d0a0c120f050d1e052d07150f0c020609120f04 71
    0x5400900d8a035211650008008c074507200207000d06401080b510310000420340c51902c0181101030018802489a4950000144198003613070401001860291222051003045440200102034900500d41c9501c68405150ba1640c030001d0702e00d183c1c5a0580d0b82450491a111100b480e102c003140e01120b03140035101c0240c02d80400000c140384200340800007401131110368240043c090001070311560508030f04000042c0401c1d04501490000e540c0860300080b00d84d0740c0d04089580c8400c1c500010014142030100724040c0105410403100f404043c4141d504c20040208070075503542c50780c44010311612481da0f0800043d4840901a0034045c0101110202c24040303030344003400e00e181c13001c0f0a4042035100e0050f0054101c21142042d140401f820b1041c40c0042c01e40000603166603642c0b05408400072581c540001c42403c0003640c0e40710f030b440024040f200c040705000c00c0150115031403c01c0600c5c80d00c0c0100000510000303411340030305071510280003400300341d820440d441e5000a02044403544100400984 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 755230827 1250 755229577 755229581
    0x151a130b190306060e0709050f1f1e0f021020040303090608011205100506010201180f020906150412050c0603040f0c0b0c030901121508060a0c1403060607110301 71
    0x169406414414107400e0031480d12004452113500605804000c810411000a402c60580416120212103903204000340600185141d031001c0391003a80d641008080c0701c40300390080e4065000b0f03100c0c4031546a1481540e001295000d4400d140c1d0b9005034013000c5640f00c01803241d03000ca4000c1c1c0c40340c410860700311744002070f41c83c0c40d0340154022000603e078070508219603a44204180c0c0034151f80c0c1c4440c1a5070081d621403e5031880c0c5803482800c615610380208049178000d50103d00d1002c400b900c3e400380b0003030b213061481c0651405841680121101000505c441c50503002c040f00e42080074105030704150500200701c0002c1402d102c2200d1611814100c0b891560314000954400e0b44103080f0b452103034103070b450720b08501300711603000c1d5401c0c0205100341d115981011054561042003071812003800108190b00e28082e20304c40c0015800303d6010180031402640114200b4800d8104420900280c5050241180d007404100c01c4450304c1c103000c0c0081006442c0600040c44080e000c0d110342d40c1022903072800642 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 755232077 1250 755230827 755230849
    0xc0503092505060a050301060909060b0a0e0301060f15030e0303091e0c0a03060e1c020d05250c0501080f040507144207050c06030c0c06090307151a130b 67
    0x101117180800100110b80e0702582c020040d00c080031040c040d2a01c0c1448800d024059200b2140a102031890707100720a890075030040b0001d15071240c41c581d4980da10303540c1011254405e07820000013810000c0314002035400004803402554a41c00038080f03a0000c003c0d03445180581c8003003c0c0c250141442d01340d85640d4210a010155004000006402c056401020318100d1100c10601800d142030baa90040b10b500840c0401080c4000d052041d6101c58840841d15080151201210083c0401001400f4040c1d282d4030302c0295242038031a160726071151410443c840c3c104440040c0140c0c040300043c0280103c1200c2c003c0d1100d0081d003680420844d20501e00320340040d100c040c103200b55403002071900d2707865520400f00e0f0007441080920310f011110340b1401d0325190b800000b14043c0e50000f01003040c07404400d00b00e41c0075049140036151541131a0310728507140e500c103800541315072030700d4410040110700c14030541c1c1d80551041001e0701000407034018811080b0640c610b040c901603403204854019120320390340342 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 755233327 1250 755232077 755232097
    0x216050109110a060e0108150a090f090b22061a0918120c070905041403070804090605060301050906040b0621060405090d12020c0c10030e010c050309250506 69
    0xb075070804140b018010000d98075440401040b1480e6040700090741c010103425000081d43d44102442c01043c008a050100580d01281002c0c1c54020800780010180c0d2014440c02e02c01d0301c2111050726a0812218454041500c1915103645506008000707940c1d036226608018034801c481107600c1140001805000044030701c4100110030003680301c000101404000d940c0500420400d090198541070141e658038140602d010350740ea11300c00f01d014003900c1d603809420800d0f1a02201c0e580c03602442e00c540160060f00c603400900e403c103040803445140040580b8140d41e4041c240f4405640c80004020141c0040b107211a0480c400300580303844000c0c0806042e8030401c0b07001c82000541420000d020458400624800300c0d5001180e621140e03550218041241d03481d59800983c85080415442d410040c599a045900c844405850f44040e80c060f0821824128984020005401552030035a418441110480b045410003040e00100304221400e00c1403281d4032880700c039440780d10b41000ca0410780c0584400c2d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 755234577 1250 755233327 755233343
    0x23190806040506060907051213080a0f021009030804060c0e03060c04050f03010e1504080f120402031603080307030e0f010533030a030807180b1c02070f060216050109 73
    0x4800d100c410429a900681305541e07060107841c002000400d207018981204044240c0f8001042d80c948182d032104d00403a4204c00d009075200c4141c1c1c005803264103040c0700070026000785410031494491504c140f20030141c144e2920443c580d203960784c550060520b00b4081e014001c50282403d060340301001343c0c510034841102c045036a40d00380020480c0405500031184d110380e05120104d50640800702e90340000f101c0350041c44c071040d2030710300c0c00c0700160042c02c51b480d444520104010308514200d50041e8003441c02501540c1d4808040d07040e503d0505014000078120660810100300e00c180b03c1c1d0712000000542c582a030301c100303000303125043c00d441d41559442c01c440d210454610069001c2501d5014100c01130040b1010b040100c0301007034981990b00c80240a02089800041005000d4000818121903240451007225220038010072503401c1551101440301d1120070440407203125100b100d61b07003034100f0240c0b242c0c2415962542c0103075114500c0c0740141c00401421000054003406030b055600e00c10652 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 755235827 1250 755234577 755234581
    0x31c02031c0225120f0c080a03050115031a0f030a0501180624090c0e03060709030606080d0e060a05130f1a160201030c110d1e0923190806 61
    0x81001000c000071882c1e0340d1078022481d40e0010701d0410062032500180d0400441084600000781c0303140c0042da070050710b50b003400070328048d900d40d056001c2070698015000028188075441d80440c1210f09110070809400d0014032517110514020313140700c41140c1c00030101c465034a8035544907401c2d07407800d0b03d481d40e40001e80f0100c43c0c00c201e124020326041c04c0708a00038102c92042c0958101c6082218882c0d80c40e0680d8503041403981c030b0301c00e2410500f0000c001d02100c410f03080c4900c004180003ca84002d0f20542d26021020490345404103414425200d01da8804085a074101c08000190703002085038070510408100313034200541b2003100301d401070034200c2031021081e151440e11504103100e4180400956002c00a0720107104414150071034007074080c44c0c001807411139074005850b80f44c00e1001c00c8580344607441030040e000750f101054011014000720b9103030151040301c2e0242c40e0907030345015000d1000c1c603051343c401100107480d642451030f0340004c0c0030007503071314034205141c0004415801c001007071b801801c2 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 755237077 1250 755235827 755235847
    0x30d0c08060a060f050a050d06030b0c120a05090c060903102f0403020105180f03010513030905040b01020d080703111303031805060f0c0a14031b0606031c02031c02 72
    0x240c040002c00f49800c0c03019201d01040700081062141c8050f49080c0900814034038040c4080c0c1d44028080c551001040386242032040030301c00140c0011086421401408000804068440c000c85001e032191900400c0b1160140382040b400360415800e050705071144c1e0700e0034860005603008007051b861140031a0820600b8500710b0850704000c4c01030440d14101e0411040005036801403c440d07150070075203000100000d0201c0003c040d010811302044e450b41c280410302c924915105407007a030403442500c610040607901c0d820300040d61140d009803800341e0030014070030702c4490041000301c4d030003017403850002000d44d5540756000c1c0341d030003403112484802c1078024103208044c5c009c0d40b5808070960143c01015682c0c42c00d40050094401c1c4038601d10480b80200303140000200c10014280d005600402221540c044c9583d626580d030400c2c0400042c1c0c9000002c01d004000303001c540316000701409800303882d2040c1c0c55910513000504060784181103200c03c00c240e0110091502710078030701c032005907000f45e0345001c404 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 755238327 1250 755237077 755237089
    0x30d02060103230c030726010b09010e0601110a03050a141206041d010609020d110c0c0603150d21030b010207140307030c0e010e1302130905030d0c0806 67
    0x5015401594400030051011400c901d000d006a1180c000f001d4645640c03c000050420a40901158140c0b1500c103011070a0740b88804040d03140c0c0d90361103800426036001890039090f904403000d1160410a9040180b0226044d007010951140060600c00d11501d6104001f6103004031441041c0c0c006007010540c15074542d4000c0005509041010641d8100420f221000141010180c0920704c40ea41d5822903000d07500d6410b0b85a010162448004c1040308e580e4015031019502041490304103070f1424041c500101d51041c2548d09908542005040c180c0c2e0503800d02c8100c0d840075001d40c00c80021800e002a4a81d10408403000281c4078401c00c00640c0c4646004a04014082d41800103050803d00c4c80d80c3c480c0d0340046c42d0f000b16950400c04010503042d0402003410008181c1010f4840c000039000442e10200003c000c50490f00c1822840d07266a0f55400d180010383c5039044000e5114030310303010790030884016401c0403803514056400d591408245000700001c41c1c1340b602e004c1e17001c2464201004200c0c03a0003 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 755239577 1250 755238327 755238343
    0x10308030105181618090e011a01170f0a06030f060e010b121f0b10051e040f03231c0e150403140102070501060b09132c0f070f0503 58
    0x480f00f580d5080080440c031200059030070010402c00307034404a20a0340c56111780c44004184000301000714202c1c14501c1406003420804604086001e12a0f43d54107501c14002c281c48003402c40011809616920110121200c002c1c01400f80203454540c080301186807020403500c590311442d00080c08490840c800e03429204c841064a10540c20900e112000302030104100c07100715143c010700241845400c0301c40d4001c0045d859136940001d000b0f06215030b401d400a00400103024020407201100c095824092258400c074094006480a2000c0c1000080c90b02c0045540d518100151307032485c9000c400440d454000d680d07450080c462420380c510480f044e0800314280b090f8400391510b0a09440044c00d440c0b0b94801c0c1c3c4030041c04e1a03881c2e070908030b01e02c90a60507505005c1d4014024804555110b00c0b069050b0071025049206111040402a07500c80c03c1c414101d0a40f40e8090800d803260310501c07910442d42c50401d0482860140e0801c90700040028440300004c0c1c650f68150740c40840c10002071610341110 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 755240827 1250 755239577 755239609
    0x9090b06030703050c06090307032003071a04141807030b041a090f040c0803070b0f01051903021c0b090a0c12081e04090507110105060315041203060b03010308030105 73
    0x101c19814004904007041c1c03171290110640d822992203450501192400581d541b000d04032416000103502d2046400e0001c08c2d0514044044030002c503110f00c86c2103120100c004030702481d45010070080102032441b0554505003036008000e051050703140000c8061481d011110321000a5aa03140e1411030314051042d105190000300c148504080d100010801d450300140c004070103005450b000604000340d25000c0e402070030060090341d444000034513041141040640e20903442006080000c0b5190501c04030401c5101c18610416100600c3c1d6020702c00e00861000b10482003d1415082d040801d4003601000d000e1901d032002080c40000034180b0a402131040e4103c0e0040c1b084100703001010414440540b224010540051350140c400001c80c00160303c10b590001003072170700f0b120402c600907030407122050070605004d00902480d030320b41c010980c03910f070103030080000300c51004082000318101d80d0120515240794103000a00e96150b0300c51180e84e8100b41d00454440d44000010b02680c2003113400c609442c0d0b0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 755242077 1250 755240827 755240833
    0x100501110703151d03040303050304030801120209062101020f040914061e04090f0b07030501081f020319060321051201180b040c03151a030c0c03120109090b0603 71
    0x825a5540243c00c3d071a071188615032030b00c50b10f14107422904000740141c103203001d6044039502c56407032030007800f1604100c0d410ba01054114000259120b0109540100c150b030041040700306607620010031071074594426050f94102a40b80c1002c00d129000d100800c021101c0200003602c40d442d1000d0301c416900f0444458200b003102005001e43c6841d8154810000c00758080c440216218010106004181040001d043c12030a409503100b406982401180550314540d0103010980c2c83d076188035038590304400743c00710038400c0409105c0c10742c1e580d5000e03540140c03100d0340030080031620610903030640752641c00551707a184041d5140c0c80e4008415580d4a2000550700300740c1e05112a036015080f0fa001c0c144510344000c0c42c0c0c5028000055102d5214200001000340104100c054001d0014001e04e201362040241c040101c0000c14941c09440c86408510132807034410f89591b13981c01c58541c60740c026034190305c0e4901c414080c0346c030a04415400c2d50b019001c0e900740000e16140b181040101342201400d00ca000390 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 755243327 1250 755242077 755242079
    0x7030212011a060c15101d060306060105070c05030d0807020d0e01050702010e030a0f050607020c0103020702092205010608150109021303170f1809060621040c0308031005011107 78
    0x82c0398080d508a12034212080c03522600030f458103034285440240181c085c078100401700720003401c0800d1140c0c1030f2000401c2618404420b042c00c80c04140080e00c10560541c04480090019840350004001a91092b085072040310340c0c44c80424135102c55880c0e441c1c041440e42042105035a81001041c00200440c90325411646400c800607115100c1c5150180c10080341012044154508101d0340d0303903c80c1d000c0c2003040948104d0170504d0300d8143c20744e0302c070005000310203181506600c24000d1b10355490300140300c110345443d40c2402c02000001855545081c070381c20783c18280454028402c1a00500700c860180c000e42c224130f9468081100160042d090075031050007801101c00420b244602076036031281c0c03091150513010581c51100c0c01380d0380c0000b01c0c0d004009440080c2d80c41000300d4420b40c84069070306056079114001000320706e0150744183c2003550161441039109078075114140360018040c0180c0704140740ca03512a03504940c000c4800c0004002000e404002c996401004051b4844a40015142d12 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 755244577 1250 755243327 755243351
    0x6021e0309010b1f210e0d0e1c021302030a0e03030403122003070f200c09180d120b060408160503030c121b010c09321c140703021201 59
    0x501c990315039010710105d903040c01e81c19400990348810700c040202e0b41210380000c0702250040220441400e4680503440301c4007080c41d104804007010b00125030061525200304e1040d44048020f41004200c109582e81b00c880d15012100280001c40c003d5001e59240050003d01204a1040d0340038401ca100000d40e0500d00e81306104440310550390003d40d07515201e541230203841c0f01181e600060141103030040802c3c114800d04043c0009401d42c030f164041e80d5482c1c03e43e8900402900f151890300b001001d03604550050315910b40b041d551729840d0305980100113102052400460000d411940044079a0f5001800c1315920f03000003080c2d0f200915084009500c3c0c01c1e000204147c540194060b0984c0d0071030041580f00389006032808018600f00701000800c10625845001040324079548654041c4c04402c4e090744a0907040142c00a9602202514444003030000c1014000d003803031200b40902070f5150000c02280055a05265420741d201303440000c143c924250300411080340c103044a580103917071500000140d4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 755245827 1250 755244577 755244587
    0x24030604081914160b0604020306060403080703050d020d060e13020a090e0c03060a050601090f03030f2001090b09250e040305040e0a020304030e0102030703090306021e0309010b1f 79
    0xdaa40020500d40d40e02103002c002c0e1a281440d212031044960041080940410b04490005541e030041a007600075072180b03010f1000b00d03c016901560080e6007044144007084260340203101c080e110b40303481444d10840504030000c0781c0013a11544103071a1246010414111059406a00080c6000b20400f24200035400200c14117018420307442456291020540400800c3c46041e01814014040d1044d40c40e01c8482c0300000c107800c8a0690110b034100101103043c402c030f8080308080e00d6141c2c13110f2980404000c001d0b600034940310581c600c0c244c180e22011982c40710a0180250307151044140c2409410442d0809007410504208500c1802103a040784203e2211000e00904450b2143c000141581312810102c82d076100755001102d00704040010f01c4500034440e0700452050b1700a41d0b9a8110307031031100c012078403441070010160006507105418004205a40c1c020205140c842c2c00904103030000b001d0340300c940e42080b299045e20342d40d14a000c510600742040d004000c440c03091003003854501d000c000601 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 755247077 1250 755245827 755245837
    0x80708070f0605032a0d0218032407030203061c0605060f010c020d02040902040905190302070e0405030d0b0123091e090c030402040b0d0f060f0204050307030f08070b2403060408 78
    0x111740d0030100d00020a41500d80304171052496144000d540d41ca00315110180700c031906541150081c400d0b1304a9a240d40f01c4181c0f2812200070070324000b4221b03281c1c080110003a4201900c016407100411160060b42c1a001c010403101c907200e0140801c00b40740070010440d212013400ca500d8140000c0c081158016030394242000002ca90468001070307d1581d41c00817500070222076500500c40d101e0f412000022039003507a01090401d120782e080f10001c0f516811070f05105c40c07058600421a40c0140124102c1603203d40102110b010185015008021201c245094041c2402c10030380c1100000144002181000d88001c031441059500c8068480954030104150490041c1486898040400070a04640d42c03500802c105000003804405c60070740e20700340143c420031405001c442840c5403000c55422245240260f0b001c540000740680003030f5255440e00310f140d48100300b003120811b000b00510340c00245404451406074000054013500e49048030948013180b120000300e503100341c5c08841008006444001103907 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 755248327 1250 755247077 755247121
    0x513050d050703020607050307061107080301060320040b040e01090e0604080313060911090711120702010201140a1506020f0c120c0306012304060e0f0c04080708070f060503 76
    0x8400103400e81801400d0040d07070380000b9030100300010844140038001019000660040070104040c0031942c05201c50f038482c5d410000c0000304d040c03004000b068040d80c40102e0b04550b409800520200700000340016600035001030012010124092050800030300101d8054138020108005604100d6619980c0e0600207000510300a00080000c80c49075004184510480d80104140080b407000e2408401c505c0300c26200724094040100011080d501c00e5681d440110420000ba00c03038410301a000c3d0580b0fa000420990542d03407104800e190340744a4035800780c89605905c0000801c07400b21075040f80c03141800d40c482c104543c8842010706201402140383c80d080c0c44101e40808418491403d00e50810310802a05071340342c0203c0000044600341d1107503807160f4145c3d40000c00300d54101d0208000c100c902074040c8503c13441480c00054259500e4038842500124000304a9052507950403c60345000d415801560282d00312240402090031100940c6001e0000750510340e09515100241c00e0311894805a40 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 755249577 1250 755248327 755248339
    0x6080f071518080604030f03021801080a02090a12110a030305041e0e0412030e1f020a0e0a14090f010b032e03060b09010b12131a010e0f0601051305 65
    0x5034000c1d802a81d034004000081c950742c205450780c8601842e1164400c0340c06901044940c407110500034881c1c0300700c07500c2d501580c3c5101081c0350558011520400d009014180f800d600b041142d410795540d050032001041401440d0b0a541c0003480c101c1591b00c042c2c1401d600132503030200c1c180300180d0400700352002d85001e000b51501a115400300740c2411013091f444880062070740380a0101303019845c01c900301c80040d140c4060001d0342c0c0c011480f41d82c42d81c0c68071107034016603002c920a01003141d150700148926a843c1c60318a26040d84c800c00102c54404981c4084d96907030001e03102002c3d070700307080070b40b9684030f40c0300d8820721200c2d03242c0405c1c214288001800c4104041c9401201101c4840c900c4260224103801c50070403060a44034038000008100c00d00800e0321610301340c4000105a11000300b1038038207000190342101691101c120004050b0103200c811116942c10f0b0f602414826404415140240001f00500d5810300340404281e10307118003e0201c13810000c0070402c141c83d11184c0510340c41118410745032 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 755250827 1250 755249577 755249609
    0x1c08070c09020901050301140d1502030604061502070501030f1d100f0b011b0302071a0d0b1c20220e060705040618050306070201090209090106030c09330906080f07 72
    0x3030700c8274003001c801860f150342c20170240401440382d03001d036100b85410b42d4100000c0b40c0724144903a0b41c91541d114900141c0c4008814041d030f5202c0c1d00085401c4200040124101c2ca0325004c05a04c00b050701c051401d1944001020341d01000b090040c880690000c071030802102e8075460002300b4010b1891681034991206415079010140700b0490f1400034000381030a0b48a05444400d21001d55000141e0780d4115810003103884420314103440d0b964003c030109170f05030380380900607690201d008065052005407041c3c0f10340c00038025100c0c99110107501c480041e114081d9108508480201c0b01d0041d48c18419030f005900700403e41c0c6d040341c222016a41c0a041c080d9140d411a618170102c03841c55000690903009081c1444803003601504003c0c034007407089440740e505580e00c01006080320480d11000d440240300c0d150030480d04078540d03c1030b450341ca551280040b046480d1305000b5a0f41002031684108003840013400c100c0f9048521407180540058005006481002010035586540c10300400e06480d5103d03035 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 755252077 1250 755250827 755250829
    0x60903030c010c0f110616081f03050601030312153c03051e0c010509041b0e040c0c0308150102190602190804021c021c08070c0902090105030114 64
    0x106a074a02a1800d00a10500490300002085502c60b486404040340d884402582407140203d030040c0328800b40608841c0825203440126410513014080150307042554160181e03d25010031128003840c0a00000d007910b5256180c014850003194850b0f80b00280f400c4103002c0d034102c00595840c100c3d003003080151410341d58038084940500a003904880d900760591100000d80144d802804112802407040d12003142480700007400300003400201e10b52580003a0281c503565805480a0400300ba0042c1c0005007414020600071182c110035100100442d814954046003458140030b141c030a42c3d42854654600c191650300030300aa400500900c1402400d45104240d9074400c0122840d111000c8500b00813207183d90800e03000075072048460707803840304551141010386c40c050078105000d0340d4003612501515462006980b074900ba040422030380302e03942d00b00ca6460310300055910000680039982c020303070310112440c1000c0f0074980740d0300002d03d00d0300500a0308201d03070700178090340d044070f0135280b201d214110010 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 755253327 1250 755252077 755252083
    0x30c05030c030913020f190e0a080a02030c0307150804050114071d10050d0504020f03010c050a09060206191a03010e0312060901061e0201020702090c040509090601150f03090210080402210309060903 87
    0x8d22903540024820318002003034400000c15002c0d2a001f5015200107005401c18181c480085009241122040800da00d8901d4850b080b070a81c000c2c0a103000051200d003800044c8102e0b1410344421000400000c10540000c0c00da0704c09118881302111849801a1098001781c00d0b806885003080c105961100003a00355111091040c02c0500c00400030080c40d028480e000d07203a0b4204501800020380c08510100704d1900001c0c515000e103130b0740f103494841c6030070079441d40c0094039907400081e140302070706130148006480034014000400000700c091521038078907030174032400044020456441f400804004118250f08403480c169070b001c20b0001742502240100b010b034068800c41d4002500110780c034081120801c520340c042c00c20389804580148142d124001d0f0310340d0b540006e01801c501358440b042054206401411071100d40301042c100415103005607000641401018984503010030340e1a000c104c21031410755495030342e12900440905083c1000a41503980c1d02503100e103a80030b0140001e0100b0566010 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 755254577 1250 755253327 755253347
    0x16081f06030b0403080f150603010509191b0215011412210301090606050a1e09080708061b030405070603021809180c010e010516030c05030c030913020f19 68
    0x8102d0b025041030714008240640894a040c0c0000320715012030f01c0e000805411a0754600002d001c6070559003080d04000210744041c21684807003d54518403601110540540030000441c10481e5001d5a0403070000307401e020b00010100c000c10071000040c00b0241e1a5040c3c40618034082c3e804600003c480b880c500d01e045009600c41404400e2105015070010000c401541078525400c000d0100b01c3c0c1c0d58005440354050350750050b0101c1c00d00e109110300c2003407071010100c0d114481e03c0e02904942e07440ea03000307050405940018019400c04410081d18602d025042200343c00750014861131442c1644425450380d902d800792100f0103400040d42a00742c008a448840c58160080980c0f41c075041480e5840e40441100c03180740410b010715488007001d58010043c0004420040c2c64880c54104560700e050204540780da401c50511440302010b0000c550200301521000744640c0c01141d03240d0b0748401300008001000300c184c06d440d00402c03c0000344a090001d135840d00801840c40c800d5140c4004c1c040c1e80e443e0072 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 755255827 1250 755254577 755254583
    0xc0c0102041a030105040b0d030c140717100c020f072919030f150308090303160c060801050a030327050301111806040b12070c021306050316081f0603 66
    0x3014041410b4001c88000b18103d4404940030005401032109120082e0300c04140a4049006994a40f000c21001d00c2000d50892964003502c4002d92181002101741d00104856607c1d6806014816000812481242d203889818002861201006c4245681c2c40d02c10780035002c583c5104101400300440d41225082d40c2c032030840c10b02074403500d03290380950400340d441140c4070009041c010440100307440c42c46110100b44241070311400c0141942c43e100984e80c085210706800d071008000c1525690300040750030701c00510407420729135458a0310750300420480040e04030b6841440b49044c200000394002203451496006107803000c40c3c202d9000341303148601f03525a022a4240d420400882c1801c405a0000e1a07070800c6103a81040101c00310003400414080da00414441c11400c000e07943d15000f008005941c4001c5c189030880c441281e035030110340040700001e4051a0750b519148244050329040c071920a810414441c45e550080c5482420b0340c2da5000f40f03070148841c0600d0100f520f02019207401c04006550 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 755257077 1250 755255827 755255849
    0x118090912080f010509060f0a0801020708070209010603020405180901410606250f0b0610031505120304120c060e06040f0603020318061905100e0c0c010204 69
    0x80c560400560340304002000d180001c05941c00650b40501d1511520b050f1000078109010a0303031540c080c0600c040c0e610b045164040c6090380001540e00c400d00042200c1407054039055104c034428410300c0a09801078202c0e0302072600500052100f91110220090040000e403c05403c6803a42082940101108004070789180040856050f040055500c044600c03c450940000c05001800c10310341d00300c50544030303294400d100f04580c4c030500300d010050310080042440321090000c03580e5592076502c2c00079141181e40340d00d03210802003c0d24004c06010114904e41c2014800080243d2024004507081c2c05000d10603000624800130f05842003081e2400780101141c040311007481424007034180052446400300003000d0b8488060301e03007048000c5d902200c288102186603203007070080680180d00001c0c100440800012030305d80b102e21081101d64091401c02d0010b4002501116800c021b6610040c2070b0350100007220000c002e9000c4040c682603012071400000c50300d404c0301c42d4980c0e004e4443c81e80f0520743d40c5 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 755258327 1250 755257077 755257091
    0x60903030724140606130e04030c0b0a0501030b46061410141e1206062506110c0d08011d06040b0a1e0e0901060f05011809 54
    0x2120281010a41c08403080b003003851681144544003d80e854030b0b030740100e1400e980001c034582d410160301818a500e100c6400b8000d01d5200d0500c00700d4682c04035010380c00994600000d1050005143c2820b402800d504003d20540d81562603503201c101c1d01400858031030040440480c00515001787d040c4581e0500800c0c21906a070003c2e2100c102015403121034203980c82d20000185820b100b201c80e1201c18006010666050400790091310094001c1c1c582e2000054104026541d140c0b402400034143c0e4564200c091312402500500b10003181c0090001d8041c0354100040300451b80803801110001d4114842508115010310f0500080c03e00f00c07641115419000c2000541042d01042d044041d401c2c0da03032114116a0303500d085c02860107509004015a02d02500400c410781041c2d080102c58050140404000ea980e034241d2780c825030850550008000294141803011514102c10341c1c2e00324a60b0402481a50304091250840c8085440ba090600040800041d10b0240ea03120101c01400b50800400200c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 755259577 1250 755258327 755258333
    0x14070c0203070e011410140415030509010507020c1c020d2904030806280b0a0e06091305060109030f0303050f180a12030f05150f01110c09060609030307 67
    0x15201184089100703024038400450052120342070b003412038480d10100340d03180d20140c09011080c0410440501003000300c14489480141c0e10340200010441603c0008880c148084018201c44c00686140c0d140d9040c50140464250f001071030703000d400e004a411040031485031030442681c9d000014025001125208500c06002d0b06203086d280c800740399458281d0488488e48013080442c0700300c400402151440c8046507007410031074004d0f10f9007681001100354400c0f042841510740d181941c03001c1d82141e000a2203450b03c96000038204603111003070302c440f410442d40a0002d0314041945020700003065503400045ca0350b81c4100c1600c4002c4d40c206401d4100036201d0308009010307140403100c102c4044286008900000e28480401507885039040150143c0c0070740b41e80b42c049000000c00c0d0070701059111010f071045d481d5070b441518028520021882850740c3d01030144440b454028500c181408880c0703c4c544200040403d50501140e400c0741c1c551035039902c00000070841e000d4441c0194051101003880310130 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 755260827 1250 755259577 755259587
    0xc031823190b0f01030c031b050405090f0c01021219031104030f020117010b0d09082502090c070c06050705120d020a09050906010f030207020a170303100617010b0c011407 75
    0xc0d1900a007080302c259620f02c0c1c65402c02c01c0c0c0030310001703208105101c07007003020446505c00382910310071310086041050760764000a01910026604140c481d0004d1480e204003403020000080c01d95028009451070001c0320489240e41d0080000303200e01c208030901d104844501c281e100400354a0743c0e1360650340752502d034280341c820054806801c07800314040001e01a05000c00c6001281200e03070b0302100c2d501c0c010880002c5005400140380803100140148003412101c01d030b480d1202c440c1c048501707400e5000181d42c01048086400603106031f10380075003001218081142880b06809403030040c2010340d07880c505854018a0324a40354083d03002d800c80401c440080258a4004264045060f9070300c189075070700c1b0020804640c50584180740411007610129040f14020340150802ca4001464112440e17170b036200d41e6203803440e0041c41202c03d410000c1000b904400b10800b4a01800213890000c075040f58013524052a1207040c02418901c010200b00041e840000350008405104041d0b50003181d03003084c0e000901 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 755262077 1250 755260827 755260873
    0x50f1608010c050f0406050c0705060c030a0801090c32030c0307020f0c0307050411070b010803040812040302030c0d060f0e0304060201060801020c0c040e10050c0703030c031823 78
    0x303015401c020304030150911032420383d8000809150003505d003514150007500c2507804604052031038064030700d0000c0c3d40c0d83c421018141c2005400051603903026240002888400140c2000300c84e44e2800c00d40440e000d40c80a118220302048005610201c548100981000701c20200c2c0c6000d0f4000000801c900d0f41c0c08003000d1800303003541da021200a40c43d010b00c2c003a1649240000070f500765101b02400c00040c6401c4d08640704090440c2c103030034640a415120b505c003c2c64241c1007203100ba880050104035001c010412214155000495542803034215070005e0f49400010b54854429080101c0a170140140d6a000c86480b002c060701c20404040c0c0f02c011191240c10500c10300b000340d468020009400e88040c02261036401030240a0a0340a21010401c4001c0801c818107811a01c5039041001c501c2c00b17103104c2d00d406072220b0407426445070814a802000d0750f00d0200306c0c2d010142800c0600790300005504003100d00d50340c000161030781c030b1000c1000c14005224040c1c49a4081c8940c800c40100001d454200b01 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 755263327 1250 755262077 755262089
    0x616030c0b1305120901050d0f05040c051c1211030c010902010f020714270c03150d03230d06171b031c03060b040e15040615050304050f16 61
    0x245640d840b640c001075080c1e81140301520070381040e81d600040b480300500400daa2101410000c0c10070208001c0301c021903000700c3c041209142c0d03a0060109200205d160071000300f030112441000030b158410180d40d41c808414000b0158101e1509140d001800303010111145081101104e07201c3c5501e000c1e4074043c00141509074086550107082c0780444d4030110301e1000755500340d4050409035101d00c040c8003111600000c40d444030140711825034501c3e648241180c0c080c60b10b2403c0d0b1030f1039050080b886203620040e00c00c502e1040b0b8000c0060b00010b40c00070780b840c01c050b02c0035003000003034882071003100c2041c4288008660410320f449004650283c9003410020042211402c44030a0312551000ea03900c0201104882d5141e4401c041602841d01d103c83e81004000d40e6107000b090240e030390f52200045403c41d404c001c0740300030031004012007802002c614840c2a07208075428861a454a55010f4220131020640000c0040000010781440030401c400303900081c40804480d100d030ba9149651032942800e0060b0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 755264577 1250 755263327 755263343
    0x702090a140f06010207120503070203061014030703020a0501080a09120f03141b0705010906050c0403140606240f03070305040b0f040b06010c11100e04062705060616030c 75
    0x1107041c00d81250344091080c03e040c3c005101031800d02c01110101968101708a03190301c01005a00c0050b1002d1014501803903a69550740e01c25170400b05009000480d403400036000368048501003000d607039007080c50307011203601303003803c1c851901d4159a11002d0314080c7c2001d44a04101c8001c081007a03482812601361750202c1e981044030810b0741040700301b00c4400399140d01d418045846500d003201c00741001448503134400d40000640003259500e140c1910303021130b0040003031000814104240609079103c2c2100204150191945140c06000201c40034070140c103640b00030700c01040c0d078920024000c040380c1459080c205035503142d1520074801000b41500303c1e001c84d0342880100124000e1807000c0005401158090628421544c8410046800c0d0050880c1900d8140b0a2000e454484d2914081c0360803c22850b5101c1000c8201d000a02c42a21480ea00c01e04d40300c20840150101c01c0350080d45030510403036040010955442d4440041c034507008002c0c55403a40b45c0c14120440c1055000409024418071503049 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 755265827 1250 755264577 755264581
    0xa1101020c0a0b030402010530060a0905041a07030f020c060723070b15092505040b030a15051005030a0c09031203240602031216050d110702090a14 65
    0x80c0440d90400d071240150000f02400441c0066010300060501e600501c0403054a46918450507504111a200c4200e0700d127400c0010b1101304d05000b01a8070140218000500c03660816070369100f0001d045180d120b170001881d2020503649031280d0040942811806c8e419910380c070f0301803491070f1541401c1d142e81700030a0341521540100ca8040302c81d140c0768807081c49042d0402c03044bd16107000c4900b0060040711007614804c5682e4103a50303059000d40c0580c000c45505d01502d800c410429080000000c1e08006100060108002098441c41240e80c499000e05001c21843d0050b007448510604581005911143c80c080c0034194591200195100d4030844505104441540c4d41c10342d00c1c00c2c941d0002401600e406c1507002485402b9400100540d48ea00301781140120301c440702c031350b101c4000360416401600000360142c240550100c003036030002400051408020020390300a040c40c0b141da080b05401d0341e1612207620b480a201d01c2a6450540c002e8403c00c450b20300743c188030380280003200043d1000c000d2280 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 755267077 1250 755265827 755265829
    0x90601050109080a0609020105090603040501020d0c02030301050f0d1401021617030103030503040605090f030f0d1410030209070e0409081908010303090b092704050717030d0c020f0a1101020c 84
    0x1c2d401d01101c1034000a4050194103031103800240661100a030306000b01007020f22a01d895010041d807241d8042c400060329440e401c80808190344241503028115481480180120350340d1742c00054100104030f864901d882620705c0c145200300d8a422846d442548042035025844445003411950315100d21084140c40c6402181d007400d6010038040070340000c2090001400040c103d51040b508121544110740d0800c0c417601c0350920f036a000e040c3d032030785035480450903030041442c07400303000d5450f003100c010060945407503004201104294032010b4070801082d004a194a4003901800392005000b074020300c0b0303034169400c18000c554032a400c101c0000c407207108a422190f100700c5165050342e40c1a502c903081e0701c0c41c011b280302c5290802d20f03c5a50004c0700c075490a00c5004a0500307070360000450a2224201e02d0503080403800d1004d15801010b14902c08002040310309c1c804402c40e044052880800a40c040040c0d6089240c80529030b00300d000d521440440c0811300441080c214000002682180c15195440c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 755268327 1250 755267077 755267087
    0x6081009231c020a0503031b131412030301030b0a0c1e0203280206041401020405040f050402150721030e030a09080d032d0b1c05010c08070804030e0a150302030906010501 75
    0x80d0050b00640060000c08e17020043d01048030350a00c5401451410410010f842c1c481c24143e40c0e11400304a00040301100403030030070801050a0300f400d00d020750304540c0b4603200c8078041c5000400c0303044400c1d0380307402110101340541d04100202b0540c03d001840a113840f00082e40e070741c1c030121002c4900500b1201d451480b9012100505100c001c603130290106071a00d1b5102204044c5400c10640555000e210100300c58403544501d0074000000b00f404941401c1074010702519a20a000c2c00c001c544003000013902141c1c410105011400c25540f41140940a041080340108007044180302d8900000500401e21075100003140b003602c0101040d02d0514661110560458030302005081c0c11540c0c0b50300c401500e180144c02c500942c01014400700f1017404050024150b030340b40a03141d001c900300075403c140a10100340319041c014410f80c02d20302c1c840e041620014054482c014002020407507988080409038076560040d800408072040c0020f101200100f02802a4000300c42c034a901d4032841d000010f0542c031078 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 755269577 1250 755268327 755268343
    0x1080a0209030c0906010908010e0303061314010e0907050904150c110c0613120311070b0412080d0f02181513180605130c020c010306081009231c02 65
    0x40041c40951a1042400130b1420300406003814001005000100f01400b809819040034009002d190345e071402804000c0c14003041a5000041840c003500d43c841000e00408207810b41c2c01c95a1341145070f40e250010f15107004050740015421011003028881080b485119059140440710030038401c65000100c100c41010300d01c0700114641c1d03c861360004183c10034030f00802241c0240901d050340f90b5124004000c01341c10390981140010034480080010705000d11112010703000402c10300b0310303203407601315183c80c8422a000301514100c00040e820100c034007903034440c0f013600701d07090b5055480b04182c003002c9080c2e402032001e0f035004e10001ca11040408c1d83e21001c441e0701c1e240804050380d40c0303800e000c100d02c2d1600350604e003a40010b5a840d40031450b030307440b41803050082144400200c0c501c001c0349402030400c0c090080e40341c141420301c1d0051250000125138010011110940040e12002c0e50414424042050f0000300c0600000f4040c43e4000d4000700c1c0c500b402542e103001604808060b04800c031390320101 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 755270827 1250 755269577 755269579
    0x3030e06070912020a0321090e1005060d0f1a03070b071e1b0816090513020907141c0606111005040f0b100e0a060b07080d140a02070201080a0209 64
    0x85050140401480c2000803448180017404035011a0345a03a94411410900e5000010100340b0000e80511143d1042100010b0220107141030450305190880d00300d00c0d1064001c1d140b203035001040c5616440c0d0140e0006010800c0c00c1d0342400b501e00b06003103101e0420a85c0d03e465001e801688004246890800c0c00c0701c140c25131060712059031000ca10003012031651404402c4807101440098070070900041b1001001910301280a0844450840914018000c50307512980702d0505050400442e9442d460f002c00e400340d01074441c076090b90707034030f00c01240c3c1d445a1690a110701c80d8041445040c00e41003103905081c044c1100d00070040d4984492040c1d0b00c0c0c400c048000005a440000c002101550340d82100c0e811a200f80006200c10186d41d6034042d201d00200c8c0e0360030200c13111407010407004900c210520b0308040301040810801d4142910b4201c680704582d809007103890001885030395000390340e001a8840f4042c0e4800581400c2100c2c1b800065449460142d000941c08400308006041134800c0300c2040c1c2c4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 755272077 1250 755270827 755270837
    0xc080a080d02030a091703150109060e0d0327090506010206011212050702060a02210f07030e03030d02070c03060b01031a09090a021f02150c0f03100b070b0403030e0607 74
    0x15407010481d010394002450000c0103a01e40410134001402c0641280c800740c6560145a124034088201c072000c2082344807100c1c10403183c1c40040040b990050b204144036032090354812240e41040c01d083d6045080d6451445044800308480721b01c4003a52840681901c070458424041e50711000012650745000380940020f941c8411640300000705040c00c00d0608a259040080c24011203400141568120900940260700004910802d81c4040328198240882007041641001040c019001090052700d50081c14481c002c41684010381e030401c1a02c00d441d8040750117548d01c01d103529100805d00e00e54401110010b0800856107100d60103402855030000c003612003040c02168001c00c10510403006400c0c1020380c0548462800541c80320842c245050140d485120a510f202c41002031412003d003810014524059050100b403054540845420061561032284c0340d44400d44004540c81880e842819040c0c80084e0700401c00090401c41d41c891402603c0c100003140566440a40340e44084501d040010 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 755273327 1250 755272077 755272087
    0x7050a061b06053c07050c0109052b081603111b06090c010e0d02280f150201091127010902071407120206030c0c10090c080a08 56
    0x144507907291801da445405080c06414000e80b0346a04880080c0c41003001030b03001250501d031309081c8200c94403031034100d0b50100b0100b0f40500e84000034400e024044104200c000218000400d009400c4449410381107003d0711000402250b12420240c580f03045c00085054a20a0444850080403c1d500c1282e003c0030b1160000f1f44100110000d02031403007103000c3c2d080144440c480d00c0340041c07c10021a001000180303510304044940c28a0000403c3c6103034100302c007045800520780c80d01e80744640603035415140b0501201d19445003000c0c043c1c2d002c44000c010080c01000082d81d0907076001c0381c0100c841243e03c1112550004c90228241c58030108040c0c5030400040c00030707016048c400c405c80e110003003c042e49600340c4080030891401480070ba000447c4140c0104001040c0950802a6046040d1300c0e0010b086662901041031900100c011003c2d1042c4000310002d001c00500400b115180c480000542e0300a00240022100801c0d410b9170945942c005107a0200b10a8400100408500d4001a15074100 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 755274577 1250 755273327 755273339
    0x30818010e1002060a2a0f09050d0206090418080712030507050901020d0f03020903030403141b130b18041a24060c030c010e0601030303050a0c0807050307110717010e07050a 76
    0x2610b40c031a5000341c107513901c00e0b00c2190308840b030022000142c0c1596441c7c211900c0745074000c1031a0f07215003006114180480201005981d503104450142009030780100d0783d0403100d120407030024041030b000340c40b828000500104002406c488220007041d2a2030401c05a03c0700e81e02202c0501500760001e000d0f0340098529440c0034040d4070901e04002c3c5074a000351034078212001090868009900440b81e071120a036900c54030342000e000e07000c400240b80c10202614207000700000c00a1603501c0328619002e80d14070898949880e02d0103052811240e49c5040a40c0e4141071801d0300402620741c0c006542c80303c81c10042500c01e07120400c0f01c40c0d190301c61440d01c061845200d00b000410790112450004610003000300ca18509030078000d81c2c0000d01600040c200e01e600d9420040c0644000030002d02c030b41803601400003500ba80180303580382c0004030b80ca03200b910390741c645505560268041c034200180b0f1042b0780e400641150800301c0b40580e211010020300240c8180000966220382034000c1b2a4482819481403080e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 755275827 1250 755274577 755274581
    0x3060b0f070c0302100302071106070c050d0503041e090b030a120e0d05151605040509131a161701050d0b0405150a0504031715090a06030818010e1002060a 68
    0x200e42c054008444a180d91341c0c0020000d042208407140426000718044007400014410950203550036595286029040d82d1061142a42801140d10840c108914081405020001c0e1405001c08002c4000409800581b0405140e101d102e1500481e041c01c101c50f4050502041b0700004681c0602c91a2114103051416240030f210680c50703d40046682404501140c0208402c6c040c040c5440c83c0e98405040c00705540828007900740c00001408800c00c4200305549500c0600ea40c0100c2c0c0a540c0a148452440c0c0500800b5120507110040c3c48090203000c400c40c1400d4580c2d60002d0192a85800358285002118500000344965a4030684440300e8101040e6642e810660141c82801030340e180854890701e00c0a00c6405841001c2d04030f07a110b040004050304402111144003a0803080311701860102d075100e202e8a040300c10035025110703600224580706000d8001c2409550700841d05921454480c0004003410000c0292034000303034103485141e0311420410784228005669501038039490307545a0b0b40c500 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 755277077 1250 755275827 755275837
    0x115090209061c021803070e0406050615070506010503100b130f110c0a020a0603050903030a1140030c121a010b0c010f02030c0403031206030605010b071203060b0f 72
    0x10b0060020041d540302004441c500031100328080f140140c039503207224101c200c2600e0a41d0b0381d502991110105100b4910042c0126078420790042c804101540d070a000724814591202d81d1011071000869081c1c1048808a0054103030f601c140e003183c0e400320740418104203036822614281d401900d00400d40b45044010780061107003501210003c00d502c0b000c5141c0204542c0022101e1040380c002c4480402145000443c010041010345005c1c04603007004030040f500c070f100c0030305030988003aa00d40d00e8405c00c2100c03101b50358207038542d1250822300945446060112070040c4904010750f44c0340004040c1c4800082e4a88130a813a0420005c5602e10300340150300c400c1040b80345e02510b074076060749994841e001001078984c0c040c0c2000e503146500c41141440d92803d6420600c4070002503801482004028501081510b007140c0d01032829403c640c0c43e500c1d02e40e004266135080541058280b0b070000c03580d900b510303004101c9c55110348003103452070300998000c50489040740982412404108803140c030141c0c0485c0074107 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 755278327 1250 755277077 755277079
    0x402090a03020a150e01020c1c0311060a0b1f02060c18041802191505071b060806010f0807080c07140a0311071d06012001060305030d0501080115090209 67
    0x401d07102d800086604880d40e021034681d1004805480389254000128001041c00380002d0108601d08000030f040d0300d0040006c960f0810000d80e40100b450300c0b0320b951215942c0c154060307070700e242807902d8200302800b03080d44124011145100c01030b0b071500c0380a024001d48040c541c0a40015124544c6280741382d1722070103000f2840504c10510200d69a60b5205040b078031041000340841240141c4107000c8a0b10700b210304520384d0126908100802c0c40f60050000c1c2940f81845c1459456685280c40034103034034003500403008a01002d1010030381c1074000a50900031002600c070900e00c00c048000c01c0b103007441c1c03c554450000b800140070450343c0000e030700601040d52044003413002118141b0407480c83c02903282802d90000d81c0b0b010600c208500306020300c102500303c00100c201601080c00c0240081400074243c40c0c10441600da04c154284047c1050018100c01d1100902c0700340c5e980c2c1480c42c1d90b42c00114507850000c0c82d040001800c0d16052180f5040b1554211813040b81d5882d1124000007074210203001 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 755279577 1250 755278327 755278339
    0x1a06100c0503030c0a1e030221060f04021606020c060403020c0a15031a06130609140303160201020a02030604120f031e0c12110408070b030108031207020118050a03020d02030405060405040209 84
    0x40c030008101b015518078510701c15a07006031500500c90b030002010320b6095007030954420380c0050182d207864454980710400c0d001d4130090ba5030070400702c5500e500b411010b000380c585440898841e650707205c0031407004d0007503000c3d42c01c80d01811400c07020031401c1c0400e486800c1503004140207264015010303030407141c500b80e1a105c001c2c040324000701c04036509500140c0d11081c41421020288060f5400c500d104000c1d11650410a02c0540c109010030f82e00d100718540310342482d48607031500045a1080110042e0780703501509032481d509092074100e00c6a0140e41022001c20745140d801c280c603c9c800c1c812943c054a0036031030409440d410580e0a0010201c440403402000055041a204140c1500030305801c0d0200b003080a82c1e0300d10302070000b07050641680003081c0d09641000100a1807c0000c191400000815404082c0380c5400030164010095154440803008055000c1000c3c0b10002c00d03085a070301d00135004d43e000100f0b800000c90b100d214500465502020030300040c0000c0c205507000d40301c000005408 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 755280827 1250 755279577 755279597
    0x30b0609060f0c0607030615030b06041a041a07020d020f04110a09050f10020d05032503090203150c03011a040b04080a1e0209040f08071a06100c0503030c0a 69
    0x401c1c140c2d8401e034104010080b0000715035031803440c02c0045584c40405864204101780c1411000880c8880b002c1e400d00825846041130302c3c85030303154002c0307030000c00400d5003500443d5009061400507410522461803a41402031404c0004100d950403100281e90007490601c800f500340e070820085424040d035154001d9503404415800b0380c8148001d040c0c40301ca03519404410340c600000c002c01c8107402c00c42103004443c1c000b244c43d1300640004000864014a041482e02e998541d003e8a0803401200001d000304500552941207043d0140e100464450080d000e468034850300d9651748098a40c262044103080074100010403081c0c80704004848025100d80c14070b89000e503182c07903039912074020b5000020783d500007408003030401020740344007a1600301c80d4148503500c40481c0c001a40e0f101c0c0080020780f0004000e4009000c101c2c89800300e5080640c0702d080301081c2d50f200f25500b050740d10102e9609004e0403000c64050017031402040c54400c010740c072500452440c2e607000b4070352529400204005041c01421a4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 755282077 1250 755280827 755280829
    0x40b07030e060a06080708010603170304030519050a031b02100b03010e06100510110303010303053a06080a082d070f03020610060e1005130803030a0b030c10030b0609 73
    0x110305809100f42c3e48002c01c5035410181032034100702c0194007003c400d0b032600900f00001264043e6030303c0e06070383c01c0403110745940c0c842c1016601c6204c1e080101510718000c0741c40c40790481d001300140448c0c040300d0b94108401c40c0140c260300c400056400915001d680008000d00d124802c50f0004120100050004104211004183c40c07419100352040c04030100b1301070090105050850200442d018030740f404a000801d9034151b00e490b8401808080e080100c00600e00d4007060384401c0020b1800100d0a180050b2415090740031146034000380b00d8190b80c1d0070528005110700000801054403500900a6481e0140090780c0d01803401c429a8a02d031700c1003110100004030032440d805403840360300903542c10710b07101041d00c5c0080c01d00070300070324212107108170300c7e8288055940094801d1404030f0540e0051400600302c0016101402090080482c0c003e0841c0041882000880030b14041c014407001484204003e80401d52960820501160480417004da482030181c0320340c006280034103025081d0340c0f500c58080 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 755283327 1250 755282077 755282083
    0x1305060109080f0c1e0913020109030b011511031c09020a081e01060e150909011b230403031413030614040308090a02090c0c030f0a020106210506040b07030e 69
    0x408000c3c842e030003100034000309050400040c224030250f0040c0904103c952000074a001c0009481c0f40501d030a0008040d0444e400394050380069600459544c5a56039100c402d651759040304110340d8002201c00350301f80740d008000000e403031304018996900380e8100c040d8503003000185013140342030364045049003000440d40002e2190808110f401154880708030041c500300f5080d200365500400e0881d0b401e4003041881e240c0020101c6947d80100d600e4222074a80c2d1000502400d840241d03060303140740000c03520128a8000b08404140c803004802525950245c90100c581406684000b40100c4e411000e10383d000e440c1d000080070f200018600c019101c1c0c2d180d07203465080790880300c581d69003920078201384801d154001c04041d038000040c41c014104031010340d01280511101911890021a011403202c01080d01407040d42ea5684e9446103075621421002d400901074012482802c1400e98109481c10021342188500700c84141c104000744100d0701c0d19079503a1020003004010400709035031203000501c551814 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 755284577 1250 755283327 755283343
    0x301140702010207020a1409010501030e0f1b040c020115091d0d08040b0c030417090d02060d0f06050a060c03050306040207150e07062a02061308010f0b0f130506010908 74
    0x541c00140c94181e41c1c414440c025101c0d40040d51500302d000d00e4400c3d203541300f036015810740b0004c1c600800c0000c1c00c00200c1d4a04509921420b10a00a503d07144540c1001d1001907a1284800c85041c84800d5800d141030342203800c0c5083c42c0c038101032001c400340030340b50030383d0071241d0011038460600310346a050924041c2030a40c80030050000555003400d10050240000243d43c00c1051040000d24500303059071083c5446070300c0705c102c5021041c003242c0c134250345c1d840760740804c80700341c014240301c4d590102c4840c80c6005040b100300c40303480b0918200f80820182402d2101da4103603801901c41c0c0c0158000c071f48049d40c40d034200411155000e0f0702004000009405444405d5031968219804909404d240f0350650070304005070042c2e020002001000b03070711944ca0f5000411840e1030204c0e440c2102e84d00d03002056107031142807150000e03910101d4000800d01415486281c44810341d0a08101c004241c8040104400c0300300300081d0310000d0a00c80070341d1121a548504d412120504000c168555500441420021701d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 755285827 1250 755284577 755284591
    0x30915020303100509060609040f0209030d0206040c060e061c0b0604030503070b010e07051e0c0a0b0106021b0a060806040b13020a09050a0302060f0a030b03030d050403020d090e0601030902030114 86
    0x8418030150303101c1c080d001000340c0400c44141711649044000700f0003a001d111a15445a070715501d4101500c4c07616812035100e039201405a03180032801c628003039603e03503040d80d045030105144100001c1e5203100b0842c03072000381c0009040b2031070314110004900b980d01400100000700340e66498100b0342562074a00501c001e600c191301941d100d1609081181c1e020f48164070190780640030303804005da0f41c2c0d48101212603100e4607020900a440071480c82105c036000b03070404107609100d42060348007448284030019040307030410782c03c54082400340e0700141b441d0441000b1040d00a15503c40034000a8015009141d10000240002544540b41d00004030442c00070307028440200e500254080030194016513400240809840412950b443e541c042402d6105038411810906008181c030380c41180b107500728800d4110300804983c3c40e21164152500100030507075089015200310025002c002e4064641c0001b15030351009414025500c100040d07002d80f403150001c9a01d9541c03024459428581d442803a402850 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 755287077 1250 755285827 755285833
    0x50405090f01091409030a180e0a1b020c0108040b0a0e0d0f0306090603020607020603040f08070b070e0102152403030f030615072402040305010207060b0f19030f03091502 75
    0x4500902030f02118600300e503e400e0b4051400c1084900c40000040342c81846240c542440c0d17604000041c12502c1c6119040305014a4055090004040c16070308444070880c0c0a076080c100e8800a994140d9a402e845006070740030540d01d100140c042105080001d40c00000c001c2c022031080201c503010344c140a8a0032095020400343c00140c8060ba0740b42c0326200181c10244004c100c1c15003190001645400f41400007480381000000103030400c10040c078007843d01da0740280d00a07100c0034589011059100101c400000040c0c070a0030315403582d031002440640c006810003031002543c03507800c0315410b002d44c1440340800c0045412100c1c091078408000800c4050407001e2a2512070a003e000c0254841e510103208406481c10701054002c1012400105820500450340000c83c1e0b243c80541c001900035940041d02c1544080790480c20b00146400001824000701e03010b50701c00c030210041010a218202018144080300d240070f00000720b2050800f8103050190400f41406503544107034100d17540a2041040050b0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 755288327 1250 755287077 755287079
    0x503161215021b0604141902060a05090a06050408101404062f0705060106170a0e1e0f0607030513032115080f1b0405060a090c090311030105011410050405090f01 71
    0x201b0742c0b00a28810781110180481c9515008100354020036141c003c0d01c20000005e4600c06903000e0011901040f80141403002c80030342e6030b48060321a402c240f007035030814001d010050712058070350701c5070101006e45140400510b45540d112040144141004d070411204011070300810080d003020b0810320010280009603803032540e45081403c010040c1c3c40b020601800184400d41c10b444504840d5002e440290002420282d00061a01d0010319916000b11058421003000410101148141e2000081c0c41211515216038800310100d52089400080c81255176100c440003038411089416010f000040b041b0b48000d400782488101c032071409803100f074005061810000340000f402113800705441080500303004007010000e02000c05012241911603991100005c4150761149400000340104800400040e040c84102500e4031001c0d001c00c1e519244e515621502a00d014040e09050350b144004600701c9240754000d1141a100d00800c01e41840404e000100d01501d5244115110b0031805010780015 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 755289577 1250 755288327 755288333
    0x803160f14010204181407020d1d0a061e090b160f061104030b13150b0102150106121104050d0602070f080703030501150c020102060414030706060f0503161215021b0604 74
    0x2200448078171400c4140c8001005a915004a2700b80c0703081000d070031318813500b444c01180c101c1d0b0b1044c01c1402d02d610120300c1c0c90214940350312446170b4908801c00c5000d0080c1b0100201e00707032000c102c184200c043d81603003000004454100c0100c6c00410a2080700c0720300610140341e542005803074086000c0d49840c4c1000c00d08100b0f2110440b511030304600342401002184559440341e4001d00c00b455071700481c0a44481c00c000c2c41c0d900c200100d00c02c0c0c0d81a00f8542c209035031290750050100ea400480c0c5000d90341090300340095000000704640866000410018209006540300c1d0007940015406441604000d82210301203081e4000030940184284c0d000202503050285070365400c16071303000c810b00300700395921114010b0341c0009505410a411241c80910f01044c0000d0134518868540c000b032450b818280700140c01100c4400d40d805491003102a40d008607500c582c01d80c0280440d200740c518401e0403052010100d920781c1c0005102003c902009490a81d40300c2412501d0345040a403271034507612400401c014 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 755290827 1250 755289577 755289581
    0x10e0109052806051005030105040302010e0705010f0203041a0c0706080a060906050303030411040f0c02011505030a0302120a170c130e010602100213030c0e0108070803160f1401020418 81
    0x3016103031900200354a2460041814030b462000514003aa1540400e00c0c40001d00240401408024028009450913180081c00b03004110301141c0c2a109410002c43e0541c041d0600c1c2c454124a58005c5042c01c0c03409511849040d0090502580c40d8000c1004604440b4140080340240c9250340b212401c606051800c13604a5000d03601015601e480e111041c441aa008001c0300d81054201c0c0c1d001154461060003c1c00600c1e0810659010600d070004201c3c3c003a03010f400601d04186e81000e00c1e4444ca54580c141a2540c0382c0c0900200160810b00d0074810307102204000e01228492407806071100c1440405200c178411055450a014140104441c0f04614258885e0405041d44280c1e41406516266000c1d60310040c0c1c1071a0002e45401003200f50540c070103203a1500c02580c0001c0b550f050380d6a50760702c40c028814280500c8445015003100401c06000000072140c0444844440001c1d480b0796480e0502c126030f85000c100e030502c0344103224401500382400030340081d003890015004112550030024007 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 755292077 1250 755290827 755290843
    0x708031b0403020d030302070c091e0b0f0f27071106061807140f07060603051c020d050903100507021b090c0a1103160803040b130c18020c010e010905 66
    0x94000001c0100b4401070f1100d0f10340c65803040d894240940c0381c10007071410071035240d03840c3c00c0404540d16054403a040340a603a103012402c4140342c8000c02000c280340e020302940d1144900e10941290b05200c40700e1140c20401841c083c3c50049610105544080403800c0410038419101840002c03c0d660308920b082c0028007507542c129104903201030280c25101890000183e000f0b01e640c0034002001244c0c40c484801000301c44101043c0d03000c0b1580d0303070764920b484801040c280c0000d480710b03c81d840440c403086982d981c545400c0890f070740090180c8801c2c11380846d010fa1160540c240c15004000d0559040500b501880e405040560098107120141e07001e40544980720080c014800c0b003580c0c051081c0c4107a40d408440d0311403c0b07071070305060a85001c0035103480c5108440150301d032822907440c50000d20014001542c05a032140000350705a0f101d80c45481502d41c048140505030b021043d01c10460b0703a00c0318000b5000310008100150a082e103020030f41d800c480b0308035200d8204d85d448803c140c04201c82880710702 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 755293327 1250 755292077 755292121
    0x50f0105040e0c2b0c0803040e0705040f15030207060c03090311150f15130519020309060a050402210709060e070504090b0f0616020f09070c0204090f020303070803 72
    0x142c120400007488003440d40b06032402004c4120340c1880c2d42203110f44a050940d040700c0700c4500300f59280e81b036560b258000d22804606801210208001d9841401180c040b1011603e070b1003141410121b2465000040c5d180b00c2c030178107034204480c0c000144c150089022101c0309480009410400d4140a04604c0c007407032014920b40c100110002c0492445071041e40c00240130610040b540d51841640c0705002030710050103034003603501584000500b5407034210301d10400d050b2144010055900206400740e0000b5101c059898102e58002a0101a40c1d0303c03c0761300c6400101045e10102242d20300905070502860900056000301405000190140c0170b136070300800b40010620518034100340700070443d018034019250310588542d01d00b00c0654580c80307203858548008000f0f6586802c440c81c00405882c0d240c03000c0b40144a0085600018079014010b98421140340e2103070b849001c62036080000500280d0005c0fa0724500700c03032480025880400182c003030103114000d02c55880c00d12180d49802c0092000d008 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 755294577 1250 755293327 755293333
    0x9210206010b19110a06050907080c04110904050703061a0c060c0304050c010c08070602040b0d1808040605070c0b07030810140f0d1a0a020d0c051e0304030504030501050f0105040e 79
    0x1243d200312a914a06121030b4003854801603c40581220608210300140007030842d500301810b21071114400b1807100110b801c140c003202d100301901030500064a101c040124030030241408910901c1c10150003855101200e03250004400d525a0544c0904c41e0718211211545000030030000c108031801c01c075031a00b20350710000490071883c00340d075403955030704200a20a04011640c5400c104001100050740d00342d031390062042d034455894919042150304035440000b029420134000e400c0e0052076100b00c0c010a50400102407600d17080c035800740c0d01a44030042c1111024180c3c080000c0003c0c0ca6400781074124426501c24140d410400200302c0c101c8001d030441c2c0f0042c0301032060351400783c1c0c41d2800d15012500c15540032503c44464141100c08203800b0311030041681101080011000c40ca03401003010800c0c00104121080d5018812180d034091003000c21001d0b00d0503042e104402180c440a1548140f1034035200d841c0c55166075030b4038252103054500c060001c16100041c001c0d45031034020f0404a4103c4401 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 755295827 1250 755294577 755294587
    0x70608091209190320060a020705060318070801061a04060c1101030e0a03020c01110c01120905030412210503040b060405040201091e090b0303031b0d09210206010b 72
    0x12600c5222a00308512407041c0020091074070740311500c0042140c03203142c58004403d503682c280070807604080c0013003483c101144a001c00c03491510806482001009074003d20042d81844140440ea03800504111010003400350510086e40301040034074058405040040f4041d440e080c8801810040102c401da040c1e80306000c28411507030700032500c409650300b001011044844200c0168000c000d1004920100d0248007044810f2540010780400151401e03a141c8503203481208a403138075040380d6140c803400541c008034526041d41582d004018024001c4007924507065580702280c1e12010003560841350b001010f410752803185550f4186ca20b440c107241c28030711324516007551490141c800003400c0c0b07441241d655000c40c7c20369100c0d0403140c0141000e071419113900d245032561b03007038031301254455103802d203092940d000d01c2c604020003541d001740c140b905201d030840c070314101300340b04c0341c0010740c07418680d0b581c404224002c940d400307040d801e1500104107807008004050304020305062050304445114541080 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 755297077 1250 755295827 755295841
    0x220615050d03080f1f14030d0f0f140d0501081606050304020609011101060810020c0105060d030c0f1403070c0518010308191707050408061e01060e060712020609070608 74
    0x315143e0302c010300e02031380c0c00940e4a50b11002c0c600e525990700c400d020342001c0300102e07140404005c000b54406045048404146140b582202c0c3c2e10055003000b80081c00500c0c8011480703015420000e1300f400d201045500745640700007034000321070f0241e10603001940280540a440700b01864000080e00c441d25085146241075000b10b2124840ca01a007410494414106441c0b1802980100c001c2e000d10340c00e4504080500d44c08002039003084031001603d5280102188051601c581c100a12a61544a441507001c0d6602ea03080c0c20300c0350920507190408440b40c0c0611b1400f0a0008040541c40742200b03007089800c12060241200b40c0f11140e4206104010041c0080740f00368050303480c840c40042d41d80905500d6003004551058520b810105c034004050184580c0039007100151059400c0c9500716a0f00c2da9032a0b440100c01c0c075140c81c0c4070b801c801c038150060090718881c03903034001031400103050030385440d4240c1d070707464010720f46200a1001600114288589031070306004100040c0720a14081e00709081c024 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 755298327 1250 755297077 755297087
    0x140124090b0d02070c06031e090c0303180905010b070308071704080918010308041d010e06040b011b0309080106081b0d1a09012f070209220615050d03 66
    0x80501d200e01d00e008034188000d07446580444a403a64041486a8500c4d500c81c4040c01a000d48040501143c1004441b200405014400d0740036844e040304440401a26544055441600e207400510246801d8040801c440c0d07994003540b4001c03c11460100d0b038a0446050040000502500a100308940d65990781d200c5030409168079005a009010b480c0e69440c20340002e0404c2211041150080100c03800010501c040303580500125820081581d400c40c6034142004c001110074058108400c11080c042801410300e540440c2c001241814407509044900c003020303105807804034040380010304100050003030f40ca085c020304004144550042806103003d104400e00820505c0003103000e078000c0d418110502c003101111184815101100e4415800c2c40b401442c0645141304078802c000d803050222074001420342d81c101007100301c500060ae007450784c0e59080003c0d10718003a090a103031100380c66003030190741944810a800d5500c0b4410009000d4540b4030350440380c070b074a035018610442c40d0365000400b0903088 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 755299577 1250 755298327 755298329
    0x3020f1206041b18050612010b01050a08060406030b010e15030606060a081e0106090314070509010e1b0a050d0605031c08090a06110301090f0e0c0f0d0614012409 71
    0x1200d5043d14441c030b2808209140b100b103038041c0d110040c101403100008081980140d00030182070300c3c5d1400701021600c02c142078428290390240054400c10180000794442d03d080d5420044c01000855225503d850315442d014023a0008a85000700c0014420081e914101e0144c80c1c4500740c001e00317294a42003000440a01610020109220040c0001160710314408101490001510424052540c491100402284242c041100d0070854a2400b040c6400006240e008940006191480580c204040c00144013406006051100507080c000e0b050700b003006024000c8150240d540c203071141c00801191742910410750005000740c0000d041c010b03880340c900e0705003503c01c10203041c100c80b40d89442070107514280b902040030704854070f050202d042070f44046000303604035950394030107105106081c0052400c59110703820102055101038000c034264100100c00e0103000800618a581d4810141c41d07000a58241000e0810030b48509001403000b410a030414030701d84900c01e60b5040c040c0c51000070103402c2d0b40003 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 755300827 1250 755299577 755299583
    0xc030a0b100e190503070e0403090b03060a0506070809090106110c040b0303070303181a01090b0301020310051002011d0102030f010b0f160f15060510020f03070609210903020f120604 80
    0x10f0140c00c0340c00c048900036103070b00408001d4101c9000586e50780149408202c180c41c1100042e0a11800040c16059101903034002c55004140d0705407a0b1400b02005619801407404942007403051101041e40d45e60743c01d010b40200580d07228844000390513a021801d0141803500070344102e2620581c040700d40c500101743c0c1c02a41e0f1609001801d00041040070700380702c2d1041401804090024100c0c601400001000340c102d0742010310922404c0a040f0401d404d03070004850809205001610030407003441e0000c07021528030040c0c0000140300f03850310150713110407401c01c103210026074001040c0215145490085030042907040610360515022215010481c42070303001c0200c00c14140e4455500b480141c40002e0318290f40450060b00d070300107007411540904480d11030b60703118003120080c0000560010910301d0b404000703640618030380501650b0308001040404820f440c04140071600c022a64600d80100340c100c4155114500070328514070400940f1900070350007078050314840508685145001406a406c80c0e4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 755302077 1250 755300827 755300839
    0x18030b06030c10110d030501051815042408010c0801090b0303040909051e0c22020c0d0206010317040b03160e09160212070c0b0d06030b0c030a0b100e 66
    0x16684002450300700700b00c500c958090008040c4840300d6070801d440c004495421021303200d880b082d203142501103440034854203410400e0f90a071100c034991400c8103a40e000e017058802d400c400040401080841709103200c0f0700004010b0710880150890000178500c0204846c0b402030066a0004030018180c21040c450340d0a040e84071400007249960901c181d6014001840d010010f4800c50704000383c0d1501c0059003607038980044003002c65060304c04561500c28410241180c100030302c00100321250949100305071181c16500707100028402005200c1d40031940c00300c0d4000c0403954198100708501100165150f0140d1000304800c000c2200244103032944910310760784001d02101c43c400705450a03030301440d0050b032008a070010414085066100900c0710000c640c01c4441030070741c0a19a02e0684103140c0054001880a5020007130403c48100a1100c2e801c00705011541c1c0e5540e5860529000c001d58400940401c04400c0004861051150404502d42201e48010554414801408020600031414000c034 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 755303327 1250 755302077 755302081
    0x60a181202010219200c01050a0507020406030507090903080c0304020f0433080705121009022805010e010507030e010305070309081306111b060901110d02011b18030b 73
    0x381c000e43c151407a2011244045054a0151500401d200101c074032803216800368a04040b207018001030700c24020701060312813914280c96520142e8076900480022640039468880c04000102c0130b122203001170211581c0895505003600c2c010f0005c0c2402452121714400500801005d0307a28070351010604002035800241e04481c504038910842c19600c48404001c0c58660b0404299007003042c02406c44000e00296123070a134858040250744415000820200c0d400f40f1a05c02107071560b580b02060052004010040019200c14540310569400c581da10702c00c5148070040020f940c01000071220510700b4a030640c54a4100e0313030003030000c6000c4120541055603540014210501076406030500c942c0103140c1c075450b503410206e2119a2015401500c000842040303846503030200008010b000180e1000c01078021007184d5041c0601600300600031810044007401044030f1942c01d1240c054080615070010410405c001203007020369180c081c0c50300030080e216403d0344100014030440025680d01c4225a4a15 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 755304577 1250 755303327 755303363
    0x40b13060f091b1202011e0c020d080403021509030d030e0c031b040f0203010521032503110601060e010509040b06031006170c03270105090f060a18 65
    0x804001005446451400300d8180a1081007558440310301c3c43c002041c400c1031340319414011200007005009001c51005130144101510140d038000200c5d40da4944210002543d400007007140400700030a40324210001024402d42c01d01c04d1904400c0c2e01b0400c0144d20740750000011a03520480710806504150303841d9940314840000348020803461034001c080f41c01c22001c0500301c543c40c03010b20b809284200d10308682c440c5003801b18029207049900041c01ca0900205602118100c5003000d6041621400300f0004a5110240555000211000d00000c481108018500030b0108404004190010340c0300c0c1004200540e4801e8026426440c04c1c604030707885060907400324001d0600344420720380c03000000c4200311688079000c00d80c0c800c07512690765101c550000d9004806800c0d50541d000d00107800304100082c10251001c056200708054070203117508a41134441d030a42152000e5034004034a8028030a154108041008041d811107401102000208204910400c8142c010365005040b405480c083e4840 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 755305827 1250 755304577 755304581
    0x31a0a0204150c020d02150a03140c16031701090603020102010e011401051504090207060c200a111c050705010e03011407081f080c1512040314070f0803100e040b1306 73
    0x1002e9405003c08241048087c84082e071a04035180000010785001c00c039041e480c01c480e20b21402807142420492500130212030103d083c0d032048a0a40c240000d030301e005100d5a80652016000303144003100040d066045100081c00d40b0300100154401e80c6c10103030a04900308909802c60704650007102c1c8036031b10091682c20703114940916800000c84a00c041464400c1c08900c0d00301004100d801d0f070701e03a02010304070ba0403549207902c2c10710980c203140e02060041c1c0015103141e44581c40c8040080c180030320900d407548000500440310b4411a800c0d0080b640030002541c00580c02009100700702d00a000b03100e804d0301c0701c0350100030090440c02041081408903d0103c0c9001060100c007009100340e180080e10340e09032030345d20300da00500c81c0d005951a040e03403081ca500d414141d800b8544d1a00d4610b0090700d40b0744080f0f0703941c0c040d01e0203080c014030204221400a09451468400f4900c03c220b00390700d0340341410508502140e036601c00d1014001180030000010307024591903500c00c20b50242e0302c24695040c100040 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 755307077 1250 755305827 755305849
    0xa0b0f06030705060f130b040807060f1b0f150204050627060c010618110d050c040803160b0603030a020316060609090311010606021603140313031a0a0204150c02 71
    0x3130042c20000c1c1c102e04044044004160f07042242d007109181a54a440042d494880ca10540c0641d412a44007400030038411892a5503243c01490108400c4400c1880c903070902c00c10032000c485280002d2000c8040100e50342118100c02c01a0008504040c81c1074007250052040d418a140741c000c010684452400c03e80190030000200500010b8880109031a8640200b0440c014100c0c1c100e00201020700701203080c0150204a0044200d1070700b800c0c041c40d8000b0150401414488441ca014407000c103613074200f00003500e403103511070026000b07812080c1000c00444002901407402500200108506039400204851107c1024001d4130060143c900380800204810f400488040d400c1801e174905141e4889012504045004000c124090740d07040c0903a03031204062070b0038550b8042c05a082000c69581d00d840180c92541205481c906844504501d0300381c05203410881e01c02505006c5800041c2061b00c03100da2003018800e007145040c1c1003109000380741c0c00204c81081040f501c0d00d03450b030440d1240c00e001e02e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 755308327 1250 755307077 755307079
    0x506040f0627110703200616030e01140c0d0207300309021c06230106020717030f0f0705010e010f0b0f0a0303180b0301091407020a0b0f06030705 64
    0x2020302d4451204045180340e0201405500902440c1180c0d00c0c48248140c180f84985889120319248075039500341e0301d07454040c14140990001040c01c04001000340b24103481429110b51018041a0141020741102c0246194800f03a03894074098600780880101d03070540040d8a080c12607203404540d0a6100a440352910080c080389100560340e4041a054210000d00f0000081070b90304070b080000218212882208041d500c5884419895a5884000141902c07680035880210f1045c01e0700c00040750b071a030446400c101d003d4540004120183e030510080d005050000c1c444002da15944030515568000d00341150a404000182e120804240904481e04503034410000d00000d180042182c2c000c4c1b030340014001459060520700e00203403422900c88080c43c040200001c40d81401c6440850768070f01e0740075040c50010f44000010600c00c1500700a18002c00c00000d020401000d070200c010110f200c0034000030203540c42042c3c650001000b20400b02d80c441c003080343c0009960384000009140001540c405 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 755309577 1250 755308327 755308331
    0xb060c0102040605030601030f090b16110a0f02120703112b050d080a2705071d0601120204050d030e15130509060d030f050325020f0d0e0102100506040f 67
    0x10703c00d030b006806540318036400d880400105400b8202041030783e468480090101c940705000441c180c1d00c2c4020007160000c03516219103030400e0195070502e001402c4405807a407800c1c68869030118580150300c0400703000600043c1002500e107a0781c803840000b14803e07487c031450002580c7e4030400410026146400030813402503d454595082568a8100e1200020b00040b01500017a4040d4018058115060348482520f1801c0c00010759001d00e682034103200f1038050166100001c2c0060004280b49010024040b0310351150a101002521280e009800702c2020340c0140410011642c41012820945816003015078030f6030202000596840c0c415002140e00100202d4407600c0c00607104e0b01030054940a44060201d522103e04000051071000170041c0080e6003580c02c050154400c0018540040210090b01030b505802038109a180340307110716030f80c0140d001c2140080e40480400256000040605010340380c0501140000d40b038804c410f40c1207190940f82d0020450944580d1300150390140301d03d1003 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 755310827 1250 755309577 755309579
    0x210912031519170f0705013c020d020d03090c031202120f090a0e010e010b0f070f11010305060906090c0703090e040305041508010f3003090f24030b060c010204 70
    0x1040340d10308003000d8010540c4605402c00c1505100005d200b41500e030140c49012162540310b01820040041410b0010b400411103080500341e041e034021000c1c401456006880003004000c402454402140a5402010f003000d01034808960300c202920b05903900041034001503041460268540313042d02003a406074920029500c0c003490030910207800075840840b5500702403940c4001841c440c030030078002e1140032001d08004000080c03402e00100359420081404030306040705c0f82c4524903610088078040c1c07841e09401e080b01d5402e690600c201d41c2d01000440e600d100d2420003401180060381c000f407620100460000e0395100303260240f17041600924540050202915040c5801003180d0070600c1402810200140d00442c0c5138061943c0354143c800d070707541d0a900140b820310b802c2c02a0138070200e030a60001c2d030824000c40500072010f0520055019484180c115407400c03210000c2c1c0d061039400b00310140c507006000729404466011001510046160109801041800041c4c1c2d83c421a23110310a40e40c40054 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 755312077 1250 755310827 755310839
    0xa050f07050f04020301030b0f090a0605010603060f170a02090603010f05090a0311060121080906130302030d020d050f130503031209190302030d0e010b06210912031519 74
    0x12440306941042ea6030030001000c032010b10041e8002030000400350807400300054103030f0000580079a0f002581004507403034240141c45000842c0e50a8224100280d00c0351424844818504006801004441d0f42840d10085604d009034960550304d400074032460100000c035106982c2500b203000e0b0070783c103c50204440d084c01c1e00e400d0b03a903440740041200450002e00821030b2018010813140c2c102e07001048901c00540002e10300c05070b4091403080458a00c802070004a00507104c42c40a4400d00c0004102c1806050450041500d0040d140903900210760044d429050780690110660300030401d640c415540b5880c166081031590301554205075050b100c0424450042c41043e00381a0080c82c6010582d10000320303901d6002c20003941901c002d4050303441040402c00190003075100c0038a400b018000050080e84903030000ba8194450001004aa5540134030880c181100010460304a078000c030003040404070303144103c0401d01009109075425451500341003410b0712241c02c420588802604040452070b2184 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 755313327 1250 755312077 755312083
    0x510050c150601080114061e03100f05130b0d02030109031d09040803040326010605090306130f020d051513030f0c0b15060c010c1e0c0c03030f020a050f 67
    0x4424a000c500c99014000c41004407000707400d0282030103070b489803020b0382000943c9182c80e0000182c16004a4200985488442e42805207440210382c100c51a035a400d00200110500c04243c010b0704c00760101200400c46a5901541001d40c51221040840d200000b0000548455001c00001e0340550900785c5940801d58000d0301110701e4101e010f860041c22051a040c0100203c0c03c54004201041c108003003000309000b182c10b110915890003c1909a180c1c0841c006540031742a800100071a2011907140081d240600210b5400040745558075481d10643c0c48140c1c0c0d1021070384000e0302850714407d041d01440b0091041c5001d4201441400f6018144200440c400d910210429130000d01405440740d0194801c0590b050304a8020b14982d0654a4002c00d07100016441c1d40c0d420382c044000c018803007561000f809554100c032a940c44041031b241c000c00d140141044426240000c0000c2c60700800006240c0074504010340b40c00d8501300c1c0c142e0031442e4061385032142041c0d02408038071405520800d40a400 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 755314577 1250 755313327 755313337
    0x610030915060e0c0408030706020d090c061110020c0309040c05070501020a120b030f0606010f02010b0d0c03050f06010807062f010e011a0307051509100f140715050c04051005 77
    0x403c010b544075540ea007003a84018021401108616013040104001241098001d8100910a5000014400d1241d95604d1000c141030f1b0004010492034500c02d0540369061145c0008070449000079460402550041e54a9210710380000d0303c11540c952055031000c1c4645c040e90409a4048001c5540f261012806803134452a10701164056003411001001418040340c110041c555990040401d0b84526005580550b04210688110741d0f84035181604d580d9000b801d40c01d0240559610b008103030440c28164109410f0a400c802d0a62103203004104003400000c00000b00c5904d07281c0854800c0906004058021214000080d6400d4501c803c3c1c0704000198846ca182c0341d4050000c12008407401c4440c10808044038a640d45030300018406c2005040c484c8461034180c0701c0004480c54085038000085000180b800354a00141d02500b0004450384c00c1014200e04c042e2140d004c5080c00651307500c10021300c01100310046419128008551441d140009440140c84000c2c0005481c294840f0000d00356001 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 755315827 1250 755314577 755314589
    0xf24030a060f0501030b100e0625020f0a03050319031107060e150114131116030f1b080a0915031517030f0a0c0204060f0510110303061003091506 64
    0x1c8400b000440d0b6000c0d101d40d40074902c0140c00094003c081100540f22000c2d08811107070449000c205210240c01890304030752485c00001038101e006c038128018403d81c90ae00740c142602803080c0d600103101044002003071711360900d00c0b0040300c030340e582d80307200201c015024810340b2044194010695904101d4a41c110390340b0307084100110340055040800600c0a44028071882c0d4400003010b0700034503241089491340312049508080420038211400041c21154015031594020284026008041550121440091030020710b42906503200c19442c07840c030075601c030340300034010100002e4812480380a03194100003004002074020b035080101e100034009d805c4004030303081c19010240c804074000700c62841200115181000131401c0203003140303412415038010401311062065082078440140e0f254000c420182c220000136888040c1383c40f080c4160000b51041e01424024505451034001c0800000e903540b002003201d0052a042c0d55013020b400501c40d0041c0501104100c0ca80d241703025145170007410840e06 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 755317077 1250 755315827 755315849
    0x1a0c0a030515060405010e0420030f0106080708070309021206070504060909091101050702060403150219030e0a020f060904060f062a020402030408040512010c0f020304050f24030a06 80
    0x1a0b0705550200150000380b00c0ca41c8610107004c00d1102d544035105030048000c0203080000c4190405690010052104c0205008100d001081141488a182a86004090b24200400141403201000c3d0844600814503c00c0503981d100c15019552505200c024162800003555441d00b4801002006a0f00600945012901404c0f0000e00d818051040e8645d0f01e82081c000c0021b104031500445144c2c0c480a4103a0303000c00c062001101054440e400e41c0c11442c00f0401c0140e44034140314801440d00051384d6131509240c07078101c04081c0207401145920340640e0456500d071403110a0310028505006948415030010301d03266012543e421072011071416030705036407903414044010038003610010040100c14000761152280303003030041c03c040d0003442c1c0191040f030307540d401d1a4891020410144071000e02c034820740c3d110803a040309036401101e2a5000500c0b0b1000e1403500c2d04140124917410502a041d40c061010352a03114030801c009080c1e89181403004510a5817401c1600490025003814025641004 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 755318327 1250 755317077 755317081
    0x405100918030f020f1e0f070b040f0b040e1605040b0a0c060b030606031513060e010b0a050f0a0501050f0f0408150c0310060e15161e0305090d1a0c0a0305 68
    0x50700028040b001c448000b17000788100c21400900c01004030880032900041d01c02c1004a06080100b4403076400a0300072019015191071408180e14448030090f0711034081680100414800c1054031b4081c0f0390700103034080406403845c10740c0703500300d0341803155511800340704c000881c4c00d40800b90b01c0b921915203d4018101405410107010404d61240010f8072031a40c9540465030318190390540300c048507070142815208054071b05007030300c40c0b00590301c41510160581c0d642e10507880030391920302c0e0028041c0c40152111144d0f46050030100d4070030f959501401c0c0c18800c2c0802c1074025640c040040b85e000c2611403420f580c40382d6868142540e00d03035541c0c0d0080c201c1040719000400c9009800c0559104580f0380e020705540b6440c00b1001d50380c8041050265030803080450080940344024070050215526122650714446040e05090b01440c140038840103640140860902c0841d41c00407c0d1810104200c1300143d41c54a02d16000c1540c007280750b42040a50500340400c010b007814000505603140082d00e09000315 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 755319577 1250 755318327 755318357
    0x80102040e1f0f17060906040221030405041d1209010c12170405160605090607020f01090e0109020d0b010e0a1806180204030501060b0f09040510091803 67
    0x40e024502030360702003561800009100040042c06091561510b501c0000100d031521640880d0100c03540000303d50b8040d003c20702910a1040040c16440418600502285c0c281036000900150031400c00401b400e0b01c51110003100da0701030040b030f00140030007001044240800140196040d62140380481c05020300c1c003010003406610002c40301c2004050b0b4501038030240656500d001c0c0e140304129082003040041800002600e07044205014134000d20003001690403400074a140e04850303412881c204030b81840401016210700c000d880c283e41d412102400c0c01103030b042c0100d5441180354401f00d0b070b10700c1c0c00f40000340d1070791543d00a04a2014000b001c0c010b009400c0c0054401c9203c1802864100194040800c4803410841071540c01554180c0701241c050b5a841c0300e1860711072422480d0190030341c0003e08004100c0d00b40315443c001c00c8010180c03404c281001485103031030302a40d1040c038020340d01c40e000500f0349880d5000c00070203090003407030400044080c5205440c844040e00002c80124510400043c10 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 755320827 1250 755319577 755319581
    0x21303050a062f1305090403090e07020d140d1808040801060b071a07020c0a060215010905010e0c2a0c01030b150409020c15070503070314010b0a180e180105010801 72
    0x1849440e0f4050310015071045001c1515803021401e0f035191400c840c00415142c2e42c030100a4055400b84c0d84900312941450420007056101130800e00a42d4002c821232584150000c0d0b050200440c1200c4007611482000c215034040e0519508100e892001c0300140d10401050034050010b48503850f008016071901d810900b4610312501c440a82480c40e00940810b4991094503070b0341d40b160036403041e1a0440505808600040e00c650442c10140c0c110303045100f0704480400e1658010000b10301d0502c4903514240003885516809041c44025440001d1401c00c0d02c010001002c241900d0400c003411010149404151149242e050050001e07007080a14040303460700c880c980c0c0c840c0090190342403505241c42007120081d4800c103041000c0307014a071300100840000c240c00710b20410068641d20759900d000d210003401c8a182c80c48686070054504014410a1114070031f40303000713142c40c1c240700307400610b0506880003281d4140e000100214103542000141045003040d035003100e6290303000703010740d9807501200c5007 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 755322077 1250 755320827 755320871
    0x140a0506100f0f0e070c022d03010903171302030601090f050a060503060a0f0e01060b3402090c0c0f01021b01050c070320030d1d010b031002030901021303050a06 71
    0x3061415050180501404c201c0c0c0700f40c1003001401c0902e0a03086540c00700701c920503c4c1425860241d00080d090710f64250000307000c6100e0a00f00e008000852180d60041e101d141040701c3c81901e4504280040c0210000ba1706450109400804031406d540c0d460304890301a08040d01c80708140382c00d110124080740001d00034041034a41c0103001d8001665406100c60062424000102190f0344a50859000f44001e1003004050840240c11039034864800705041880040d036503c61030154074208882000758154954181c421742d048031001d459403681c02c0454001c1c000e26030030400b1405002d54000a0000550050991021442d0303440c0342c0c0c04007031010500729101290301c1040c0c41003c010b6280001c0c49203c804451281010a9142c041048903196203160403000314030400990b111910040361040040c04d054100600b00240710786010980441d4403400b003d80c01c0d016154001c8041b0744840400c0d01a250101c285d0b08012204580e2814255a0b9000040c1e0030380340140b81800b01003001c11034414400e = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 755323327 1250 755322077 755322089
    0xc090c1806120209060d141e07140d0e0a0506090d020c0d0c0305030301091a0609031e010e0115050a0b04050d0f020102010623040b0907021009140a0506100f 69
    0x4105072a2400c2038501e450020101c0c0b451580c02c00081d0b409a445401031700b11075a41c82e2000800034824a1020f09021002d058012102d00321500d034514241c195503096848440c1c1e04e42055600e00c00c00804010f0f0161612540e20113040c03a40011650308006594042e00c1c0c06031b411100541c444162041c1c54940d042141401031b0449d03400346980b818440d40001003184210044030840c8e540382c440340e04640082c7c00c600c6115850f51950144d0600701030b0000f4010004a5169140201040009076940100c440c3d0314060012a00c0c260802c0000f035002c020301c10f6404c0d00038007030880c0b8541d40340b161348414000d6034805c0d0200e0b400071400e0444041a2415180d0141c0800000030751621001c031000c00d454012811036480b184c0c0070920003120038640c2d00010f40d00c6042c0300c0d0b80044104000681d280785154030700410a407020444810350019200c181000010b800240c151880c0c144100702040070010029644a656004c3c000c004000514510800102c50b4101805458542640550700184500 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 755324577 1250 755323327 755323367
    0x2030702150405070b04061121070f1703010605040302010314011a0f13090218011701090207140304080303090f07050d0201050c012d1103010b040e040804080105040c090c 75
    0x4503141050840c0d1150814003d0044620650b5070b9040108180d01a4220100103860484030640c0740c00100001e640103040400061003000801d01c0b80764680c051f80d040900117a1803c1c03905020300422000940810b0b089250003662503842c1c010203001540144004ca0001c0d1411000c0d02103100f0803c2d40317905960310990218038941104420050b00e400050460908180402c040308803000700c0800580240f45800d4003680390555a80011100c1800c82d039058103000d07908500c900780c26101c036056819240300c44001a206c885609045e10b401c0e0140710f00c0c030100d00c400180490307010000006140701d080b0100403144280c0b090740355144c81c1c0440d44105a080144003d601c0010342c06400945a000c1d02c02c070001901103001c60300d020250110748071303100440083c404900c0f503a184900a4a1100c1d40c003108076480e55251116810300c5201d03900c100100b0618035804181000480310868008101ca18001e008a05290510a400c0e02d00c0c1d101c0d0080b082c0c5406d9058108071302510880c582e0411102e84 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 755325827 1250 755324577 755324593
    0x609010312210b0a170d1404050303030916080307081905090418062409090204020c1f0b100f0f091701051012081b100905010b1302030702 61
    0x40c0014041c00350141c030103102c201100314110035000109540c0040b94072001080e860004418800c018030710780c0010140200c41c0a00803046400003400400303020280c645003425801c14000c2e0340715401141c001c00d605020000a0040000d40001d900080c241300c081d24486855503403141d07981d40e00c5405402440d0f07020a0003d50405400105054244416404c1007450f110f5034000103070480700d0b00440301001001c1034201005100c0d99109120481401b912582801c010081014130b0210203486440c007800d88900800c2d04644403078050702c00746842e20003160701742c40c20312550007042c00d0280c6042c41500d2030050610601e05d4002120608464a42c4800c03601142200044560344036180f18442484402c031400603155040121015054140c440001786d2410450011002207040e9071151100d0a9400340080204071068100c5c0c50b14048007070502112000c10380c0c0705060080020060380ba103481c003520342091020640048100050480b440d10380b08844008200407400191400c100603842581 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 755327077 1250 755325827 755325833
    0x90a0e090c0a030f03050a05071a090f06010f03020d02150a081f05010f0e04110c010b0319050c010f0207080d090e130c05040f0905010903020f0d050915031306060b130b0306090103 79
    0xb00070074515405292203407070280c892b101e031110003016413500b24480100300204400140b05000c0c80001c0c0d00c1102c040c00e003d51403d401410300101c0743c000a44030f0341e480e5a0b006d0841d560102c29800c1c0b610b901e40d400d61101000360000e4001030003110400c03401c111048000808000b01c10102060f035005841e804400c003855001281c2c0d221450388100e8200e80c0c0c0e000c921130990107001c090110710b901c5d440003240104104042c9800c2c5603512240300306801d02d00080700300248020546950a06080c47c0450100c0300d11101203113001f01c1684a01024007904445004540c2e00204500607980028500d030301644070351141c00d02041030000040c01680b0f1016090040d840c00d50041c2046209100000c00d2140190f1165801c50740845021400350340400c2200341e06890500000c81e0184250400a06084002e000700d8801d05800f0309002c00450000001521120b00d401020940c6400000800003192644600c81c02d59100a42c400d10342000c3d880f00080c2c1c1c104010072644504800b400004169117140d03 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 755328327 1250 755327077 755327087
    0x30c06080a02070b0c0a030e0f1005070203070b0f060108070516060b03030c10020711010207031509021c12082a03040320150f042006090a0e090c0a030f03 68
    0x60481d8070410b4007041068007280b21100c005020380007218200e0307625090010b020302240d09000c10260705405c000d01304c065440d404240070085d03001041e004a000c1c2d5603030404900b140306400008010560980522070500d10140d44107202e03800030b0b242d20b1220345405a0030765850140406030b400c81441107003124000703007107600a030300342c21005400c80341482c2e2295100c50410140c0c10040810941c003042c039609000c001c4101d10541c10080c005000036030f05585480b249a0420444205410b031144000421034542d100701419070b03009684811030004207481d080301001c3c40714403203000041c00c110100380d841003110382031080c4a6640e90310f99402c0031901483e0300c0d5a08010400da060114054202801100c100e000c13100e06810034020740251140f810302c80381d0340310300a80400030075030400c4204000103403284541001d1f0300108031a1415107403140001546441044511504011300c5000042c020030020710142c01024194241d4115003064018006400707003e200c0503100300200035260022034090 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 755329577 1250 755328327 755328331
    0x1061407021c05070801020a02060a0b090906131e0f0c061d04051e1608010614030a05040f150209040e370203150108060703091203110d1b090e01030c0608 68
    0x1c4095031301460ba280c0007079003240c001c24810710251700181c0400c180707500c2d10b1043d03104102003120212148c1c100414826910100201007954a282070310521702488000130700e45804070b01906800c211800b040c50504595500c520007261402c181c91301c0860400d0240c0c9990700e0388240300c0c00c1a100801c0300d60800000d00744c05401d400484801e0f68152981505c2000d409201ea4010f185802848031181c50003012440d0581c001000c01018a80480748600004202c9402010001d00030416480d142040005010f0701e840c024aa0300080035079070002c2c0307445d4020742a43c070700c01c5500b040040da00302d01640e122040b491480400300516581110031010b50340044c1400100d00c2c2c1640c10b032507645c1d40032a1030806040c0c00b1059100403040100414001000000da0212301c80c9030030f04c403240c0c20782d80d0081e810082c200e05006040d1502c42340c200052001003900c1c858900c040061088100d5405c175001d01111400d002d00006500f0741010034283c0310080064126640701c840212140d1071f28504482134040 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 755330827 1250 755329577 755329583
    0x13060528020d0b10020303100b1224040920040e190c0b07051506040b030c040c021f0b010e0904050705150d021c061a22030f0b01061407021c 62
    0x10f2066010039980310710b00504242e5106800440d9681000c83c10503200c0361644c0d10a03014140100805203c09003d0b00720b940d00241c8c081c001502e072817803000c148928004e034404082d0b0010300c0c00c8110018020b40b00034400040d06801504007800721858240405c0c3e80070650181c0c0d569010340001c215202c01d00b1101280f10780510200701006440b00e900000c5c9601201003983c669001e0000318600350030030030351660402003c42d800c2244038604004603440c1c82e60605480d11032540d030b444c0b00c8003660017804000d010104180e4154450300709900e60780300400600304160300241c405c04403480c2600340440154050340c0c0140081c06018a0b010420031485080c46501001c031600780554032089040780007809030140444007003441c80b0701c6e028501c1c04440c0c00d0b5118540c401481b0050003203010030340c0c045540512071485052540c241b4804000344ca152507a1008003118101005034080c450152256070607240140c2c2c8008860805d0302010b1954000c0c0040a5800040d6020f4083d074203040d80127103188948 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 755332077 1250 755330827 755330831
    0x402090a0618020a0201180b04061508070810050a05070c06050411060c0d030c2c15070f05070608060612090c0301020c0d1407170a030b060313060528020d 68
    0x38403011081000341c031282c482e0000c0ca40200b0304100c00307034080c014040c40c0140c19200030f0702c01800f920f40440035071010744040c001c285d8074807007020314003040340c03400000d4580b0008848041d692140f03956a1490000c07090b000080c03030030010a88018107802117600600301c5664981c564605d80d11850001d180c0a4011610484a01c08040854803882c0c0500300001e44070002d001034035610301d4060b0646000f10341800401c29810380c040030005561003e5045207100c0c1002002003041000400c40d03040c0e041c2c000d20110080414600c040154000ea00d4052620070810b5034025686c0701800daa1200e030a450656000c030341406400d45444102c64025840307007100c42200c1000100c01d020a003203074013100040849403c5070510088554001d041a1188071034244001d2801455464401104105851842c1440c82c0010000d940a03c07980165009580080001c1d540382846c0321501440d0303000403c2120100c0c1043c00180049482d088000c0e201104046010401007c041d00030000750b001e800c0030f100b055 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 755333327 1250 755332077 755332079
    0xb010f050a050903060124030501050306070507020a08120c07060f0504090b04290103061d0601030c050c030f03330603100902040909030e19030f1406130c05030d05030402090a06 78
    0x81e804105d054001c105407400e002102c200c2075080031503d0900c900c43c409041c100001088240c40005282d680314203940340c0705840725082e200003848190143d008a54a104002c83d5081d038080050080c169070b040c003411030701540c0d0744031016104105500100070205609000800c09041140c2007041d0f8800003e00000e8041c100d440040101034110311400c4065010844842007942c01d449070b50040d0021041042d40c8400d04c60340c036030003084010940b504064443e08204286801001601c071591b000c802506c1d04c0341e074050440710b203507001196440e580801d1000080c40040e40304901140c543c04240b07940c82402e41c0c0c1d00500640340d00103803170f80d1000c03040d0b0500007400314002c0c4042c3c03010305040180070401c0122801d00410a100030502c0c54401e0b903150350844441c1144001c88002c69600c040d01d50003483c4281411000f0240d40c6185120341d005010030401640c03160b04041102e24492404941c3c0d1540742c070180350b500c00c05003e180000c6101000810f0148c6003400340d8035885408500041802 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 755334577 1250 755333327 755333329
    0xe061506180405090a030224060f0402191205010b070b0f071209241424210607020d051819030305120906070e1002070503070b0702090a0b010f050a0509 67
    0x103d0f0b0131200c2903056003004d480c0404056061101d181d13024184000303c00800c001b401c2c4858450800751032075119488020114080341c845070151900ca840000064810000c0e11002038658072600307121003501454240049900e8076043c0540750340d50b400c070103440c1041d079584102c3c04449001510700d0b414031080045000020400d4018040743c40c3c8102c55400550201c5644014000015542c141c500b0b070800c109124002c41146980350310000700c240c0444950800035050007c022489a095000507158541c00303618600307141032201c6400300740101c55041da01c2d998102e88400803c0c15640004104122218810b11003008805c03c51000611a40800d1ba403d032000303641c819136900803800b01b01c000ca80046200c09d2021306660150050015040c0fa00e00900010309541c4a060356900c103281999106501798820864040a0070014080303070415510392045100c02c0e0002d1004a2080300311100241c0241c0c618040c034410400c040e1076851184020303043c196513035000074010604004043c0b000c0081 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 755335827 1250 755334577 755334581
    0xd0803011205011a010e01080c1c060305060708090304060f110a0303060e0a020432031f1107050d0e0d0c0e04111f03200c0c040e0615061804 62
    0x7005408003080c6005602d01e8060300755070f15980c0b121024113940710303c0106030b608040c030041100c509184c0001d071640c501001000310300a464491b41185000c1c0a464a6503490341e2004086e01d000304111095596079120403500e5140071100f0350050b403c01c0c042045100e004c3e80a00086581340d06210002c550804003442c030340030390480142c00003500c404081140082c1c1803560b94000c42d02c00c0095180ca030a101003802400000208202905021a20006410088a054020304c2002002c1d21501038400403000d00300309507040484181d901c0c110001c102150040101c0358101d601030007801d1100c507028400e40b00340b0310b110b00e0603400940004261f0002810b01c3c4c26100903107698034850080d41032600b000e440d008100c0320241d024001300c0952240e180c503a40146180030204d0710300810100085401d0302901c0c00003c0051501c441c000c45d41d54090714001c80c03000d034044015201084015000d103ca10b0752080d043d104070a58841c100c45031000f0f8200308000344650364220f07500e9444404803c1c00300d41 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 755337077 1250 755335827 755335829
    0x901060302131a01090e01060f0912260702150702010c05030706050412141206120d0306031e03081803070b28060b1b01090b010b1914180d080301 64
    0x802c95a44080080e600558144401c1100c4800c3c070b0031076007050816660342e0503854107000d03801c00d002165111031404e074807904440029007000c002070086e800203464640790a00000210508410805503200498800704007a68040358000b02401c000050302d003100c12669001c008142e041150420780340010980420040c090390303101d4400000d04c1c0c90035050804d44030301480c00070000c1080295146800306004c506462880408202411503500da100020302500c4000710b102201d8000c501009141c01d030190701c0352085901403915070058034100707882003942581c800d00042c0890003080106058410700355202001c40a60b0f41240d14202284c1c5401d600c00400f11030360b50300203031001283c0c00c3d0317900046a55a0000c101d80c00c284103450400f9445503241c043c6480d1080f240103000307500c0d11315000035007083c405540c010860000c00d5840d011202c1c05035001d140850040c00304141201d0f07030103125541c02034020401c010301c0380c282042c034801c0d84440d01d200304001b5840602046d440b404070f50100000c42c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 755338327 1250 755337077 755337109
    0x2007060c0509060417161d0105010206071d130e071404021201031e02040207060b120106261e0c011706061c140f060307051f030c120e01150e1e0901060302 68
    0x1c001f0004806808042c81d03058100504640200c800e21880e6600034028801c207801c200d43c04490a00807001248400b991902c00d80e80c03190800900e10750201c80400d410701604c882d0080c607481c140394003060100382e101d000606010103410328010401300b004011032801046181031080c140d10102d40004041e82c00c8410140e41c80f41d901d164007a00392070300c02141c580404004c0024014149083c44444c0002d2104076040035540300404180d0300c480b020300c40004068914a80003000e946002ca94036030ba0402134000e01d000c41d401c0078480d40042048103000340709002c0102aa44fc03c00f48125004002c030311540500d001c5034884410704030b0300b103071074015034454110f01780000107914007a41012301c0c10040c0ea01c038500a940741c10302050242c4d40081c010315482842d04020600c9030380c180085076190b60201c01040c1c002d01c0c08000c02880312040d000401140c01a808682c1844d460703490590345a00c0a4034030102015401241150070101200ba0340c0d48418050000112180e5a801050010001000030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 755339577 1250 755338327 755338349
    0x81e06060f07080d1812050a1404080106030b0105010203030108031905041212080a020f030a09020d020306130c0608070210091b030b04060c0305070c0602030a2007060c050906041716 80
    0x1082861040c030031603070300030320071442107180344146d8680007850804061400100440040d1019540d0b0140e4146003043c002048113a070343d980d840031124020401c40c04105d03154010b140000a06601c0001628140c55821015510b00010104100c40b0841c83d04103040910100344030005080b49015051a125401001c00c032809404800009044000041c41c02d45681d1051040040082d0160240c913071080807811700088080780c0780000384aa17044880000e5040c42180c0821442c0b00c0b540c80304000039441a002442c8190f1030750000e40b000842100c08200590003905400100140d1790403580a0070300501d5440202080000c4800341072440d5002510b5040d4290144030401400348500c0201902071f00d010072542c10001c100810b81000c840d4050034103500440407603840301c1584c0c0005813409803d00c5001c2c0c8240340091740c030b040d50003400b800c0c1d807101d01e80449140220302440480305003600042c01e603407a19050222040c40c10b01c0c14140078021784602c515410b0304845c40b11007040900300d12071078 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 755340827 1250 755339577 755339587
    0xc0915030b09011410060c0201180806041a0609010509070503040f2316030f140115030b06040b090c09040c0908100b030d02030403083c041401081e06060f0708 70
    0x104d00c88004000d031181241d280c14100800001e41c1c40051444520b90900e029401401e02c0d41059140740c20580040f2198000c03c400c0c03100f0002000b1803d00720928600368802150748000c1004920403092081035007000a0400284881c7c0c03099004561152003601107858644403a100c0382e0704408580d944501c3e0b400000241404254200a9924841c0d560703801000e0769400d55550103555200003000500e08031240c0e054141104003074225161206081c5c20309070081e81c0e20308280c10241c900b03a44160003180b41c0101e01d00b0394104010403c0c410207009001d189060260000e10005100b50407802040050000020850308028019000305085903d00890b00c0a090b8080508141c0869020810355208200800003d0109014fd480249e207005946458290481441c00c941c2061380c40c4103044140c0b004800440c403034850203403041d80c405c4400041340c2202000150380010f0103035541040c4a00d19a0b94094030760000e0b40580d84411f001e4103042c140b5a100c2078941580c1c200c810101d8000d0070100b1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 755342077 1250 755340827 755340851
    0x1180608101e090507050f031e13030f0e010c0c0b0c010e28022206321c0b0a0501080d0e0f12011104120507080a0c0915030b0901 57
    0x340c0380545107203040c07030b11220001c40c40c100b0404018802d80c00070760b483e90b0002d2003050150b015510021801180130b9039914113483c01011000404403000711500c503020100c0c0c40c074500c4000d03941c25168142c0302c0c42403100d16080f06942d0308000800d09030410200303104a000255021140c0310040c01a100b00c15120300d83c0001d8182581c034094092402c59208480c110180d40c20708282d010100d2a200700d1038a500c00c540003190144c3d440e001e24400d10f05201104208001169000c20100c1d900d01c0c4507000303201c4060000d50030700d000072204c0012100300e0042c04251031801000112006a2062084402c0300c20f99850010840040300e2555400c2c0da2180100328040d401c0c881003000011030300e0881405420300b00010003060303803c0308041c003030b0007401d00101070101c0c25401315034050b128442c03043d03c59644042010594012180032241c6029004c0005200300c000500500c07650740c0300000c0b007070481c1800d40701c4000f004d08003070305c001d550306060340000450500440b45004113050320020550401c240 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 755343327 1250 755342077 755342101
    0x36020403030e030c031c1202270117090d050c071d041a010e01030f1703090a0c050406120209072304090c0e0907031508030a0e01021005040c0b030601180608 69
    0x10850034000e0300846d49004c101c1182e4420141082082e050803000100c0003000b41d4024011304065102090503195078800041c04042001d800400c242d070b5a4040842c031801c82111003209813428515580450300036404a4050707005400120301c01c030115603415642c4c1c00d00c1e05003e4161045c003100000f02c0c00a00c01440301c0206d25070341c860241081180b00e5450654001580c1d1130510014000c0e040c0c0c00501d50410644820103101d0009403061180c403414010b0406031500c00031f020460756403c4080d400122402c180c09034404442202c0180703078005c00c16809001801000816074010403c05080c141050503441036a06451442002d03c580c90341d0414110504560b81802403006005000303080b40100e07918100a5680401c0038030300468040b00208448049800c01c4d0031103106030002003544035400c0d07481501201415026422070b6240c99246004a00310340d8284c2c0c02425060303d000d4140410000c1d00c00540d0092418548580c9008000a81000d009030350b4101d10000f8031032005002010040c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 755344577 1250 755343327 755343343
    0x90b0607122c0d02040506060d110a1805130c050c060c1e070b0406020d0e1e070f08070e060d0218090106080d230f03090303160936020403030e03 64
    0x100c0302d980c04180c550030006540032441c00c0300910032501c0b20700180c0c00c0e8803102e0a8500b4100c64800903c0881c00178821123400740c00200f000ca0016100d1003000c195402c90340c1c0d0910484034003608141031850000d2400004d400240210000c4c4541000202840481005914490b135201d0b407d45484d44170500035401e000c042d80c1140040c1e00300a1240001003480b078440305d40c1082d4412001a941c880080d2440b0161020703601043c80c40c000c06400142d4508810000c04c1c5a400000c203070342d225503c40c0d02492402c4118000d0b041300741c0c0241024031800304030912003600240d00400d45c011b50722280c0c2c002040c070343c1a042c115002000314414401d402100b40070302006018448007600c07882c4164040200b401f000c2d41c1101c120301c04d00000582000416a0490390b510913002c2d009941c80c9001c1490075603075481030b50284000040c0311802a00b5601c507241c0c0c1c0080d4ae1182c9041407852400c0f0030140e081240e0500e15210000280d14400e8004035144001c200961184d00c501403948940d60402d801e003100 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 755345827 1250 755344577 755344637
    0x70f140411030711070506160510060b04170111040b0a0206010b09010c1e02041d120703051902120c0d02060c0f0a0c140105010e1915090b060712 64
    0x184001e403101200c0580c00e0360740c03000c070900d402c0c038000c40800112454059180d106a410040c000341c01140d20b800035801d42d40850041088940c0b425100100c241121494030030718510b800f0501c41440b060500f640042200b0442e0000420f0340d50048070307682102d500c550f03c419409000010198940e5805000140c0101050a100f6003417100c034000181054030307948802011013510007241d440f0f00d188001c0d501681500030b4003c0080e03e0900c45400c01c0b1380300b4055085060700c41d02040c441e40e000110708568044d40d00d590707502c0c01c05541542c00100361a884008330258004c901d001e0558403011005400140410700051401c4100726070060704121010b00340c800d600008104140f10704954200305c521032040c51800109624290402200081041000c0700955003004000284426403804480c020906051004054031400364038200320b540001d602400c800c541d200400039807415a0000d40050000344c03400d858002e003540e40d212450b88881603c00811040440e000f1201d0b034605041380c8202c2 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 755347077 1250 755345827 755345831
    0x10c080601020309010c2111120414040c020a0203060f01090b060f04060c230109120309020117091207050d0305130b0a02030709180b010e03160e0402060705070f1404 73
    0x4000c00003d403a4030403600e015050200102e00502004001e4100342c14000c055018000e100011603070060180d0402e0560360761a00c1a0b07008010110603110448085803890030200341d40f801c2000a010113410710304581415802984007078405618240070a40c0728000640b204501581424890030444221564550184500380700c803a46603c1800c007201c05031021400c01380c0452081d4075107514884444101c0800d0b05076110b45814110390150058440756215180030041d00c44600c0341107088424206002c2e0020700080d2942014509010031550009d80c00b030141c0d0a40340310038a800c62183d0014038102ca156002c242c042143c1c2e6850b204e4160851001195080c0042e40ca40300e4200520014040421150b40040859485030003030341c01000402c00d07e40c252054610028414000303010303200745640802c0300c102c001031140c5004103000a00301c90812080c542c96007081e0400340700d0343c00104200d8101ca000c005000c04607400f045014000c011503071104984c07e05115042c40782070100600e0758001c0d8 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 755348327 1250 755347077 755347081
    0x4230109020310050a181b14010509090c21010305160503030406030506030c10020c0405010501140a0305060f060316090905010308090d020409020411070b010b0315090703020d06060908010c08 84
    0x1950100710759041c94070041000c5165102ca4517450300401c2c40c0d0441000d160422001c850410240e0b04407000c2c4008582180d075200355540f44d003012038010985100d4000b0b5000c108034440341c070380203454580000e015601c003410007501708031710b074601035480e07841c01d00c20f03041d00004000300407003000b41075500408950302e039001e0361402000c030359a401203000742c50a054503180015041e8030304210b07407404a040140405040180c03650007030341300d80021503160f000c2c0741000004600f0354052413200310500000d1004030b01d41030341610114000d00c4050b043e00d50018500740007401c03c2e42d604003c0c0d0702501a43c4070b400006004048090075890642d0300400006040c20f004102007484001660001034040ea40007107011032074800a0700800101d44000c0d8824a800c022100c0e100c0c010b0094511140b20b400500780b140d8940051080501084942421305001400b65000c10b051000643d034011001d8140541041c3c00d4160744416078925411450015818410030803852409005141030b504050410007024 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 755349577 1250 755348327 755348329
    0x1c0e0f0a120f0302010b030d0c050c10141305041410061d0d1505160e0f0a0501030207020d0b0405010207020f18041106040305010615090501051c05041a0423010902 72
    0x1014920041c0c100750b82001c002040c14002e40100c40b58035001010b484070b000b92170001900c5600084029240c0780701e042c2c019261814004101d050b00b598540b00c0104450704526400700d65442810074018002c41004006029161402352450803407500940702c0840c6401e150080200d803240c1e01080820008502444106135035020190000750146c0e10005589800c2c14200074034600300c40040c5656140508122034030f6140030072041e00c0c3c540356031b03110b0880100004004101f410016644c0d40084242c0040104e58000c1e8001d060551020f00000809607040d114024400b5003224141d43c80c1e500050007000f1031404048400c0c0b1a641210082620980505421140c0000400c018845140342a030031a450750b0380340c01d4900540e400402800749a40394540001c10210b4201000d021907007040c1e02040c5c039030180090350301c044081c4001020241c8058101e0780980005070042d00e208081c43d88526220356282142c500c264001c54150000322107010506004035080002031140780d14014a42d801 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 755350827 1250 755349577 755349599
    0x60c030c010c2303100302100201050402040b03070e0a050a27060c031a100302130f0509010905011a07020a0f0b120f090703060e01320a020f030c0c1c0e0f0a 69
    0x100c8610f4401a074036542c40c101070003a10307825600003a40c800102e03210124026415000688a00c0c82520180803504103582807507a40c511034081c58480c0c9011078001051040d90740e203c81da0041c00d2034004540c001408469082d2291141d061010300d04150280906019050081048001c42490b0410104140c14915464410408080351107402c00c0104640058400d4056a017105001080303015010341e1505a50b5140c911446801e0050f010b030000055414418411241241c104951414104c1c044c4070030451554042035040340e1102c0304503004124024580800300c050a44841c0c9656600e420703c100d20300d00103005180703422084d2000f04101c0c0505001c140f48007282d50002011039501c8004900901608030026a5100138111503821080800f4251f1100b00c1e0700708038071811100c0c3c2c4900566405902c0b0f103001020b000310040010800c07a540080041c40c1500071402a501c2c40010383c50401d1018180390685c0c0e0002d41220b07108041461714401c10214104125428030034545007880da104 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 755352077 1250 755350827 755350877
    0xf1e140d03181502060c0310120503040e010f1707080d051312050d0f021c081305010f05010f120c0303030b030f1005180c010903080a0e060c030c010c 66
    0x1014800210300142054050380d00702140720511500c0c81c5195440305010656510388000c503800520030403011078010382107001107901541c10f19420102540c145141c40b462034100c0402114588020800001c1e450198110700340a80000304d101c0f800340d443d000d03000013071031311074001ca051942259000308210140092268109112420455110186c0840d00c040c140e98590081854041e803016840800c4400704c3d01c0c201c182000c0c0c03a4000540c1c581c4030200e1b038449010803030f25801d075886280090540e000c1c0d0b41c06a0300c440904a041101d01c40303603882c40d007074501e00c0101c0001561140014000d640750100110054200041102c00c0301e42c19890300d1221000920002d010f059868440c3c24107510f051011a500140070780403540c4590103100c2d01030041008450850500c411019582440400403807101c184000503542d180f6901d00307545a0100705e603c8074a08005015204480f84501c4d260400540240301d0303240c01441c0c0380d6562040d4142984c8c450101d00041204030441d0700d0084801c203003001 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 755353327 1250 755352077 755352079
    0x1060e030313150e03010207120201110c120d021b010603050d0c110f0d02030a0f0c091a1306081504170a0918140406091104020415030e160f1e14 64
    0x12000f400041040c0ca807821800485509940000384030010b01401d25281900034210303034020488a070f005528140320b40a011015000743e017000301c6451355500d500c0e0107802020880c590051500800758040142c202036029140126512008200140003041c270460120800c079062500d0000360130390f591200300084e02402441180c0c040343c03400702c1d2b0300c1c2c1030500002290302138200d401c400090b00b440460f01561001c2154505c0e00b494012501d407485010b003500d4080811810015580783c0002c00054400c04881403030065510310001645800c00c200c090b01101c0d0500e00ca10041c1000c0c00c00403c10b02040350034000c10750003009003034000380c0d001c00b002d01103801341c0c00c0d001041c0c00144000c8004d030a00c60081c07500b142c209c03410301c003d10009511102c11a031080d07071401c4007500c1c0001440184e00542c41032405110a50054000e01070198108605480400c001d844008002000c020868410341c0c00c03200c40c0c0510540144007210b840e030003419025203100010f010203032600070701c0d01001c0182505c0b2 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 755354577 1250 755353327 755353349
    0xb180d0507081219030b01050702043303020411030601020601210c0e0610020c0f061b01020301091506090b030420120d120209060301050f03070902070b01060e030313 73
    0x50900c64280007490103000d2010544600c400d02201d40c0c8140d0b08015450f421000e1544980d01c0018001d02c03900d407070740030180c407000e0401c02150200710082020000604501220300c1441d6540c10300303800c1410405c4405d644110410b401d5005110481c0c0c8040e07401c424a1500300305011090380c0018070507045511403112800514446501c81034290400040141301c00e2460001051514104003254492141610342041c1c86442d44803c80ea0b0b0b0000121190300151011580c00709801c0c010024101100c2c5480c4071141442c40342d010500f240e1090b8082003002d070381c80d801540c840d21840341a1000b000c079803a00c1c428450600c0d141e02510b04c0040c00007040f0514401001e41c0641900070b2210003004028520021045074281860b2211080f480290020301e11103c41c031400c08141c0b095460720100a4140740c2960b00b004203001c07220001d0070403140c2c1445100070006141c1c07010b000801c000d40c071502c03584e469945051405000301d000b00398018802d810034071040c010420941041c008481c0c2c280741c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 755355827 1250 755354577 755354599
    0x203151914030f030c0a032616020c0a0807170a08030112020d0212160605131503063b07021c03060b0a050309061b0409050411060c0c0102070b18 64
    0x920f020a40004403219000204a03440003403c00300398500740c11301030749070407502408401901e2a81c080c0102c0c509040d4019002259000540700369041d0300030440d0049a4004d103484000505a103120b0b4003040e0241d001d4082440703a00b00e8002e001e1001d51a290042404202c030b075440800130b0105014441416000c0c240b8a025913807100c1022802d5500640b128a10130301000e002d80d180c10500c4a0040ca02811f00c400103160f82c8a070044403590303a8991000c000103402e0400c0d0b0300092030320a010300101502d54038003040300014800558182200e00b01141500c03109014160042a0949074030038a0101c402d0400516507000704110703c001c3d60300c0d010031807401504001030b001044e0710b4002002031200441d00c00c00d0190404021800760740a0400c0303e02541c0d949410941d2400d5001e04100940414407041040700c2083d0407840d041841941060408000301c80810107681100000c82e030140c0c811405916036503014480d04d00500071400502d0303d01201c220120149000d0445050b00400441c00 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 755357077 1250 755355827 755355829
    0x6090e070b070812070314090318060408120306060c07180e03130902030a110d15171e010b03010c050403200109050d1a0c120f0610030c0201020c0703060203151914 72
    0x40800b1008074500b87d121500c0c2481c22400381d894002380703035103510180381c40400c10003880d0010985044459500052080f01c07607246c00d0f403002c0e40000d070a86800c0802805084d501c05000d0015102402000302c9442c404429558010242d4118415101c1550010803140440701d0400c80c5003415140c00d80b0303026030360391240385c0720038020a400030f2152a4854045080c0020b54801e41110900350b02100300c0b201820b8480441c1000f070411a2007207040d6030722010380e40190700c00e44284806400000800000e0200d0701c100400d0942e8014510880000d400003001c0c0204521410048807040c110049801c03110010400170b4101e114901610344500c1c40343d200c030000c000601d000c2d00303200c40c50074274a21014184000d20380c502c0c0d085401c2d0050303102c925100103460700980124072807190000400700403030390340511803d03002041c041c905002155020000140e1818040100c0b0000754414200141c6da0700d0a40382d0b81016903520b8986e01c0c81944080c1d10303e080035910f888410140c0340f0a02d000b5208501d244 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 755358327 1250 755357077 755357081
    0x60e010c050f0615040608030c0c09060d12020c12030306010e0418201f1704031e110106090227280906050405040201050d0b1306090e070b0708120703 66
    0x42c08501510441080260b410590081c80001c01d00a4405001075521104102c3c2c1324090003051485990184040c014246486901e551b013003c4003a1510707090102645038200c484c0c0301d0380980400740e03001072903119071400c00e00e0713400c0f0440307a02d0800b0354154209640001c0041d07001030442c5100d10f8a4516603200c15960b1400b80d03800c581e0101072800009000c00040d8107008007103921074400c0580c040e07080310018140000c0071001c2d083e80d0b118013802400320350388c001145c0040c100f58108407842002c0300b5004901c0441d00001111034641c16140c2070009403660940709241c0100104900520880d000060383c0c800e00514034090003c002c00c000000c101280c41da501c860860340710021100e400e00b0503498061010010785446075400d0140d1a15001444250b49082c0d0340240010810050782050441c07513481010a840014841b60306042c2c81c41000081c0c03035143d0480040705985401e07e040c00901046204001c2822540f040d0401c1401e40756000781c1c0c0140002c54000c62509000621414425 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 755359577 1250 755358327 755358343
    0x1203060108072a1506141201060b0f0c0102040b0703080406050a0c0e1e030109140609012705120a0504140d0515090a0501111c0b0310020903010b0303070b04120504060e010c05 77
    0x4104c081260540d20010030600c901c10201e5180507985801c2d41c0e40c090316040c040d65084e2800b001c10185031801c0e64a4407400fa07840360020b0521950f0038000486c45241005c01440070602951b2401414180ba080c904103c90002d001c2ca4046803410390701241181d0000340402984000702c541c0c400040d6414081c84d0340010307260b45d5507415441c0001400410129000c01f6050481010440c7e1603035483c2c01405080b20581400201e45000780501d0121403d907a900038003006205a080d20b01680054a556995800c9101200d01042003c0750070700101c40141c9400a6800c030840d45030700c4070011522895110003020090f132912600c00d40010b403c06404018440d60154400c00070040c4034644140c0c451680c00240c078410341c08000d101528a180812702554107042c4004026011a108507003c0c00001c0d8000e010a0303130155252111069076550a00140110034017488103002549068034040142001c0d031100340060120500c028044a80c1c424400780c5807000a0a103e1301c200e800b400e18034502108 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 755360827 1250 755359577 755359613
    0x80f07060b0d030f0e130606050a1202040b0904110c16051306180213080f0109110103051e07020a0b0906060411191b080a0e1c111504081203060108072a 67
    0x2400000107523190b000d0700424541e982542c1d403002210040b500542603100c0d03445200c1028400f0b000d03046040c9415070080b40308100c900e014a107485005003400e81800c000201c030420f6442d0700368040100d824000c50704030032080071400c108001814440c280500d0910f030000700c143e407507022a41003150b100100204000c0c1140b10b00b101c0380c044449129a018003080790742114084c1002c1803810b151350007405094001c903050346240e15040b80c904941440c18070014821011031040368444e0000c1303001e650b04640110456005003a0300e01d4400b050006681d00a5103070301000500b00314001300009481c5100105410314500300e1190003c0c104950b056040109000c0c01c4400f0000709100c60603003000030701741c0121099a060000e40001005020300040c0000090500c0314036803140e82d15843c0260180c10380741c281098040c00d0503141c10806103444120303034502241c083c2c00005d10609680117140f10307a004580d484c084a44218405144800d00c10650851745c81250061404041140c800010b401c0e00301 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 755362077 1250 755360827 755360831
    0x100b010507151508010e0106060e010e0d03020c06131502030708070f03020a02060a0e010311030106020a0809130603030819051b03070e19031505040b22080f07060b0d030f0e13 77
    0xd1544c403010b0003480d19202c54941d941c13a102000450b18003400c080020a58161070380558880c0403014810030500c030100031011800303000140803e590301c070740180085590085500c3d1542d8140360141000321068030340c010035507005000c001c00103103641c0b044420803540400318404440d001d103400d07454414040402075000700301040c41c00300c1551101240c174892100340da0178040007045e004400035a10082c000c0c0c40050300302000c02030219040c2c000070088400040e0035444481081c182110440714141c2045000807025800d0288400c1429050510780110b65003c008505041003c3d00c2034880d8401500c0e421700700440020b100a000b01c0340040942c00150000c01281101c11400e0300d140140d0000f1181040c10b880300b9031011090307100b0785110300c1e0301189060591f1250103941e20304058100074080c408509801503000101140b003d041803000c00c00400ea200e00d460b1400034142d901090b0360f60302030155800820003007903100840300e903d215207040114041c803824000c0340500c3e4003906803515081c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 755363327 1250 755362077 755362079
    0x1207050c0d060f051302010e04020c0c0a030308040b0906010f350f070816030f0212100f0f020c0604030503061804050601060e190308090a09051305100b0105071515 72
    0x700c68000c280c0c2c03d0312084040203c0e6481d032490520340d208404010740000d0f05040f00c06a18200703a401010031420100880e104c2c10043c800180d40c807000c84d001100028152b1081c0820441e445000e1900b00750b802010f07003101c1d8104200f485541049208004030301091050103840d02140c654968036a000c0b031200d00c0102d44000c40007070f94a40c29161010070a205400c400521004017207414403c8032844e40c401420700346142c441c0c0300c4200c0d4518059078807010303100440d50054010010141a01211b6001207002c22142221504403046016000c0700180100329075205030340302048180c0d02952508005450f40c4903c000700d0744203000d1880c0d1146281d006820711040c01000a0902d040b9040760307035001b50341c2c00610140101c3c12808482c0c0740c19108280024000690240d0241019440c0644003502c401e50314000c80301901c5041d81c401420741c52200c4003500740300d001c0c4500344102080303403410f000ba46142d10009001d845030342c01c00381244c1d10300342140303109424030b80102c80c00e00c0d81414001001d0f = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 755364577 1250 755363327 755363333
    0x1202040e041a0c0f03060609040605120d03060f08030a082707030b071404030308040302030906041215050c0d05060301021207210c05030610030912050913020c1207050c0d 75
    0x1e07644516020442c010380c009420340c5200d404444690384034030320190560300c61600780f0060340c20404c01c0e554029140d0f10007140e16200c41c030030300d0032100c0c0010051400c118510300140c02c0704d00542101f400c1124920044c008a6030000071a00c81d01d442e4a0010007a58079143c15003034098006071b101c15180881001c1e8488550b000441c1e40507603008804140d055191000207803803005099007102c8031601c05200400129010700540c942c814003d0041c0c920b06580b00c80001c2c900d84c81600041940380c5034085481c14454050381100c0c215680030307010480c0b41002c0344103141a00a4850026000e6212400129940c1782074043c1c4001280309102c419481c140050060005132140c07001c0c050804440409808618403405824560300d12511494076585845040c001c81c4108025014207140d110b07100c44000413a00c041802c00c5080700d81c3c800380c03201018420801c03c0c090808c00313407000c1401444403180503540445c1e00b000c400b200d4905540c1e125850302c0d00b01d0800d0407009031140c0c00f8910400342030138 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 755365827 1250 755364577 755364593
    0x9050d142b08090a020102150c040905040602032719110301090501021902120a0e0d0b0702030a021209031902010c21030b10020c1c0c031b050a0b03071202040e04 71
    0x300d5041d41d1075400d401d5440c038034a0341d82c0f1402d0420180c0140d22041e1101640741c0d038100040d812a1007009181d161517181c0c44c001e01038a1050b03070304a406550001c10401105104581d0021301c09088560280c40b40e200f448003580c8020003100020a090003440c88401c02583d2000383c0140900a0001d0140c0095824018000e4006026608140c1d4030440c00d5000d90388049007031348142e9114103c050600796000c1d0115400010400340d95000700100b0340d200c000c02d00020000d48034045540c0116074804444100a0600407040c01c02100450103001c0401c00e0394011815462900050360121461003050004887c0108001000b500d46180105100604800342060401c000151f49050007100317165401c1c01000c0700144080c0d0700503009010b169404d483c0c042074aa036034001721311921809822070389a141e8035081c1ea60084038400012442900411304100c030000090034100d840c000c400d45441c20720780c0e4601c8002c00e20070401c00b00030302580361441b169066030302400f02c0524204c42494540341c0480 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 755367077 1250 755365827 755365903
    0xc02041a10020f121803010e01050a060605045a1a0d09030306211a0906070c03022b080a050118151a030a050709050d14 53
    0x801168018040076025000090080030290124010308425a841080101940003003408049400303e04982c03e11558090103038030f203090002c80000074541869070000b8200da800fa48a0401e04c44284010007074030324210305442013940c12004040c8010b4080c0900282c603410390042012186041d0188007644060244401800d079004600e80c030b11039100c483c40d030030f0a1180700746c03029620020080307038240091581244440c070380300c2e04011500b80d840e0302d0269540000c19050350403140c000d111160038400b14006130014481c1c280002c001e00e05040d92465201d100080092060004000a80c810141300300000440c41c02c81703100f004c03016060710581000c90100c0e000f128002890f2900819030300009442450304858a1903040d82048000351400000303000481c032011003103c01c1c5600001c520040300fa02c5240c059440301860f0b07503407400115080c00c40310b000d480c3d4000c0004240c024002911090003c4800c0382d00b203803c404641c4400c01c00c40e0b103444020980030b10f4541760203011410002022440d64 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 755368327 1250 755367077 755367079
    0x10311090d1424040609050c0402032a0403020d02010507170307080411040605030c13020408032209050c12060d140c010327032703030915020105060d0204020a0c02041a 74
    0x581d00007100b60300c2c20051401e000001641203d40004030340001e10580c0440c0b2000c1c85001503a0036244110300250403604102c880300201400421013561011003000a0054141c5000b010f9003441c0c2541c000c243c07080c0a840009050010000d82c0c10240003000102c80c1000048402c8107076203240c006001815500b05071800c032510307143c14400c10024989030085006a170005001440c02107d44410810800503151880d00c5841d0300300300204220000303200400c007a801400c01001a10013480100030340c070304140d002d045000d1801f414042d80042601c203c44c21402d074049a10490303240c5000007417643c25030180052442116001c0348002050100b0308403001a02624108880103559001c45010b0040ba6082d02d0201d0348214403000190080c4950100e003000c0c0500c3c1c524180c51030529090015564100f5004541c4040703040214a00102c80181c1801e400e02c0213103c0b03401c11001141804e01600f600038480c4d0b07008501c2c00140c0d4031864000d007210740c00a00901080801c81501c00d480c110340200a = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 755369577 1250 755368327 755368333
    0x19091208060d0203100b12010e070f08060f1609210c170712030314010e19020a082725050a1a0310030210030c11010e0c010311090d14 59
    0x100180b604000e40c0706041c0c0c014001d4408800c4114481005005e04006282d004002c12160780c0211024403c601c403120322440100541c07801c191018618030b2580d44080d280341e01c21400c000228030a00000c0e41c00c0100c0c0c00f0b40041c00c034500b1130282e800500a4108138140350540d08010307451074004a1001c6050301516000e44129145c60102d942c0700140400320390a588412010405100b940c1128500e1364040d03d40040e00070a110746200c4080002c0e070050007850074010501450000e200c154230105144803e08502d015042c1c0c50203000301000410b0702441d000380008050110245505104400f8504da00365000c91106501c1e200d51404032000740d8001100703945010419040401c040300c19160046101140c03500d09520b1f140c006e520040c203c41e184821110004016142c4400f1207540c84500c0c3c501050101030190002c02128030035009001582c10f01101030003021012840c0641104286030101c9c910030071540500a61050b6900c0c0c07604482d041100b882400410110082d0130f0110a082d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 755370827 1250 755369577 755369581
    0x90a140c13031e0b0403090602010e03041208070c0b0c03040303021509071701020c07030f3315050d0c0e01060201020a080a02070201170c0a030b0d08030103030819091208 75
    0x340d01680990800a403264004032018808076039450000c00c0802601e41020241d00c0f22030f5101d406192041e9411004102c1646080c40b17015020b009e407200a000c240001c4d4201450b0203801b0001045582d8041c088040000c0c0305000d004030060303007801a00d1000e0407140c0c2c40020680442d40d07a03000e40b0003540140583e0b0700848682900b00009409441010001e10090b800d080c1c51a440240c0b40010356902c0d98208076030072810600b4008a4001c0d4003074081808500024103000d402d029000f58501d252041201e050403250040c0d04030342c02d018041c0ca000207540e52110010780040040c1e600013560014142c483c410400c00321a2a0000343c44011200480b141d83e00d001c140c0c01c1c2d000b4034004070082400c85d070002c2c00e02c01e03080c4e0103005050700514002d0120490400c11524000c815038000722220030010382070040d00e400d406a81130030740003503034400e00013003403900c520070743c0d0006000060070000600081109101e10521010100044640800c81045245410b00501d2071805c00000402c82d5080 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 755372077 1250 755370827 755370841
    0xf0512011e0213080601080706030605041b030b0402091f090f080c190b0a09081c0c0f1110110d051c050703020409090515060627060405090a14 63
    0x40d8400c0078100c603540224101100781960040d410505456803510324443d40040c0c24401002401d000b090900081d00503242052402070954500c0d030485c5014500b480f210313610300d005034585407880040d14540081d031000b1399800a00a0b108080c1019031100c43c1c56141c050011403003c0702e00051141d9214902c09596400b49603050040c68848c5078000d400c1507a140340741c0e00700304104d8445103400c212038526113034451b40000d1032a0004240e100c00200c0c0108288a010000c1000c070a0700520304045104041c0001ca0050a0f01165203004007105201e0105a08016655400e10150b0700700810781c002004a40c070f03000300300703440140b8610030300d1144101d00e1000c5030040707044a0010000c5204803040004883c8110042d10000d440340d41055400c010000e0701107190711600d9941480360016100f40800c8240c0100b5481029208900c030350810410103d00c05036404510110b2060400d41003440d03034103a40061210301030f07580904e1304030f10389a040040901a90340044036010509181505980341c2c80 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 755373327 1250 755372077 755372081
    0x6051903090506070810090f0b03070b09060904020c1204083003012303100b03061506030117030d02071406090706050f0903010605030a060b03060a09050c04090206070209010f051201 80
    0x41000d00103400040c0455030543c80b45c0442030f400265a500c0c131074555907914400c012100702034603000c0e440341ea54900c0386040c58103200ca0802440704840090403d00c244000801d24070403d410304d845030760300143d030f50180300090090b65070707480101c081240c4940c0c0d20542542c6641c5080202403c2401010541e00582c040003c8501ca8504840e12103045030300f000912003408514800e0100c0c941d181114108590380d08100c034001c14000e00c003011a552060406251800c540908441e0f1422160042c0c00d9480c4c4601041d00e044821082c00c2d8411200b070103409234210b1280d00041a2014000101c210601440ba10b05038407410400c011201c0303d0b6a5070036415140d80ca5402000c002850800499042c911a03a001c0c00080500400001d000e9513a40700182c41c140a15000310382460b21290090001d1070203211b01540300e007800c0400d00c85907420741d40d4507031a074040030b02c214420b91341c3e60700078402d5413a840161001268080c201d135140796161040d00042c0b950501c1480d11030546001481d10050040c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 755374577 1250 755373327 755373341
    0x91214040608012606101a0c0a03030b1203180a090506011d1c0b0702011401060c0f03050906030f090c030a020604210f1202010609060b0712110706051903 68
    0xaa031840e21503400c0c4800700e0a25140020402d4084130041425800907206101320f500400c505006200c06600e8000d040b840100e006c142c04812150602c0409014070002c292400090341c140b600082d4039405c034000402c4103245150002d12803001040080e41d0120400c80490b03040401c0b04d5200c400f03641c9411140a40380f04a522900003410b01464489014001c134601e22a1800244030f002102c01d0780300c0d488a503110000d8143c840c43c5405041c0034400e5028814003100d0b58942080c820b4540c101034000d060300001e414014010000c140084040c03610035802d5a401050050000d81c0d2820b00ca140d00041c2082a124042c4500030f0100d0055107207000203d24004581c0500366900341442d00c00b010400c002041410f1212404069051000818001080091070303c15450351440060f046002070031505980c21501803903182500a024455402c01502c14542c0c2c030020ad000e000c40800812103801c01c80403585030951180000116415400001409610394501780c0c4502229541380d04400b92000c07 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 755375827 1250 755374577 755374589
    0x16060302090102011d3f090a050405010506030f04060f0204081e0d1b0804030609050a0c0e13140127060b0f0a0302240a260f070e0d0609121404 63
    0x45c651052801081381c030482e0034a5055518028407a00c01c81d501040040c455003601180f260003d140d514a1422300b400034003a01c41982c08009941c1450045986848060300042c803101d2903100250800c90325070051482c20001c21800c0d92150394401034907644884090320000107035803d2001903c0d1000000d0801c0e0030190603078a416000007020400003140216850603903186404200100c046500c50140204452241008001b490190705065503000200e4100200b0385480806011080f40c0000390648456000030191042c002c03d400303024010500a16440080a909110440d003a11107204400489009230007e02643e0114010480754008a00f10f1f5a0700110409090005d030514848041c1101820141520340800620404403240c11080c01c6038006008020301441a108010b1000881012440e540885080201c1d01061075207008121104002e0b4092032214155185280d0001d62a0007102c200061051814450400c0d4040c01604000c2282ca4000d4201020800c04035000c07541 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 755377077 1250 755375827 755375833
    0x14070905060c0c03240a060503060627010605190306030f1e0f0807110316060e0a0306050c04140a060e1c061a1207061403070216060302090102011d 65
    0x4141000c00c003442d080003501152610a10800088a484c01c01018a83d40c01e1100001c013102c482403140c0c510b8a6000f032080610a003130020422070303030301d000a0720303500503a04a801c40e80400c0c40704110785410002910298616802d280001501c942040041146035501c0701a00b1030416041c0d02a016a903503440020404503070b00c6255800710b180000384a0030b0041034200000d60075001d446180988034541406d903400c42c80007500c40c0c200110003d8401d030301c040650141002010104000712800141d100700f5040c029101840c98403a95080e814030007441d480503040180d400c00100c1c60780d203504980075600d071148090b00a82d6a038500202c040e422103003955144481c8984007400e02c60301d2041c90f954010250182e00c403c500056050042c64030b14403c02d0301d25401f0000202c20400b407000180705c1014913400c58842400300b00c4d40203000d5803030190507180e080e03a2902c482104a1800440c01007034480c00310705100103c0c1003640340e0018035808800340e009003c50300f00c0d07050b1040400d240c0b0151809070380c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 755378327 1250 755377077 755377079
    0x180a03030f0c0e24040803030103050f010c1b060c0e10031407080405060411042904060b09130b0f030715090b1911010e06090312090303040c06050d0f060e010504140709 74
    0xe00713a000032038500900c0b9619038103255503038144614540080c0c10444003034000044400345440c09104108034081240741440518581d00c111405410956802400c0341c4c0d1509588450a80280c06c565090840589070808031140048020f0003072030740d031541c00e141c84d51503000308104921480c0d4090140303401802411442c0c50b00c0d501d40c103007a4180c140300c2d078016442e80024407000e551a5484100c2c40841c80b0391a0355686003408000444100760047c80340481c05000441c880d8a50726948020000450390005090344414006244520710000440d82362003503020103d8050810103070070012900644411540a0b1143c05d88a001e0003034210140c1c000c00c003071f40b84403501c5102d0414260110240000041c00c0400381f402c140c10920122100c3d0050351000940d204003000055056a2200c1c055015505500b00b96444000c8242c0d030380b02d041c00300500407411110b42c2d84c840d40b024404111104040181d140d807101d01c4500c01c0c100340b14203485940341200e010740c41c682009900f80b04500e15a80e5034015 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 755379577 1250 755378327 755378359
    0xe060f011b0804060c03030e06280f020711100f02370c05150405130506011b15050c090307051c051501030606050a06020a020405180a03030f0c0e 64
    0x41103085401c1401022240804100441c0040014000c16030ba40d03042c3c07114605015040c1c03a0b0f41c404040613944600100400b019000c0170865120075604049900141503008071405482c2031041003140c1803002a0729410060103d4681c0c040400a4a50803821102c1507025103e0358100c0b03164001582081c40104a250400d0000f080c01c0031014007581c00090742d40e11034114828000d030044a5045e0902c0d4107000629000c00e1580310968907209041ca01403c2c80301140c031203c040500c10031f01d1781d04c42c80410940d0703010702e01c1b05502980031702940c2180c041c5402e00130085c02000da4454441c03450f100200b10142c60484c00c480140502a00424a05140c00300f48850043c445140c042101ca054000500040c400c1c04554010f15980c0c1d6421901c0d41941840804c0318031a5000f07602c1501040000c220040e004038840e030000d03404480c001856038a83c113100043c2c2d01000d145803194000d90303400004042e09640200441c043d1028208801e130b00155023504c0c000040e050850780440c1c003102c0a900e07 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 755380827 1250 755379577 755379587
    0x5030a0f0f091104061505070b07091e030b060603040218042120070e1909171327020f040302030609101103060a03020f01090506220e060f01 62
    0x8619149040020501c4032400440d08580407014112060b02c1d0360603c0203160300c3d19010700d0000e0312005075400b1140c00d881030050110322803800c0c014002240e1100051443d8010000c010003070a07104c0304039101071542044955031050b0740c0400c5910b1707580c64010031103904110054911907503015224822810150700303820305c14800103104a0304c640064006031400c0c0c40d41f0307540c2e9000031042e485610208900e0302c82e0081c090402055151142e000c400100701c2c03060b100303504ea60030a03c054541682080f180c5048809051405005000c10b105801040d0407206402c00800e91011300c205804283c0703484611082d030302040d000c104983c80712011494203203661154010200c100c6482109480d2a40d41c0c2c2c0401e06210f0125201e4111703400c42142c2141180340c40c002c0406034081c00300018070354a0058006001c1c5c0281d03000c081c3c0600c14200c101e80e03250f40120281d00103420010002070320f51a0f4806003c4072241344800c04e0315003003020742c2c0c0020301c0050801024080c0100a0054100e98003040044030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 755382077 1250 755380827 755380841
    0x10308180f040e01020c010e0102390106060519090501020615010905030d030b090f22020103020d0501180b01140d05100e15120604030c0210030f1514030d05030a 71
    0xd4821000d1841076680d54483c820452220344107400581c03120840e44241c0e08541c56407003041d00c0703a40104030044101c10f03014094803580c10590003480c0349041d0b004a82c0784a03644288110515071a0040220704241c000c400380802d850030039600c0240214142080b250065248252400750784181c0200701c55170840103240760003201c18500000c01c0c6680d00c00082c5090001c545140102e9a1200030b109103043c50b080555000c0c405103084002400d0100803e03034900c1a074041c00c8880b41c8400d40d080110381c03080d0106c82c40c410000b0030500c8196180e05440d60f10b0040309209041d440c0c58211804265400b507a01800d00c3ca580c035040f00e00308915144100b0217448020320350b649000303c840000c030700000d485035a507010b200b0389828066041042000c0c8903105015141300301007035010b6020440000c0d40b100110040c141e054403039800c0c0004411f401d030040c040e240c1050400381d00b0140b0303030240d00c1d41e01c0d0f1120003121800e0f140180359042000074140c5441030803c203100012010070024820800c00d4211310 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 755383327 1250 755382077 755382079
    0x3020a05102012040b0c070f080a1509060c110f010e0309060315030304080307060605330409181703060913050703290a05061c020d171b0601030818 65
    0x203036030b503030808803109810b5226070800ca070030b0b14000c10046c1c00780504101d04400760590500134030000341010306499480607001c0009000544070b0300105460161900300c61982e590000003030011480b0004080c25010b6243c902c040c0520811948820580c014050040d461001402441c40c0110010610003070b80c1c80102402c2016868411002c1c2940701040200b001380020800307191980c1e01072910400f40c0c1c005a0009200e80340b070300841e4014a0f001c41800021540120108812440c03140c02010b1500480d8000c001081c58001064150348020088800481c403403050f141900b40304006c0e0907803a000c103403800340c0c1040d201e100140d0f01e16100728000d49020701440032104010703501c0d0b4500c100c01100302d074014040160040084440035144100340d421601d504010300444c83c0c13420200384008080540004150030381031038901552100000c0d8036200750490401c510610383c01514554a600100901d24052090a0000384000300400c810381640d80c880e58980c9840d06030034100c901d50001080c03013 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 755384577 1250 755383327 755383333
    0xc13050d301806210b190305010b0d03020715020a0b0a0207030f09060e0621070e0915150a020f01241d061012050a0603020a051020 58
    0x40c507207071039165908488100c144041c801d100000700030080002c9a118041054400391080c00d000580c0c000c40507961449160004001001c4544210405401c54860581c1c000800007030740c005039a00000d108098a0240b0000e02480c141d00040c0008a510a000640107030010fa4003404100b00c0c84c43c82c1100301120f84101c0d06040c44079128038012001c280c0e14800e00d268002994020590000f1306800c0f000030350308100000300d00d04000070300402006c100561180200040301d140c000219002454091400315404100b851320000242c0501c0014900c01c0c40391403000001184034445100c078112141c0c01500c0100b034602e524082d01c401c1d0300f2600c0503405500603403c000040d002d0034801c0101081801c00209009c0f5003c001030544441d154010241080307800b041341c5c540090000903150070600a503180071006201903c2111605403035005151514208403c1c0112040c2582000d42540d000b1582802d200c0e550f03034100541046803840003c080340c0001e54454038aa1008459100b084141040d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 755385827 1250 755384577 755384603
    0x280b0a030501050a4d0a17070512010e0705160804030c0503121e090904050d08090c011b030302090a030c050324060103051506120912070507141305010b030702060c13050d 75
    0x548626a0044014800011140304c01f078a01204203441c07954010555090140c41d040c0c801e10801c4440d030050041c08400c40604000c0f0307030b049200d181100e4806001c80032040b038501951502d8a1580c1c8684015108211021004a590b00d00810b49441c08000f641080f8a08007101035150100701e0421601d144014040c4003c8100d82c840013102407189200f44040c10400e00400005062124090030010240e482199901e00990f00400f20b600d501d081114101007440d40344c54114042c0c800c842545411604041d00081041604a1040306880b011026a00d0765400216041011403420003078100f0084c802d004244e16501990040340c0080000185403004a804000b049444d44030350140390740481c840003000f5501da000c1c000c004802819000315031405403142c5445645c0c2c1d031980609030a01421203202c410903610200e202038101071b03c041c144125070355180c48901c01d40044503514054021040000c070100d07042011214200b01d07000c1648003003400c0401340014050195001c48014800401e = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 755387077 1250 755385827 755385971
    0x120d110d05090f25030803040203101e060e0709030816020301020301061215050a1806180209040f051009090302030c06040b0108070e280b0a030501050a 67
    0x58a84a0402e02008200301082100ca0500d800e14044e03140f800480c0341154011803110040c0c80d20f084a400550786a205d840d6800000c1c208000300958009140c40d00e0340320120840d84055045009104a87c100102c1d0b90312806410550001c844e0303680010000881440004c6902c0c015100c0c281403000308041c1e140e019804079003268020781141011071040d2420140c8107007503025101c5c0581c11a101508901d14040c0442e8140010340624181c840c2c219801103010341d1290302c040300501f40e8140d40c50700f0240407140180250700c4600b4003030095050410b10141c003121401028001c8048172110281c6a02d000e4042d4001d209405003102180410008014108810400c0a0040d802862200c5043d45400c2c216883c00c2e4260740306000384448407041000300b400f01d030303842400c02070380751180310841031046002d2004001c0344110580c000c01d8920040148801580494402d8003c401e040000c00d2100c0203140001c40041c440840441035031030f08000f1031100c41840034030a6003c54841400301c148038 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 755388327 1250 755387077 755387081
    0x4031101140c01090804051921020616030e01111914070b040b0904050f13020405100e1003110d11060723010218100804030807091d18120d110d 63
    0x1280c185e95621000c241030107103241c00c0a0540190306280c400c2108240380c41c907604040b80c000c01c1c0c2c01c01400501601d1005549947c021034062410ac50010480a01c1c24600907108540c0c140f1924002290003006031002140010400544207190090510512865851200c20141e40b045148c15018a160000d24004102c010703001030941070700040d80b508607400074001119002030055494010700d1090100d54581c8400d030001b0960113440110f12559050756070030301107210f50b110034524010002007110404030100b424059078400c1003580039424098080200a00300000e016010b1400101988010300d003040003002500e11542a14061525401455003004041051300e030181e500007a000c04100c851170f44510380e02c0c0040f40d02070030420012100070400c6800500c0107092200203004907081d140031340d00c20780042850100c5220f0700d20b0701100117421000b0588d8600d89800f6054244410b040c0c0c003050465001c803032200700b10700780305d22640300c034000d070901000b81490040d08001d000c940344518 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 755389577 1250 755388327 755388341
    0x5040b1b0c161706160311090a08060f0a0c05161106130e1014060901030603021203120c0f1c0209031005060f090c0313021503070305010611010204031101140c01 71
    0x60b54101d070905180030b50b09111050080b00c2c192058118000708040c1c034400682c100a41d1246280014007a6031421210706180b041b40483c0d68000c001c4480001c10190000c1d0303040c428175211244411545410680c40180c03140901c040001c43c1081c000010317402d81c1000342d4440300d40500015581030b0036000c0821030607400203800c01080c810b020401c0c0000d600c0d100c4a1a00580b4040402d80564605020001070410078514184a04c6001031403031200e0f0310907040f00c00616002000c0090b182138100166039291300c4448020900aa16000580018010720035542d00400d82941c69244c00c404582c910752031011146880c00c129424051000e2a840070000b00300703400107001d8005030a04026003004100000c05030f0192240650104001c4603005000a9070342081c0035599130440b02070144001100141c0204805003002800b10402211a505400c0103040b2110754aa580e1b1080102c003c45083c0c1c4205c3c0405081041c0d02010080c0c0c80d4400c540c40d0b0040c42c02e50040a00f400c140d80c00c1c0ba03080d1001 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 755390827 1250 755389577 755389603
    0x60303051207110703060207030e0414090c090c09060307020708060c031905040507063c030b06180f0f060c0106150f1e0c050a0c06021005040b1b0c 65
    0x1000c03800c01110040e40c00c01c80d800c50920700f02540182c02c42d011040e901d200782d0000400594020460004150003140014403490000f042840042c414500c00c51a8040c02c03103190025204140700c0e403150f07007400a11980034201c03040b5a50305d460703814401d00c0b4550b88040c0c5990118468840009420f078001e1000b1401440c11030740b026030740d00b407864030400c02100c66010400d10f98504024080002c40c0003504c402203422034242107104050090003013040c40003800c1120104011070000301e80001c1c02c10381a2940340d0168404202c074090001c148032160107041c1613114100070419044400745400780c1c21002c607410040602d05030003020300115203540c0003008403482e203a4646000388a0740000312061312058a943c541a00380c0031042d40c0c0100201424141e900075801448014141a07105a062121060b040011200ca041a92030800002d009034418a4014010703540304200e102c0d12030107840d000c0c076000024044141c5030a0f010341d1128584030340c0011646010010f1031200c050034481c00503003480c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 755392077 1250 755390827 755390837
    0x150103290438011e0c02010f030209060703020a060608031e07050307080a020a060515060a030506030c0a060f090b0f25060e0714030a051e0a06020412031b020102030f0d02040306060303 81
    0x1403c8800502440010116a011044c40142d84a0540d03001283c0901e40803102500b2558184e0003445100034840d00004000f40c500c090540005a10700858852a0104000355031448043c2c1c803401000503001e0700c0032240350142e007d2243c0c80040e0a045014200b80d919014a0396616801544500d00942c09600300390460f4085c02481d201c1c007030344060028440a0480c42820008015100352142c05040c165130300c003c61505e0714100103c144034034015002d21f2113240c495074040d1115041034084000a00d108002040c4401580c058030034141e080e03083c0320b0502000d1320048019070091595403460b440034480d04c0000c14901e00070302402d242e456024040032400d01504499900c0c0c0c5441c0345000750300c05e0030740b5000640d00203200c0c5d10450141400c0242ba1701c3c4161843d0410a034030b10701030301883c00450041280402107004061052098032489070f284181051108140d61007a40a03025030024030070001880c1148006240e004150000149440e071079035100021110740b900241d000607 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 755393327 1250 755392077 755392181
    0xb0c0327040506090702030910030b0303041d13031b06022b1109031903090e1e0105180c090a030804090b18090703080904141501032904 60
    0x104041c428603403c02c00070703070300e00420340f51400000e1750300d103d84042c89001d10301a0011410251090b03006252031035006041c0d030343d944c0e9590f442d00a4102840b010a900a0014020035200d00300c4030342110407258181c0350b081c4020022611011141c4014400707840042d0208802d108103003010302c3d0a12200c0b02160070100c0003c0201802084071000784559144010800280410f5940018044043c0c00e940f4861009044249811145503102e0360000324500401014025074007000110801001001c00041307200760380c0c1d103042040303050058154140b99209070020461a070941c0008050020b00540110003c5a8a0b41c0d56016648154020b00b4100d0740c070451060305242402d03190a0220400c0c212441c0d900b407003011a80c84164500c8003c201c08000103d607140b60f101c0c0c0e0060b000b00022001c01042514200e0402a250200d01700300030700203854102c40079840401660140c00403a030184d1140034a80c80c980c24070008000781501032030f030282070450005580c00c42221130558140c1d0b100d503402c0c02ca = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 755394577 1250 755393327 755393329
    0x25020a030f0315031401140a020a08161205101e03050601090608150a090807061d060907060c021503070c11100c06090c080d0203040f08070b040b0c0327 67
    0x1c01c0c0d654074600109800c000303d101d40c29011140140036a5000020003c1c007203002450207004144034140c82c003040e440b40040100b0751400c0c1d8042d14502c42a500c90a0300e940c0c40c0310785660312030b140504100228002008036482944c0550000f82c0c0100e4501188840d980c58410001300301713000429824454108600074030821400b440070b98010b1108200c24405c060400031810746a0545d404400030940c0440001040090140c100c00d4205420a80c00e0750707a200107003002e1001e024607200c2101240340680382c4043c103d40c0094464400d00d5544050000c440c00c15000b1500040e5505040e40e00240784007032004040b4090000b18010720107610780e200304444030324281d540c018107140001d1080d10902c3c0316808071070304208603043c2181d10110000f61841c9a18010348841d003a03030011000e0303210b1002066281c1d50000000c105443d000f40e443c05040d6660500341c2d0361281240a1400151000d01040007105041409480401944400c1c1d90401501c030b007106054010841c0c1d00301d41034803070035881c82c01 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 755395683 1106 755394577 755394587
    0x304050a1410020d0203221203090c09110909011d0601210c03020408010b040219050c1c0201060501030e031e03180601150e011107030b25020a03 64
    0x104d04054168200a400840f01c034800100700d503c4421541070b81411101d5815071115403a29540011441140581074003c0c0c1222456440c0390045821511400340401c40c5c4031240704641c403900341c917080164641040c0d10048541a1404101201e51006500b02d580103200b800e0180941e0700075140d020003c49000f02400005180103100484a64990018000c554098000b801444114001c1108a10401e101000a0440c00205034100c90090003d0195000b200c0b0540717013203000d400d06001025103210580c000607590b50f00148029a0140f044410303ca84d644000c500b400d001c102c803014000b40c00e007100d400c08203000c40000c0d200c0e0111480d80e01c05d40d0719842a91034a5a6a00b00102491544620a008101c4102400300f89501c2807203980202400000200750241c42c6482d4010180320240ca09824148860000c0045000001b040f02034075805034014074540b0180d01340180 = true := by decide +kernel

theorem cover : BRFrame.Cov 755215827 755395683 := by
  have h0 := BRFrame.cov_init 755215827
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755215827 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 755215827 ≤ n) (h2 : n < 755395683) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
