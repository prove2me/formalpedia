-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3783
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:39:24.371555+00:00
-- url     : https://prove2.me/submissions/6d74fc04-9d8b-495a-bd9d-5d6b79d3d96f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 680215827 ≤ n < 680395683 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 680217077 1250 680215827 680215829
    0x5182112030402060415020703060e0c1809030a1d040501090c110d08060d020103020d0c0201051602030a2f12040906121a0c0715021207020109020d14030d1107030306 73
    0x1028000401c244401070304c464007150100c0348180d5150b1034803020490104e0600c3c0d981d51018007800c1c00c1c8400781b22403081c0420f4005441008580d8071722002058020b0020904c001c0399003009a80040c800130294500464000350300e40c90401909400c003d80000040071500f007038000c480c1c0181e172880101d989a0300080d4800400034120002c00080340c4441c00142920700081c0344c83e000da0b0f14805903104690082c0c050b5480c04003060010700c0710303c45080d4024001d260445240321100c2d18079071000c0d805030001c0100c030040402660303001c00c1070f00d84c2c00441c012000007a0030303196218584640c4090440050040428100021014541da1480c200c00d00d802c0d2550f82d040f8a041403a10140b40001800c441816181d00c4048040003465a07129020880030b8010f600000e000320704691099405944590300401c46c088400d05180c04540f50003034120708032001920025045029809100c0c0842c10415040010070310b150101d0b45428244840031042d00e00011250a0000020610304101909401220 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 680218327 1250 680217077 680217103
    0x201120f0b091e1812040308090f09010b070b06010e0d050c030c121c091e051503061c060204120b01090e011b05090604090908091905010f051821 64
    0x100c0003420703d41400701c40400502910207130304d1803180520b0001810700c5004080c07088280e05030703155039507130400265952000808901c1821914801042c070302c0d012417502d05a642c428035180c01c002c1c1e103a8654405200c050441d505210f52072000d00016540c1100100c0102d218074094010103144405145c0781c42100c0c0e0b141c6104403d622070b07206801c10006800402d08151014205914800b104140c448103075540105070a45200b40c58100160807920500b002c541c000d44d46409008801d107400342c2c00340400e6522aa1281c0b90b1102c132542c60005208082c0b100c5e0082c0801841c06550b1031912a0400740c41c801220500490f20042005070001d108908060451100078000c6503200c890007820ba81848000034280b0202058240740c5813110800c2c0c4000d4800340c4420858801142841070b0290450340006214025030031307050315504020285042124410303107c002c000204204181e496030452800e9402c911441c40c0e214440d42e035803440c402000e0540381c05e044840f420b0001c07404e040400100c403a07 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 680219577 1250 680218327 680218351
    0x30503090a06051c0b0a0306050f09060a02040f0e041110170603060105100819020f07150b0102030412060905100b010f140901030207051504030e0307060216120201120f0b09 76
    0x4c0c601d280c2c4d20030383c0c20028481c2c419000400d901d4040008102e03d403590400391040e49010304002e4001004894240942c1d03001c0c1c1200d03101d907070f0382c600101070b03100354094a6804403c06030100903980e881407907a07400611409540c3c2501d41c800c00400d401398103421f0b24000203400c41e01500085110500c40d19000a003c2c1c1c0586511341c100300105010180e902091750411000030001480c1490000f40c0c0d2840d039802c0340040d5910116007280003010b0300b0150701070300c000d6000342c44855012418030072800c2e0f1043c10380207542014940034021443c103043e03d400fa6010398840000a0014500780200812514100c2d800580050b810000600052007450440148150407403072060104454003996204003091902503903cae20189400d82c1042d0b201006161195084c10a0100701074111101d820000f80680460301754130303900d00c0200d907211582502d1195031091410240403464001000480321070041c182803800000c510b02010403904c0d440e110b04c2000c2d6a42c940310300d452410100080d0400c241c6a01 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 680220827 1250 680219577 680219587
    0x1c0605160e0a06050f13090618090b0a1d010203090706090b040311090703060509070818150604020f120a0203090705010903080901111608030309073c090204030503090a0605 76
    0x1042080002d4040d54081c020003181d040d1105000c0001c0340c107460354810000ca841907030717544500041d0400340500c0d07003214800b10401c01e0b00c18040c480d107001e0580021500085495200c074131030042c05034a524019506413460381012541c400d000171405129120000e0955034030386840242203c8841d0407050744a07204220800104000d044e0300022508111140e24840d1240d40d400d0707005216071303070010303030032a00c0c40040000d95500a10308034441c0c1c06040724100ca200111030354548410141d1001c41c4070b41c4a11000c20124100395000c2c7c01101c142e281110315004c01c11820a02403081121007a201a400004120082c1e40900c9800014403003807c22410143c1150784071495805446447e904202e80d891418620f24010018844001c00b21140c141650351034410485d10b0340c0c0221281c11491103000c0000805403054904100300400341951840000b85c040c0e42d0300d000c1480c0303540b03400d40c1c90f604400114003c0e82c3c5200500043d84618015a56640882d0a2041c0c0c140340f43d00c44000c0c0034042c40 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 680222077 1250 680220827 680220829
    0x3020303040b25030c0b0919170d05090a05100b0d02090421031409060403090b030408040509240307030c181d030903070803040515091c0605160e 64
    0x3a607042d148401d00c00ca4803510514101401443d1000580409043c5401010113254000300800f425501803400c1a0007079403803d00309a51103031100003401e544120094400d02140003401c004080a0100c2059480c080400c14103c0a449040d20340d802142c01c03500b40d01c5d0400808000c244581204000c062100781c155800055442c0008000a0300615080001804221461089050040000464503031801507001e0007801444d101c12040a65000a008240c00c8480080d20368441c1c0d91542e115541a410f004007094581c1000c6c10442e542c400074800403442d641d40113401440741480c489546462202c3d00301c1e201d4501c041c66070b041e010740c222442c2840802c5151003400b098840e4401d4045a5100e82d401840c0100b81075000d0340c00150112440844030f04010008241c100f100310102d070300711929000b000341c0b24499031003001d610650b0800f0a1113404a14005400c840000428802031010440c0008a150342c9a04080303c900c5e540c0d40804c000703503004444000029040780b0700440b030403080e44 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 680223327 1250 680222077 680222083
    0xa1e0c03020c0103020c150f0a110f040302010f17091c030b1f0905040203131109010e16171306050c0a02030403060e0c1207060807030e0616180b0c010e07030203 71
    0x34001c43c1059000a600c0035003020420038040e00a403c40c216506500d018101551a80000d41e441f40300d42c0d041c130266a0707864080c481658912410714030250b00d0a443c5a0040d01c0700c1144809107410f000090001d07414140d10f040072240b00c2d04042e0080c283c0e40c0301c941c0041342c6095080400d4010306140500b201c000380c5a144025268030550000d07201920014903068410380b2041d071003564000e0000082112004e01c0d80c031001c807014803550a100b40d0f0b1008034104520301c4030900030500317a0f90000000444e031071013146c0c035000b0301034141c00c000000c1c00280002901d01d032000ca030040e8062051512403c100421407068030303401600855a14281f1301c00c654000e48170302c01c0d4400503011940310f04024441d03c10a01c40440400001464114841400080603440e00c1180c4510408603440c1000600c0e11030003401b4010046242e04003400c8a80d80c2c0c2c054400d42101d03ea19510b0401084c03158486800008610708405421000220754071030849031802825100da8418210091304440300c2080107032000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 680224577 1250 680223327 680223343
    0xd061205070816140f040e03181206041509060209060d0902100306120204050c090a180c170c1c0216021c1a0a0f0603032c03070b0f0702060a1e0c0302 66
    0x1110041722150a80c5d00017009030404002d50b40880c000056074003000e2070302e40500c140807601641e02c20100001207160586480040301c02400d0701640c030034074820100040d880003149503c038450050400102e1004208a600036210840c00544d64120240552404104220f2008590f1900340413150400e11100c41c0942000c2c0c0090003641c13210007054031032110b0f0060300c8000c0f030060040b000755903490209100c01c1004c080c1c1c400b002850550303458030036841100742d0200e00c070011482e0f5a40e910740021070191907001081101a060500d64580b1100030140000c1c9000000d11903080d80382400c5004000a03207101e4066075080101846040d40000c3c1600700f03034201c511014400c0b4100d42c2d12080200081c3c801c2515011060b880c02c070b404001c054100301c406460b800032201104948a0000c502d900f6001c103001601d601d503108260401c04d03640504001c0600c041c13076400907810000380b0f6001c9055074000309200f030080b607040640903072030b00800da0f0113292a0719507291550315103019803000703074070b074040 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 680225827 1250 680224577 680224579
    0x20102070620011127010f0c0212010609020301150903020306070e150f07030e03011a0418020a0b0a140a0c0b1503060405070e130302120d06120507081614 68
    0x2204038030a540d42d00310b900c110908460200240a43c03d1a039101d00d10aa20400c455034085641d070030000b041c00b5900342c1400b2040b406840c0c40d000082031a0099642c80b100354400ca03071145509400a1075200280681d90040c4078410300941c0b254184030f1280141148819902d0800840240410240e6800103107142c0081e441c0c00d00e0402204c0100205a0030740c001d070150070708820005411400460200700501c0403500a135100603590b0741035801c05080e1007507030b4140051a242400c403402d90349410f500890904400a102608110403076012a01d084000c1c0d1090121660120754030344856000000e8080c0031a0840000d4238024815002900051108130017608090500001070825143d6400403080e00e1402011074101d441c0618010356550341c503000310200940f0b0303c00440c54aa2088440701c200903410340151485c180180040c41040d00519000306005442e440000b40c0d00c02000900e0f1a07190151300900780341c50500d9021494a5924074140080e118094010008030111a21060100c40 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 680227077 1250 680225827 680225837
    0x110a35010b18060c0604030207150f031e09081c0204050904080c0a081902010c0f09030b0c0d090b0108010b1903080901020f07090c020c040c08070c0503071a060414040201020706 78
    0x50306440642c2210140144a0b0b0482ca0020740d000d00e5202c001580d9200f40c2c4a5800c85140580f10003000c0c043c07905000046011030500c3d4000d94059010b900400c0c88510104400e1040c80340312090070342036070342c1031f5030a803040e000000d403042072900c0e5012404a1152290360039490f0610f0440450042c10000307201600300c00c804a1100b00c2c80728144509180143c002d41016160503a8010204590031100d21000156280010540b00a0701910b840c1130510740c00c1e11141c0d98203107907440c2e003060345900600348584c9441c10013020880c15010b120740c40010b8010241d5070316641c1404002809c50f500c1100c030300e1192112110148c10244440503003000d90354041c082984402c1c0c00001030b490303e08500a6050103000d42c1d13901040c0c8a00340e50160a40c0005a42190700c1ea9036031805010407030340244001400240001e001a8415004c5c46d04095814821000c480c038006c0c05445041c44555640b503030440613000700040c08554600b40c01151141d1481500c100640c4c281076001035600d58140c443c1d0700030302c2 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 680228327 1250 680227077 680227087
    0x50907050a030305071a0709090c02010902031b030703051207141b01030e0109060501030b090c01030e03040611030d0e0106050a15090608060103060503060f04021f0206040b040204110a35010b 84
    0xc0408886a071b1101086c45010b5aa4100010040c0158044e40039045409260103007405000e48140100700b201d5030041d01030802e0b81800c0060414808520030040d03058850301c40300000050080100202119104a1082d2a200c1518015801c10413900000e21142d00c0070740e0001d2407105250000384101004d00b00000c10034005000345024090491020304907a1500c0000001d200345129105e20520900d4251b454403d00c003030040d4122009060047c10980c01488184081409942c8a03460790180f44102e90901080f08036190680e19080c180b00000e9450b40c0c010001070a003240400090071401301d500355110031040008190544512030781c0304002c03c01300880c80c283d0283d408440640700240036a5024508000c9a505190f07040c3e800700d018290842e40a1519502c03032404242c10890355003c1d04580e1215122005180d002500c00c1c0d912580e01c0040101c0200607030000c040280075602ea090381d02400305400525a16101615490000411180c034406460401c0c50343c15a11401000c9440e1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 680229577 1250 680228327 680228333
    0x50133090806070e1f0c080306040207050613020f0d082215021605091303030504050c040914070824090f0d050d0f02160209041a070909050907050a03030507 69
    0x10140e1944041c4860242409018886601102d410344154050380c0104207080c10b01103148002e80c080541c200000e41c440c4c10000000c02c03900055401410080015043c030070651a60303070429809940d8240200f2205440000310300300b0125581044004959545683c030144e280c5504034820241c00b64024404000f4000001071040034120103041001000448160cc4040103542c4141895070130130902c1000600081500d8004512440390540422012240f04940d030b0943c050040680101c882c0c1c0144410f1815540f22840b50070113090217030107230310440865180c1d141d0409840d50019083c60300101d01c48101c0041c3c8448000c50890450500710a03030f40d6000da590300700f080058125905003d56410f42030750f40c1e4004068030405001c0642000f41d8442c04031028128407901210303264800030307403100340054501402001c2d48580500c2c0307000700808000644c2c404810f000c450080100e20703c01e0742031103600e006104056010207408000c0030380e2414000042d2401c03410788402020054000f501c1d40070 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 680230827 1250 680229577 680229587
    0x9030309080c01060f0906150809030d050f0412083d080114070c0b01061b02130c0f0305010807030b0c0c0d09060e0405060a0308090f0303030118050133 67
    0x14250041c12140c0c664000040e030780e01070000740c4218a4a00104000860604424030031071013140c42151360031403400c00800c016544010014600c40781070105000040822045008491196075001600c441900d000e1134035100d0405001e1042007008103107001c0040483d0540644100c02c0303c81192120f00c000d5104107040305c40644040190f092101880002c0e044405411800c0403410b141c403420030560b114101107a00700351600d00600740916440040001c81e000f842d02c0d125030021a81e442061410030780120f6810112001e05041491b541d14065050a42c4146c0c20306e24042c170b43c6014051545440f8000b030b079403001404040c14804c0c2d401e010070155200a07003100c0002080703100b86c803000e296880000e05094203600c9940c010400d281da4a48640c9030901c603035031250364010100400c00741075469076001c680211403841d41041001e0502035099608201560003082800c2c00044e90342440d501c41d9080d9041a841400d903035030080b0b403014105040c4540c50844506a440714040b80240c8082261 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 680232077 1250 680230827 680230841
    0xd0c170c092404050117040f2d0b0103020a1a0319020c0601080a021f050d0c0315080615040c020d0e0604030221060f0702070302010507050a0512030412080c030a090303 74
    0x8140560001c4104401e440d01c00600300311071098030781040210003286c60f5120780320308440c024841c4580180144c0010741c0e8201c40c0b01c40e80900300d403101d40e4403520341c80301d2903c2c03440380d0090790503458141c010800c5103071a904c040041c10000c0101500d42d01c0340c1c4005000340c0006081d0700c07040c01d45d0b00404030800349103034155854000304200710f651030350390b514180c1d860700c1e0031200076805640141c8920618000702c0d90021052415070383c0c0d01d464400c050303144100900d034004001040541303912091510821302005100034110301000750a40b030516990400e0000c1400084900450030301701911300b029008518642d00049500304607981100040010706d440c45560402544442c000800034900902d008103045140c920ba0206c844030345541010030200c907001c6a0800040c0c2c000e403400d00044d4800c501a002e91403013102202c9110b4010307510360303040c500403100700c21412001104200074032940400c040f140c403000b414104454103081202c82d00c41d00c0010040780760230383c4864400003014802da00c01c031 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 680233327 1250 680232077 680232109
    0xb040e04050c04090c080607050f0a030504020f0a140301230126010906020a0216050f190e0114010f0c020a032909010510080105010509010905180d02030d0c170c09 72
    0x240c0c2413070315000b03150010901a52000f40304100c0012a62400750307003128a01c00103000d5031414085412002c130081c020051080341c106408000155450b2280040c1001900341282030b05c00300300742c14040c5821904900207019403542115410011107c0b0300340c1060669010170300010b1a520031100b2100d6019141c0c000062030b40c0b8000d001d000340b0600358094802110f080e030a035840d8041000c0394241c580d44074002c20b80d014000e090035440b04d182019080c0c444152410003002e003695240c000244000d02640b204600d5074003a0450a41903134000e04031100480103042a400340c00890300491041e94113400000d18084004441c09090b07046035004103110b107aa1010f129440c130f40040c3d0640070f84001d40c1d0341c18040001c840041284c40040c05a03a06035040604403103c181e20f0000c212018003405850894484101403a4840400050081940741420364004603540d075900d4007003030112075403580c5c0c1808226040401d4258610608405500002040200b80e110450240010341d0003000520003 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 680234577 1250 680233327 680233331
    0x50a0207080a050d080c0c100216020612150108010305060a020a14130e0109141506040305070824010501020c043b06090a120813080304081c02040b040e04050c04 71
    0x8040120019098108100c0c81e5903010080d117131881c25a20502075481880802c0d0030100308c0038140d00866000c4d0140c111403800009802201c0d402040180d8000c80807000d212400604204043c50000d00002141400303180102c13030f079803554407450b490321070107070840200b070341c0000350140e02501c14688072501541c6149110307030f901001d509241c0f860700d5038440c00e100c490700c0d01c3c00002c0c80a0140f05101c4a14042c02003070950341d94071b021084044541090b903e512060900c0040042001008401d0142003080d0007003091f8815500c44810207100546c00070b0100110700014000c1d039074040f4150541c11020303034000c5921143c01e0600440000c400145004060442e08007500c107030541c20450b00403102103420313224940c030344402040c3c0714910b080c405407c000c42003080500403442800e0344c0d5808590000d10114090450382e0360f242640c400e4a050f943d80c40080f07a4511150700c417982c0080e480c0c100400840c5030031b20b040d00600707440c040d5115444495190361b00040601a0601c030f94280001c1c020b0003 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 680235827 1250 680234577 680234593
    0x13031b03090924050102030a05041a120c041716031410051501120c09030215070c060809060709030b06060d110705011506090605071103011e05072706050a020708 71
    0x6400f00303000c43c841e0300790321003100c480012207500101c1212074003007850303440901d003508042080018900854104c0b4402c0400c0042141c1c2441200e04030303002d403200480190b5140d14042e05c24054582c0d0107580b4945401c200039008100b600e440c02c02c2c04487e4000340714911568222540360602c840448d80729015420702080010b81c0e8041e800008a10b0301c00d89440e8000c41c041d41782c100454007201c15400200d0350800051001d0320b400603800074103003400d00c40713146014200d80c0c600d1b14619499010b200480c5402d03080c00241c44003440002d0b405041440e00a0000d4034685481e03080540150145001d1000015030306002c00c01034001c039800100921001d81d45400500e400d03802442c3d00c4030b0a480c1402250008184584603e0aa2007210080da8402d07003400c0319516216145031080f2000796041d1b580f11200d105014115a480601c0d42c007014000400e40b07040d84c005802900c480352a10a8007a644000300c0c1410a81d10404003561075a01e00705440304d00894059207480120b4001c0c2c240c6101c0c85030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 680237077 1250 680235827 680235851
    0x9230403020f0a1b0b03010b0a0813050f150604230a150f050301050702030f09040c0c02030604030309060b0f03030d1a0901090608070f03120f120e01050f13031b030909 74
    0x44d074900c600d0314013075030150426500d4501030641c3c002030090f080701076001c20040c240309204104040c1c06c0010001c2c0ba4410024070394460f8a400c4d210340340c2800740e80080c0c06516880b51803241d22684000181c0c1d00b031010801001c0130800010700c008032241d01039104400305040782c803e0752140080c11300d03102d40c08064a8840150b04d020207402d03c43da921039800c020004500610102c240e0702a0002e1003c01d50034a03a04804010180203094a41c40810401e03481100240e42c04001c11802035001752800100503019041c200d0598240c81030351401090319201050094500100b02d4118068101c0c0c000340e0f40034000c0d00d454004620a8409920804420000c0340c1c2c0d01c0c072580181c0888040c0c50441b6030782035540900312124102480050804189002d40c86841405030010319610251885c02a88005860781e8280c00c65609120160b00c40c1c1d9a0401c01c03c1c0e9032000072269800c0b200d9a0001085c228450350300504008158940400004408920f0f500301030083e40305c84094500344c14107104680680c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 680238327 1250 680237077 680237093
    0x11040303030b03010f0207021005160602030f06030705030c0a140a0914100e010f05060a02010b0406120209090c0d08070321020703030c140d0c0e120f0709230403020f0a 74
    0x800c40c00d110394a083c05100b218100ca1003142c400c2070340a0b20b11400c60002e0ba50990303064005070450a00f440005103200e00084052004510501d0a902002c0440c00d02078184752a250440d04128065803001004040710b0b59440301000445142c414054480b1038020041886000e01d54400004d0380d050501002e800008151018454005e800c0001e8030565604003d5002c07a60070321901100c1480c102050040b4105a001080318010a000108801c48044003040c121851944920320072003854916a0842c9061001c136508408500024600d81c44101c00007200f00502c0b4100605074040040c9440425025800381c071030003840803600741c500d0b80792001084065408150100d00180c80c1c00e1031710110602401c00078503031030040d40600d400d0841c1c96000c40d00821004814005104408502134100da446e80c0c0d800c00c1c442c40030f8010708098020015420b18204490b044030950381d041801c03440d1035007802c4440707001c1c2c0b449122040b11151210f08003070741402010329040034280100a10041401418 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 680239577 1250 680238327 680238341
    0x705120a0e150a0c062a1121030705090a03050d05190f0e0112090b01122d0305090a03140f0705010e0d020f12030403150c0f020a12031104030303 64
    0x540b14508210242c0618615502c1000741482c04645052405000b08016134480b02a012004000c0b5280b012940b83c0b464104811200ea80009a1201d4020000c4c00051150205039048201070460245800035444440e00004040030200100401e400307003195290813a94004540020550b45a8142c0c04002003140d880407562899a0210588522342d103032046203a001103201665031400600030b1341004440e01c07182e011110300840d8072105028045010704801c50b009080c00d4428282010300c0c4c2c90809501d002400c00c032010090465004800318211000300002c01c1d41c1840c22039690300320301000480c0707540070340c0004d801d082003028107540c007000008441c0001e02c0e5080c201c1c0c03a0740d0b50b101c2c0111514901c40a41c4e64103ca5016036440050070140114950403c000b4640307091041790a01d4245980c02075481070320b8903003100180d101c20f11a58814032422107000c0ca08240300000c405006550f60451a0000b801d01d144250f01701d542511030b43c00080e254100b000340a0b501c0e5a41d04004000d4600 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 680240827 1250 680239577 680239579
    0xb0c01051f03080a0c0c08010e0c0406080c100f02031201030f020a08030a35040312060b1204030e1906053f0a020f03010303090303171b0705120a0e 65
    0x1d00c1c462030701034650300c0c0c950003100d50100201d450001006801c40309215001021142007400c05d00210724400e00303009150944580d403005007010428a0108801e43d07111398406900354112126001300340e21000003040c080310080c20100c1c8241e4000708102d145200d94090a618103134640d0010080007407078085981003078000c42d0742070001600d600c01d6035100d2140e038051001041d60901e6034a440c512010b082c2001580c007445251000040f584110b0346041d08031402c800140402c007500070440201c1c42100050250302215604207003500001604240020308007400b0b11902c421a40d4450380c84845042d8003001d100f005c10451581c0720400380440e008500780280302406804400510400c1c82d01a102c0e001d2003010584803224107a50a20a40e2006803071403090b541c080004140100c00c1000650007540301750343c0c401d03096103142001051250b4030240c9080c054445001d1100201085201c8407180d500700740300031b54900c441e02d042d80c503101c002d000751481104042540c881c00740e004161a04c40c044 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 680242077 1250 680240827 680240851
    0x8100e13060516120b0105090402030a050609100503121b0a0b070f05031e1b041404060806040b0123040e070602071d13030e040f2004030b0c0a02070b0c0105 69
    0x440d112021030003e56200c190000500c101462600750701c05803c03621014806041080c500341998000c80c00348da004a540c00180c7d034031103040c0f00b500e08210511581c480c03d110102e80e0800d08005c00a52118804100002c102d000030030031000076001701c030001c0c04541160b021100c02c08400c6c80c1c10340504030101c030b0090105414060044255019004581c402c080200380c50341036960b03040304004402c5020b85030745800401c0d246640c00303408082000b04058090140382c4d40640340c00760100015154a50002c030a142c025900b880001020700080c0c6040d515000c0409500f40103904c0fa030300c002c03600300c96029409070415550311071448001c81d808040d218654280c2d40a0358448590b641500d0007040328012501051000420f4886004c425810082c828500581d0300d580e090f00140c26079099031071005030a541d968024800d01144a000001503501c05c41d00d50526140d900c80060210004080c1d43d041c0c800041d4007030000b4801d00c80301c030150000540c001d407900602040c0c2c40c02080300315100c4100fa4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 680243327 1250 680242077 680242081
    0x503091005180d0804060b01090f0b0c1f0905120a0507060e011107030c02030c0114040e131a0702010b0103060b07021512070c120504033f170f0405070608100e130605 73
    0x15208800100640310194014100c0300d00d0300e903d540c1150311040207a00d01c3c2c011001c0301d80d00c0c81d036211040c1d00c0e228dd89045c003041803010b5040c0703e400c02c81d00c000c00e641043c0c8104610b43c80c26422000b40d076100e41e08140d000407110003035400d250141219442c00c0003948400141c034402c05411484543c00140250101d492821400c001074a00348072014807034004140521040005010303400c500f40e4091560502107441a099a4580607280d0400001c5264010340404002e04039074248600d408601007481c0501c401c1c1d1400001d92003c1c855004083e000380101c10081c04034145000c202d40403030400c03080802e0355150082000388226880441110340006030345d05003841030312a000740c0c1d0a482e004440c404003088800b10b8110708610780d143c02441c81550450820b4a0350020b00841c220b25a5912071209100e6012044400c180d002410281101d1050080c880494000181c990541c1c045042802e610380300c5804070042008a5488600062103050402c09a45240c0803002d041ca40b181409121079 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 680244577 1250 680243327 680243329
    0x204030c0b12160c0512031509010b0d0f0902061201080f03070209070c03020a0215180312180109170a0b0a09030206060f01090f0f03120503091005180d0804060b 71
    0x94407520008582ca03070305071404102c0403540340e070310032100075a2070400312598031241d5507050601c1103660344418092804000c110042c3d02021008031200ca0895001c4210340c140101902c450186010392100542c0d035456624182d0403580c005100c060f00141358a45172011307522440e808400074011151903004441419110020020640d55400d81c024000c042e1071b550700d0408c0b661070030022419021440f0b807440c50400350301c40d2141e13003150fa60301da06440d581301c030007030f404012140d0242c0e4041e00170703804008080c10201111058170510402c690b0382c04400221030740100d4030b100540d00907510442c40401c0300d044810002580401c0709101e20101101566504050001c454941801401607041640010103a142030f034040b04d05800141001c410042d2907484680d0134500f01d8114004503444030130240180103a021041040146c24a80a46180703025029940c03180c05a00080603120380301d43c0490f2201c05841c0c4185201001041101c124240d02c100003400e039202681c003a5442381c940304201c002 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 680245827 1250 680244577 680244599
    0x5010b040807050307030c030f0c0510021011071a101d0601030c050405061218100911042a091206020d060806010515030415090f1502120c07050c03010f0204030c 71
    0x861b40c21040352a07c8510710b8640c3c41b600082007100300c55003c040c110200701d907642c1011060a00c030065004001c1300640d4100c100486d10030400300c1c40c0c807540070301a1310001080541d48000d0f40d078001d00c03100019110345100170581105e82d003007000b21072401c5810300f50214a2481d42c510440c2d0980c3d0a01075110004400e803114400d60043c07581115082143d4401c1e68020101d00c1d8106005004420084070b0603072401d4203003c81a00740d4000b2070384404c80102800142805000d016408503010042680805c41d14481d0112821880940303600022800008030300031300c883c800410044001c40700d05002443e0040095110040309615a864894045000500003400c135050320350140482d010049c1c00710185a0795080284100c1e4840e01052440d1310f800c200d030003952100c92150748441c200b5009032510b10383c1c1c02c2c51218201c0d00c0030310512850085400d034007034590300810705460300c0d82e8500c4d0a0500609007541003982c2c680560800e0074030a8401001d60041003268000c0c1c07425080c246d1141d1800750 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 680247077 1250 680245827 680245829
    0x9111503100b04030206190905060d020a20060414100903050307120b0603060d021c0b18010c08010510020a14030d0b01030e100e03271c0203100510080105010b040807050307 76
    0x2d08944144078100c47d02c00349130315003020344100d404c0c0b07440e0b120765920000d1103d41c4607691161143d50042641020140c0006003201da07005d41119101d20107006059403a5a544010000741c43c90701c10210250000c8014041c50500c0c0508500c1840301502d02d00f80603103280d00580f540000120602d52050a1000711b2180c0703920200b00030805465034403400c1c100300180740310b0b070740c00d07680700b03d2620038500d0300b22015050b0120184540141c0b0450328000341900c407403085000c4907100c20b03410700203860185507106e96407505542013280c40e410b40241100c1c040346040b1013003030001c00001e00034409640c181400000b514029002c90800d0001d410341e4001142903804040c4400381990201c0110320040310140c0100b071040d5600307001c8904291f00c8403940a901c290200d6116440d5a0f22240c00c03a0a00382003103200070303960041020846040003a80400d68a096444807249410340c4ca90200d1944564890490000c0c5142c078000c0c003ca585030354070502503a125100d60780c6c41d40301d03130000024542400703d2031034 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 680248327 1250 680247077 680247079
    0x1c0f140615120607200f06010e010e0c04030807150f050117070815060102030f162603071202090a0303121401080a12050405060307030e010f05130609111503100b040302 74
    0x4440c1d134854540076a202407214022009045410140e0f010041041050200749510807008001c1540762402c0303409281c0041e00f080d140018540e04200c14000300501b101c0890380d002020a9130741050b0304002041310001a1180d030381c541800b81e070000014264012038140c1d00c81a0580c007201c0c40c442d000641d68030040c030420500d508003001c89000b40306190725146e444401030040d07d181190341d118a03002c5510400218030081e00c1ca503004001c0c0203a003455841c045c2035454100c2000503801c500303c84c0c2804003ccc4203108000016452038400f8200d41c0596130048005000d4000d080e0300c0303180c041e002c00a00c10344a80342c2031034801c2960070100600a014100c91660014009160144d2144010b48006585010500c202000001010384900d0000c61258901d030b60000380c1a4240d050140c29920103501610744141460240544084922034145140b580140f0014485106150032a541d0700c440026650211580d0a9580f003007003028000c1d4840e500e2003039060150750721002c0d500c001340594000a = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 680249577 1250 680248327 680248333
    0x90c01020d0905040b0a03050109081309090308040206180901090204030501050c091503101802190c200f031504030807020a0b010515091201060512010501051c0f14061512 75
    0x700850b0500d42d0000d01c101c98040d106004540c0c0b00e4031601d0039514101c004842c41140000d8334090300402c8284800a0300030039005201706000b41e10002c000da90302030b00180c03003a50001504110344002d5544201c030a0800f602c20b124940c3d42e0b0220348025002403100740c50035400c05000455900342a01295040d1400806907046d210700080400a0754000511080c0074540f194004120700b038000171111420041000050788e200c4c038140224500e619008188d00500c4440010807001030240032141542018075055507141c640f90304002910108102e03030540c0c040c00303010a00310325042c45040c110300c658001d45400d003498a4640d0103d0342e403c0380d01d601420468074000140b0661a02072900c038400c8200c4110b407070903c0701c0c5100083ca0003018030b00c11580d80e03540e9802000349042903441c0c00322500304400200265803601c8013045110a4101503e040c2c802e01032904c1007046404100d50204503040f19012117450584c030000b603070380d00c0d09451884609031175501d0050203250002d14007160002e083c3c06 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 680250827 1250 680249577 680249579
    0x60509100608091207060911240d0f0203010b041403030703020c040c0302091807260406090302012003010519030f0b040507170114130804170106090e06090c01020d09 73
    0x20854245002903c506607034041d4640905401010b4006000440d001c0c403c00285a80149044258061100e101c4e600403502c3e49200d40441c0310445003c820010310803080340c0e482c03c1015580b00280040320b41d1600441c40480041030a01c1d44101a006540103d103100c0b80c15a00700040590340c0c0120000100180d101c01d04480060a1582124546004a080160801c805140080c0c007498089030341d000ba6407803030002c200c2d0041d80161800000111178000c0000d01882c000458201a4000d05c0640131580321140c44007010710035884074548010b180003c05c0003e11600082a403075100713104851240809131010802045048100c00480f07070b0104080601407425030f104c14500000620070740d418051741e00b000600910054008132441e814000010f0503070240c1c040340b0011000035007102c5112500800c460005040103080300c00344e404205842d001014415042d41c090002c581100ca10982000c02000244000040c00e9020b010114140da640c1c14100004983d80c551017040c01c400235402840c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 680252077 1250 680250827 680250839
    0x4080709090602091f1d030d14070804080a1a010e01031b09020a11100b010f110304080d0905030c010305040809040902010302070501020309030c0d1b0b0a09020307061206050910 78
    0xc04a280140310b03030005801c103480280003584840742c13600d81a4421000920900415620841498002c1103084000c6204907222001ca941c40c4810740040044c004800b801d044a460914284c40e01581e0090090b40d035651102052038840740d401004542ca810313a03030f861000d40711300060058161815000511602c1e1320715104c03200800c0301142250944044003501003065206400104100c402075280d4940d0071031650101454903854000c209030b140c2c41c182290507147e03480311941c0a402039034a0301c2ca15409403c2c840500b9841203034001646c0d8440c1c881c81807688c50304001c000c401ca62044040c0c91581090400560646408070b60007400700d002040301403203614055008800390750040c9030060906840350744441c220307070055038007140a501c0490000150003040118120258061916000c1803182c1e079481107180641d40b0008101d00e150600043c0e820400340c0c000c40680790002e0486031016510800685981a90703036103091030608200010440e41030140c0754601520040100d207040e249085 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 680253327 1250 680252077 680252081
    0x80c09040602070b0f0709050604050a090b2d1315051203070203010227120606010c1a1602010e03040b250b040501050a0609050c09101107230604080709 67
    0xc004481e607540c2446450003007031030005060302c20580a0805505400d118001038082195079009622498040009125a0300c82c10b03407100032074460040101e424005940010a042e1945c07035141c0d03070281e01c0340004c0000344011654200e5443c0640321280601c4985128a080d502c60150b204038004420408110703074142580f06c0c51942c0c0c500801d8174108886075001a00760b0b8000e44960028110307265172403022403105229032004a408940100c4420b024045e0b06486c4c16008141a0510800a80c2c0d041840054040310242010b014100c0e05c2500e4409900c44400701690424001503113452a03490482c1d00020844042e2403181e0700d0107081c0019034884c40001c00d985032200d04520b1800c503002c00098864044c1d90b00580c4904e00104a902e07180450f4021604141d0200f1004c80c1422305002d42c80500d0000c43d4140d64007640c0c80c40c680c031200700090b2822048104e07440f000344240e00c0001824070030010290320708640e80e03012201e4110b4500030081340b4003031401000d1850700444c00c1000501090707 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 680254577 1250 680253327 680253331
    0x4030b070929040f06020c0a12050a06021e0712110105010501120207060f09080c011107032a05120a020c03030304020a0b0a032c0d080f1311091003021306080c09 71
    0x3a1080380c41d084e1100310b80e01c2d030f0b4201e96100d0380159104400384803040ca003070301c504c001400704140320240c0d0a06984440e5614010018040c203070740d500190340c0081d00b8006003040035006a1442017279036811070f4a000c0c4060701840da0f40100040304e0030301003d82d00f0010301459040740c2d41695610421001b0b8a00c034402076100e0802141ea05540d82e6007211000014081d10300030030b000d64500b64031031012207509802d607445140f0040300440f04014000019030003c64144010321800005030384540d15000011507140880c4014000340b00b281c007105148070401001b410440031581c2a94140030312003052543d46d00050710001d40c0320b250818240b0140a01c100a465141c020349404075800c580103504440340301c04903200081d50702900610300354540b41005403008156003441c4c075410758078003039a0b803414400c00501141400000d41020038180600200551746544e8020301001c03940c28258600d105612aa00c0200d000d43d030207501710b414028052280344122240742d8044c10000030a101040303882040 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 680255827 1250 680254577 680254649
    0x2100b0f040603030206100e010614220e09010c05181020060a0e1902010e010c0b090a050c0607110d0212031201090e01020c0a11011b050304030b0709 66
    0x50340500c5109075076580036802c01140260042c00789803e060204030540042d0f5041146180003400040000703580c00b100d0706100480300544a903d81d80900d2100082100201188003000d03104400030074145000080d450151802c2c0c402003007458000d0070250340b14018103d1040d000060020098441d080118039494019401c1c684032001d441440d00e6107104c080701e0324090440d81d11040401900e0250b521540302c0100c1080000e02d6212046c2500403050181450003d0400c00b088942c049140d0040398410b19040d4014100c00403444d00e40e03036403551a00018015140c0c0c0c8105010123041e0305003201100d14145d0404146162560480300303224a080020b070049030481c0c0059203078007003003506201a0040100d9100d002c0c0e161351411540300155810740040310401d0b40b0410025400010014540c8402684484102c451503d01e40c0180e40d000301d0f210500d0352088061810104201f004401041a6440b810001145032104041100d609000340581c01015001803100c549600320310703d03280c0341d80c22 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 680257077 1250 680255827 680255839
    0x1e2703080609090a05060103080316031a040f110705010e0709020f040311061c09021206070c11190e0f0705030105060301061d10030c320307020a020301110909090105040302100b 78
    0x4207540d174441c41e00509900c10707101c0f0003010051149544d0441c00342014842d10b840d0500c420402c1c051007120f01112080b100e0703c00c0d691808841e5520f0901d4119400c04004480201c1e150083c1b170800b2406091091607480d103e0003001e0003c81d40c0c2c0d4407407080e24604d404070160a803c0c2400d540c2c0b29200c05442c00c4c2081ea2112040c00340d6a98810804200d00400140316400316542d0b85a1050140240e40c1038840f80361600040c040004899100400303102180d00200a802840441c070003080350455a600b413910501070b904800704110381d00202080c0680d0301c400c500290f80c2d8914508440c940820b0146a511610800040000c10700c40c43c5803006800c180045501c410325501c001904152229013880d021a484982c42a86160000c402e0b041c2d00590102200ea030113008001c0002007503103062080c1748940007001080c401882004003800c9158041d00800030100c421400300c2050704011010361203229601c0004500801c103004aa0044d03605800030084c921041202001802403081000d070040 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 680258327 1250 680257077 680257093
    0x61b090e0109110412061b050c01050a063f0c030c060c021305041a0a060f0e09030703031d060403020610150801060305060d0215091206040f1101031e270308060909 72
    0x5024a100747c1c090200c140c44580e0b80b400010051429204c6c020015040d03e4500481009070101c0c0f00100303030b550036003581e50b8507a4140408400624026002d505456890b80b146000704110010101c10181c0703004070100c1d103a65aa5000c1111825152400250842264110384400440d03a8001c16000b42c0305204000e0404484464203101490842d13403c3c002e01c0c2ca03043e04002c244800014100509100340e0580304a00d1724009142d56841844001001c15940c0c8090313100c40c0000c8100007601c0680001a168181858140295542010b5580c010100001040082d588c510005846843c2c107142c1c9804d491607181100580061900a1045421083d2840e0520040c0c0d200c02d2800e01c81059000d009031200940d10070310941c100f04180e07102207070340000144404070b00c10b11400f6104d940d000450f00c00707283c8000c004a01420081c5041ca0181d4030040c0014a12862500022402c400300785000b8107041031019206082c8000c142d010300801e9440c00815220306000c1d01c0113900c503018100b140e48a03 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 680259577 1250 680258327 680258351
    0x41b15173106050c210c0712090305010c0e100f020106050a030807110f090f0403031404050c010f03020a050a0c140d0f080c090616061b090e010911041206 68
    0x41c04460020204a07420303850014204061407040642141c800e081c40d504000b0300464007460f418124000803e101c201d0b800080c01d034601401220f9409a126100d04a503404500c070141800c445400100d0b119400d00346100c500903c01d843d2003182550050a20200e089058030035107030165070518040444d504c2d1000864540c07108214040114405da4085540b002c030ba040c103242c095210600750b07120355041003075a201035403003e098a4001640c814540491744640c502070340101170028040c95040c0e0a20100018006c0118001e45c41c2d0100780c82d00b400c02c000e1414214101d00c00e208041e4081758080c00903030000c91003012480f201a100385500032060b018404000c6c64a50380c0302c130030790014680e1450060328641c010421a002040d0f4800a810900340d1400510b142c0680702011138241034055881003800200d40003040c002c1ca401e58000482031030620700070300c484000e02510503500e940400005060b2013902c264500044140e8416081600381040368481c8400e02c04290780c20780d00e40d80c501c1e41c1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 680260827 1250 680259577 680259631
    0xf070c0c080d080112050a14100f0218040b01092904030606061206050604210f0c061706100e0607141b0d020d030311070605041b1517 59
    0x6808010300901c0c1048580c5002030020005030850f2007100f01c040d18000006400280100d0810b500a0b148c20034088140c403264500410507112903d03550418486255040e004d80c003c10b02144010000d60390030f0400c409001c16991045ca2040c000b580d125410400da0700044440c0c102c03c80d400603004588880003040e80074a8001d80c005480d01075491108101e00c82d089030291034100c010702c0d0240b104514090001d007882c0030741d100c0d038103605010455900040f41761010054525510108444071041c5509294081c002c8a00500c0c001c01d104460040445112106c22440348100901ea0403d0001e02c4108580364034a61040a801c0801400032400088010300e841d42d4032002c0350010000304140d854204008207180310322501801c0c0001c41140075885520501c42220781500300401e0402812485860f60302c1a84c00150216140c441800108050160b1034050485212807585995480c1c655071599440e80424513408100342c03041c0301240c01d00389501103a000c03581c510420007000e244031400031 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 680262077 1250 680260827 680260829
    0x30f0f06270a140118200a0c060f06050307141c1109060d122102161a0618070207050a0803070c080d140702030c041e0b04090305030f070c0c 62
    0x39200c1424401c22000ca01d16225114200c0e071091038880f0783c0d5240019441098139a040345622564680040a001c1550100c0c0c160b00c03c003030010443e5640c07210000c01807a50b4441c0c00c04030350f0303203040801400010416000e03c10a4034001000f0b402240d20f80340c0018036054201c0b6000360044520050720f046682089152001940a8030400403600300300b90800c400b8240060003e131050301c902400d040480c0741c801400f0000c50320383c00e041c10b044c50b840404d050180703450004c0b83c40c1640005000b01c00c00c20044200c09403103204103440c1c002150796003902d02c90720400300c644640201e042e503982c80500d50440c69068002d260390054600381501c4030045240703c011604030380195800004c034134040110001001c002094824042c1403540c280310303070052007624050100c915170000491079000350755042c811000760400c005c00402040708515058102402405803c0c0c02d280d01e400604040390401e401b540003040c0d4160780d224070310754484000e81c412141c080e02407002c00c030000c50034500051190800c00 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 680263327 1250 680262077 680262139
    0x70302061308010e0a1e050c03011e0b060708070b150312030702100c021e120a0e0a1a0d050910112502061e0c010204090204060905010302030f0f06 65
    0x1c0c605401c1080035801c2d0f0300310300c0c0c10250030303800500144046482c0c02221903003401d405c0707102400b40f00e150400390704d4590b51200941d4154039049511100c01c0740a2801404a4411901803100c4102e2404003c00c50080060280456008101a03400201e202410035400345041514a40302d011000205e8a4041d114030b030440346103c000144884190100200761884c90032a005100c1c002c07030480c0082d21070f403040101084640a000f80d03d4210f100c01d112400607100702c212050346a42004c030009140c02402c4032031900468800d10007090403007801809a94050081d00428500341031400014001d003030003800422a4004c00e141302101605a024082031405c001007000d441d403030201c64030010312864542510750940c03000103200040c2c8590003950030039001e440c0a140d89003c0130081e900603100c0d035562005103520004000c120210b03aa4040c3c010784603980c7d47d0100c0039480300d0054007240300640e440500240c200c00019004107980c1c28643e07001c44051321841114846120003040e46207190b0086d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 680264577 1250 680263327 680263357
    0x1201020403080a08010509060f0906060c0a0c140105180d1109070804150b0f040b04020721090906080619020f070602180312030f04290a05150303091207030206 70
    0x22043c51540001c0543c050081201c3ca4005821300d6400609820f200c000340600441c4403100140c0b0342d42d01e10b800d84919000a60941c1d0303060041c0d140a1100c18610300070000b2042401c010001c080d40f2403c2603680d022a0100c0c0030140503c0340040144450346040100c400c40b0301220700100d039480c2c0420890140111340c844e50740034102850300c210041200c0c00014116442c00d40042225a83c01402c20110070017981c2c00a200050100070a0192103030410150900d200c0307100500420502d008010000760460b078480e400180c40d10400c40566003075203c6c9816030b51000c8082005400e040c40fa084c00b0b94035070781d030042c81d1500e04c82421035160440d40c815100c4690104404000340413800c48551031540c00c03005030095031440e24a8038424000a816031000341001e00020701004100e0803071042006074a151f048202544244c02c2c1d41159007114005c0b81c0d2424040424000a1302ca909810301c0c45006016604105800051062190341c103403506c10f4900c980200040541c4030311009100b6206040c0d00 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 680265827 1250 680264577 680264587
    0x1710020d0f0e0c0d020f0406050411030f0708130b070917010c09090e0618030405061902011d0c04020a020c1c12020a0309030f0827011403010302090406020306120102040308 76
    0xa0221410380c42c070120325400003807004800d5074440c901c416500e035049580e0303130300d482c1c058000c1401000c158002c581c0283c1350030150700581000300041c40c49458102204102582d600b541250802402d50700c01111541c000c00500002c5d0318128070030f41c80881c07498101c0400c0d50302d006c11200300350241d5032001641d540344014040d4903804111200a01a001c40900500c002500b00740e81c1e070f0100130455403915100004460100030140201c3d0700a2400034916600e40810300c0c280b540d00c503804800400036603c1c0c10418014005a01103c2001544c00f60182c00303100050004c3c030000e98408a800304c118007032007980c11070b1a590304400300c00f002509240d8622100403403a00400071445d004102055612124418000951000940d0305681d8070515404110385180f4058145009215000324100c2007542c41d1840c07201c2c00284000c8028090342c440071030907080400920240301c20f000c040d40110000b0009000300d010740d00115007120300605000b00001d0321604c01400c82c0c1154208603a80080020 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 680267077 1250 680265827 680265851
    0x50a020307230d080912090d0501060305010c0908010515060310050d080c070f381602030106270c020c100f1d0d020d0206090d0f02040f02131710020d 66
    0x300c65506920f00f03050a020034145560036517a120490b144a161511002031a241c6540b188120030214036071003c024003400d0380300e2820038040d0076070500d0702c000180745200000f02044c05024040c0144d000e50b515920144698007800520f83c001020140c0920074441d00140d00c0c0c40e80b0124501c040d000b42c1590340c451880003022403d0440b0703a0700c042c03e224a504c00c00c1c0000028003003110b44d005100d0007494454038a85c0d400c1c0c0c4035021f20341200c0c02c0066003c2080c41c081030f440349884016138421002003103019140c1d4058603007203c3c20310812030000142d246002c80e201c0e01e60f00074408006240129507818100c5400514651102500c01c80000c40800c40c0c82502038000c5941d40d02c4040c162038200400b02c21802040310307085d0003d0080d03c5040c4001c9218199116407085441d680409445d45002442c3e070305100c0d805860003034049004501e84038080c03520304c000c0d00c01d03640810812240d0724005450400c6030048242041d02d51005030007000d0320f01c0103085041c40280108551164040307155a2102 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 680268327 1250 680267077 680267083
    0xf03140f0c060f0c07031713140604020a0801060f0b030a0e1c02060105040c050909101509061403040b0c0d060e070c2102030406050a0210020a090513060e040201050a02030723 77
    0x9800103500d00c02c248003000000f40c22070450300360040420002c00041d6600b08004035a0b48000d8005898034a09c100040741601c80800c0c5c051040d40255580c1d03035070650380c1c0003031400c948091060040c00c00c072054040c80314019000003140c010f0946240400e8144d4031191140c10540d5044042c450307489400b0183c1100c41d0144006801050104e40411002c800324001510f03902c54010203500c9040341c0d00016110283c0e40000d400030301408c40d1820020804410080d280c2c0c80b00d400781602141c28843d0241c010495481203070300c0380354081e49104480d12003d40105260b0000481a50015100c2401107540c10b082640c0b14403c0d402990780c3c024282050910341c020380b100e00d50404000d520207240190b0141c00000321030441c4e44c03600d002d0313a4640303d03100124100041c1c4600c008080d800080c10000039944140e10005940c022203440c0c00c0205100c5250f0121610ba105d07400012020a00040240d8000d01c0035003028461401034074540380c0d0340c1d90f85090080041c800c41140ea440d61902d004200310030 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 680269577 1250 680268327 680268331
    0x9040513030818030405040b041d101d0a0f020604091406041a1806010207080618010b01020610031506120507030c050102010b13110403080403031707030204030f03140f0c060f 77
    0x1442820210382c3c40581d03243e1280710310300406d40901d85034200b03803900b0b8540340e1102000d000a820b080c200b0791040c0074004d45589001c64245a4941407501d69500d01c91100340281d41c11216900502e482c00f110340d00d00c84040c080801c241e80c48442400700003030201d41c502583d41140c05105e003090031840d1071002c00c4125850000346010148001003034602d1030311020300c41002280811001c0c8206e50301c2c0b0004034981107082e0040b03000ca0081206105540319540d0100d20f0311100c80b0002d0000b41064001207a1f82d40e8103e42c007005c005250350f01007011589011104c181d84c11550404100c1944500100041d000d500000303c6259026540400074030884a05c0701000d460300740300a129802c079810000d4440341e548018400f032140d80300039074924200c98400b1280116481618191582c0c1c1c0c3c1d0501814090071094269020791000000800841c482e1003103030b0a9980c050050703c05d40b65192421100c688030354580d215810801c010401042846002400380501c00c0070081c00c813890004e01c1ca0b410b203280 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 680270827 1250 680269577 680269591
    0x30706091a04080303130c1d06040902030f010903050310050f0310050730050a0605010e0906040b040c02031b1501031203091e020a12020907140904020316230d11090405130308 77
    0x2235083d40c03140b03646090002c19041141100c000c9a10440d500020307040c42c9150034030003c25843d1422400401d0b4001c405140f05441e8034403500c030b281e40d442d0300b441103120b000c040c02035058100320b1485560403000e0740095041056482c10540d002420b0401964100301c40c684003241ea046180035000f81c520324002d4aa1000c0480018002c0c5031038840047c05900d400e0441a01c140e404000047c00c94a2f41d602811368100000c00500040c0411036000c0e4480e0300260350480e180040e89509940914001340304000c0c09641c0c034101c07110f40e1a688a01f40085617100c0d0f04005c0507210084100072031982d80310b007806a0285004125001c0c100e104000407032001e40c0c0301903c14841c42d20030402680e100c082c1c0660203200303420041c072060390781c003001c2500d8800d0055283d4020710210501c400f500200003505503204040d10f031151182d65000300440c05200c054035588041300104031744000f01049400200840c500b50b128241070680100001d4141c800171100d0800a50341c41c50b521041c56400340d01c0c160428a = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 680272077 1250 680270827 680270849
    0x1060509040b0142032c0d09030201080411010309140d030e01060f030308190e210705071a090904050f0d05180d2409050606030706091a04080303130c 66
    0xd540f5140d02c02092080002c041641c4410440b4201300703009801c03151018101c0408403040d500407100031800900e40b1000300050b03120700d000c1c40a03807a010301c1d1040d050301c0e0140c544500c103688a544048804405058450405849829060009070b8071f0003c124003e0035000a0000040807a000a007124401d0b66202c100c0d030b0521100b08a003004504842c01500d802d0704d403001d0350b50748140002e031000c62080c40c0b0303c81017460120000344076440411000341c10040d415000c003a407081d4201c1a1680d0040c1c18016102d5080600100403080380548100540c850240c1480d040c0000b200c001440400e0465041d00d5503002054221061902800031455604e01420042c0c02d14100c075940d9490100c500f8100c902400440d042041402213030b01c901010300c0702c20281c00300941783e2516550041e05400100f2500c0b4400d04010640c0380c60041383e00d40c1520030326685d00d80e1683c9003c00044030f46210364003132042034030100800300e4140c5091000f58800c029100014150906070b10341440761384426400251142 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 680273327 1250 680272077 680272139
    0xb0f13030507020d05030408120d05130b18011e020c010501080303100312020307021c0c0f050f1c050604050d080105040c090e04051c02011a03030306030a0201080901060509040b01 79
    0x80e04102641c0c03403143c041e64100e49860051512034510310883e082007103544502030340626485008001400c07d40900320081c0121b4442000003501500c00c1d02005018620420000348404107090602c080d03504500008201c03a4050f14090344080195501d100388a40c001680b00c42e00c06007401524010a441c400139451460310142040d0071380644d000040800090440c15100c09100f0026106507640083c0700720448020502c090b640b80040c00c80c12035002d48866000203c48900501d81c004580000c0c0101d841e5910400030403045502e14030094842c800c1b01100780c1c01145041050301d00c55032290380200040360710340310007403c501c0050b440140f00303070704041c40381c3d0815500031001342c115030404408030f003030b078890345800d81c2081c0d69845640d000000380c2c20150f002c0313981500702d0910f00305c81d8600d513030050307240d50245900c921088a0702c1c0c0c5c241c0e006075107d0006520a480065000307070140000100c00d0b407200300203235a403502a6410f40d01000c330780d00140b180000340001b51a0389001000720001c18 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 680274577 1250 680273327 680273333
    0x409060f0603110a031a0702151003050c040c200111040332101d0d08010618030825080a0e0f0306040309051909060e07020f060f0105041a030a0b0f13 66
    0x1900402c0e04280060101d107002c980350354002c000c440a04402710070b4102151910294041d07411226100a80b0720f4451b04440b0002030134240b086114038000c96991205640b0000c1c5020019003070895041440d650700c1e0301c0c1d00031500448014002031442030705010301c450340c12414201040c1c00d6464800104140f500312507601100040c01006c8001c21000100e1048241d03246081005419035000000380030318404103d80d076034000550390585130759855018400c030410480c6440403d6501001f02050010402103800705000380c4500c40ba260718418401da0721400d85e0710791082c2d0304011942c0c400301c1c01e003981101140c5130140710035013440400d6006091270f14158400511000c280e11910f405010400003a00c00b182e80e0084c600041c0c0b160b04014441c0981e50300032982c107800c0848651005000c0c056700d00c44814030104260b070207160f2004401e0711990918040100501605030101d0f101528080c000303a89443c14040c80b44c0c454000c0c42c0d103090307520b000c207251956504003c1181d0105541c60703c2c03444c00 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 680275827 1250 680274577 680274593
    0x10801150512040c050415050301050108030c0a080c010608070611070608090d080702010e0d110616050409050a022b050108030f0a0e1801150f050313110409060f0603110a03 76
    0xb0070000b1141d403a400740c03a0307820310148107212134104035086401c10404004100030325140e48103c42d0260002c000036a82c80c03041130340700c0c013030300d403044940b904402040f0001c2140d10001d07060325205100002511642c6800161402400d58400d5001c90134902100c101144180300c0c1100034a41f07410545242d1910740d8210f901c500200e1000c4007801040000718004500c00d501201542094204440410003082c1028006501d142002d8402c3d10440c4001011862400d903030014000c00b40d150a82814241554480903000050000040e643d09000102050010980315900301021340340394120300b442010b030001503540581206040e540104091711110500344210350a24800780380621801d01c0410000d60700c0c1440010104200c1d5a400000c940c4448940002a100950740c9910512a003c410140e449010848010450703441c0c0074051008103030130407100440000c000380005212181d6540d101d01b110081c6a843d0141a1350317030400c0c81007041010300e0010580e012100304403101c0c550790f15690 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 680277077 1250 680275827 680275837
    0x20111130b070c03170705070902163509010e01030605150d06030606061e0305060a18020d0c030b040b150906071a0415050f19240f03020108011505 65
    0x381d40c5000150200078012a64100700c0a1544010940c8500841030401c0f0b0786500600400e443d0390141d0040000c842c0002d1003210000d6803001541d510b402000c0d1100c0907021040307030b00780e61050540c1440c1062035056a0406400c5180340455a0701c401d224800106a080b1100029061514054091005984002c0900c200702d10380c000259560310401d00350405001c40742d0008107254107011010030a00d0b0000b0300344c610400c12542166084081d407000b1002d81e00144d4006070442200141400391001110240a01160b1004013600d40309080810f402190031072740c00400026a00e0300d51544030324043c010603441440866081d501c0c0b42408000700342c0d901c540e0720098850070707000030700d5002c100c03586100380028402d04a15542d10700d0320b8144160303044d000403000d50715185010005044242002001070150346c2c001102c6010070480003800006000030340c80d840192000b55000c00c1075011240709080a00718641d03100c105a0b24510014140d64010380040c0032400c846203450058603032000c1039070 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 680278327 1250 680277077 680277089
    0xe0613140301060504090b1b1309051b0a090810200c070e040b060411070807020d081b0309040c0f0503040323030a020304051c1202031005090103050d02011113 70
    0xa040d4011100c0041d0041009031300180d00a4100402c44041c0304500e200d0921503c6030303107680c04418000e8803503032080c0d200c0d47e81280e08031038440100344400b41c0160711088e403240410080800d81d25100d903040c074079074000803404000221082010721950070213001c1104801410780b0140a500c1e4100c800c5112031803510921030500001040316003c007841000380b01d006041c60300c8041d5071424142442601d0f42701c01c686950083d404d0400c4480c4801400301141c0120344c0184480c1c7c240200c1e9400c0000d054886032040d51050400c1c0101d0b414810901d0355515584124001903540700ca0701b00030b001c243c3d041443c5010900500206005a2940141c00c40740d01c691300d864044910091050b156685030110108202005004420404180300700d5008601035400384d000c40d4440d4030001d250003261044c45800b0f0000860400d258001402c29801564002c0700a4529262280c2c40380c003c595918801d1303100752000c0c2e2050a040000640a10801c1810015403030458580803503902074907101e2845100b12 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 680279577 1250 680278327 680278349
    0xf070f151a030f0d08361c0e3106090b040207020f01051c0c0c140d020705060705010f050439050603070e130c030b0904260409050403020d0e0613 64
    0x60001c603103050415110b01540c001520960070100700d5080b820001e804000c040d106034840749204c1029440c40a0700301d890f44d61968160907005d07043c8001030b41842802c3c03150303040950019401c034409d035103c421410203c00000540307a141000440a840c41d20100724041d9104118900260f04c0b030f802e051200e0b070800e082443da140c0040c594400e442d4000c00d26800b4040c60040204050780d8881106034485000319041d03481011112070300754a600b9001d44c48009030780b01e550308000c5410030401801c1d0043c001c030000110104200159029030300300701d4040301ca00143d20040d01c8000e6046009003801d181d080305822044015421101c160f505a001d41481a100070002400c418071400303104004010140021210540c040c081d031026140c080c5800c000b090504120581070b0510321040c92003190090a03010081030444030212800340b1000c04044507200401c07000c2654031442c09040c1c011071183e401400d014040c1304008080071440580c0c0c07841504200441c0c200c8800b4513100805407040f039074503 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 680280827 1250 680279577 680279581
    0x250b0304060b060c01020c06040309080f280803101d0f070822050601052b120201060803040b03010905150303071121030309070602010504080f070f151a030f0d08 71
    0x1989402005000c1c1e92940c000982c2c2c00141c7c0c2c012030b00c60300852103500c0700c401c030079161005035880341c01103400c40c0c0a65000c0302141d19440d41e030b514150252404401c50482c103040c05d484040142d0301c200c0d000030000800c0001003219640074005690504181c40e8402154105080ca603085407401800325010000000c1c0882c208501e0450007542c54202c0031100380d984203861910f1610340c0c80900c2003a100c0c0d030328a1480d0313100c806d0b0071407c2c18152840010f03600c0083e00a0b616111603c00e101c1c440030456507242d13408180c0000c1000204050805214041d0700d0f5894403441a094400003486104462450620306402d1b440010070b0707800c01a030210307207802d001e0031440118603803192103804807196080003024100d00800100003107004d50319007001d4540054403810144c2c240c0d442942c0050400c171341004140b0601c840d0300d028003040c500ca01c47e800c01c00945030701c8401c0419051080c02c004541d803102c54040c00006909803106107030054015184d02c03d82c0c6014a80c407414000c040c0c0c5c2c144400303400 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 680282077 1250 680280827 680280829
    0x1503091e080d1803020c060306150705030706020c1605040b0a1412011d0c04050f060105130b030106120f14062103070503031006110d0e0f030f250b0304060b 69
    0xd0700c09000000b50204a2580354449900d41c40f2102c4400750094081d281844c1007030304180c13040300c1c072541d8043d11b50146541001c0804007590b1100b1420b49440c0810b0050305d00042541c0004d00c41400450010b000402e2802440040041c15901a80c480e500c2c0980c500f580391180b20750380c012500c2005070b5800950341c14003c00e603660030301400740144c2c0d480c00c0f100004c2d032072000309040c0c14440c20000b240c8400704030b4005e2004807141605d02804210001001400a610505c000d0000104a004079040c547e0b40e69207003e0150401c5c3c001ea00840c0440c00c10360f00e9552a0310919201d4110340f1014081e5407001c3c4001c800c1e4110103004140100010001699651130281303e242c669907100c1d040369500c100d14104607840c0d401c2900c0384030500d0000b01c0300059051007600302840c2c0e581024041c04001da0380c80d6094a4002e07222100c0d075000900d5420079000365070103004240c100b0303044201404041015071859502c0103503004051881007001e0300148448400b000649a00c1030348100e0018100303840308 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 680283327 1250 680282077 680282093
    0xa141608070603020d1404051e060c0d0e25030308150a031101050f032415090d03030b0907080a0c050c070306050408070804080d09050409110d08040b0a02071503091e 73
    0x1c1903846d4081c05040c44100407000408100005085141180f0b1107030640c00c1603102d10303042d140602040030900c84444c8024040d44040d1440300d040d000c90700d0016030042c1544121116444001c0e030605200410000d054004040589c440403004207050394007807043c00901250040d01014210084011000100c5e0b4000c000311a035440040c02e8250303c80c82d0825000c96606001d8143c803080010641000c602424a41002200707401c41901071800c10038801d00303124018550040130b80805031a058140507545580c0700240c003170002a03503403c07200c5c0790044070a01643c4000031035200300001003003800200b41000c16070700140c9600030008106600ca9042c8a803181c0960b0b00c0c0a0303d0b200340050002030b80c4000080442e4805450748a00c1e050943d20400c01080356440d41d400b0b020760391f040101008924012a1443c03001c0e2103548442c0c02e080c0c0b59100c203e240d0300310b8140140503a00c07902061007201c4020110110405d528a41404031a040795603a4440300005025100e00190302e50702042000400 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 680284577 1250 680283327 680283341
    0x40b060301061701150b0309031602060d090b04060e160b03041703180105070c08180109170109060614030a15020708120403030f1515110a141608070603020d 69
    0x4000010b1005285a03040d8001c15640c5c0c0307002c07440c004071240041e24030555070950348100c01101c040d608100d01c0c1c040c000c0d50310820010807640140e0401030380a9203036080c840c42814078041d440b40030346c914051030300c00102d501c5403010311041c0d0701c24110151110710b00407510081d034400a15081c1c0744d44591818412407076500300d8400c80800301208025040c441c4005050801c03408070000e000c2e5403074645d020703540c600e5080409030400c01c007003000740b0007180b91150160203000180f5001d00b140f0307075900c0e07a415800c000c040400b60300e9469501c0d020500405000b000068030030750325910164550000007956030b10300d42c04001e02d507124603c44850b0001d07c80d03040d540150342195000c0c0e91a00b00210341c0394606001c4908401003880c1c1194400300f46017a1007666486626192a24213050420f402d0003c1c17400d40c3c9803008104440e96404c4c416550040c050f2551480c4151105000403007421415418101c1003010b10898000c50182040342d0305000a104040f140c083c00e005a451b107000b1a800060400 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 680285827 1250 680284577 680284589
    0x90f03010603082d04091109040507030209040b0603090312101802070b01080307021003020d09150204060e030a0302030a1409210d2303070905030d020d26040b06030106 74
    0xe44507000082c40b403180002c0c4414025228469881c3c0031041c0e08a0000320030606100c41e03c81c00740000d210740703030f156840900c0b2810006505030802a0300c000040c15200122030320790010760042020b00355030500c0e0180f90340000c0b04581142c118500074124075a80d0040c078042c101c44e0313100d040110302d03075a003102d091401800310700180c0a07100d803415034202c000e5800104101d41d5508c540c000021064000700650301100e50040000904800b4514114069008805512203d0303559101200c0041c3d05413200c5914004408009a1603a00e005005085200d1040420b40130303400c0080e206000a030301008032842c0d2982030400140841c6441041070480c0603044d119500a2a01d1103402690381c0b000c4008220b110f0200c0440d00282d0f00c0900c226268000081c03421294074600c5030000c1612080009180d0041540c506040144d680d00f0010386041c203140f0560015030056290079502c160300c000919210105503945034540c07520951248140d15009001030910b103400c0020441d240e80a4000c40700800c8 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 680287077 1250 680285827 680285831
    0x809040f020702091311120c0108070e0a03240b0a0e070e06070b04211d04020c070b1e030402060d09060b12010e07080706091205030c1603030809010917090f0301 71
    0xd00311240050b0b00f1001741d0283e4208030340c8100c602107450b002c200c282810307d1000c050800b0054400c01540c045001809003000c0c03041184024249840d0448210011402040c50400014004c500b4801c2c2c80d014540801401c0d04103030007900c04ea1940f0141c201107481c0707064201420ba407170030002c85d00a0b0041903943da00000000304403050110b01078455003c0ca004840d500010b12000b50407d44050381d1002081c0803400005c1c0c8010448011a284810a44054030140ca8158180840d13402c1000c00d400030b030070100300890f001200c0d0301c0c0d04000d005160b901c0000107265080035000a0032502810440e0a182902c541c200010450030380c100d19043d00004c1d1018800010340450305028028145031800e00b842072040c0011384a030001106011250780d610703480842070505080030b00c10340c40403800341c9262104204140000c0c03030402040b83e01e04160404001031070308514004051210103046840d07268100603203440410540ca10281e00c019034080101d03502c2010101050b0313500095503400758994 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 680288327 1250 680287077 680287081
    0x501020c030f1207020109030206220c031a07020a080f0a030b120c0301291002071d0f070309031403060f0603040c0905060d03020706050d020705011d12070809040f02070209 76
    0x4040c0b4041c2c146018030f540d21003026a141343c0103d00300c5110000140041c0d00800100f0740e0a03241c400c00350501e0f640b000300d00c90140d0301620340c808e80c848c841d4000c5034114540f40080f114100301101c4240c10410901c0500f4001030341751680fa4041c0140c603614204110001000c40302540207600021031850050f007208802e07441d80d0703100384e1190500d0f49203900a500340100315100300044404640a1152101801400020302040c4031207031030484030310011b5108149020408045000160380e035030300c0020b940c82d401d00d042d000040d602140a0010418181000210700c00a0f0708500004141401c114820ba2243c0d42d0500117101000031040c4150807510010510003408505034540b410350b418054144a41c0c0c81d91400d1001c0700c04501c02c09030058201b214107000c280d2103171000b45064049404003500b82440c5840c0c4a086440080068113565046940c6001c84801442a540000c0008400318103120407a00c40e400288107101c0300d00d1165980d0300c3c0b8404448a96419114000d070050110b03002c80c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 680289577 1250 680288327 680288347
    0xf250906210e0d0311121308071502040515030106080f09030d0f06030b18060c0c011d1f060f06110109120c031b020604050603090106050411040e010e0c160501020c03 73
    0x203665003051610009085c0340204029240d0340b01107a000340c1111301c1c01402aa038081410b00c10084051080b680300c0340802041c00801ca2a5000d128a50082400140e45515100170842d005c1e041d6001024145828001000b42503000fa0806500c544a8030500c02c4594401c0c504070b00f988100308070115214a002c4049084102c580e1050013500c1c86001ca044c0e01c3d4aa100000e481382c48461b03201981b41c0d00c0301d00052100003a030340c0940b988070482400840e81d000f8441d035020444010102c10131855102c07440d40200c0f96803030740d10300d0780340036040c40100320321030800151041624150041c00240f284000e20b0800ca51825888089a241c0082200030071004010004105400d02d140540002d103072168081c1d1119604040c072030321252300800003840c1c10b1030b0009001031340c1c000810204241d5030315240060981c545010703111803042030491095545003400b00354001d052068100d030455400b071004100d040d1401e07030202c506c1005404601c10803088503103003540c003a20842800c0b5180b8000440c41c020341d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 680290827 1250 680289577 680289583
    0x30403031a100c1401020310150903060f0c031415010311040e040302030c07080705090f070c050a05060105040c050c190507031a0415020c070605031e0f250906210e 72
    0x829101340e035855407900f00e400c02c083c287d01007901ca681146236002820000c002e080c1030140f640c48100d003420706815a076901c6100c21076419020388180c19469901d00266a5418400c8005440d6045089095406d242d8a01400c000200c58407d045c10f07964450000400d041c02c2c00c6d60300170900b42c0c0b41c1c011640380a01d8001e483c0d801c10349100085100700100410251004a007000c04d030b90300a080561555a40318450400800c058074034810f014440c00004045841444821311141c0a6401007601e545401d00340001c60350180d0f0f21004103e014001404030003004503000c145e426084818070010421818520304020b4580c0c80205085c1c541c0c85581e0344440c10005044c8228095050124030701e04c1000323854140e100e0082e944045412000f014000f050103034000e1900200030300100341044a9034a040449070f40180c5800d5258200402002400b5a14200750204e00c0b4900f041000603042d0440c000d04107018500400090100c6070500c3d021646091144c4001e403624200c0a01c130240e180944152 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 680292077 1250 680290827 680290847
    0x1b0f021203070203190b1e0a0c030906020a020d0801140607201e190303051218010c020102090a0b09031f0f1d0105091902040b0a08070f0e01060e0105030403031a10 72
    0xd06d114200f000507411044c03040c81d501e01162404001040c642c0c6180c04d000040c101c1c1c0f001c2400f8503585484080224003580701400c440006500100f0b040034414034040c0a200301680304121045214142d1400f50303c9050a8454299210003006401088076007040418400114110780244c2c5440040300d00c20b0b18600e00054000b000d45c8c034484803a8200120751205030480c003015010510170030581601102210b101903004c020b0109610049400d0500a070940340c003a4200c0d80140c2d004950320105282c01c9001000500c08440c7e11440d040003900480d454407030604012002e070b1070613202c1880c1c0b20314030b803c00381c560401c2d00d40c100704a140c4591800c21040c446000031410390310340800520050f10000c0c0b1099402c106c0f1191200c0c00f001e80c1d0800000d010240c0b592034102070512400036040c0000c00c0004082c00d010511003041078205440c0d1104410b0584c030850803c0a41c0c03030781c03043c1c5c0c1e60030008683d0095098640820303220102000c141a0401040c0c94030340100c00700700c43d4100c880d0b000010038 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 680293327 1250 680292077 680292083
    0x1c09050a060e0615010f1103041701290904030e0307034e020f060109050402120d1706030c0d06020919050a091d010c09061b0f02120307020319 63
    0xd103440b00e840155960300c100c0d6a4201c1c12203c0c240d118142d13000700d420011071882490300140c0c2c0d08441d00c2076030a5403c02e45c00718511018040c2a50300c981028003501c601040350300001d140c40f0340070054001000425150842c042c1400e0b030081001d043c494010f0408000000c1d044a040b01d9032458541550030703098450403c100c00310714102004a03a448005101040d4000300c215040d414440c10510860030b1760498001d5115095290865880620086008042043c00000d01d880c043c011700c1120407040c9030046d4141c00c506032840815400c007404550b0340101501c00c00a5036a00030102e0b14040482c400c07d507012460625100400125400500c030061040c1c03420500310001070651100600180204d44d407003802d003c81071020b6507640d07000c40c900d001007140c0c100d107119190740e5450844042d0012040001e518610621500d6008529054103072044002c40408002544a40b4503410f0309600091040480208000e501c0404000303441c00d40c1d40044c103481c180f108503042c904070210442021 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 680294577 1250 680293327 680293331
    0x1a010e07030e0a110415080601030c080303070203250501140106200c0d050114040809010906141b1614031b010c080c070b0a0518100504050103021c09050a06 69
    0x210010710901919603451225070080c040c0307801071341d501c2c14184003c1c01d02540069a41190500c541c02a02d09200204060f83c05072103d541141000f896400040d0410030341c03a4003c1080c084100d60020403101140340c10f80018000d881c641039207415801c42580d024140390700b4020b00002d481003803203407a4100ea10395202c80030b00c1e03a2071040078082c2c2040a0703070040c3c00c0d8000740760340011424001007205200f441040002840842504007460b0840140d0b0191000080803500640329604045050081c04840c100800807d0030403207840d0151041100041d245601f454100c6800368081013510181d040d64103102001c240c5070300040d41070794840c1d0070451003845002a00c09070032040c41d03041412104103a4170180280c1e80c40c5c980c0100341c0c0c03020406000910440c000042c0114960300904001c0500344e40e602c1c0c1e2140c081620000055880210600c903200d881103040032560001d003240d044800a080240c2c990b40342149802010700403515580396a400c00704035100308800481c581e00154490441 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 680295827 1250 680294577 680294581
    0xa2d030b0f01110c010c1a04050f0d1704110a03060501060203130b03060105040501050310030206031e06090105010e0d140304030c08210412080903011103011d060607110d1a010e 78
    0x44403c43e000e4403e90039250441358044c04994480d03ca440880c901034808804201c50090050140300400c441c1a01c198001c1300300000d0350360b001e0000e0340600002d40362941c1000004d0048801010010704024a0308070f1509405e0071680703809450b64021500004104455a550f483c00380d01c0b0380c40107800fa4545100301d1030204100d203c0d0ba007600d000c0c02c410303501c040c102070030440150745c690300c0540b2520508850880000050307841000640c441c070241c40c140d4100002888802d140c1e000f0151469200e960140d0041c881e503603121001141d4500111b0704045244d0780360416401142d080c00310090395000005002c4140401d0005210448402c001258030b42019100d4680c24013140c48030310103940754104001c00901c880400c040e200c0c503015001242ca05040c8500003402c40302075441c2d07401d04541c040f004024214002507541581002042000b14a01e090310014025206401000380750a12031041407403d83c8a407500c00d940c80d5840b034052111444003481c0c42d0040042481440055510080 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 680297077 1250 680295827 680295829
    0x5070e01020f07092d0b01090b030402091b090901140102150f0403051e0a0e0f03031206090702150a060e0703020c0a2d0b0105120a02060a2d030b0f 65
    0xc560300300c001d90801810103241000b030303c600940072985d540242d4004000d86010070099000e00002c40d064505070014100079001c0014001c000c5d994004c071428402031041001684a1403a0107510030303504400c03186014242500c1c03c20034021503180c940c000212100104c2c5404448400c200400001d800318ac0c64616040104400e901007256070007520b903030020103e40041d002e82e020301120100d6100c80007648803070240c54442c0303800c000d01000020703d151400030034034180322201d0074406e0800d9010758984180c80b2100c5005040c05000180201e000e0b100241c061071090049801c000003070701d024001070601d208024040c00d441d001d0030301c04080140200d00d41900910880740d600749500090218080152079862204e421103488007040d46219410714540610050300343c1080e8861211078086506010510001d8070065104034039607400304d6032010140e90384605450310f101540c64100d618100ca0050404805510101c00803500b01007010005901d8043d0803030303591000300741c410300001e090800c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 680298327 1250 680297077 680297083
    0x71109011a070501110d05100b04121b050901061214070f03050709050907021b09101505041505190e01050a030c0c0203030a02010b01080c070b01060e0d0b01030605070e0102 76
    0x200c142800c1c0c03a0300c0700481014010640c0074040083c0100f000043c1400c0c0d050302c6200640c001843d80444a0b41ea03410041c9142d80b1051540c060b0034081000d6003003a04111452106184a5002602c030004c2c98200398200104003500300041d0a002c1c1480c2c01c156900c0d100608080d030035200d040d041a04003280c20030800f01a41210f0b2064006aa5500d4684400141a00102400342005040103850180401c264440d00101c60191500f035000301030800c3e02c0c003240b500c040c2d0481001c600c5001d00364280131300c3d100c00c1c00342002562020400e00d08440d10300c503c01d980501c00c5900210868103044407455405800c080503200c0700004030244c000100c4014012507812100c0240d06021440911000100c2071103a4056804c0c05000e041408201040c3d800003460f60300494905030040c0e4685003880a207592040501d0380004000281c241803a507642e880c40c101610502440080003600b6013190740941c0e40c0668880501e42054583c0c0c0e403561213040c044061b14088030003d020981034542a2a130794800 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 680299577 1250 680298327 680298329
    0xb040b1b03070e03030d060305070f0e090a2910030b0a020304030206040b0702150a0e1203040c060c1106030f16020c0a0311010905130c021e03030a15081207110901 72
    0xc2602186942e6451005036101030001d28400d806100c10f10140040400b68031681001d580240c00a000c298504508050101600d800098500803410705008140740b0010381c079200c0d55400303901400000d0145000340c012506da034407100300a00c5030400344050440703503803107140030780b80074800c40c03541c90b40c80301c00c2c030300076848280c0780100103a201c94000340c04100b00003082e40e001229841070303800d19620210082c08440d425105d0808165581c21003a0b04580c080022840d2111012002c07803d40c5023944821003410442d100b42418403011004403410000803c5034400940001001684c890502c0003102442180407a00d40c0d00b80000716002d90741342400014072080081c8014141242079003141c0e1070309100d144d0782154a041c040d940c440850f1075034030f540c0c5c0c0307100042100c080000c002100320030007854540c3c3c620071900c0304d00400d031264000c1c441c04021240e000003000300108505460117817080700304269510504444c06250020911100102c00412209000b0540e00502d02d05c5442081900721003 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 680300827 1250 680299577 680299621
    0x13031d0609040504020f0a03031718030a030504051c0c110105030112230102120a050c03010e18070807080a020a0512060103030f0e1e19140402250b040b 67
    0x4140706000c402e103000e81100b0f603c5480a41074020500300c080c081150580d440e0411000f01e100c03403c000c203110410800c1c1c103510040e500c001400603290400f000d62240f2400ba40c036000c258a640028044c08410001c80f414806081190010741340c5030400102143c11a03041110351402c0a0300c1840c41c0e43c8908250782c182c1d41c130b120004040351003640c2d500282c001d0710440000c0e40003130340d1003500e03d0103000c2c8040e104810702480480302c140341500841c000c4490080c10301d0300300041400144a00c0c5a030010711a4002008100c010784c0c0c84111544510b0165141d002040324411942c01007502c0801003100c2400500c00c3d1080008651114200103950725500500c00380ba9012200400c0401e105002c04502000c90741005004118a40049403101040780900801c0860070105a015814541a900e40d060705026104005031b040c02c02d11005001050782c0c051060350042075103250084900010344035403007580c10410403030600340381080c0c01050071a415212240d2520010f0720040d184410a082004 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 680302077 1250 680300827 680300839
    0x40c0207080705041503020a0f15030c05030c0304050a0f2a12080f12010807030b01060c0f02012a0b06030d2316060e07050306060a08120f1213031d 65
    0x20510f0300340f000805003062880c4424080390310000150b2500b0324038202a203d100a030081040c200b17016010000e500e0103c0300200b61400503a500c129034410103030394103c81940000d40c2d480c3c40d20300381645407500e6040043d040914038401d520401c40c0ca200f241c640821200c042c82c22070750900030120662400c61007400041c200708150070000451507070003080004045045a0b042640303c8460010b4510300741c00803611680100010b1040c040380c401c1e11801060307249010401294180d403105262244481c0081c1070061030500c034110780400002000041c3c0710b4100f092140642c50410725075100c3c003503032614028000c950840713070383d6407150010402650119418809001c402500c2c0b50807540000d0010b846280364040d07110020754280610040c4a241700000e081140c10320081504000380600468810111460f080002031804a2245540000400c51680703e1160300c41e9064a031094100d04c0d02405804000c10007800b00300801c0d5454039009036a404c0c2d5000e03a03a06224081021000d1140d4048 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 680303327 1250 680302077 680302079
    0xb0c09210c120a020135010f0302030c0f010c0b0705040b0a020102030103140c100e010e060406020f1216030309020d020306070807020d0801060806060a0201091e02040510060903120306050d11040c02070807 90
    0x10741c2ca981c2d1400e46d031001090034201d030b502d003800002d03101c400c5c1c1103800c0b1a0a88441001949010005559601012a4142211004a00080c15100661200500e0ba454a00000d072905000301c00350303401044495941941c03002804002070007988240011642c105914803c0481c1c100001004580f501300541113000e40c40040030700359540740d400e140725410804288225001520f0f4040a44000d0016400400f07800403441c0e03c2c5402c1408903401ea01d42c03800f0501648802d4400c00204038035040d0981070014103500300d4008217002031842e80010f5007500c180d20a0180325540301c00018400d14090b4280c0d0014004140e0803a440c0300203116201c001000030000c21031a1500000504140f8500d000018901003282e40304180c1a82038007a43e6100303a1078644400079410140500c07680310107030b001001000384c28200f0281c170742c603054000500800000281c0d248118029888103018000041c54800c10800074078100340141e0040f8680e90040d4100240303141a1400010304005480c01040906506 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 680304577 1250 680303327 680303357
    0x10510081b1c11030709090b060d0302072108040308130909080702010f0e120d0e0d1509150213092a230c0703030e09040b0c09210c120a0201 62
    0xc001654281c9041c0d20350030f1050101e40d410848030b0000d1031a140085000112810450040b1900030007060043d0182c0c0e04290000f9400705101003592039034010700c051107103e9900f0040390a5131001c010540318001170080181310004000c2e1a1a041c04e440408030151214044410384101030001030903910240b20101c019805000c403040f0301541807034561800224a0002640c5840300400c4a14036000044d003069015480030500034030319400d564000940c042540c55001003043d90300503208081e600e00c462020465009020b14a2102d0844150f4441001c00d111000300100340c802c0e0002d26103081c0d4481200607443d8034500c1000d500c1d042d00007988000741003d4a41c480c0c0c0501c0c0701c01c1d02c0f00382d8039201001c0180c1c001170242e40386100d0003440e00a040d072602412402540902da445995101c00700000511001d210701c0d0302c001c05101541c1c940d1102c40c082110b1070141031020f003038901280364202e0348400005515000d100129185962811005c2d5115120010203078041e0018211000401d42 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 680305827 1250 680304577 680304619
    0xe0c0304031101091214092202130608010e0a09050c01120b0402070c0e0106030603080a0302090321120c0405030d0c050307021503040b070302180d14010510081b 71
    0x100c03600a04001915031800710310b29003103d440d010115203045030300c0c82c548181da501c81a403043c002c5882603613170324200340361000800091506000254805414100001220141c1c05491803849050500391607952034030300181444200b4001c1c20804030718038001480703051036401456070b4241c1010152910060070001125a560f640829602041d19105040082d88942c40106a024020385101d01303c14100241506c5011060340420109400c1030414000b10300c0e40d004403600c8900301c5c00c2c01a030b103080c0d0030003103401e1842e8603080c41101c1d40748507100300b544a04003000304804001080107030300540d10700150040f680a84d0145940540c05000010042c1d40500401074038203000e5000c581c100141c0d82c0c005040345801d8141d416203040048140020000f4815025400180c1824290309010303031414642030007106548070b1840380244026180c14000e030b00c0395003600d50710395100a00003071400742c1c0c01282d881098820b05d19544500c400c1395074000c1501383c043d4500c900042a801c1d000f4184151014 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 680307077 1250 680305827 680305831
    0x10b01021207120c170c01180c0519031b050103150806220b040309030308130203150a2414011103090402091201020c0c09130203120c070b0301031a0c040e0c03 70
    0x824001c081c0313201004a03089000b8000c0c0850703a031076010f903101c4041a0050940d800d100c03095100805103860000000c0914083d2000c2d685c066910000b0b404134800003100009040d40090f00491041c0c1d80001c2d043c903032a0b144002e4440a880900c510300d010720008010921f00e103e80700d16030304043c0220f0a076405540b0920308c406180e015401d002080c1e600e4448800c0f41c103440807004030344040320400406400051681d81300001e5007074604500540d0b00800d44801342c041403a9200d03111880010701c0004079910040303140c0c1c0c2c1c04041b04503100c070b503220080300302d8454000e665091748800d41038502584904243d5846200c654095407c01840105000c0a5085486a00d038080260558200c4411003440900a40b006600040480069210502580c1342000d00000412030340d8400300350142e140040c44100004082c1c00d039607038031580301c454281060a181c10984040800000010a100840070008074034141c905440240c1d403101100341d41c00e4400e034844e28540307210110004106000e40c401442e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 680308327 1250 680307077 680307113
    0xb150405060d0c150e040e0703110108100308210a1517070509060103020421031e0c02010c0206041502210a081b0f03040b09281e0503040611010b01021207 68
    0x45d2903d14050004051340c09030704480b09150b1101c6800c005119041215401c203403001e00307140d05141004142c9004140090201411040001503003100400728010358181003071014146030510b08203202e0000c0904500101100310100c1002c001c07914155106207016850540030080c2141490001030103600e01d00280002c0c141030342404000f4026450030031031880101411000349164070745281c064100302803011000d0480344c4d00300b600c00780240c0000c200e6400540900302840000c038a440000c0d2144030741d40045c450301040000c4109003c0d0001030308841e00c4d440c40f101001c0c081000a8641180c01101049400501001e01140320034980a1180070307030448a549017854030a080c03d040103603620a0350100d8411580b14204040d002003400542441e00c64400506400c17140310b403400a160074624005021010300c030301c2141541e400da4002c0d003941644203061b0707a242d5a0303d86001d0042d100009410085500f4641950460761000c40c5100d40800040310003414540c0030307110b019005441c1c003001 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 680309577 1250 680308327 680308337
    0x10c021201092f0109030b060d12020703150912050a030603080f030103150605060d0f0b0904050d0f02070f0303030c050d0516020c0406260a0b150405060d0c15 70
    0x801040c402809142d082c2801164045924499100050040c0d204408012850710748412040b115030ba0105c1d40008a0fa0040301c40040313a01c0b103a0001d070b1130001b03503500140b00038840d00f101900c4540118010b41164020101004454210501d00b010b86a011100030510a00031100b0042e06d409100500352100340d500d00042c1aa89170381c0c80503240da01c9940c41440d46003004c001002008810020320740580781c44d08081c0301c1246010003103100c0d4084e0444081c1c000c1e031917122a000900f00e690000483c3e500003001580c0a082c581856510707034045614503400910f0001c141f100703903070002a960080b2030442d06981c6000345903841c124001c042400918041200401c003500d101201c5000b22400307002da0784240d1075410322001010303243c407650b0b03003c0034010b40c203280c810000004489881040403089031001e40c40b81203100d5440d41030205000340186080000d90910650900c240c0c2c500c122000207032000c10040d100c41c410000d04000d00d00d0000c1250780400003d1001d056005401d9420303600e50b00744 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 680310827 1250 680309577 680309599
    0xc0506070f0812041401140106082a0a03150602030703050d1b080612070e01050f150a08090c120d0c02030c060403060203040c050d031202030705040512160806090a02010c02 76
    0x60b2030070342c2d0700c0741c41d4000f110a814000c0c003007401910355902c0e482401031002000020f000394034000c9066014400c00c814805e031388000a540d8007500181e00a1100c0d486004070041902045072045a000384402d03500084c940f4007096604540180c001d0140e41c5182c005500b0310a455604540581c0481038603012281c4903c0300840c0c014054000303001d285542c0c1c40780a407030b00d004414001c44d00c3c1d041c012a1142d5010301000c210b00480d0380c92644c1943c40035980b240b1500080004508102d0781080880144080052401703005d56004c0002401000c01006490780d40050400300108154989179a400c590001101001254003071032038200d40501c050291a103001d0f0b04000a4440d4102e5071003542d5440e000410401000041c0f19401c016040c00c8600704803601040d2401001203200030200d0f850b596000000c1034035940180c050f20300512005044c07100c1940c400c84960344500341074800e1722070003000031000303d604031300400d10071301c2510060000c0001103401e800441d080350310710700103903000903046030 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 680312077 1250 680310827 680310833
    0xa09061e02030a0e07120209060d050f0a1101030b010f05071a130b09010c020601271805060603060c1903060e1e0705031009050901020c07030303150b0301030c0506070f 74
    0x5105560301008a00140c8900d0421000c0c02038481c84070061400c0e4001010500000081d10020015503405480e0f4030b060b540d808022514450442c3c0001d4050311465480600401c00082c004140a03c100b01407503512024400540030390b0120444c5a001c140c1c01c0c00c80c2549140305034041e0520700d0140781c4414401c4035409400e44009401d60744402801d800d00090000d104c0503c0784190442c100c02300801040c6d0f2030301d40c025152001806400440103c8070b5920400c0c5404903520000700b2545007007000304003000d1803603048407a1940c80460b40f5008410010342d15290200f03049110b050b00318846440c20040c141e0b988018050580400c00b4581d60b4540440c22460b5110f42340c0c440c0c001804108280d04100f501a405110020164410007408004100443c00c2004080003292108032010615031208411980a0b004203680070002c0e00c541c1d0800400d041e40741d0031050365030031601c64001c02035841e64481a01403200f400040c08c000c0f1020010001d90610030b0041c204280a412509540c45080e5 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 680313327 1250 680312077 680312111
    0x30c0603021236010510140901120f050f060a110a0e10091d0a06050d110d0c2c0a020a170907050607060c030506060a020c0d03020309150301140105070201080a0906 72
    0x424103043c141c0d503a100300001c2a2090a000d0050480e810707100f82001c3c01c20b00000d6240b08140140d000b01c0600150003010040054204c440199011064a46068441c840540d98920488484502b941440600d45402d120b000840b01c0da22a565126900300000c0350a100b0038507501d0702140d0400c005041c0000e100740703920b280c10000c480e800004041c036040916444080d10080d80280e0700c100d000042c0f400025807512290381c0800ca060b01e41d40c2004910f41440c0c00c5070481ca910003c024240c42e03c5491202030042010007100d101000c6100003078880b034002c0001c80c00380c040980041108080c00c402551030540702a07610004040c216840d0585031800314141f50403c5204a42884e142e032240c40240d6014016103500c14419660942000c40810000790b4644480d041d050060000e8141202454800d0040380d40541d0041d00905c40c40c0313000d9440035840d90003442070400c0c4254419800b651517104808440b03a190f0145e55240c0c060326044414402800c0482c42250003da4603608001940081 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 680314577 1250 680313327 680313421
    0xd08070c320c180f0112150e03091206010f05121c11010522060b0409200411070209070f0c0507060309051902060a03020c030903030d06030c06030212 66
    0x407005400040c85060a0007214440c50204614022240c03041240311486a08243d0446803540001c480d080414244840c000b0004884000441e04001d0b60700381181300000148181c0d0800c0c1c2d0f003400034030003800069858040030701079800c40102107182000b440c500340c5245c1891000c480140c80140c0c0c460204030100070a1128030101140022030700d000e26003020320a00c1e034040c41203e01008105092818109a421024401044143e0350306034807035240c890707502c07000500d5804900800420b00d01155260341e140801381c81441181801220701c48544a001625101030780074041c0ba020391100e5000341c0f413540803011041e0400118090400210f00e081203005d00500c4251800100c2d04807904101d401d15164100040c080f041203e94070300144c90b010700f01c03458401d0500d80141c6520b5040000d50451045419003581340c440843d04c0f40300320303490750b1081003102d01c1a0f12589506a907050268281d000d50300171208000d0000000507428984020702c010440b12280c0c400880c2c4121001034000d032515 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 680315827 1250 680314577 680314673
    0x906040e180d1716020c09070306090b0406080309010e1804240b0312180904060506040b1008150d050a060609060501090302030c0d061d0f0d08070c 65
    0x110128241d0381e4003031050034510300062500074111040007000b801c5402d00640702d440701c0720030b106204103800d10038400100d11480007001d1448908043d24020040d14860261003581894002d030000c90303182601c0341200300d99010014600b000c01d41c10040d501300600d42c08254000e001000c9074501c107442c5ca44007620a074807030304c18000e1010540e006445140348003060340307a20a281051b0084070356400140110500440c00086075604412154040070380c0c40b20011b107800040243c140010007920360400d034032981041d6030411580c40c0b040104013507018805166000314040368040b031120000c003d81036251580181146002007d00e03641c01d460002c92880c1520001d56840042c8418030305409143c005040910304030740c01e1801e68000079100c0300321400203440307004400c03030344002c012450300241000710b6000c8103030b591355070051000b070785503080c0b040005a240180c24010150601038404140150394569442d0760207070b650343c1c80d107140101c01d12903050b01c07200e402c6c1900740d0804a101031b0220100 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 680317077 1250 680315827 680315851
    0x5090a08042409050105030a0f020c07030501020903060702010b01140a091203030c020c0a050303121504020a0c0632040302101802010905060a0e010c06110403060203060909070e010b0906040e 84
    0x10703422020000d42d61000581c002000301c640010400da07a400320a6a81144d0100350000701005140001d01c0244541d0384442914054603034004140413064bc0034001c5413605030305803800f90342c401000301c1c00c07160051000c501052129991500c0071000700c01074007080c081e90420032081e0340c582d1610001d49051410850000703841b50241c0c01030036814031500c051f001c003c1e116100d186080c0340c006a22030249201040821061400054080040001050b08044060070441d6a00c559043c01032104500c86c01c207039415401d0200d00c8031100c0301404103041c19090654940041c503020194504101d0025009800710702c07070b02581c9200030000d44222505282c20dd45040c80d16041403002400504990b4070052240c00103020b1055201c4d0009001c2c8242082440d2108580b8030500e8448001c01c4410181d00d007441010602008120040d8020750180b001143e25011b10387d03c0111480c2c0d100d020703000d10310340400d07080010010004118080c08980d1402002e4500385500c174101e0320740941e811204a12a51 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 680318327 1250 680317077 680317109
    0x3180b03012105060a0917120906010806100509130c15090b0c030711030a0b0a1415010e01051c0f06090c050c0a0210090306020307030c0f090f030605090a0804 70
    0x346010300440903801102d184044034030310380d8880e5030300c40c400108624003060f190000c1d2801c001105404400940100c01d545403031321803202020454000c1110405020700c910f0001148003d00003481500c80c80d104c10900407054148010b001c80c0e00c00140100c500b0840001c1000c0002c0c1100c400c040103441c401c0c480d08600d202c60440141148440d03800901a82010060034031046000b0081f283c2e90380c0c010301c4500b441e81a80e40440e02c2d01e0b1859401401d6092000d05020101095421446104a8900d01c040840d180c85440c04514008900818040b0b06800e8440b10154080c001500c81c07444020f4400d45c40c0d00e8443c001300142c501c907240c203801e103a0784e80409019012007445008106503107840d00509100007000525910811001c020740303c1c2d20512819035243d8400c1d000c420285030b0156013551282410700c40070f4043c1a01c52440000f060107c1400c4411505c5002c0c04800c5a440e40390b000aa82c0c51a200c1100a010180840c1100d000712082c910100f40d045001b08018101020810816 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 680319577 1250 680318327 680318339
    0xc05100c05040b160318060516050a08030a050a1a01050d0e07050402120402030d141b0c040603050d090501111e0304050d0b070e0609210124051503010602071203180b0301 75
    0x1c10b2880390410881c2c083c8020700c01c1642c4230058402040e07002c1d17105403207180603090651030310503155070040100c9400810840901d150b50445030140060b0f50040c828050810000542c9109403140079002030014000303451900819001764464044440640303040c5921400420140e03441090f122121404007818401181801c001e541e0310001c7c40c0c07405094461500d140000c4500c14419022942d07040034800404075a02030111800d2244010000c01c80d150743c910b4805d4076441d0000381710011504600000400d94000d2805501800d103040c050440c460085043c1c04003901084c3c098203142c4414080418240c560040c90700d03046008900030f403ca41717480c0034000c00c2d10410408840c022541805034036000d44032400f40901181c40e48020960001000032507a00415a4a0b0101c030200b2600741828400300d0b402a002d805e561083e2010f0046000b54070048019100a00c00c040040e0700904c410892101d82e800d00100c1c0d40e100303103041c80b1130580c0803000d69542451500115407006001004200e0317 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 680320827 1250 680319577 680319587
    0xf09120e0a150f120507050712090b0d0902090601030b010207050d0f0206030705040e0c042103033e0301030512030711070b0d06060e09071805150d0c0c05100c05040b1603 75
    0x51040c13403040c040340c60309074401032240c098540000e01e10101c4c030241c00290b0b07009105910141500c0091a0b031252200d480c020b000c0c04d0307504000ea0280001c0404034a442d4071038010346201a1068005010451a100c00d21881801c034540a41c2c01049030b0820b0401a5100c07401107004005654556499908150001202d0000901000a400b10400040001d40c03504c181e0746100e41541800e070f186d03020060500b680070708561340301001d1200740c0201c02003200700b03207040381d207002c0303010001c3d40100ca21126002e00c0e2500c801c0c0000ba0660f070090586c1500c59080c80c00843d403192947c0340100f614081e480583d850000c1c1c42e0010300d130070312000c6514204103089104120080c401850201c1c011203080c070105802c050080e01082c1003040e8034030900b8071220550380c800700601e4064001035120040d03000303440454101d100d908418600341014411032a2207000024500c0e90040050b00032804000d4808000700744580c520002c2c814103000002d00c0101030b8000d44035401580d540b001c19040a4039000704 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 680322077 1250 680320827 680320847
    0x2301090509070609031b1d041106090d080906090d030e190b09130b18040c050402070b011e05040e0d110d0f03020c07030221010f09120e0a150f 63
    0xa0303000b10010040075500c0184441180c0d00180b00707480d220f40350015000074001d2074000b40c50006401803500f0a40241a030712038482c034024000800003800010801000784a90a60b1560003845e000d8520003050300c290091401200003010b0740d04e881100408500d810600c07810980124074000401142c50600c11b403c02040010f1128080d000c41c100240c0c9840b40c0124086140540c00f9101086103c01045d4440c4104210042500444100c6040312142d610030444080314100c041c01000180d6083c030340242c07007400c4d41c40f1280c8079240c0e080400b030b00100030181c2e941c1d03002406840800a0103882d02e2040d142c0750782e1703601d0140032000d4213120090141035948003034000b19071000505080282c3d1010b881c00400a2514016a40d030007900d000030f1415449820181d40490b500c03903040c808400342080f0003081c8060707038004d0041c0c140c441121812110030303c00c0500054010707421140c03110300c00d29210041000040180ca20141c44405942d1844108510340c07000c601c03880b5071020403e4009007488 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 680323327 1250 680322077 680322091
    0x1e1e0c2116020d0518010c02190618050609010f0e04050f1609080d0f111005040c0602070b0711031009080903010b090907030f030225030309050105030f0f0a23010905 73
    0x291001e1400404d03038401c4822011074070584403400c59030703a0300c03c0400e031810a8005010312981600c0400d04181d2414030b12a5002081810905007442481071140c07600312000107010a04019102c1c006686c24015650400e041009440b100c1580d80c2d1036214990180421000c11906407600c3c85840c1c006c000d6280070107045c00341003901041130923400500c05640041034600407101d690b0782c0e14291900c42e2090600821400f034a41c0011200003550f00451045008085440c00199121403c2c1d844200c01e00442113000720400200d030201c0e00510201e401050003500321800231002003043c4044800b101c45c100c91403807001580c41c205160900886100e1001127500500da0f080c080e101c0d03580c50441d48001020b02d042c41300040103241c020702ca9000d023207100aa501c20389005140d100051084180001c0f03020503c42c00020615501c1881034070b02c41e407407042c540421034441c80d1000c4980e080c014004a00c254641d0090036500d441c015513541034008440300c81c0600e50404003886e00f0b4500c020008 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 680324577 1250 680323327 680323333
    0x816030905060109110d0207060e390d0209040c0f0f0f0509070314100801150503031b010b0301020a03020d0c030b010210020904090b0702061e1e0c211602 68
    0x41000c103402084160440b80d01240c0002d040d105a18400c5c4540100310711610160300c00f2940b00305000c0150010066200b1038010b0b030b841d502c41015681000603142ca5004094529002829203890b903024900c0c000c040001c200c14581e503050780c0006c01c071075011a8100c40d0480c03050020032106080f0003091020303001030350840c0003042c240341d41d5000e0303122144521340c030070a2014007141c3c8c110301962080c8580c034400080c03092a4541014840c1032841c4902c0b031020700d90710748401c440c02d2080203d6401c0c01d940b0001d01540c0303881111000d40f170f0b400038008100360b2195617a000441d4690b03000d1000380100c500d251809611445907045d410b00f22180e5102070302c1854140700380215a03a038041100f40300448003100040c0c80d03042d00e001250041007846401400100b91106000005400040f001d02c200304288190881004481c1001c0800704140c0e222022846a1041c200c03030140c0c0f10036500e900c01c2c0310180c81c9017004110500394000c2c541642021070954007046c18805803220120240341c16130418002 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 680325827 1250 680324577 680324591
    0x20309060a140c030403030f12151403070906180e060f060108150a0308071401092f03030403210f0912140a03080604180b010e0613020406081603 64
    0x499800e00c16044007000304445142182140840c6005441c030b40040882102d0325035449140180001c202c070b111210118180700300c01e804603606d901864205c2203174225008c15662030040035100014443c070740240d15024010020403085420300c60307840100b03c450039112a4002e1680d462080b18603440c1501100d4000034100180e081400b00300540000c0d003840d01c07841558800b6092445800088030301d0340c0c414103440c4000144481d030b0026080490150344c41c803062500900070507088864104e0300820b032507100b940d00544001360320081415441300b58201c0b0114807545000a095034010f8000700d81504410f520b4880039030840021484e201c40b2401c0084003030100a1014001121502c1440800d04070510080b00300801e208010b0307608238001044922a00ca50707c3e025141d1034080310f4850203246000604803004000842d40124070707800c503094080c243d0814403440d40326040140f0158000030070401090400c0240d10042004001680c1d518449003031100c901e40081101d02000c508050800031 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 680327077 1250 680325827 680325829
    0x1e050f0618100b07150207050304060e03060405060604051017060703150f12020d0206030a0905100b13052203020604030f0302030c0904090c09062715120f0803040614010501020309 79
    0x1c0000151544190314948903100e038034107595440b5000a1445045e030000c2a170400700711001024001f560340c01d4603006c23610f040000600d03a4500e0100d4000d429a88690086192800c00381d1125800840c4500c460ba8030320345440001c40c088685452812195010000f00600366134188642c84410402903c0898050316148881e214080540100030712350065040140c1150741c4e402205154540c007402c091780b2403030480f00342c40060107140b005131094094500910310400d640e00c100302080000810651000305d070250f03454001c003001001c8113030f0b00e10781045030074650120815601e810380c880d46c000c1100e031416140003080c682d00311510400f890f0051060007280000c90742907034007440e41580d002540d02800e0030160340003002d59018501551030300f100803511005031740c10150200c1c25009604010916011140200c81c0043d02440c100d034804041070205481c2240b58403081030180d5880143e6041648824150360300c140c404030707003ea65503c44058518606200d1034010b1030b003400914108100c101c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 680328327 1250 680327077 680327101
    0x109030b071413060e151c0e01090503030112030e01080f0f0a0f050c0d0b0a0e06120a12030605010206070804050d2109050604021302030c0d1e050f0618 67
    0x40c1041d82406944622420169100825101811029016100c0a9588032000360112202c1d85c1d50600500d94030b6100030440c400d05040751221101d081c4c001003150403800d00d0301d00070070030429000c182e9500d600c55480800c0003040698080d003035030040070221543c42c3c0742c003900d01ca1854100a0501465104221540c6002c07401154061070020344a6402d9507a14080c00c010070080d4600200f8619003c14014805030707032005010200071940c01001001c6510080050300c0b0810b01c00d12421641410016020f0b0800228068148104108440c9010403940d1654140c000750f03051600001e54440d410096980c2c10441160402c07054204105282855120705444800100303c81c020b1040552401c099a5060001300c00c03102d102003c00c00c564041454800c0e151081520183e110b800704414047d0480c2d0540700b240d020751118007610780340c010345a00610241042c0e0518000803111288451004001800b03140d11800310b010074a881c40c58000304200700d40032010401c1c407a6241d05400c126602500c1 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 680329577 1250 680328327 680328331
    0x6030c08090f1c020316051c020f0309010c0804080106030615090203191a03030403080a02070f081515040e010c11190209060f131a040e0a0204090c23030c0109030b 72
    0x9008003107000101080d044e071451103515003c00c0c4031044001d0003000e001000c103007045030204007030209540000c0940c3c200d9842c0914152140035030400c00c514800356014800003142c1d507202e030310f00e11308180d501e103002400c440d001da00644484da101d03245000c0e1640036078035100141041c0389086003541000030b03014006c0b81103420340711000e80d601c2c4004040c0b002198081c034014080101160345d15a1649000c1c8100c0d0040d0341136201501c02c521001c228581828003c1c0281c559450003441500c0200506120064026120007440031030300358105d0554032140550504e150f920300000c0b030045007020700180080b06a0688200342d0300540c0f0040b41d9640015601502d42d901142c503140141c0312680041c0340ca0044502c59544a400c291208600360003581000d41c3c1c64004161003a00c1000190900c0203480d80410720001e940c00c0502504018038199003d8007940d80a440000c1c50aa2101c100444c0d07042140d1a02e9056008403030203c0203894200540c4040781004c0c03134210303021469695031903240000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 680330827 1250 680329577 680329603
    0x270614012102040f0c033e031504050403020a0218190b040608010e0d0801080303010e0406151505040806103b07081806040c1401020a0503030106030c08090f 69
    0x6140c80c01c02595141e411540001d1a40b2008004540d00c011003d03008000500c004107020a440310544070310360081006071b200c1c0b0005180a92002490051920a944000c0a40d8244006c2e48400c400b1600d0302d1081c140702e184683c00514408809004108001088081d5010504907005c1000001c5110455040800d28428004a00c2c01101c100140103000c160300118540d620f8a455224841c5001030304a030042095221148242d0721140c406460b1720003400344a40050300c4001040016400c0e60042c0e2250740410240d4900a803511810401d50111100400010350049000d01c207041040c800325030000c00050358100e000b803824001c0f000c0003a048956013000042e074081c43c280b040f0b0200ca1002c440d611003080200da880d2400010700b60710300a0300c42100c1d004103010071040d1000001442409a900100542d0040d07103842c850b2050b2039400506503045010303845202001074803c0001d1030207803089450120391308a483e1001480c00c04014510f440b10362090269160717182020924a408000c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 680332077 1250 680330827 680330879
    0xb0d0207080403050d170a0b0f011d090a06141c2a030803040b01080f0a12020316060b030c010f09030308070306031211060901060e0c07050127061401 66
    0x400d6080c152410b009941c0302400d10f01038110040010b80c3c3c403500d5810603142d01045078042d629180f1006046400d0030080d02c5c0c01c02e01800e02c101d020360040b20381e0b4500d0482030544d4110344011174042801076805485001c2616185d0b08144802001c0d1103100960a070240e0320490760a14924014096640b880c1d40a03181c03503400d9440e2620440720050950744036400e0740d09901300e503643c0d2600c1d0003194011a41178618003440000030480d020080780c059003484515008000c042003603125480e603074540001d4541588400c112a54991302a05102c0c00c0c4503004200014106020390300b4103003000a020700b842d04110103c8061505150050060360540307402d0718103203480e82c0c0d0300b86041d0010481e940016210a40d040ac20bc00143e034003201c0d0007040c071500c01c10307240d02e0380360b09002d1800c0e1415401030340c05041040000a001c58a408090070f03415001c0c00000c5264800805000d0030744c689100c40d1151407141c090b00000f404118024071540c10408451144107614201a002c80c04000600c0510600c0c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 680333327 1250 680332077 680332087
    0x1031d0a060903090b040b040e1b1b0c19090e0309090a0c0309020d0b190b0607020d020301021209070f060c0c0509041403030a0605190e0103020919181b0b0d02 70
    0x521442e0134030f0103086000a500d5495441ea0040f44141d08548a05002c0302e8005000901110b90103045120181120b4030660401c100b02c03011001903090100300d00261301c01d801102c18a0f540b21407000c6480868441440851030801409d41c3c240c5d070516200e09543c0d8406c01108d41039403070b52487e1550050340c00e04002100141740c2d00c114094148220041d5100900b00709100c180038070b44018030f004132280c4004104445a0050b1a019122038a00d610303481130040c4034000142c2803034070308104158030090006150520701c01c2c0c00340e5015800d581000c07165000810901c0750012091160000d0442d908041c19034202d203032b45803c070704840d500809000b041c120011034100b1043c181d60221400042086d2500c82c9401d080c00c400910780ba108031486a001110524024403450f050705c3d003581c151040c507030202c0e820758083c007400e401e01401d02c070b03507280f201d1850f2840c0c641070b4032402c204903006100e854142c002c581003921914010304940c403080300e00c000d001c011035003220080303030025070361031801503110 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 680334577 1250 680333327 680333333
    0x3041710050f220213050925050f0a0f030507050a06020a0803060d03020c1035040f0f06110a030e0309091605040f0f09110a090911091c0201031d0a0609 67
    0x1c6403180d00080d0015185d0690f4003010305070b900528030998281c01118040300700c44041d4920040c0038640303980112600300b03003884175042c01400b421200fa409007410340313a83d5a0303075200403800d5141d500903141074207d1030007030244d480c01c404050020701080c0b000f4601480103460790906403102034001c92045e02d03030b9566102014021301450810710001021408484140d1401031f0811480b00354940040249208104404002101f0019010307900c0e035900c02c4c20740d201c1c1d8032060380c3c4c0d90111058885c0c0d0040001d51000a410340118900c000c40d4403c0151200c81000003c0d0595208846011094206102d00c84143d00d0f0400d142d5071002c020200c1c44a09500d00d0f9042e113070741c444e0360071a50300c1009020f80424682e00004205040b100090404c128ad03480e03480018296014840c4414000b030100301c0c00304240c80070750300325104081c14001158034110030540090382c0803c541d41c0344410f540754000030005541e00b42c0b0803c0c885840e000900034844070311500f402d441d01c0a240300281250380d150908414 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 680335827 1250 680334577 680334631
    0x1508030f090f12030c060907050a0e0c0f090a0609030303180807022b03080402030c0301060b0a1112030a05040b251107080f070e01150e130e03041710050f 68
    0x4881460059070745c0e80c108803c5141d01d520007280ca1003980d206406001603942840c0040304100d450b10050003443e9150320b4804c8036940e1026120001c081310078020fa00032a510b50909000030996070b00c50b10301d440d26600d805400d403a4600032013800e1070f0043c00050003003080c40040340c040c0c95048070710215550401d846506001112048126400e8446d41c09208064202441c5401580210100c40055203020109802d0b62054022000000c0081c4240780e403060151140301e07400c030794010136a008440e10301e80d152404c5d00226a4150000e46810a00041c4030181e40456003100014050f0410b10000e1482485403074600d901c81000c0000c1c4646002841805201da40301a004007800d945041c9035030800b20307540f0a1580900084002e0140c00020303442c3c1c6042d2a034101e40201c2e01c034084001c40c92b90400400442420030326801d551140101e0300412800e000400c0a4003110102c641201c1154680301d10b40024101d8250341c03545001c0a00c100c5d5000c0f41400d40d03001c00c42082d180c203000704100d42560 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 680337077 1250 680335827 680335849
    0x30f020c060d0c0306170109061a06120c0403050607120f060509071202090604060f080a050708071b0b01270225051002030408030402100e0f151308011508030f090f 72
    0x1e0840124101c0006c40406400c5040401e01540003400342641c2092200303800f2010fa000c031640480d00304090910041e03040e490341c0d4031071003140070316042a503039844160405000310790050000b01e40b005e07611b25691082c4200407080610307035020001c0034140400f00b0034009000d8988410b100b0516140d022640442c1c044a01d07048002e0701040d201d41e91124050140e040a003240c002080300c610010301c8802c0305104041c890006540e9000050326210f400380e80c1c004012554003c005114649030f4041030310711006038000c0030400002800b104401ca05100409110350500000c03a0040040d00004101ca10880c43c4110a07441010126901450040e1902c50801d0030303030300207900110800052000d8ad02c0614400d500a64a5541950720708100b190707050204ca08160384003055480d0940c1b14100740c0661016150b020742c00780c0c90200a230300444550640c551100e00c50380e44070704e05400c40101c11000d030001804003000070350815010783c41910440c0100081580102000030103005603981d04900c0b01 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 680338327 1250 680337077 680337089
    0xa080403110a051509010c110a02060921060610030c17060d0f0804050f10390f021906050318070b120a0e1207030315050303040f03030f020c060d0c0306 67
    0x1682e80d19a03135100e1211980881c2c00d00c056503c1c01c1c1203032044130b010741c11101c1c10300081030203003040300c3d01c80d82044455004a52440d40002030907000c0e00141180200318200c1117002401480e0915101c000c201d0301580b480500d008041c103142030031454542151003001c10006420800c001550f844020810082103441d0103008122001a1307041845404401001a10002e80f4500e1080403000309004422003060000f20003c1c41c41c02821800f109111440c0d080b03c802c042c650200c65600001c500c80d00711002c1401d46404064004140441c40c0900440c4250101ca004034003003580344c40c001a20340d0000a024800f107180f80703130300c1e0180c80e08144508005403400402c443d464101040040d88001400c41c0e610140503d41403400d2043c0354001554a030180310146501e280400c1590201c015100100890200845107000071450743d4092014201600344038042146051440c20000d04601071403500c2820b42d0403c88208200f13072581021038400589604000c101008900001c5008144a078008 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 680339577 1250 680338327 680338333
    0x1c0605010f08060105041b050307110d02100e01090f0b0c0c011a1e0f0103180b0f2502070303050309100e0c0f010306050609041509050406050a05010b0a080403110a05 73
    0x820144545081c400544106008440e0340da070300c450500080320081501c0c00c1e0102000d181c3c44070306620510003907900142070300e41035545002e1900b2951a10480d055600003607005606442803c19007481030000005492009001191403034440d94201000c00d44040d029140da40c00007415031809400f1110300d500040020018601000c0c0c0c1c440340c4400c02c1100c0c0c1d2044d00e088098104520001e00c0d180310101000303101c1ca620900b0800190014801290300e014007980441040d800314052207191842980a86403a1004d0715107082c08907400d00300610840d51072560280c452641c03603800540172068a034141000d503035035250241310030704d0074452420b035032103940c04c10b04141d00700440840c901c20f800300b05803107003a003034440303480198160341060050503003080d03041c0000605440c29401000541031440c800505d00e03500c5106213010340d0300841d81a25025198428001c4c5045103103c0c280c01005099001424050901c00040546501a101030100042c2015240382400140a225800703a403010807 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 680340827 1250 680339577 680339579
    0x3170a2001090b011508060f040605040f02090f150d020304020a05041d0105011719030c05060a0b0a0509040302030702091f0611010b01030908040317040e0f091c0c021c060501 77
    0x100c0e0203448404401c46080b240100009100600700d0624015900c081e1206031142d41ca0509102c17200c0301e01c00c031165010703454040c0040d1036181c91003003420900d800340c400f50b60380e00f43d201841880c00381403a01c14043c1110307104451080c1101426202460302d412400341c0d81f0b0b01da9000080070030340e8682140390300519150234104807804c40064071007030b01c1c0d002000784a00c0c2e90b11107403191001120f41d5010f149801211080340003064000d800c0e031802d4441e0802119003ca16201c0601e0000200c8841c1c603903990340c1c00721030254a888030a1400034441116000807515242d034000b91070380101c000007409846c0c00004101c0445070700165500c07441124840004940d0f03a00e500a0840300302c1d82e080c02e02546020319111359544207004400c5166000001503151915560b60010045030b1030381e80f003440840900c004941201904203031800303a003041c4500d4019091929546080c111181b645804010085c92404081038200f4021074189404407070118295529010080b442d50000782c00825243c0740c600 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 680342077 1250 680340827 680340887
    0x706060f1d0c040602071710060608091209150912010e010c0e030c0306011a0408011802100806151c090c031b06022a03011b12020403170a 61
    0x39040603040c803a50307034407505515400700d144103a1040340540030041e0400d00701802500d040740c0d00048014038a00031180a8568020754034110340e0349810101c0010f40e22000c1c800c0112040061038484100101803d06d80220100001d5244e10a6130782498000b901096954080d41ca010b081100c01d0f094200034400c0026060041d0b0003018211044030202d01854010002410001400311010501400a100c56400c00a21000d008600d040c2e081a04008020100d000f0200b80a0307420821030065480360f001e40c00d441000b0b01002021018000c101d281d41c20072105540d0080c0c15040c1e81010f4001c150340300e091101922400400c007030311004041c00d01c8503400404c1502c184000880380aa4101d0410300100d004551488071603102d090b0060340b000581011440e20440d038501403101220602885a00d40700110782591403082e1052485d600350300d0076011217500001c501151400c56041140b400782103a44403281001401146400c040c1c010443c41c0159004420b0319280c0c00341003520030000c0788402 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 680343327 1250 680342077 680342099
    0x1e02031207080a1409100e0a05190201080903090108150d061107050f0607050f1812010903030e010e280f0b070912050c24040602030405031618020706060f 68
    0xe10f0301c0e0612441e1003031105008990b46901806030018801030010a807200500c08003031300000050381414095100711070002042009a41e04901c02c41c10016000e908600024003c54402040550540c00400150055030ba01402c003a5200c4d207105400086120001c000c6441403820041c020100c80c50710300402c0c40f00410360040d22483e8421021a0184c0181c4180a40c5a0b1803d4641c480450303c180301006800c40198041d000e8550904800340a82c05624002058003400c0002c44245035074400411041c1649030180001000c0704000038000c00698a1f150350303607201003241c0900006002240c1c04504019142c030f1900300da80000651411306c4050620103c005410744940d0046523884400103800000c41002c0c141844d003041c05040501c2c031050a02203000001c41300c5000b032907400c24a014000d5400001b03440640500c0e40259100e41c1030009052800f80c90007001c1a4241e00400b0070072200d4091000d105124103040c1d005a1130340441e181c95009003025030041c14150f030100c40045007884100c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 680344577 1250 680343327 680343331
    0x501020c070e01150e0901060507020d060c0c060b0111071710091a1518092112091203010314010e1b1011100b010c021806031005071e0203120708 64
    0x44413094054400d880244c0d44038000f201c290360055518401000660301071805011340741d0018260000040c031a1362480205d441c8402108049141c0d20300e00303030a00c2294402c4210390340080c200700d51a11400e5100d169102c0481c4507800300441901851410000240012500501e082000703208214170791030f00d00301c001c641038585100704130020b0010710100e5000c0c08a0304040f1002d0501001791560101c032480b158070042031046a4403801d503103515021003c00464405881018205498007180d442d03104295401905009241e84044215003c0c1c4220360226070441c0c1c1d001441c5c24410042085044c05890200e50b00310080c059010201e00300c24002d008040c601100f2504a1031000c0300d80310540b40301c6107800044101b44d0000e9561002c0e4015940f180341410414100300442117815400601101190008058000c60b044107201c00760030108240c0554028042c010f000c90701c0c001c100100300c40038180c0900140c000c04019508447e000f401200e424450016884483e4600564050705000701 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 680345827 1250 680344577 680344589
    0x3010302031b090408250b1b09060d27030f08010e0417090a1206020a030c020303090606040c0c0b04050c0102070b0708030c070c120b150405130b040501020c070e01 72
    0x9a04040b02081030301c418440d92454005120090584454441c0945e03508042808040c0000c80031189000c06200120740f00d003544a02c0f8400120701c0c042c05c4070b0034044000c029284c42e201040c498a00706d503035020280c81d200700d44002d0002d00640c007064440e0300804e0880c08069109000a12141810361106e500901c40c0d440c2e4071107203604e90380c99041c0811128222006840c191031103a0020903204040020081c00800400340c0b0340c90340d01c0e0341c401c0044000340c01045440c2940007401d03c42c0c55030180140300e80703010300e40041d6055190121303103a074aa1a00425092140f5070b10014004101d000f1070b0300c0141036400551214062402d8501581d0307420003006082e0140c402e0000c0004c01c0c50b10b9501b00c8446540c80400b44e4110349074001c101070160403a5204039008451a10040f40d08012500b0f1300d00b550b8080c0f4201031080c1040102c0b20351020051031100e0160741013500f0440320360006003044030f009510407013010031079803075080079802406040001d6409000d4401e000034051600070400d03043c0c3d40 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 680347077 1250 680345827 680345833
    0x902031b040b06042408360d0909050106090315050603120c0a020a0e01050a030b100506210f0c040e070c0c14011202130b0d0f02040b040e15010801090f0f0603080301030203 76
    0x201100096941020403244144a141e80c80020b038081b854109001c42d2420305615840b1f6a103405106817402c0455030b14950001070444001008203070a00d000d0180141001d040c0340310301504503221610900d003154a210829900d0703a001c244642c9041080a110b130300c0c02e00003541c170341644100d02a1120460f0030140d102d9a600c080c040b40900460441d58100c03440208808031140c45c642e80c1e200811001400202c0448250400144d15211580101500d42e82840d0900d1851034903000c1408158020702040c1240f0302c034000b00714032941c04000304c2e030659100710440c8610742e80d230301011601011001c038000d20036075003040c0000e524407016038a0403000e00d098849407252219a001301d0102d0150081c1503040042a4100300201068070000349104504c1c01c0340810040520351018060781d0050f2302c04050385030000703001c00c0400d4203002d82613040300c1841061006298101e0008024890601484d510f807a0f5540302c00062400580c070002c0d000218910502030540da9003004c0403590000d100c181e001e40 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 680348327 1250 680347077 680347139
    0x60c120906081914040b18010603022d130e19050a03031e050907051201091130070302090c04120f080c03030a06090c030902031b040b0604 61
    0x640190340d104241e454a03a90182c5555691480842c0100d8600004090b40d0340c2e500d0f14042c040c00c81030300350311540c003600ca04003103404d2030311840744006001a1100e120364904270092006980d0300829420180911590313170344062813000d003001d441d200100303084d502501103282800d0020344c40d0040d81000c04240142d0b940d24805904084a913822100000d00e03582241000400103030003548111410203410394501000c0b424650902c08882d010f41c0c039100c080d449604104028a4a5020344071810010b0f0020300442140740e58080180340801d80303442c41044e00684204040c200c000c030040806024608110100d00103115144d01c60206001c01d03070041d080080003404c207450a804a408860724201c0070121040d1903251005070030260301d0100d91220b410460440f4184041024600800d502080000d01c1403805481904841c101510034042c0350074140c4c080b0241e90003045000c01f6054200c0c0e5100740c880c0410008004102035841981d20880200e0003113841015620a40d0510b840340307507001030103 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 680349577 1250 680348327 680348363
    0xc01060e090a320307031106060d020d23030409020405100c050a0602070213020d0b1306140d0614010303080403080f0c041512180213020306091b090901060c 69
    0x2d0032001501800c0310180344048160903001e82d1818807400c2503000b2940800c01c0c516010350a6500003181a8001240900a0b204550b002c1c0304054114004032603141d182c0c4111360100703001c281880c001400c1d84504010b00f074140d01184112500d5040708600340c0c1e54540d11018484029000303130041a0040642d01c001e0000302b409120f681010b95009402002200003559524020f9071240d5412030300090101d41c5403884e103c0c01d0020700903540105401040300c0b02007505010740e400340701c984841100e00f0508100144e114461100380f01140036103803240901c4140c1000005850ba030f4001c540d440020384000414183e121581a0040e88207685a81ca1360f00c440404c3d0070009000e880c416038174041000200f201e004000401c01700848142449140c0c01141d440f21000c484046d241218603c0307408501204600c4c142e2454000d00302c1c819811825800c210002c00c00c1b0b400d00a000d01510301008400204090140040c0d8054000c010f00c420410360311508024482da0030050111000c3d60700b00004650 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 680350827 1250 680349577 680349583
    0x307031a0d05030708160b0a050a0c021b010e030c0904050d090f03020901210c06080601020c060720010903170a0e03030c1203100801050109050f06091303050715020c01060e09 77
    0x4a0b42c00ca030040d401e00849803500310180c3d000e0150b5000c0d03449020800000101e011461a03c60940070300009500d1506540990a640c0071951340021500300d01c68410f00c12200507542c40e00c4407828a0000b89000000c40800d10300b0400304902c541c0004504200020000002511110f00003907540b00c1030101e907034090002040d4040d000082d80025000018000030201101ca50540110104e103042d002142d07031910440d120b0260040701c0001d400000700940355804008031042150705486891506000d610703145448481c00200d841408095001c01c24a07a1055180c0c0d400365030002400c002140c4481d00074101039100350320527000710308009003100c41c9290110640703000c03140c0800070b030030440c01d640314959142c0c0c0010b112a0b9059050b0130046a04242482458044d2500381c3c400112800c0c000100740041c0b0303008142501c2100100100169210980c0714580f9455050074020f0311504c07c5d241040341100020341844030310b80301095a0503c0d03d030540100c004c44618038500355841d03c400d036543e91 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 680352077 1250 680350827 680350849
    0x50c041b0503071404050d0b0603010b1804021c02061303150c02060a0b04020409020a080f1609120302030d240b0c0a02190b03100314010b010f050c070b0307031a 71
    0xc0400c1c8140005910b040c06a1205482c3e0140249110b1416484400044080c1441e0790b083e03170341c1c10119017040f4040c02e00744290b91201804680d00107502c22220a0500707410b00040c00207014030040c1a800c07008001480070043c1c2c841d4003c1860f6143d5040d400300a610700b00c5171005503525081200f5017a15403403180f0501035000e03490f6028040d181d960040282c05448800601c40c4c016030308000020300c10080d072001e440342422a5549881c5420859002e00407940c014005661002d00d25a20a003565081481c0342c0495050340326011003a0880d060590031400390007503161400d0b042c004a100741190620741610201c111041031460a9222802c2c1000741c0641901494990300c010055405460400d98100902e201402421080e40d15020b41c05103e40054a9020450300e4503a014009c100810102c900d0300e402110080108c220104002041264002055421310400168114200205001c180090302010752460364904083e2401001030003901c2c0380b419090288070940c1c8a920700040406 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 680353327 1250 680352077 680352131
    0xc010516091202180106170c09090f0a060f0e2d01120501091202011b08040c09020702030f0109031e020105010b04030b2505070201030e0d08160e040504050c04 70
    0x291410704060b801c02a0b41801c1d0b00503070307000b5401100e40d803842d240503007058040c0107181d8400941100f40f0041000441c00500341a41100c000e1005d0681d54076145003040d030102034155214050b8070745140040080c4101d0f0800040940014000301c0c034641c1d0001028050003503090a0245e10360f943c0310140c805004076030070a220081400c01000740e030404282c0100004e00800c00040d81e455140d0b1160510125403403103a02607515030017100750072196200400c0036600c481c2404600d030318107642c560403084142e0152900290307000c1107100543d101048001c08060180c0020841100f00e801c001d090036a0301441a495140802154164244103020f9103040305c1c8a000a6030500e401c560380c81890500c0140f101440100c000d8421524030942201500700d13140c151146951000a03000043c107640f00052a074081d60302400b52202d202d03a001484d2940150079100c40c244600d0310030412a00707004001c0415030b10600f40310521080c00b0020540031005401114100b1900302c1185605400c445035820741 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 680354577 1250 680353327 680353337
    0x11806020102071205091e270f060603040b0a0906020c010c090f050418060f02090a1401090608090c0f1f0e0f040605060a1b0807030507030806040203130609110d080c010516 76
    0x602a0720401d91504241c503031000b084200d02c2c150403817000c2340e892000c02000003116842c8040c0a50301051240c0300e5000042983e600c2d1031807078261159240f0790000750008406581d41c1da00d85090000b15815204c603005240000d010028a480f001070040006024070090012900300c001350920b000c0c441c45414150748545203141d941c039911204018444200c13804c8003160200080c0241c0e070380e20001d041c060002141040c1c030394a040c400041c007000d41a0441401c0c4280d64041c001d4000c00029420744c407400848041142c00441008240075010421003610304460488500c4107080d000241c0d0088041d044da13030514041e02d4a0100b105980041c410641c010200b0009807580511035074102130072541e10001281c001d8026030300d09849a219540513000a040884c07648200b55211034101c0e00484112029411410042c0075540081c000c6040200300550300d051400c100700b0b4141003004550303030003003290080e10501c2c141981e4552245178640419443c220000c2c418224001009040c40307003075568 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 680355827 1250 680354577 680354599
    0xc020316080306150406020f010e072d0f080c010e09010e0c0f25060e0105010f26012309010606120b010c1209060e030a05120901180602010207120509 66
    0x742403503540c03019007103641000d03001044649210303440b001400149065402403072401a00740c030140c00c44500b0501f101c155040310b1420800c0c2c0d444548004002c91903132440304c00c1005810300c4c0c07051a142d281d0100003443c1c4072200006404101051034907100380c003a00c613005002d03042402c220160009000d02d01c01840380d5400b081104076500302818011011502003890011412201c0c8c829008414130980080d07580040311040001d00e01640c0c2038001c51800074004c40d41840c00c61480c41c00f1034082c2d40c10100d0b070301040508104c00903013184440b01854008022114101c0c2103a214111681c0f0b15a04008030380300455502c0105100320390803641c00b50385003445242010740d0744019208c01003019040101216603400401c100c9082c5c258001000d48461140303903d0708801400104c070300d0107036500c00c3e0007860948000c51004505412400114005203507a21403200060b02c00403100090050f111100120205d0039580540c01041c1460054480c250000c4500008480500c2032004854000000102c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 680357077 1250 680355827 680355833
    0x1205030a050307180e0106032a050c10060e1b0f03070513030b0a0b0306090d020303040602070c0b040315060b27011211030a0e16170a150b0102010c020316 68
    0x7460300324443d8541014092a100340c042c440544940051501c04800c0c4010883c0540600c244404002d107100303c00c18120311425481d5807104529112400e2140014002109010920490f54000802070040181d9500d5000c012070701da104807107240d00c600c143c680d4900c00c1c1d91802c1c1a2195001c10000e1280b40d5500e64000300c030341e6004105100404440c10340088000b0390f084446038492592004001000c8865070200f5280110142416a140d080320350807060065002c030403aa03105d60000c4c000342e55800903140040200441e50b000441c800f80214000c02007016844082c089511105c60501c05c954480e0140307a1a403013050b50300c440c0042e013152211070100c10081c03080c1068005042030361154141d40c481405039400003511a104c0640081042001c580c14481c0000f6040c03c000101070801c1c800b003507105204103600501082040394440ea84050904105090078190b01084c03c80b03003c030080c84204090031035442650301550801070305600c2d09200000b9035000341c5480841c8000030016031 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 680358327 1250 680357077 680357087
    0x10c0209010b2d1809100b13051807031b0e130b03070f08060115090b0f0f0d1406100807031e090321180b0c0c0a05010608071205030a 59
    0xf80d081400248402d5800c1070f9500c0b8240310f0b851940982540c0e036200d13241d030744002c1014202c4184200020424071452240158111041c0c45111841d9596001c480c914040094030a034400d41c0d0000b07090803103052424803807421900400d5552014050a0025150282d80d200003882800000e110360742c61000030314000700b00e464000d003180d0b000205c0030140f00109084ca4100e801c40440380c0790703601d010490407100f000003d0043c4500c2d60005420040240f000705161041d200d4040d00c0e00d808501c0c0303658001d1000c1115501d80c501600643e0b80c1c012410050050581d42c8015452100d04100160040c148824242141d1720b2568070314081d95120f500950003800031102c039011303110104c80507600442c0347d84a40c050503806030300ca8104004203900c860440003440d4981d0003a8a08000883c03002010181810241c7e507804040d15502d40d841c4040074841d4020343c103602c2130a102d482d44180038020190f0000d4241c03201d040c15100515182c1d06010440958802d00404a520820080680d944130b4 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 680359577 1250 680358327 680358337
    0x201060e01090515090a0f1103091e06012d0303180503030c0c061b0307050f1c0c02010f03110706053304090503090303120a06051c0b0402270114010c0209010b 70
    0x1b18400140d114a1894801d0854051421201c003012001050009807582041101030031000c5c000040504440706c0745058540d001881148005140100301000705036007072041c4180300403030801c40e5a110703507039090003018103441c10b0700b00348d525645000c08a407900300030044807420240c0d02c00074503404001500f8422554401240c4c134042e40640740308001c2009003070008001c014043c100800000b54485040c0c0d0070b00d2490b8449a00d07094202c2200d11000350451415281d00342c090a10010400ba4a00e054014294001c100c24030f40c0000039080041041c154807203809a41680b0b86460b280c40e0103450700082c8049421300c0781c1410781400a40700071f4506034100d1803219208038196800c08002d540030074074580180c0050440740011100300000071207144600c000500c4112828008400143c08941c070090410a0152250758184002400d640703480c07903000342c0900e030a0203144144512446818005000b80100c8241d041202d03042080e541c46079001007107142e0001c0030109242d1810640d5401070b402 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 680360827 1250 680359577 680359591
    0x12020123040f090504051507140c0304090504030f0806010311070b060303040308131715041e15020405010e092211030304090b03060f01030b060d030908010c0201060e0109051509 78
    0x4000100d504000410b444008154a2501107142e0600d0b15026003072844000c0e0410300f4452102c1081611940030640504441c840c0a14a90301c1c403940c81c48a0840c440c035001203e2581c10103061200300342d40622a1038524403160307903480c1c650325200b0044081d42e400b48002030b0186c00070300010740815000d02c0b5075500400014103c80c0703855a82d035502c58076500a203074016114440e4840c1005100c9900c0285800c491b8040003070800105d80e000c4403030340c810300500042c1000c00c0000e04054116503080d001e60a40d074210b000303000384448500000340070358414003031540094030342d00811005050450042e0301803a8856000302c5c03c0140070000c1018408070340819130308200d0144210308039031001c0c03000300041d0251000118144003007606040c58080d010b0503812148107524010804100a0304100d0b8200c84c007124a08050046402e0444078450a81c01811080d40780109031001c464055000034211949d8040e06c9501e6a601d106005c12180100c402d8411503a2400b030285051506249003940300308 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 680362077 1250 680360827 680360897
    0x16031a042703050309160806040602071b0312020c15070f030c0c090510230424090209010906020f0307030302090a0e071101110403172b0209010306120201 68
    0x180d01c50340200e010862490030340c041500002803080d904014002101c0003480700f007a54100d2450018001c0d41c03050001d03c0034082650110300101001a2041003140c110b0b51060003031925900c0b0304016441c0800c00032804050f100d200030500890400380c90307003500522030720742450410b1481e4495107058075804000b20700700000d242e941c00001d1b0140c4031b0308002e04008180046c842c50100e5004100741f60580000501c00d8000c038481d1400080e404490b0030000056802180d1a07842200102e144610099680150300d0001804079490899601030103480c0026031710318413500d651b03d5081e40c0f80e00c89480343e01f0303440d0001c00c44a004a40240c00600001302c01904658900f940e075244a80202e100356101d40000b1458801980340031800d0050b00b6200c4550000e080c030b032030f15595032158150003514150310120804180c980325001c00165407041d4070401544004804440060344000354084103000340860316158012030400c4401070341480c856810307124451307070b104001102204400003203030308102d9003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 680363327 1250 680362077 680362121
    0x603170a1e030e0706050f0919050d031e05042919050d1a030309040f0b0916140406170a0f021306080a05070c030c03090806070816031a04 61
    0x1040c41000c074000950740d40c0d000038102a81031126414003100c1d0780080f003005001d1040640303017000c2c00100c440c1160126041c0100c5000004101854150b80e44815840010140e008041c56005035030941d00105000000140b141d440f001510381d070286001e03250380c1050b0503ea40405600140421b205004401003ca0611442a0907921440e2089501c100010004a0303032420781103090050903005689400d5441c44140d90101190f643c3c0946640f02d4451501c80c509031603400c000d5880184481c001405040141c6003145078040c007003a40003d4400020301c1c00c400c07080168100c0f01503805039074540d0740e04111491318a03040d00a0003000317800010815036070b0701c4000841030f02d032000340200c10403c54624805031400c84060301081c2d00a01903094142008204030105601c640c114203401d03410700b00300c8000c501c6c074282150a0103168100307002c01d1285805001c080ca82000c02c561280540391142840035005a80c210184d680c911407550034010420803981d081d14154000381605004181d9003103542c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 680364577 1250 680363327 680363357
    0x80304060b0a06110f0705010e131508070302030d03050906070c08091e010f0306211e050a021c0203060c0c010f0f02030618010e06090c09060a1d040603170a 69
    0xb200a0381c0440c01103100302060260014041c0007051080040b0740190884615210000c0e00300303e00f8043e081d12442c1e02c2c400e00d0009103500d0340320b00c221110065003144000c1e21201d0744c603500e07102e07030000340e01c03034451000c190014500c03c8c00ba46105181b050b0140600e40c80b5140203641d061460401211602024085581d00d6111074895207040e07540010703002d00600c4c120002403c00d41844c1e007260101070030300ba8103004100094030001452618100501c3c0d80c1c0110f0300b0440201d82a0a50000d80c060707000042d84140540094880166402101c1c844601d507012101c008800c2840c400080d0550440c00010340d11021200241481003000c1001103600c5401451650031152002c0800a00590110a204072428540030502c8040d6060410713000c10b505003484814107a90013040b00384602e0082c8006007101440720181d4030450006440d4907115603d8203000b4022000034011000d1548000c0301c004c145181070700070340046030303081001420b2401c0280c160962030b40c0188000340601481141e1000d10b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 680365827 1250 680364577 680364589
    0x42604030b0a060f050307061e0c05030706020301051503010e0601030e030d0c170a020f0f1303021f03110f0f0c0c0a0e0901060f1511010b0307060e03060907060804080304060b 77
    0xb0540140700005102401d1030450302030107029030030a44c0607170f0100000384145504841d40e1f861148034120f0a510840002400300e03118402c0c808005d100380000703d107100c00c03c240d45d00614180c820486507074032510700c407003056582070009104040034121208003080c3c41d9402584a132403900642c1003668038040045409006940700c8803208000036040c04181841420f282c15282d0b0402e00640c07096140150074003102d003081c061a000c2064080d000507644051405001c120380045602a21034044081010404040c0002c46040c820200341800124502e104200d070480d02e4480c1000c07016801c2001089882050f030b000484c9072050ba00c210403000460b5034401540074010b00200d1160402450141c00003400d6803100c4e4001030352035010401c04d0010740508007034506032030f00c2480e00e086080180700c0c1c07180c003400b04900003d415020b2490007080d6558450404501010709500b1070f001a1680e165055a03441c862080e000003542c0200450b000811400065802900886c008581a8680000504 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 680367077 1250 680365827 680365831
    0x610091223190b1b181306141c0f12020a050d050a0305070e0907050904060902070809010210050708040807022701080114010513020313050111070218040530071506080303042604030b 80
    0x108d09034129003216118078055030f40382605100b00395140d0800030a5079031741c8420b05d40280010402856600b4a201e0b061080022400440c1c110dc100d500c907500c0420b002d400356108071080c0b4002420704c0d0000744004d00801c4c1c401d00c00d0501408050103a510700108444a400400503d5801920765400003858411400641009802681c1c0300b03646202d01400640351050701c04090611a0400c1d08010819030003010301c6a025030000012070b0f0b070341001d01c00100402c2514400e0760780340f803954241142c0c080c0c1e056001811707269014000c00c5030300784822400e00c1d002001d01c00e650703110b181c00d5040c0c2c6119109401035500109806580c0981c040c036a42c9150a40d854000040e503142000300ba10025413502c4880090b144a004118605504064881070f88070f02c034003042a0a40240180c00030781c501d90b950300d1000b030a801c1140468540f01c803441c00d1110500b0b030003900c400d007500308103010981c5400030049a004650000c0d5038076485c0b201850511024401500540c05c128041c071000000ca40000c000e68 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 680368327 1250 680367077 680367089
    0x1103030d060306021228050606070501020a02061515030604020a0302090a03033b04090201090f0602030c060a11160f02180610091223190b1b181306 65
    0xda1100c0c018118100c2400c8024540c4480140c02004903004110468855081006c50480400e2a40c3c540e008a90f0512410000825030f40c80020342e041a0f640c0425064000c49604410f00c2e101d202d43c1040011b070304090550004184000c002140039071030254006c00000c101401c015042240301c0d800204010250703803099001c103182c4c08800c0b4102c41e09501756244100b0300030324031100381e1500c840b180512840c05c0b00a80603591382d40ba0b007002d581c01940308200500b5403000032038505465600080d100d070400c6040080600c5040040b803e048440d004031426a80401c10f20f0303090840070018030f400302c41143c0e015145400303152007141c0540c9504114800070400d042c3d1540550602109205100d080582204100854902c0174000318000b80d01d8904860f80141c0c0e03000034030070032580c05011399811081842091281c3c040030f9040144504152400e54002d13200a03200d135540e80c04d84010407081c4041d00400903020000052110103210300e41800c148040c01d00302c032030345004280718100c0300c0f190405 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 680369577 1250 680368327 680368331
    0x15030f0303100b180103090201031401091d030928031b0302030f0f06011a121501080702070f090504050f0609011a0d0206041205190803010314191103030d060306 71
    0x20002d21040c207440b00003440c2c84001945803205103070312025074441e03420115042580f00c03403800c0c2c01c2d6072013a0403000d4000300310801c8842c03a596680003580200840324802c0099040803514411f00b120200680307084001c0078188107240c1c41041440800c65002c6501d03641804d13080340020020668408141e4894480107207080002800c40c01090300e4000c1c003002100b41c5910031001c9945400f008600b66044178006400c6049040712070000480c0d5000740c500d00511f600222040050f2204d0010380c007110b901080c2c91b40070301500da2850484c0ca40c9103074054920f181d5601201005030504503030117107500c24000e009540c003115100d4000707424100160b542c44000c1c0e45952040d0300f80030038401a0f0200b010100d0310405020070799404107559000d5441031080d04901d0b140260284070080c8a40c1c1d5000705640c1c044021180d00b4030344415203410030700080c0c960b8640303420400c0c80b205000541d2481d001d0501046a4100495039684519840303a4103055090b00040c401050020318900a1070007842c030441c00 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 680370827 1250 680369577 680369581
    0x130c0f0314061501080604090b1f050a150c060902030f0f100b03061906150c0b150108060d020f0a06021b090103021008040c03020a1d0106020d02030a0815030f0303 72
    0x800c00c051050481d4a40740d4001c2824000101c086881d030090001007820805c66550742c203c005402008958405000b9a0401d81084412104141440c15560003605100c9920340c45800f8880305518500070491021703140306405660f80c0c00b880380070401070312410700403940e481c0940c00301c0e04121075034189100c5688508250841c1103014440b008031002ca040b000c000c004010320000c1e40d90f200183c00202c4440300d070b100030008101c0540064001d04021002d0119441514100411003007006100352503000c040408a10150003445c84081d000701c0507950212103403103034030820860410110f01203910072386103141c070603183c1c0f43c1c0c1900e03400a0407a40c0103070098004003010031068031443c0001c10700c00d40100c0300608c0185da4200e040050b5a041d498403c4480c3d403a803401d40f07155035040c1c1020b50321034000d0700d0024080070007008228229513113408491280c1d0340c403442660303501072a12900300940c005003c480d40e480e00c200b000660007440008414a01400c1d04086070400707004c808800302540000003 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 680372077 1250 680370827 680370833
    0x180f0d030e0906040e07061202130b0406140315130f0608010b12070b07081819061b0305040b090f040c02070806090c03030a030b0d2f010e0d0605130c0f03 68
    0xc40b0701d80c400010784050240b00081c58100d91a9a0a4000e0f0001c1c411142c3c2c0c80c600380f05030365042d201010b5203010400c0350f40f034a559142815410a100f16000502d01039546c0c40d8070400c100c145c038040c100506840f030304410700703004109480c0550b1075101c06007a0b85804840791014640103000003003817044000240c0700c059000b4004c07044548a14241d00341d000b06810005c40143d18100e0381465003140145459401c600c080070808500c80c511650711103540c5c0380400c0e0080011600304200c4001e600c03081e04100c1c000c0303144070180c2ca1400c00980400e806000400800380480b008104488001f003e40c4820040e03040020301b1a448031007004010303841303080140030148c8200420b40d00607020500511f190b071104000079131385c0e11503c13044c0410141c44251100141d2120940340b0126076000364121940085800c1e00401c80314511061425049400329500055002e0002c0050700c50004d4011144800e03281c0315140904000f0b810800f406a00303500030f07030100c0d0070300400b05e003c2c000f0411050545c0d86981 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 680373327 1250 680372077 680372089
    0x50a111903050d11030f0a05130b012729010207031502030103050610180902011b0515010504060f0911041212020706141b1e071703090105180f0d030e 66
    0xc103c0e07149010082040c04000100b000344698040300d60400448c1d143c0d0f034038a051001e4084070600901e80701d104c400208003c11b101c039403034030301c89840e840c42901c6078000c988540c1901d48294114040101d5420152500c0450300c4840d8862181030040b03502e80b80d0b4a5888141842004504541281c4d010005204021050045a03081014009494485810808440c441c0700921310030f2070100395a00c29400c110790144044141e5140ba480080001e080c02e81000d07612810310701c0b450002211141c0000c6081d00e030620640040c0e6403668050803034681041c1804005201c001c4101840e44810300000656203032202c00070201c1c910502c2c1c41006802207400c003a150080c142c1105080c0f1240c58a0600c00d070003101c0940c1c0340407213200040e0400b9200d0580c41c03410540c101c22650725a024040640480d1440010324404455040d150f4105955101400c5500c9002d40c0c450701c0d000501c1000342c5160b4a0041009501c00032004040301245485000001d0309001c642c0e0084010990044580c2130b5485d081c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 680374577 1250 680373327 680373341
    0x190803040f1d0a0509100228090f0306050405191b090c08060f13020d02040e1003051e010e34030506130f1208061f050a111903050d 58
    0x400058015103940c1071038001c4401c401402e02e4580fa41d5040010180725080051200103c12031000319a40c41040c44011000a0211a0202d5003160040036900c030900c00c0f0802811180b510a19200150031940d4000140002500036503c9105062041c0e019082e0300645202c554401d02c2c210040d0710080c52101849842940440310640c030f82562081d101d60400e00c0c0d40c0d8444800c40340d84241340c078130700009821510041b420070314051001c0744c000c094441c0d641c010b00c1a5400c20342036940c40c0d41c4400080d06911128000100541c000c190b01c00700b408040c41c000c4101c8115000080303028540000a03900d0074a002c01e141d5010700c2442c0b0000e541e03142c821020321181e04048214103446055480d07460743d862015022800183d1004c001006002501200b011460360241c0304007201406403200404801084c0d560a210b03049040790219107140d88860140d402860b070300c5880c24807900d540e0980b8111102c800c14034060007021880c1000820f1300d40840c413418426210380307488200140e070301c00c102c801c2 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 680375827 1250 680374577 680374589
    0x30c0e16020f0c0105090301140c2d0a0e1c05010f0615201f061d041a15030102121f030302030f07020a080d0309060b060a080f0402190803040f 63
    0x8488030b4060b1550010410036071401d03085c2051940d400500c00401c0c01040e00e14030718400f10f045030301400541c0080d00300501c1a44c004915444507040000c3da99990458a5411100c544c0f008010100c0c056004080c1100c18520003032141103001129030791090155651075007151a41d41d1404400c68444c160b2154001400c1145011100d4680c41c0c07002030018561001040b01502c0c0707804140103010301c01c101144030120943c1c3e80413000e00030010303000040c1413540643e0085150420140411126003d6100e20403038000d1034000f8070180320a40c2d0401204098407101d410b9130b5119901c00c96803400d000500c100c8800c183d000b0040d1420303800d02e0003a0151110700b4604a20342c0c8c3c0040000c09c0c2d002041e079200c0b000120005582d90424030004200d00d025038483c1c1d10501030030421010554040d0b120b0340501e0f024007428019418820b0030000d8a214a4400c0000300b5042408900710002a603800356106101070010b0b8048011a9850680c1c41d500750300c071104a9000140030300405085102c06802095 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 680377077 1250 680375827 680375833
    0x3070618030215040c21060501060323060a03021e0f150d020f07051c0e01080f01060813020301050a0905070b0304081c0f0606030f0e07050303031807030c0e1602 71
    0x34607641c00079240d046422403e5050350441000c40c040c0315410f5500401000f04d5900695461030b149244403443c0000b95050711004d1901c400091302c01d00070700a60483c00c12200d008168070302040f4480162080c00381c003054114982e61008001603c0300c80f201c03840c1d10f490003000941104144200030074141e941041c21b008101031007503003c2c00d0384668140e03003524407101000360703c840104010341c180b40500c0c00d01401074821580700c3c1c40000c4102c10802d03001701050b0740c0c036242c03850810300540c0c00e840c09031141e5a00c6d0710baa41c010031289105041c40d0390031010401c644001d1345202d400103800d40e042a5021240555940c0011003044810403010004142140045056103000d03143c18035140984214140c0341e44010769070746080f000a40c4034140004001c4000c01ca0300740c40f000010028150f4280110f02946042038101d84100c0002d440d00c12210014000d40c03442d9620180f04111036000c15042d40d15204855021000070014640003028180e0091181c22915007103440450b581c80c404072540c1550 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 680378327 1250 680377077 680377121
    0x1815060302060f0c01110f03010f080a0f06050619030507060e0d0c030605060102030708120604180203060a0b01050409020c061b1206010f200109030306140102030403020d060603050a0302030706 85
    0x10b12110141c540c0d0192541141e526140c0420350f0754058480484401515803001503010b4000315100d0246044c0c4403003884901d105038540d1b071a95940c00e1000805408082080841000070302c2907081640d1040f8003900c2080c4138041ca03022001e0041003600126040c2d01f0075801840b00c2580f00140510300701085a842e01c40c15400d8a90b8140100c2a02001d410700781c030341c00080e025900800c01c0300c44496020306401e86d00e4202070b00c1404c0824007034940a210f01c4c20520000302c1503d05a03040000140c0040140000e0b4885030340d2903004100c21030420b414010b05110010341819184007420280e03110700060a040c1c0762020b0700d01880705e0850000001160281b24242e1011026040c0644c481d4081c2840010b6401c804410340340884100312058640006501e01c040100c4107402502a041c4030b51418044584c40b4554401b8240368a00c2c0300c0c0c0180d0003408100090320380204055001c501803140022015104c1d121035081826029050780580d10010303000701000305500c507000110000342c10948800c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 680379577 1250 680378327 680378329
    0x90703021e09180a0b0f100506071a0712020409020316050c0304090c171509160e091509041a0c04150309111c03030e01060b0406211815060302 63
    0x4800140c5124003180c0420459a880803003000415030032500310308000f04d030f40342c603d40c1c05c49081b008a80b0b0303000041126900080f41d0400c4000d8440e100d80c03241c1a8103141141c0f030f04078a1402c81c001c00030030811118a0284c0000703800c1e84000c2015001c94030025980c0c2ca8944140540d014640150307908100040017258641200881500c0550741006c002003440300f003180003103070522001440d1611103040d05060190314594610101060181034401000e03503520b80504164034103014189001055241c80f07400c03c1480d002030042d0380b000710301c0704408000b5024000328441e94001c581c1101c2c0944620001e210407001c29a003c0e0f07100103040c26403880c1605264030700b070604020700592401c1c1038441c16090b0400c102c583c00c5008510001d8102d05450303500c2107241c0002c8095140a4001c2031030705024414890042c01890207071400001510300d4981340840c02ca90740e1104900ca2041c00d4072010b001c00d8119101c0c09002904400e150119001d49000c1c1031800000c2400f82c50a00e216280110801c01 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 680380827 1250 680379577 680379589
    0x141b061302151804050f090c011701061103040305160806090708030f0715050a0c0f0314070c1a0f15120703031d090a0c0e03061506030703020f03090703021e 69
    0x100c0081842503280c1c0c018081283d50540702000065000741401c1c100070075080c4078134883c0d210302d844c0c00440d100101c2490054400c8084031182525a00300c003001480b1040c0250380940100341104210303454142c2d244c40350b6081030a4004101c0500c1d00d244420400c0d910104107050300100c46034013410b00c0380e1600d03648941e80e20440800041c10380b00803c030481030044003c00c4506d1180c1040080c00700e4a0841445001007001c2140c0001040c0610499031a151192090b034407900040015110310b51035140c401d0f21302d075001650454242031411081883e001030524607501650350003d03000f207a800c1c00c905500001e010401800d005210303c00380b0300c0b042000000c0c44d1044a406080000e04910380c12113410310201c5d40010341d60030004950500940101035801240e030541c0719a40e206942c03115804141d2603940688042e000b501903100460023501c0c0c182c0c01540c0040083c10010326140203a40e960580784c00882d40b03d01c058014000c100158103020710f505c03400640d511080c5084d14568800284 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 680382077 1250 680380827 680380849
    0xf030403060c0903020310050f151507051c0807020c0d12031e02041412060103020102211204110a0b09061c060b0714070801140c0703141b061302 64
    0xe096102d6a00014403400344003998080c6802509445500e070800c1c15200140600380c840c001d9000060001600640c1070b06000042c60100400d048031016040742e155147c0e4211034016600380c0100c0c0d101c1c64400003020b488100b94150b503240c0f040301d46041880a81003402e0140414041c450300c10b10b8000141d410145030410380c000f4100069161100d04001807100982d8482c0582d584c400130340421100c400d0001c0c0da00c0d2460840d10394243c03c55240308580c44840c00c2c030000707000d41d0020310315400c04121450054200003400d1005403c00101c41e001c282902410380e01901d40300000407907000581400c1e00000042c002030203003a8501014200424194801e16040a10221241111803c42445a00100000c0c104a008a501c410542c01c010a07246540e104082141c8581440004c0184060144010207400154034040e195100c0401c0582036002d02006ca08102c102c0c200c02c4c40e41c07905c410141410304a0700c0921101c043c1192007207460418007601c5528802d905900f2600140e6424086003 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 680383327 1250 680382077 680382083
    0x114070f020c0402180909240c07051f0506010809060c16050d0504061b050a02061c0609020c010e070f05061b0d0203070312090c05090c0d020f09090105030f030403 72
    0x4052015022800c0ca18502c02e100c1d4000e000003400c1d01200e1100c03100030340303400701296051a0f0f912040d10043e03640074000d411405082c0602c1c1c26080d41701505000ca0740c8014030402a51510290b540d61604255165412400c1c0c94000003118810220500c945035000301c081c01d2009490510303a0400d650307000014400b1481290001d900640d400078000c1c1d600149070f0100c00c4441f440340c0c01d00041c0c0150410300800c2d0000d03850500b00301710700700c0158201d424990040e025003000003594081c06455400900c88003c615000715004440204520415000301f450300740068441c401d00615a094400d403070070107481948880d90030301680d9444141c4004846048030070580c4c2d00300c80780224403500c8202c11103040b40d00480d03a824105130303008002460103e01c65911140c480241804030401c442c1c3c2d010014000d0b1201c0b140c1440241840c2c0001c540100901d04060304026100c6140e209980c445000f030460a07801044105050516601460141008401518660303a0b410607840c2c2c4da000e244805 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 680384577 1250 680383327 680383337
    0x105100b07020f13090b0405060916140607020f060705070302120c01020304120f0c1d010617070f03060b1303120809060406020d110a1e210b060919080609011407 71
    0x13140c44409180c0c84481e070560300403a00e00c22854542041910b409003100c04814900a88042800c85107039401010181e5007440c5c100f8052080c441c0a101e516041a441281c0040b07400540b41481d903250009828120310400003495880e00718414803980200303c0f030410029500c280d901507010381c0c02005880035645850b006401c07622560500420303210316401c025001d00030b10400400c1c08520803a000c800001020340c500d100d03980c0c0381c00448807900d02c1c007000c20b001e50540020a0070640b0800d50301d1441c00071440c020a0403334a9441e106034039030000080390f04600ea4501c0400800601d01a6240c601a05003000003807440c00090064075004001d000410950f40060a0b284030f400a602101c1e00c0d04040290756200c003c001d001800e1011040d00b460300307130121880043c44140c841c15022100540c004a451124504800d000c0050b05401c205180c2c011000d01610072103403a054040580c030020400304e100754500e0540b18600701140030300070f071986904041e101902030b418080c0854019041e8608 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 680385827 1250 680384577 680384599
    0x1e16090f15060504141804110a030b0106050703020c0a150c1b03030c021c050705060d0e0607021c03050103030914040f05150a172107060903020105100b07020f 70
    0x15a0014030356141d0192181c1c441d04404961154001e01074419511222119512148014204414a214542c20140880e603000c0001c001440d60b4000141110000e8101c1c081103440e2303a0384080d01034007604076000103072020590b03505041d03041003104006242620725600c07039400c03c084c2410548641d5924030500c074400c00800100139035102c510104c121040140e00010b501e03407400402c90202c04038180d2040304403070703c406200e8501c047c22015441e413090080815038580001c1c0300c0c42c0d0304050750404041e559261503d21546e414400d0740d2049449038054880000341d485404030300b100540c035074010546402d00500020f40c01030745400595000c0f0f84501945c01c01e0310001400303054013030b805208143c1403100303215070201070003012080700900301c41074210980c941100303c06150b510011a8000d90110906020006a41e095019071043c0418500d16048868a400044c2c1e1428402103005070740d80c1080080003000d02c050b14025110444c001d91070101d8a4001031400150500090f00c243d4a002d2 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 680387077 1250 680385827 680385851
    0x503090f130f0f050a15050423090a03030606020708030708090609190503070b180f0109030b0412080a0507120e1905030c0d081014010c0f051e1609 65
    0x8607003000c0101190140101e000d045041006003a101a400c8030030350800020481e0034030203001c0c009040c85007007280028186030030200005012480c20200001911440c41c1c00c000500c03110692084640340d000705000040d5143c010100d0b45a0b51091045401800003400100d80201c00c55800341e03008054030f9211000c81000400c01e12414240ca48c5c8036200c602302507140c00d22010850304981089081e2640c1c0d03940c40c14090b13298420342403100c00c2c00008040780d070041e01d800d101c10410401d041c544680d1650302c95580411004040c0d6040c0e0344017021241d5084420741c02000645c1c4581581d03018000d5080c4010050150203103228105c1d00b164490740700402c2c030401004400790409245002c20500c42045c241191030b5405002c0190050040020321010a80240946030041c1c142040400c2e0051a00c043e4070802004000100e0400080e0000301c4081010450011983c030f0007107024105460841c03011540041910540354000c1e08440d410700700550350b40c4480070403224012030109030046005 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 680388327 1250 680387077 680387089
    0x703020306100c210f090f050d0f14070608150a0e400302010b04020f0301050d0809031b030c030c091f120506010302090c180d060902131a0406030503090f 68
    0x441c0700302042d400016201c10a0b588038400d550f54120346e8645079502c9445420710f03000510b55014040e04007542d000320b00001922851070324a030b140070b80303030300a06030819095040c2031403826031100300050510801d10190089031111a504a10200d40646c00310313140c001c544500300c1d00202040340e8445400c900001d05003c100c44a520701c040041c54581c001491110007030008034000042e070056180402c0300407a03040501c200c0d000c40d41081c21890550b840c01041101481c16424129109074050041502a403020460b08401d1218000c1d801c600b000405e050500c0c2c04000c150461007580040990311454545010032a0014181d4180c07604d03002c0c00c1110400300f503070113500901181e00d10403c02010b105c00400d40f541030780e208580807101902e8541c800022070240f0500c42c50b40b500903110740d855034070b0134228594545204010101d0019142c4e00000c01801c842c803040501079850300502d400ba900010f03d0900558400c81d4204100c0c2d0540c1c0f5602e50302d0283c0c50400d80240008009891165115 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 680389577 1250 680388327 680388353
    0x1140d140313080102090607060207021207120b0717040303150e04080c010c0801080316060605040e0c0406081b0909030c0609030a180b0a0f0e0d0501090b0703020306100c 75
    0x4011500a03120384498255654411182490307180c55014020500c000103000303c6008181c000d1803203040400c0c50312a0710095210407001c0fa0b02606003840e208007540d0a10101008240b0000c0d405d400b0f015904000d845520004c01744410000700352441c495920101c0c0c0c01c203030055090320700060929010001c0c900c00c1e40780d92300107030750040d0601c0412042141d590020305042c51108000d202c010340d1800c041c2c450100a00039669150003c2c0405900f030920303a100307600d0b8540070300c402107030796640c8401003401c0324060140015181c02843c00e50314a424203000300030040146200034416022400f001c1e42d0895012188513100d034440300301003250300100300700307680c505030014050782c4035810145034690356603006e03140d6000825031482100005070350954662017241c07186220546020104134045034105214400b060070702144c5021070b0480e4491214611a1700d1180000284007100d604140405400c02080c02d41014010000c0040725280ca4000c078000072040e05208406680da032400403800107503 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 680390827 1250 680389577 680389583
    0xd14010e0316060c090501020604150b0405070e1e06070f050f01020c0d03060501141206150a0c031715060706022119090309120204110304060207031403070801140d 72
    0x404115803402c80c0407081903255880c85580c0400c40b95070030b802e00b500c21001c0d900c5aa0301503004840010081940074a43c00c1900c00c0744000010032001c100c0010f02214801e0f20351000181c01c2038620401400e2044444d02c03081031215688964000b02d10001d0364038801c0300c00c02849076440040480c02c00c841041840c401e405101c5c0299102c5456000306503848411a07001c00019041040c001b460394094503c405a145906140700e1500c40442030700e0b401214054902c40d00f0850302042100c81d52002c0d0b01603c00070700c1c1c42e40c2c0d00d0075900c400e04005040742035a0303840788480e050380c2041c414002c00b6000c00c6022248240c0d4001d4440905e410924000c1c001d80412444000d640d030001c110548071080305c24450b0700c405145d1254148518040c40c2100c42000740280420052182803180e0304c81001e840803c1c078401800800c00700c1004e030740220560400d41d01141c0894010800e4410960803d04d043c2c031003010f085c00c1ea411440d02610042c00d52030180301c2c22004800440444029480300304100c0c645c690 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 680392077 1250 680390827 680390833
    0x4020705010203010b070209010e040515090c190609241112030c0904050906040521041206020c010615020c060a030b030114041101020c01170603010e060115030f09020d14010e 77
    0x2a448542c13000c06c0d03010078030480c41003a886c40041181d103600c0c81400d000d950400001c01e03150410300311100c007518006d041c074601e910070880c0820305555512076500b070400781a440240000d19003480500304100c95001801d014104004246003a90301c81c0c20561584580d19144681a021090250504800480001a1000001c00c00030012910001000a0345040c5c40c2000696107240a090300c891098030020415000044040b40c1040c081460552076a0100b07881c3c0e20b00b5650303555210f550b40e00700404540068011440c858000790a100d417400802d103905001042c8000700600a444032504900f441c41030b030000c0348080c0490300c642c0c00003081c1880a0000c01203100b401300c07482d03100394045608559038004202180c0b03055201246550841c0700685030181040c86441c250300ca120380c0200480d400d99030324500910140000c00c5424002e2040003040c400c0100f8141008040c0d0f007022030030007120703418090704000503103c5005c0d96110581000d40047c40201c4101180e001d01144950199244 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 680393327 1250 680392077 680392079
    0xb030d0507030905180a0504140307050a0512071a0a020f16020405010b1305040e0a0b011d0601230d06030b0709060801170a14030d0528060b09010e0402070501020301 73
    0x5a0404000d080711070183c0c03142e800103036076601000380030710038405488124070900307010a1210440360481c98200d807054211091180c1518207070383c07554005030030a5559911035900a01408410304c0b04100003019190454034140c91511010a200030101c2c005042c00a1040090700007015503056800340381d0340c0051181e584043e500000b00c00079513500305911880c600400021102d20501c100c46010030016180e5044901c0d000400000300007401928040b070007241590000620390300a0343d170181032003102c18000014103940780e4551040042040b81400303103c4107030f00075070280714500f06008c404418207075546600420a0502070401c0e54401031507084101c05000d1300542100140c007d44a195850489981c0d81d4001000a05039800c040c1d0826045280f20f00045044510180b07004580e81e001c5918002d842000c140031590100c5149828803541891100c801550300240000c000001106000031400d00d1443d01c268800c40d811641400240c04000078192115010b4030503254001d0005c544035 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 680394577 1250 680393327 680393353
    0x30908070e0403110d0251010905091e031902030c0c0303040f210f050309011d01090e0603071d06030c0d0b0c1c02030415051b070f03030b03 62
    0x3800c0a540403800b013145030301400f40d0380c100000c116104004a60061a042c04141c810010341d0062030310a000ca03201848000d50300d0420030740c800401520b584100c00c186200640000c0701030034182c11038030b002c5060005001d50610001000c1044485940e40720407800c46407000c5034903520405905040110703002c18031140d5280c0120240c0448008a419500c45410b01010140c1328421405007084d0940260400c1c04440c0d03072840f4101e400003410121060310105900d481d03d441003450302c11583c0e5440050341e102503503800002c000d00341c2c0d514280860804855400604044060702500b1030307940480d80080d9141d60304001c0f01004021810044026195010000c0c280180465029001e071041c45940206810040c9019101c180c000b200302d0703490344070100451880d40c4814650f0061180c85688a110a91a48010b500071480790709a004200e5810641d0005d98a0080072452400ca481403200101c5078044101d840051b07101e100060f89881510301900100f01d4032046503014070482c0850303940 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 680395683 1106 680394577 680394599
    0x3060d02030f0708070617190b0d030e090f010605040611010912020307020414070c060203060d050f06011a092b0206030c040f0e070e090403090807 65
    0x11421540019142c000034000d014002d0700083c2e41000020401c04c07414006094a0804e141f0717000c5030501200350b040e4000e00c03440c08124002c201500200302c541c412680c0c2080104421601d0350982002004452900036460081c3e07186404500030031007400f03140b4101c035403903500c1c1c03840c09007006002c407880303a80444100003640d00e03a0005000100d9845c038051b800b0016034000c640721141d900400060303480c0c0c003160f903010000f02e1301800300040d4080d060201030350f0814009a565241c110115076000408100680301b80102c00281407a69008594241240c0b0318252503400d011842005a01da0300c556040240d011a40e0003d40c0035880c21041e242c1c000c201407118110745d0b0310707040d00851031540c011141001030510014091080d0701c0b80081c21000740c50b2111030b1031464a001030001c0c01c4e60b002490340d00d210700420700006042611492441020b00325100541e800c203542ca6111b0740c4 = true := by decide +kernel

theorem cover : BRFrame.Cov 680215827 680395683 := by
  have h0 := BRFrame.cov_init 680215827
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680215827 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 680215827 ≤ n) (h2 : n < 680395683) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
