-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3849
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:52:08.299483+00:00
-- url     : https://prove2.me/submissions/6db53a83-3b50-4489-8ce0-cb83a90f25dc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 692086330 ≤ n < 692266187 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 692087580 1250 692086330 692086357
    0xd0c05070f050f16050112020a03090c06030b100503010509160c050d0512010806090d08090a0602040b120603032502012d12060e060411040f080708010b0402030103110d05030f 77
    0xe410810751000d10586510f101444c0910704018142030018203940301001d00409010380c04201d8444480c065170241410302e0304658100007596498000801038003048481c5401001c000240400c0b050244082c0c034140c800050120880d6610350a40d1450640200c80e0001004000c02c1c0b408041b91045c00a07099888075540d03010f035a10030b9500b100f4000394041c3d100d4440f50780450200102a40003003005241903030545801c01c07064407a5040c680c503010422034050080da20008000032040c89820040103224403074501d0319929640d29003003503101d000c2d18a00010704268010341c1c04003501400b03646c00030746205040c0008001b249100b4140b4074030741100089600a07078202d012144940000107015140d100c504280310107402d0100030007000364040c14050142e03031604040040d0003032034819a00034110315520401d8246d0303110752483d0b5884c4144034010b01c651078126955103d0809000f10390680b9000f000c052100700740141480f84044202d1410703203ca00007400000c0c1224a84401468507854149 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 692088830 1250 692087580 692087593
    0x3010b030402030d09051804060b03100204050a0e040308010e0403031803030504060501084e030f060a030b060607021f030e24010b0f0f03010e07180503030d0c05070f05 74
    0x410300d0700e80b0201403192001d000c105d0701d0410940d6284600c040300d080b04424604580d480b149801d90203000e60301c0507030740d05000300da03031707050b0300100543c06413046800446105d01200d0351000e4081891209030b402600061540700144142214101b0b000c2c1c0152103032900107000c100d041503281540044000441c00661503400b4041070240c0c5000711070141910380c01809441c0780b003003200110744080640e03d48082c011211195450400b800f41750042c0c2c0341130307000d154081c114403c981200784e2080703801e4800c8584140c08980c007810704150400507242d02801d1310304251120020405180c00c0704c0c02c22a0302020740a10030503400b0440c4821034014244c3c0d100402da42000000c02402c11f140389003007840280c20050301d1480420030f8000305044170f48800001c0d54403151112010194403c0d0000075440c51000000010007400d20f14015124902e696290485240d40400e0061102820b12036154507134414451600800d1055010f480d14a00d0790805910305903030340e03803018500c90070441c0035240c2c1e80001 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 692090080 1250 692088830 692088833
    0x204050408120a060e062b05070e0a0501050105091e0a080706030e0c030d03110c01020304120306060509030a12030b03010906020705161d04060e0f0d1e0e06030a02040b03010b0304 79
    0x440c0e10b82d00000c00b568140281c5080110b480c202e000b00400561041c480b003052034240c000c1e0144110380c0d184100001003d44111418035a46d00c110030f200700c0400150f8803000840c080e00501c51607061340d105a440c6440c0000074410440c00312010041c508008a602c0c6401e0403139668079a001005000440140c0030741890614050221640041d05142c40d07040220031103010f5802041d40c4030800814100042c00150007407a03102e603400740b140c0c044c0300c40d0b100009002c00c1c080c0d41410041c8130842660180403050700d0398011100d500400c00c0c4150568080800d075000201c0c009001c1d1860b200d90301e40000c005c855200000e080d10044081a542181e0005408080c40420f00040842c10129014810418a0140c0007a2080701e40101200756600030380225041100325004903c140c5000e03030031941c1f0092040c0003142ca0b030140060b200003045c003450141d29502012100c40340030305d00030380702c40c5001440c0000b80301c0280d1000f0003521001d6400c0001048482d5118003940c080d1030f4001e0925180d05d00b5 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 692091330 1250 692090080 692090107
    0xa06170a02030f0d09090203070201110a0518010c02010507060b19090b04060618151404031b1a0a20060903030a05010902070b0105040b010c060c0e1e10050a020a0204050408 76
    0xc3c654140190303040756840c9095203170810700c10012109541c2d40181d580d0b82d400000c03070043c002d410340c59100800c006a0f0038106035124010f040e82c00ba020262080da001100e00641c0c04028620b8000c0c04034505202c100c01144407540111070504000e800741d044844441e1581801c515642c00c201c0c0070700ea40b407018814608103031081074040e1440e410031011009902048211007003940c030071132810f030a00340846810a40f08030121008070881c5103001e500d540d140d150901c401c1c800b0400410640369103200001d001c501b000c4054520b1245207800602d0114000011510509030802080b6080101110040016000c110840c4580e405401442c1ca0382044078528082c1e0340103900001c00a801485010b021502c03104085044900c01c40b000030300c40080100590b441110000082c000c40d02d00160000c04603002202d18442e441e048410301403400c52254283d0000b030303001c0c3c49950048641400c841910b4000c00040124415900484072041d80507400642511740c102c404031000c1d04003141c003081c01c128 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 692092580 1250 692091330 692091343
    0xc0e01120f06033201020705120c01090807060209102a17030705030108070b180609220e3013080f0a02040609020304151505030a060203060f0d1a0a06170a0203 70
    0x14104c000c0d45042c2c1e040d1503103585c03034002100305080c2c00d00000c0c4000c0e0710342c02503021b1400c0d19405240240c441d19103080120003900031903075640c0130300074650a0610b130503c1100c030710541d802103e141c480c500e4000e0954071489189850300b12000100d8021002c20300071884d0185204908580c6e99940d41c0d81803620b1642030940e141d2260350308280510021000d0013841d8018881c185041d82d21030b0301e9581100c002081c0c241d807000002c0503844c240302d6a0b44000c400fa040341414540034411105c004400d41501a040c2018142054400ac0c511540202410748100105058403805540e00981500c0d0700002e4201011030f02009100e42c4408208021420180500390042c5141c250440c20b526090300c552140040800c0d4030b802c060750741e4130f1071014007803801c030000f01401c806811680000712514056000394415a00755114a5080f0381c003400a10b4030150a02d081d9034410040d2100020b40010511400c0c07010301046d000b41d84841011401c216000e801301c842100000050200c00d5150040c0f6080c0309 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 692093830 1250 692092580 692092673
    0x20303040c38031803030108030f0319020a091e030b1909210f1e0c020118091d010e0d0804020a05040903270b07030c0507030b04080403060c0e01120f0603 68
    0xf01700340300400c800038002c0142d80510b40e5500c410b550740da840c05043d60070102000148800644049032601030f8035842040f076015070384220a00b80140881c0c04801d946640c031444028a1300c0017034000280c200907010310b0308080c1005140c02041e01496592142461030f4880ca40384841000003500d140b005500080d10709a0341c4950802c05076085459010950100b0744005800512010102020440e4440d14005141140d90f00c45413104075100c08410000c0c21703084c1c890800085081c04029110103061140342501e2054200070070784501442d1054641100050060780d00800c100c41c002059180c5004142446100e99610000e043c0c030240c082d040c09182070990282e007400c035001805246034410841c0d80807505410040b4003030046140103464020590401440d020900e0103000030444500301034000d0b82e2050000344895000200101d41c8001c9005a050009030381c01a2440c64100c10352000c10030030740d160004200740380c4984074082c00340c0c90020a940c460341005120045100418904c030b0050 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 692095080 1250 692093830 692093833
    0xb0409090c0518040b13030912050709150618080a0308071112070b131124041e0915050d02030f011d010c0c08070b100f060e10020303040c380318 64
    0x345142d850041410015024042c14032609d030400805105041100c4030040020b21818401c4c50300c00c0f03102d04e017003520300e02c10600031890b60180c0380705040204c030310307071080c3c4003104021b16400038540c81c1207481003400307490441404500c045411a40d041804441c643c901da04400030383e105610302c0c001d8213a15008103103040c0c40d140340c010000062000c200f4803800320740407a0f041c0d1050442104101a1b10030030844a4481d40300001c00140c07101400c10480024a021210002400e699201e0102070b91000c95900302c910504607410700007840d108040200c107a002400701c9403103580c400304103030855984d0046e882e45603001e40303840310706030100740201c04440c4c18070314203143c041845070349009141c05464001040c03041c5820000742c0741141000c05c2c84c02808080c20082c045a55075001620041451651034080d951581d2408000e03800042200d010b207911a40c1280c00d185407041005644640100746d030305030809081c000c4005003800340346124488545001c0c40d070741d0803e241c065481e98041c05400519 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 692096330 1250 692095080 692095111
    0x3080109020309122203060c0e0d1214090303162001021005060f100504060816120f02130e0603010612080d0c030b130e01060504060b0409090c0518040b 67
    0x3d000010400d490a80b9414166075240e0001c014400d1015941c404a003001145110000051041b240c012113003105486c0c40d0000102240414000300001d0800003130700b07100c607417906503444611640e8210040c01403c5001070401c80c00c4000a41140c1c030050025450b00d400c443c103441070020300c8844508500384412540c0c1c5480c2007200103901c038210f4105140340140c0e94000a8580d031100048107094600080488040206994015105400c68054000016154000034010300c00a41c0b84514010154540c0d005190321004210080c000941500c0c203034076000d001d00001c0020380d00010003e0800e203880302c8030f03502c0d00320185400c65043d43d0000511310781d0030f61003034003042c04142110002480d084c0046100c00200d88140c0140c800500415000a440354024101c140c0340c1d800b026400300385030001e00016907580c003040156401401000d21040040204104107805a4094000d00c5e01ca042619481c5a6403000554500010441071400301d89020403c0200101650060780c00700e01c1402c0b4105 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 692097580 1250 692096330 692096341
    0x30821090f070b0708070605040302100c0206010509011214011e140c0708071a13110a0807120c1e06110109030c020f06090d05010f1104051302131a07030801090203 72
    0x503a24030b54440e00c0c0c0710076000681c01c4d0a1102d640c0480e004290400300c10700c82c030f0405180007980c4040150120908501d0b14805140c2c05101180440c1210b10091507400e180e420024040001505210f04480c00070b4468a80d0981800070302800b40d15045a005041c42040c00e00991000d80b01c01c20400d03120640c0f010308100400b200308090350f0017903800c14485501c030710040c603010401901c04484500308150130760402403403203040740f4885000c2d4407034041e481c01c0d2241d100903c00040d00d14000e02003103412850041c003126204100885046004004240090350b54280102d030704910351403000803440101c03c041c05101c0d0084113080518a106e40200f02e00b82d504d0320003d01c1c40601840091080342040c18101c066600d440540e604203400030301508022540f480c2a174000d0281c2000c6000c0b142c00d00a51082d19541002a6400c9a4ac003401c80c101070b41c240d603c140000d60007074031000b642010380e01c00070176010740c1400d100c40755005003015a99908141e09026041030416841110903038010001c004 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 692098830 1250 692097580 692097583
    0x111070806070e2101061a07050d140702180708011a030402040c0908060a060f05010f0e0f0301060f1d0c0403120c021c08030a0e010b0303070b070207030821090f 71
    0xc0e0b0004681ca030801201100e000054030304031100903642400b108501d001100e4000642c0640c044800c1860500f5103960041020700c55802604805801171700400c0380a0001401002207a0110340d20040740c07890041181d0016019449154290b1140d050040410045035000001d040c0941031118460380400c080401030350591000410083c0955142c42c20284681e0081280310301500c41c1400b904d84900c1c003408070f4030040c0018030601d401203411940c0019030303501948d1803070140c0e002540c82c141502c210707009200ca039a440c09c10554043d9640d1100003403818040f15a030014100ac80c2d40900184440603002100328400303040554a10b00801003080000d600d000c82150b00519420003524035003250000408011200480303207a40490703c41400d0811070314000851144001581c100700c1000007064580c2210041130386150158070400c400c0300400c401c99a03550348048a40304a601450f181e41c0d0b070024035004160801051203e4110258031150a2184290300034007003401800c0045d030904169 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 692100080 1250 692098830 692098843
    0xc010b0301180b0c0d0219020c030c010f0c08031321080f100504330906090207020f1302041508340f05090a0311031207020609090603011b090501110708 67
    0x641544d90000340135070300b00005405681c0982c0c0400c03038500804a800d000a922154030201003403007400780e0418100c036903009801d007507130041e401e40c2c1c2c50440e84540d60340c200c9a80e01c05029490303407050201003800040d0320408074400b075452844030344c81d1004c1c4212026040c0c0c90302400b506c00c000e0703000042040e0308107400042001c44004482c00700300710309040e02c1c0c080024203201110441c002400a100c10590310441140c0071209000030400ca0b003562200302c07904a00a8090080d40002c500403084a146009003c0d101c001108040041c9041d94400c412120402280800ca002c80d0014081100705404400c400800700a41c85c0b4141060020406c07881e920108440d59105006a19041d146028498015038410860144c40f20315070302c0e242e040c00340708401d0440c0c2e0360b4800d108082042102000c03020641c0c0d0502e070301801c4207060404070f804000414400034062901036594000e920140e17050b2000340c0056260b0760320341c1042c86043c14001044600000417400040e440349030b00700001ca0000400 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 692101330 1250 692100080 692100091
    0x306230306070f030f05010308030714090f06090a0b030a090c140f12160308030a150b0706020a030902131a01030212060409020f030607080907050f03030304030f12020c010b0301180b 80
    0x43c02e092103c104194001d1000106813801c4518200000c410061150000c501403100d503294031201000c0c0400340061031046484507908000e0100948480d42001d030003503c45070f00300038200701c00795483e03c00500d41500700301c441099454841c1010001e0102a00c1c41101070f028038050504800b04410215079004443c501040c022000800381c0203900005101070280703025041c4144418a030b9074102001e45030000d4450220a601c0c2c0b80b400342d2441c031046002011034500c4030541b410210a603e40b03a001f900b00c0d900d80424152164581c400595803409041007410030310900003106256580442060140c064510b0705051040042e41046500c91078031035032006c030859011445603402c0c030120391041c07041142f0703603058480d28060001c070a8104c03103000d1007000d442003100c280c550b69004200741e0341c0a0b070003819003540003000441c01003446103048114602c16400d2003810313602241180340481c0e11041c1900300f640d5640341e40460304e01d03082c0540f60343c44500310280054129aa11606260034001d400c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 692102580 1250 692101330 692101337
    0x50d080a0c0c150c050106060305090a061515030f0506010201050112080d020d050709091b050304081b160f09060b0a0503220b040219030b0606090d02030a03030623030607 75
    0x501c101001080d0208401604004800c0b520b490740c51200038028802e241c0d0b003250154200303c0701062040c4203205071440b5400d17134401041704084648681004002d0a04400580c6451210100e20003219030391140c0d00403116074000070441080e0203074808840b000303844141164104001000320302c9400c0051410907800004081c4e6034183d10300008002e10801c0340c40f50031581000104a4050f030400901022034890b00c4081c0040da03e40080c08010b059072400c00d0010a8061003c603002c142d002c0054202d11502c10300b28468003640d020006d26142d0580400c81da1480765200a200b0400380d0030290000f40100801400300b2070a040c0000010b01454186004200340840090b071018560700300001280600c2041c140c8040d000d080240400308221007c0c0d0080440100c400d000a080000c02c0c402c90741c0003200e103090368640000b081015884080701590180004030501701580d01406001500351080d1000665640782c00600610001c1c02410b07400104540c0304009042c0e200410b045900c40c000d880c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 692103830 1250 692102580 692102597
    0x8060906011b050d03141803030a0c3f1e09050a140a02010318200111010203100f080f030f090604080a0303060501180302030a0b0a1b030902010306050d080a 69
    0xb2000baa0300e200010040d01c288200c1c4101d456158050b0b2010101a15260b080c2e04243d480c00d82c4d040c0381400440c2242d200c0d60040001400740d0301030754002408086145803102c10000d4181c01004c98040f0f21101a01101e03841148000100d144007034203160540140f000e00015000382190103400182e800224030840e180d052800c01c02905003c11030310554030001c1c3d511001c03c40c441c51541c03a501c0c0c0d60224040b0b4a00340701014424000c10010400c103a100565210002008d51b98a10345503800901310b05112500302c642030b0b034820030700240d0f1050101e14400d0f0486481e003070304a40c10002a0340b2154140e0009a07041070414404002c48460300c0140c07441e0f0303540d100c0c10400b1803842d00c115881484240181c0440004040d0b064005c04112002681c1c0d160000c00c100400400080c1c0d9071000a6165101409880014804039402980044810070004550081c00c0742020003418850f500e40000b0b6440e20400211342e01841841701801e021750f14990f240e40d154fe85e0781c40314031444840c88144010034 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 692105080 1250 692103830 692103857
    0xc030c01030c020a1b170f15010b0316020f030a02061501090b0304240212070e0901150c050309040203040f1223130504021c110702090103081b070b0a02010c0806090601 74
    0x10716108000f485015200d0f0000f06c078480289440303120802c185d40050203000382080710280400e00e40c0b0f042c0c0301e501d0203203071654076a0800d29104c90f001d00540029030086420f402112001070000e0304003082c0300c4c1c0190165160541500c5000c035041c0b1400c605000d4150418000803d60006072070b0f1195116421041705010001c0d0b80c03040c1030000041d00e00007800051902c16401e505c403e500d001301400e4840c1c400c03000c4400104200b450382400342c000030360205005508174a11030041042c6260103042541e1625510b03e022030b050781d0045505079000441e800d42c0d241001031000590382c007051725107031074941c6500001380b041c0b074542d003c14560b4101310701044111009800c0b18004c0c3c028000140308640e01e122086510700c4074020711001309019032034480800120114030080fa00d201e9802084e40407940e087d030baa154100e800c80d40c11070018141d0548000d420500c1008583c01800e8882e015a80b148103080c002404c1da4000603201041107031507405c0c0304003516002c5629410103000d0802402c80e403140b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 692106330 1250 692105080 692105123
    0x16140d03020c19080616050f0a0e04060f0f06050c03030417090301090302010b361f08010902090a0212070e060f0d020a021509030f03040c03050d020c030c01030c020a 73
    0x352419035000032a4260714086100088029040754448801d4440c199115101c0311b100449105102000c14000c2101010300200f002c000d042a00c12810402d40f4114840c01080442d4826000442401c0c0540c6061040590a4010304000d290602c0c0c00d6240105501e11a5124080600020021924200503070103a807680d06c10b481c2c0c1c128019008100b003002d20700340207000c1c0c072426800d81c0c0984440400303801342c0f1142062110a04078203060949005168403030045511100900291800340c00740501e00780c00c0e0309002d5403c01071000d078001041c82000360041111035030000d009012280e00c10480550343d10380310800507a02a1145c2000a0100e242002042d064030580d0880300c040032000450402c10030442d806020030985030307401c950443c0004a507401c5008420303070b05000301e82c1c42481a03180c410f09020003546d006103c1c907495050780c1c1d665070302c0d5031034540b2080164001d40c002151089450030200b120102c0d6080c2445c003886080c501c40c4010b034807280d00107806403112099820700810f0168 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 692107580 1250 692106330 692106343
    0x9040b0402120a0501030c0f0b180d21020d050328021312050601060302040e0a0203040c05100c02040b09060105071104090516170c060f0711060f0c16140d0302 70
    0x2c1500b42001071400e004040c0041c0801d00040f40e06044650000c02d03840b004101550503074451000c003514043da50075015416440c402a2207901110034400070700010400322800304220000e909009aa050418010781400c54141581d404c00c0000e1003007240c100015502411040010034000c1100c28400c0303040c101900c00d01403180281e00b84041c0000d114002c05070801600382c015410340c1c0c07269885030b07400c600707134407541c45000c0b80568810003007013500310603500440d0070500c28049121070b55600d4020890460440b01203d012032004108001503007040c0c0110403034420200d80200c41c9150600004e040da00650074054000a201c050104913070319182e024002654006048441c40d002781c5254250102113030007040b80070714404400007407076600025103180040006180c1d030b0502e045103444204a4200e200143d0722203611005110203074a43c0c800070708890000d02c400070307514408007004034a046242030305804010b40d242c03c204480d4000742143c0340761041c00c507108401011309040492801c103 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 692108830 1250 692107580 692107597
    0x1e0c061409010c020d06020c070305010b09040b160203091305091903140a090b070602030601020d090f0e040305130e01050f060301290f040b03150d02102001150303140f09040b0402 79
    0x2840010300414240307001480d2700441c0e10074402030080665000078002110015200140f500034840c001c500003060200304101280490300c1146d00303040c01900001e040740c040b4000200c40c142e6071014000449024010545801440b883c03480038051a5a4000c025440001413404800804120031441134411540e100040001140c440c0d00c0b004981030402c025402941c7c40c1d40584120306d0b418424074018001c40c030485030900c1100061510b048004020410000c03c02c50411904000156601c0b602015240260103a421940d0342581427030203100c00b06886c0140700384520710500c0100028003045008900e203041420282c00c401407800b0040641e806800f40c0350318034000c04075002c68643c00342e8010b9403081c1d003402008844c1160301d105105d1882e24441010707410040c0d81c0e20717214038140680d540e040c0fa141603401c8480e440702909002800c40701600c1e0101030103c4104002c006047e40b100a802c508111100030b940b501c410300e0615449072148440c000d01603070b16520302c1c007060765640c0d06403920354 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 692110080 1250 692108830 692108843
    0x2a1218030d02100507050d0e0309010201060f0806010501080c1204030e0a08031305061605030706050712020f030604050601120903020601080d0207060c060f0f050106121512020910031e0c061409010c020d 89
    0xc08c801e1a84035048407010500561070004005020040045c4480848000802404059080c140115107090008000c034488000c10032a54040c0030031903440c14451402079854014451381c800400409c1b0805034085401b95105004011a0340000d2186c103007212000c869041e510800d801244c42d0300405104064440d00001c100d00d0180089a048a80711b404159220701c80000c0d101086000c0b8020400c000d54009020301c00101eaa0401e80c1c8419000300050500f810604d60301d00c1e500d425901c1800e02100140c220400400c60550300b08103001d00c0e096107002900210b400c0007401400d00c1d11500000d072540c0d80300c60b20fa400c03100d003da10a1412131410742c0c040c405580c440f40d0240c40703030000c0381d004002139103818100500c4500c03c1c8d100c1e206913542031000380c030120b100ea02041820315025200e07201141c1c1e640c40000004201ca00611510320000034846409103460809040030380ba241d00ca04188015018a80c1440d4003000441310091400d00b04031003100d68900200303200701340303400300240f48 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 692111330 1250 692110080 692110091
    0x515031b130504200103090b0105010c06140a0603050c1c0b040f080d230c04060c02040f09050c010f02010b0d2010120b01050f2a1218030d02100507050d 67
    0x602c5104c5000c103807042048031640005640910044044400259000d406512144014441c0f58400d40407000030a0044001017081400703030020000004040e20181407059403280c003001042003d10140700f0100c0300325070540d14074121140f24100c112220000030084038000000504011480328009000c90704111165102d50040c00081c0043c11480310302c070305241c515844009600045081c0718880c425a50195082510380310065407900b510302000c0764042d407a0701c00101c0503403152040c2e08840e8010001032240302e4032180050310010008582004590410f60b80c040300d03456198010b404150311903203c4003226130002d100765600c1d503c0e610a5902220442e01890500d038040c8003082950140c0000f004410135920042d202ca100b0081c621307000c41e206008541c0d08400030307240600b0400c112081c201400c032070b43d0203c90800b22002d40d5183d0b40c000124a1041ea00c2d0308503442e84006c07106030018081d02c441c00001941da003040c0300c02d152029441308002011503120744107a50705d5583c40700c0148075 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 692112580 1250 692111330 692111333
    0x51210090c260c01030e03040305010f0501031716030507020604030210020c0109090b0d080d110a0314010902090d020d230a12090303050415030902180a0515031b130504 74
    0x280d01c10300c81c0405202e041c080684514209502041c54900a03200400105001400541c050b003c501b601c822240810700c00080411400e010b8116014205800068190304505d8200550200031213041a41c5000740300da03184c411010461282090740608046444440f24030000d10240700d140c200a40010391054008681a000104c41e020301c00c1c2622108802605c41c0b06440448410322031065021703c90034200b40108421100800c00d20840b00e501040303440f01c41d0b691780ba0990149003074000003a6901a241001000b4070011805044480300651405c21a440041c1880e49103400192150301d004440800300003100180b03070fa02e20484520307841c110359030072442e03910307220003003010b5900301460f00c0241c07030307440c440c0384000180e91381512030b07609150609025001c01490410480300b41a5900c980030096540c40d0040c03034814954005201151406180c4201606c001801c83c10795005001000d150694000c504106a11010283d4150ba19180d00c0000da4115038485010a007515010070b000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 692113830 1250 692112580 692112593
    0x121b0206040e0f070f0e060906040e01121703010f0e060f09012c010e01030b0a0b0a121a1923180d0503060907050306190f0f06030b0a05121009 63
    0x620407800c8a640c00107551390b1442c207807100c400520a042c00610090102041c910b4504043c0000c2000a42040d040a07260102410190000e8010b103840c510a0304061040083c00081c42c0b1004448060050855250241c7e001880c1e50a00440e040180034800141c0c00381c407821901d1850301320041640300b807565210000300318501d818803d01000011100005220100c040e00c0758102c2d403108801615984c03071501e8440c0c0c160005000d150200b510780080101ca0b94480b103211001e840707102c2e2014240e0065190101000b00c00048448000044400300295400380d1001c0c02d0202001c9840424940c2c0c011008034100c862205d07002c1c0340903c00c4002d00c180c40201d980700c4c4404411807411142c022003201e800b900e40e80070031039403a540090044000350202e03100b8030141d034101030050603104031074001d1440001d0350046a0010700c07807066030040420100400318142401402c250070100001006580031500c0001c960240b24002c400d02866000348010803c20b4001900c50321200f040445150714090 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 692115080 1250 692113830 692113859
    0x309030703080a20100e03040905011401030606020f100c02010b181512060412030b030d020a030201050705160204020901021203090d0e011416031404031a070c121b020604 75
    0x40300140d0080c141c00c060214080821302c1c0d48120030001c00003624921500d4016140031500707503106000034440000c00584601445001e0103040d100355072035aa90070001800c6444a0b4490000c6501180103a00410000b02c0c03003154681c0c5004c0081000100f115040e40900403011015810410220410204078000c05800703014007c40340520001c0010700b400c224042194980348400d41e0069404600001c00014181d1506080c81c00c0100300c0b10300b171b200028207102da1a501080903030040103d001c1019428894540d1202c0c950900904010408601d8880000161b0000b4051940042e89600503030003003002c2c01d401c080d00211310b40c0d03a21b8540e0085403074180401105011802c000302c840055801151580070440c0581c0d043c1d4141507130786525520343c2580e180c05809000001c100300f04070603107100040014600a01580c445403500d00c89540e40d0090051540c4200095005114002a440e00404400350544d2a202e092903140c683c4458851068200081d0712040000300012405d030b402c00c0d074 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 692116330 1250 692115080 692115097
    0xf091204270204030302030406110a0605090102070201021e121803010204031a1302180a09140706090b0f0a0807110a12180f260109030e030d03060303050d0c02030903070308 76
    0x1404400007807002034103034003030b5002c0240560410b0000740320041c030403444442141c103143e08a80030200241c42d50b0080f50810b44800000f40d40005510096580403c1800301120f681040306600c4041c044465441e655803407101e1941e184000780c41e8054003610703000300418a030002c000315030365075076440c1c61682400d01000071000751416000103290a00d50040ca10b0480782c002c0d011200c036190b40b4002240f004002403161003459a071b1601e40d40890302c003d02c90744000f4a4080200a032508004000d46522590360040200640c03c220380c400c401c0c03006040c0d0389004801e00308030030241c40381e1906a8891060500c0ba1034148154440d0b0342c1403002001c80c1c04040101d949505510708400f0700030b803c1151050040b0180600c503118104000e150183d0032100303170700160307408040b04005600742c01d003903071300c419000c4d0000380094922a48625007808503125050b00c6c0e0804100840ca1542c01030301038015060314110240e038407052060454000d0003112107440009007903c480d0340e12407074031011030b8000180 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 692117580 1250 692116330 692116379
    0x708122e080718060302183405070203150a0e010e0703050c010309030207081002180613030311010b0405160206130b060907090335130909141e010c03140f091204 71
    0x41100d0a0125a440041440c030342242d002e184800307230001030b1480d510001c0204e030544921001d4000e00d0001000080c012650440f002c9106d4232452111429036070501d5400846402c106001c000040c4009a00c50f02608203090200d000c5800c0e09003641803072000d50004045009403d1900d07888413141e402401c800441c01c41c044407410405050100d18001e00940340080000740303100b44003103030080880e6681500d6440002c1a0310b540d450104084d01e41c20303521900c441d1540201c2c140516010710042e035001340d084213440c4640701c281d100c410100c00c002d84580c1c010444000170500951150000c1c4014640084007c404942e00410044440700711a0343c403058400da0590404a0780000011650700c80000040c0c04259414507101100816403100111448181448520b111000510007001110344450b80740c500700c080d9851340390a4815a10260b402c0500d0061101310303d81d6000e545580040101d5510421940c540d0f802e02d2400c0e11882d050113001001042c009001d4102c0e00050140300c40b19030 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 692118830 1250 692117580 692117611
    0x30305091f0e2e020703020a05060304020d0602030a02162012030403060b030109050d050c211b3c03040e0106050708122e08071806030218 61
    0x140844a002694100480000c8000411100030700d00f5400d10a0040c00b44006010440f54855000c2c41804440d41103a0140e040301004000794508002c041c00201000c1e6103141c918039003a40040c400084600703000740326550200104a40038a40c0e41500c115000d04021500102a1400d03c0390b42441806044070f0581403a001c42e45250800b15144241002844002d50030301c1d08541c1c44402820100b00c030540c15640e1180408080f074000c005404443e03103070743c542d640e0324440c040079142881d04159002c901c14141078840c86502200c5800c40e10b17032038611540010380c404006403260a0603d442d000040000100310a1101c044403215007c0e14060005003202c10703a071a42c6000d948900680c4180d240e06030003100100510390242c40103220040c42039502a1900002d04240069460b040d900090010301f500c00071824032075120955039080c44083d0030821424500300705965600e40764080d803241000c00400340c100102581d04414041d690003000951022210b8007105c0e00c003081102d00008211110 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 692120080 1250 692118830 692118859
    0x70611040e102612121909050a411b090a0903140c01150504090209060103021605240f04030c030503040201200c03070f050f040b04090c03030509 64
    0x8400d60011101c8010b43e40e03031141c1d80b41141c0700c22151014400400c0d4080d0741441c000b4802100000c0001e03800030003c0306420709192440602480100c000180c1e0035140002510100c0d40c00601415480c0d400818007101c440d80309241c13034070000d120488914030740060703081c0100142c07450316512090703403100111039441c2690f2450840220000c41c025410400c1840440c2c0d10350704a420600001c4c0c00390820f004596070754844403009030712106c441d010316507480c4124100481030544240080c0811030b03051000101503000140703440009049141415070001d07007003280380214031004056a03040000d48801c450001165803040304401c09034070b40042090b00207020301504240e6a401160144d90710405419182e50940340b60748040d2040e0705216103030720507071000c07142d6004200e075000d955000780c405070418001f410718000007a04050b0071100000700520061322090400300283c41d00322400308280106002040040030040805000700c85181d401105254100d0002c01c0070150a80301ca1383c0207a0360 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 692121330 1250 692120080 692120101
    0x302100e06270f0901090b01020102040506070501050103030f0e182d010f24030209040f09050a020109060525020402090d120e09010f1202030708070611011103010803190203070611040e 81
    0x80c83c0c08075805088000180700e8030450b54807111034101c041c0001031901e074a42c030001d005d60b048848122900c1e0b443d100180f0801d035210007005050402ea060411014140130f00080e14100c4032081c841c07081d800e502c0010510400341000d1308005115449500200e00030f13403c40809494240940122640383c0c0c84001240c0b0041b4448503461a0010007451484c2c80170b000c110041e41c0840541a80300c0c1d04c4241031503100000b0b20031000c1a610590040180ea410b620015240d070310640e01980038400144021940c01e0341c180c191201d1511f1040c2410180002c0d440060000d0003003031140d50b08407201d405140104811298007107442d0013207442d81c1c00307040102c504100e6002024000c89840d50f074820380c10020319895110b0303170f83d2040c030040603580c5181d04c40d105923207002001e501010015846004824003000c1c00e1043d8041141941562440c43d030620003250350341d10030b09120783d8180c00100b1180c40001d1082c42920180e542c0458148030400450780300d904203402c18011081500d40300c10104078135804 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 692122580 1250 692121330 692121349
    0x10806040c032a0b09120a110d05030c0d08220201020a2004140105011202120c07080c030c070314030c0703060510050909010c08060111070302100e0627 67
    0x5101c01c1048450741150380318140e9030850045220151810750422034510548001040074000c8440040d450f42d10b28810890081400c40642103503421800132100418014100200c0c4014150746206c0f80c41c59502d8a40e1852141101c4040503005000c0c0054405900c1000f10b4081c8120040e01c03541c150721010040f0b6072100710600207000d82c0c8035080c0400040d0000c8000c06d60115403a80d119400c02080c40070600791040410000c4030202e4540052060350b810910004915210050450400e8945014400040000361408100c5540410f69108000e1141c0850720464407503004d07039450f404030506043d540d220b0350108580001d012107155913505000815641d00c00b803104001c0c0b140924644400000b806d010789140e44100144101040a0315100045801030425000001d041c0c00d02c040000c240ca02d004e44083c0c100902c0d1514920100c90006032401660780464486040c07070b2061209441001e8865000343d00075102080003411606607914042c1c0e00b02c8a0240348540d44501001c0228400 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 692123830 1250 692122580 692122583
    0x60b030c1909120f05060c07050a080c0a08040e0106140c0d03051008121305040605060f0906120106020c1003020c07120f02150c01181e050c1f0801080604 68
    0xd01801040c0001007001d144000c00c10060926004081d2a6039440c003c0100b01c4000f07542c032500c0100c100d001c10004101050740042d8060320a4188442079031303400e803913203074688001c6c00d06400417a043c10b60303003400e010f0720f21243d0340700490755605c940e540b0400216913024071a1801041c02e20035108001440b4204643d5160340301005400780414102c000e6005280140a00c00d0004c80c180e004981d085c0c0402021080c003422124103502c0d5815506a500c80c1c5401e5000399010f98281501081184c6408040d42c40308a00442540c0c2c44101d0b500c0815070070702880f201d01c2c900315642d04c0000740c81d07a000f09940611080a03076190700005204c013025800d900c1a184001f59a900020040003609070104072007224a104848410710000c880e00040c016040c9104180409400054010002e042c00d01c41e81003075041450000484880342d44aa824100340d0311030102043d42c0b195000c0f0304002c800c0c0a0694191070003482c0e2000d1070005a400001c0c0381a0081c5039000c24031150001c110504000343c418400e5 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 692125080 1250 692123830 692123851
    0x6030601081003061a09150d08030414060f04140d21090501020f03060315100621061502010b010c0b0403141303060c090e0609060f0111100906060b03 66
    0x16215100111200071005003556200e050700d80c4040001a81c500907410350700155000315017400021030411241e040040c04d0705000001c4800c1c42107030b40c1c41d034565040000e038200e503089881c0e9882d070404416036100f9580000c02c5000fa41d0030006030003140c80c5c4c41401540620220010700400220341075845202d074982c400440d445481c90700b000c1541c018620034090200740c001c1030f1004c2c0c59a07030f942a41c001e41d4000c03811242c003101b04041800c0c20404524012640381c01c401c15810240700b003082d0001c16000310401c2002941c600d00703c155600d050f00030142108001080b040740c2d5007607a44000030b05880c0a80c0103500b08240344103c0d61141c00300c8281c03203401205040ca251038554044e603000e0504221266814000d0042d0002098074181c0a4006c60241001080d102c0c920304008242529136041140210f007001c052140c80d444440e01190301c1282956201120304040c001078039103001d143c82d10840f0340300d06105141e071585150040d001251003400c0502107981c0ba2082c0b00d031640411948800b88 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 692126330 1250 692125080 692125087
    0xa0819020c060118090203012c06010e24120a170f091009050d11030d0815040f020f070f02190e0a0c03060e090604140d0e041e02070506040302010e0c06 67
    0x244c0e02c400740d4842014072200c000a00780036560119013035411380c1c1207284000c07508807840b013004a9280f0581070043c80d04005001190704010405207110009400404c4ca90319581c00780401990701300c25030000e00c00040200c00316200d503003d01551400c05d0f078411124203009003440700020301030209440400e04140704003030800e03c10000780258410581000410030116040c0058141c60701d004500040303001d40c446034040926081418030b80115542d00c142082028410014010b080c900300d1180010102c402081d86c5d114200000068003402c21100145900022020b08104448000d1900b46200391000303400160100e40340c402d040c80b00d2195a400703402e00c1002580c2c2102640c4183d04070404c900b030020b000f68995a003030941d081d00f2a82e20000d5030200c001c0c44103000c81c4403d4104040c00d280001d01014003e041d008200300714010040d8020f41c2c5511102c1c2c11482c0417050826824035800d001c6440d0344c05424030780c1e03407004c0a440c2603026500e001c00c11105014045010080d41001405061a = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 692127580 1250 692126330 692126339
    0xc04111e07021512010305010509070e0f10030c09020702040e06010f1707030b07030203150a03020303041a04120303151505031602030904050c031b070f080a0c080a0819020c0601 78
    0x2aa100200c00c9030b1024001d41c020011500c040b020b85a031034106030342c1d1302080d8110b11b041800c40350301900302401d55005810422814566200080d4002000041601940c03120289803038a0303d000d400c020640c0e04240c6020541119550144c90341c90b0081754103104940c0801c079140e450b0402030040394281c5410302014403200507610903900b420b030840c0b41140c10580d03aa880322196000261452000650000309103c1f81500c82200660807030401c8070a200594a182c1c00079503203204504c164040008100840f00f240c01c01817050b1070043c840c080c0c40b8040c074049442c006000300f101a0006440c00c0d120320020800c03030341d50501410710082c1521102c0c0303980c98802c12164440701412052003140b204010034052a101ca0103914001d00c021100207071242003500440c01c42d01480c00c5072601c034440512650380880c0b010504240c4003071300a2400c03595440c400104840000d0117220241c0991070008501c103400c0d9000f20040c0c86050540907014480c1d42d0500b41c00d0581c46240002042c1e5030142d0300511 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 692128830 1250 692127580 692127637
    0x50f090d031a1c170a0905090f01260a1428150912080411030316060b01020a05070303051201090209060d0c03061205011b080f040f08070807050c0411 66
    0x5490920040f4044501120796503d08080e4442c40305070660f09408508042100d401c000c82d58050642220009054036000c9a0310100303110521400c51041d1051356500440d800c0c00300c0000e010302741b00055a103030002c10f044c0036201940803044a60544076000401c0e400c00d1009060120800344800191000907032511002c00e1000001c0f181408150b41e07003481400111848008032420381c041d1104801c610342414001b41e03101341c0d116528001e420401040100c0c020203009051801e90040e000288079502d100101c0c600001800e0040440c0300f4002c0c08014150007001038000e9a609000810140e038070341440c4402d0303002d4007482c5d80c1c001c0414491640b101d079664000c507241c22020325000584c81c0d90307184511284110f001c002d5400343d40d51544100c120342c409212540810103402c100e40a81094010311400070703030092000e420703045c50a181d0b0081103004030403150b40580021603951141000d04000c0c0d21074004010981c0305d1460040681520702c40705099940c0100c484a00c09038614040180c81c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 692130080 1250 692128830 692128849
    0xe19021f0c12092d1a04120f0501020417210706051e10080f0601140d060f050c0406022b0516060204090902150405091612050f090d031a 60
    0x40e410302c070264101144c06110f00b1200310b50300c82104290700f500001070314607018125250b0070540010500b40a59030f039080e038071402ca808079080b2041c0a0425070071401d02101c0400c40789402811540005000031b0260b0f0090b40c01908200e07803405403000680710042e49010080c59060400e40e4550910207840441c1c650703444544d101740340030300030581481c820300f0704240c000b001c0380c0400744200b5403c1d0074483c0d1582049178100d8403c4200c0100302650618100762074071300010901340d1044200f2003800c1c04020491f0000341030044100f2091106061040070502d460300b140c01240d0061066030100d80140500b59021040714151180d0112400d0341144120750130b07030100404c05110803081c1e07103010000320248001c200070039545100140d2282180b041000810103281004081c100611003880742c1d0740c643c0340c1c0da504068a0030a02c480018444c03002d40d8900e11004892140e6483e100810120300c8015001e10701c90206001134404011815000740c007102c0e070748070007082030390746040c0780c55030341d06002085 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 692131330 1250 692130080 692130113
    0x40f060507140706050c0709020306090402060903190303090b060103022109150c071208070906080a0908070507051302130e070212040807050906040e0d0c060e19021f0c 74
    0x40301e410a000603102d0b4a440c00310b500102c0042c100040d0542400c005210060140c1a0f6540951850400400050300d0001c0544085d10a100c005074403541d0359010000c070120000340420000e61020b403810040c000741007030201500c40603c071030001580e541c0f1910880b82c000116140800c810f0590042d0a140da070380007400c124107441241c001503641303202550002c0c8210040400b040c1d071780c41145030600410100300c6205040c08591000e008405800414080c00c0e0b86107490200c02540e00c0a410381c002d03011241001d4400c181c00134400341480340103d1800150740056034051404054034000d00224400d08440c07a5040b418030b001070010709034500c44181c0203d60b620485840003441c07529151944c1c0176a001940903400341804000c141007042401e170307011a044600700240c00c4490005500c894000c24028104401010400708002699216040b0041620300f00c851810001906140c40104003000340d00c640e140f40d8192405107041000c1402041660392102c10080240d0b0710f4100c0d00d0040d440 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 692132580 1250 692131330 692131343
    0xb0415020d020c0f011a21190f03081f0b0c070e0c181507120207180f05060402130302011b0f030c02120604030504120516091d03040f060507 62
    0x860080010600140507400321280140180c004c041c06040d007183d400351100702189202031034a0120740d07103805924528110058525404540064005003052100c0c0f01042c01403205070000c2091221013145002c04a100751071720302080d10b170000307450baa15030051495581019541000c0c4000c011403006441211905421140c080d5140c481484446d441207500b034800040104e1102000354044041c1c002544d000e1f1080308140001ca04452180d04c50110041c04a030604245c039070405208101000050500002040c0c20340d0021200c10050100d0450341540030b0f0801d008207040d0710346442100c203140d140001000326103265074010751b0268488440d8009101440740f00ba00850280460f03118440d11954814008103d1407040008001c025840d01d0392580c03000c0d04200000343c01c101102d054802d030481403d2032504501c0c080d4035207200300743c4401020002c2800002c00c105c00b50082c40d1042c1c3c11a40108884440408690380e80c001d1388115440c0904107071042101310701400052585901030326 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 692133830 1250 692132580 692132587
    0x61b1902010e01020301090b1c030f0f021504120f0318020108060114120414150a0510051203040824070323180c040902090402060a03150803030109180b041502 70
    0x80b80d2608907042680040c403025114114084181b0f89200080402c0d034400100d544110b56540300241124a100304445c00d200d000a409441180200003915883e22290301505103450545440043c613150015150041b0300000c900e600c45078042e00070a410701c41882c60418500c0c030a500111001c0d40040c10460502100038485400f860380a401094040b0855942800505152030054028002c120004205402410140d60200d515244150700140240d80108054031000b40e17040c90791103594040d6500922000c0c10070701c651000b1010300103c6a859094403001c0304e040f49054101c0c0e80c4681410b1342000b1803400034404a0081d80311010581c2c00104552951170071400e0114031400980d140c1c180070b011241000341d041010806042d404500f500c00344644085030b808501c03031800141000b840f8210108404419034400d81c008241c113240c03c0c100c150304580c0c502c8481e4491b072003800340c3c611007803e010060086950741e602c00c070001075000c82c0a83c22662143c40b5203680662007040909225001c0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 692135080 1250 692133830 692133851
    0x9060f09120a0b070914040e010e16050405060d03200c180a1116020603130b0f0f240f030c0a230f0108040b07030f050709030203061b190201 62
    0x24a00c0314424101e80040007004164100861903800003452001009035649080c4038007000510b080300c02c00c8050f04c01007406d0340702e06031341400343c03c1c090202003052191074210700c41d40740314242c88011103105540800c603030b0300d0b108140b100d10030740084003802007600c07840c40b0b20041c0d82000100180c180f210058641e8404036100180086c42ca49080704056080001032100310704680c4500c40c422814040c849181c0b41c0865681601800001c201901c100750100005440c1206801c02c070044641c40381d0181d00d180f0b00107044c0e54030f1074001e88000e17224549000010700c90000e0100c0040700440540d6201108400b040e003006801250800065010b005050701c1910540750b03400840050250b01c03200d40c2041c0180d40010441d0090342070a42c2c0310714400a020001c9036040b699071a042a04080002c6c0c2640c0ca808058014103500f40d9910411444c16042100f030a03804050a81030320320850903a102da0312089030000c130381701e180254007040c1917082080094206e41030700a50050259800042001100b2 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 692136330 1250 692135080 692135089
    0x115200a0f0812060406030213150e0f01030b090309060717120903040602010b031606050a0c05070303020c040e0102210a06031e03110d0504050402090d0605040f02042009060f09 78
    0x618001c40c1d4102e4042809034500c0c00003d1030b654480400e49003000300741c4c03442c0c0029500c14012a41000160342c0d0b46049600c0420b410ba81070f01411005075025003609007221200142e4500f48000d540d2002c50f030002c5270565001104507044540003c15040c1405110340b43c56071580f6914240b823281200070040c000d0001c0e9001d40445c030582408028584440c03074028003a0075a40c18030883da02c00d80200007903e0082e20707010f015400380ca6a51600540310040b031041034400144640f800340061140340c100000300359000440315000c00094400740800d00d03d140d0302c2400e03402404407a060860002440d000c0c001e81100120354030511510002c550a56a92521112031562031040340c0e020381c9541060041c10381103c4030340d5122007000300522980800c010700a119004a00a440c0b00b00e4001401e9201d03075503003455000c10280c0102c000c01003420585081c1b0021140540228041d90410320303903103c5040311851b5260410f00f50340742503107040000010040c0e40d51003000d011103203402c140800d43c0142c46 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 692137580 1250 692136330 692136353
    0xa0504030b0a05040b0702070605030c0c07180203011d09060406050406110c06250f0503070909050c031b0405010903020409020d06060b0d0f0c050f3f0115200a 70
    0x6920500041c141420708000c45c2881d80200148103650143c9010000507501200322503002da04a0042c6440e4020045040d0407c0c041b075001528140b0314903402c202c1d012650b030095040f9840f02da02900324030303107031030821b00044c0c4200c0d4810100d41004000030f010600369000342e544184910b0000504c5002407000290300c0d00500810380080e4031400400541000d5080c0c103e4211001055481140e043c142008051f031541c00c110340200113012000c122014010003114001d0131003282e05000ba4900141d9070300d060307013088860803a42110360340083d41c0c00e460301040301c2c19504186d46131007040b03045030244005048014412a00301000c0400380000ca102403260f003019020400b0656075903e100015101900c00001d00d05c0b03155031408124080c01c2d50024101c544030100c004d600c546482c11508030054540c207840d48032030314600400304030b032558006100481840c41003a0320750f4016603e58030441e800626200c20b400100b02c40c2d603480d0b001000016040081000b50404440203400326640b42e090303102 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 692138830 1250 692137580 692137591
    0x804063b01030924020a02060a1a0d05031611012613080f04030b010303111507081906170118050a02010305061906020a12030c0c02011d09090f06100303140a0504030b 73
    0x2a07006c1034440e212903052040750b40040d10160140300d071010380400d40e092a954900b2952245810310009401c200043c0182ca00310340380180c1c001c42ca52943e0820150342c2d07050102190000381110603007174904260755403007040ba994106100115954002c2c0c0070340004001b0304107642c00401400502c150404c503100807c0914441c000c210706952642c036010348100c900c84a00b882070341248031000034108a02c0051540400341d490101c00c0c50300c1c0c8c0031404c062040d0b4028100300c1c803400e181c000700720a2955a50181c19000c020000c00c0070801d55148501c001c100500c00070543d4026141e060055032103030700b03c9900a180102130000b9265051070741d0085070381540c000c0c00580c02c10001c1d40207110420100c0503900c0c0c0c6c1c2e41014003440d010010f008241d0449404000d0610030300394414008070721810070702000000040c04021103810306042080c0e4622000030110701034070400d00007501811b50400308808481d41511014240c51016041d09456001110b1460800109200010102d003202d0030003030091 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 692140080 1250 692138830 692138903
    0x60a05130f0c0305060c0c06060d1e0c05010f02121614070e010e0112030f030507030e0f0c120102040e01060c0213060612050f0106050f0c0a0804063b010309 69
    0xa00d11316115003031140040040650400c203000c4018a90310118400d584008102e58803a01d4440300c3c54045504403010050403040c2421a0161707040150b000c0c4800c054807001d0321503100321414110100d03035510000c200b545100d4818423402c00380d922101040c05a85220700310349220b5490119080d480e040042d840084c03441441e40040090010003040e880c09850000d20740c04048030749803400707030002030649102002c0603034580000d80c00d288a81d00c11503a07000600c003551850000c6600142e51650910400c03441158030300c082010440051003110111420920710740e01caa0300c1c00c035080d504131001ca0400d0b07070401e001107000c0900b816075105541c00340c00c068480d1040e010007200c03540b04407800100304041561001c030041c00a903400c80141e400c000c5103802400d0ba5080e1101d040c50a01c0700300750004018990208010443e6500710041003c031401d00007072600d0071038004100c4184c0c10086980b0340c04002e400c040c108440d501c45d401c0704046a025821030400b51005408101e0808180030303662821 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 692141330 1250 692140080 692140103
    0x18030a061b0f1b020603061f02010c1106061c050a05030d05010311010804020f040b0402041d0708240607050118060b0f01021b0f1212040603060503060405060a05130f 73
    0x6103600a194006000210700d00607602d00645909410303803c001d6040644189404400a143d5980340401c56501c000b4400d9003060784504444d000e8081d201242e0740b000820705030000c51107410400148584242c2000b0700b40e0704030740c41c03204090030842c0c84c818041c0d40c0360051404100203d0410401007900181000300007603650300d541003042e002d8940e8000241000311180a010241c0e4800d0207442414030704960024910301003c0c0080d00030303c80c0b0780c40316041c04103c90728081c8180b4165410b500ca0130131a2511550b9940d0b62440c03441e03030103410761046050000c9028182031803c0110280a000f841440000340b5105c14286420a01a200e08102d80b01610740c01c68070880d04090201012003182800142207480201f06a80c1d00c0030840000c1c1800b80780001000103d65a0b04010800d8408050054403568184413405022a82c400c0c010000441d041103000542800c0c00110544241d82190251220352205c1c50500007610700602110041c5583d08003400208044803100302c149803042589403103 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 692142580 1250 692141330 692141381
    0x709050f0105030403170705250c05060304120311220501111b040b01031808030405070b03041e050705060a02010203010f05030708070306151d060102010b1518030a06 73
    0x4040400009410003405005000000303800241865060000445011195070380c80c4048800b4026920006070f121014a24480c5600c4204030000319580103100c07400f04ae94452041c0002c0d4403050300c0040070003120b5001803003003d1080c0d03c40314401200900d0585089500c0390807000c542450752095400c2070041000301720541c1c00c603010048075008400a0209000ca9405c1c002c03807020a0040580200d03250361812030541c2c800e60005a291034260240d151f11405400d01501d2b42d0000c0310200e50501c6000008075901c03400c0801c0d00e200f10381c0300505410210700140511180a52084211136610401d440801d01d5a80c0302c000d040018000e031300058596241a9001040c9031850380a18080d4100007420320940e0340c041444026a0741081e0080340c51705035005440d00f54100342d44000c1f12000d12400d406940c008850029004001c241e00a100301400c2c1c00411090b0038900300000303192001009023501441045580062012005040d10b1102000fa260f000548a0800b01c0c4051220725107a000b5 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 692143830 1250 692142580 692142589
    0xf0d030e0325062303010e0a0f090f081305090c180d0201020c0613050a060507051c08161106070206010f320310060303050c0d1e08071403070905 64
    0x40c9070040403a19100700201c04454811000c4580916410071000801131210500443d9000c0092044403503155902d40e07440c0e075400a10b01095503180c41860078040c0c09055940b107130041c05d04103908169030303a116040c0e654904405034400003040401503038000c80081c40d5039a5140c002d1103031407a046c4a135911100c54a110140f844002c0796244265102000d60300540d0340020710344016801a40e10700d80d02c4003584540108058254031060780b0214040003c0340750f03684240948030fa00e21a404840e4074820b00c04c1e0400490b000c11100c10005050540014a0015207048a545641c05030502500c0320000c403c040e8209041102e0300170140e842071004118010280c14030300028040480b02322201007441c1c00b100900e8060f2192000840700500701c0503666a81404211403941820004000d0755943e807a000c0c005801450b001804da0246480a42c01d46020304014424082104c0d41084080030440041c1c40045024007100100100440c0130384c00b11041500450140da181d46403401528500700800 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 692145080 1250 692143830 692143843
    0x1090513021003230c0304030513030f0305190e1014040b03010f050a15020613170a020f0c0a12080d090f060b04060b09030303070c020102121b010b0406080a0609020f0d030e03 77
    0x10f0301081035120170011a200c0340703820340303801a0b854644950340b0044a8801c00303040142e1781016001d484010713100400c054200740281800c24040b0408109901c141c181990030a0f0015a11500401544180341040e48201c40003550781c4203100c0480c2c200ba803101001e50881d042600304080710400c24006206030b03d442592000204009a0711202c20700800c80000d4807018098110280b414201ca070700c0c0c04110010000c030404040310703200e01d92100a071600095403458228950f07502c07401460f82c0400141040b0707400d0015a949048030410b600c40994903006e071075001c655011001c6654801c40400901030000c003043c0a4090800426a240f004040004451046c2c1c0080c0d0540010401c400c81030320040243d070390054072030514818200d69400141d0800707419580061240740700152610303041210485c500c0e40b0644580081140c3d5050310248000c0728070a000b01086a4029440000010b0080d0800e9591780c1c40500881490501e00010810703507064250210045803030851072141904081012 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 692146330 1250 692145080 692145131
    0x130503070f0308030405010219020c09010503010e0a1b05061b150417030703110c01020c060907240507050d0804060b04060e1302060f1204260301090513021003 70
    0xa4011285021600075010700a03100042c031040700400050f003444020342c10744180e01c51701e1541c11150000c50303900a440b0300807244c2251040740c1160020900d07041c14842c0551090149004106100740c0b0348649814082c040c1c0e8200c441c080d00c1d6000319a684610025024460303000c03d0740001f89007400c02c00e60400000130703c652440c030050000c02000c244125440084007002020070b9a880d16170400c11000742000b450300740345d0b1650015080d440c98030158024441e107007000c5c0650703505880b01c203ca282c8814252103060840c0f1800c00541212541c440e0011802c2d1409040c507504d4141d00b60344007410403220720417140106e0075501c10481800214000c8504091044a08110b050b0074198100c0740c1880241c414460880411040c0d01151a100119001c0341100a540d0391100b10305201350b0b8074840202c608403041d560050a0700b00d0743d414454024074591850140504680c280402d400013480020100045145050711540241e124140d407821002d00641c0c010815516919005991a00102c01d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 692147580 1250 692146330 692146333
    0x3011412010c2f062706010f08010606030b090705210c070b010503011e150b0403060626030703141b0d180305100c0c1703070e04061d0405120a0302130503 68
    0xf4400c5509402107800c07907204a208079100c20301c8000c8904001e0007000031015410a2084d4000031a00e10445100c0c1411100890001d00c030054070741000301c0607103421b01512a00b041490020030401401407018042080600381c05400a2140c2c80b100f02c8020020784c3c0b0b0701641e0800040072003e00c58503080a60162200b0340080c8074810120a10000e1181403040060100d5a01c61340903502c0c86294209400504405100c02c0e15561a4100040201641e20800070541030880703000c1c00a034031040301d1303040d1180920091810032100d510192400c8020070380c07205034800d04001c1401400310443c8862154002940200300403040404080c1107038081a0354851194020201080004c0740000e100c100114245004208041d0002007920302d01864007008010260203030a108840200e400690710801c80c030341c2c0d0900064030785420b200c1140c400e8000c002401580d0b0881c0c0e000040001d2007680c20900c200c040300c1c142c1045113280903c980011500170000ba4000400782c580070300d01d15840026290880 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 692148830 1250 692147580 692147657
    0xa140403021507020f010606110114060a0b090d060c02011401060207080703150609060605130e04020904080711030d111e0706120b0301060b091c0803011412010c 71
    0x100d0203551201280c1c000d092001c0064009844184240078504032a0319540c0244a00c2e505e034100a80031070710541d00b000c150361038212040d0144c1e1040e45101d00030b0b04050300d8032203c40d04000010704158001e145440d00031120141042c0050b0403485080d203c40c10a07400040c032801a4020b8044180040c0d0040f400c5502c88803042c8072100d000300d403c0d801c076940080000b420b004520004006044507074404800940740c000c001880e150440014480b21904030101d001d40c1c0d40300d0480d0300280324141d0340a90071880c51000140000d00d10720040901c54010103030f0200010010340001d151500d140c0c00c40340040c0b121000b80040f00d604010a4804940455908611100f5843e55641c1c0304020301c12001005500001204103920303c1c0e0100c01c10f900017400070301840e502c0b451895515409001d82900810000030308909426000d02098880380d40094a10700d507918210343c00d480140030352425580f00c0b15408a1900e128024407400d00e00e5035503600c5220300340100700c20910b0700ea440c4142010314802886d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 692150080 1250 692148830 692148833
    0x30f0b01080105060a0f03090c060507050708210a02150109061502030903030a0807170403030b090606090a0e060109090e070e0601020304080c010c060906021b01060f060c20030d05030a1404 83
    0x802c15241a10540c6c9451030b419581420114050000c101002c1c0c030808003004003080c840d6000d0b0013061803602940455000d140c0e0b4540700c50ba10001c0303411030741d680f01f507114101c510619800013b2403001d5542c03040300c2c0107583c039200250740310f00e081c0d00c100c3c0d5040e51080100a840a4034020034009801030010f1420042c0c84404030b238403440352440c018104040344002903c0a400341415100102001200c1c141903d01403074060014014001410b1203640035200040c1d65140100440d149000050990280d580c5841c0e80062000301c040d140c076050224181c80400c1b0030046120304c41400d40d10078010f201c01c51070081002d400303e40280c001811500300300000d02c1000c00001d80140b424000303181c440315003038081c00c00200901c8916801050380d400001d5031f00341000f605101c04848580c84000304156aa65500780300500f071140f103081c1c040764039040c0c0040440e041d0300313041c4060405d2180d007244e00d544413000030303080030100101130011507400310522007502c1840c81400040302410603c41510701b00b5 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 692151330 1250 692150080 692150089
    0x106050a080c0a091d0f06090705072d051b180112050a0206030114030724030908070b04050a0b0603070b03180708070f08011401210f0b07030f0b01080105 68
    0x14004016031400040340d2000034890300650000b440c80c40020062002804622000c00000341e82c001b41d8080300b0b401049403440c0514a00e401074a1680303c4d00d10b03007e820b075605031400900800380b00f403030b00e8015040a103c58030303408800622071194000d0040d070209424818840809a080b00c5d0081004031055030b09201c039075410303038103581000c882078010484030300e0418039007201a0b030025080b00c80840005003200400c007680e07000c001e04a0a8441d010340795803d018022f43e28408002807100b08c580746514183c001d0388040400c1d80542842480c0400b182c8030594490002da40480301540401454800e01c414402d203941c0004c001c40103014014a031130a10005404060050102041d000c0394154031914100310050040903800c0030f85000c90380d100c4010585120074400c45003a9400d00320108004854515114181c51032060548810340d8841d28440100103805810bc404011142e0b200001c1419517100c58031030443c69034007040032003900d0174980a8501d00c2103600e050180c001c0040c040c0307544 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 692152580 1250 692151330 692151347
    0x50a0b010c17070204060e090d0f0e0409020a0914060102061e010e0606090d05100e030403120e01090b030a0510060e010905060d09020901030b04021008090604030c06320106050a 78
    0x400100b0b80042c0031a250440d11188a40d0000030b43c41851300b07000050f0001410354080c820b1410f20150789a60040e0802522604260400d0800042c01c0880301d071203600c0c1c00d500c090320643c005042007103060f886020301c000310f4101c082c00020040b1749600300115580c1c100320300b035881240b907600301c15180d122080210b24868180a40c0d0a5820300c1e100241c0c50742c4800d81920100c0100911001d092401810910340768504030051200150400030008640800082180c04690744000255003c0104c210100d80d004205440107040080710180001c20680000245004101810f40010700d0306128203280d08140060380007009110120342c070805180e03000031a00c41111802c1d100fa65030340780341001003c003c101c0880000e502aa60000110500c0b02e520b41c918030488c800d4501000750f90011000351403159085500c4410369001100041c00a8401e1003103c03140c038450040130500803641c1d44403035010000b4a03110441403ea030012900000071501030030340104101c2c1070541c03030240c41c540c0c000d00880c0c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 692153830 1250 692152580 692152583
    0x13031a0a0b0105360303070605220f020f06070b01242f013803060603060109020a05041212120204050d14070b281b06231801050a0b010c 60
    0x1d04e4801c6420030001524a00009403400400352940c40c207d41c80d1071001070406451200000c56080500301e022090603140323603480b03900004181d5070703280c40307174208800c801c401840310350448014000c1d240041c0c2402e0300e56005e030600414030041c0c00a5014081440b40007406041c04100c004240050800c403400e03007200100c8486142103008802905885001d400314400600b0f89402c901c030868440b030880c03e000d0034001c000f415040d598200a500705542d0343d0042e610644d25400c104010410155960f0041c82c0c0190706003050f500b81960307540410342c84c0c1c1b00300c10190781561f800385000c01e94035071129a83d0501c24400a003107050508240200d00022510540101a402c912070080c81024040041ca801000d0000202d5038640c8030f10501001004181c100c00c804250034816030070390a006000151191200c0c00002c1c0303110b0703412f84070200940581c0c024000a1440107001070302641800360958440d17401465440300d41c461400c111801c5900080080c80800c1c901040740c0c102d41c1e4080000075406 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 692155080 1250 692153830 692153887
    0x9210e0105030718170c030f01091106070f060f090201030c0f1d040f020a0c0201090b090907050304080903070b030916080c0904240f05010e1b13031a0a0b0105 70
    0x29840d044c880d010882e010f070020451060071500c4031007080c0e40000d4001451409500750380320140040c10351800d03503000e040009d20015201c0409203075828440082c140c424050300040456441d1901d40b80c0032135a1040c007009405803641203074400d42d40c00d4052828807442038034215a1544c0900d41c0148000302031801c6500214800c04200c84680c1c40747c00a0901842c54101159100c0daa03a40107841442c2c1c6c1c200480c045401c405000403080b01c141c05550101c0000f030125200360b900c00008507080c0c0c1c070007003017150381e00d50500234034000d501c04001e443c0141c05184100313030341c4e4104210002c2c6005590489a00459041003050110080225220940d500252100c8060f529645400400302842011881c62a42407091101d03d021603604182c10181c4281d034104003070707603c0e01510b0300101412100c050110b0485441c0f90200702c038941c0200b00140f00008801035140d220354501e65242e0703064884040520000b01800441d064911405043d903909007401440c1445100c880d8854032103c1d02102c000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 692156330 1250 692155080 692155097
    0x5061204110d0b010f08061b2a0a030206010303080c041206090203031210090507081317040b12090613050d0e0109032307090b030c13090609210e01050307 68
    0x180c0e02c510200b400d610380d2214060003950707103c01707071809500751610484003240f04a10108000300c64070500144403412003100285846283c11078049840f031181c5004d0700c0800061030050040e84280049c14100d4030039070141030341e5403640c10010903140001c1d041d50171011003000f0800c58069141001c41c810b03903010002050041550000904500030100818072201c40101000b8144118140240644d80040020400c40d00c030340e44211200e180454072480d20091800601000c00d06d1441e205c0c103103e08070302c0607514064885800c0f94242c0c009492100d50068006c040c0505101f0602c5131a07800446083c6c06076484242c2d40b11203545160300c888000500c0640074000d02246d10070901c2602454000a4810030101d1441490307801c0f02a01038810064001d044012903440c10b41d01507000410301c01001408900c2c1c640080002401d041d00803025101d650300d0015002450a0040030b21060262034040d07160741c08a0810001c40c00440c4602c4108480c1012290141c0c0c1c0107411f4030381107111850410032 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 692157580 1250 692156330 692156363
    0x28061404180206120f0901090221070b0c0a03031103101215020a0518030616050c0c120708070905131e0b0c1e030606070b19020c060a0605061204 64
    0x4148001e20001e50404800205501d9000e1074100309030142407504650400e5581c2c440c0700c942210b50300c0e11300075030140c2c1907511208505520301500540c416880d055035540b80e550002c411a913845405010169041341024105150705845500203000b0f001007850318628021185840c410203500030508241030f07000782c1c102440303000010514441144c1a04559540351303a8000f46c81070700400b9050099406001d15004c20381804501b203401100904008280080c00080a40f095049200c040c0c156200d08458403140307950f91a8800702544550020300101402c26003403a06000c5103030000804141000c0902c00c1c2e46256410b207628940c3c2041001050708160307184010400e014800140c1101c0380e8006101000340c4180c000d03c080c00314400c44000000c54084c2402c1107000032541039034000b500344120400700c2c0021380003690000940400c1214604404142c504a800940ca610015801401003141840c180e106410203400c0c219900d50400c01140580f4650039401000102007110410300c00300c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 692158830 1250 692157580 692157611
    0x411030a05371a03060f09030c0105010b0a031440061409070b030f060406050303040806070e010305160c080f04080c09070f2307020928061404 63
    0x684002c00c01a0390881c40b041551541501500a07080c03800031481d00340d4803070400381100125445400064090031103681d40c000983c12040c40141049518042001560040f030740031700c90b8070f000e050104545600c039200608010219000e0346a255140d0941d8818801d00c0d460b180501e4480c00407504010050b180740309030281000c018200340712003c4001168003401c000c1d042d00295a01d43e80c401100102e55a41804142d880107144203421802104002040284d8503c981c2d082d4030030300142011503059560342c042403959001e544148400e0b00104207000065501c0204407200c04400d10381800a4100100303d2418500c1204c5401c0c01e002c40036039004208921982558000c00d04945207648480d40e0b0142551541d20303102e03800f4491400c40000075445802890154410310050350b4400c504200104000c40c40344518002c1007461030b09102c50b90051765884c101600c60000b45842e221503d680c00b1840ca0850031034170000040c0d9040a00034071443d0180e034624503810500710707004900d4001810180 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 692160080 1250 692158830 692158861
    0x140601030201090b0f04180c030b030c011d061902100608060f06040213091803110102120609090a0213060306050612030d1503060f020712090e010b0d0f0c0216050411030a05 76
    0x1991b19001820b54008075200c0c55102310074000841d1030034014000700000700364503990440c480c680030520100010743c0089030349240100c0d01102800041c42c100010040013488000d015080c40140c0c020f1142000d55000e5006120007031004100525090510000c0000d2030030008040500032607000c80c8200040340c40f81c401c0e400411030802c040108681200c00301c02e14400015095010407a04452405003203414400c407070441c800c1c40383c070307524540700e0324204080c000300900b43d58514854a5100700260b901c03004c1c2a02120000b0b080002e12901d503103050380654400400306881011180d10540d90f6a4011085a03074100c410800010001003042d1403004002c0320b900080d103d949404109489010154003c0903101e004039503002d540d1141c00b6084983c0c0764180a003405500341140104142d0700c001026224510f2041e5000c18020302c1505124225280b55480300c0c0180d01c5500888290140340a403040034080590b002d1000890040564016100103410140e00e00d5903100010042000080303403 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 692161330 1250 692160080 692160089
    0x10b011b030318081308030309030702210d2105190e0a05120307081305030405150f13051e0a030f030c24060b18040f0605061204140601030201090b0f04 67
    0x7198405240c0d00f0004130a0b08080d40c1605105541d260105540d14004143ea20400d5044c00440c90b0054580c00e1185c990301d8180360301c0c05003d02c194000120001400100704c0c0382283da80f03505045201c0c5940c05048551807181c0c02180f440d140501888914081507056000440d042c0810b5585148542500e02200c44401414a00a0b03800e01307020450344034011030051b02650707525542516074009103145004a040028802d43c030812081009007421076450310035008001039142003401440340c206035580019180402e40b082d50f074050180d8948001e00c50140e882101703220002081640c00303d0654262030101070203101040c00310f0401c0621a80344021071684c84024003600052901f0300307500f0b50842084004001c1e00303021380031426602a900740e035170f1007032604440d43c0300d800090b00b03010003007420b41e981131021501c9110202d8552181c80c020404900c107441c0c81042071030542460039821101500c1c18640e0742003040100f000d40c2c0d00c4040001a2241100c0d5207594451150300c0d80e0161055601 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 692162580 1250 692161330 692161361
    0x140a11030d020f0304020906101709070b160c061b02040f06051008071b03170901090204230f04050705090a020c1006031b0312050a0210020c0c12010b011b0303 70
    0x81000f00c546000000e54002c910903101c40040d615224104041c0c10032102c611350009251544c41010010309500b8550444030742c2c1e080d15011900c40070f81f03030061b80c090060b800e803440c0001d41d68030800c40c0700000300303000b4051450700343c80c0040c1111424040c0c124044004c2d21036510b40c01441903440051b80100020f0500a00402046906040c007038550541120780d0400328541064401890100d0201c80c4403569040c1d6518031001c4d07100341c0382545801c02400300f203011b40d0303103501e54801a115485554490145483c4210713021244003001400700c80000c044444003d84501408001a000504001070b1081201c01b103c0700c2d13940b001e80710028000d12200d0100b44c4200f11985030103900d85e600034010b50b0f0148000c800b8410401c00c54001e040200d01c402009202c6604c0c068032114420710182c19000c4842c815189214428504003060381c1000c000c1060030741101c10150310381d2910407070360403107815140001c0c0281703104400083d09014140d14280035690070303400c001081502c2540402501c2c0c8a011 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 692163830 1250 692162580 692162587
    0x7050f0601030615120201050904092102031b0c150c031227011506110c031e16031101050304030e0316030b07090302031b04060f0b0a020d140a11030d02 67
    0x14100081d0010b00c9444904c0e50002401044403001900000c54650301a11060300e0103070740e4828400106007070b00c0140c076010840c0304850760802c005104544c0e65a00e0b98000c41d1280c4803c05081040c00c440f54a04002e94403001c10804207484120244000580028060b40c603580c54086507030440c80342300003850201100d5003c200c05802c491030000210208803040075103c100843c503030f500b251800002c7c50354a00050030200304440c8a9007100001a02140aa0f5101c072480004246404520003843c2400d1a013151001c00b40a020020301002c9038001c804007407002e01c1d544403901d445444909160403c500040041e0606020750106079008c2c3d03006d001c9403040d0740110280b00304110303a40800c44001403020302007040b071ba2298000d9400c6d240c00402a0500c802c003103031100000382034400c81035049030703c40d000041d54500c2404044020721088040b19920000c10400906100d100c191060501201390000c01c0260070b40015a0b10410b91070034400e40720505c40e200c5030320714003512401d81103590001 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 692165080 1250 692163830 692163833
    0x20c10020307050d0e0d0605151806190b0d360501060501090503150615071b0806190504020d290906160c1b030311150606040b07050f060103 62
    0xc000d009141c0900300b0703104500320544c02200c5a084210303120743e000f0106261403003c03c0705540080d400c0810031032001d008401c1c85010405e03c5589001011505550404205003400c0000c5560251101445040422800c15120304034900403c0c200500c0c00c0d503a242c490501d4241c030105c0740003d001000d210369154001c551506901018030707038101c0300da5003025000039095004100a20580780001c000c0c0102ca84001d0403c40d189400030301042d88a400c00344040c0340140900700420140e401a503041ca4100c1c6510040c1d590102c0c140c2c010352042d8800005c0200709800c100c82c00c0040ea000300004512500e4500000310184500000a00404216401d451800ba034410880c1000412012112501d5031100f240c1038440804941d5018401c0a450780481030501c6009805c2000b40300c0c03544101101350713861015850b01c0542e0800c07000718110081c0d1041c940c00810108028140d030003044011840c004000c039a080c0039900ca12070054001040d1841080420711281d1041c0c0207040440d03c02d981d4a = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 692166330 1250 692165080 692165083
    0x3100e01030807031823030307080d050106020f0a051b0f130218061206010810031a0a050f0709030212120c0a02040e030313020607080705030c01090c080d091203020c1002 75
    0x1030343e0300700d01051807030182a00c4030b01c0124603a030803142c1c01c0186c002e00c00780c821325000e6006008202c03c0d07454081004500000703072200c0040c000c100380300e1000140d198100a0040e1400100400030039280d48103003454400642c0c00999010b000c0c181940d03038060010910046402d9030815054203a20170b00b080101505280c042d4042c01c031944000104100c101c09100030700182c5d00c01d1004141d9038242000018000e5400741252580100c00810f40ca0299036494030781e000860311300100100400124803c1c09400021030042e80c1d0005600700ca206451b04000d2409850b0090510000b070043c161590790022650092000505c1c1c00b9411803900e076540a003c003400c0d1903849040341203100d107181800c40008501c0000641e40f05007182c9101c1041c01d0929000c0001c6a040014115441941001800005582480074180c2181c0900000c40c404140d131500100c0160141c2001c201a4030900c00c1c4090b0760b5100003540212014000c58042004080c1000ca040000161410f60401001c80943d403801d0b90 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 692167580 1250 692166330 692166337
    0x220b01110d0c0c0b12010902031308120103020405060f06090d080d060314070b04060801170307080d0212010816030303020309011803201504140a02040c05071e08070803100e010308 79
    0x402c0c080c2052031a1a00000700103401191760280314116120010701c4030801a500a50b080f00c11480544203c180320381d5100040e511892026449034a503400410031401c290240a810040840d60252480400780c046503007030041c0050b45101d241c0045444050094400c01c8a103101c04070b25082c030500e138407400c00c5500ca88504801c1d400d2480b030414009052118082070340c0a0380c03002c2c0d841200c1c036460308140702103128000d090080c003400104410f20000b15403a00918011600420141e100d002c000c1c0c0205040030142c1c424107141c0c2203190014511451100100e080c4d070391505005859881c1c0000290061403199241c0d841003100c02084014507401c481003d80340b0121348018424081c41c0052643c85000401080c107500111300c0105000070a200c082041d500c80c003404441e450441500010181c8040c00501070110ba00005c0c44001e00101d0540910b60085810b0035287c16145540e0301c1070584200700c00541588400300c042400d5220042844004188040c451952941c40e4280001940d1 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 692168830 1250 692167580 692167583
    0x60504030903141b12032d070b15010c08190302040b0c0c10020703120c0201111510060e210703080c0102120f0402150c1501090c0806220b01110d0c 65
    0x103103504c0030500700b881d24545515240d02402d01444c20444082c100030303020ba200c03514245011020520b10340c892100f080103803401c140030381902c040720300b8000a1100341802c01080d45041005a203426008601403808039504901d1a082c01d440310342c65410100d000340034075000b4074402c06000880c2184c00000007034017410110100c4041d030a405c1d988000380c2c0d546101348001410310049445031003006008521414600c1d0040c14850510f542d0500514148881d9120015681c04404240100c2425803c1c64001070001400c1c074242044c075084c0010406620403495688600030490002500c032000c0c03140c10005c550022030240c4032001d8914180c0030390021540a0307406160360000401e01c0c0b4415000500868000d000352484002000d91920160f01c20000c4075810f20603a44600e40c2107444081081c020052014009031244030581e0040c44100090b020600c114a54000104002c105030328042e00740c800c08400044584080d801a07929240e020240d14440c0075030b0798100d650580140e0f00b4480c06 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 692170080 1250 692168830 692168863
    0x70f230a0c1b1509080c041a06030a0516020d02150c0c0f0705090609070f1d03070807051f020601180b040203010902130602061308070512030123150706050403090314 73
    0x100f60031022100902d44c1d101d030200c0f80d4820a02c0502508195004803aa50103540d5030200d0341c23078580c004c1401c5500c2505c4184a00c0d681d13004124211070f4002120704008000d1010707100103850202c00070f50756001d000800345921505000f003110068440110380c510080312090765602500e403602f10752241e00c075100f028090300a4100086480c41c001c801e00c5d20604480d21004480c07000c8900c11244240d402112006100080610030000e69080100b80014071009004000d001d003800244600c2c900b43c0708420652034044006a4600703900850500c0c196621010941c04080441158001408c540200e40d50068030000020566002540080600f40440640800444e40e184402c84e0740316000c9803032707805c0341e00501e1016000400e21030003000030a0082003126805082c602c440402c0f94003e034800f50010b5540741d5098020000f100c0701d01c01e40d00046a0701c100110390020030000300c3c4034411005040d141d079040003600700b60040c00c005014503000b01000d440108124141a0740300b001d02a0f15404 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 692171330 1250 692170080 692170109
    0x901030c060e0f1507030c0c29120f09070b0a0c1214040501031d120a1b020109030b270d17010513020a02071203030203070f230a0c1b 59
    0x1182004404410b4090002c0c00707003062200340ea0040d0459805c20401141000320201d600e40125114061800180600008005c400701d20941c1b0404810760303034413150f000c502d0188048004142c2d40030311540d204038000c3d40a1403945c2c0c4c94031103608002545c0c002d81d241c06404070310710600136441808040140e100c3d0049804542c6410000c0e030321040c07144c1388043c10070381c2004280f201d07503c680c10000001010304964200d043d41704d00360f0f80c10204540071380031902c5000b18030003c1c05a40003102209880c20401940c031100000d4000230030b119410b00015007400109804184406220303440c442820f00701200e0b1031030001c1003182040c2c940c0e0740250200c000855452003007071000410001036040380c00050000510f18040318540e8040e400c02e1580c1c1d01903001d1600001050b01002840028641c442d0340c0050b43d81c541000003070030564403040b04104003d0150400600c201c60180104444a440a10191501840c04080340d8440680d50024089170384d05500c00c16914510b103d0805840700410310503203 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 692172580 1250 692171330 692171357
    0x11010305090c061c020f1e0c07120f1212050117100c05070503030f041704030201022d030c0105041e05190609021203030603010f1a01080c090901030c06 67
    0x94980540740c0d08155000740c03202c0301851521038018a00746000305800c00100301502c0c401030032600000e4084088841c0000c8105400c0e40d0000c40c3e103a44800b00c480310303080210540e07500d69030ba00d807801000303524102c01e40d80e68203100c10281c00d0158907a109400c0c01c0d80d05240140140840200618080780d40c1c20301c400411080140c1d030074204000c070148020400e91414981c8140648107086100301400380800158001c01c10500c0214811440c5245101c194246443c00d1004460350352000f10809009010a01c0180e9010649030841d00c8801c2e002c8911071880301254551405900030011700e84030004041d030b06d054040d003040f8441c0340503080121840501e0002a2549114450000d18941042100e00e045002110305084030703a0064400150404403603001c11070707030b40315400c0f030301060307480802000744602d000d0085003000700000200b8428035030300380389449a40c180c40340b4442c140800c6400140d501040d42c016104501b030b000f00803903003c0d40c4d43e082c00407071040310f030140000107042a0440700 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 692173830 1250 692172580 692172587
    0x40f08010e0f06090c0105090d050d05190302070201050a080907090204080f0f07141302130f0806101a0702030109120c0507060504081005180f011506140a1b060c0c1101 74
    0x4c0c40780c420b51000d041050101c1d0700444803940318a1003154071000c1c41303c0d81c20200d0801c00c505a404400c41c3c43c0d65607a01c003205440f1150340000342505042500420001c40140d9200098504480c410b08100505480300e0044c0c41c10040c264000000036440480c0c00100618001000b03440840d1080544021490b1302c0d00e00c0b070301d440c114080c038445402c416048000324244045100c6821040c0303400103007042c044444442004000f644480c109200203442400802011302200340c214804d4964025624644000001e000040394407620b0100d101003001400e5450a401082c421030703001e071540c0d50030003007110301824400d0169802c0d2143d2050750804941c0500490440702954a10720042c1154002c04161b5800b4180c020240020104d10124000907807070b04208541e4103400e401c0011030100d4011140d14141201d0364400c2d0300300212442403150381d43c04001156811400340c0f400114492280c10102c5040d0640d003001046107251060440030b00760b000f201940703040d10610501038010b00c00310046 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 692175080 1250 692173830 692173843
    0x9050a030e011b0b0711150403090e0115020d1101020f1614030a0e400507020106031a2701060303171905150a080f06160f08040206040f08010e0f 64
    0x2024032510340045200380b40260b1001c501d110445049a0801d24007041044407d00c1c196001c0700400c81ca1034080c41a00300c0042c0d01030240c80d2854001c01158887c0000075610707002618003c05011002d07248944a400a404070790b030b90303105941c0996031481e11401100403200319050642d41c014103005020307098070b80403013114521595652414130080541c4200481c06040103101c858a1030b860f00c013144a902c18980703448100030300301400c0401c0b840d4100000d060b03a4000780300d5421645040b40a00c0011199080401c0c8030740b110b034003c0b1566498500d05101251480f80c044401030140c240d881c84042e0542018041e28801d58a42d180320750540907000f2200b4040e60f007030101402020712000140000c0c3e101d658001c4035040c0d864032140d85440482e81201d816004442c25070088040319031b145800700107064218890104208a401e40b810004000c40366119805081144800114040d9645c0c103054030090301c40c030441c420860355945400c5008080d04102808507000b01150301003161404a400d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 692176330 1250 692175080 692175083
    0xe090f0d0906050d091a04060b1002250b070c090b03060708060402071a090c01020712050607080a0b04060b0405011b0203190602250c0f03030e0906010309050a030e011b 74
    0x140074100341011000c1c0d41a4002040e5007145a43c1c038107004000c0740440103501c3c00442141040b80070781c1442d0610005035100300d2526405141c59420309005154001102420104600c1690440340400091140040e041c0d0788510102c0002050302024003803034124600480c3c600344030401c10048194189903c03100203d4a440104c2c94840008800c0d0400781c00520540d84070311541e400b0700d0440c0740d840ca00c000301078948202d81e42c00381d21007009a5030100800c07405050094444503071500e4550394103554403801850351003003000040115516203081e401c41c40c440000103105029090b190300608402e50020b2194900082c6d05900040c0004481e04444601c2038000d80600344010030014082c10481c0c0f40b0700101c500581c00c01030f140240b14618544181e40010034078035442c6441e9418494140035561300301e01140201202c0810000350008040c40900c41d00b5601011695035500060b002400c3c01d10b00a40b950040707421510816521281802da001c4090702d411020303541e99100c5800401030b0450 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 692177580 1250 692176330 692176337
    0x216080c0d02120f011a0f01080108030703030222080303070311070201020d050c030f1206030705031f0b1f030b011211040918050a0c05032811030102040803040e090f0d 74
    0x80c007025091030758031100b840c0c424500f21907807000c014601600b1580b2400c9010100522011200118502803201c0200841e0034644050254102000e02c0e85900c2407100082c2850ba002942d403c00c64500c8248940d01702441081d000300560f00c800640d10707688200c1d4410300182c9007250640d50110326006031000d6a406038002c101018000308162510f41c00399800031801e110500c4401584018200200b02c0300200003084039050070114181454010b450300024800d40001c0c41e40c00444c0003051039180c0e00041101c001c00c00c0c14904004c03500d44034070441101c0e0321f00ca46e401d941301050703003503000320410740420b82c0e8000020880c441c1c8a021980306040c4448080000c12040044040641000310820b4890b01c03640080341040d52001e10305480700340221610840620108a103180034030000205414001101120814203a0000003003020342c58000d0800c051005401e260303850940c1600c014106820440750b5803515520246001a001c441000e40703481108191440400045500c1501105948 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 692178830 1250 692177580 692177599
    0x210c050c0d0b040b0919060e07050406050612040809040207062310170f031201080105070c021f1e0921080a110c130501030221060c090f09070216080c 66
    0x2130758942c600101600b4280c091146007219107800303501000d0720400b40d2042c3c000150308410455040c0c241045507000c1e074413903031610b042085261605030468408100115900c8891341e580d241522170b03400f80a18140c0c0091020980c4010030555502412100c11001d807001c101d02c1e280c481180390544100c89501c01e0324001d840811400340f84e40024001c0b55040c01c252103c40300840c0c2031500c1c6800c420000500c0001000042005d054280f2480750001a40d00e4014131b4001c40380c010034440c100041c018a0032013a640c085000b43d82c810800003c0c96482d541c622002d20b40742c0803004045022a0268034500344202030140c02d207203100000b07041450350100d599030030716400c6401521440004003402c0400c0c002c9404024040d80e5000d004040d40074480d00005a5504500500401c41c501c400ca0302240b004841c00e441d01c0c0800060a50b510400244509941e486070401003110144403014458010700040240004180c0100d0070b00e40750980850b8000d00300d50384080481d5541d10070840142c01841c1c50 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 692180080 1250 692178830 692178833
    0x5100302011b030e06030f19060807030f030e151b0105190507110102070302010507030612050c090a06080a0c05040c02031e07021206091e070308030105040207210c050c0d0b04 77
    0x35200c2680e01d40c001d00b003103913454004001140f8240e0084401c0c400040107041000811500f042d201c8151340209801081624141070140d5a210114080644100b01c184a1102003503c140e42d08920190050520000b2101f401307184020f030340140e100d801c940f04034a8500c00080f1014880c1c240325429201c43d1000c2c24400c096800000c1c00e029002404115603066105440c00d4240010190b040c0301345d0000501e40790405004084440ea6000080268001c480360f40104100041024901108a8a142c2c00e61542e40c0c80c00002c002990022041c7d0050000b10002e02c0100000d480403034206071000e1100072403208003241c43e445043c0720416048007004401502c3c0031034001620a03980302034106446441b04081907860710100311a000345950011080c010f205024040074018020190700a040d10340c01d650b80c81c0fa99000501405001d103a01080000c04d02c400d6140c140a02d44800c145003060308110322008100c21004034040d901441035000440c500c0c148032461000e200d030054500c45941e22503 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 692181330 1250 692180080 692180117
    0x13062c06010f09050f060909040302030a08060609010503070f0318030c150510090b03150f0601180617040c320a14120106030c0f230d020105072906040510030201 71
    0x44441c0b041c0c1120b000d202d6103842e48c0703035074480307501a0303000790001c60b10382e940701e0001403501a0080042d40244000c1c0114009660071138143c80d0403000900380034031280c0c0e42d500e00700d00074030f00b0306840c22480780052030304400d0540144942c1001c2e8001c1c3d2001910042004d00007003079070400c1d203091000e200b00002c108240742141d4081020b5450090a440841601c0f82c4d0019114000362140212083c944092004540e0440b080700841c400d10342105140c10b20f448405030048504c41c549903032031981c0030005001c0004001400c2c004c1c19407205203280380d050080102d401403a0601c500d0064011828801c0c0061170191658003c88521084208002d80018180200000c1d0440c240a0541d00c40c000480050480101e00c4054030f55040122a80c92502d69100000b0713070824110014500d8880302660240c407200711034000182c082c06c000341d0b216034518010140d1081100f698406900c004445c0382d40d5800c1d50000b030301401c4112820700090301c1b015003c0c4103060341407000a0103d8104004542d14164 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 692182580 1250 692181330 692181349
    0x10807031214030c0318012f0705030703090f1413020703031b0201021c14040f0c0b122d010e0a0e0304030b04020406150c0213062c06010f0905 63
    0x361070402101000001c038002e10307070001c0e14601c40c4400044104000760310b0031a441d20300d0007404002400700ca048150a03046e007540012000d100900800d0142d8540b90040088448040d0b204046071f03510328460030010701d00c8000d40500c0d900300e10384500004024440c0d200142d090303a0010a46100d000310600d48200a40c8442030840c2850b855103090b0003c0b02c04a4144800c2218070707000540c0c3c4920324034090320b25a5101805a030901e140400301c009003040c4100e95984568004007619140300c0782e0802c0b03581325046502041e01e02c1c0000604001d442d0030925414050f800320311102040395804000c07500364002c121205202424074100410040000c410b20311340140c503c81002541c4c50503a03407040e0540c5e00541064a00503020001d100441c10140b08441c010500e070505140e43c05004007004112000c909400703071091103404d0300c4070072000f095030006000745001ca480c8001101c8040c16080c5210440d002240503850400002c0c00c40e50280c240058a010a80da501a51508140400c2010355 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 692183830 1250 692182580 692182613
    0x806090d0e01140a0207090b180105101803110306070c120e011407060207020909010b010516230a06112d0d180c0801060315050901110d0618020301080703 68
    0x2083c0500d041c40411600a001c501d03450780c061b000e01420204480103850314000d22a02500122280301d80d030160031003400b815203004507000c000525030050200c83d55072445402c0140d6040d10348000080040c242645041400700760b05580013690741c214280d855074076402001d444001d12880001c032070307403044041c1b03036000303030141403440d00711824a60368280c603080910103d5480e64009402c030290714200495079402050f460003403140103141c00c002402800b65400c40b81c088021b0741009030800c0243e0701d0911558040140641709140b0044086560707042103401910306902e040c801d65010403110f0b084600c41180404000d100c01d980181c0881c000e41c60b00206601d004003032003c1c01301600c203801200c80f4080b6466001100c03100c01e00700020b021086070300c403103001d0703140c003000f00000b031581040d05c0700c00100ca00c1c2c0040c19950b280b01260241003201c403100c45140c40090b01120030111944504140c03284014620b60864030030340e040c0101e11080c05503c030123601c022410000620700070b65480290 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 692185080 1250 692183830 692183837
    0x7181203180603200c120d0b0301140106030516081b04030512040f0b0304030c0f0f06090302030a030b01020c030c12030f13091107020904060e0f10050108070806090d0e01 75
    0x110700301003400c500300c0035000040007a466503102c4010701c0074200460080700c51100514944814003401582c0d076000b00d0024403441d5004039992000e2581d5034041c64603800c000d4028003440fa01156402c208820901601c000301c1c0c946004540780088070703031950040c01b2164440f44c03142e403101032515441d10701c1d01800c503119040410011001038028040d401403102169002d54440f404d04103000001f2086401000d4002010300400000c640c5c82081c03002110b03000350010203505110306000ea000c8001e00d0001e0140f50038040040c0404d0381c004014404070000b039504003c2c1c201100c00490300d6904e000b081030340c9035000503440340b5245814082102d0000102c003c82c1d00c3c004040c04d842200c0e820a0112a4160001640802038645907004001c0e00040d14401940303001c1150b40052544600a0400b8245980e520340503420640c00f0442c503003014492100315502c034030000b140480902000d0181c1e04060040c40400210500d000550600801d40c0e20098040010f9406040b03c2d440b40b80001d0fa0b041 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 692186330 1250 692185080 692185097
    0xb090f0c09030f070303110a0506011a0409020a200a030e040f0605150408070f080d0e0a0801090c080706090506190315090e0c030d02030f0708090405010e070807181203 74
    0xe42c0c1c0030004041420a0440039007035091640c1400350420b2000042054981c01c40d44034040092800b05a190548100c4032018094004846245541d0f01035a04074040395840002d001d504590400100888902c40603055141d00700450f400750348034248460700901107642e56110b000d10b1301d003d8001d460240564007000a0207030340c41c00040d0f015030105526406041e0005000e0002c00c0060007410041c0040e0001007074564900044950795441c00c03403140003040246504005c079943ca8946000c01091400300a01c502800390800f0062500540f1801c0341911030720000090042c011001601201c1c002803106e0309002240224500016844030000304050f0b036880c0d004401651804401d020b001303070300c0340050025450400e80340703083c10b843d240c0c510982c0881252030340c03181c3c00801c90b1030560854071b005855188a14040740180900c804496009040c4400030a51a10000d6100c1c8241516542d51807281c0700c0c00803d80300404c0041c1100384d600502034090100707440710304411100341c7c80392508501 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 692187580 1250 692186330 692186347
    0x50a0e0c01050d09081b060a0c270801050c0d06050a06020d050c0708060403031b0305011a0d15120203191106070f1506080c060c060a0e330a0b090f0c 66
    0x8a83c06084400344d410f401c0d00b41c00300c00107020011a48c3c40850301c80c0030800300018450151801c40d002c0c3c11201c1d4100400380d40650082c03807000c4c940040441100902c0541802c1071003105d1604041540040c1620f041400074171450400c0c0d1500440d06c4c16006440c010241030f000700c1d1554441d092145007031260741300000d2810f40410580c0e12441c083d41c2c3c00905c19008031700c1c500000340306941c100704040c1404010700074030400056070340e0f5400122407410f5842c424940010058444003515424006050000141c5014251020310b5000d1088058a140c15040e0300155803c441d0300c80060040d400d13440c0c0c440c0c09820001d00400030f49024500004026400750344000b0204070078408440c3d0300c3e40700d01c802c001c81001048003400b51301c030445541e410100c0103040d0555410780140a01805c61f180c4002460450050000ea18507280340e4a92800e42210400900d088440c80d500300b0341c014034200000f45e1010100d04c95691032180c01408201c0c16200c41c1c1444100c4003016212550403207041000a8 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 692188830 1250 692187580 692187593
    0x50c040b0a1b030507020a09020306150901020f0105040f02030d050c0a1e20040f06060e100e2707140a14040f0e1b030402060d111c050604050a0e0c01050d09 69
    0x701d070140f1a903a501d942c0d04003403042c0144c842403580b05011160051043c00050f81d2070143c504600d6074200d09164441c41e110004030714110b84a0b40d12035003540f0744070501040c4010a030000c00781d28000c2d411125003100400e4112a02c0c407400121401c2d5810060780003000441c1c411441440307940320100d01d80c48008036202c4d524078103010603000ea20000c80440c107500b075003028050601d018042100400441e850000301400d04085892030a1203501c150100318080c40c011082d001c0c450310090442c1403007540b10340d01c0c2400d902414001c2c81c510340307101c00096800e51094001107100382da00030b1128100400e010081e508210f20703c40152100405100c04251030b4850b160715002000309203007130051820085141d030401e01c4407503410035009404000b040056241d200403038001c90190000000c0f00340b03d459800c3e402d80680c1c000c070388540e002c504510b04a03035030a0700003e0162808a90811440d1110840e400c00c40b01e03030311280c051603003042c10300d400c0c150b00a1018118503488100007295165482d82c604 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 692190080 1250 692188830 692188877
    0x2109011401120c090605011b0c09110304060b0301061a0a020f0105070504180908040e0703060b0d0902030f15010b0d020702150c060f010b07140f0703030f0e0103050c040b0a 76
    0x300c03525501664040107008028146800030404e0385820003015040c180000d0505590400300d01450703c030b84002804003c025500f6000a201c414810801c102c1c6040380b0b04040d41c01a01e05070b4806080800b0700406190612984080f6071414000b816064560740c0080810341041c1c100c40d0541c010351444e10002c0c4828081d00344a019640d0b00e00340e480e402d02050540603c403951244115528080c60380c400105120121070070740b070400300e01191071746c1e07141e6040f8050021604000b003000004141d5004c03200d49038110001e00e501c21000d50310101e02200d0000c7c0d5038203109188110892040c0010003c181140000301054828840098a81000381d00442c10002c2018110303603d0440c0051141c0d00920140100d9402c4a000e4440c800e05515290142c043c0c0e0240030406402e0640c5005500305120b4100900611240c0744015600034694070704000d018200c1800b0501d0200f040c844c2800007540c42407050794420340641134003038241400e110282806820a802c854207204076214075252084501814 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 692191330 1250 692190080 692190089
    0x3040f15150501020f070b0430081b01051303050306120f03040305060610050403020922050705011409011b02010e0a03060f1b02100507091a0309010e032109011401 72
    0x18480d64034103000246002c0517000440c9183d00b000714144031074002c000844040302c0945101c0c03d589110700000309500d08035201e158803651580508030040000302409030281d040c030a5440e0004c7c02e00da6104c2c0f030a1b00c2007159020f03449030010100000090103031000e19040500034000c0860001c00300b1441e440d1105006482c2400e0384045000c0007040700820145a00200070750f40d10081c98607004000e440350140d40170080c46a00c040d030000380c200d9480c1000c11084030400003000e170b0804407418003640b640c2e05ca010b030600052401100c010002c01c03100c1160076600701a1358000040d60400c10740b4114090707181040741040701c1c034030f034500c11030303441a10141c040d6006034800603590007524060002c880c0305000703c8102a000449240081d40c002c104c0502c2c545000c1000300342c50703507441310440702d100b019040b91410401481c525080311041d980039500c141007040c000c000c110b012101e21981e90081c0b07028981429003504c00103029059100c002d80d0451100000814040c00135020290741071400d801 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 692192580 1250 692191330 692191361
    0xf250e030606030a170a022d0f06100504050a0212070504060201050f1303050c0c150706050f060901060507050c10030506210606010507020f040603111206070503040f15 74
    0x2140951a0a001080e08480100c0007044451410740e10209155030117940f552407000085810b8200038000d01007000074080c0240900052440c1d014a000040118010011b25128582c003443c94180002004c0d40200310f1049001003807458501000003801c4002c00b50f118185d000c1c05100341880c1003c41c10341c05041e0545569071100c0c10848000e0031503000520704200104e2000510442010500440343c0494151a04580e0313071460310601ea2410400004060300510030240c03403551440f840d80603245e914440c050500aa0726141031030700320100291440c9a100d6401001013004a01840c001e02444d03201d202034410100704040022641d00b401c007086030100761610204415880d0203c1404151a070b06000c0e1410801003039801a40c07448000e0944d4140f2600162210541da40c8106200307030f181005000f84030300c540740e2070051102c10f51150494042c5101307014000c0300610120300a0300c1401c40340d40307481c15640d0ba5168005041400030003640e100e04280c6c0d112060748030305c3c001c2100d0030101c8031 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 692193830 1250 692192580 692192597
    0x50d050c0912060403051c15030309080c060931060807060305070c05060a110c0304081e1507031e140103050c01092402010e1c03060905060102060f25 66
    0x41400303400c0c1a420002d084607000801008002504003007519200100300d04041055500a403a0ba40100f144901007030540b030300d80d2000404c06520010302029184a031007510610680b50090040c0d038000c05a800340d000031b02e0f80c403804d071601503054030320081444c01080000441301300c1d60b034008407080394009480f10382012601344800303501030044d60780140e15844c0041c3c00f07140c183c07105511460040c5c18100c41584070242502c4400e4400261a03450407568181d0359915914422a582c0300c80ba21502c01201211070504084650007050003c440e035103c0d0380d00003050341d41c54406c070000c203181e80d00c10030071108642030054a001301c1e01c00d0444402c00c000c0549801d504608103a86081d0010410750304202c000d10b8240003586081f80416020380030504900c802d524185001d0703000d0031200440c01102d00c214460090003000300009040c0303c1d28152800c01906803a01e8008042c0c400c100c404c0ca0141c1d205802003a02d80a9696926600200d03898005400b050920161086805801c039034000045406 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 692195080 1250 692193830 692193847
    0x12030f0c12010b070204050601052104050304091805070b090105030a05312607022403040b100e07050a0804210210060801050115051810050c16050105030a0903050d050c 74
    0x1f4450103400c003400f42001410820746104401d00c2c4410400003444450607240071034100402003017a41c0140554440500c80401140002c043d0595000d105450600c02c1c070340c000031b890721400b04548040c4411f950b001e1566491400200242401412041c00c034164149002122400030281c0d525034003280c0038010032541300703043c0107440e801d0041d280e844030305010192400f003945140450f01c2c420760560311010f00243c000d016000c07035009000c013000030746400001c11042004c610001846a001c00000e40d2103503031034072080c00c0020000c40b41038003c02c0d410440652004d000d850095803103441107044580d0f124220103200100c90139a0031003805603002c0c1c11a907000300c0c010700500000d022580020400c42d0701d04200c450000100385502000d000002a050256043c440d000211030240a09000041082d400c802052688030803100c46590103000030044449207041c5104044580580d11035040d42c48138500b910082c49040006c90500c40708111600c1c1100d01c0340122031080250a28031038503252a0b = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 692196330 1250 692195080 692195089
    0x5060d1d0105100603090503121305150c03070c150f05010602010b03011104030f0c0f0b09100509030a080904020d06090902120d1202130503011d0d0212030f0c12010b0702 75
    0x4440800d5031030341010708004401504181034011146107280210719080070f030500078203511416010080084220041240c040c9070845042062842042201c0001046140000344100c058984400c0000304001042000b445041922401f6010780c404540800e80451580105c49501d40c0c51164a130302d03540100506074080c07140b0b01403440154001e000c181111401014284102d002c000d04054071103160307800744441c80030303c000500317072400e401c2640e1074a400340082d19401c050101072003440e800c500300302c81a11510907a00c0c442c00241c010704810781156141401c2d60800f8402a0304a80d0a0240c50300040441c059000144101c0e07a00146081c60360046c410f00003100203544800358010004a103041d90702c0080c2081c90845900c0050300c594000849800c50b1140b5802594590f08100c6181c0180304060760035000381400c178040701d0b141d40320502c069032035a03a00c00303000344803840500003d044080c0080400d0b91102800f803550780703494241c0503c0ba800744401e81112452243c082504011800d0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 692197580 1250 692196330 692196371
    0x6071103010b1c1b0302030d020a020415080d08073c0c050d0e030109020a0902031023041d150405060f01051e01121d06180309060304050705060d 64
    0x81c180c58000f120444030118200c000740b48040149190240c0710036001e100002e009078800f942d03000b410b41d10410380b1b40320004c1d80d4070310041050344164a00080240d00e0162880090200c078680d070b01070310110001e600103592890006151340240702448031500c6031107440c4d9a050050942a00c0c02c00001c003200d00001c4100c1003d41508004d0110048840d004100b0001e140008200c0c00e150850f60800040b001c02c2c00761000880c000d400655444010800840c280c0280d07200f801c4c2c074500c02141d5940c031000d12a40c000b40704444124220300e542c50035018280b5070408904144420300030103409440801e0607207014803095605054661400a00c4100a0244451504041c1074080314105504000020307544800f400307040c201c880d6000c1d40796210f50740690101c52001c0031000d4204030207900140411074050312a01e080c10903015400004142043c0718a00500c107211640081d0b04064000080c80060350002d007003a1500c0c4581c0b1000102540e6000040c07400c0c0400078408078041d14840f00100008a = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 692198830 1250 692197580 692197601
    0xa03020c030a030206061519031d010b06270a0905010312020307020a050907031506110c0a0e0103020909120a0c0c090e060a0f110d0c1431050607110301 67
    0x4010b02c10350004203500041280d0451021503800203903044100c0c1a54852040c8005d1000c03010b407044420b0070aa13010f0f032006915259500c24007084a080c0b1689900325015041642e500c15010300c40f01002c1e4081c070110039071130748410207668060388480e400622100010b5118000d4252150010700070815400880450f8503001d0008600f003140b9680001c400b913406005080c012184140041c66036031280c0c100021004109101e40e007843d8946000404003100c040d4481c101748511080354510b0305242d40e0180c00c0b2116072200d22956400c0d5802c00c980c100014209414912508804142551440d0020014089143c550601c640072502c1c00300c0c501000c81c0d0000600c0d40c81c0c0b014220440c0c4012461540c0708424407800541d110f14040e600300244600340c0d0070860002d011405008101e15544220001c150640f0b9401c0501c10642c0c1c200080d101d807248610500b040303600240300c2098405460b240798080780103d041069102d101068441d082031600340e0302c004007282500702c642420710501c1180d2 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 692200080 1250 692198830 692198833
    0x1b0f0d05070b0313080d20121801060e01080106061202070203060604050408161a0c090a0303030209030c15030a0c0203090f09060d0f0b07080105042016140a03020c03 73
    0xa4a40c650a0311440c140c030481010050000015403545980258485416171000c4660303200c08000c4e000c1001480b116132a10320310000d170000241c0840401007552600c01008a4030301c4e06541d030308610031860f8a846d01c00c0f1140d649030b081c0800c1c00b8280b907a032140078000020001900c58608600181140301552140544610400c10003004d42c40c041844c7d40d1144003075501090b43d03199440c0c12000b034070401c40c10254140c40b01c3e1510003040001c40001840a040b00d9072122151511101980b49100700d03c80182d100380f030b0000400002e40203401402d01c540740201610741005070107000c608000010401d10002c00c01c00400c201ca200b801e48580c0540034014402141000c2981e8080b4006079810864507105001ca07000240140d9580d403003002d1811b911001d004101130062900d038145500c10748400d0081109940045140c0c1080d200705442e41c8540415211802841c821309207507a44594092071001034440140000700b114020100b01400b402c02c0140b41c001c20a080003810080508540d030720a = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 692201330 1250 692200080 692200099
    0x1060321030902182a0d110405030a0213020f030f010503010e011509022a03120a051b210108070501091e0b09012015010b1207030510081b0f 62
    0x1580701c10300c00c5501380010a4400c06943c0710324900c1c0f18950303491000d810740c0020040042c1805d141078000b030141e850040d6003e00c54030f9501268a0031b14003582c05400c1d0154000b9031400090300e04090301103445c06a008005142c018080d645c0442d030380c4200c581c4c21564a91000402c41d50a00b403280710b0440c060321000b04030a0040d9404c516001c0110b100310240c0540208142e40c511301c2030390b10081854820520700d40b40e181d250440e141c50f50041d06030220003860410000d0409900780c060f991169440c0020300c5031503042141c2c166003036003103a102e2a0500303801581803028038a9a072082d0f03028205200080c45110328000004000c44110381091030581030310017800d03480c2c400341102c132025240702e1040251900c0c14040101d80c143c86162000c001c03960385070f001c03842410020940c3c3c2ca1803524500850010380e200e5040c00e02074480e8144030500660104001806107120307a00150304a02501d03c0090348595503a00c2501d411a4000000804503900d14041882d16142c0140e12400318141c411110 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 692202580 1250 692201330 692201333
    0x50c0a08030715050a020904090609060e0f06040b13051501032a030f020f060a110118120f1823010c081912060305060921041a0705010603210309 64
    0x240012403d020020700f0340b01d10201d0310400b8550140c48144201401c20030502c070701c0e400d110313015080f602c5060321a50300c0c1084245540c8400b00e40a140c48003650010401c5481e03079650364001f040c0003040b4054a0341380b41b4800c000500140500d848215201e0603c03425075040d4142001070003002d102000c0044483e0022240d400f1441e400c040481707402261f0003400701c60038000304190160b045005d81d8403a9000036018030342d94000d02d4005045404200810951448000548190741000b0006d1f226011040f20085818800c0c0c0e1804011149483c040003400c08003800301041444a40001c42907032580140c2c0c034860311140302c1c40c0840c80c0007481e00481440013a2161051407040c0901c021904124440a007441402001d2403012120007038401c21106a0303a09080d41c90b44010740d404540f0303010381c0c00c100200784180034111103da08051041840c10346001914045907841c00e81c501c10410b41440381070081102840b5000085004080c00461845c0c146400c82c41e400501d000103051501d80b500120 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 692203830 1250 692202580 692202593
    0x7060207030314040b0a0507050c03241e0c0a0314060907050307030b0913050c0f01091707030f0303200406050403081c0608010e07050d1e02120109050c0a080307 71
    0x41141c0d050b00740910403c9409592040030300ca03a8105e1001c000000881c86074041d800401000c0c0700b802002601c100c040c0c04000c160716200400c001c81c0071a03510b60481e41669003990007054028400e103845950510880c4207405058100720340c100134454002c69125a19600350050408000700c03541081c0d5503282000c0016032401307001d08050b08100c000720009070a03a000790322542d04004000d03e0310456192a81104803180080700c0215011300a04d610028103050000715691420f4050f142c4004240c1403c46800541035883c4010b000382c800e000002010030320b0500038000e014000c0e600032039200c407444500503581034841003040540034200010042c140d4400c06603802c1d203a201c411385d90385042b0401241020004184203006140c58030000041c0c1c04015070000c1a40740ca1142500c0021b59900d04105a070150380101038851541140800c01c2030041e481640c1c01ca501c010811a641103980000c0383c00c45030450301c03c45503540220300c0b1009529100001000404c051030003945010007969981 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 692205080 1250 692203830 692203843
    0x1020d151206020a093b070f0f1b0f1214070f0201110f1e0d1b1b0f05040501090203070c03030b0f1302040905010b0f0304110d0b070203070311070602 66
    0x68145a0b01140c0b404045210707400ca034005041040d81b03c60690304440000d90410246110b1500e010320f500d000c0c010210740c914a49225040ca500da20040884004c026201084155540010001202c01003900e2042d4030b0a07078407005005000000b503410031841d0510b440399100410300140f0008811100b2000c0400045a414030b42c0401d41e170249074450320040e10041c13403424008015024290702c500c9004170000300c03e201c181a450030003003000c050709452500e072204100c0b03510000301041600510400e101c4120a4040d2050000c044150a6892001c041d0009070b045200d4910782d01c40c1c100080d113410b0183c2405130100c83e00c11451400c040c10042c1c400303150703000c0c000c040c1074480013000d141c0c0ea0744000007540e4400c0500844600742940300c3c0c4000950250141580712880c00340007185080b1041c0a4412a1003540c5d805071440d103a80d00c4000386c1c0031a6100c0d072903115070f0369004500014a0513200d035004440617001561a40781902d0080c000040384c0c00c0701d50183c9e05c9280100051a80010711 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 692206330 1250 692205080 692205083
    0x3030424021b03120a06051809070b0c0708100c0507020f030a0b07050403050f030a0207180b150306040b010c080a0e030f01090308041b060206011404090506040501020d1512 76
    0x10904603122a4050406805480108544080e4442c12031240040100040031104141160008281d90b03200201c4120360803802180c1e000202c09420550b9181100034030394110303880b00115a0500e540340010780f13880c0d0100038040c807660803642c03040004c2e110400c2005d40742820781c903090140d03001307081c402051401139940183c0301c1d400301055403015440601c04400c01c03542017a800201031400800181c4554401d1200302ca1070711070340c0c29030302c0c071400040180d5401c1110b66000d4048580ba00c0d2000400344007c0c481c00352002e958090103180e0703603565070b03c240c0c01001d4410002c0e143d180100400c4101c2d200001041d0621028081c614002a041c03000c4690014442c18000003200b07060001c246041000c0a00000540c41e00c0c0d0348005158010140c64411442021a445804009156010a10090b00c50315000d40c0c13000006101000722260905041103004d040000c1801b500d480300b501d40401507805031016540040c4002c0042c40a00989501c0d940c1c2d8034166403401d203480c02c0d40d24220f607085c10 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 692207580 1250 692206330 692206373
    0xc0103090f05120c0d09050607140f161a070515070c0b1f06140412110d1208163f0e06060907021f1e0518030304 50
    0x31500100004104001c00d000d80040483e0509040c90102c2007450344960384203800e42c42600d01c82008107100d1096030055840180c0344504051540d03440c84150320740030800318010700070803c86444c682810000c0e501c4002c0300da900b10402c545414400400c0c19101c901d81071583c00b017004200003085000070401e0092100e01c1c529101d80d42e50007012241101c02100040a01124030300780000080c02040808205092241500c100c55030351b4030507035103e800c55600003c0017900303120400180307a5801343d000d00180241013040c0144940400039900903010303107080741e400180b00014256650301c0b1811036400182c200d640350454054403070280140c0001030a05140554407440c05903004141d2030300c0d011030700068000050844045110201601880080a00500c14903002525074903101c51050700a422a40180203444449071005181d4910001020306031910380924580a01c50301903480d9009079030000001d03060405100d00c01ea4800340800c00c1042c0c0d40f00340140008164214240d00d5040d20b80d59 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 692208830 1250 692207580 692207591
    0x708041103010c020309100302090d0f020406121401060608071403060f0d050f060f06090105060a18061112040e010b0a0908060f01090510060807120209030105091e010c020c0103 78
    0x140103540104425040c07601542091070b070030201034000014041040044455802c0416007440c110201d008060320280c2c419000040c0384003044100b5000d60a00b0700291010480c641c44802c0c030b030703194203401404403100d01c0c26481e0b2a41c540000e00c600400303003d00345840d200714144903200415041d0300080d0405011000004034070706d556100d03001245800041d20005044440341081d50722a040140c240c140743c05140001404030844168051140d803000b032010b11240d00b02001d00c1819044007040f0380c1130000c07940320140144c1644411400410041d40c031030114880c8100760340d00b481c50240c402c0141c3c140c2400b060101c0700440f420141564058030313a898030b500c0400d20481d10f065155000c4000743c011720b001c0c014003400316141107050b9241403109201503290010005010025482100f000030340c0c01001c42c111920a4440500c40e0071034003405400c0c02d00341da0010342101e0040c0c5600103558082405504140f402c031031000d0003120780760f00030031000c180c0300400382d11030310106902810140e0340e1 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 692210080 1250 692208830 692208833
    0x2030c010302131e0303110f0a0b07051b0c030f1b010e0112060608010f0522020318070f1703030108060c070204090b1819020607020609041b02010b0a0518070804 71
    0x10080c8014424418400391805800c0e070000e4820130a40415030020301c081005403074003080086d800464400c10f0004000121540d15103501c0b01801a2a0340f0410008216643c6085040248400003404240180090f40011801c145c9081c100f802c552001da0041c50b200d0f0109081d51142254114084c00d102c541900c19100403503141c0710075440c1d82c59103403030044049011a800315007181650940500000d4041d10b8104102040848103c0418071011401440c480030b940c9801540e000011071140340100c00880405604043d40c030380044032141a17406041041002010000010f50341c00c101a624650404c102d46480e1100140603103154000000d544045460300c0e801564002d40010b03844c3d685007045100c080b403ca050084075007162007001000b603507500000c41103641c0642e000b0310b050715008a95003441210340001003465846541e0300290f481100740c1042d800c0b04c124841d40000b40350a100c40400202c541c80750000c1b4046c002c2c201040ca070000c0001e881680001242c14143c0c0b680d80c40c1e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 692211330 1250 692210080 692210107
    0x1c06082a180405060a0b0a03020907030b04020d0f02030a0b010503010b07030c02030a12020a0b060910090510080a121101110a03091b3305030c0a02030702100804110d02030c010302 79
    0x4619181e11404060401c1009000021901501a0348002c60900041c10150204000350318180000395010210402050000e4001d900c080c8120750041c00143c2440c2c84154040c0413141007002d0402e071190004100505880c007403085000b5031409082c02c9046506010020440d03018412004052022820071082590740c204882c03060b26030b110028000028403000025290818a1421036926080d000491118640a5512407050505030180003d003890315042030040d020152518001c150300c1807007c42d280c0410b000014440303000700c041d01c2c68003c00d000000d10380708641d1100c09207a40340551486070455160120340e10512107207408600501d480c202101c111040380b17407240c0300241001c800a4020343e0001c8a9114807004201907000c0c10308680030003580142c000c0d90400250341000003401d8600440043c0101c458584100d9040c5211680840c0100c40d02d4450500400e62500402003040048200d800460a041d0740d00400c01406501007030f90341c010a840035052640200303014005011 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 692212580 1250 692211330 692211349
    0x1e0b03070525030807020a051018150509070f060e0f04021606292110060816091e020d0b0604170c0114030109050703020c031c06082a 59
    0x6611508039291000e0003038540382e50201c01e01100401c0c0200e000485a50000c121402c240380c0140241580d5555032500c20020400d2008005112101c1080b48001c1108100d18100207503c401c000621428801040c500c0c01d043c66100f03042401c80c0750002c0c098268402c24803102803105032001590140d00e90300003030290140f1071a05103542e940100307040600c01070740c0140100103a412030340c44000c0d42c041d80540c0080f00006c00140c01440301e4a80d0408103242c200c0d15015041a0025030b520100e0451504c2c0a940b1a41c0c0102265402003040000082184000d03000418121a00301300c0c8134080c1c81592642d030710307142204290f10390201d58880702d41071a070403c451a40c0000c000503612034940c405101c2a40c100251626180300f546401d03407595014400d42851800d090b40c0703250842c3e2a0000e110003032f00f0024505405c044d0203100c0100f8409042000d82100f40e140318843d00c580510740c03034900031100964050340e801d5203d1098104100300c2404c0703018010510756401d9120445c400003084071800c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 692213830 1250 692212580 692212597
    0x12050f07080a030f0605040204081203070201020c030d050f13031d010e030a0b0103171c0c021e0d0f080c040b07020d0515160305070f05070203150c0c071e0b030705 72
    0x41c001032604500340e056002c3d00401c461410200043c0e5211024001240901d000e080c0f0180d002d803400214031040503002c0d5a002e0014800036181009101086045030004420210340300d4a55003130000103030081115a52018424001c0101004240c8008000d031900080903000084007466500cad059100f8501c0d80b1899401504030b4803c01081d2415071076151007444107640210300d45080d15402580d49007103925a21030000056043c41c0c1800c5103030000c0c5103443c0c1e000c00758031600243c3c070110210050103001aa610401515400200c0c030301c094441e01c804564981000455400c02408071134100503902038950070f451243c4c9030146440031401d0841903620207001e0344505400c20302c45031030b0103101d580b052480641c2808101c03c10740064042e01d0096810101280c9002401400b0507c6680908080781c0010304843d1200a00c046c8441c03039120030346281d84021000104a00f504008114180041000c9600c400170f0007101c0c40050136403c018041e01d00940400008114510712401c150399007803 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 692215080 1250 692213830 692213843
    0x406231f1502030a030506040b09071b0c030818010216060e030a0605100602070f0803072409210908071a040f0602070504051509190623040e0a12050f07 67
    0x5090515019580780c01c10130038200064289400280c02e0b01f01409142c04130030300a000c00e01507851701402aa40c83d0f16101200000c40000b601440114982d156900011405490a590f5456125640502e0710b042c0f03600260666109144c00341481d8038a2110b21b04569192400402000f98030000904104458a001d401c4a0518040c001c5011500511004864090302250003195850100700b240c0f5966100d00d10903a082030107014041380b071941c44a01980811440050300c007000300161000c54003031903401d0b2940300401700d1087c0d40306800c0c0081d4810490504124140c24984aa03080e919a8180101d14a01c1409580e43c00000041000d4a0203054201501040700e80c0750311000b580c88120748505480340c0e05000210b04c4c030030004a660008c0007000b0705480c0c180d030b4905524810f030816580f207051820f030b624a000503510f182c08074a5080702000b5100e2001c05210328003040280e482c3c45070011440e80210b0601c40000c0c00500301c0c001915800c1c00c01070349401045820300d00b01c7c0603861024216 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 692216330 1250 692215080 692215109
    0x10e0118051e12012a080705090103060b0307170105030c1c03021e1f02030906180319090801050702010528110a1806050309030d090206041208030406231f 68
    0x241d0064000c50f02c589505842e0290045c944500c10364007a1005101c0e4000c942282c0105070395910910051032203207010f040c0451041c0c5e540d5000d5085900460744000000d01071885140a070106022807401480704600404516042200250100e044020420308400400300f001081500a110300201c40c2c2700000540d0400c0e803642c07111526103020001c90300c4101000302200242c16541d20036203000d03603403040c010051581d801c00e00b8000c0a0060707450001912050200d00030340c80039240c041c0c03401c03030700b42e904e442da01d9240032081800d4460203000b640969040c6410000c4105081070003400b102d00001c82907102421742601100180b80c0c4020403080d294000800c1810107800010705080f980711000d20355031559598104a50500055802040c1c0c1d8000300700130600b02d0390940001411500044c407052519540f00441c81c12005000012284030388080308100900030648500d241ca1700010703401c81150608509c0044c010392008085000c02600f031064500007a42025501d00541194485900e1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 692217580 1250 692216330 692216359
    0x20a050a061706010527030a051e0c090103020105070b04080c010c0c11010207030201080115050903060406381309020301331203200114010302010e0118051e 69
    0x82e03103091142e441034942e00c8002095240d40300c0c0c8202c0e03204a800100036818400c41005203842c2c01d00c103240081e0305105558413900800c2040c050801019030701e85100c41407403041d07510541480040030040e071181285000400141c0d0b003080c111408550b2150304c04d003040d5220701c0c140d1218010140703015819840d1010b0341250325004410a60103500800c00d610307160140782d00480c0e1701e0a0ba404001d0005406200410207028000400f00400c10141013540c1003068450100380b0b071420465050b56800d0312402c4158a111101d13064480d045d102000e140015075682c0e420814400d54586c140780a00012040062014565440725030501c1c1d004009000c1451640e41e44006000140c0c0207810303025100e1034030395050b8000200d04080301c400030000307400c41c004d5407400e80e4551007003e101c0f2030b0f601d401051403205010a2150030512801e400c01d2418950640c00010007800341d20000c02c2c18482e244a680c0312400c90103030070204a40c0b0855035030201c6031400f0310554036000c26404070354001609001084 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 692218830 1250 692217580 692217587
    0x20a051603051c1e020c0109050604050a02090709080a02010c02060708070b060a080d140d0608070b030709060503040f020d050705061b01050708041e02011e1101052d04020a050a06 79
    0x35115484120400e142102d42003d00101d0345002200c0c20341035522404805015442d0b009021580b044900004080c0c3c03181c0c40e21400c0030001c40d011200c50b00602201011031030b0165005400040515050610300e081070003069841c0b502c0c036800b038107003c22080c40310f086650f01c0e011503038090340c000d10141d00c0790300c80e2404034100c000694595118603c680030224424030300040388140c418007542e4030304120304001d00250350795115001e10850170341c4030080030611401c1046004020b04114526640c1c910b0b00220082415490303802c03d10410908000303000220f070041c2400d070301d4a0780488140315a1081c40c03030a03a07d0160b980d0b100303a80010b004a035888201c810740c280500c0f0600f000000b40420fa40f1000225184c0800300c81c020710016280141c003144100b03d00c1d4a40e51640f06051058164841340c651441d0321440d03003035a000003071001ca200d104c074180a000301d94001341c5406072030981e107020b520503c80120050810300d2500e107200f0005000d540c0c85450810042c1006488158500e842e2003004 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 692220080 1250 692218830 692218837
    0xb0c0a0c170d0206060d0b06180708100f051003020a0210060906050108010509060a0308030c04081902030d0c050304170124260607120f1a1203040b0904020a05160305 73
    0x40301903000b048402c2510381d0020a21034800e010082c110480e00d002c0c1c2e512454105c00251490350400c040034940e007030032620704041c0c1d40202141d0311008110300d04400c24400d098420303000702802189103013003009a500c441c0d000d0341480c6518100543c40d40c01c03a51089160404030703117903482c41c541400800138056110364882d8083c0c410a0343c07905d03e2aa00c5400b4450540700c04e54585400088202082000c2050340004e15000315940040c0b038903103540c88034224948416000e080c4422003100080d01c04610342003142c20203105550401160001554650359203e014a03c504000a00c10590010780f025003135209500000b840d00303180b170204008490a10000704503025000c09000140290748078400607a840e2202448004000d008941c0e40123404c440c84c05581c400001c2c0daa4941c1c4614002c4080c44c0140e02c03280d007407011280344003907c0c0420080744000418000d120758004020078450003100f8811900d00c0d44c0165805680c9280403241128070344191107002e9445d1807141d01d414100b59015008 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 692221330 1250 692220080 692220119
    0xb01060905030d020c130207081306080f13050a0602032e140102060108030702060a030b180603011a0112090302150103030e0f151918060203030108060c070c0b0c0a0c 73
    0x3c0700c1424010f208280d80d1100102c080070350000030340402007441040da40007080110301c900c01450904130080812040441c55070410000700380d2500c01c00c04402c001800f41c46c0c0c81400181c04850780c0000c0d0704d58540300d00503043c028004540000c0001e00d003385c2c03882c40c141c8031140032071502c0c1da03000c0c105035581c0c20711006c0c00303009032039141501c8001e601e6100041141c140d94a0317002171840d0003101d6003001a9030344084032076414035481d400300d00f8541e65146690020409076940012091402008160840301c0c907424000312950107481c04490f59910130441307595140380c04000941490241400e038540313034441c1d91070b403170401400c0008000c15a00c05150011441d00f6101440282521020861152a45419445018014001544141001c1c0308081c2e82c58241d042c025500036808680b110403001d00d41265000d68000030041200706400c0000c1980465604609414a01e40c0e984814104046110b401804440403070920041502882a20641d41c0c1c00790b200d0003885da82c2e0500604280b440440c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 692222580 1250 692221330 692221333
    0x8090717010b030f0a031719020703020c10020111041806030b07050403050f03120a02091201020c011e05010e0403050f1201060c0308310302010b06031e24060f070b0106090503 77
    0x145a8000000541310030090740c581c607103c0c0e849502440d40503403008010210b54100b4040c1050060000540c4014800ac2d80640e024203c1001ca040600094152b040440d008582c58990030500000d030880c290b4081d40c00c01d1800b48000c0c1c1c0714041c07079030240c00c1c10f030409000504014180440103404c0802042241d00c240306440700741405040300c60b00c0740103a5034000e180301250000103034070b400720384c2c02805861001417074210b003d414801880d0882e000142130075a50781d074407604041404200e442c801c9425482204c00e000540c1403110300b01100001601c01024400c01040e60b50702c5000202c01e40715900d40e40c110081403176960380c0004200d03000c4180160080740300d020100e0b500320000003410a60115041000241e102c0002c3e508150070740071702c02601195030b504400d07900ca6540d00010743c014548404220a000c3c019840c0c14201f98014000b1204a40d84042c3d0040b952402020000183c400b162a19221141002e180942c0c1c0f2400d00b006049800600c00442c0040c0c1000b80c03042540c40550 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 692223830 1250 692222580 692222593
    0x3370c0f2c04032f0a06020d0f021602010e0a0b03090c01080a14041202150c030105010e0a031e0f0b04060911040b010e0607030908030c06011e060f08090717010b03 72
    0x680c5009580c2901c0c05000a01c0440346860100891115204088810420213840c00c003410350160800004400c219200381c0c00040c07000d6a81414000c00903000381451085142c20b001e04003060901c2e0028000a040c040441781c0311205507183c1020100515090082c6035032440c0500909499800620381d080c041003544000c11048111481000741100f026296801d807521503031110401d80441c0ac6010301144240049040035214862560b4081c1c44982016603e03541440e0000d8802c0c030303650101e240a044070301010004503825580310000382c400d003070000600103800c0c1080e0341221a400b07070150070104030100b0303c010401c0a44c41941c24038087c00810b4500701e840c1d01004161040241418000343ea00c20200e07a880c580306000b00030300b038441e007842d1003020340c0c581c9100e0a58100801e0251142c114000400c074016002c0c0d00342c000c1c521095940341740a401c1c4800941041000480107040242080010707060000030400e0310060a0310f907440030b40d148210403034103010340142d0000301e0181c020913 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 692225080 1250 692223830 692223899
    0x120a09030302162304020d0e0f0f0d0f050c0c06160b0a0e03121e010f03050c0a0b0d020a0e04110d0b0f0a03020d0609060606080603370c0f 61
    0x54075094074140f410503001c03140c41074211304c40500c0c030b0681c1903845582040364041c00110381c49116455111031020b449251541c4982c1030400c100703a116074103686c001002c5840304a601880070f00031080300e410916160001d041080d440d04400200e816085000002d2082540030301011384450b032341c440c090102c40c9903964400c80c2c05403a8280f1034010703940d02c1440808040d207004001c81e58041034942c1424528403c40c40101080c005c00e07400100b000158903800d00921500b4000070303140400581e0303c0111146407482c2d0036490b00c1002e14a0003200e502260402c1d91034441e9401c80c4142c8030080060020107001480440194050303c4881c0148e40750804142007400c06021040c004440204190440303803a540030301c1426000c6910848920356501000350005030305101e00005020595a800e40302d103800010301d0b02c1c260110310440c0102c400e42c0f0354030301c40c40c0d0441c0c40744c07106100be10b01e5034110030001d107010b00010b02203811440c22020284800b00e052441c0314144100840c43d0071000d98440f800 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 692226330 1250 692225080 692225113
    0x150b0a0b190e0a050d0501090c2709150b06090a23030a02130513141b18070f05070506010b07020406060507050a02060f0705060a1d070e1602120a09030302 68
    0x1502c1e20950080a00d650411481ca454044885807a00072400420b01d40b0440e07590381ea501545802c41c2e240700c040f80b510208480803220b00b01c40ca0541d114001c00803500651981034100501d03903c1000c0c00c649415183d80b035500c504041da0000600544100e01050700c50b094040c0440d0120800442031843d212484814030300007800c0098150050208847c2d12030302c081040103400000e141c0400307400198887c40010702e0081004003407220b07420207070000507016115019240b030a5006244142c01e10490220907012030300101c0c0d00040300341040d080e840084032090360103002d034110180c000d0084000009210840200507c038240c401c680401900380c0b02c1d90196514003e288000d46a50f00c144041001401d01200520910148115080c00d0408541d217035482c0c010103e803030800c3c2c00e0312030242c24119145401d200410486c01c1d4054002c1c641007402420300d103a801465030124840811800340346c41d00030701101d183c5c2421f102119541e603a580070040c0400c1030620040300180b0865180704000301c04d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 692227580 1250 692226330 692226347
    0x20f04050405070e15011e0513030809030d09081005150d0c21080d0e030d0507050d06050f0f060325110706030c05030402010e040b0303220906050607150b0a0b19 71
    0xc140c44681610850f4041200441314044051007231042c1080400101115030086000440c840c2000d140d440c0c400704145400c1c94140403ca00c14001110001c0c001e0200104841003024410640002c01e565580d030702506c03559000281c50b81000011680c80b06202c03403280c1c02c00588541141010b16807800b944a55551900d2580250007094180100c500012030760b0000306140b0090b00c1120f00707150304020b8410440d10151030400c0032030000141c42c40c0600a60041c00000c0c003080b2000c5001403110004105801d40e407221007449540e001000900c031405a850034043c405c00841303c0c94246850400140a15502e00200c0c038591047c0600011a18420f0048181c209066a281d50941e00d4070381c01034408400920303080e0f81c0b06449030001d071040d4600b00080c09202c040c0301c1003080c03508450301c1c41c00d510820035000403034801d040081c14401510780004540d40700e54441c00504040d00210b040074014000d000070a81d005844141c00161032440001a003801480b08502d4031810000d0002130b129400c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 692228830 1250 692227580 692227621
    0x80d031a1c210f03150b03060424030309061206060903080705010e1005100e100e0907030501090305070b01080607091502030906300f060607020f04050405070e 70
    0xc01c0303a50110346188811884000d5144510003007122104541c0e0054810761946140e240060206200c104489602d400f450604903c41c0320070700e0003d410a40c01c9074180c40300400701805182c6848114881000141000c0140d0307400d20b07040500d00340c4034a03000380380c48450b1143c030b00091500751043c08020018850802101c0858489214140c6180c1e640c45003030304161300a0703c0e1b5541e91130810300d2282087c41052213880064400060a1070681600c240c1509141c1000022100350381c10071079514039956032503080d00d0303601080907070907035401c1d07a640e19291180e00010010350074480340c1d0080582000203080c17658841c1e88080996a200c09030a40c1d02c85045485000040c9814410400442d0481701c2540411181c03040c0c13131802c0d90719008221190300201c074a840740200e5014070800e46012218080040d8141b02d0035000307030b08103051b005401000180080c4d02c2800002041c0003196038482802c0100c4c00c4c0035100340428501401e140b52252480e2180d01882458140091f0002242c1e2034000c0450 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 692230080 1250 692228830 692228839
    0x30408070b03150105030f04170d1b08130b0c07060603150903120908070b060105160813060e13020a1e260106050a320a090b0325030609020301080d031a 67
    0x145d49139214240080c604a195032700350001042030401a5156000781d0310034600c0c8a08001400c0c0401d200108414401810204000e64002805000944001c006504440e8200c2d0130b6841d10079904040000380300c650300c010500405a0206e66140c901604602c120074041e0305e034400308a2512071950103845003002c0c020300c800d0040000c3c4000039040071400384c00ca00c062400c98200a024091450503401100302541c080c0070201d103140000661034440005880c2600c0c0009a040b00100828040078900340d000320310907000319480303120501c40c1c40c01030091111101d8a042c3c4028070721024200000c038032807045142c00e00541440e20000701c405a541254038a6540340d10300411400c08980e001e400604000c000c84901c0b0081d03410941004031140b00404c104006540d441d01c925010f001c04031550700075950040140200080c807011000402d1092642c141c000141c102100300440090031300d03400400243c0d102000200b0030300000661152800e5898908004160f0155500e041002558400c203510 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 692231330 1250 692230080 692230111
    0x1c050106051e03041115041e140d05010207060c03020912060709051e0d111905150c0c150a02010b1509040e0a080a0e01080609070c0311030408070b0315010503 70
    0x40d00b5584004680c0103000d03612141000200000041c038481d80c180c40030321910b03070108080c0b01d2561280c400000c100c44001c00130f50f18918000044051022038040b00d481901090003601c01d0100c01c1d011142c66590100040181041307240015009411400c403c2d03010b901c50100d01c41c84240005080c0c2e00800791911a080202d1421080040c20032040f02c501c014101d80c00e003c500c0075105c10030383d86c610070312480e03d02460a0000040c000711005000c0750400c0142c07480e204026503124183c441446e41a040ca080d42c1c1c60346d40000c1c0301c0c5040003160520fa00240751070521070720310000402810310105168001e000c444421403c008046100b0800340c0c0c54140c08105510070b518080e0b101a0b6410081e03400e45000b0031141e102c4600a40100721124086201c05141c5510756030302c50b13a40c603441801100c4101c09410900f0740100756118440000341031007825000011203030010001d4034010710b00d000c1200c1c0c2b90b5488480e11070007904140c0d1240b049045c0905c1c0307680c40d13600030020341c2e101c0c84503032448000 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 692232580 1250 692231330 692231377
    0x1e0702060118060b0c0604030305060d21030b0d150501090209090a0903021f140117100b190f080c030109120c03090509011502100c0c02040b0a08031c05010605 70
    0x201207407240e05001070ba81c03900069003404e403030041c100043c0c1e107002808052401d4100582542c1c0001e0107144201001711054000425280000e071113441d0303448032940c408000c22016001041091125170b4401001c01043c010840c04400103414a07900344001d00c00c60b6624224141079004030340300390b90b00c00040e40c00114000c1e02544041621402481191102048885d602d2900418032400c0e80c0c1294850f0700d000007408900d0000ba00401c20034240d4001d41544000603511280c1c0c02c01c0c5400d240351100620401503881c00703800d03d442d45400400302c4282e03035120345192189001e0b03c14100c16000740106170343c5524041c400c81031031742e8000000030b2a8400300642168000910b480840c18041e540d5400302d51a29601070036800b074030b042d1643d1101402c1c03200000e4500300d40d01040400e558144025880e500e640820b90403805a0305560205100080c900010b52810188c0c11054452002080340d1100110003643c04501c6101d80508000690300c0b0303c02102e407885400750a2008900012a400 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 692233830 1250 692232580 692232599
    0xc0a02030f0d171905090a06111303031206050901060e030105150d1515090b040e060c04090c0c050a06061a070c21051c0f030209030a11011103070b1e07020601 70
    0x43d032241913240f2600d00c0d032440260306400c880e002d9861150a5000301d580104109151182e01590304400030850b0405502000c1102c510030103000c010100300751420704182800b410b4008002030b0000504100482d078458400030501c15440540c03d10960030800454111050407541d24500d41000c0c150324401d9180c0d864091030a50300c0c4c1416000c00b0303502c41c0700d0a0581c2440a8000103412400302c0030407512050003c11050325490075076441c140d0445010700070f4400f02c1400321400c40b5510b007408504d81c00c811100762408800000c000e0100c0c00743c01030480070014985c1c00312054035000500301c15090f910040b002298000c0f103200402600714104103108030360384180108070711001181e1007110140b5075034a0b642081203402000c004540701002003c00ba80d00402002c01581c2d0500d070860030b21020b003001941e14480310b600540842c800c5841d81c00707164865000f488490f9081c0d4101c82d42d5171380b80c0c80c14050520089443c4449248842c3e0600d040d0707034401840601401440d4000c0c8100c0e4205107412 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 692235080 1250 692233830 692233877
    0x1216140f0f0c150c09010f1803060e0c06220b03010608220525170a0b040f1e060b010c05030a1d21010f0608060f0a060b0c0a02030f0d 59
    0x140e070500c1003448583c58181d00f40100b910502e03140c0c154603207030181d010015060420400b492000e0001c0c1d60100b4510110f400c124404907a00b0050200e01ca41c0c0b01c015203801c02641d85000c81c0c0000f000904001c2540c0c0d84000e0171481076807070f070f0694400c90352000054010302081c000c00c0700003810440441c0c91010010205030b2204020081c40c000c00b14565940b916000c03001d000c1d29091170114407402c4001d4041d1152200411000d8141d10580810032603494452049940007851801800082410300000710001590103501403c205014402d00b60024060703040da40c001c40d801d5050000f886040d511905000c160258080000c5042c001720f40801d070382e550021088072154121900b4400c80a5a444185003064090300000208080014141d2400d5545100b501c94031103040940c100100440040c005500c04003070018001a074440030201c0c005408907520481c5440c1f00442d40814103a800301340d46401910840c2142c02244140100c10f460346068820307080400e290080321a030407070442902 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 692236330 1250 692235080 692235097
    0x60d0609080904061e080105090c22110408012304260d06081605030307031d062b1b0f1803050a05070806090304050f04021216140f0f 59
    0xa480c20040b805020a0484104c1c0d40003059943c001d071000c5807120007440c1042e01030117802d4000c0c0303c2442e108400799610030303504401901922400c0741b030103202030660452502210302d1203014080150408209541a00140650301d25540303040c44485030500e00b40403000c00100110300c0005150f450791101c04500072600c00180b010305d041d60850a00024100c002c1a102e6488200050715500707000005181a103030342d288840943d14043c0c1030242d0b940000555542c1c40d45440c06c0360307032002d034411003640242c1c400c0003658010102056209400d0031510340241150210450074480302d880d1440c80098030903030400c02c5603640e0306200310781c1c15502c035072182d4000c0445410700d0600d0707101a10303600310904a103038402c0d21180c02409040041103001d0045078010821749000b05403d08001c03ca60352684168441c051182102005004040d15503405444421482d01025040740c9400d07100380c15036205a00c1544c0c000341803424440c852954640c151403404810030861403c02e00580f9106403240e02c118413 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 692237580 1250 692236330 692236343
    0x806091b22090615170a020603060d0c08010516031b03050604060e04060c26070804020a030510050a06080d02251a04050f090402180c0c0708060103050f06060d0609 72
    0x2020403120414011508114400c40c800101c203540e03401508441c4c004c941092a2004404c0b090400e0382100142400d0f0840d01100c810340d6a40729180081c03050f01006100604011000740001060703801075000602c100e19031501c8005003d240d00c412400c03100b00207031102c0152440c03031008080ca803003540115031114015000240356a00c43d401c4244462040720200c0710700da11109a2032107a42c0c0107500c048016010003105886640041005605260080450080120103070000302955295841039004507049402d1b152110105201d000c040c0030111344003009217007001000140384100250141100800341c0c05000d000560460300405a010070560307920714009610080344218400300900c42e1a038070010300555591070103051041c0e008156820922405180c0300300009038480d100d040300134030036400d0010120340e6100c407051003034080ca00e0020f5961142e8807000c14010300005007107040c0da005a040f076465100c0070320159610101180c00c581c000010541c2c0e00c0010311103030001c0d0049882840b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 692238830 1250 692237580 692237629
    0xf0a0e150603010c170f04030e1e030c01020601030c03080d1e0b01090b09033408060f010b04120201030504030c0c080c030c060f04060c0503072906150a0c050709090308010806091b 79
    0x40051f01c500c1d4ae451410044408600d402c1005140c201b050041c104020b00151405c2d62440e10340c030584020a12024040d0540007030340c024128959841038a483d4040d4040c3c00800c006120000001d0811281681c003285800d9004030321200104144c6002040060003040014101c14001500304207651300022040703540001742c01c0c4d10740309119020251a10318010300fa01c0c85d0440c2031018100c0d06a0141108501c1044140300c02e41c146819a0200c58080c200400c1c01d854625046602000501014040e5140c60201054001000c07038114503003130301142100c0c91a8440800c100c0c0d10b1181300503420051104100070800b65004070000b0010a0003502030f21300741101e0f5183e05075105401018110000c00c0c407140d44080c3c0071403810a9401440949464a0484020001c02c03442c0c807070092250b00340a104c0c00c601081020801000c000f07044007030701c1800810078034540502840c000380114450340c000c80f400108010800150290000b41e0320440c20001440750040c00095030720013a4550b10b20a441 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 692240080 1250 692238830 692238857
    0x91e0311060708040c06080c0a0302090319060f0609180228090f0501080307240902180406110c07030807081b1606050903060f0a0e150603010c170f0403 67
    0x70700100348600c100c0e44411449180030b29201d088602d054001405200c0e040050007003110741c0100341c9141d00200d042c0140d0f00d81030440060300d03281840b40c80b5000e590180c4169003c1001d40d81002096118000c0140b0056403201c1061040d52800401a040b00311090340e400c0240c5007003500c0309185030404066005d140e13070070016030036558074a0700002081d9441d65665070183d4020300c6041d0061042101650904626544541043c0807a5001d110341c141c0d0084101c02880303055006280c590f6000384908040e1340c0f41c50600c01e11a5046505540c1c0c1881d040b200f200d461300c1b00007164080045040a45403850071035640c203100741c12500007521004018400e4268000801e1002c07a030b004101c1e40245080d0f204940d0f052540481078004c00c04200043c084c081043d03d00090094100800f80c00385c1d00340d07558103c4200010b20440000818611a00801c40b4660b505000d4103070142c1030640c0280402009230b081500c1000018030f640a04604a8001954016130030006641103442850901da001001 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 692241330 1250 692240080 692240083
    0xf200d060902010e010f0512060102010204120b041a06100309080f030109090c051f03092a06030f05220201090f06170114010503013311010f091e0311 66
    0x1180800c03103845a4920811041d90b81010440e40e800710240703040c0c404070600d098003d0140c0111604414441d103c2c202095aa038001c5d01920b02030940741452079120b0009042c101d02c0e00c201942e040e20600400c0007a50b0101c100f1413500e03407060002818044410742c0c0f001085006080400301034910020900442d10001d10101c0294024144d809010807818201c0c240202c81220541c040d501c10842683c2141c0101901c18070f582c002550382c240003a0a01c0c4a09201d45510320a2295083c000c0c00b44103810b5041c0d998030b0144041e5509075070f041013240f01d010308820459201340d55281c0054410401841c41403440b0038040300091061401034041aa103101000c100441500008040740c818129080c9440c0e6440b1103500400758018580b2202d4100e100107080380c407060190498010b04d0800f4543c010b82483d9400c3c800c054444080c4120f208060300c024580a1100c805030015400c1c014142401000750250109040d00010f0500f00d41003804110040421103c1048041c040340b548400885c120 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 692242580 1250 692241330 692241349
    0x12328020702060412020f01020c090a0903050903010212011e050f100302090d03020d0e06090a14010c0803011e08010507080c0c011119080106080106050906071a250302070f20 77
    0xf40c0c030f45c0c02c0c00041958810005401c000350105411903000d075100c000705640d0340da022030b00107860450000396400314ac1002c940303601c204202c268141d80002a24010b032102120b0f00d5040f960480301006421100000044801d4003900c145a4040d071100803d650510f0640040b14050b00141001450000064003099910040e01d9041d0096000740c0010510700c1d400a60065500c05c0807140a80f5140c00d0310000f403100703c1c0c00c1c010703c803c6000e8420b00078001c1c0d016605012310700750044907564413582d460105000b1602c8940444c110020001c00009a0400c14040d89001703403010703291080595600d0341e14040302d030000c41c1202d91540d240d07440350b109092000000c1546461080e0400d41c810840c00d4003070001c0720182e02600c20004014010407c440d80070066804080341210f0b911780d512071a01303000c110400721a50841c91034981c00700340408040c1c1c4440030150032004030f02e190000301c00154154100c1c02018005000081c2c9078641c3e400151520000341b00c0305400480324a41d104511012441000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 692243830 1250 692242580 692242589
    0x8030c071512180c09110f0a1404080a0c050103050c03130201090506040f090513080412230d02010c0315090902120a0b0a060e0105060a030b0f10020123280207020604 73
    0x502810104141302410b50b20b84007800500c60b090007248201b00607a01d40344a001e00214520030085003800c0594810507000d0f802c0b1040da901942c4890315080c01d6a01d5000c10203088038942441000043e0650180c0902e601c9075416400103400c55071040301181c442c42e02e082c001c0341000340c7d40d2808241d035035400001d4000390503500d42100360301e8181007248040300c0020b07003a104c00c0c1d0340e44d465043c006807116080f201030354401c2d42d08844415003850300704003040d8003c00640c00102c0d40307a060003081030300085401d6401c0303207a4024001044504026412a00e61032080182c4154448041c4000ca88035044101c51900c090700c442420300f02008042c0c00c08955107021510340740503c007403101e45da4260144c800038100c0465040c0c8954074100000300c181c4165010700c824940c5030700c801d00d40b83d95a411051400c640250407103400340348004000780240709282c10744007020302d80000d40c0501400300381024403c5004200e2442000051108021020019207440f00807503001c004400041e2100c0000e0070013407 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 692245080 1250 692243830 692243861
    0x8180c150c011107020a05011b0b070e011d0907050c07090e06091006080717010e120904180206160503191e0c11091302030613060608030c071512 64
    0x80501c0300030542982d11000d01c0c50b05500d42440082c0250307541085180448509007003203441440b0841068031180105500a449141d0007410000307065041020004400c100741e0b6001020b403034600300161902401307074590342c0000010b1300180c141401341004040301d40b08081268085031751459407005498200c051980d81d40c101500380015045d00b000700001c480034400d800d001c110700706500682d840e00144200c0555115459501440100a521168207a403665040d202d921000204442c00d0f80d0100c02d02031b004501c0c1590300d11084441e8a40750400c241d0007006103160445030b40c0f0f01c8011021f1100e09880c68081041082c500710b20408950300142003c0d19003074000141c1030b014214803011514030342c00784a001d001420004104104940c55880300725a03039110b90300c400f81030000201014000940600c550420300c0b010b10890040c0c0745001388299800c1c4001520f4041d2543c40e401144454850350f8081202841014443d1600501100c1145070130102c0c9220b2048080503540359010b901e082 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 692246330 1250 692245080 692245087
    0x3120b040e07030c050909120d1b0e0901081203151f09090c0305010602251805270a030c030c020a030f050c0a051324150e090708180c15 60
    0x400108840210040008886d66205c92401c1402c0c00d440d070000c030291400e03820300081e08210601c40ca910400c482c44a517225010000c68200b0042d01c1c0d039481c003446911030400740000181801000840000210340c8003222419926500d8a054010b030300904400c0c0d01041400c00141000c6d545c0040c14600443c554801e200c040c40c2c000614102da680c503105c1c404040c209001480a250001004014081460300100c80340c580c402d040c0c100e21000f900412049084500c0e592041e1082c1c0d0050340c0103118004110310380d0b60640e00350315100703185848149100e410040c0f81704080ba00030b1010800940c02818180542016a03000079400740c030980003150031040d12000c0c5000d22104104208080303006880710a46142000c000a038209480321075a1042030b228071000d01401e40b1380904115540c0ca029a402e0b1151b220f500941c100400c203101c850003d110030703000d0100c9181400b2054060303000fa8950101c40e0311100c40f040369154450030154224404c00c0d0400034261250300b94058900c6605480a49 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 692247580 1250 692246330 692246333
    0xa0e0406170d110c0a05090a0f060603020a09090c0e090411030a0b0414010905061303051b1e03070206070206072924060307200d03020a0e010503100303120b040e0703 73
    0x9010b819011860843c0d018130102c5a02da180c05914106940d4102c0c0c2c103060980c0c401c40d07503c000e8946203c9101e18141040c000142d4980c00d0f0700a011801c8207601c44503019031300c44143e481102d071802c62030350000f11503507204186170a00c5603a80c0d400c81e004180c00048004090b0201e0b01d0989610303802c4500343c4a000c10401400f84a006507008900000028804450b164484a90781e0302c014101110043c00c20340a001014011130854118183c0c82034601c0501350301005040d04c41000d07400401d00501110225581c3c510080119012180d001b4510707030810b100d940900c001a000440221500400e0288070512800c01d89603d014518003080903401602c0d201072686802c0c1c3c91040c1c181c4070001c060390218415031320744042d60fa10001c2132034446052401d02c0c4008066105044003c0b24900401082e1415194141c00030030162009840e1007140b40c41e0400111204d22003120310110304254248d051000030321580b0342c036074417494408010400300790f500b0005d021100c1e103d14080c100d0340580300810 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 692248830 1250 692247580 692247587
    0x30703120b030f070b090102070512070e1f0b070c0e2503060e0606090103180308250e09041b0906141503010e09030706020a030f0f02090102030a0e0406170d 69
    0x34041d40d0207401800102c0f08004410355149224001d2041c0254040f5030034282d80d2080004d0002088004d017003810b41007625140c2520360fa124040c6800011021001400d101c500c018622900125408151507451800018154a0b0003400d41219140b02e00c280c002410b098801c1318034040c0602500214507900035500042698042c184e0ba0310034513041140c100311b10841101c10320f6220384180e600940e6540010012802000804980300141e0310014200c0700785a4440c3c07150784111414006040700ca0030400100e20002d1746031501c0000a0b0200c0c070b0309046070500501c8280c100d8410040030381c0043d541c1404001c00401c580003018800d0751036404110010380e0800c2c4006400c8c0948803940d4000c1003c3d81c003511840140a0007081d140500085185038000300300300d038100d5403c901d08548600b5080c0c4000d000d4a01100242031440c1001c00d52100002c0901c200c403005c041c141c00942c90b01c07281250964000e0b400d155040d502c00e9580c032000808036010504803420104800180c038211101c041c4c0034 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 692250080 1250 692248830 692248841
    0x3090d2003040303031e05010b190801050d15141503010b04050f01031403040317030105040b030624030709060e04051504050c01030902031603120e03240c040803070312 74
    0x184903454100c506064141000300486003074139007618010440f00541440000c202e0340307840704009940c1c0ba040000030458002c4000d0440c4204046100c0c2d03903049100e0040328104001e0241550111210b86901d0005400b488191314041e610346003c100100c5540103416400811203112082c00c524080c02c202d80e2500703204200c415502100d0421450901c45c50384500c01605001c003c00b4511b5104481c01c40d03050070010b030b8001b1035005000c03035071401c0c1c8040524900d8100313106250240c2d0800d05a40d1117883c0104403948500340f11501d01d4041c104500d44110380c0b01c400c60400380c044c0606000812a080d1901444018001d400d0403030704141040d02d403081ca4641c004601c032741c80f81d460800303000c00502c011076189104442460b0220346942c0d1400043d062120707900c0c11003018001c48078004204800d10800841070b480301e40f620100c42c0a15004d0585035124030100c2542404580c0c00b0210805040c0950ba030003110303070307010030741041c0d01e5110b0103207150322242d0241c0120350b440b03a0078200e0502300e0088 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 692251330 1250 692250080 692250107
    0x50d0b0a0602031c05010f031101110a21020309010e040b010c0b0f090c0102030a050909190e0715020f060a1d030708091e01020a020f010e13020706050703060602070e070203040b03090d 81
    0x4001c06e6150003081f1043ca041e80c00014070010303e1029805850380308000c1503244960100035620340441d546010925611518480b02d080307d20001882c03e01c0303001100303441c0c2c4050181c454440032040041040000c0c4281c69145d418444d0300701c803190119041d650454850750303000086011900b40548240c0c43c10004004450465200308070924095a00400b82c0c0d00012050f00c8820081d02d80140ca0b2844030310380218020f07a5454100700c401c2c00711000422104842070703d0000a454014110100d0b15450300740c07020241030384600041610000f9a912403041090158005032030840456095420b56000300703025100108081905070140c0b420a981c56820500c0384916a60a114040082d41f12451980701074465002021000c04d1640074021101101c01c0091048a40e1a48140c00c5d0000350048602070302e4182c41d110010314407600900c921001d540c000d0b0002c0401074901071004410200082c544401c500003804005600a09580550300614440d0301030f0240c201070b901d0040203883d400d0f02e07 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 692252580 1250 692251330 692251387
    0xc09010e07090b0307030f0c1d03011802060c0c040e071502030703080a0e1002040b0406030f06050303190c050706031d06010308092b0c0e25050d0b0a060203 69
    0x3441038442d0080381200440315000007054482e9500c8406500900405c0f5039030070784c18184019007065591200d02c80708040050403040b002c00300740c6020f1508072026030220000880010110f80090303d80100505074121480c002c44100b95400c0000c9000d81c0d00e06120071030568403801c0d05004000101100c02448001c0c2c1c07004505240b1180c0700104681009840314940c1c607660340c01109124418808080724440d0f01c0c405542d1656102090310440c1c0c400c1c82200e0022349810342c00c801c1130050b4000c0c203040350b100800560415884e06032002c06440391101d0003091010404c030303141c0000e00c184240d2004009603240001c11b00340030403c1c01c000000b070400d0a20180c202400500000c0c12120076034203a09425500040c050345080001c80303032503281140341a10040344103001c3d41007201140090056071032100a1008036154464070120380514603000b200e5030554a52000000c901c5080034194461184401244180c07041000c00c00e001059085940140c00004500314001e07505440c5034030280c0c005a = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 692253830 1250 692252580 692252609
    0x1107030215070b013201031404050607020f0105010b04030209071803050a110f100807091e0812070b070e0f04021b1606020a1101030e0d0801030201030c08150f12030c0c0901 76
    0x50301070114103101c8040948019070b172140d615103030344031b58402000a00c800408102c0340c203060600b05d61b2100300300c4081c4010700c2030011008900310103003e441c0c102c44000500c00d08290556082201600303005140108100c2c1c043e024000c58030740540000002c1d0f008101030401030600c3d0405070b0000d1503640785140074682076254003103151a038601c6400040c0c140d280002c4561162502154038107070690001e003a001d40e050001502000520a40d000c0303c2048045444a00d00904159118050480090b100c80d400c500040c0189020303442c85001250002d050944880d00341c0001401c0303030405e1000c0e80c080c0803180708002000104220403100d02d0703852001c4403011071401c04000e60b10500c12600500c01080880f840c4000d900035005440441001801d884281d003c041c801003598100344016030002c2c2c1011405040240036100043c01518030000c0000c500710303424280064503410b0091a44c03c806044021010a03409001409840525902500404113007e082045810703041e04904000d10024 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 692255080 1250 692253830 692253869
    0x6031e0803060427060506124c05090606060913090204020c0724050301060f031e02130501090e06010507120c0b040b160801151107030215070b01 64
    0x400941c0c0e4094030450b808101e1100d8420b5580404889111500441811010010030807450360401d0b44680b00a60700600702444a0144503a10740042004003d2180d00300700414600450300d100b1841003d084101c46a800703c240143c0700348140950694808503a183d0902c003000e402400b011f03400c81c01c102c07081410b00745582c002441c0d890440c508580e0580d603844d41d210031900c994064441c041c86040c00d40d456241d4451014280c100740810072080c5003800c41c3d20b007200303a0054046d00e0680382550b40d1648a50900300b4141c000f08902050000c07070860035400b03042481154001402025088401d140c047d030300c0c01002402c07041c0f80350400890a8001020005642d9010003903a800540100c01e4480c00998944103403211500c0540251041900d02c08200c01d0040000709a07004440e01008a00851401b00e81250558030a01a10441c001c8580e02c0302c1495100303044185402102c2c0003a103e01c196240e00189920305084140c1c00031020105290007480301d4002c071580108840301e20140e0b4030541 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 692256330 1250 692255080 692255093
    0x20610050312071e1a1f090e0f0a12030f09080d051e070302070311060f0402131413030e150922090b04051e060402060d0209090a06031e 60
    0x703030040b8400c2c800000c140001408502c040c400905010aa1008800565402c3c07580702c6003059144c5620807131988001c07408117002c1c404078807081004034a401101d94184600007001d400d80f50100303c820300c6519840c030b0b1040024030001d02094444e854158244000341805400e03500548520302009280c1440d04001c02c09050031100884000100050035507101d0300b2700c0480c100c5201460415680e0b103020498039581503401400594000d03220180c0b1001e900079a40d40d00c041c2220703001042900d4002040c01410b0001c00c0d01006102d807000811019008141440408012a40c12441051039000b083c141500b1954000044005845004800d00810710207000c620034894140d005651200d00710490501c846001d03400781c810090305008010311070030814a03541d8242c4080d075060144000c80b150303903103041e014415410348900141c10103541d0303a000c00c04680c12201c44108200c0c2c080181c541903075180c49185200c1e042c24400058444c2c1181040641001c0d604840301140c0303400313040d19010070300c03 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 692257580 1250 692256330 692256343
    0xe12060403080c0a1e02070b04080f0601050904050c040f110a0207031a0405030412050703020904032c030703030e030102130611070b03150d06060302040203070c0b0606030c1c110313030206100503 86
    0x8101045d202c0555900049181c40d1a503848903e03020b1000c00d012841c91408101500b8003400d11003196860790b01ea02c104a00403900740e90003052b40e0310504603000d41782042e070403070012448462000aa041031003501030b5000d034450401c090050704228014010865140303465003c0711200303001a0664541580c1d8160b40f40300f80c0c00344040c01e452094052080103c03c004040c05141d01a00d110264101480d01420b0f01a444112207060500740624410140c1e110300b03002c000070300080c0144903d500e503481c1034400c0c0f480d0340c01950b01550208100d0780001c2c080080a0010b01060340c075800c0d0028564101030070b105142d0440c04064908005000703000419001400b40300382c0031526480c0203e95445c1020083c20729520003500b00b4000700800c440711f42c004802c8800d0714069a0304002c00d5940804010480c40200e8150343c07405800d0080398400e802c101e03921801d113006001e0004030506100c414920981003114078607004010b0512032010035505010158001c6049000100c49504003030020b42c4640 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 692258830 1250 692257580 692257607
    0x43080109140d0c140a020303041d060d080d1d030424030204120b130501240b070c030605040807050f03070326010515041a07141b060304030e12060403080c0a 69
    0x800b1070304484e81c501d01c24042948440e81c0101201d5440d5900c10f400240203100305185190702803003100246c070318201500c0728088603900904062406080c0600d03c4001c2122694400e410400d80100f0003580c68200001c001401c048017a10701020005008861594480c1c0510000c060052100700510403240c04140c82c0d81e81d02545400d10743e030750401021012984040003070715541c2007009d0219144200040038100c24401e1086021490710f40503a18414415424001d0401007080070810100d0704c15401960400d108034251851700030b81c1c1c4c90765490a080d42140351030942000031a9000c25400c0303074240c108043c111400e88400c070b41fa00c05c8150715a10520503030703014503900e01c850b8100c9107084003210b010303140c1000b854400c0b245240120080742c203c0f03a42110810b0340c4581c400b100c1640000c910301140321680c41020440c80304d009010040c0c001401c118180008540718807042c1c1d4504c881e03d280e02842a00074107442c58581030041900c5805001010600380c03c1216031400c43d8031031500c9034443c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 692260080 1250 692258830 692258843
    0x120c06030a020c030a030506091008120f0702030f0c0406090c0c1401020c070b07021315090b18010b0316030b0607030302090f0603010803040e010843080109140d0c 72
    0x941d211200100a880344090741400360000041d403400301601356000c24010101070703035180001e0b954201000c4d003040050040041c2c1d40c1c0180e00d00b24290100900400f0341c04003d034002800c001c0702d58013091800c02040390141103a001280e052a8034141840f811000380601d440902016440c0c0d036019241180400005d400e80c2c2c808290000110402d404440e91401500c00b01d0714417075130341d80b41500181c014403c101d102e0a072820740000300349014002c0e00805003030b24122880081c58640703548001c041c00041950410a00c03410140039013903e90400d4002d00c2c84a044685c0e81c0381160301c01c00e4109450988c2020b15240c410250050344030401a182401d6260030010703907074029600040c2d0300d00e142c51400d44d4414000000421604808809881110307101619400981d8842d44165180d00c00b03c61040c00040704200c00d140e580341e00c003840c509a17100c6981c444c9490b040c0e1525034590b054851f008085103a4540c0d1102341001525191040d0140114010740740035210507600501c3c14480d107401a250 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 692261330 1250 692260080 692260087
    0xa0b090103020d110315090a053702040902071a160e060f16021e0f1e030a03090510170112080c0d0c02090106050901210209060d1a120c06 61
    0xd50381a501041d0445030130048240c80b032070030809225842c4d61103211140241c1003803001c81d0381c6141c1030081901442c0445071700e9500f02003104034070b10b28800c20b05c005010407001000c084c020b003025200a00c09042c001c0001b69803529035080650b51060300c406190311400080d07040068201c00855201c4907040340c2c1c60084880703440500010128002d9084003010188001040d05215081445d0450346920030f50b20052502035521f4030310f0b100d600402d52190840380003030310380c3c0740c62a102d000f40310340ca084400542c01aa00c001d001c0b03860b1070150078089011407d003210038072051030040c0c00785664030010702e003016080c494542c82c01c03010141803041d94080e8142031491401c01240c0350607150048a480b02300c900035560000010f2060069003001d81c001c801b09400400d2040c0324608071220103906031100c120070f4503d079103070f00c0d80b02103030064500c5001c0c3c2c00d00c2049802e650b070000410300008130380340104626207001038184807012440940c61048070340910445c00e000d000f1440d10f400c0d00c000c44802d600d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 692262580 1250 692261330 692261347
    0xf0807060c142a0708060115090f0803030a0507031803020a0c0906080309061b03030406060509100506090d0302160801050a0608060106170a06030212010911152209020a0908010b0a0b09010302 84
    0x240c40155008921140206c0001240580d94000761845881c0c0b15a0b07200403496881d0010440d804c800e000342c40c041d40040000491900c13054201e141c10800361b00c0c000841800c00c191000000d01d44c0038044005030440503440088c04088c2103213101600ca401c00804c081450601156a240f090714012806820041a0100100f49842180a41e2104042505d80c0c0f80b80c81d15040005041c580a424480e4500c2c0010940314208100700303500b91140030b0005890801e050040040b41c03142d50b18201c0c03c601c110070030100c0c0c1e0744042c0c10041c0203000c000004142403c1018040c2c1c2511003a8200b00d41580c0441c2c0104500395020a001c8000302d40741a100442c0d440e071703504a01c0a0659074201175004228400762416143c015406182024003409a035000502d18400b046840c82501c5041e03001b420303042c0100301e210319640d45c2c501601c00c0c01d40b0b5004c44250f581d012040a80c0c03c0340c00c1e50700100d1101a000c002c040e00a01951220301d808859860744682003403007921060240000003410154003042201 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 692263830 1250 692262580 692262583
    0x108060a0e10081207050f070f1205071a120f090604080a030209040c0905011701031115070f05010b0109060504030812090c0a2403020f03040605040f0807060c142a 72
    0x8003d0a104400d460700c2e00440d000720540e55120301d40440f0940b14801801c50780400120701e25040c0c1d01e118103031002982c90075a000b4a00320f0601d000f640c45009480d0300203060010080220440a02404003584600c0c8040402c148544010711890401441d602008282140403031001c0e44150b00640300ba454401c0090110001e00880c82d189810900e010900104150051300420882e10240c0c0d5a15552182c0d500712104000d084c40010104c1c0700460420205240c032b000c9141420002c40106410042c084c0c0f105138510309408010388050b59125408071083d644400e4100c040d042e00c0c142185418650f07a1030030b40703074803549124980458104c00030500650080c000750000100c0108512455621642c0480910140b5000050a02c6403000030161140c002d0090b80c001d90000c054290956946441c0e0001928000f4000c9481d03503840229440000c4101018168150141800107008652800c01a004803065080e070015038206118070014611001201d01405003e0149401d00034040c0709202d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 692265080 1250 692263830 692263861
    0x303120a0c0c050a08030a05071d1314010306060914090a0201030207171c0513080403020f01140f0d050105061204022e1e050910051315030e010b0108060a0e 69
    0x80c2503011300c0d5901401d120200c8044c60190401010070409511984015034040b1840c0344a8101c0d01034290300020f161074800044e141100840a010500041003110210049400d030804c44000f640c1d41c00c20300c0060314034030501140000507140c013802d50401d043d0003079503280384110090405400140360420084e801a6a0407001d81c00c1010f580c58000d1482249a001400ea00303c04840b8980740003e500084083c13101d0301e10702d400c04072051410f401d540900904100790800f1348d041c8013040444051910b00d02c0010840080103825854580b0104c0014006440040c2e00c030a104070400d2141e0600094951500d45d0016070450b004e500307100307051406d04041e0380350096021040c01180300d01540d0a0b00b1400000181000c444800a202c00f40401560280510008260400b040d8481358480900400061824030144151242e0040d0b031800014001e1411101c000c0000307032200c0341c0d0050130200f402441c0e81c1e82d9003400d01c42240e01e000030100c1c402c45e001c2e109601c9031040d1180416800c03801c2503801d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 692266187 1107 692265080 692265083
    0x801180c290a0f03150501050406141308070807060239100905091008151302101e0306030818010c0506090114010e07140f160605150303120a0c0c 64
    0x822690414bc000030400802c41c1007001d503c180342105400302c02440184000d01189007880303074090501c03005a00410941d0b0001e045141c030050410600310090b040440d40b21120640075000400a203124000540c0250034a25070580306a4410021030036144199012403090301e030046992240341007442102c9203a000602c0b500d80038029503020541090148040c6920a82c55400080c2107494924002c0040703004142420390303142192a402ea0151213906041000901e0f6407682013040c840d051503d084140c4144841d4a41d85c050455102c5060700311003100e4031842e0030f0002500030036a0384058803041201000000c0c54045141165224004c0d070342c0c41040307180b0807107238202082e0010220440c5003801809135640302ca1541c4203680d01d00740128800b090500b05405900d000058175116540a5001001035092014100605c280c000300403800000307011100c00b20032a54240b05403070 = true := by decide +kernel

theorem cover : BRFrame.Cov 692086330 692266187 := by
  have h0 := BRFrame.cov_init 692086330
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692086330 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 692086330 ≤ n) (h2 : n < 692266187) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
