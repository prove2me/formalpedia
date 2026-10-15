-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4660
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:19:41.10008+00:00
-- url     : https://prove2.me/submissions/d5ceed83-6b16-4e2d-abde-f9fb66819858

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 837949640 ≤ n < 838129496 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 837950890 1250 837949640 837949649
    0xa020315060c070f030c0819020a090b13060b180d03050a180509010308031909330f0209100302070309030b06040b13020c0d090b090603100e09010f1803090b13 70
    0x201c0c0c20030365a1411b074056803c244907041c80350040042035003a00c0d4508900c0d8040550051000315060700309034007100244185629150041e40703c200486108147d80315200180c203c0140706510780345440e900d40c03942103207408101c1c0039621104c840340000780c000d0141d0f80410814185446007407404500c101e1040b45983c42290720080b283e0001081c04400c100450155540408911013040c906802c08143c90090200509020100c2c01c6100104010b00392003240703403400303603800d400031000480c2c4500707948148050101d95a800a5002214500004034a0315406d19041c2035041c043c650700c0c050300305030007440042c005020510004849958590280890394402000030800303844104040009400c155130003422445035400184010340960340d048201c0d103810f00081e15160310502400a107410191520001d6404c42c030000c030f07a000c1e40d203414500c42c804c50000003803921901d00d0102e065880190300c1c00b211400080350b03c0046540001d06c50141d4040f40c4809996521142b0440304080e04c540c00b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 837952140 1250 837950890 837950909
    0x6082203030b0906011706010f0e030115080606010c05030a03090c05031f1109090105060a031824020a0c030e06040b040e0114010206073c02030309060a020315060c07 73
    0x15008068140c1c1c0b01448146094075000328560398880151940410782100140301820800010443e6100b640031740c0701040903141801d10f80d5121800309081d0b40704000f000d0310002c0030000c14404c0d00c0701000f51543c803c0003441d01c00c0c1c0824041e220780f41c49104000b680803c06840c4c0508109029903805031000901018044503040441030080030031501c02c0c81304c2045072a04100c482000b44002d00300380c1303120444c003c2082e0a80c3c0d20744001c005060380018582003d2644a4400d040c90700341100c902ca08a60003140100500c600b001d0110b09844800301424013042c4c81408607803500c99004090582e40e9a0505091071625269000580d040c001c82d0b0009003101030024012031400d1550031114102c600c115212481705401c4070040e0384807041158484005004600183c1c401c0203d0036144040d40812507442001c000306d100107e515990100100340580c0c000001c2c0b0440075400c000140d804040c1100450660a10580600f000440c03407450782d1181c1d0004c204143c40000c14040100105800403 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 837953390 1250 837952140 837952201
    0x615050a060315090218041e05010308120c21130510090201030f050f1f050603010b0714062a040e04050a050d090e0118021603091e08070608 62
    0x1103004001d0315200310f4000103500c00e40c400081c9041c65000790350144441080c046510060481404001c000b03450780e600040d0303000910f02d08010614481c04d800b943c011500c043c0e1302c4000e0b50b418541c820000d00390700c0c0702c14010819005d01e01d01104880d203400074441d03800095525105003c3c1081d0380c002e44041c059005490918400c1c401551144070740b10b100781c80c244041c010955005045680440360ba89100281c007001465461800400d1000b0400984c0f42101c61501c0300041000c1e07070426002900c1140300081ca070014032191200007803000088800601e50382c5000319442e05022060b8080074000d03082d203000c400c0120001400d440140081041c0c0d4030083c80e060604c0342d44d0b141d6940081d50640200440400c04c41c1c406d1010000790340d2039551100060b40b0300030340b1544504180301c1000300c1c0d0343e0034002c17080011031000e034000180340281c3d0390403007041c101160540340c03030300c00c40e500308424015107010048407402040a4003241c2150074071240076035076501c450554565103a9089210031094 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 837954640 1250 837953390 837953399
    0x50307060c031a04060305060730060303030b0616080912011802090f07080402100309060216020306010b1e16050601092313260705030309060c090109030615050a 71
    0x40d4803200115030840c01c00140301c6452024002110042e006c043c10a802190001e070040e40141c00c04c004101710000a81d42e41d00340100c910000074221010348500e541c03103035020001d040d410300503001032032030403540030b8600191080b0000315000701c40700080c0300000104101c00301d517499940300002940011300a000403c045044807552042c400401c070312030b0b1850340210304200e01010703600f44222010703102c110382c5803945e03007c1264124880c0186000c064440c4070210000d611400500f808101c1e41c9009114141c440c8109400c1080c141c2100c148030005002d004c207250960044504c19104a046055544c1282040040640307928100a41180701e901b00000381c0300d203e5808200b4045920840c54511007520f240d0f0248620b06880d281c0b0085c01440040c80468000703440e80748001d40024141d05c103244800f2181d900380c2c0000741d00351120f401c00303c100b14441c803003400b03c0c0349c1c4295180246441d100712100041c201c0c000f00c2c00094066661400240c903015039540413100646001802c10104035981e = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 837955890 1250 837954640 837954647
    0x106030f061104060c030503040203070b0406020a3302070510020313120305011206020a02010e0f07050f0906010c140109020301090b07021603170a03022109060c041d04050307060c 79
    0x5204200d900e01d1a010b18600c1c409440001d44080ea815543e403004290110f840c01c59a5400160050f40e15000c0c0080009002ca500700044c0010719031900a0300040c0d0f03a40c14603d9000d01140302d404d281d40ba03500000c901740e40010f054441082d812036801038840445041c054945490300c850700da042440002441504071f001ca0208440d50320419a03c07416600200e021400e84100780702d07c8114401c0341c24200c0c00210250003901400d030f0148000506442c82000e070074941509224490065042201d040c48541450035604100d968282e4400d20a410002d000078100740341c85001524400140b403890104410a400c90303e400c2d41c000700203100c9014141042c500008040c5c52010140c42070742c00c0c0380b415920103075100303027100e030031204101c1500c220068011442d4400110300301019400c0210144d0000795025490b50204c005071030b08000d10b421250359151240103072104150300805c0c00b04000d03942c4181c015200005803c00b403149141c40300e01e4898514010f001d0010b01403410040c1d9a04207561 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 837957140 1250 837955890 837955913
    0xf06010308030f010803280e0a030b060a0b040803250b070503180a0b0f09120301080610060810050f01051b010509060a09050c040c050712090501020c0604050d020904020a08010603 79
    0x10030300b00c03404491741c0c2c0301344640c0e403846281d601c50000340f00e0400c940c101c00b08650120200950500300803040e501040005002140719401c200c0b0001d681d40b080c404182050046007010700500c0b4101e624281c1005901d03032b070b04c1c001c02c1c070f46401501034201000200d22a0800c40070f0581e502c05216207080c2001600545907800c00c842e5032009442c8aa07040c4001c1900283d05032006800c0030152180d03446e40000c4a8036054010300c48181c41c41900e034420001c4803010020760081c5000ca000c1c000b9414103684907884144150b01c80f0003000f802c042801610352300c2118150803a041100c1c001814510600140c840d8040c040c20404407107001c040100081406401091042f0001e074141d8400756100070480c01140c0c0d040102804940c4603028041050030300b130340440f0704401c0a050003070420700e51f641e444400c450306588000000318003400030841942c04000c0c2154840302103491500703240c140008102d103118078000113481040d01a01060a645a40b45683e0207080114003d01141e44c8030b0904101280 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 837958390 1250 837957140 837957151
    0x9020307030c031103072a0602031801090b010902031005040204030f0b061e040b031c0512010821090f06040f0e060f15030417030a0e0d1d120f0601030803 68
    0x2800c001c2c2c40503526109100703124100b000b803000c6078107545030b007074048650780301e140401c0907044607910420720b4100600400c206014442e18000d0390301d2914070316225600504ca0050003550b07040089078000201d5030801c071030540390301c2c580050300d965502da138500d40240a540901c0e0014400a004070501400f81c14150741c403030040044080d291a0f070401d00c4402e000c02c4a0824502e6009400c107103081c58107420154080704010125580001c00500582d08012a50b00001c04142c00203074915a6144203080c00b401840c80074041d240840301c01e0f40701c1640d42c441c05106a08144000340c0c1c1e140560320b2420b60a044100500001d072215160784094450001a026a070a218008000219640380a50b0748007980c0d60043d01520081d000e40450640c15080500200e817a0742c0030517282c49408052401030b510400d40704030082025402d040310607040682c01034601c0100b00190741c1154041c40c14114080382d194040d00e500c2c0d04000c45400b018140090009010700a0040000010602105201460044 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 837959640 1250 837958390 837958397
    0xb18090408120c0a300b0f130605100305061305060d0c03120306050d02060403020907022a04050105120c010806130f0b12030a142514011506080112050f0709020307 72
    0x54100d140c4c1d1a054105c910003100c44203001044181e1480c5880e000300e00440006020104950900d00015201e1365a150a00c8007096640c5010031091a00141c240401810703410208041c0c104803002c0344000d440c60703201c0f4103a280ca43e4045aa135071510300500c4042070300040b0f4500110f40320b240000b8000d204a0445001a04085021031249040002281041c1d0b00a00c25458603245a003070010b619402040fa44c29400354203809450300c903403012014401c54161a410360081c0492040200304c40301070300000c4c0543c288040c035030004100080c041f0741211090034003d0080c0d4407480020300c0f8000301c10030040d1143c20181c89800c92640e0303070010000388004980d55846c5c00c40c64840c42d940ca00580d1382440002d540d51084e804608400b200070150795014490740880d03403030704900b201c1040038290800c40e140282c001d155603040b6002c0c4180007008410909034a40240f8041c001001442d060003103080a51800011301d040060401c41340217841c0352001510081c0750380d03040c1980203400444a40010 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 837960890 1250 837959640 837959657
    0x26041101020f0f030301030b150a140406090c08150a050d050f15070f080907090606020a02090709120308130c080d11070b0307030c03110301090609060b18090408120c0a 74
    0x640c203001c100320f101041008015403e680c41e50300c4007080c20303030080c011502d12100c068880d002510b41d142880b0250103070160580030070720000b0a01c07044407000c0d4000540c040c640420b80c040d42c0d038004c2e010740d004010f036555001e000c28150002001032025500c401c0c1c0c86100300000104114000ca00c1c011004098000c0c0d54480300c0110b60341b5801041144ca400025043c05081810140107603041a000003844080b50320702c503251280141100c503140c00407000f690000e070b186411440c003504842c7c2e010545103440140b16262452565900300000d0f001018040702100085510100420511040e50855808045203560740b4409489420030210301001521240d0385031154000000c20340c003200c502d81809491903640c420105c00400d11170341c5280801d503e0340217410700007900030040c6010384800403000420624285402045039aa40c2c800c005807001403004000b80304900d14941d6405c1e105643d9950701c0e64442c50060694812284c8424044540100f88200701e83c00760058152030615071a4a0786 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 837962140 1250 837960890 837960913
    0x60a0e03060f04030e060a02070513020316140910020a0605040b06090702010203040f0f21030501150c08040603021b0303040c1401020f0717010e010501120c1a0304032604110102 78
    0x100340c2e408a6010b40490300f402e080e9505800c140c4010804c60101d07106849126448500007103000540301400b001d000e40110501c0700141034440c401d20440e219040c032100942e20404410b015000d40454180b00310b2070f901e10b6412290081c00410900c5071f10100070400c1e0301e49460002d081100039a00c890081d50000005030207503005102710ba0140b42c106c0001d50300b01c0025550740d4000d000c5540100d038025490001001c21441e13452003030300c40c0003241d10041420f40c1404d910200030782a81013182c0c1000310b0f48400401103114901154282c07100351801581c1d8020101102c805000700c604090b91a00c0000100024041e0b038108003809c1d94800113084401b50040301c0120303940d42a03051800141e80000c1c100b0400300d0103810002445401c820004201070303a054003841c1c21244240d0080341113000c0440a20204844048000090249501c441a0182810300307160b80c0d13400010320090a204544045421107200ba188d10f103001c030b901d060060300350320700f81c580001c02c0310800900902502c184295903030b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 837963390 1250 837962140 837962161
    0xe03031f1e091e05070903050c0303040506071101050427060603020306090f1518010f05031501090e1002040902070201110c220605090c0403140d0804061a060a0e0306 73
    0xa4100c8440c20030311801402c0c1000c42d80101080c1030704903905000c0c40241d10100d9107900525110340c0d41030700e607040301074610f042c220b0406200c2200075101c0d03041040706011581ea0142a2411685c02c00044020080700d000103039140d00c40da800c683c800e05070000710b204081c20030980315490284011410b004035545c82c14207030183e000940b6450b034030420080004445541381031245601c64410404c1d102d119151304049042c05900001940c10540b01c2c40061004ca05007042d104020170b010380040c400c0d10030500000c40e81c200306000304200340743c03243c5050511501c100120b41015000d20000c550b1182d90300e40e108000d50104070f049010802000d00d541c0d2107a40803614800040019140003903a51380703c203402010144290302558595510f0a002c070791030312040b110074854481c15110707960321030070b50401025944a00c0701d0340306d00d580a400103000042c1c0c4030589607006640540040b07801c0b40ca49400041c134051a001c1c880d04240082002c420003540302030f405001c03d1043e030a440460300e03822040d4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 837964640 1250 837963390 837963419
    0x1e0601030c090504230a0b011404060b0a0801120f0203070632090f011205090d021506150a030f0c080109060e01030f08130801050c0a030614010e01120e03031f 70
    0x10704100302170259081d101c0007101030554885500c000382e601d500030996464690607401e0300705650010b0096000c00280c04d0a01c241d00140c180300b01e20a013402141c080041c100c500c14082e0801c619003120340b08041145082e900c080341c42c1d008050700c640c03640780c00b0002e010700d2100d02c2d8a00c030048805200700018092400148007081113480c11031a000802c1c05003c000083c82c034106041210002c3c0d1090450100d205590140c800800541900ba02c001002840d00051a038140d0342c140b114414084180d8420708142e98107030b440503e1945a0000c400c040d4003c004506000c10010300b40490106600c0e8080c1c0101c0c140c0306090810480a80c0300c4051a0000e1800d0100400e014901d2100d2030200e840500600840c8100840c1410400d0719020524296107058540d80e0107406c000c9a030b407202c3e5415014083c00340500034100c030004003000e80001d10502c6c00005240c180b28140103254400d125a40007481c00c11084400c9a54a043c201e218aa140804046da104101c0390620041501c80c20401e44 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 837965890 1250 837964640 837964643
    0xd0207031b15020a0203070609060c03060b120a090602090d0c06020d0f120e0309151c0203091504050316030801050a080708060c13360b060d0203091e0601030c090504 73
    0x141c0341c45807000441c080084d070042801205610040c03141d400054001d002e004800c610409020a40c1a246440641680c50f25084140d01150a101d425060080064825070003552000041108200782c24030200070303c03c010b02260040341d0410300001b8492400024000c40301c682c1d0845480c0d0500701d5040b81c000f50303500351080018001c0d402d942c03043d101a81140385217a98100540385064182c2000600342c0080c000003981005003c9070510580758110f541c0700402d555900c0035491494224801601d4410141c100c030001546a004502801010400d03928006400580c0d4810300340d141c10b020703190010901c0303140e10600c040c40c13001c200c1c10f40c045518421a5000b00040010b82c6884a10340c4d1107811401c880302c00050403600010b8103c200a00c480640681610003140000c6901c02c00040d5810f01c1982d6042c190a0841c0c010960320740da021200702444141b801a101e0310354810300c905041c1030101e0346008410f00480c4000310840410614101c9115407045a502c1b551889440300340c0b10b00315030 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 837967140 1250 837965890 837965903
    0xa03020d0207060e0a1a06460905010803123d1e051008042d05160620030f0408010b01120b010212030a2903010e01021c0e030c030d0207031b 62
    0x4c0c0f445c00c00b03d03100d880110030344415609006110b000300c8c01d580003414010300c0079224071800904000c01d600c0c920800e40900f02400c082c41ca010224103003500885d00213042002d0072400c0604000030000d0190780c4048880b03020142aa1a10000380c12044c501c119010b90440300700720003420002001000380c908200d880c0605000001d4414180550780f940004206903189000401c0d0500d074011465004c0281ea01c840d1090300591442d810300c40d160048008482c450640154000d000a41c0c0190040b050035284075107843c0304100607140c003425400380390030083d610b043c04240840c20100c19004407160140030781e05c0210788180e012281c0d0a80310882030b0070780960025006480e880e9060b000556014400400103d07004813072800c4501c20304992210500340e040c442c251404240b4007030054000c042c000200a5040800fa00e03006a4255045e8020708110399841c2001c05624206000350382c0c51515020076203488282c80080c0b103002c1e501c16241100014072020421280e400000c448074a026003024 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 837968390 1250 837967140 837967159
    0x1e0305100e04020d080a020615010f0e0f04230612060115080402010e09072012160218010905061504081e21040e010504110a03020d0207060e0a1a06 65
    0x40440107841d4020b03000b40d8200e0f440350340391340120311441d00070000b074880c1e03900524a51030f05032488020200034882450420011403424500c05610050000c90202d0072680c41c0000715440002500511504061143c0004400112882c04002d0340300e44d0b108032410b84070b142c0c202d0f51402d441078507403100f4003482040c01c8208000000c060300c90094a070b8094410b04004e5181c149503000074030b00950450b0741c48000b8240107403881c0607060004507511446803000c020300040c020040c18910354065940901c14000c0034010704003c0d5030700d00305a40e032204082613016815584501640d00501000c0f1181801904c102d20300c9901c1c040c8400495003280e500d0700140c8214030150044111040140e4010300040c0302d5000300b030000ca80e202c8150120802e208001581d1103140804079002044140e010078031951510250035204e0b030142045412100d040c1c540180d5580e0b000641a009015004010341864170301007028881130b20025808222034085e5803c1c1c10925084101500004000c6070b0740b640180c1c180 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 837969640 1250 837968390 837968399
    0x30305030705090d061a03240c0d050108100b031906050a091e0606150e1513060c02011101051902092103070b0907030f151503031e030510 61
    0x54000d1500500c0c5441d140c0c0c6011480e4000401403107848600b038510036070701e4490070b03a20000020f000c140c526040e4050700c20305e4100c2c403030b041810543c180440742910304000001c400385840300c101c80c03610342040740400103940c44821a075680d050143c100214140352007040c03262441c1c00100300c13604e59010380d1800d0315511140c1d01c41c0003a200c054120010103440d42040f10000d150850400d610302050308014801140074282001610a542e1103291802c400709080f120040e40403600542d0355506031107002c415010141700d1001e51098900c104084018500c001c10700300c0d0311000300302400d4001d90701e00946641003512907003254400d6400400f0f10003001c0c0000c14480081d005003403101c4004114820103000000091426081810905a01e420006e105000c111410700016088000d050080602c0c90950f981e01004416100c4090241c1d6918820511340c034440390404c00004408090140c1160b54038580507005002e15034461600074001e05101c0505842442a030384554440c1f0044000710b80f50 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 837970890 1250 837969640 837969647
    0x150309050109050709020a031a060a030c05040e0f0a06080c0a05310e0105010b0304110402090a0503100606083403020405060304050d0914181f14040c090308040303 72
    0x4550200c415548030408440400d005201900082c2000d0501681e128083c000050895aa1484c0240d0024020500100c95141c0c40255a2814554200010604c44450099a440c003907580a685c102d4018020444103160651645024285540f030034004a901d680380903803a1059800c0302500115101c100708068035000071a1941c000000c421f0168014a200854644603440481e60869540740c504401090788241300b0700d801400810011070031750411380c4e18504401c880f804401c2c8180d4020807010581c1e0340d505091002402c00504686001e4000310310724001d01514400c0b140410403100c005400b010403ca02c02c08a000c000f0340041c1c44007410500028069400a8403000b0180e00340000324242d11070000071800383c0c0c043d80080c0b005080d403000c01015041d45401441d51424029610100303a10383d902554030186e60000b103100250341c0c0c0490003290361000f061085041c200c0d2500020201555202214980c030159001c1c4000d21108000b554400345034480140ba1640400c004c0000c0ba11 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 837972140 1250 837970890 837970901
    0x803070302043318090e060612070501020703110406171c0e01140c0708070303090807090218310b011403060109030b07032309010b040b0f06070f0602070b010e101503 73
    0x201900451001364449050804039402d01211409590000d407d015a5113000301840d1040c00764070740104600f504000001f5261b80242c8002000c0070841608040c01d070381e0303d80044010700300382c03924907040c0300403124402d50b14040c10f038a000c4080c200c2040106603911402070300203150410386400d1000720400c2c0d0091840d5001e080d130810280601d11011500e69420b200800003540240d035000921410171229508111150713210940c900e2040200c40c4014201149104e0035041c105e03813640c00c2a86100182c00c9000c00c0040542e10701005034504a190287d07940f09540c82d0000380d991040e2039103c03400988082c801507600361f0128407007007001c000054001c2602640325485281c003050594900c503420002104800c031220075000c58404220419400344541d1500e504211814408208520003042601503912001d5000d448005500c100307000c1250602101d46511280841d580c0c1d040b4200740c9582c1100b030141c004542485c4011071a0001004405000e0320900401110040c5600505400604 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 837973390 1250 837972140 837972167
    0x80c0a0317090c1c050f160314010605010f1d0a0b0d1a030604060518030708180301090f060b040b130902030c1509012604060e100e0318040908030703020433 69
    0x31038580301e920b00130010b00c501090f904c04580402c01f0f00342140b0344400c0b03551141282003900e038580765041001f6030344406821080405414085d0301500007074031501b203003104801420f41200c0d243e0800120b0101d11001060600c0c0034810810181c2c0303000843c2061840f815049aa15500074000728010171410f0b030010350004005c1140714450380b08104500e056070001c00c0c041c1c801e204003152020030141c020041e002441d80840003001541015500d88003203410300100075100c20740d04d004503103c946175580407074105400180001a22554480c1c4003000d030484000032130090284010b40320031f07410603585201491100c12270f1681002c95040044a202c042e0b00001c07858048032060349212220902003842c000c500511010520b180784080552a140c400b11018000e180b9215440b80c549401106403400400c4298055003000741400c001000b501d000c503005802130000106100c1d0898056006108032307541d2055107105400040400780461400381d0b038050f800740b25880e940110501c5002c1c10385200 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 837974640 1250 837973390 837973393
    0x906030a020f19050c0601090509190507081906060803030403050301120c05040203070503070206010e06010203040e09030403050f030c0105010f0311060715050a0b0909010225080c0a0317090c1c05 86
    0x24020100d0f842450a5010300481d40c00200094031000905c40c960161403c410140000d0030458185a5a506140b103c500580c00e42a280b00400c40103101800040c0744400807100c00f00070012141a001c5000441102c2640c50000f0015845c0404002d07284210b4042c0c843c1400c50b031801d403814201c3e40342440222065004000c003c565660b03284082c50250810790341d050b40760715106030081e02d00b54044e0071241c800d01c605800c1240c00e80c0d001048800766840d4114100b0f198942e04025484e5000e503802c0281107001c0d001c11704801fa100000030307203660100500284070030399031420010311106080c04003900075042c3e403840784101d050850060030303c60b03c60030044282c1064003070303260108c440940f12840702d15142c2401c0202842c4c00b0400f240c004517080002c5103001c03e4000c4503039000d04843d21b001c820509680034074040c03001107030941d480e0300110020345801c55444d1500621104000c1e0740c4140324241c00c008108080f600054034039005001400c03000140700c02164412851038654021984c0713 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 837975890 1250 837974640 837974647
    0xf06110129060f04151715130e16060309030f080c0d020c0a02091005030c0105120a0e0f01020304080307110f06041b05130b010e18190603050102030f01150201020906030a020f 77
    0x5c2402201d102040e080142d503480014407141c84003a050a0320213040100400d068031842c071559614001403110040400070f0000c0e411011400302230800140c503800b00d00344007040d940080c48a401d9040002e0880c0309580c0c2c0c1d25a00c0b111042a0f90782c0034207880e24001c458041c009001500c10b154014480d00001c2c0c0221100d0540940c005907440b4003c44100e2040c000c0007004016504040100c020480024200242490a100c0349248009401068414126100c0d8202500c184062000601c6103100b08000d42d940d00d014141150658001d45030100041e201d0029509502800f00308600d65602d628003034411611152101041b040f407102100c1920200b4200014041e60380400220807204204c030003042c03d454500014241901c600d20089c003800400d103402c0c018807446080c0340d40c02400c0d10300c0744102e1103a00c043c00000300b01582004001303610000902c8010700705c6c0c0c0c0349075040701c0901c6402034066000b06400c0b8280c0c0520900d003600200c0c00d2012a5083c03809402070140c1ea400c000000d0309 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 837977140 1250 837975890 837975899
    0x10801151b111207060f030902150d02040305030703050a020d0923060910030506040b0a030203120c031b0f070515090d060b0a060503040c050411180a0f06110129060f04 74
    0x110ba00b04001074207240c4c0a000c04212141c0c11140c241c0740f001031810300300106590354000c0751a51011900e48400c0a000080004174404541d043c1ca0107190880101c2c0c8d111a02898094110750003c1b0000307001d0700c2150002204944210210b100b5202e5504c1c014121000c0044988410078001c641c8960080040c0310100b403548403008003040e11503c035903000c1050f040c00c0042c802100c10724184203002c1c642c4603c0074409070301c6c0050040070031052224a581d581e4a1a5203160031740c011a464181440d4020211b0812054001541a011070044056840300e07982c0304100141d01d080b600341e81e1030340342c0240320310001d40c602000103c1d075081c0240310106064200000003401042960000b4011a9000c0300388030a00200c03a030004060142034070200001d0031404840c07441c5d40500500807030080d44a09030250592a01c0f03000744010640904840b610307580320350003d480c204035500e140c1c00039848c0040c035103010782603c181c000d108211880e250303c4001041c0140040e45d48406201562400c0030040000c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 837978390 1250 837977140 837977149
    0x60f0a0e12240c040e0a0b041b0f020105070f0f050c0708010c110a050c061602090703290904030e0a0e1f0b1206131d030702010801151b11 61
    0x40035103400068088608000c01407000b0b2140c6440004220075180d00704140f000c1500100d6094070341495840c0c0c85a43c0704116140030f05050307181d1301d40040c04e2030080d594805080c5c0720308204c0083c42e11041e4040320301450403800c0311011119000003825a080003406e650281e07108001c0c0c10100c0c83c181d4604406103030110b140c04965444070400b0ba44d42c0209807065540087c15840080300400541035000d12900d07400d640701da0200071144a404000760320159810402e4900c00c0b0254007400076a0340b403074024009002007610444504060001c1410715500d0421090b181110b030000030110203003038a40e9102103c01d01114a0f03850303040300c2c4140000c0352174020103a0941c85242c2c800d21a041402d80160802941d000f15440050340c9142804010402c1d071203680303030583c010b0341510b50401e44024000000043c0c101500b103610401c01c0c01c000040801004001400d10324002e032950003450340e0310703a40361102c601245c2a000001c0c0c24156061480b045e803c5070005d802d8000c0217040558880000080c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 837979640 1250 837978390 837978409
    0x2409140307030c080322050705030c030607092304150801110c15071b0b01031104141f09060602070e1806130201022a0103061a0a05070203240411090105060f0a0e 71
    0x607503288d408448104413a2500b001011440c80c015070142c44142031840700604051100e001e80d512000b07100c10380071103114a0419482d425140208140601400d2280200e01403003d4055400554240308440d00b02841000445a200100e1001000040c523505010f44444102030003020800c002410020030b80401c40b8018106c960245d543c4201551462a00d40c03658009202200e0145041c02c5880000d24801440640c0c450300410491024072240c19500c40c204025820000ea07685c03500c030021135403075400604d8405440d01e401c0082d41f261500c180d03014078000d42040e80483e6504c004001071542001c40d40d01c0d80030074810300403510360a1284c542041658254906007045800035107289250f51303810300400b0300801c410007030110080112030100415106402d001000c3c44400120300c1c0440d11b0401898040d06c40c0c210554800d00109011001c505009540543d420080c2282e90342d00ca00d03000e440c5504994000744420701c1c050105100e85219082020807005115110210084948406000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 837980890 1250 837979640 837979643
    0x9011d2107081501062303090c091806071b06060312031508070b070c150c0210050901200f010504050c18040b040305072409140307030c080322 63
    0x1035501290222003001e16002440c1d1008407983d01c240300300885000c1140349241034034841d261050a004400c0a055080390643e419107000d12000420859410404129200150700450300030905031500385501003828945404e000060b00400d022030107541c06190f00e582111301c004e8407103402d06099161041221a507900640e450343c8034803041c80ca400c0c1e040c480c185000110344001004242002680c55a50041d4090300c0b112800015510080c4030051540758000e1000880201c00c10681040050440301c0002089010b6048503011106c80d0b4040e80660314002c10607580c0420000381c044142c4000c4c0c01c540c2c181c0b10300e800f50b00307420441c481c0c0a00540e485240610000c00e50244544280241d05a00c100c2406402c08480e01b440000740d0106500740d0030540503c1d2550700e8441ca400c0030400311520507009840c0c0c4c1410880c3c4400e141c0a90090700c50300340035040407031203180f4501c055a00d0740700d0f9210090016000d02c94500000b403400c8050340c0c01198102000000e160300ca00c041041b1000c281c1e0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 837982140 1250 837980890 837980929
    0xa1406100f120c080a1d0a1203020f070c03030e101407060209030d0f0e0f090604050a020909010e0103020108010609060c0311010608030a09030b0105011713051906051605040b09011d 80
    0x300b02000e0618019848035071b58250707400358000340142d401d98840d08481c800800300042a5044440c0510139015903d4040700004495500c8440c3c2c54001d0011140b4401100841c1c00d482518503c4c0c0b5100c004102078800c01d49800e940d10040707042c200780940c000c0c54220b034040d40c28040100303107450400521030f4004c40340e1038030302ea00c6d09200c002906010031400302c1d074420070142044104c5a1900c0352215040041a10046a1512030140b103030302034080c50303101d079400900301c0d000020b525144a240700d040300d0007038a56085a036220342c401c07100740d1a07074080c200c08a184458560000b0b031060240046c0100c1c1800005a259105d140050550780120300d8400050040a01441406420304415004282c242040582d503100160b4965001100418600d8408204c4d2821024010180308604200400d04505402c5118074070b003420007024151860000182a0492044014003800840d000c1e140c03080c00c0d080c103041c00000110740d41c030303c041da0518100604e0041000340f44c070b96103010080d0240e9501c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 837983390 1250 837982140 837982157
    0x6052203120b06180603040f06050f0f090705010e09060a09020a030e0c0f01090605032a0a0e010305060a0b180d0303020c15010e27060408030a1406100f120c 69
    0x106040d042c2c03041c040c100761049074100b11084560104a540900020003035071051340b01d644500700f41c900750a820002030011414a010480003000300c1d90365510898120a230039070320f030b203e5404c52a0340c1d003030740e00416001c100145082001071912102155001500404510304c0a842c0d00b40303c01030303800500ba8000825242d41420000150600c44181800300c1070714100040810480000c0c00c8036924070809050040020101700c0004c2140b00c2c800c82ca4603d50114290700031900000f240d26408540004001966668110b0456221340540c5005a00c0100180480c0d4140402da16140d40300c026081d4a40080e82412103403510340050050826000392001601d520342d4510040c1004100180382c0382040641c4c00600188002484890300f10100946840e46c40700b0342145c1d881d09041d5484100860f1003080c041001300941d4400840c4140c3d540c0700c0c207000c1d1002c01c0e5001c0d5041c24068501e15802030000c0d00120105104807800c0201000c5854624207419000c20100211170403c1d180b003002a01c000e = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 837984640 1250 837983390 837983417
    0x1b060307140c0f070f240c0f060213030b0609090703140307050a0506010e090303070c080d090b040b150406050d082104141207031b24020301031104150306052203 71
    0x71300c41702c00a00c03420140e01510318440a5240190207005005414840040c0d455004d220550714089070b407a0b80400c0071903407425145041481c01100d40f108503070b200e404c540002d0260030a1030f50540200805070007492200c0c150b560b011442c010759007038042644410310055010030410000500f005015401034016035062585140004400401c6400b082c1c0c4108240200250b02c00c0e40342001d070340c200407900e450300102c441c2c1101402200710060502d107100c0f0240410f025000b49214007996800d5004010b481741c0740241f00a0b01c2080c405c10f5805510f25100b20080b0f506034000b444241c2c044040d0000328000e00402080c000801c2e134081d91031044030407071a1035404040001c00740074032311011000c4c180f40d0182d50050618442c4044110000301c00b0030700c40304000e041d5042501c0075604040b60310980850515090080d0424031003525819288247e048450502e80303c1c024007400c080f881056164155103c0102400010380081141450030020b01c10007030503084089c1d02d8070b219070703503043c1c2c0c0e034200 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 837985890 1250 837984640 837984659
    0x18170c1006180c09171c02030d0c0e011d0d0606060804050f01060b040522020307120f113406061d06060d0e0f0f070303021b060307140c0f07 62
    0x4002d86107818941240b482815400080d64070498184020446000f0700890086040c620700c941c044400c008a008404001c1e50080003600c0201c0b512501040403030340c0c40c602203505244141c3d1150104080021f61446158001401a61403c001e03002e114500803950f11035084602680c0034100040f1a00e081c80100b017400d01460b08000325041c02400742500703165090f03101d44038034840d480c483c5c440711900f60342413800c142c90f034103400908920441d1a403600503409040451151007414045117000369401c0e94122500c11100da981c40080480c1c1402c1c401091400d2051006410881860b0010003c0c4c10300420f00400804581c402c62000c5103091a041c050b2400f05552103011a0b4611001d0400c10552107101c25904500b9422a0202d080080071f030071a801c0441011055900c0e000c2c00002600d1030000040902c2261710960880d010300c1800b07080041c145404e20344442c0d02c644100041001c15101c0d400e00288032000144051908104101061400000b00c91040d010341103c0002c00003c0d0700d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 837987140 1250 837985890 837985919
    0x31c0206100e070e090718030c050a21060b01171311010215240607050307050601080a0c0b090a1211090106021506040c0c0c080708010f18170c1006 65
    0x401068154a400c0203c00038000d00000c00c522030040a0070030005203494400d2403003000005081d0052160385490382811350100101e07001d01800fa0784c0c040000169010310003615071034070344161110400e00036982c1c1d680c0040d00070b0340c1d111810031a20044188400d130b541100203000304d40300050072f040c1800f11302d00403440b20f85402c151030554001ca2045036840404e40511940038150b05030800d0119600302c20b00310740d00803058101b90018070104444041088c000020580d00d401081107419030380c3d9540540d07a42e103049a6004141d05448a01000030380c40b01e0024000f4000000c0421a190b5180c41b2880016004041c0035904890443d80c070003114144000880e003d800c00e88058150307540f0103000013022210240a0718000c607568610b07220003d10440c0301085095200c414654104d9565020581e21078a41c050f909203035191840b80c40c101e0005201c2d4514408000200c075488480d9600d503030348103901c0079050640081040282074a03040c418450240514200ca80000f604c6d81032030a610203120 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 837988390 1250 837987140 837987149
    0xc03041811030711070911030f0108011b080a0f0207110910051c05010b0306041412031003140c041b17010b19030f0c0801030b072c031c020610 63
    0x1450200185080301007281241e512a10f2824204005900d07480d40030b107400200c0d445048510310300400042028181402180500d201000401c0c09980740c003038007030885100304030030f06444031403c0c43c1184641c040c00c000c035440340c0e8042000039100c940b030340c0a00903a400b0003402c90302202c94051007036070343c2b42000a4580004082d003c2c0c0c9061401e20010415080442c240e0003601c4409006400c2000000d40281e00120405000e8882509007861b000c504d050010211000c9800340100d6245c55995074410f0f24811321005105880381499902c0b9001803405c1c1803400c2d9803a0040317034486040c94956000d0030b00e010020b2a040302601c0f4012900600035030410b10241178500300c2d000104010080d41d01a81e070b0384070b80485040c80d0380700310b500c00360020f010b41c0c0a0342354200d04100c5404202a001198141201e0003802241002d070b4900c5411a02c10300c030000c003085491030030307103003403080038145001c80d03450400c0602200c0d054680c043c00342c600c00318261390280060388440104100941c1e869400030050 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 837989640 1250 837988390 837988439
    0x702030d060b030610031a06070c090f05060307080319081e09031801080c1806071a0a0b10080109151a03270a030c24050103031107051c0201020a080c0304 68
    0x11028040319410310109881f1601c981c83c04603154052041c05100000204a80f000c10050300b8212480a40a04422100b442c4240120f040016a001020086500f031780c448042c144500c6840c803905461048000d840018004030f03000000a81c184c119440c240a881e60200541e200c54809824040740c103901e000c101e040004110510541341419825a02940c1e21a002ca01034500d0b8040450b2860040e2400540805255085500005c0418254a0091009007410306c0f1902002c0c09114400000e80306c244002030001c001040360707110a030b003c079611501344a00004041c0d50341d0740509054122010b104030008000003403003032090001c60848583c21514105d00740c051072030503001d5185c000302d0724041d0500800009034010400300e1020903840d694460b166250009040c00e24034010142404101c0110320400340c0300c1100000025100101d07600180300302d00009038503240600140114500b241548100700d60300d0300013480000508040b9940740300654940703240c22281c460040e5100c40d8236004 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 837990890 1250 837989640 837989651
    0x10e0703020a03080705010e03030112030905330d09030203310b220306020c010f050c0a03090807120f0f090b09040b01020708060c04060e150306090702030d060b03061003 75
    0x60300c42c008404100c940100d941c540312030443c148240904105d03106511079010000011030040c01491003410301500036541d0308000b503142c500b40594408040c80c3d0b85070020700c10754149200d4030503010b2498442c00410490b0b081090106c0300800380c440c101d0040b030248c0c00114a00801e0703049a03404c442c0034844000031164140803a0500c0c0d00e14840390203001101240050031020b500e80c4025401d181803a40450030704e5859990404800039002802c00310015404c2039a01c1c0c440070490300a16003d2010458514036044400c1c1e0700342c00a10a040081f100404184035900102d6407241600300c0400d00c81c1c42d0b6082070042031100619070400d026008040c048480418080900500c0594540c00e00c196400541100c1d04401170b8a00802a03004442c98400c910401101a520030301400407244942c40d4140ea1054032401c000395550004842c4e22007030028800a00c143c030708100401e1300a5400d0056a1602890054071415a0b17920f0300444000c10b4000306109140c1070070f4444006214640c5410441d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 837992140 1250 837990890 837990893
    0x40e1207080a030605060a0801060201290d0201200d111504020f010c141606050903060a0b0d050a0b190227040e0723060c0a080d020d020c010e010e0703 67
    0x4902440314041d04000001c240b044445000fa48581c0240400801481d1180d95101e40180a54400d0041a00550030807600302d40250005110540c44070f018103841075001c14807407d01205c46c00d004070a038100034550380c080d40c007444101c0101c0c40000445018000c41001c00001910044141c804841c1a80c400000740041610564000760055811140344034503800013001210103a1107000007800340e800580c030744100c3c0500015182c010024004c1052a165650607055405016000703140703800d0741041002440140d041d0b44001130400780101400c1e01c0c0e24240c0c80c4c2a1038400c0240301241d0758400207050280070000001c0b41403440d01c00040561614002c10007441e0104180e420000900310034110141c803a9840c2e410130b11050b400242250042c59881003032034147e01c521002c290082410304071030340341410309100301d03103000080c50000e02054600c0d41d1540d040c0e6204047c18140c440c2d003403200c01400e040c03d000078030040c0200b40000c0b030340f004801103090840d103083c07a810f481607012020410 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 837993390 1250 837992140 837992173
    0x60f0609050108101406040b0a0e0307120b0f06030f07091509050103080a0f1b0b06120106030503160303110f03040201031a01120e0703020904050d0305070503070c0f1106030a0b040e 80
    0x207031101401c011401d203517081c0104409001c0d94000720203101d030118043e1012548181450384028046040721340701540c84c0b0032480342d860f1982c3c01400c1011480d0000b4804030b91032000c01d4102070f0160441e1441e05808a40d2307070405043e0f03040010015200e0741184c5036203615903c108041d16440b04100055450b641c0c40c00c003644141c840703903000e2100a8144d0300c80d050080704003d000058072240d043c5040494036218044410841d00580f00751404840400810740510903041a20750000042d4070701345108064488511040800b00c04054507000c0701500d034640030f4041c00c2c41d16448000140c807400c1c82c0c40050143c8101c044c200e40c00440d4040c1c00c4506070380c41a003038424802020300016a42d245840180d050000c10b40002c0e41007410b10007403008128001540d40c000e5080c6640400c01c580f56003c0c12161480b06442600004440c19000004130b040107004d0010580f04001d100091070315000401d070702e038004440342144142e076840f90351198103060151404000498028040f002b83e81c2c041c0c1d8 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 837994640 1250 837993390 837993421
    0x705070902040506180315181506030601030201360e060d1707020d14060f0a020c0a080a0512090714041103180304030b04050c13140f0702010f060f0609050108 70
    0xc030b40901e49400420906d4406201d000b03010258007981b4829481e101e29410280c03440704000020700d2041100040b001d0800c0d5860601031007008014000c80d91075900110f803030700142200c0410082170a03038510048005c00030071340c0c0d07001c0c2200841842c0a103406c08114282000610440c001c000030981d0200081c032000203984250002c404c1943c0b2200e850020900085101c0d40003440e0b0000d1100f1003801c0200001c12900c0b41d9484091107100d903640074000700a81c00350341940c10450b40110302e00740009001c040074000354945460120b0600c13a8150b146801500309403601c0c0d03075941002000380262494894805000c2c00161000e0000190306201d4448520004040c2010440a0980c20b2130f805000e00884c1c0085421140d155020304060402d161141210984d59100b45a9010070400c209003d0040307166403104400040d85503910301c10310302c5820f100180361104655031500d003070800f94060b1084001508004015440b42c5013407100161403039500d5001a07050054a030200201300c2c44d0440b00 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 837995890 1250 837994640 837994657
    0xc011b020112021309060f140613090b1305180f121b0c030607030b010e0d080a0f1b0c03120306080318041b03050f0a1e05041e03050705070902040506 66
    0x5031356990311a0019145400ba8201c010308070f0500500086016a00090b481520036503c0300e1280f5040f0b00781000501d10a0740e40026803490440c40800040d0b000c1e500403996218054070b484140c00705491281d04072202110f0907950321160440100c00c8240c10081030141030a0030f00103048044108815582d2406045019101a052081d480800420a200d200b8012402404a03100c50600980c0a0f02904218002d140081c2c1240c3c003014961800c00725800c01690030001061411104c10b40c00c9844000c900145820700155807001d025080411300b801e4400c500a0503444070203410361400c000c4805075070944004040c20300c0d100b8812030305c0c003200311034031001c0307860440380c208181c80c000c50060b098900e00c103000129032003001d01c6102c3c0c054210328801c85001d6007a880d10764600540000f25000301d001000350300850055a0040000355003e15000381c040c2e04500c440d030320400000d030030800c0d803504200e00068010481c0d0003041701c02c002d548080e1100c01029400d1500f8500440c0023070294114 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 837997140 1250 837995890 837995927
    0x80c0315060d0b092b0801030b0403031d010f150f050909150a0c03150305060705070c030b07030c0f0c0b2d15033013080a050c011b0201 60
    0x40361166680b0304801c0001079012150324010714003c007072243c076008041d02c185140c1c03600d0311a902c0d081170b0400044544803060307211102d80341d007117846110200070010400c4041c195500764816954550300c684100c0c1000e20070011698080001c405425144464261403420740c8080c0180a1240c2c1850004151002030350030709050356400411510701084010521118030343c80c4281300882045800290008280d80c90601036489080d580b00510342283c0f1010b846508801c02080f1150310880040c25420301600554241d07d8407a120307801100700c107988100200b503580b1000d159142e000021800c01d001682455000700101d80c49a5230324850041c01d10401404400000c2c1c000c80e06074101404420b445503018005240203811032034044d81150303117148248515162441041d0483c112304010811054104050300c64509001c800381d080001054015500d151010600c800e0800c600f4060b0f500a0780102440d030119800541348842e080022041032100440140c050f0b40c2042130910b0075141d500 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 837998390 1250 837997140 837997183
    0x30b06030c130507230412051501091406060310140609060c10060f120b0402060c1906050c040b04120302030c0a03030b100903030c0b1f230609011205060d0f051006080c03 75
    0x38041382420304d0200404c04069207040042404040b33a8404034000c0104843c030f65041e207504041080350f000071100c80e0000340c00c524060001c03a60312110380c45840000b40032181807048050026181d03400084203005075a0012403080c41558180c010712008068500c865804a4103142c003510280508035405440020aa03004c0b404644600007219101c807c000155a030200d846105860f2040756504d0a640550900340402c00c203044450880b0110384401003441d180510b0b18005010845400c1c0c0d040c0c0945c00140607540c1800c0090003110b281920a1f5000100c45020b401084014035400c4010001c0000d8228203000207600524113001d09038014103010243d681e00030700310901c20401200c00c004141002c10000d801e884551307041c040303c031a144000c4215000e10040c01054061141540c0c0010318543c4850007200c6507a004541014001d4101107195281d510b407030840c10020481110740f03a02c40e403090200840d00b0700c1070741c018281c100003034200420074600007540d44104085a449400158 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 837999640 1250 837998390 837998393
    0x1e0c120507030909020403050303040203010c0806030a0f050109052b08040c1404060b0c10061406070b070912080a1106010f090209042909010f0f030b06030c130507230412 75
    0x248256802404c10030f905542d85c43d203928200386c5a03041075074120300135070801c1001d080c00d40c01030f0065481498090014110260300351541d4480440d00c00098804c3d5603100d035402c012680900145500e07810f811036075503140401007441190b55280c511030038200f00806080c0400582c2c414800300c11981010810301c07046020b4000603004203070540c040711200500244112240b80007090a81c08159503641c10004a070792141c1c0802958140100c180e40303c00704104480001d50b21001c0283c003d491480c04021190b11a5480315906e04200c02c00c5e9803402c2e002c188410207503442116140080984030141c1059450241c05a2544515000e5500f0281e0085041200c94850354005c08620b01801d1807004104003040c140f1812103020744160340154001800424000d030f01c2c171340220445183c40e042410003032943c1c0b0b03030130512103019042d0f0f0f0741402907428800340c694503080144005c401518001619040006c5c0c003034032200821040082c180c803040d441d600400704c14010f503030440d9007003010640c1c1c64210303 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 838000890 1250 837999640 837999647
    0x80c0f0d0e0c130b19053615090114131e06090f050c0301152006090601210203030403021c1e050c01080f151504061e0c12050703 57
    0xd101d01e58010044034031000c02d01903144c02101d1020303410b460000000701424040b804030b50075070145e80e8000c0c800c06402c40c5060b0f00315455008500046011500c41e0b501960110b00d10710003941e0582e071621003134101d01c60070310708000c1c0c0a00409008010107501c180c0d000c0401c0c00002c2c2c40e10004510b45e51421440c1d400d200f81070b0341180c60741210808206840d12841868000c2c0290403003903a070f90313180c42d000034000c12110088034181c5003062081d10351082e895104494422000c4010301601c44609a0040581d00c00c0100b80d000d011031034081c4c00c070740d0304001002c0c0700020004510f41b081030700b2045900150301d000c400c56040e40c0e015245c1c40c080281c102d070009000003202000400a241e80141800d03c8942c0c2e64071030b900544540181e840c0e240780d04004456640003a9a1103a0b0f240140c00400d00c0c42120303100403214060081c01d031002c42e040c807c4044000790031a600440200c2d541c04c201c032401c41c243d000d000400d00c403a8181480740f80c9081d1203611030444201182c005004c800244002410300 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 838002140 1250 838000890 838000903
    0xc0201090b04061e0201090b15030a08040e04060c020c01050909220302030a0906050301061403040203010e100617030f0417030903030403240515011d100906080c0f0d0e 74
    0x40c200d581d55640e81d0320801040b0301060282d040d00141d00e10030040c2c0c094418041c03507100c80d4200388d040c0495162440100814401c0e1341609616100314040c4c500026241805000104181201076001c6c1c40d041c20403205490341c05d41c3c0b00c0c04542001e100610181c1c0c100e420b4401041055410942c00e540391303214104800c2541c90b4012210300b11800384010103078000002d1540d00f60994921300150f0307803900d0a4602380028001c44012460100e90084a583d60401840d03000e80024004140e51203a4028a820120301c5c003d0800340c10b84507102804032407940c0c4900c041c1c107500700000758501501d00c003c540300d81c0268000d40200314000d100c1c05ca44400200141d802109000b42960b40c3c560381c1e031801040014100c0302c000004010b6000c00c4821940038800c140c450a00d0050000c000c103524001114104003025898030f08045c03c420052650302c3c1c55821511170403490310b640403210f0510748085d081d0240108034001c003240410900c40924910790a68409091091011034480500301d400c50500341e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 838003390 1250 838002140 838002149
    0xd09020d021f02070b1206010f030f09031d010206040203060f1b120106030b01020a051b030304030c0e0411030f07060f051c0b0406050402040506070f021801081c0509030d0c020109 79
    0x12490314061039241422140c265842d220380e001c41d12415030703c0f119010701d40211003a20f401d03501404001042035000703414200300241c491500048440d4007240510444444200960000343e00740c002e120004a0b010204d24040401d00040c070301d030f241ca640001e540301c1e4010129102918141c001c15a034078080210010f040d0711250103e030315404598040003007410300b4403582002a080c40e02c50000c95001080d800c513000d81090180510580040205c000e40e40701e03007a5103070144000c00c0000042035076100303020090500303018600d61034141030a000d80c00d80200d401c0070f4400e0704a01440351000d00005100001c44906041412115505038410344990003140d09440280c0d40745403580c0200e5000c0d40c828801024100c50402c00e20340c41343d0a2000301e0050740585600200200315500101380d0519075902c006200600050340314000c0c003995030700c0e044d0030380c0a40e009501c00028a42d450b07000443e5010001c6642c500a03081814101c002a500c40340d8036000e5060000010032907040d07910038080300010b003 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 838004640 1250 838003390 838003399
    0x604141e0a0603050a0516020d211802040f020a0819021e0324180903070204090c0e0a02070f060b1206090d0206010e01030b07050d0f06030f03031b02030d09020d02 72
    0x200c0e542d900c0980070b01021290b460031a40b4240010f110340528098605116031164000c18402042d000305840030030528450080d08184112040d11016090043c03d199219440c41b0a045502c0b500c10b02054440c00b40050b46045c1c014800482c010b81c2c441c1000d42c2c04100c0079039400c002c4012540c084001d101d608260306104201c8404824183d0500c0011409505001c210109500c42c2e4860b2100f081210302e19581e00c8580400728264881ca4000b413030b40c0000f0484252464801e1030350002e01194a035040881c2c0c0d00456840c00c210800310762850035404001480203501c2c3c5001da0350760020042ca5044000e0050b5918441d4030001d03241e420145220a036581c0803107001d41440b451069071845070070b02a400602c100c0c0000300d101c1c0e46a883d264100da9014584c2c0c2444c0d1101c101c10f4440b60040d458400d2241e99807400c81e0485c00c0c4501503a401903003c1c00385286440324030305008003a40c043d0b61905692000f20034404068a5000045800c0c070807501200059075010b0744001810040b0040019510 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 838005890 1250 838004640 838004659
    0x30a0f050f040b3a090c0e010e0403020f0a03090603050403031541150c0102130e0c0c06060108070509030102040e0a2403080310031a0103110604141e 66
    0x48554803000f085101c01e080080c0d24040e043d080c080140d00910f0440c130107002c0d5481c10881010109030048515140b040d044c10401c551241e0380110940003d900007030a08400d03030140003c0c541c0501500e6454540c04000e07003503840e860b40307002c0d00d0b40703041c0d10400d0105946d56002409051184d0b12004038181c202d0300080740070f556011134020b982e4141540800a804007141520560526500065402c038032070001d1195040300d9003080440310706108400914001000765100d0b070202071000b0701c4821021981070304c0c3e2500700305041c450200d0003840080303002c600700843d6524070070004040e98003041c01d103401002e95a41e804201c2d03035401030300034070b91700b40d03002180100c0c24001c2884c6480c4141e480c1102085246000000c100304c582915041201000d500c41c0c050000c244079400460388480b00042c043c2d041a0f076640e5000048441e40340d01484040e40100500130072803850441d281206045414a0805040c034a60215611404686a118000c1c12601180c0b0140780c0c00384c3c0400120040107a50b0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 838007140 1250 838005890 838005899
    0x1d0402210f0c0a080c0d02211c090e04031709070f0605071e21020a02060403050d09150207050f030f010c050a12020a090909300207090608030a0f050f04 67
    0x50340c1620800307082c450126103034040748070400042c150100c6040104104494030047d000d00801c01c0d10b06441440d94100c50761140c030710761001c102c6a0f8032100d0a62666440c082c0e0b441008280450703d401c0b005400e0701243c2401b020a5208940741d4449001c24240c0700d103034584081c824581a100d82c00480d0b17030711000000060040e0410050305180c0c0c0290100b00440b0031142041018008a0b080101707031144031038a031110611505203083d00c88400d4011903580c0c001d1600001c0080e0072641c4100c909501c506200d030195a40400903038014100e03001c0c2000c59548144000c0d44070302060240602407000d00c8580c80441d9001c028444440c0104802080400714000000f0483d41c00003403020003040b900d061124058549100f10f4413425000e0b6aa90041400c02485001508101406440004082c0240e0a01c07952200052840c00c1ca45040707580540c5c1c030054040e0034902c003a440342d504c2500d09201000740e144040200c1d83c00704000e00e03000703607201d5503d082640c55004016900b504420040b0f00440c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 838008390 1250 838007140 838007143
    0x80a05160c0602010e06060d0c060c1115090f01020616030b030c060301030b01062606040b060d0606050408160509040803044d01090b0d062c011d0402210f 68
    0x511314070301c02c5c03d0765800da5460741800b42d00300041c88001e205d08901201041058072a1801030041481016542280c81030103000500152125034441c1e02c6942c0040d601e981d6143c40142c101d904102800980207a141140e1382c940c848000d1030011046c5a141c880d581000d075010300004403e001d00400c0c0c80e031656164281b00700450000d00481010514000000c142e412a003041c4503980c2c01036804588941d900c410502c0090091200c0c015002541401013200c204c805001b040040c00f5250340c1c3e551a0f61070582c400745010114450000c10303901150090000e03803150745159510a40000e841541c0303885924003140114000342600b00030612801340400ca50b0115041c69401c2410140070f400320072000110021200360958145010409451041001c9442540036142a000c100710014500e80c0c1c071464190f00c1040c07095858040d0700d04025000140280301c1100d8054550b00041402d009042c0154140700400a40040c0c071601d5501c44031608000c0d0900f64100c00256401501c00480800312004d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 838009640 1250 838008390 838008401
    0x606070b0a02030f0603120316210b100e030601030b06030a022809050c1903020d0207060f060e06061b07150c03020706020303102303070e0a140103080a05160c060201 73
    0x55001c131a0200200b8903d01d40050000b4001582c840007624640740c042103030440c4003a4145240600181d9011071800c055042020b4030071084600c0045828a00b200421002d0300c1000e041805025000400e4241e54a00080c1581901c0e40110340c0001a15000d00003480c2904a4000a41c4500403d20305000010304a0b4a004401001415a040c458517404c0b2881501c41c105d0301403a809400f40802c2134690012400080d5183c41c0741001440c25500d40003210a13a400610103a801c0340d00c408005109004522a08008068241c4258200d003461400101c1034451a90850110344c031030a0280d80d07014003803015000518420802200900c00e40d98050b10001640d541540036000c0d4000c00228140040222807055800022500788141000503916100071042c10802c11030310445254011074030b04200c04809401c200d41e0803000c1e450840858000d60750f8007245404411144001000018a880141c0d44032012070704003d51501d441d5002c9070314440c0451005040b291220710b0010b80141c041d1b101 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 838010890 1250 838009640 838009651
    0x7080705070e071d0d0c030803010b0a0e030c010912080c0304030609150615050c0f03040e01051507020907030218301902010309051006080319260606070b0a0203 71
    0x600c151940c4002065400040013440250504401c0d501c1204a180c040da04002c140e100e000001503854407611001d000745c2098205180c840350016a440762250007104000520204034010300481c0c00d4100000c0c0001207034420f420044801d075049008201000f81540c44030003070355080740d864030f960b4104070026215041d01a20459840260013160b546103000f1001954680c007015041650342c0e0608860b668000040452580102d2005101d428800d10052008044002d502d01c1c0360750600d000c0101604e004c900c0041d040078200144001a2a45050a40d004503075003001a00c80b00101244800795140406071076020804034841b43c14420340191480310f0522841c484e20a2600000b030b40d80e9100c0d495041300b0b819a03200409180150f2080d00f00d4108207105400307840c0c8603810195410140c0d00380380c1289099070004100b4010861a0300b4103c3c03010f180920b860707929407505e800a02c004e2800755007070002c6403580c480000d8041d1980012200800d51009042d02c4600d0031501c0e0b40f0007074005881 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 838012140 1250 838010890 838010909
    0xc06050f3105090411090c0927060108090c091e040f11030703030507140312090604020310060501271a1c050403020316170406080a050c130b070204020708070507 71
    0x1d02140c0c60a0540b4035611a503804520749543c40d0b034500c200541910010491003081c00200602c0c4e102da26000c00074240c100c0c0d281c4120100c03148001d9252083c00340100041d0401c1801020468031600004041c1c0740600c042d00c016209444502c2422040388107880c2e0034080b0f45594081c8420440000d0301c1203002401400c0b4071002c00503040802d13403a20401e120182c0021410302c080c030301156007401c001002d24112021245049a00e1440c0700100c0c508554420f125040201007006508091094100da0722130300804010240c1408001b03010710420b00700201c52410200119a00c050762412008050a0f00c02507042c55203030804001e619580c040f4941c08003040c00c603011601c007540c05025042c02160301d038018505021800580c017a034100002401d5904140995540715200c400e40300400c01340c4919928070703415142c010a284160303840030f0984d01151a003080411800d100b11902c1e24140c4903c210404d64034030050000a029000d121005000d903940000d0500800c200040d89204071204100f = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 838013390 1250 838012140 838012237
    0x1020709020c1b100f030f140709060807080f070e041401090204031a0c1b014706031b12010b07050d0f140d14181501030c06050f 57
    0x109120313040800309512408264540d24000002c0d0003900100c14000d0720302000640c00c4000e40208241c404160348540100d01d8142d0300380400c580c4001550381c0322150781002c2c0305ea81070200007188600343c01130402d82000490000b0386148d580341e400000003c0701100007034000396140d244420080d48144000c45011b140110580310480392a1001440740a482c6007107414520355000c5488070240c1328001c600e45560b41c4008030380030926085c42e5140300300250445840e200c4030483c041070f5503045100c801a14074804c1203140044c3e0710202201e50110b02c01d040c0055140400c0c01480a500851101c80d403d4040c003400401c603400340c0c3c005002c0b0940640c0803182880c40c00d000566902c0401e142080004001d986912640301500d0300802d6030164624001030540304502250314003510030b40d030078a42c04400310b10360040c0e4042000442c040070b24000c4c500d601940740d9556503038015914400c10303040c0403000c12104824000c0c001034501551224808400b4280c00308941e021b00180318118400c2d06000c1c1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 838014640 1250 838013390 838013443
    0x7050a0c1e03080f0f07120e041a03072309160801150504051e0d06090c0801020c19061107050a05160503031606061d041e15090201020709020c 63
    0x1c0c03000d40200ca400240b01840c0002d9151440240c2e80000d102041c07115007003000310002030440002603414403a0782d5810100805105c00c000c113903410070408060761000095242d80740e46e804607503081110700e260b03180101c00c074505804941d01d18944910329800b007002c0d000c000207000001501d448003402e42d030b42c0d07030016a02c40c44200303c5c1d0428068680300181c0144400d10060030700c5284400a191100d480b042c8000510700090505822008112180c41e141d8408504001503070b0b01103000b90500348001d508080752004400c0d550100714500c84492140400d105040c0000c1c0d5112112040500e43e0341540c62046051a80d40ca21441108490b28403400c0f01039001103560122407419182c0c020080e6152007a00f0204044100020b6401e6498a070b4607040060380c0310400000e180c3e0881c5107245400d40d40380ca41030454808400412f281e00030b4a04280703841c0000c402031720301c0441c0118004005007050203400100d2510140b500300c0c0070310070700c0007820008170400050042c104200c6a03603052400ea060 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 838015890 1250 838014640 838014689
    0x2509090605060f0105040608070c030c0b090a0311060601050a030906060b0f0307021510050105030403090503011d1204050901121505070e04150506041403191a1005030705040e0307050a0c 82
    0x3c42c807d00000039062004112528450f4810b8000180a4681103400900603299040c0300741c0b007502c410156910034541c8004040e0041c208286051441016121524140c0006066071103100d0101082603510243c200801c83c01d5032220010304000c401d059144d100c07003400422103500540310130f005481820120480560b9011035544102da200c4200c011103440e00c0019105030b0400780003103080c80120200030030103450900c607004814600c081da001c540700103000101d08011528000c40d2005904020901940d01e5100480741110101680740d01d10090714201520001c0d400501e59260320300385010f00100c180e0100700310811007400c560402c00c402a0780c0001036615490320031184c1041040c0000c00c2801c125020320440080d007c1d055640f0b0b2541007034080c100495030481110f00c5055010200e03500c11203171207803d0f4800e07180070868160038141000240d40d2001e611800d482161500c0c81200f17076400c180191155640e2001c11607641c00e0f22071401d40c50b0a40207005160584c0089110130031603a01 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 838017140 1250 838015890 838015897
    0x18020901050d0c121b0f03020405033003040809101d10020f070906140109120f030c1505041502070816080c030706020d05060d052509090605060f0105 66
    0x50503124285801d04000c51000542a00202c440500036204c0008481660901400c81108514004100c502c41c403d940500000400601c6c041010320500050003d51400101e40c0c068031107030b4550f0a803601c00048080522800c815140c504240040284000c0042d8100134100c400c40c00c944441035440070403012203020059003114504150315810200403800c12a2900d21031f90740a1054400702c07580380c100b840c9091011390219000313560b00e000c2089030028030300e800c0c0224927003482d1407891646420000062200d02400c00f07441003904111500801d80a03007008165140d000b04003203103101e41c1002c80f50003032008035000c1c0c0d05c100b0007020081c2601450720031645590b40c000903e50610350700040a1100096160301200c1c1148100141130902c2c0c4100007910003540710b0280980d0b00e1910003014800d0300d0014101c240140c81c902140d200241c404507000300024850395131400501c043c0c08070341c04007666907408400114600101d101c01d020241e0812441640e054a502d00c00a0082004480b680b0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 838018390 1250 838017140 838017157
    0xc0b1f080c03150c070222020406050c06060d02180720100609021e0304020d0f12141c0c09030c060c05070f0e01231f080f07050a0c021311041802 64
    0x5130104142e0006140000d9104044e080421120301d4220740907004204030b90007071304900007081e004500312a5030305082020503070212090340c6036441c1000175404900d10320f02e075400e040700e800707403103c00905d0f45441511080c0c015155603441c200c1c41480d40260319140d156000803000341e0343c1810303000300e082e0007503008480307000406040e000c20498120030b8204482d04061700c120781c040354100a41002c950300c0323103070b400110380140b00c845403004100d1006018440c041020001981091091180702003481004020300044440046031400c0703100002c403904101174100901c907039100e1401090441e4080c5040c920580f040342100c0c07a254440d91128070796038040c80782d10408240e00c40140810143c5031a4182e65546d800451060305807500001015031189640108822058140780414590b121007079507045808020341c0103c90400c103400034a284100610b410911106412031811515410140f1201d014040e4081200d02c0f11011030403041d82c001e11941c0c6004400c1d040010601d181d074800c655506 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 838019640 1250 838018390 838018411
    0x80c0d053c0f040b0d05060a140d0f030201090f12030f05040c06030e030f040e060103060e040309210512040e0702030a0206150d08070b0103030216060c0b1f080c0315 73
    0x789030000684056200401440c21180d00380400116440d810b07020784101101c511010509240000c01d021841d1000d034440c80040e82c090704a141d064803443d0000c50203940020f07010b20076100f0350030140c1c090704018030000c0281caa400f01b00c0080c80b5900c04100c031072201564040c0702a040c0303454420241d448c10b4402400940d0300440400013030b8003075800f4034a181c00d82e4054034204000028529515001588568804c51921342084015039041c45000090000e0700500f43c40c90402c0d440003030218a0ba4080c060640304403040c00e6040c124040c1000300f20503400011540c02200f25148603e0315041445928854145140403a40c8140080140c448540050740100003c1e070724a610101003440a5083c1c6400c03040c04213070032020035550350041403401c5c012090103465500d10b01d03009182614410924401454509042c010103500a5102d00d00c140c01a000c1030058654a0341842400d143c00d82e80a511107920074006466180440e9400340c80004401703072036010300c003041016541e1404a0701d44551 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 838020890 1250 838019640 838019737
    0x110a080403030e070506030c1815120a1e0b010504090f09050d0c02010c06050a0f0c110c09132405071107050105130e07110f07032901050d080c0d05 65
    0x40c08080c8c4c0252441c0c6130000c0d61540c0915131030300810507200341f40c0b85c055a0b1120010788070030b0754011007514035005261203000304000c608803034210a08800301400c04403815280d078070100d19607101d00e050b180540b80c0340c039040028907074140200008080480742200e1f40d0044000002d48a80101c40c03100c5030365010b0311603c06144d11560788034002c060007030200d1450b40c2c2ea12001034904080e44142c8034150110b854072544c507201109c149144c001c000e5102c52241582ca000c001c01c0c1e0081401c282d2003103a00070852007250341141004603100e2102c0142440030780c502401c01030700703503404040310342028181e0040c0c44400741c07140d00444040c4280700c000702d40b030f10340280201300d10081c0c91030140d40010640ba0003c01c119090090701d0400ca45e801003050654041c06044c0140b240c44c2d1030a40f10001c890091070014080066808201801441200e104900c9411a281401241000c036000358449200b51142c00903140b40140050f0001e0001d0401981508200c1030354182c0d8668034036507181c1d4031030003040 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 838022140 1250 838020890 838020901
    0x2060711041521020d1209030c0308120906010f061206090f140133121d01060602030915031009050c0a110a0512030a020403080d060501020d0c1212110a080403030e07050603 76
    0xc1406c0107000304003000070070a030000200d0220995080514840d004441c4d995401e01c00402d0007042c007411075101504140010070078205441094400c840c0719051440711408001e250b00010451540031031441820201200501c02d0310b507010180003440050501007990300c031a00c0d040031552001d08501c2c50700c000e919610105941d0a100c48005009183c400304a020900c0c03e6400e0f03841c001c001340d4443d400d90004102105080c0a4800a44240d10081d410308210b02c0008655941480a8984000c40000801d1082180101c10400b03802044803c0c0202d0520503a850011391101a007180001c41d0703d140341d400c800c004680710708400c0e0400001d14181c44d298482180390392000d46600d08180d801c010000000300084c000d4048a41e00107000208070b4a0103001a0070700015180550400020355010030005006040741c094075052494455000b0642041050081440c1911724103400004500b02c01c0640d800080079226a100340d03400c0c000107824a000d9031343ca041c94000c042c0c0c0040c1c01c1c0005503 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 838023390 1250 838022140 838022153
    0xa06051c0f0b100e090c270103110a020303220f02210f011508030a091404090204020d0f0f0516080c07120906080f060d02060711041521020d 62
    0xc00011050200040b510a16030000b09100e042e012242e000c941921804075481c0780c00c40c10107034890404070b00d40e0314081c03c1c10696a1442c2c00590b02d80000030440d69407140c02d03442540700c0032150202a800e113035551082140a981d0350411910310040790b54044001c0429035600c0c0031142c56607885a2040c0d1100050342c204100801c1c03969035045141c500580002c00241c08100d07130035103a40558000211001c20028200d05120284c0003410154170400541d110268000000d100b203811080300c80f11101000e200240141c0140c02e00a03605c68000300d118140b40c0703e5a84800100841440d0804c4480c1d4180301040c25560200c506c0610508072654101c00744c3c0c007419001d5400300709100c215241032120b0b5902c81e8030100744001100007900d40c90090180031f4200e046290000354801e88820149050300018001d00d90410f40203026040224400703081245543c0b0a01095000910900c6065941183c0c0c8405c018a0712800a0399207081e14034070302541c110304412050355005842c440c5090300700d44501 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 838024640 1250 838023390 838023401
    0x20f040509010f060b070303140702030915090612160f0206150a380921010207061a1813141501031a0f0f0403080c12090a020a06051c 59
    0x41d045540314039030700118100a118480180c0901820f8546401d05801d0040450300300203481e4005040303003c00d20001d250004240c41c02913900f2290842941100c4144030381a0240642650f00000b0100318400340340c9416100602c164a11580a01c0482c880f180c21140609111400780150b0000c5c004200401e1441b05c0c41c005400c0b024260b440c20a60350b249000700b00504141c98045e8860398807007203010304900145610303030000c03c028490034000c4a00001e0780320003401000c05010703403050000107074481080d0141c41d000c9070030a80401c542c0b0a440c001d0501c040d00d0b40829403280c8801d0341c0602d2840d0380207040f180030300c09640d0307150101c03031040d84c0300000079010017881e44241c454002407580ca14000c0365940c4c0658404c025508007840c01b0b01c00b1039405200a072010800a4034101003007940340441015079489605440d2021150311011080403643c81a160100000148a401c100441100289007145d09100b0f40e100d454032a66984100c400d4040c12280300d42d2141c445502030707000d583e1034001 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 838025890 1250 838024640 838024651
    0x2d010612200d0b12030901050a1704060507020f150604050403050f0d0915050c03150a050301060f0f06023f03010e1008010203060d1509020a030c0f060507020f0405 72
    0x980c1100740360302495026058611a064218001403404942c0d00902645190003815205a0380e60401c1c40d50303117030316030040e0f03001e080c1000000318200300200d00c038100714020018680210505402d16007012130281504a807a030000d4490116002c004040c0010000c00c00802c0020341121610f40c201000040d250141040c0c04000080c4041440d91200d803004020800f2036680010f41c41c5410f16000783c01e0613000000c2c1090034501810840d1128104040f41d60190f0f05c0910150a40d00d000300054500032a0340280f5015864000042004843e01d14880141c1e201c183c500c2c00c40721380c0c591040344d46200c2804080001284030300302c150703c1e0800d40002003a24101c026480c0c24003070a02480b2419402c03d170f1114041100e140184414400341d818508083c006080085d0714500e084008a102d102c070380007009251181036a50b504412034103902417002c140e402040104076a90f0b900741a10740407201d008891012504000001d60180960100d0703c0650b4003820403100c1d202071004000c0105001040c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 838027140 1250 838025890 838025927
    0xc0206070803090607090b28110d0306050108090303060d0201121112070f090e13020f0d08030906100e0c07110409120318080405060a0c050f01052d0106 67
    0x60006161400690703c00c618001c0280031600e44140f004088402580c04548801d404000c1c4c2c1800c2240210300360080aa921104d490b990b00c00d080c102c400343d0501c1c81e140c2807401004400f000259154101c2c100701d4800342d072510700688880180d035889200544802d03504c100680c14000055000d02100380807081c491030000f0703081d0000ba414070b2007580049682c00504490380108003205400101000d03c00c1142e00d0828061400d11003a6140c05101814102e420360f200c1480800315500c001d82443c1c181006002604012403e192089290300103407400748481c003a80d40001c010702410f83d1003000315410368501c98603e8a400c00c168456511a1500f40d41410791100303000503a03200c034060080f40d42e105800c10202c00720002c1d4001d00711050640701940807020541c50f40d01060125003500e0982e502110300f6952071086050946111013080001490741c040c0404044c6101c1c0103500c558450a001c4490807505094582083e2103901c4590340924005424001401401d100b803074200d070302e08400ba2 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 838028390 1250 838027140 838027147
    0x190e03032e060306061b050607080a151404061a07020402030618090c040e01060e0a0e01150f08010b0603060102030a0309170c0f0d020106050a0306091e050a0218070f0c0206 76
    0x10a160070700740d054000c0004203480341000c03c80141e00134070000c0e070b44c1c950801d145000301e0345955490b203c03400603103903401308040307000426074000d0305030300c80441c0180c8591030112940c0d4902c00030140a2003540f170103106d80c0c076000000444408800c4107131008080c03003c04902d4040e1913400c12000b0740001c0c04e0301e03400c820118110240d8103401040b0500881401c030040c506079401c981000152440182c0f0406903905114042100c03440e40045150010316400004c94404610003046004000d5440160200c00565600103840f10010120b10182d0310010028050b4010005c04d0200ba40300a076800c80c0141e004002860300123200b503120702c4d402c0c0c0c0710b00f00b6001c0d0b2289003404002c560700b08200300d078419080400500390038501000340000d2130301d10380001e010b141e1030700c0c000800441940c0b20181c0782585070b46030300c0d0400491110a082e8a10a520340c8020403200d030174107955622114804a002e031250b1400d251140c3c28040d80244a0103a954030300d05201e9a034442143d0180703804030f04982190003070 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 838029640 1250 838028390 838028461
    0x9030e040501090516021c1211160c050307030b0a0e160603020a08010e060a15020c03030a030603020f150906070c0302122401030b0103110f0a0e190e0303 68
    0x1070048034000e1005120118031800c040c100310310001040d000f14010365000f9003115240f91185980300b080903003281405c988007029040308101410301c0c1100381c00c40c00000614070303048401e90303081c003d40702c0c0c016924131080301d032500141a59400c00380406400c803012071002884003243c6402454114034000c06880100558030341005a2514640209004c203401103600008298452000d40c01425140001110b50070a8008142d00015900800252078511121410414000c200c14149030b507024040f2940c80b030300d00790010010100c0c1e02080f441010840b80605c0c0c20720704203502c1d45001003411100c0d40303040e034807408100003640305010403140f441305000000003581c1c07441105010450718101404c801c0030302d6609082a401b83e0560070820794507910050010030701050171141500e41c0309070200c601141b1100003410382600c060303039294030004034800031540403902c152460140304843e0074004e07001d41e60701c008003d0f90078002e01202164000d10000d80e40d1840c90300900e41d81c0c40d8460b201003040310344 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 838030890 1250 838029640 838029649
    0x31e07031406100b070302010b03011b1202091003020f12040b040b15010801140d02041d01050c0c0a02010f111f060510020a021c0c0e070801090506060d0b01020309061b070b070b010909030e 83
    0x4d0b40581d500a20300e00703441c0c001141c0c200e82c01180de0040071508500c5c1094100c0083c000401c06ca1020b4209540404c4208800e480c484c00c0780d0401b03403c00885402d42c42c2520b411419160103e030201c401b82101004142030007000050110202016158508140e081c800080d819a1240507070551001000402c4030240e00d039403142289410b22508425221105814921300751000a48100001c3e01c0401804034010004280b003c0c2441c0d0900e8001129a10038108680604426007035409501444041e00b801c1e49600ba0415101c004443c028001581d440e010005040c03481c40041c405a0000f401030340041c9048803440d003a60380c9605e80e00d518007946072603000900c0c0320313a0010b03400640d205027823124094029003185c1c01025a0201400f5900e0540042241e600403045841851603c40c2082c0507584c0c001d0041d511400405001c0f1501d91810f80c0001000c642e100010182d280159000424501100802c441c0c0c0240c10094600b99a440c1c045054010511141c00b90104104120b8002c00c2d07994 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 838032140 1250 838030890 838030901
    0x1c02010f02040803070515010506040e060d0b01061215060e040f02160c090e1b04050612030d09170f040323030f0d0510030b060f031e07031406100b070302010b0301 72
    0x41d24021900c90b81545000c0380342416246511121f01c14100042107503a8801e42200e0645004480415440e254100030640c80000a600103080f10040c60011801315480f04502c11501d10b800d0f02070008000d102d5503c1c1502405005900000311000350a4410b070034541c02641818100000041c81c105420a01e403c1d0b901c0d43e41011030310b00058a108200c049118040d2614600300c10018110440001146500c216100d503000b0b80074035122000902d69a50b50f032402c41030907a003002520383c0c510280c3c044400070301c0c5c100c0302101d8420429411800f0312151000307a1700751080100c0c94030702d001d066803101e40d9400070f01403a4558205805841c074900c5032040c0040c0180b1000510036030b4a80c19025126010f448009014800380c603c02c2d441000859614048035803c03160644089850a000e400400d08081400140c0001d442070068812640b820014201007120b0148a035664003054051840340c9070388060b00c0f000d000c02000300050000c142d0040003001c07a54422300000075034a030344c407020900707580 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 838033390 1250 838032140 838032149
    0x1b010612020a08030c0604140a020904060b040c03050606030a092402040612091101050d090b011401200c0f0d02090a1415010c06020307050913020903100e1c02010f0204 74
    0x303010200900440c2002c00004014044070000b03142803d1040c144940c2c0c0d144000d00190103070b00d042103001107c7c03d040c0011444103401500302003080c505030401001800d6080c003d1800349190480142c0303024442d00c5040d004000040c0400d01d552100c0a001001c2c0c070720b90304291580580c00a0b060004140c410a4100800b01001e006d40c507603290180180070409804c0543c21050b040c11100000a5010180106241c4090802c3e540395601e2100f110002e000c0c0030700051111941200200d00b21003003100300d5644c10300907a148a0f10000361440e8061340b120f07080302c45025a21080c00304c1c01c02e2909441c102800b42d0b010308851090403440e0001804030005642b500d81c001d0707541480620040c0c0e210340c01d5600c0000c110706441603054102c0000c107041645140980843c0d404004219400d2040d01181d0130500000c024622070000103e100b0002c0d40f080240503c60302c030305d1045200500d128020018101449070240c406600091300300301c00c5a0381600803038215540d800c1c030080001110700c003500261 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 838034640 1250 838033390 838033409
    0x4080d0c03020106120f0308150d110a0f0f030f031b0b060a060e0114090d060c11161203030911040f0e06091501060c0305070b07030203071707050405061b0106 70
    0xa0080c0c20040d0840d101c1740c0181170958442810807012541801c140551503502d1f01d4100b035a50b858549400315201d910320102d038004003115074281071055130b100c00603803030004440c152803a0742d4a951100c01d010a0b88a59100c4e503041c00300c1000811a00011a07101074000d0800b407100c0c0584031418001400300e188111202c10560081c01901e082004410b00581028182560107140100001e0858210503000c00c01046002404081e03075115420300d0300303140383c2c070510900424045a9002d0188045024210004c0c0f184e0148805850300e0200303494101c48440350100e48129203903c04601408503030a094980090748611502551220300c99802c0407408590300240c580039008509061101c060300e400ca02d41d0110400c41d0350ba00407411803504440c41800d100c1b000d10711926041d00c581c010500080d01c11142c13001044809600b5070000e45c0f00e51166658a500c59035079440608280300c050382c000f8001032003440107102909151000300803102c00c00b11002d50703040c0200006800d442e91508240000d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 838035890 1250 838034640 838034657
    0x181507050304030c1502012915040b0a0f1b15140c0a02010e0c0901051219030e100f020a1b030506040f02010f0f020606100908160810062904080d 64
    0x2084604400301751202d1242c8024450a446e0300c000c80c4143d844e482c0c8524030840c030410952180d54031000c1c8105640c00407a040c0b91560350300c0452803c1c9400084494000c500311851440c1210b1040c0880c40c0262120051851a1440d545035100c1c0e219080d80350040403136030f6200da40d85101381c042030b844c420391000c41c2c0540da42030800d130b0003400d50b080c25105a0081e4450840f09545035100b4880307030b0559406582034407800b0000c19656180014280c2c3c0140c2c00407034258242d0905901407041812103d05551510700c0c02102d401c112280c0e2051052040140c00c44080000040c81403504004009940c8040c46d04098594540d207082c0368003030b0307011148101d10881aa0031560881c0c050b0007005014100000e052151800194807100000e10092084100602204086000e00310707010180c24908125003980c0c01c0303045a580e01c0c080364001d901840c4654600710400c034546002e210190f841d0071400382c0d07042e079034260042d05810112085030f00c0000280300101d050141005000713012006a42e66200 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 838037140 1250 838035890 838035899
    0x80d091202070b0f0d0c0201110a02010218010504080a121808060f0a050402062d0c0a030e040c0e09100b070506010311041404080903010f0606180b181507050304030c 73
    0x140c42c51552140c0d1541c0d409100b25100d5140c400c064825038280340102094001500c4001c900504e05514000c030b00c02c1d80410710f08500c80d070543c0509520510542484a1245800b00545160143c2c1c42a5401a44210325140004942858001c1c2c10001070500e00310707020744401c103001d0400e0b10350850045176100d0382c200002c3c15003001c00140c20001810007002981081d0300410228406d003134103d64440e00e550800d42551455026500d10000424502601c549500581c1a11140318480a5000420312809050a031800384941c081444c0b03180c503840403101c4a041072000320030f0010410103169000c2400002d01000000040442d10310483c0a80308541c1103103080711885540d801400e000d00c2c5030681d0480d000c45800e80032034009804c640c000c1e441d0031454000038007400e00b02562a17819400c10f00005041d5400110720400c1c0c451a036141d5910755125111544540a03104c01074031441e005031441c031030506240c0280148400104602d80c940452074580601d1603015a004880042d500c000070007 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 838038390 1250 838037140 838037143
    0x70506010504050c193e0c060301090b0d05030309010209010f0201060614090d02030703061b02010e06010b1303050d0507021e1809010f0609140f1b0304080d091202 72
    0x3405460100c804004506102d010441c0500a280d540480d02100c1840340c00c42900804021007081610079201c4030f00c041c00c401c5113032509010002c15444060004152002c1c00001c241c884500da00130300143c1c01c42e8a40001d541c090301a600f981c80d04480d1400d85900400d80c18401148140c03d890b001682e13502c103035000105400418417020b000c5901d054004e00c02c0315804501c0d000042d0300c1c2d074281e507114003050300019006484180002c5d4503110b003110009c2040925000407450000030551b20b414a05101c000385e00380c47d0303450105a2140c10000c018020342048002410148200215000d0300c0d83e142d694003480d269103084100b010680c0441c1d8a0f08511307000d0005009540e00441043d0100c00320008035441c04a03403000c01881440e0400007801c20007096104400501d034009090000582d500780c040010a600a44200420f06640010f43e0004510a4840c000d29100307080030001c1c420230700d00c0d0440d41c001500c21140124200010440c0008034040c00340d1043c010840d2244019655502a = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 838039640 1250 838038390 838038403
    0x1504030b0406050103260301030321090b06130612021201091202010b1003020c0316390e09071a27040e010b012102040801050c040e06150711010c170705 67
    0x30030741e01500304500c200c0401b42c0c0d015a41100d60500300701d4403e4881d440b410f0b040f07000c4040d5540c0f40314a082c01050034001a103003e240600000d55040100c0050002e409080d66202e018002d1480e80d2031107250b005003000309000180010050000541c040a030ba9401d100c4e0801800110040c0e460702144042032816100c400e80c3c00046082c00c40c504180e0350021500ea000e100c0d082440e4003480030f0030304148403140002c1107810b014040842900031354103801e41c200074058034544001452065011070700740742103e4584d028008050003401201d24100344007900f4075042c1d050840b0150706111889407440c0c05003002070080498126104401460b609010407103146001001c6168102080048581d8001c100309109080203061000c400d580f9401910107442a0380c0890440c4d8a042d082200348a481809441581c803a00120a521f4684a0400040c4494580d010300068810001d02000070300c052079030790820906052075680c07421350341c60f09012242000c0d84480d00c09400100c01c01000400e0207207 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 838040890 1250 838039640 838039673
    0x20f060d0203042306040b0106031d030a050d06080a0803060d0f0c15030f0c0e06210a090212060403020c0105030406090b0a05091e03040603020307181d0702010513021504030b0406050103 82
    0x10100c40c5041c7d20740700c0a8160600c98602810f87e03d01640400c6041481801c1c8005400f8044a90300c03000060010081d030b03c00c08000040305e18284002c1100c990110303060f01001d81007412141107031030302410450320300c41030704081780c0e40201c41202c3c00000e00096049002000f9503444400703074844401c405000e8482e013030082c0410314a40781c0c0701c88065400c03001e100300b1488140c82054903104800c20500e0302c52034214244030307554506000c0024400c41a000241418800c4c4c2d0410007080526280b207944000541340200036810813041840c0652003500910392040c0207000c081000011515500092001921508130058503002000007013071007000071000d141c00400e007561000300c0100070603899000d90b00441c41019000004200164814031040c01c400f40541c030700205603030362421100c1e0f400c101c0d1000440403010407400a48020f0042c401c0906c508090350f180c40b26400180d00300000c00341055299142c41e40103000110114014400b0031f07106921131900010780b941581402c280d904e40d1000e1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 838042140 1250 838040890 838040893
    0x9021804050f01142b1205070c09050403090e1003021512010b030601030b101115060d060f1e05250f0e030a02101215060c020f060d02030423 62
    0x5125000e030103001c0d9603045a14401c00f00707981c0551040005c80d00704001401180289115a005075550884001c606600303121b00f15180d60407215002c1618640142c003400b411580c0d400e82c0801005200d80c100d030790b01c03501c285000009691141c60f0689035010940310710b040c04003044020300c00c60410519070100a00c074140310500f08040ba90001c601d071001400b414000410110205031240d0103900b10606c5001c0c01094034143c2c0400117001040e4680307980d6059818864814800c5c0701411100c041c034040d000186c08881081c3c01d070385801c006403610400540400d90385071526011072240c0c48203641c034404000d0f030200d843d0920326502600a40041900303078989a18092080466400c0002e070300e001102800d00400c031100c444002800c00c844071310065085001a110518100d40c445550782c290134401c0300c10480c4256145004284490309d002e01c20100b003211042d50301601d004130051782a80c030014411454084a0005175003680c0054400f00e94400c01d504141d403030000c03d009000c0d841c1d01c4840 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 838043390 1250 838042140 838042151
    0x3090c040b101805030f0f010b09070806060a181512062d08150901051e010b070c0504090804030c12032a050604030f031d0318011809021804 62
    0x40009108007000d542d80e10030312510b0511510502d100b0000d140040a00074203032074611044462003505d40e61354000750b440d90f51130641c040d6128a0410300080c0219a44e40c1c48023200e42d649001c0c00115400565503c080c00b040404c1010340c2e41542e036414014040841d03501580441c08c541c0644030017a8003034560001ca060800500ca0040800d4035907240020014240781c0641c1c00080d511086007960f0407444030390045070045098800500b28060140750b0040082005690b680000190310752300c26043c00b4000200001045100010400703859000e028100190324180e8030070008040714510a0101c980940100d030401c1884919030610707004180100e100b20314010360303039401004051014807140741001a413110012400d1a410009002da80c08000c464050030142405411001081120b400080c10444140c941006ca2440351481c4450000114140111598101000741302c02c08128100565203d035140042058224540101440da0005036941d240b00141480000481c2180340070701d040c00b = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 838044640 1250 838043390 838043411
    0x307151209080904091b0b0307110f0c27040506040308011509050105130902070c0e0c0f090909150a0501060305160f0804112d030a0305072a060503090c04 68
    0x2007044442080c01103400082c009a1752408224081c1c03810000d014030a2106004140082c03c100114001c0c48a515074085550f101c22425588896030583c8802607045107128070010b017800e003c083c5030304071398601c0ba4504808950800200410803581500d00e03502c0780c003d0205040d0094122405002550104403080140340000b6040035441d1180604104000425190048501407040040c08803080195a941000e0030600040e04041c00b4501d480030b402030108540e4003d500881e0709801c41001d48a08084a1104001c0403200082c038840080c022620318030001c0d52101550f81c0318210300f04000400d541460760040031148014165200b0070018102014641d8108185660484085c80d0015a5030707114500100e946401e443d00c5a08800c20344030210316404095524026090138150700c1c4180c08100d820140e846000000107404a1b00410a8002051040515556120540c003080302c20225032005040008560f501800000da000710901072150340501500901e01c0b4212000d10401110 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 838045890 1250 838044640 838044653
    0x903050301090e191e0611130b0a1407140f0a0c0e10031209051c030206060d111201060e070507050c010807050d0e16030f0c170705040504110307151209 67
    0x1015400780c1000001c1c44c40e400700f40e407804041007106074419014440001d0183c0e20f0f401325007060441c09010004000003227048124070b000d495428507640d403502103065218940c200d0036800303150261907a1099001c1c0800f042070411041c481c8880d1040102884180da04014040c41916008440310409650138007010700d01030900e030300a4a4201d4240c090701c401894080c0c03050301103139010a822006001d1080b00e09002d80502e0340f200390083d000d030b6129542d454100000c2500b00d0700000d2000d206021401c0c44e90406004a04035100702e080000f480949034003c0c2001480110750031030001d6400605c1f0f2003045402c1c490051021000e0a1003041e504140c4005081030080361040ca4419070780d009107060034038040014815010801160082442e16420f01032a81480c1d0042966202c0e001d04c0000b883c6004140c4007929210f07034401500c40c140c10801004082c20000d0000d0729815002282c840f0255000c0c85804001c0041e0f595820741d100320302c54040d240c8544103803102e07003040c60000100e011405 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 838047140 1250 838045890 838045933
    0xc050306121216171e030901141005030f151302010504090212060f0907020c01080703090c09020a020f06070f0c0c031a150303070506041205040b19090b0f12041103010903050301090e 80
    0x30320f2810368071b958500004500400003038540d005464036241c10302c174201100803810342c240e52054064400c904c82180206580300403070055240341c0c000709400a80c0c0c921800703049404c0f0520516000d45040d90751843e58003a40c100c1d15040054002500c103000d01031606402001e02c150701641c10b4042440c00c0b40010f5118044451400c0c144040d6100203440325100b50b20410340641d0102d00e454031180c540280d00025003103528a24058810341c805042164400a042c610400150740d07040c50300c1050b2441200c1030000c00c07070b040303e05101b14100400000d1044081c440c0d4660f441030382c105186004205d60b41980c2e144580700e4004d810800241d00070440c0410311507841504011501c803d1103401c50201c07181e01c10b07a80b00ea2103030702c1c011031422212200f0070140101078119940d4029001d40f2164400c10238810841c0560090700200302c4e0420150f50b083c135050740640641614080c07031400c1d2021909548408804a000560000040c070035410341d84030760603c19070410010400c103070200c841d0043c0c051 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 838048390 1250 838047140 838047187
    0xb0718050d08032e0e1e2205010f05092401060903020906030a0614040b1e04060b0102010e01020a03150f0f050d05030903010c0e130c05030612121617 66
    0x58005040c09034131101120700039145001c0c600701882d0503036142c0d800c0349604c03c151024054814070104120101c42070301400c5008a1002a11000b0043d400f000410400c0682c5400c50b00c1d5501c4d11060351840410344610791080b10824040e10108410340403070603000b0b250115491a060300000184819980501c902040da5415120400725440320b20000c1d1403d81c0b144402458a400e2000f0307541e800c41d1f8042e0080c0500d106940e2120b81d51984100110b07808010b403d12400e00c0242000600072503415001b0094a0806000000302303071200705403181c2664031602402011a4a4001560103000c103070540400610104040c40005400d10407540b81c588050302c210ba100e014815102010301100f80101d1b019800c00400800680324110800307401090b203241c1980c41620840100b2624000b5801884010031266484500c0c640d0b601041110403001d0041e0780020740704084600d0342081c0c01d07030001c000c0040c200000e42c0c020805440d0814102d001540302404842c4144000704003080052200d44059 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 838049640 1250 838048390 838048411
    0x9190b040915030b2d0402010e090a1509020a0917070b0705071e0311030102071a09120c16060504080706120e0607090305120c0a11010c0b0718050d0803 67
    0x300741c074502d42c4000c55030542014148480c4241888404006444d140350700d901401400117007080095500310150340101d80181c0800d1000508283c0c91504280140e40300008807070020380e19180c140034040241c0580c11258a03150b0014149000c15040000c00c3e00406c20604903c1b807641d0900c04143d01c8400c58031555107014030129000c0100300081c425100a828041b02c1040819040f4460030020441ea10068485980c0b03040703040021300707060003100d03010790300036050701070401189a0503d842000206988a41d001d03001d61900380e411608002d0200c201c0030030050901c4004c80c00d2029208419034804010f0002c200010055820301180d02c2c3c0480300241011504003002204c450082c03c2034405000d40e5014102c10095141d07081040c0b030080c0c0b4000d2003140c503607501c00d280d110014030801e055015140c2c040302c0c00c0c40010b103240a0400400c0780c18981000580d00964442a00780404d5130b001f0049440040d0356428807082c504540c00820040745d217845040ca0315114240700e844040e009a01d0ba = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 838050890 1250 838049640 838049651
    0x30c03070b0c1218040f0c0e1504090221090d02060c130306090f0606090e030409020d020c060f01060219110910030804181d1203040c0f0b09190b0409 66
    0x1900203001d42490304000000207070f91545107521000580c604d0144652042c2d1420200c0300805417244214602d0894544400c00004c0a08040001e10810249103c060304000c00002c80c0c1d11f07105001a158108001101040759080d1006415000000030842c40540e8403401b5180102a40000d0180d0080c1c1d0005840c2e0340e83c2d08000d450801a40c081c0c01c090710b0103013409101e00810544054480501c1e02509003003051036100c02c00321040d100c0107582d0660580c028070051000901c0c543c001c0c406545030300401031520b01410001030500d001215101040d580900c01003140320303018481071100f8414425121190340695803808581120001004c0c01041040c00049000000328601c1000d035030400003c03602c1d5995451080704120406084218180c1402e84c1700e010740110446650803040d501c009000d43c0664a00c01d000386030401030003503c50080c40000012200c171a446400090400d042a2a94a5480205100024600503454031000c0d003054800c0200454003170550b01035030603000d0041072 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 838052140 1250 838050890 838050907
    0x50a020f0f13030b041a090109200a0509040c03120503040201091406160c06020106121101140d0608100e031905033103021e060109110c010e0f0c030c03070b 69
    0x402c4401078000500029499091100780300d0018141000200106403800c0e0b1395592010090a991840200a090611084215403202d492106003003021401170711403405070ba42c442c0001e030b000600b0345090302e00110844050092010010464850705514240146542410f40c0028140d541c207114603586000c0b2014034220580c1d814003116105004014500840011810075508202032071281001540c6882c000181c0744e52003e0400980580140c0d51a054188100042d01e24003aa540d18201001c820031070707070f81385c1c1d0b105215403400ba204190080c07040ea206c0036001c0701152120030040000c0d601c00c0c0400d611090b804001e0130110910b514246031a6280c9000f40b500e9081000c0403902c0d070500440400950b0307500d080c07503042c07194001d03800c480c441a042c02d05404801c42c41020302c401604404c00511550718250084030003480202ca9140c5041a4101009c0c00c40752500848103142e000f000181c584828100407002120034110060200c6403881c2c0c0000c1c0e5643c09510886900c200d02186006 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 838053390 1250 838052140 838052167
    0x9010b0f03100305010f150f03150f060b070503090a0f140f151612051e0c0309060a0c0611040b0406140d0c020303090f06010b0a0c02040b13020706050a020f0f 70
    0x400030f550000c02444a040c254642401403c0c81c01040394101f5410440019022003900400e41100e40009202584151340d85080c0040d1400000174445203449110024a1400801c01003000900031005540c41303c240204108002007030758450303008200d458a0030301075100c0880340c0c6500c06404480e0500c11044100201c0e1b569080303040e1000d00a0400700e00b0541028068101490461080c42082d80100810302d0660710b500070702c1c11544500d00d541c1100300514100f80000c001052108049909181281e0000703075890784048003410000307103c065200704001c0180100d0301d42c001c201d08840c0c00e090a00e04410510301851040404001100782402041120002141c00030b01075004184800102528065520f51059400fa0411710402620040102d0082500fa05840c2c2c000d10043c034100347d545d02282c0e070f032207000000da038000e40c0c40c05855030705d9650002c1846800f924103800b6849803014100a02140c100134180415940100680c0701816490001c48003800d00c0c41000713940765034515000303c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 838054640 1250 838053390 838053421
    0x607120216150c02060901020307020604030c1a1602011812030f060b0a020a150c0801050d03050c0742270305101b0f120e010f020a080609010b0f03 65
    0x41c100403150118004029110f40216407015115001c58003540c5841048900301c2c4000c49141c4010b030002e2003c03600180c40380210020b002d00134000324507001c445440d0607101d510f041c1c4000070b410940b400e460815907020300681c00c1140700c400d07119890050030745500c3c118440d13050002d004c040e991203a544810081c1d901c0780019249404680b41c0740c62000802070750341d4201e60429205510101900030403c0c03800d00036407039684201d554146c1c56910341014040c0c80c501c0108210b0511505000e400041542000640024002d40b002c100d0344c2d15004200503601032508400421101c0c0c90403080459140c08910b070741d03403c1c0a41ca850400c03243c000641e40e50002002c00c510341c08480c1c0340000004d0050002c1d1038580c2441c000c604006000710002458080b5002c402c40c1c6000c0b034050116500081e010700015007040740c0350b900124034007079481d210500b111841c8051003a6694042440c030450b0741e0007281e10380d00c000260788000807075042142c080424041d180306000300d42800000104007101c40081c8 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 838055890 1250 838054640 838054643
    0x2d1403030c16030303051018020904090812010f08150c0c0106120305040518240a0815010306060e130809030a0c0b09040b150f031005030d050a0305090607120216 71
    0x41d52030084009190200812030b40c4415000241004046442d010b201c07964070b011520343c10150207540c401500490041e401008042d98005c0d0384407a9240820725000080510080c18a07403a501503040105003000d60400d81c002d01c4480d80282c02c80d030b001900d68541d6503040103000c400c083d19003052030078090140c81c4a801020300c44400d02c0c40b02c0d04264004014209440c0102d4603880c141c3d038102175581403000101d0710110034880940d81c0c551503400301314401c030007200082c10402c0c130a6107402d400c81c0303803903c4020410344201952004005010b03a600c605030113482d640800503030310304181480e40503005020307401600700030001580b0b4106a1b002c11a01100f682d10810346046241d5941c0e25040980010700c031240100e00340300000110b86001a0b00000701c5d40d1241c6600d00344904500d40c03903816000141075060340c0148010126080e0b034104000c02d101e90395a80c0720741c2d03a09100c0e10b000f8182e807c00760180030654001c109000b02542c003c00c861024903014040140c4840c140185030b803446044800 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 838057140 1250 838055890 838055893
    0xc011b0f081314010c0605040311010e2d070b0a0908160501110601051c0203070902040b0306011101110a1428110303041109071115012d1403030c 64
    0x3400400080c00d001e040010100c2c103003402c0c5540d4500d0a012800f03060f5049600142c40e010184001a45541c01203401c039000345000b401e80b0f000c101c1d850b030840722600b0b1150040d500c54541182c64030750001d105000c44181403103a21000050f03503619507503a41103005410740c0120101c0d110322407611952601000b4490b54085603507420788107034000122115801140d00082c1d08030b032440c00b04000041c01d5412580b010386065202d8403114013404800300540000c036414090303a400060040710f40e0018001506007040341036a2800e0030000034000d81090380000f0b4003079041c255401d4880c0c0460041e2210f45540b03080c0307084800002c80c601210b138401d014000b41e0111140700355060050200c1c1031008102400e40301c0388120545290403d6407401f0845000707103425550300d24001c450030715500c219003040c05030400360203540c0030f03000e5103040c2224880d8806121100d000100504c3c81ca00384541860030305141540c0389800401162540c03000c190240400b024000010000e035920100101c0380304003050300 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 838058390 1250 838057140 838057163
    0x150f0913021908060612010b13050a03060204061b0506010b0f1605060a1a03030708160f1b050d020102030307082a0705060a060510031e1109120f0c011b 67
    0x260405034001100c02c0500000c0c071010000309281005002c9802070b41c081d0343c889405a1810580e06c91551015109506981000b88002081c3e00d41c00e4080006e180302d0790f805a1200d042c5040241180550714182d0401d507041e007418000704001281c2130f07064034580d4104698075511426694500e02c10401d0b84640c995006229200b80301002c507065004d1700c540c0c82c09120100c0303491000c03004011080440d42e41034104005413000100d643c1c00800f80704a940c07400071406641911981c180117030a08064451810b20380c0c0401d80c41c3c40c3c0c1c0301c0720000b808007200d00fa210300940b0380000350f5900000380341d101441350f100c0200300c40c5100d0a80d20514000840740e018108101d90325100c040b9006040c1c00c8619111f81d50200c4c2d07540302c580c0030765000d6038009000010b0101e01c500003103001d02441c12140c940b18901c652134030344038420790062041c11994522410307036841c240c005204080c090104401c0090f0403101c0400382516020941e000490400d192083c40d012684402a03452240050001c02207800b00 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 838059640 1250 838058390 838058407
    0xf030309140d080c0c0714031507050d200301140301090b09240403020c0108040303020c0321070c1104110d0c030e070618030b070c0c03060515150f091302 68
    0x96003410a5001d6560a000c6440d0380480056a000700b001d02c400540041c1811f101c54260600743c1c00c0d0103c0010100c40c1d490310144c0040c4402c0b0710907144200018000038100305c88900502990860341c550070004031015952038400105804180102420a40c0540b04100c071a5001d4020703c10441e004107041c40c56090603104070355541a640d401c141300c03107a0910b2112400c0c40300440f00e4407a17078254010b0100714080170700444000314004c10403418142c0c20702c20104c041c0c40800242007540c1c40c988040c608100c0460301d41f9074602d0000c100c44200b01c90442240d00217084e8a480d821011030950f00401d90441c1d0340541041e030b0040c01c0103c44211f240c44510310003030b0b50641085070320400d424140e61310b03a0745034001261008510030002080701782c1a034040001518015403113034000200d00d010301410a842d41c0e8000b083e002944180d595a8480301480f910404c240000800c44000312900900920b50101041d0340e0300851324111241613002c00c010b815038480c0c3e0b03480303035885000d20821035450b50007 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 838060890 1250 838059640 838059643
    0x5040e19060b042c04141612062d02090112020d06030c050d0b0f130b07090614041a0702010201090b0901020d1103151e03150109050606040e040f03030914 68
    0x5200e44d038401200011405020781910f01c1210301c1d150104140d98841d900e68490040702c000f0203c080c26144140480780450702c1c5070241d0305c0d002d0310301213a0404940b0210304045040c2c4d04017016590110445c80030f44203102a0810000c24543c414160250300c4107840c0e00181c0d10311280c50007060321140005054810034415500447c20b81e03100b00a04400c1680754414402c0c0c11a81c0c91008103d0900d540124003c0d890040d086640112808c0c0d00780c01c0360807180c1c2c5143d80c2b00810384819020880000092100a0300100300700145042d610800d1b040030700c3c0640b0108150b0400300300034040307000001ca41003503901c00e41142c0582900f04090404500b00408914001d50000300c1a4460078a0b0a500e00302101ea4074045034020703ca08180481c00e000f1240401c11152040083c010507500b000203154a161002d1000c48031512880c81c0b49480ba600d03104460040d03c074020f169905c80d00c42088184951000d20b43c02c1500150021140503403140c1d0f0f403034103030018a42044040c1c41c2d1801c2c0c1408580c803420 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 838062140 1250 838060890 838060897
    0x20d02040513090804090f110c0a06060602010c051204080405031c0216050a05040213180906061a0304031101090c030f020102100b0a1403030702040c0c050d090605040e19060b 77
    0x50550382da480070304185101104580c2c0440008280300c808200400c00114141c0003460081c100140c0080e91036407465210752280d0050b11050010303000f003a071803001d01001e44901801042a40000d100c90031906800034814821452051070802c02c1c000480c06101207074041c1c0d000707400060111002031f410078680c01c41c241001d0000c1d10051250031100200d500e08244402c3c02c41d9000307440382e0220b501b800c003000082d4010b0030401401b00309404d000074031030300c0900007000030201d410700000d052005801d001c404e072505a080ba48200d250038207a205910b8010044a40c01500740c82c010311740c900b5200c0c201d80988000301c1c014000e600440004828044a0310305920054400d0b000c60710380064110926040c0c1e4007604069600c081c040383c0030402c2058801d0304906c90000101900c0c03070410503a00240c1101c95a005d502d00160a54516008100301081203c80c0080c05043c140109490050b006005114602031411401c482c0c6000c904940200e480c4800d4540040105001840d154986010943c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 838063390 1250 838062140 838062149
    0x7051e0306090322080304050f010c061d01060f1202040c09120507090e0d140a05070804031b062a0f06051f090e1209120318150301050120010e01020d0204 68
    0x210b141c450050142006451034048030b00405c0a5814103280204110862040328105410301102d485280300007030003441000210b4803a6540c50110000603068182124070b942c2020f034401120200030300541ca6000d0240c100c56a04840c040b0360303903412090131100481190b00c06a000c1c1480c0c95001c00300103000c2241002d462416600700000e8101118541d5110001861031000c01d105102c0c058140b40342500400b11000542041480d203841e0b503444000319030043e841a02c54888905d0001c0c12601c0c41c0c0003141c02000d079031820300140c1502454600c2203069589455100c2c0a0000c020304c00c00500007001c40c8a1500410300f0042864425110000000d03441002004104500004216008a4440e04403142594401810a0803c0300b8501e69140e1003a405643d04c00040d09100c20300700000c1008190803a6610080c09002c0000814803800b0b0300080110031100105000500c902d982c000c54103d034000d0f540003c0c003107891400c1e05c2c00f40182700c00501c20481d54000141c00350b80d041e96400600c101e4 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 838064640 1250 838063390 838063417
    0x101203020624220e07090e060a110315010309061a0a080f0714040e0a030504031203020702220e030c0a020102160602030f03090321010e0906060307051e03060903 71
    0x45500859111929200410071030384a903070b5100d10039010f8204588000c5164070410002442100416103a10303200466001d4424103031641c40c0c16180c040144012608101c0009050140c804941058801c0b40802050000d09101d81001e0303005a0f03100c2d030400781c2d01d1508100c040002171700d9880c4600000d0100d8481d03a01030f0580c04000a41007000095030700084138900094108141402c509030001d03102c100c2056482500c603180c9110440f02405400380e050320945500365150301c1c52505141140c0e801c2c12403c1810700c1801100d0140c0c0701e41c0c0d00d1004041c0e102c500842005600f001d8580141020b0018004038480403642c01624840003d010101c14000d8003211600c0e180103104100601060199030010f0b04180500207412440001540d00040203400b40c0707050801103d00c2032003140c44442a8205038003110700411420121015940c0c1140d0f000000d000d441c035000011a64030105440341a028100e0b101821043d622150a2681e0000300203007500c090341014410701d96179810114004210 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 838065890 1250 838064640 838064671
    0x9050709050907030c031e0204031401020403170a0201180b060a0e0c1b2103010e070c051203060402070813030204180b04030807050f0d090312090203151012030206 72
    0x1928052aa00030803100010706441199550300c404402a207039203d0448141900e561115030601c2c4261088000b0500c102001612107195081040380da8000b03524041c100e900c10001400840c0e40a59840c0254540c246016500c03251500120b0040000350409103000310498111410070140d031456600034002250b02d0758100c6d0300c4050007c20340350103840180d101001040141d400114800999115000c09015140c10011180c180c43e4514a85c86c242400368000000601c040f48414600a400030b4035481c180a07151810395455550740e40b00c5010996456000c40003c696a03150f4048841080d40b08800a07115840001d40030b01000b41800201c3c4100d062003c0d10380c00060610140240036040410840a525517840542e841351004d015101007007810001c11141c0f00c04600207010030859410001201c01007030800504c40c851002021442d03d04104100c0050380c0d0018000c0c04140286209103100d40340d0100c81c8140b003c041e0302c070700e68280d50040c42500741500410018170903903440c0b800c0e200 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 838067140 1250 838065890 838065901
    0x30403090e1501030b1e150c0312010603140103051b210601051003180308040201050d09110f040203070f080903190f0e0301021c0207020301200c07080f030f1809010b03010905 77
    0x6102254405207819010a050440e03941f030800540d6905070a0b0300981440c0040082e1030354119400042d21070214103801e0010031075164544903204501c10800c0c017411083d41581c1c2c0d155120904803491081c00c3e404aa01600c05030344201c00303e0903400d4115031141040311440c1c0d1403a1140002d2040501c50404038032000c401e28001c1c00b601100c040114400d8840d4426130b034082d14841000b601c181e042107001c3c4645400d0400c0d500c1280a4035018544e2103042000c060b00b0840d908014081250140d03006209000100342c101807c0d0f09200003900342020b547e61920034551850199184090309460003100c403031501d81d0420b81c0c580130f00b0300b070307550310444282000d06060a0303105d07144800c5501d41c058640305c2c1e00400254060320420348018008034034415025162000c0050b248001d01e82c07000002140030441004006101c0180820409000540705040e40c66450f80035503015110700703480004522041503100040e008000e10000c00d160b40e80e5840c1c040180681c0c009002e0050344501c0d0501051 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 838068390 1250 838067140 838067149
    0x12290112031e210b15040e06012c0105120f010e09121206040906050a0b030c030604050606060304030507060606080a0e0a0c061b0602120a0b011b08030403090e1501030b 74
    0x40455002d620340701020100500701c5071080114468100381c16903240301c90021950740d0001e06140051405aa40e103c504041c4410000d5201411890502c0318203c850031a000e20140c0540000301c40fa40015404402000140c40350300c1220800180441000100440300c1c0140881506a94464104184d1940d45580b040d0b5920385e90072181c4000c0d40705018200003641c0d5610959071001001e040844c00310445d44e100c809444051b1001e00e581034941d0680d01050030100425100d2540850060405060984800b0349032800039100700d005020000c001410300d07000f24100c643c01c80d40600204a2299250b10040803007009a940c82000c1d420880001301d071000019081c0350300e030380107407062080602c0c103181910501c1c0c5411004203500ca0400024000c120544041c3c04002c0d0102c0022403945000301005044541059200d8148095500340c0103a42c0088140000c41560000800d5640e840d282070903030f00071403249c0c400043c5000000070004078455443c0700d8080218203803002d0009889020410 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 838069640 1250 838068390 838068437
    0x1005090910142e0908100f0506270603030903070e060a091103070c0c090f2a0504060305090c100f141c0213031a0405060c041229011203 60
    0x204030f110750450000114031001e0b200c0c4210030154241500881d0f0345400071820800c070010036000c07860343d469200000e6581402003a500540445540c50302c0d800c070a408281034010030303103020f4146100c100090200d0b02c3c01c204840310500010110749080ba50703602004501c0c1001c440c801d009007507030140000c0d90456801a84003802c180410325040d942c4070300041351424035034142900c0e82c3c514082d0010342956503100300302036219003100201e06003d1a500d1452010031000841490300d0f045003120100c0c9034444150303070694550380740118a84d215004880e00d040c000803a11a401580c4858403840b03203401203c3c146403280c042d01c03001c44050200000112074010202403500c00965a084801d01c50303030960007012404a0300c80c000c4545a01c070744410005443c00254050400081000c1c072050100400503294008103400115151504100e03204500c0e851400000b0311140610f2282c4c516110003000a0308207903002600200d680d0380da083c1b1207190301c2d074440c420ba01281342030401e2188080c1d0803052 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 838070890 1250 838069640 838069669
    0x1b0301020307080a05060d21030b030313180b10080103050c0906100c051c02030307020721060b0f040c051c11031f0f06020a020405090a02010e100509091014 69
    0xf210800d0703903445400400750070002c02c1a540503000c82d10403000078203c3c00183e4040c8419500055081c1e040d054041c0841d24046a4248290b1040c0410201c5050200100003921612400130803004428240d0a0140803294192139000a129040d4040d050340424410704982c050000c95260072010003d108010702c05840694000c18002068803555002d890a8034005100d041110442c28084240c03c0741003018044100058200005000c0480c2d410000720024190b030350552000b0741504d40d000f1100c0c081c00780000b0700d00c131384407002a0700d80d0317541001c201060b0b10054401d00c100c01c0d111000401c1036200313540328400810070410310135002c059841241a0a92400c01d010f00c0d58491000c0400403018072501a4969141840086590449c003801100203050340e800a01001c61240704110540d0801031504406030322003422440540e80c09a00c5903038202d81500d549240c80e8058a0488161095040d0f0300e070441014418884c00d804034130076074012982400000e1010b40451000c006005402942 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 838072140 1250 838070890 838070897
    0x50c100512011401200708070e070207050f150a03092003190615030506070906050a05070f1104110c010c0203030903120a0915230601051b15091b0301020307 69
    0x107104880060160094520050404052a243c100350b81d0401d8005c40c480d4440f83c0d0020b88040044201c00c0065030060a40c07001230b078600f488c103c04020750710039a40c0f165510070140c0d000000d00d035840303d09400c1d0388002c11400c026a00da4040300040c003d000b10940c2184c01c424041460303512200c505c80c0d101110300c2c005028144050520444090f80491010165011543c0c0d20000c501d11111480350401588250007420442c54020700280a00655078040d0301406400c021041304964080104c821440e4401e01c20b1054607054201061001d20202c1e450350007030700d401e601d4400c00581d00b02510200101c0d400078403078000c01c0b0303400300e88034081501c400c04a5442400342c0005044522149a840b009001c0d0014021206403907244012000c5510001c480707982c0d91500100c042c10100340c800041c005c5803902e02c40e08040e40020954403030780d444031034650444e1550303440a071002d0101c0e0011071070303101e840b040d14200020b0154860326114400700c00a200388030401032608060007070720b119201d07648 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 838073390 1250 838072140 838072177
    0x60a0b0a03030c0c120b070e0409020136230303040e01030215070209010311011b0b0c07030318080a170c04050f21061614071b0909050c1005 62
    0x40d01034a0780f540991084480780d04c3d01368003003650604080724904850245040c12218102042d005d00604511400140964202551140580d81040103d0101c0748180c000030700810a904d1800780c1c0f4040703071220118814181e4400508040c9200c14040205103000c09601540089410151340f0b214901c10058102c80d000010001f6151080f08080301043d000310303d91034110140d0008106a100f44c204075040c00d070112500754a541c2c0075a07030740100202d19480305c50041ca40e850344801e01c0c800600351203004800084c0803007014426006215400c0700001107882603410703881c003003619803c007861072400030baa90f1003d50801071411800b0b5010301000d841c1545410700740380a1211065081c035001b5001202010140a0101140c00404a001007800039020070309028040401c000c031440c0f000300801607141c01c20310072104041c04a405150b4030051604a0300c0082041044400b80b1341c1c88001c0340c0703107400064818070001240303592078107c00700e405009140401e00700b5a0b2a00440701943d4280c55640c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 838074640 1250 838073390 838073393
    0x10203011508130b0f0a0e0c130507180329010b070602090105090907080a0b0f0108060418080a02060f0f01080d0c050102040b0403060f06090209012a0b0103050d02060a0b0a03 77
    0xc1c541c2c0340c0c1203544010b002110501c15251401c09010507030740c0780800700ca110b04221882e40144141c10001d9490009840a20043e100250860003514480031b2407543e2900850900c50207411044030781d40300e81d445d441d00641c0e01d0500c64903140d104151140074440944060020800c3c03400c1081c161107502d10541d0420344182c031000000c0d0004640103051040c10000b84049945101c031461003680c4594400a01e850310143d000c068508004806000f84c55500c81400e10b42c4e003240342968050b00555002648110240302c003000c4901020001e812460002185130090b98089080c610500e40c640d47c08a59884100388800605000d11620b2015000005200c0d610741c0701e02007500c0032a00810015051680b11007290040b0790040d40111011603860031400c02c08034040c040c4c5001091038000850400c11803c00292031080c1c0c00600d800845000300030034142104036016061482c3e007100700c0361070381d6840b850499918058010004d01600c65032001400c911040c0c02400351071200601071002c65481d5 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 838075890 1250 838074640 838074647
    0x290a08070611010f050f090c010e0d020415120f0b01051503060112060b160203071508180703080a05030a05100302010504060513031e1b030503160f0c06080106020c030102030115 78
    0x310070442485541310031403103a0804050060034000d150810400303c5a003032040172580340c6800c80782000d050040030301b07965503a0760310702003403050701da8050343c0200c0c40c064409400215103140b60043c01d40044550742c410140010815044c080da44502805000d590705c8a0030030a050454901c18a984102000041c0095208110b00030308010144004506107031100001310310382c2c0104187d0048044a00ca8040540c81c0400081c00182000d6040741107888020700010700b0000300400d07080c4602c4c1c1112040c5800c0004001e020b00454210f440e03107848410a01000304203a0041c0d0b251081c4a050001141c50101c121901d80304503581616000e20b414603090082d50f00780c004401d10f8108074690100080403030300d1090001c01450f50301e1003100c41d68403140351071030b003580e0300620b07420b0102204e803c02d00010360b000045940c541c141c0ea4500b00d5210161030b0107425011440b200030400b40c1c0d00d440c009100350b000035115040c0c61142e000d661520004e0b8051500701e0200344217901e0740851060450440e1401b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 838077140 1250 838075890 838075907
    0x1081902040213180c1409010f0c0515010e07030209030c040c090e040c0305060c0313080706020d0218120d050306120304031a06010906030e031207050c01290a080706 73
    0x4050405820840360280f540a014410b602640109030500030080c40b07802c5610540d145a142803d040903c0202c10001c00c829028032840e16040c01041d0804031b40316030141000110442c0d111003100c100f0f040742b0f85000704050080c03080401181d00c1c2d10200720441e00a0081c0c4116a43c094018030403c2400702c00c20001e00f0b180241c4106100070a0000714819060f01c2546201e580104001c0840c0c80c40c0d45002860584d0080004045500a00c103000072583e885070002031003900442ca29071521032134103003100217200324007061140c00d00c00a000c0400c51503031000903803628011151451481c05a40003540c458045402c9080024800c100080a51410004030001c0e07400c80c00403241400c0c0c617a61191080c001d01601c107801e85108000300a8550707400041a07001d043c440ca4248603007014045e01c04d0f03407401040d60400ac01064400040c081c1071007035003a40c2110300e8140080c8000c80c842c0e09000d015605400c1c03241d02a00c0905107544d05410311010400807250010010040907107481d8086500b1035 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 838078390 1250 838077140 838077143
    0x1051620040e0105061807020712030e0a080f0601090c050f0d02041a07060c020a020907030e0a1e0302070f080601060f030906140f071715120304081e06010819 70
    0x5640062a03115840d18440d42d04800009000001c00381005030070850260302880501003500040410011000c0e8003142c000216510324001c0e2072191000d1030203582c40c903480c0c41100e0f007000070b03600005414400006c070000c07030a8140d010b0b110242d8880c010003003501c6882c032505002c540c00b008006806441e241c0100807810710100010b00789601d0704507803002c07042e1400b00c0300c082490120b101d13001d001d0302e88a6540034244078001003220701d40b281e01052068a0041c142824980ea801866680c244184800c04146501c181084105103541c040742281e50224031080e4018400d21801107814184003030104140c2e078040000f018983c0c0303400e03400c0f02c100c070f82c4220b40c400301912203103240e0000f60300c0c0c040e08211001d41c180711140e030b2034800614107400c1030007400a810000024071a03110716400700c82840d0003188904403042c01540d00008110181b00135808076189100025001865100c003180740c091003514403101036410110300c00c541d070b07840d9402e000c0e22400f60088030308441003c503281e01c01039110b03 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 838079640 1250 838078390 838078433
    0x9061602030106060305011d010509150d1209060201060b091e0d1502121303081501020a0b04151503080f0d1d0d1202070b010e040302070b27010516 65
    0x20202030380030a0a40d01c02d68000e00c0842d0302c9000512a180025424803a00c901142d201c1c200c96142500140d10424050030403d60144100e2a82545440d0060030003603083d08440f44a02160035400018000b503001d120705001540303040130124605820343d04544051500400348948001c03195524081c0c1d400080070264440740324100080003c00011805502d500036003001600c6440e205049102c0c1d141c0240701c0d49080e00c480d00000300198100d5000303500204003020441c0d4a800a00041c1d160070055000500390b24215403c020401400c1d590302044400854018400b402c40385460382d11009460000908194051004403070700409800505804150b1000110b200f10100001018036910340381c10901c05d0300440f1480c5025908880700400c5c44030026402c625002c6035031140c5101798410302034030440c02d00c0b4001003828580f0801454015003410f200ba55524500c25055940700c22440e10601c1200c4054283c040496026105445141c41109801c494100032507441c440503005c40b41284008 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 838080890 1250 838079640 838079677
    0x908070e0a0c1107060201140a0c05030f0a021b0f0d080603070b0a050d020a030f05180d0e0f090f0709050d1208250c1506061403090102090d230d050906 67
    0x140801040013100401d5160000a2004004200d0301080d078001003d8288080c2441c412041c01740d0f00104480d807081d00085c0070000ca4880d0540140030307200e0f581c015041c01b042c10810900001020a482c80e10035035a200b1a0501101c0200595419900302e424541c140c100700c07410481100b40c1c600030308028609181c03180c501440e00030746004a0704240c003040000380c1d489000040390b1105c2d10070940c02c400842c5c64a000000da00101179a10080300384400100512010403410076100c8003241188140300510401d200c0c40d140507150001e03041111018000b410700f80e400141402e150500d40b2000b5008450b5101d88125000192500f19000e004810714544210f0030310441d00c050600c400748212682e0301c11150300170504254155000305240d14418514140042043c00d821000c4180c140d00c606a180ea2240c0e186501107009000f00007181c1e400c030b110070315080204803500000d0303001f80d01a0340342c1051000d14081e40550b50414054101c0c00b08908002c0042546080d00c06071013110000307848481c2 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 838082140 1250 838080890 838080917
    0x51c1a010c0507120f03030e06090705060a140301030602030712020304050d0305070e0904050c010237030903060e03190507030f050c030d1b11060906010302091e04120908070e0a0c 79
    0x145a880701805558116010170400100f5525000306001808864020040360801102c199200c0d040e03482010320031000041c000c014140031b00b5030882090ba007038210380e45039a9241800c50295108031403e900090922981d100410071038800e8a00680c0c104000b480c000b20840030550040402616030001e1011100d803040040c1d4a5140440c8500e10640103400d101f007105c00060f00d0401048403054000503180d54000d004c0c14181c8001c00589405034080400c0c0e0150b040030381d92400c00b41c10151240d81007020b84116004000010454110064905808800903400c1110b0500900d080100000c01c814481d42d5203034480d101801301c10344400c06982c03510304903100600843c0d400040e031348a0f040040031003851260b000001d081d40c2c2c580c224060400c61030008441da85800701404024426003400000c600c141c140c4e450060b00042445c42c8848640c02c20b400c0018150030701602003800103281c03e8003c0b8812501085145c00c54100541c9007a00343c80e5070f03201d030014010065040f4100103e4074000f85 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 838083390 1250 838082140 838082159
    0x5090d0f0206131509181a12070501020d0c080304020909100e07050a050604030302120a03090c032f010c0803040f0c0f0810150b07030207090c051c1a010c0507 70
    0xc640f180a80c46968080e107040100d100c0802c2428418040c40030f0007004028150300c0c000d050a42d164a40300c0040c125081a444030132404124054a0b04a10f40022070600c0300c000249030402d4071026000c81b04802e82c600c004444244544d0001006060244046001424623040366500701c020881503a00020383c0170041000c403440e1440070300715640404000c0185042031a2118050807040c1c440d140b03003e0a585000e5920584c04a240ca50000b0000d04140f07014800c1c1e21440d18203a1140c2440c40b126078a0420101d05406208417524540380703082c0824040031301d450503418858040c1c6910b589400d040c0c4407024039420007441900c0201035030002c4000582600d120f800513200104008821905181149140810100c48900050310305458400d01e140e440100300100d039200e80a20b42d42d14050300d0200c0c108010b5900c4014114103105900014a0300100548501c4410b003c47c2c90030b501d18603005406460b807500c1145030162141c02c0406071544074283e4814010f00400803545074035030365074110 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 838084640 1250 838083390 838083397
    0x90703200403032d140d110901030c0e1302130f171e0601030209070c05100f0b01020c0a030602130f06020d08070c050607120f090c030515010605090d0f0206 69
    0x24440c000c00050107008160f00b01076010400750450200381120390703d00e12100c00d01d1201900c4401803000310f01041a44840e0300d0125134a41c0c00c402000d210710f602c0103040714460b4005251150110f41014101c100c030305d00c201e0000c0c1d00000018480f080d10001c401e0000000d5200203224481c0700401071000c030343c0601c61003100d001422407000c00c851a00c0010b00b541d081010102c40251070002100c00c0c01c0503140001880c3e81541c0d0111000c0c00e4588035080190307052030a00c94000c120b8001c2403103940c01e0704820780c0420000315040c9400c2c003c8041c00c40c01240c80350841441d80b0f50242c0b92403003d002195655001c1e0260400c0d5030040030b40103845028901120f28298000001a070211850480d159807103000380b6080101420201202182956603c0e2125001040d030010092074a41c4411841d2058000140c1c08070217000812a0a442c0d06065a0501143c00240c0700c46c860b2201c1c0101081d0401e207140e048030003982c2c8072410075800008000c4083d04030b1200380e5602403416582e01c007603580d29006 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 838085890 1250 838084640 838084691
    0x20d12020d09382409040b2719110a08061902030421051b0304030c08030301230609060409021e1c0b15040b03040c05100e090703 57
    0x110000c0443c41601424481c1d000e80e408101d0355582c810700040002558505401008101c0f00c9402c06042e1214100560788a1980d2540959281306010510461840150003030781d07100a40300b011a003040d504d003041205015135108039402126000c007080224003901d0b08103403042d2040f080c8040d10340000b0303500c003020b5005901d69402a03000d00c8007088150041107042c0300c840d9015400c610301a1503000d80c081c0301c1208071404804c50f001702c4c10064030441c21502014001e801111200091035102603a030340290104642405022102040c40789000007074a04031450482d070a0b4a02886e455613072001181030a00d01d0b00001e00f84020b0000b6910100500090090300f080140c941c8030383c0c03500360040c1943c0c1c68000291003040200180403070305d100750111045078000f80803a61007003440208400c034100e481304041c10880030030082615400c0000950142c3e0140a01c840c00c2e42d152810005010005001000420403030140c504050030300c2c0142d40e9002c100d5040c00660b41d503140540e02c3c01c04404500 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 838087140 1250 838085890 838085903
    0x409020f06070b1504060501050301030f020109031202070503060f0f04080a1817010b0f0a0504150b0301091506020c010807031116050706120b1c02031e0102120705030601020d12020d09 81
    0x41220842d0a0700d0b4000204c2d90413241848501c2c40c01001034824030040c0405041405604500c105590003480140000c0d6449032004ca141200350074000c4d00d6424901503176210b4007544c404280c80d0285c40300c20a004645e003480020168a40d0790b5103000983c07040e40840b09105140400700c241c0d40c1190f80b10401450b20700c0300442c81200700741c00340e421500c42015451041c0f80b40c000b13540c0c03d0345552080d141900c2c400e44001070507035814010a041984260701c07070b00c54540004008100808903805c40c4075100a881454801c2584400050344c03070f0703110b4410060008020200090316188250890b03103a00300488134481c540340c1c2c50b8400c451404010042601e00b5401981308019480c0d0282e032040c0d001d0b0400808211413004d0f01d0000e01076500e00c011b040c0c0b45c11402800103080d583c062140c101301d02400502c203103803100441c110502070b420001000b0184c00c0031600144040c0e001c0c0301128890351059000d0103c880d01000e099410160b80300d40c0050907035080c00b0030801810284604100701d07000e01d1307 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 838088390 1250 838087140 838087163
    0x10302090d0828021b0405130204020d0c030e0a17070c090911030607050405060d020c0304050d0308090d030509060708040302010b101107062607020c130b0a0e150409020f0607 77
    0x2d2050302c0b0243c0e01d158000840d0b1140c164043c50300ca60ba5400e41006100f140c2c00309040d1070315000e160703041106400c00780d80320b0710018503a41c0424113a402100100703441d4509200c24011404a1612880103200240408059404401044070072030010402d46114124000086460700b92355021107a00300c0080300c01200110700200149020000c041e4000c905242051a0604183c007040f0740f80203000203480c400e50082070301400c040d010f109072000b0741009895407020a040e03090041000d0b0b03040d1141d00e854042d220741070084510a0080074450607010009003000d4845070000c6440550082099046550742e01a11340309603141503450b580542d66940399401e403030761550905c1c1042c075290300540038840d440039031f4a21040100c0385e900d1007600341310710004a59262001641000303000303403110364000c05603640501c058680c0c1e404034100020681c0c1c1080c90546410440810190584886404d80c2c00000c40c5a894a0190044151188064250541c41e071000d4081181c581045504175680e0034480c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 838089640 1250 838088390 838088437
    0x7180b160203122a0307061b0f020c0901031104090605011202090a14062215060210060f0504090303090807051e070303050d050a0b03160f0605070c05010302090d08 72
    0x40040c00c0c2d0001d404803440786000700030003820002040c0e518041c0c4c0b00d00300c150003100042e070040c0141d072a00398000c0070501010410b4000140040002c80982c40800c0c002c00762040900d100040128040002501c81c0c0100d9003542c8940c14842c1c65030b0384156005880341c08000004516018050003810080c03080d25079010a4410419180b0340202104400ca260510781e40360100844040b5030841d1058030071148400c3d854207140300b0b00c0c102c001c1950440d41014440750544001803a00f8042310256801e448085007007072401c1094400d10b01c07514000b031110010034021f900e4203521485403240f107070170005000b400300c1e41e83c407104e83c000074000d840d140c0048801c6950441c42035148091841100c01420340e003411580c02500130300070b40031580c42082d650381c00a40303262016070004c001080c00504980c1d42c21224400c0c52210782d6030380144400540d6851000442030300032010703106855845903205410b541001e00440081d041a00841d51181c240480300c1c021520040040c03000c182d00d02860314091001 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 838090890 1250 838089640 838089643
    0x5100b1f0203130e090a0b060607050a05060f0c09010c02040b01090801140a0e07030b04030c0c080a050706030b030d0e190f0f08060c07020d032007060302040f0609030203030307180b160203 83
    0x390b4040d491204e07075602084210900820103020a5920000b40d5003280c403000003150650003030010041031031185039590014442c00284041c80759103008018501da40c0da00c204005180645060350380492400c0c601100140342c950001882c07108103141414010b0b80d2150001d0a40345e00501059001c40240700b031010a00484c0951104040d9560007003900c2d521716503034250440c400607c060100600a0f10b1407041160140c040b1005040e40002c40340000c9082c00c143d80c03105414480c51000c03d181a1054100e800d0101d4035803403030b06c03003500ca00e82d4501c62038084c48510034400060301ca40b103400316404107110269044510140441c14203801c002401d007502c2d2442c0540c0034254440ea100c00f40084d1005a49400b5084042c607414907080103000e092005a40d2001340201042005001d9104013080301d0303905902a00891315004a0b200e61381c0e503521002d403040c56070ba0201940541042002683c1c4900030b12803840b01e840c41c42c09101070300b0782d140450700d0540c00001550000b09885a041001c2d40760 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 838092140 1250 838090890 838090927
    0xf0203010f080604050601060c0515090102030a050105120706030e1203070f0f020c0d060f0e060702150606040b0f0309070b120103121d1309020d03090302091305100b1f0203 76
    0x901c40b00500c014102a100c044d134540d8144108001c01041c09444c8080181c1404484900540011003943d20b00b018400355000c2c0d00102c450500740b605d0724000041b1481d000b10b010884240c400003600110341496003c50203841d000c2c6409801c2d1103010008500f241a040c000c6206282c166a40d08219a840b2001070000040351051811940014504001c661b03600d030420450300e0388010005800c2d11460040000762001030f15604072401580c0c20030203180d4010500c0d070080110382c031401a40340e0b98032040104034001c901071a4450182404111030500200000713503005500c0740201c9801a642d00c00301043c0364055280100c07401c420000404c02c100c554030b0211100a800e08101d02c0c120312518550110b016903500031840399264440c4003101c000140d0080c5a1a60081c000c1c9071111001d00340a00500e06500c1f0880c000c0d500788000640307010b04044103035922a4071002a0070121014401f0002a0039100040781c1e110300d5100b10201454144500c1458600300c54005d180c54003a11402c0101d81c06 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 838093390 1250 838092140 838092149
    0xf080a03110c1c02030a02040f05220b0604020705070b130f060206160f1205090604210e0405180a050105060f01090b03220804060c1b030506070e03100f0203010f 71
    0x1400000c00640a50343c4071000d0781c0290140e0041151440c4500000340380c0001280040c1d0800e01d480311a40c00c214054000500c030300000d920b00e5040340c05003098550343e90384085c4098915510200420310510307140d0000d051407400b0300204c450f070a40303601c1140c0c0184d01090741c441541d10140001c00002c0d24000750440208001e0010717042c0c5241040c00742c0b80c81511400d00ca01001101c04003c80d02c1801000810140000058100064a050320481e0354980041c1d41c140c82060300d049003555139182240f2400039a0741a9030f15180d552580009001c060540039000c01c840d18403040b010001404100504003166001d01c0021a80d0f00b0b203401031000081d54003a9107410008506014410075052400b2641c000e5584c170481d05110071180c1c0d18004000e558070b03004012500009000030340b82d6010000c81e001030b000fa141400a1074450400d03505a208612000748140c0041c000103103100d024140398488408081d007a40c1c500c08240c501034084940001501d48915404401440b100300c0c8951214041c0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 838094640 1250 838093390 838093393
    0x2b0b010f030b0d06050406020f0a03090204380607120201050a05010b270f0a0f031205160204090f060c0f02120c0c06070606030c0312030e0d051c02040f080a0311 71
    0x501c2c050000c00c1c4a01c000080151203103071103802140c10441ca5504071195003820303100040c0c480517500802000703814480026031149040100300c56210750565049041000c6002c484c0c41c0e10f944900a003002e141c0d0300070b445a4003260611600d00842d441d20503180101140f60b000188903e0520514012144181c000b503810120902441034904d0502e540c0c2c001c0b44040188012008040c0f400158040d42484941ca4000a000b003000800c03100c449001001d803442041c01c04440202000308603030078000c1c8039030709500f9a1810f6689001d0704082d030101e1f045074001c01d407503004050300740c8681064034000c3e1020030000325403045030102c0a6051007410620005d90080c5803811a140500d5aa601c0d0701d4a0000c2c4107a20000e0441c0400c00ca07a80030300002c40d032100c5841902d69403418104103d94500249601090a1014031802201d000c42e007880c4c6d8510b81c0d19400d08020441943c0000130003a42c1110b0b401c2542040041409a0a0710030b8400130100000106585d0081c0e1900410091a01616041e01d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 838095890 1250 838094640 838094651
    0xc06140105130b0a0f0e01033e06091906030c05030c0421060507020706121e020a030603020d05010b010f0f1704080f0a02060421020a082b0b010f03 65
    0x25564810072440920048500450081001c3c2d0000301858030703a40c0041ea008143c6035001030000369030920035040300d018142441710303214044003800c882e408901e20324400750340b0402010078034800c9011202c903071034029010074184418000802c03403100c807004c2d00d80550700391a9002c001555140c09000e0142c012407a049045042c1040102140d01950150040c9060a00c21041840e60380c1c0751841d441503000301e0203000d0740c10240c401a458102c540a07940000d03100c940d4680c11514a03024507404a04035640400c4a405a00301d0b0600a41002d280107040640300e000010159030303540c0444402c00d0291000250001410002500b1061024800d806200c80b05c0000ea001503001020001700c14070f4600980c0c219543d40c607001c0e4891260040705001c1c9080803911400043c0e0024189100d039106480d526110000e00c0c510600405000a45000617030040310100300084c40d10010740b80ca502100040145400d2a604819104043c140601e00c403c0c0c2c0c520340443c2542c4e0203000315200d07115508003000f9 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 838097140 1250 838095890 838095899
    0x20306090c010e0402160b101409090a060f0b030a0524010506190309300504080c010e03010e030f120a14150a030212070512070b1605120403030c061401 67
    0x2c1c10f0710079810144107680c003060505186003421001310f80c0e00e910201780c02c00c40c0740c0441406031840b12400781454a8110580381340c81c81c1010104e89000c3c900c0d03200144641c46240c2d48020281400d03030a030128082d2285480c940703130384041211a1005101c1e101a010242d04850420010070520400390f450120000c010409900c4540403035012800c03030a107240340407507084001d0f00070342120342c0300520303915000a80c81a0311010020300320711500054a1110807049030320045505000e24060110780e9001441a02007660082e50000d02003a4040c0001c9803003400c04010b01c3c1160458888041c4941c00000e0561441d5070601100b5030086900d2403c0025650701c0c40c200702c0d0351000800b840305441c40c45481c0003495540d0303182c810040d680185040c450400000d8103a0f100d501901ca02c50085042c03106204050001142c020b064880304110141803400d66690941c21100001d8107840c1800380841d40c1d10104e0141000700007860180d00c48580d003081a140030411540030724445050130034030500500 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 838098390 1250 838097140 838097147
    0x3101e020f0421020d080703020c0301091e14060103060b121603080f0c060406021e090904111302042304020a080c0f040e0405100516080105090c09040e0a020306090c01 74
    0x2403e8030380c0d200340600345540c040703550301001a410320040d50101c0000840c404016842c03004000b258403030f5080d243c04d00ca10200341400e9400e084401449804040305201200c9000705034480014081c80c1400e03120104078010701d0801200383c00070b4030031a4403641060546e003400d001858604040c407008180130b4842300c45000f80c40c0003901009107510301c0040d4107111140ca0030161290000c0c02c106403507c038100ba16118000358040784014002c1103194100c1e8050400c00c0080d00c1e900760010b4080c030307100d41d580d5a07803225111200d203043d81d210b981000290711040e8544081c002406042c0c01035030200c2042c4040202441c02c04044512580c010484c4c1c1e0500b60b480790009070010143c00b0055194003070000030360024000d54001900c1140c0d02c0b0708102c1407201c000380021580e46510402c207c40d440d40108461540308242c10440420032000041180703040c039411301e84c4c0c40380d82d0a0b000e41c02c194603040018162083e07181030110769840a48105d0540c41c040c40740a41040440000388109148600040d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 838099640 1250 838098390 838098397
    0xc0e010c080316090504140103031b02060d050402030f031813050108101508100f0f0e06040f0302070909080306030105151e060d061e0602071d0907030203101e020f 72
    0x29503c1080c0143c0f902c011900400008001d020000c00a11078021040802d040254092000358005041d03800c00d818081300c040039128903290054029841c207100d42d60000080c2c0310241c0220303054880c6a00d001c9006a00380082c0c07a1001c40d450050101da9064001c1020070280498911880e6107444010080340c440003542c440d1002072568045026041104032903040342807640240158003a80320a515080c40552002c14210704540b03040101ca4030194401c03003200c900342e1800b085a48880041404554104992928940701340b0440d24ac16440d0b1a2060943e2030086041303031401c40200a01280f807800b03002e032035030080021040d0002250b1071400a1072441480c030310660b5581d4080c0840c0c640f070320b13071008840800300030762402e2000f640d91316a550b1110780449250a1001c0135a503000c43d5485c8041440380485040740c000704071401e03012403000d02e003180281400480d0320440c1c100100684090142000305662907400007541c006102c41054a6a0002c1d80b080d50180304116101e41c0c00e030800180c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 838100890 1250 838099640 838099651
    0x18091e111201061133090102041203080c0f070605161106070c05010e0712020307120b060114070b0108061e0f0414071a07060c0206040f0b0a0f09060c0e010c0803 71
    0x342100b40490031070b9400c01a203554088280141c17003141803117031030309800c1030b403100118850525400e0351220b404608038007450003110300d442c00c05585200400c0c81408241d4100002914861906000d44074204c1654428501201c031240c994003000055803002003a40c2a56080e41405040c107c40e00c0010754607408020051800d00c66901022410f0102c04d40c807455240b082c100454404a4440101e02004001100d04901c24421f56402103580007014440d6003007d540040011050f8440d4001542c4031b108103440d8000d00f48041c001140422025941c0707074000c0444030040d02c42410071410740448074040001850310b0354422400e2040946591603026071294000440203040d4020415540c14241c0f281e01c1410401a0844010000c85c00d0200030b258040c41100100085041030b20305030707102c150071a070242146107031084100c0803e1a20789031aa210007800c0e000540d08000020320412104400740c1659800c1c0c0d2400c6079000c8582150b51610119000d081c80e4070540c035966a10826031000810703 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 838102140 1250 838100890 838100897
    0x603060a021b0f0105150d0515040206070503030a141006090302090702011d030a02011b020d0c03020309030a0807050c04021204030c0609020a0b0304030206010911070318091e11120106 81
    0x50911031003469106041106010b00c0981d40d0203100d041000d4081c041c252418050322840014891072442d11281c0303007410301d901502600ba420400c1301c006e2800d0780000c200780d0b0000e0302004403000203801440158800c0e003140d40c0000d4001014000c042a1204c02004424010f1508105010503600110321a04507903044603c030a990b551420224013520255500080007056000d80d41218400480038080018290b4001c1012a401c820800d118612000c04880507820603598403401d144100c55208601c0d0090044a1070100d900340428603f002084056031040f030301241e40010020107219043c01c0002c2180e0540c20f12040819009107a040584024240245070700e00e50b04129441c0c00500724190001e1200030085d0f66603031020541e0f0700803a41200107000b0f0b440046030000ca41d110384030700c8060031180039003091255641030350841100c9103038032401451007500050301783e8039000303c0310540100459802203242101c084d03803d4501c2150f41c0c21191500b840780c4000c0121030300646044a25519 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 838103390 1250 838102140 838102147
    0x20a08030a06050402030405060106020c04050f0f181903030b04060521190807030e09011a0a2d020708030702301203011502060610050f040902040303020a020a0e0603060a02 76
    0x51141c01444142d10450b0080d002000300014802c003c10814100e901d0741c0c00352908541c0c035000304801c658040325140c40070302d5100c0104514031218250340798041d401c8100d410b503420340d4122503032034103c0403d41011080130f400018020194940034114990300140c2d01403255905001c0010341c6c1a0031078240c90018101000d808402d10720810084400c1c42d407903000d021142c88a41400c01c80c0d43c1c00320704250007151002c00e00060f203043c8030800030304032030410030441c801010f4603164213000c1e8092510001081601c8070520084101100709a0f41400f49101c25101e41762000d8000c1e0800c00c02e0742c0401040d400510046c00541c40d00f40014594112203c00305004503140f29100f548112015141c49052064243c8484406131000065058a2000350410030150500c401240c1c3ca00007110751580100d41d101c0a00c08143c002d4000c1c00d0910800715405051a49640c0a8070890300907900135401607002c05410740550a00007410000b40420186001c0346180840110781e40700d6024059848481c0e000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 838104640 1250 838103390 838103401
    0x131b030504050705060705030412050106031e0b010b090a05041505031c02030a0e0112020310241b031707051c0207020d0b0903090d11150a171b04060203030906060303040501020a0803 80
    0x14000c440251103240032b0300d6131b90000d5092460080c0f045000c11600c000d1a8503282c844a80111000d22803190701028141d44d46e07007490692400d079080064820380040c0c801d54003044035902c80c080c5060405003a81d00c021701030700d400c041515001c40019200ca01c1c0f00c4900d07034664802d901004807a05800f26043c2041d4947c81a00102c60ba4600c0b510b90708121032010060020000b0b130b520f000c07801c603072020468607564190004030344e1410603490300101c081000001d80607030b091030b04c04020003614000d06080740c401c10280e048a80000044940600007007000134105802d0034220140079180307144070750850800e400d503400f1805034860301002800103075000000600300e10041007221001c4038050b040200d0202c0c0741c030b8920118000b003140b962042103072000c001246034180065130308525051fa1101d070798001c4034031400400785010b0300d001c0c20b290082204200100d0420010030060039182d000315624540100c072030303062000181805100e03070070070041001030b680d0025070030b03c025400c03808141c0c1d41d46070b0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 838105890 1250 838104640 838104643
    0x3030c0807060204081006151b14070810240b071b1202010e04020703090b0c03040b070b0411031c030b0325030201120b10120902131b030504050705060705 68
    0xc40c507004084500009020522100124107503640d41d400c00001d006994031840000244000b400d40f1800085107686040c08841e894600021124010120031400e80c004d0041d132420700c034868010002c0c2c0d520510584104800b01c2c4500e0003103149441e062940610100d255811030382c114414000c00035400700c0e0b510144503403044801c60361410721101008180da61005110904803420301617001c65009441c0b6180340c02c2030f000310760000303034545d8404000c1400c240c0d0a26a5030800400f1002e1448140004034250651400a181e6240288003150383c910300f03882c1043c0c130300c02106805402a001a07012801c0d1403401c00141e4002402820040746840810b000b02e8900041107003a071902003501c0d04214035004503540d1f5501944c1c000c2c0d0354444a5441039082c4010340c4c070005841c5130009400e03d00e408850307106a0141c045010307400e4011410b114103400003800755041c00800141e02d542d40004981c042407201da141a62009400e060090746403648881d515007105100c0c00e030141c0383c00500034007081030 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 838107140 1250 838105890 838105897
    0x70201030f1a01093014060708150102010b0117090c03120a031103070f03020a210605010e030115031101051308030310120b0a15050d0812060d0b0103030c08 69
    0x256075030410105180d41d0007900003000603155640400d00300c039004540080c0d0329810040c0e2401a81000082c056220894494a0a001c3c07040d140035000440281803c04244061b6000e80c12030b69500c0b44609040410001d45071a1001e06070540e85000d9001856980100000050b40290034000415a4400010504281c50b602843d5454015142030703080d040c001c2000342404070380740d039400c00c00030482d03450840711480141c544102084101d1041c1030300500c40d40003805461028501981c0c1e090482c2021881e2071203a00750401350769224038050080d56030050b596884034600718024418000c54032090b4521120b2800058036622030110402510790296007201e1002000300c01007502240c1d20300d9011740320703001030b07415803052120308070300044007408642d0490105400101500040d243d2081d02c0d8000d208614054400d6482d1443c005940e541d45261a010075015032100b560310b80d0f4002c0703101c04181009001520038041004d40401044030342c440301381540d60505143c0070078805410b00c0501c901 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 838108390 1250 838107140 838107161
    0x9100902040602030309010c030513060c12050a02090301050c030c07110604120b0103060606050703122c0d230a05070602090d140607110c01120e070b031b030f01030807020103 77
    0x1030000500040e1283c2c0080154403c1c080d0308000c1251f41e2820a04805842c0b0a4a0302c041b01c100039807401010540036030005250890a00b404082070a000100f2015110101e46002c00260b0100c0c1646403400d080c0111680508540034007403451400c400b506403140a42c04014103110300c96006808a901c81d002290041c0160380901411a00c2c0c81c94200d00002c42408107e032600e0612200141701c901a806a404099140c2ca034040c49100e1f1600000c020102d8200d0740356a40180d24240042c07181d0013008450038840350000c0c1090309804072020f481412590340b1060640c04140030b040719121401b0543d00d003610a45049944d900b81801c20101902034403948603440722004450108019103501290390304c80b511010741d03140307076913180040e90105088058200690003541059186600c076500d52680301c1d400090010b00080341d4800145040c030960000d0b0b030914000428420701507540000460b80e154444841423075071030f049900303071070b00c21040c40010040f640200340310f41103a0007900001f0000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 838109640 1250 838108390 838108409
    0xc0a1404030828051c020a03091211010c09051f020a0b100608090102132601050a0b0a08030703050a0c021305090604060507051213211101110909060910 67
    0x100c109020345060304030480c154000f030004500c010035459001e0700907981d011445600145820700c998042e10041d50140300b00104141d6103141c0000040e000d0520300a82d4101e503603c1d0241c41401c0c804190071035001c0b080e1101844070a40e130800071a0f41741c1d020104000342e00048000201d400060a074a0040b1426009142c03d080c0400c02c11090b4481c21164121165070b5a003d4040c2c841e04141c900702e21170182141031040105100384a000950f03079050314090030a001e02d003000c8045440c1182140c0041e510100e1080d00d0710a100f000385482c40c5800091704111000c1c44c904000c595001e04140b00d500b2600042c0880204c00005569a61525415074491180c0a12403882c0460140b80c81ea501154211000d07858007010900c8940710740207680d10507100c0d2a10f200f1039100c0c11b4040c50f002d500e00d4021609914a40300d100e0078101270f58030141064000d601c0d0807000058038400d003801c0d241e459200020308001480030414aa1702c485c3c00c5600300c0402d40d01c0303080540fa0242d465008050740d40003104003 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 838110890 1250 838109640 838109647
    0x110f0f0c0706050904050a0501060c0b06030f0a060b09090303011d060409081b0d0e03121b0a0c062d05091302030112061805060417070b070504060807080c0a14040308 73
    0xb01c0703030040c000306034800007100c08000c50b9803030110a0045900a0080c40c00141d0310040c401300003515200d2060308a1720040866480100d004041450300b43c06010448425444961515441c1885804c09800a962802440c2590f06050b4000c0f00302d6030b0300f45080102d160070f502050003030319681d000903c1e564204e0003180d900c0d03844a2444103020403030802c20003103109880301c9551151150302020079038200100544030741d107120064007525030054000c14403200d50140200c003100381c003007042c844d4891154a8486c0164644580034040c16108124034a0980c02c482071010304d1070035110341c04004103050600d6a203698550b40401c01d15000b903002c20a80c2440000080b0f000a0038000c2d601041d0310845080c031040c40600305101c00e122500d80000c099500443c0450005800006400300e40540101101d040807065214021031101c00c2c0c80132000f1070400101400920350040c92190b01c401107003404103a500305110788010358481c041e0039004000c60024411000000c0c0401c460085401642c59901d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 838112140 1250 838110890 838110899
    0xe16080d082517060301051b09010306091a090109021305043b0f031806030417121503030a02060402060c120c01020903071e0b0318060901050613110f0f0c07 69
    0x11001c070010303409080f600c518000503007519050141c188140841c03d1441d82008404016070480d0b000201d501b0b050584031030300441d40404510a035949401418100b20102c2100340c180001201c060b0400e59029004010f0a005403140d494484100c0301d00351800581c540c40070740010118034003083c00e40301101e0000c0302000d910041c9440c0070039126000e001d580001400590a036507a102d008100310220100030072071101d604c0e220000c0d560050183c1c0c840386202c50142c1000003203920902c0070343e0b145003404050200807000042e500241e540160025850110704900c0030756100c0004000074482c44000445c021884010f0181c8401016480c3e106500c98ad0041c021602079080b041059002c0d10030440c0000300e0101c4030301c0e0094100c80425022594a0506e800b02d580d070340c4010720300b04240180c1d640301007000340c0410406118040010000440f4240901080307503048080210454490030314148000c611203402c00c540d00003003541000c42d0b41e803090b044002c41d940114140e21410b4081c1031400107 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 838113390 1250 838112140 838112147
    0x100206040501060f050d1b08030d1a06030105061204060b1009080c03071d04020102010212090109062a050c2506080f10050d061e0e16080d0825 63
    0x50003680320388028001d55803220540c1d042e03500c152050036403101e0142414400310b041c4410a00092401110000c40d4648a80e04146154400f400405109649140e154051041540124942c440c111011451035146c5000200f4a000b60b0843e0040ca94034400400c0401015610602039070b00d015100950200043d0005080349100b441440340d5801f4007022074003d850040b51010544411417101c40c90000c5041e00301e10003850081040303066641c04c210f00003508900124843c81a40e06c603002203030160840c9840030aa44080c8050700100c00e44210b0000c541401c00b6006015000074a003540c1c80b0314000230706501c0c200e1840d0b14070000f1034400c0c803440e000e11034115a28081d00c00c0c0b6100c00300c1a03140d03d1010b0080072421180c3e01d170518440d40b01032119103040450060703158090354001ca07400310000c0c1c250070035407800a01c0e036150aa0360400c4001c0e403c41808004101031800d801400e6861601c003016841d1400071480300304000d08607000440c410307402842c01d8200a4100600d03d00c2040921019 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 838114640 1250 838113390 838113403
    0x106051215130f0b04030905030709020405011206050307120201180b09011116050d060e0d090503150c0301090228120e0c10050f09042c0a170d0207021002 68
    0x1c07034218851000076524612401036208540d0340300882120308203554a13940501d013030283c001c4082100d40000043c3c0390780c00700001c2c1c001d000408001a5103074505000581102078642c1d010141605001080040780e501040503000c8030300301980340041010601c0101e074480c407119581c500000c01e600c40802d01c4a11240075029445007031700c507900b12907001c01c107a5640b104003144080344407452600510403400c103101c0c1ba131101d91150102207015102140f95a0600d510641c03100001036101c0020415442d0801c801107121b010403e49200754180b07004040e01500c01400380c4914103400040b03040700c01480c3c1104004940380980a0702150981d904002c00c2240c0c08e401c0088014185012858110300108480f078034024000c11411016510102c252800c4e00420b00d401d202c3c1070300380000f60312500c1c0e6000d40114031031082140461026012400d0310340d00158000c1e42119030007807031040c0002d440210845204100c9100031512020000c030000040c1c03195110094104800f562404061900015071 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 838115890 1250 838114640 838114663
    0x3011109030c0109180b0103020706050403020120042904031e06050c1c090809030714150901080103140a1205092b02120f24011a0909070201060512 65
    0xd5814482200b00111005042801810320107400003040001180c00307940011000401814003604107402034442d841101c0003140c00790050303511307255000815480c205010381c0c906200400035080909040e0940c0741c550240e46441002404071080900e101c00c450305a40c000e6a001000c039841110030144a400c61010540c1103a1040c14503021170303d5600110151856280340c0800c880c151700301c84a0b524040c02c00f161054851072820042d01b102c5071418480740010b002b03408214402d0722800360600c6441070104144c412070420600914030182e91054043c1d044a800c000e281c06a0351860035907500300901c50134020404c0c4a20f003504401560407002402411070101c840801c2141c540b2600e68070204100002e41701071210101c81401450503108054030581c01404032110100702c1940d4038601024041c0c0c550082601621140404000252640c00b43c180039800c00c003802c2c15a40e01042a0144031222841000400000f400c25071003507112500800004090340200c141c900c030b060780c946130951903 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 838117140 1250 838115890 838115893
    0x7261204081620030c060703050d09020a08010207050c040e1906110d060302100801083307020c0307080705151b0d0921020d06151805070908160e150301110903 70
    0x3c00e0078924010901034542d50000d0721180c500440c654048030941e02c03400410440301d07a41e03104200540c541414250150101c4000140e846143d8280b0b14a06210014994421130800c5440d0304842002b054a882000c100c84c2c00510300700031480c0440c00790121003012081d10102007191040307000e643d086001102d000762840b03801500c8841d412a201c80c024062078509070700002c1078090303141841c0d0250401c0751080b985128130fa080c45441000d18203058844e1070050344981180c80f803610b4188801c40007880140c00030181c4500d0a0041140d5034001003042505000201d00d01100e5031030300501c0e01107154400292030f040e0200240150854920780103040d84e045a40c00012000104130440e00e4400c0d80040402d00c091103590340b61000361101e544250003860a50f0300000b80f00411481d0f12540d1010540007003028502614000c2c1003407800e0f880015203a0081d140044000f00e00c4081d402640d2003405014040e41d00c0900c82ca103204025030f104c60305903280c1010301c02c642d0040c00140400070740c12030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 838118390 1250 838117140 838117193
    0x100519030c0e03062a07060603050321010e06040b01030b040504320613031e030e1b01120c110313080c040603030215041b030503072612040816 63
    0x6050b51000111a0b060581070305425040042040106401c1c00075402c81545e49014007641c1c501c1c0546e109136104a42ea64004500c2014181c0440c0b000034541e0880c6041c1c0410b985400850013855102a1009002c1d964460003000300764800e0b00005000d0320081c02c207110600b45446e02c40211018402244404045a02c1031400790b01000215207a00c0d64050003040c3c0398581041c07084200410210481c28042c060144800a01c0c101204d210882d00c48d46000a0218501084a00b4200480d411141590181c0c0c070132140741c1e03006584070702201c001000004040016440503203080c19101070b03820079844041281150440c500c2c010105a41c180310035113581002003c248400d440c000e0100601680002c00101100403980b8203499100d80030f100443c021400d07410320f01d090b0f10200d4005903200d030400209101408101c64031315180d19032054400040e01012801820540202030076191004905c4000c41c091001081c00e0b00c08020505001c880e85500390b10340f162852441c0056101c2450100 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 838119640 1250 838118390 838118417
    0x6073924050307020703020f030304240315030c03030c0f080f130f060906111f0b0102010b18061512070206070f080112300305060f120c100519030c 65
    0x2072003924000d00050b00100038030b0b819a800c104442d548020388907014401400001841d40b1004480c094001c2e0b501c0c6040c013000e048940003429180700b0103c42200ba403c0c0d180410008403604038940407243c1510300700420481d145880040c000c0108009064480c001c560b03401c0000000c0e000b041c0c10103c0e0341d00322905907690340c40c0e07412141e03c51090ba0302064800a081100c030303010f06050445840000140d0b0200c005600508a44e96047c0302c00803d900d82c0c2c2c3d0310041e80d80d6024070071580c0401c0c0803640840324040421841e408814002c203924001c0c20180c0d8551414410074003614000c0c2083d0b5416410f518010100942d00e00301150040c0010307607a40e54000c40b1900541c3c90034181c0b80e400e41030030bc44042544440340300041480b07010009180303480780c0305041c80da54140d2000e510525500031400d42449400c201c25850115806407160780400d402400040000a02640e03020040e540ca050440034000c0541d014062918010541c00580f941c10355002c0c1e00d580325014140c1540c456400c3c1c0f040c1e2 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 838120890 1250 838119640 838119647
    0x15020d0b1e12060f0f1f0305070e0903130b0c03211b070506160e030609010e06070912061835191d0307090e010b06073924 54
    0x6443c40204040003a01046034003030442c440c1540035645680c6454078500c1405661801b0840d540f003510303150012403091220040b003100c0141c1040b4000300940c1451894140d098265801e885054160400042c8204110f01c00303000741c0e800c0d500103900b01038940c030403082203580c0610304803032542680600e4a800c940040e048000e5030011038005d001050166680302d0b110165100074001d0f201030103103840c43c613010365408010703462003484000c0c004243d0724901c0110b01d140c40c00c0a0001c201b4890742c45010300160a020200200d8207800c00408120010000542d5807601160344005c0c059004c521603030513640944183c011440b544001361588400074a8020100c18000c40072510403080103085880005031140f48000f0020301000d180d011214480307030002c4c0c901030081d8030003c0300f25125080d0208a0000b13200380c0c0c1070541c0a8850b5868601035a440c0014000d500301c0d480e41c24480810701509009001e00c9407610205400606208180c8070041c80c40b62080ca0750745420703079880144003400100c3c070 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 838122140 1250 838120890 838120903
    0x90106080f100b0a0e010803130905091f020405040e0a1509080409050601020c1e152a01200c2401050d08090d0b091915020d0b1e12 58
    0x9000701402c1110782040101015007100304145510000c01074010030f03807102104000e4001c03c48800115a0b4001912060079000e81903032190f61043d19141c1004410280490030030b0328038807003000081c04445100960002030140d9000759400c81e250221900c0300d041300141c5c01c40920b0180703d08684508000030001c0c107a07885050000c00c2d07503070b06010801c4880c915811142d00007a050064945001444012903c042940b03614000e1800040a94188a0628013181a8240c40d030310755192030800c50487d00c007100818040181610119001c1180c254070b807e500c58a400c440c41c241800c1c4140c2042c8295050b50003d0300144640e008903441000e0b24080d0140c4000c0402c0c6241c503d12940c1c1c40d000402c20032024100d0141c038910000c2203450100d907125040d503140d4a04c200300c0c4411500f8250185450520002c0013814450207010406000c112030800844205409e4000540c2d43c1e0060f010000140c4a401c0007581c00c40c1b40c0074400d401c580f03280f8529a000150a9a0303040b5462181c0e0070150740d81d00c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 838123390 1250 838122140 838122163
    0x3020f060c180609010201090203120405100306080307021908101b0c0c032901030b0103060509031804051015020c1302130b22060c03031404021e1504080609010608 72
    0x802c442e07a45601401e0102c0502001081400001031025890f008a400c01c034100c11844c2c0f4034100001e090001e484e050b00d0b8424003140d1031070200003542c1400842c2d41e8074854120041e101e401106031000d00b01c0408c0c51044007910855056403460080d0791402e0700500007000a040660b44d0503801031248621500039a05182c0d04000714030340d244d242da252146c0300f19031038019913120a04004410549a4500c3c030300c0f80218030506000100e5171550401008640c0d01a00d80c2105400410440d4040001c4c2c8104485445044a00040c1501c0b55410001c04900e0380d800f5154203920070740040c800c25004181231291b210f06441c828141001c800071072080344641c0084c00c601045803901031001605d000060907059948080174803140d800b50003003c0c100c0d2980e511040c0061040e00c00e502c101981402085401070040044001c00d08141d4005408001c0b042d09680401070107100c030304100d907a40305503155103100440c600c940e80c94540c460780c0c0c1c1701c010032115010741c0c1d800c00d9400200f2000c005104418007 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 838124640 1250 838123390 838123417
    0x180506041229430e270c0424020c09150a08070b07080d0213080616050427090b0702010e07290a02070e01060306180c021002090a0305060403020f060c 66
    0x1281048604243c400000000c101085141ca100f41c5454850801201c190b840c043e03a5a54050144803600722402c4000b84912900d03001440104964150061030700d0381c8050131194240314000c428004c918052206008551100c62070080c04a04640280c09003114481914400305260310784d4402507680c0128801c5c0f00c84406c04000740313030104040e00c000d080c848900150141c41c000002d0b07206200d09131039411203500d5030030040500c00410b02c040466502100c130b80c204603041501d421451104054a420300f4079041c0d4800100080840c403c0e801405a107502480000c3c0a00785104002d00900b150100c030841031041c420080345002c2e0851003110b14040703400c0c04908028040005600c180c000400200035845001000320b19440d814144d540030b00b40c1a0703000194a441e1002103004001c40009400d04079240c90b0341d40741540d6002c241c0c01001c0320820405665150090003103a01420644d0024080b0300681041c0f02c02c25602007042d090403075000080314030302d40340d111840e40284100310211400 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 838125890 1250 838124640 838124731
    0xb2103030c0706091209060f0e060702040e10090602031911030a0c1704200f010c03050901050403080705010b01020607051204020d1a070f180506041229 67
    0x40c00500502c0304520444021443c402079a56180c441c2e08103048000200e42d0404e428403809500488000700b400c058500221030f51014804900383e4030a1101c040c1c0107645030580c803002c5100402204a62060401d0200000340e80780c00d140c402500700340d41d0520682c542c510707070400d4020070780910100300c0400e0910030f1450b200c0a07822002030013102c070390205102210300d1403424052480d280921603406200c480c90070780700d420b41d1b8a44006800039841c1c4500340d400d81101069038420000d03600c1982c98204070f652500400010303551802141c0c0010140780c0000b40080800c0019088182d0010084c1c00f26440d5864030203007940c89001d64110074040d25003482c009000361807e41000039950b801386221214000e681d0b044581400d20485105c0c012070761071042c0091155100b52007049208030352500345211410030000681070312891141080410303580b03015100703014064000c2e401c0c0c014003c0305003145011710380d090700c81580b08030790030300f0b010503102900804401c900c0b40a40c05140064401480c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 838127140 1250 838125890 838125901
    0x14030d050f09010903051c0201060e0f0a1e110d06090204080a0b070509040c080f090d12050915040b01031a0705070807050a0c06180b0415110313090b210303 69
    0x5882c1c200340b00250401103001030020200e8001d0003030240360614208a034403805001d0ba4040d0039030700c40c1d42c08149600004420400c026030041103d5400085a0402040c2d80e003242c626205403010110502d8200740c0b80558280c46610803600038110076000040030300500303075210711540c00c034002c0344100340c100c1e001841e0800010719002465030307000007241081404c0c52150408907044506005003407000c124250240240007a05c3c04036079602129110082020900142d001006c1000c0c444e100c16035181c4800c081003154006100003512449040300c800b80301e00e442e0900d10b214030700c2840305588000407500003119501280001030301c181140d4440c107161400c00d0703440024543c8030b10020381e15070084540200016181603d810010181a40c80e0070042144d4480b40c0018410341e4040c0042080030413080040100240b500c0301c83c050170341080308031040c41061142c214450000170750307490701c203e01c804030305242d80740c2c41106114810303910315002140c095652517410501c1030b40f1000541c002d01c0040c1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 838128390 1250 838127140 838127167
    0x190905060313170706020d09020112050610140d0e03191b08030703020909010306020301140d050c061b030d0c120b010c260c01050708060307031e170307020714030d05 73
    0x5000068102ea0f614280950f2582c0c800c81e00503801c1c815417581c41c0c0224105569020800b02020f91220108101c9828600300080e03054100b0501e4009100c14003003043e41c500d06110546020042b0084184603007907121408640780d03072054000030507803040003070303044c0d04c03a8820054000850040080503100e50382a403a81c2100d50401810320b0101b6400704101c0d00291108a0120700840c1308850168580d410a08000809484000e403030b40100321201417103010400002c1e084210040642d81c0c40d594243e01e038240c00f88040398441c17140c400d101c005a5180ca5003500d0b4031881c0c100c0c02a41d902d08580003280383c05819120412840c900242c960a10071000c1072008103801103140d80d0b401d000c50528051070a110464100002903441070b5920010084841e030440207031688444101d002c3c000c4141955501c0000148080b10704580c001c000e4030000c20070851100302c1d0f0010022401d12500c6c0c0c40c01000095491400c7c0c050025902241118040746042c002443c030403030100780c0c980381c1c1003404d010b02c81d2 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 838129496 1106 838128390 838128413
    0x301050601050f0915090901060c12031b110304080a031d191a07021c15050105010207050f0613061205090c060f160503190905060313 59
    0x11030701c10f03015070110380110004480c20442d40c28a02664003150082d03400c103903040200c020000c07035000d40109042d00c0851113044004d0700f070105100e08509540b08400c804ca820841440401086400b40350001c4d05040c080c03044074205542d8454041c03030a5005901540840e000c40b070780300c12411607030702550f03041d00e000d96851001d85070744003134400b5105041c4584258400d012108102201030b850880d541150020001e0002e0b20f001509030042814503201124035640c0ea800304403d0441e10300600b412100140c000e803000700c0c41c00060054020641441c560701841c04c00a203291002d003101c441d170241ca41565900e06a803150a520f80072120040c240f4041c0b580711300300005213565801e088464111100380c003e615070041c403510441c980c0078030800030141d01010840c081c0419940d002000c1d50a02991800c1c0300c6a611400d00800d4842900c083c2c10300c0c1c0410103008085412020b40 = true := by decide +kernel

theorem cover : BRFrame.Cov 837949640 838129496 := by
  have h0 := BRFrame.cov_init 837949640
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837949640 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 837949640 ≤ n) (h2 : n < 838129496) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
