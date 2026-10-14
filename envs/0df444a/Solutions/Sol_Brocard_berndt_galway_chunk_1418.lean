-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1418
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:53:29.222057+00:00
-- url     : https://prove2.me/submissions/cdd9dcab-6717-4909-961f-89521ed9742e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 254856115 ≤ n < 255035971 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 254857365 1250 254856115 254856127
    0x240a12050316050d0f1b110319050d020c030d020d0e04110a030516030911040209190f0303080f190507020f0703051525050702010c0204060e0f01080102040605040b 72
    0x10060082c0c49480b00c48186200041c1d840c0c0c6091a12101e03c03044401c0441c5166080800c124072541a00050720621030b50204500b490351215802c64101090740d80e807500c01c101300304600e0811a00c0c030799002880f540c000d007418144844064181602451054080d40c0003081511080e0381c0041c2040c095152030070f0242c10050b00c4000303d40601120390003501e00e40000a10013240642c542c0c011032264140788000700c4643c1c001002181a50905600030342411030070400001c0d00d01d800d034010715042200a01c8001c06000c5200c180307031110f2459100b0300405102c8581007041c940c0007042d456029440c5148054640380c0500d64090900310411403550880e82d0b800040c088078001c02003560340e501030f2011100c0c21a0359103025030f038800010360350f0b00d54049220003140c00b000c1e003018080510700481c0c0b8900c1c042c4a0b43c1b141207a0a41007000c080e8100142000040c0143c0c07264840d24000d88546085111286092101c0b007d03400010780c00141a40c0c8100700400c03c0b10344c0003056505558900c0c28039540c840e = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 254858615 1250 254857365 254857373
    0x70519020415030302030a080f2715040f06050c030618061513061101060312141908060301150317070305040b0d05190c0c02010e04020c0f06240a12 65
    0x400003150000092500c030b4404018540c0000181100340c420b40d680005a9950320a0b2150154003507a0400c2800710040c440090140003050b24408104188129028840c413503401d200c0340c0d0403d0350107a9107007200c19042818000d40b40141c03540f00d890110002d24500b403c40c046054101c0000401d070030b001c000b5020800b01c0e07070361a119545600a0786011620f801e1001030030180342c1c0a520076040803407049002d00d048084180a4003046032f81000d1440302c000d0303e010058400f0000e00b208070105c800f04021400011226044854111074a6a81c45140f842c1140615003111801042106200c641c005c0030000035031540c400c10100c0d041c40e1402a2598000c2c501034456001d0381c1c101c21301200c0040b581051050017a0301a52040a40c0c812804002865192030021107501c0c069000018440c0c003065005035015400307400440401400c01498a000e88a600c0e0a1407a02c6032200340700d402903801c0c8007202d0030103040100125408540100340e1400300000598545032803080c4080c008002010200740 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 254859865 1250 254858615 254858621
    0x2040b060c06040501020a022103040308100b0705010203160507050703032118030f0f020705090c120703051f050f2808060405060a0b091b090301060303090305010f020705190204 78
    0x80724100007241d10509103840c146010350032000e215801482002d071302010f1101034038024011000d41403201c0f4555103a6483c2107805a00c0100007010010a0703820001e00c3e0500c00b001000d01a01840c00180c03217003091240d031103d640b1110704031410803c1c03d2150b200498004100c07030040b00c0d03040c1020050200541040c9015026250f1041211454504400c21040380c512036039190364480e584280e0012003211040d81c4440c0e5000880005038040d44061045060071803c441c0c0000c81004a181444aa40c00c21303009054100e40810009445a00b40450030421a0070143d0410034104d00c0c05e07203181004013041e4010191032001d1320800e0720780104800982c0c5070700b4013110203c2030802070f41502d0700d9100c82561000140c0301114103100700e00c001031400c08213218503203410500404403e2a506c8444028003451068403040720120020002c200881c0c0d03003482030780003c612039141e81c2c00c00d91450a086007111030f80700c0034080003801040042e00007030b0003040d808128143c0d25203280582c0b5842c0045401 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 254861115 1250 254859865 254859877
    0x1305060306130b370504110a1803060203070e040c030608030d09080f03090312060603071b020406170d0207120b0601081905071205100501050409091e0318080c0d02040b06 75
    0x4211950040400035407501070b00030100602c4051126204c6603500180400c54412900c402c110000c1844030150b1240704901c4500407240d0310032040c0d40c184d140d0b11180100ea0080c0d403c10040340000c0c080b6985400d01307000d1041400d05500302080a98602000c290310707803182c0b46c2035048040d6251035a0003003281400c16102d418543c10030043d224601380c0c0d1000d9403a4802d125581c81200d004c0001116454000d040b40d100744190343e14041442640246180d0f48621894126441616010007140c1c582d0160650304004030840c0c010520b400503100042d0804260703400c5080301e091488408400303d0b82c898a11078002d007080c60074982c550384804510f08040c04610b10355241905100070301114580c803c02d02211070303014040c1048941c96107940d07020000300c103104040c041402480304100300b41b101d45c0990742c61802003880c800030b0103800420340341848100c441103022481c0d124064620114070750302a000b501403280240381840705a0000307004c01002010003407250f038880740303100c030b09850310819101 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 254862365 1250 254861115 254861149
    0xb130b0117032a280209130516150305150d030207090c05030a0615170a021615110c1c17070824061603020a080f1305060306130b 57
    0xb001c0c14610301c040c400e05410014500451080e071125000740000c40103c080c1c2060045100b00b40403007603a00380500703104c0080c2000d18603035041030400041071052028051a11844014200090602d102b00e00b0300d0442130003080c2003602d008204809403016848015038141c2c1145d1204103640540740c120b2900100b0781101100900b403c20a101c016000405140a0900c07210180031058641c81c03450403a44e503289040c0e000a03d08610380440071008184d1a80240d0410790140c60031121102c803241114081c0f4084405480c8141c4210318a44a8480d0500c1104050241450801079a690070f0f42c4a8001e1004807074003a110701a000458010051004c0c104051400f2040c175180045026142d001d044030810f6121060000d0b044c001d1000002c0c52205440080c0031604106c6104c507500c0121050103412401d6210f11380380750001c10b100741c0141029001034141665180c544402020400907260310050044906000384961a0b68008648041009400700000c5a400843c0018812800420010 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 254863615 1250 254862365 254862397
    0x70e0f0906190303053a050402060f04030b04060f1b0f0302040f090c02070501022109060403060912020f060105010c02190b0d0b010201050603070b0417100203130b130b011703 77
    0xf0801d50094058581c002c422820701440454200c0307201050250000d01c83c21011a001103900082c0c8160302c515009400900300b1030034151465581040d90303005070010b0b5804e400c52070800003000503c0c0942090710051842c2030180440008040f61005054000d11052003008040c12100500c82e90540340203041e080100c0e5803c90760b42c2c40c1d00300100126403031240107025098022505500010b8140000c12120f002100181840e20841501d03030004440700740e004004100020104005000b040b0300c4a000c0c24000541520703c2a0280c40d0682e05115401903422001c01040b00341e0300140060001a01901e040800414100f1560a0700d007070b039041103120840c0494a6195020700340d000f903980020a800820054440f2010965540314a04c206040d04104201c1400280c2a00e120950326008550849800401041e90031059070401c9604082d022020000c5d0300904c1700d0383d24420741000a240c0e01d0380046446032180f00c418501400f94030000800c4030b410702c0f030320102081111040b2040500b21 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 254864865 1250 254863615 254863619
    0x2010b0402070c050f040c0f0507080c03121801090b04171605060106030c0509030606040c0c24110c100b030703020916020705060c190c120606050306070e0f090619 72
    0x40f40c000601036640a245000303100c45050a040c4110700071401c081e105c4001503190380c0d038200e42c81c0e44420011a10090144130070040a98100081c0a0001d00c0d18040700d414074149201031800d0380c40c010b1000703050307061410140100707040e0300c40360703403c40c1c0c20020a003c02040800c41c0d5801d48100900d000380a4101ca80b000306104000c16070704d050b5902c030b542c00e0116001c901c004075098011043c426602d40c2080c0c021908524055200b0300a05505040000c00d50f80741e40c850140c4460701666210240c0e4515142451400381441280c40d6402d07200560390410003c5440166121640d80d41054600d68408083c441d41e41c003000b00400441c0c4c010b0601a0a03d0702405041500d072030180820090300c200c0c08081894503211050315180a8032100800c101c078140c440d04800d4100303181c402d80e000c004021000c00c145000e00c65080003d0700808006c2aa0391825081c90301e00000204100200000380e1000f00b402d0b41d1f0f007502c1007400601100e40103a1070b2151400103401d10480d00f8029007440003c500 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 254866115 1250 254864865 254864873
    0x6020f070812060906040603020312070201091505030402100f021e0c03030a0e120c010f05181f1e050f0d060806040506040c06020607051209010e030a0c020f041109010f02010b040207 80
    0x3880344205029103400c1300b583c44038001e000984009000c0203500da0801030050040e04a0342010b4003425005240000b10240c2e9141008001e1150401e11000218000200019401c0c6068401910b2070240340000c2043c03403c1c00025182c1074480b0f4207525055103880c48a140d12010000405030b503c0050a0307035511072816102502e000c04406d04240100c078030082d800c00d1818041075020960704180c4429100d0b01031081d040701c03c0c0d03008100410306030301908220306480d210300d001030240c0304840e015000441407220020b00409045542500e07407102200c2001412a427003020f4400848489040c251128414880b240180031541c0141c0203c0c815401048103104001070114001d80c001c80c407484005071120710807a2201000c0302d0070800708404015100c0480701f115480c40d0b100150000000310792015074409829640540343c2c5400041c8050081400d6150909030418100000c803001c0103c0c0a060f0b1840415000d0040c000b070500c084080c603613503040d00070b400810310000020030456440b40140f030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 254867365 1250 254866115 254866147
    0xf09083c090d060608060c181005040b0a0302041517092d0a080304080301030b10140105160c030501061805010f1202061b1e1b190f0b030603010c091206020f0708 71
    0x1801e003e401c921404036910340c1027880e00b80428054954546151504043c220120344d406008400100360b8200000180100101c0d0090581c0b9541d44e41c0803600e81568642441c960b10241030303009180c11196144829001040d004492840c4118211400410454000381400303903400300900f03040c100100f01f104015081008505032403203012245071603200c402c01840d044210380502c04101070054ac00740d55640c002c1002d003440c0d0601c051000140c5015a940c65003c00c141e5000300da00d07a444910902801e80301c2c003d450300c0312900e160100200c1d0b142552545650740f041c40b5504014128a048009540b50720089a8a00031500125401c00103119090703a0f88541e1204a0341990280c0001d51800800204074104403072082245c282e5026480320401141c004240e82c2c140840000880000d4a60030a00d05c04008051202500380c0381e1130700341c0525007981d140904400c104a0403c409110f1506650762001d1b215400a000586400d5124140c0304180b0a003000608550000f245096507a11001 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 254868615 1250 254867365 254867377
    0x1021210080601060c020d0c171605120a020402070303020c06010611010c080606180a051305060f030712060b04110d02071a09030d0f09083c090d060608060c 69
    0x640a0384046503640e9440751650820f019203c00500c58a180d10054502441508030590140c43d10160441c2d9500c29914504d41e4100c02a0254008103a203020540d4404001c0006200c151520148010700c42e055a4480c0104a4000d100303541c0032400c4005d05100358169164158920100c41c1d0658540b900a0305070380b04641e14880c60343c00c000e1081c10051290300781da0b001d6070000c0e008034100f5002c9a00890f03d2110740811680261400100217450380c0c4041700703494511f40c04000002d01f420180e080c40b420b030b401101c5460003540140382c20400306611024081219030444800209015000c0006010381851000480206c402259000e400c64082d03005010145c8200100500298503108100150b01c088030642c680d908184801403800047d500300900041d05050b00064030b0805688148241c0c10108104419450031801c98a410380e207403c07840d000fa10030b00702980d20325031070b11464015840f481141c00c8c02040940006070030481e054018901410003003090750110310300070464407902c3c1c11807 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 254869865 1250 254868615 254868631
    0x20d050103051f02040b0405130e0717070f05010c140a0209041514010b190201063b0609060f0f031209010e04060503060408160602070302013305120a05010212 70
    0x1401441040500700c0c03084a007280d0000e06d000d41858508410841c480340d40c00340c1951503070f450b4002c840500c0014000b990160216092224846a001200e18981442a048401c4020345810203100c40c4c2c3c0c0141c00700c0b00341544024101482c94a41301c125052058144000307402c400e4401c107000810150007850b49290050078400c028610000081c05200c00003841110000c00e0100181c07514281d00100c8545030061500012584e155030f025201c4a40c015410412440340a050320080c0d44a451080407803140c66200410b8040d0808000180200501400043c800d170f0846165912580f916035004445400040c261450f403250f42580f004280d01c540c204078001050544040980d00d007610504055400280041446944666511540c4e44c488031502050313603200385403080051801c3c0000c00900e4401e60011405403000b6820801504e40c400d258010703900c2c0f900b0300c14410060301d0300880848070201d4402402c035107156821402c020401002401c00c0d400014020001a00c5045141c09010a = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 254871115 1250 254869865 254869903
    0x7060206161d060a05040e010f06021915150504150303020111130311011b050c0a0e0f19021306020109050d1e030b0102150a0c030506030106060e040906020d05010305 73
    0x452422205042200c0500a050b00c640303401d86283c1c00d00310301610840010303007421450940c0742c01e190400b000090703003e021100c00c09035003488010342c1841805035802d41c202c0c00b00d00300c00c441d50302c00c1050401c0c9030f540f04026655410518101c162219120004c00300030700100410300042580302c1d11500c0c140001e8016600700301441c4003440c10501181e00080c03e80303a04501039410741d9218401c0d650200600f50400201160302080600e8500030550183e10440c01400400c541000340b00d82501c866022040e942d000320200f00c03154180044e40340d40903010300700d41c801078601d40d4008002401341d08800d005170042e804011481c0c58055004c0300e2158002e104035040000310150031680017034201c0c000d502e144061482c000903035010b5005465450310500503100380e40ba420801c6101d940c0102d40d0401c0079906d85c0b240403091034151080f542c00401c04d400a11005043c407102404030b5003001c000500607691450400709102d416816900159225101030007656540d00b4543c1c2d48581042000c104140 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 254872365 1250 254871115 254871151
    0x5040606050c0c09011503230723031e060120030403150506030309010f110102030703020409180222060302060703021f0501050d0f03020109050601091a01050915070206070507060206 80
    0x2d00200c1040c102ca0742400d06e5021103050301ba040780078004021442001843c08613203a0400075110f060a031090038142c0e03c0b01003150703444d400c4281c0790500710802e40030b1130010014401304001c14141180012000b00f2003d202c0d450307681c01200c20410b01c00750380348066000b182e00e84a803030002c002881103030f02403010301c0c085032007998200c412102d082c2e0b94268103600401500034903501400c41800026154101184440880c076400b13826680200c0d00c0d08000303540000c06210050b640c0c0309000503044110b00d0390003070460b0b0b5404103141100c0070300e440405480301850340510001e0761700b2450185901800c210380322601440c01940d00d030700801c0c043d0300c2e034004800c80c0006614544a000d04985008103405562a40c0f6107800748550191310050b42155200d26a440c04280f017084003d00070002483c001a214584107001901030001040c040d042020812044040d40d0390846446101482101826901c5000b8030008403180310314000188180512131000030b2581c6c010807040d02c100c07100c240c6002d080e6 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 254873615 1250 254872365 254872369
    0x5040c0203041d060315070c170c0a080c0102042c060d0b04030e01030b060c0a11060f030a0c020f0f0102090108010902090306070f02010e01090b091b060316050405040606050c0c 78
    0x80070341d0240f8810700c1444081ca101c00c40d080140250050b0f0043e043c0c642d012000c00188062020446140c000309007507240407001c12a000f5580400620031406a909041c0707081002030b100d640220300074182c00000325500f50884000c1d41110003d01040101c025545004810010b00d184031444961991a54000090507428100305c14271041e6480005e4a000359107903035068441c10228199281003695030034500c1425161003005201145821001344944110b500d4000f00e00700907181e5160040d2000e00505c07028140c0c110940e9049040c514006c00d00d9142042d040f40b03052403004000c1601c0c41a0b40d40d85120b1a01235004200130070007a620306041daa211038030703402039210b40031525815500000000e1199446618030b2076001816100100d048000700072003a00307680040e001504e1505408041c810030752001c00c03807802c1100c0ca40700d00403038244140b00020401e010040c590060a0210102d81148522881c115001782c24020400c205e21a00c680c0014040c1d00040b102081c1c03232095100c2c11060b8 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 254874865 1250 254873615 254873617
    0xf0d020601081002030a110309010e010c02010c090e0603030903070e0709050607020d030804030e060d0b120c0306010302011209060513050c090c0306040b060403150507081f0303140d06030c05040c0203 88
    0x18544050040c03c040002900c01e10007503200030001d030540d550b6400701000060544001714000d0000d003001040c81c0c0035401c00c15003110320083d40031080d60300d04692002400d030845502030440d080b0b030319221000d0303940b44042410f503c2900340a90380340c00760003000b08407950309043d514020181d503601c000381b8030b854000340315507441803c202070350055200c40c40400282c8903040d8203510600c246810817000d049003002c103049803c405020003080d500c4560384102d46c00d00040d52403515420100410440c0d0740000429196101800084d04102d00031482980c0003186030003d103820f5038400410080b619064451580c8070310100d204595038003807003915504520704041c07000d00a80d030070000c1b24034540390070040000812004846d2600721500340030000110b01d64801030001e01c00040c02c089a07515040400501195001307100e042450110030300c600c4905d00810080c420b42c0d0b8942000650740000041100d4035000d160b4804c0820ba003080c0d0080200030112424404951003618107010004089a0a07038032 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 254876115 1250 254874865 254874869
    0x605070c0308090a051002090f030a0b0603010f110313031e0c0c08030a0e040c0c02040203010e01030606080f0303010b070201051b1c09050f0d141e060112021e040e0706020f0d020601 80
    0x951051075101c8404606c4d5004180301440200b894613082081c401090401c41740c41e01c20f07184c030080d007001c00c074107824280200803030101340400c100301c05c8000f1914040e460201425100078421100412020540558640c00514000141003203802c450210003c100e0109620103c400702e98901000450820002c2901e00e03003029a01c4006144444806020041c071f00030305902d04015030b100304140582c50b1480114003038244114082c3d01d66046081c94810364000f03501a0f11160304c00c4800d010f10341004411380e4155060018410b9550b4910300040300d00d0300a801000e014460742000e400e11100c0300180ca20402448c101c074907007180d06e200300c0a0f034040e000351083c25080900c201d020f80b401d00c0c00c03012082209109910485016800340700e600c1ca48103035070000d00da004021908a02890800300103041c010004c1e0310851681e02c40076408034540ca00b180e040300020304012078102e40b041d0344e21780112121106200441c1c80315aa01c0708002e507114a103503054002c5018003816003480500c0480c4141c1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 254877365 1250 254876115 254876123
    0xc0d0b01150305090a0308480703050d090606030b130201022a0121050f1f061202031306020f091f02120a020c130f0e0703020f0f010207030605070c0308090a 69
    0x205034807090f10192410340009180c0c943c221303084007101307090b10845400c1540300000c1400180c01e0415100c00452140020400540c0c1e48c101480264000b9511404540d418001d507400400e80d4041843c2950240505070401840d105641c003c201c007000100311402d40c981d000f6400ca4403007142c40c140585205a4440100d2080b210241401d0101e5000b4048180710000185400450210a82c1110203d840968084141040c0502807203600307012952001c030108500e6042450304d40c680103028118542091283d4400340c0c000c4000740c0d040242444254800d80c014806551703d40d190b0481e06156404955400e11800c02d0208003090440102c019180c0089640c006290b00c074038004250f01c55800c840c081400f1481031940c8000c080e02d403c11150807101000c2c002142c0c5862401030718047c0c0b07a00042c0200150300040303040000d640c55150101c440d0209070b40000c0601d401c0d1004034104085a0400f600060802c0c084c02003055100c0c81181840340a9518000e16803503184910380c89031907054004d0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 254878615 1250 254877365 254877373
    0x40306022b0b03190305090301180209010806010b0406030e0c03100507030f09050307170c01060b030a050108062710090b0411030a030c0b0604090f1a06040902011403090c0d0b0115030509 82
    0x136202c0c0e003840310070844d02a080c694144818403000900351100e064101034180380c803000d070b8400c504040d88418007400d5031001921066050018070166401144101420140c84a81307401501c80c0c01d01400d6900c2d480502030750a4610400c110401401003130701c100c00001d107401a500341e041c5852180b950000d50110246141009039191101410021943c0d407400407002c010042c43d8032401d109641c010f00c020980c0e83c1e26494000445012102e050b07000f80041e400c840c040003000d50002900d1103042c0e40321060591482d000d0101140340006500009064618244048040c0051030f900c091003207201740900d080c941c20b0340e801d043e01d4000c050001008260901d0300140020f01c04540a41e0010740904001800000c80d01c40520b5003000c0e401c10384905010322403410b100800c05503407581c003002c00d803400d00801080d640000c291a918035088103107a8408030106541140621410320329a85c020000105081c141c141501c00c40420321030341100f005140f80d0800d03403c0c080c2c00343c80e01c5100a40060 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 254879865 1250 254878615 254878633
    0x7030b01021c05071101031d060a14070c020d062009100c03021009080904090b040b01090b01141c09051506010e130911280b030f0714040306022b0b03 66
    0x111071100620b03c03c45d030500d501c800b4240303c2031191001036510f14090f40000c200f01d040c40006201202c1c60b21484401102030041003286c0550003001c041c2607a03a0586850741e01c42803e0030250018032040307100390b10420707641001000386a040c0001e800149811500302c003804146140585508500000c000d001d60000d16491178201d0690307104031011030051084070b161032110f10000c2d04450501d41c0450ba0b07820200c041c801031082a25185000d0300c806041040700050000020306111060000318500880c00100600c08205141980c60002070308001407001200c146080c0741c8031511032103410982c1c0340140000e007080d0701c60b00e42d695440a003c1c003200c800380d40402c4501d010300481d01064035a0b6007088400801911011401e158038540420a20f0410400ca140700202480316404415460380500074000c002076806489500440c3d0303802c201009029400480380340f40034030ba0000e40601d1000c44c89602041094941060700c1c20030804c03000c506d6030701d95104001ca4119148880d09540042c00c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 254881115 1250 254879865 254879873
    0xd0e0111010605031903200304172103010812120c22060e040608070311061b0f031306020109030c080a030b19050315090303070305040f0b07030b01021c0507 69
    0x80300c00e1219840000c01c0c0c1e0364590340030a1618140a00f81005648900d011000b410f600c1a807422408024044100413070740b2100669070b0701d014074000d0010544030480b024900380c90410901d8140d1a8900c07402c0031024251402800e550001d01c00c518203030003884c900710142c000c48411240000024003107409152241000f48546030440c00e18000c98440142c04540b201c1804682e580c001e1140d42c0d1006500d49888081c8000e8034004d07400203409511840c028000030b41402c2060f0803914060300d80c243c80d010407541e5a0a040e01e840c2039264140140c481240e08000040021b00d699000c40c42c4000c0c0c0d00da83d81104034200c92284c540a00050030b1085010000703030a0100401c04261a4170b8081781c4030f5446400995404042c0b04000c95100e803c903005c00c00c9003024070031054450b9011000703c115142c46000c1903124403004080008150340c80000904010b440b4401031ba140d80c0100c0555403510340700c2006001084c0b40c40040380544514009800c40500da00f618464845042c0e44150401c151551 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 254882365 1250 254881115 254881127
    0x30b040312090b0a0e240a0506030a08040b131401081b13230102060c12100306020d0207021207060914120d0903031b0f080304020409020a060f110d0e01 67
    0x2005825581c96030700b0100822842d80441e8000c01d00e0380700010b02c202c0041d80701d81c80c26403000140d0078002d4058400341c1d41c10768542c45070b5511400d40303407011460790b07502c40010b0b003002d00203c001001424041004584000e141c4064011b20b90203040c05080c00361a00c019480720341603011164009440b840000300d40400072072001740c0307d800d00491a0304010040e1490b100c025095006101600c296140b141c10032401354003800308013039081c0049c050a04100b104481284542c0f0100540d0101d50700215940400f040c0c944802142c1041c3c0c219290759000c0001e10103540700200503031080c0291f2200100c40ba00c081840400ca504039205e860481e1320700401802c104040d4040d06a010220f000d940014860a0085510910081c2e5a2800703542c1189401303070a182c02c00018a50100080304103100090384c801d40c4002c607035000004140c8a40c2c1d2440028003400341840000d4000300c1d1400c0018a06412012010101e8280d0b01c0304492540f0345c0132407944d1200d4262400001074080188a1805d5000f81c03 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 254883615 1250 254882365 254882387
    0x1031e0c03030e012010061e0308160602030a0e0f010e030313020d140f0708060c040911071a07090501020105150d02060d0911040605060a0e0f0105120c0a030b0307030b0403 76
    0x20402d0407166920f140c8603907a4031581803039a019034000c14400c1450ba00184122401b910142c00000d0429036894181e500071f41e0303d030000500100700040c050bd40081070000590026a11500079580c0e0300d07110b80c0c040e010300340d10f20030708040744900d80c00da2040c58010b0080c0803c1580ba0b07030042d0f0071659080c000e01d00c0d112849800b030b40c03c81c007070091031008142400e41040901202c4001480207100d9080c205180074030395071240c1d038150406400e01c510b44040c0b10440381140c1c080c80022500b80d048100c41c250a00c030f0408001e0000084001c101500221804031500c85c0780039807110300c4503c0d6560010780c01d860048030202007040c2840c03008041481d04512002c08240080c005a04052800f262402250f00007030302524681c3c540740040c006c034a8540128405448251011800c0183d80d14015103030440340d040700d41c450f0301860030440c01039202d102a29206400100c0e00c801c03e00f0030300c2c560055640486655000030b0b08000c0001043d080004116003100d5111041e1021659251001c90340e0201007 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 254884865 1250 254883615 254883617
    0x30c01080f130203010e0114010f14100909090c09060603090305090607030e030a1104110c1024140f06130303050c100e010c120c0504050103150504060e01031e0c03030e01 75
    0x42e180001c0962024860f00304407a01d00400010500750031003032901c802105038068000b01d41e103804188200c4940780320410550b58152550a40009000015610641c09400c0505954a450000710600c03000311030000031245546410030400d030f02d94400310152050b0040250208078100034205082c1403e0b0001c00035580a441c0c041400e06d000c0700042d05001d4090415181e0b4943c62440c2e41c0c3c6071030a48203141124051200c424034004111060540780e412850030b0440b5641e440c80205400280100c1041c4c1c420880350200300e07410384661810560018202560703000d030307540003648000c034104002194908a02c5080703030030915182d941c0c00c035425480403c1081842c05070804e5a5282e000d9030042405090a420012881c040c5204005005049001c401401c0c107080c003421907c41500401103a0681c0ca083ca00440e10248000c645d1301b1454040e80030703a800c240380110001c0c0e030b140303032504840c1030713a2251a40c042468544405148122192680074000007000d40c010400240220100c040900c41 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 254886115 1250 254884865 254884891
    0x30e04060803040b180405040218060a05060a03020409050a0501080705060a090b030c1801020607093005070e0903090a05010c0201030b0a060503090c060301030c171005070e0a05030c01080f 83
    0x7601da400341190441e500061000c031000c41c0d0b40300c69100d43e1180c90318601c030503942042107160540018020800286000004a50403130200e591522504040806010094911642ca80103018001c1c004c0d88640b040c0d18006103000b0114651041c940103d504035446003008040c00b6003050200710711030748224060400c2c0645a0f500150104c0c030000610f128105549405482e481800400e421300280c000349181190051000c2048564020301b080f020b40d2218018160856142000c6072100c80440c808040b807000c45c41581400c0000011b4140c082d81c0400a40782203039290001d41640e04c2c022980c0c01c6030b01008241c4140a554880c036464402c541c0145408a9403945100c0856290895a0420400590f0000800001100401c4540758880082d43c03014615031440d100c100c0c1108083c06100070206030307a00d0348800caa40070405200d000107050300c20001410b1203c3d01416415601d00400d010f00d0b101640061f1500e0080384e0103d0064040e104c03180207030750702c0c84520814200103202e81d100c400 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 254887365 1250 254886115 254886119
    0xe160327050102040f05040c200109020405040b0a0c0801151209020612060f01140412060b100c020a050105040602060f0a150f0f0f0b0f03040c030209041506080613030e0406 76
    0x480d1019032150030301a500060b9a64103101d91050180040d410050240f41000c800d5010700e588a40e040c41403d98034100d40c03441c40c0c1c241440b40e000d4030580c10080e51050600c4184410700002c004200d01440c5240410841c0f0b80040e0020b455100c824403507054414610080c0c00b0402d4014801c7c0d00e4405190580051a041c55900080c070307682090510302181c0c40c41d031040045a04054900100d654402d00340403076801050104c1c08818441d074042c24000e1205000e50404000040d0000c0110f042d00030049250599001002407043c1e403120b00903807151401c02d00018403075014400700c07800d860103503000c0e0072140c0d0741e102d02c0b840b882d8010381000c080320394480580c03204540c03510002001e032010009a05110380b07050002d04200c14140c000144400482c1810050740380b4040465030b134a50000201c68695880c0d0900025001c410b6002030b4020035a1402c010401040c000580c1d06140e440d501000f10710744a8081559030b660440d5100085000082c859005c24000c0342456800d101c000d0005c00c401d5 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 254888615 1250 254887365 254887421
    0x60f0c0302121612020613140a08040b0a02010b0f09040b041103030409060609081615180b0c0f0a170d020f04081f020909041104330e1603 61
    0xa80100102443d0301c041140410420401000d0110399070300d2031009001c00d0500c5c44000e00301480c1500c000340941d10182c0e0141c040a4240001d030851500284642c2d1078550b40c020060566004100c03d9005510b400784900d0146401801c81c2e21219010b050324015075a0390742d94607058140903100b59004030311000c1c5c0361000c2d07804200402c05001c000c0030205403146801c1000c1c0c9615819003001155410500c05944003c650300c0404045907001c0212408007011441c06903003000c031703c801030008000f640350045042e54081d001040012503400840e6042c6018405058807070101c0d0000a203c0158020191a2950201c0c0074040b54150f0020040c40e101401e51071141c164029480035070250040c021610b180070b4204190407221070a100103625012459002400d105e20041c0700030840c0746804503660568032a80c0c00315640da200030039000305411910b111003911400e110510644201040000f04811280e8407501e8040c2054600400c1207081c1d84600707034090103095400002003442e4a612140304 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 254889865 1250 254888615 254888617
    0xa0210050c0d23070e0a031406041104150e09010e010e0607020606180a15080d030f060b0c060103080c0f0a0308060102010c05030610030e1002280306060f0c030212 72
    0x3461850007440c0d030302c9801d86000c0090741c0100301d0100c0c06407a203d04520045242e110650742c801400e00e001182c02d9000c60008801d2001030700041d04d5190494108039030340400113107507400383e4010004902138030f00036801c000565052612044541409031010016003052a8503d0b4000003560000301d1309401615150303086032032810300b403a0180e0000c014803500d66010701509030018015a01821150003016a000034410085c042a500554502601020030744095020011307000440c195022840700c4034004000d44406401115154070b0607100080c2c0d0010f4204071004106040084d0419a01e15100c1a02d036400500030a402d5004002900030015014004541068400d803600441403d040d4002421640e1141c010002e004080040c440f003a61628a00002d680d0ba40c90041500001d4100d0a1708141c0140381c1520320700c1c008507440390035400ca000c01040314031164481c0808082d0620080301600c2c80c610030b40b4045010440c2d03d1451511400302d41c80c00500030700485498240780510b02c00c003 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 254891115 1250 254889865 254889871
    0x4030b18460c05030c21070f271a010513030c0305031b0a020108161e0f0e0303030c031f1809060b0108010e01050d060b060a0203040e0f1302060a021005 67
    0x1c03400300103048500300101c018800000c0c20040d0010020ba041c100b01159503140c501c0c00001041d61245920780c004041000b681000e4140080500811583c0d000090101501c903030282c112501d5201540407481c043e0710450036400d04c0610034141d01c114040040d00c4541c0600d2480d4555998000003001080610000b00e0046100b1070007141d8844c50001050309520014007542c0042c2c001c1031042c0d0250ba40b00b4010340e000480d0040c0008502c07414201598406140d52003201c0f400000203540400541180a1904000c426120080302800d03100c20161a844210340080021100307202242c00c0803070310300100d4a02007a080c0076420807a10341d18070083c0d800808054998060312200c0000821105001c3c44003050000e081607001035051031002c4106a50500038103024440d986003900c18400650040f40d903034040a40520f5030742c00b603254003e442c2d41c003600458001d01160f0003c180400c0303607501c1244c4141d00510380741d007064015508120050380314240d1041144601c000122030542caa20a481c0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 254892365 1250 254891115 254891233
    0x5030f0f0d0627020403020307050609060d0518070b12150105071b0f0902070308010510050409090f020a0e0c0a2001050a0501031203021206060d1805010204030b18 72
    0x1181120003a003000c03a202810f0001d075441030040c0720800c0181c4001601030103540c41214095203c24084004c15842c0c066500002c030303210309100034802504114405100807000500503109948c0d21400b986140e4815021484824005c480010f008004c482280c0705d49030303e0515005191200c0d5840c1c0008090070400d940a00012a4004101905550128400401f803a003c20340c08c00401e5117000e005020148110b5008400d07900700c641070540300e070046802408603d501040007000c141002c180c006138500c02240503150071003000c2100401c412031a44902c0c04000074a2070030142e40d104558421500c404806000c041c00c880c111100ca00b806414440e0704d06080008640d0f16604024940a981200240030306104001002c1581c41c540d0006600c11400c0d14510342e90740e610050103008200d1004003100d0048010544420050103400401c01c4a005110200c465181c5e140c007208a0840601140001e82c090000c20b0b06150240c80c6952200c03480194030350100c000c204103503c500b07002c82c0800b0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 254893615 1250 254892365 254892389
    0x15091501080304090c110a030e0604090212041704031e021f03150b04060504062307030203220f06120e01111c0203010b1b010227030d020a05030f0f0d06 67
    0xc00352100505c07620350802c4082c60010040f03007403440c61302e44401f00030784040c040100400007010345454004c1142d0003800012003c546d103619500d00c02c60140410703201101c01d03107400c008011105c1080800c3d82c09072504042c005200b001c0100c5408501c691260b001c0742c02c881000c00c00e080ca0014082c4004a85072651404144000340b06c0d0780d4640f0190540240040701404e00c410310442c0e5211701a20242c807000e0500140c140190315000c0c80407640007609046207500001e94204050b80800541048082e2404100b6031101210402000f00040e00440086502c0884d040084610840d10301c01d044840321030001e0030031004c8145c0b03825150892a070b201c01d0000002d80a8a901d018294a5410807081c002103013554104030304074042e8070856100c11480506603c0003450002c2c02c2d0f04840d2400e40941111441c0c15940a085841d000c14400d518030901540a1913a4514000300b501c100c0ca41d40003003c1c5141030260f802c2105603401a6003410960341047c043c038030301141d40303100799400740c0f90201c004 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 254894865 1250 254893615 254893619
    0x9130210031103010519080102030108150108010c170a09060908041d090a02010f11060103060501090f2d0905060117190305070206030a0902040203130201120c0215091501080304 78
    0x3000616a040c40e0040c2054a481c9844502801d15401d41c1d044d10070032200c03420b0802942c000d407592159290042103595100000016180f41d0000c2c1c0c014a120940994603096a41e4001880c2200c50503855000407500e40360b440509080c40c810b45a40c411003200000460b0282616001c04541c1c031030804458400d0009414084814071071800390488012541d8503449160030808a40c44010002c002410701c6601c0440082c600c0c010800d03090b540c48568100c1d41a50307500d04009010705000c1c0b00c0c5001032413801e80b10030b00042141c02030b82c00c0c050301c0e01d03a4400c0c40e01c4160030b40880003010165a030b5500d551028103100107401400302a001705903168200350004800807243d03081241c40240b980c03000021034010300000c0d03048001e4898607a0100da90503160b80c0ea680e502c0c0c005d0100d44000035031041c400000c00c0041d4400c3c0220039184c1e4003c1e83da50314071164082035141103800301035240000d40c0c8128445107180b50503040c40b0b680a510b24080d9503080c04603070840c02c01402d0a8116503000e030000300342 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 254896115 1250 254894865 254894869
    0x50d030e01050603010b031902120303071d0f0d032003041d090c090a0504080d050a091b06090b0702030102281e0504060e010e030706030f1503022d091302 68
    0x642038100101300d0080144001ca240020741e103c10f0094505488a1811110410355a5100c40140b00700c1040b4180c6c2d60740e03d0182c0008158407030081c0f80811454048903004004e06004945950100d005003000f403070454561801c1d5600c407078842020f160740c02c20000f01c4007518800d001030002030600101031100002d04841d0030140350002000000c4603400380302a07080340d555400e0410b030090204000021241c580741084101c1340700e81e26070300710842d09000c28021580150742c00944840c0c018510840090400500c101c5449034910800c40000c11382c0d101446a0f0100c2401494014801800180b80c1840c904a2094440b03000178040450043d9070700c003480c180d80107001c24007404852030098000c03100780d1b140030305940168003030306040081445400003903034051400324024010060455681c0b070742d034500040c05003175107a400101c5242003501c60310340c07214503481c01401d07a6070046c260399402c49050007450201612303e4866840300c00b02107c044250322106840c9000f0f40d009580c0d400d00c4101401 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 254897365 1250 254896115 254896121
    0x1c090204290402030405030a0c0807060c050c060907060e040c020f0a081e16140f100c02010b060403050a0201030e032203110105030906060f0a0f090605030d0f0c0618050d030e01 78
    0x4407450145004200f00400901c0100071905030b4810390800400412071424000024000c1a90040150345004098003207503401c0005031013113600007400c4079016500d00c1700705038442c042445010041802103419140c1c51400c0e800954002d281031041f20060789440c4100ca20b01220040c040d2040d000004c1c20700a0341c0001c00d030780c00c103441c0131b4041d1905d8814580d1504817641890f400c0074201040c140700f401080f410a20401340c0c0c00d490079085038216842e2040020091840c8184c01b005507180c0800800c2c1e82c00e00c08141c600300c03901301015040c0440507030010f5014110022004030f00340001c0013400c7c100300642c00c0380040c504045443d034040c603086141c086032035543c40d80c00c02c2c140041031003084403040c00001c02c181e000200352202400781800c18080b80c00c4c0c441c035410002c0001290100460110226030003801165012022100211100702d000e46000484402c000000343e50310010030089202a0801c0111446071031035008082d142d0780300c5134146800c003150400042e81b140381007611190f00f40 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 254898615 1250 254897365 254897441
    0x50a060801140405030403030804060f050405060a0506040b090f07031107060207050712082b020f030603070518070e0a12060c020111030907050d0f05010e1501090603081c090204 78
    0x1501c1d02501e04142c0c844c0c0e0754038011031000070b0070840d6450004007000b00c581c001101000820030240800d003402d00c0c21780d4a07610212018070381e0b185040c0004016107854040e2400028020340900c8240e216006402881040207001c00245505ca0105420042c11032004041640c007500c401a01c030042072500702d091140c1644241e0b2004c6503841c240d07010480003c02c454401c0100c040800d4a111344844c521244160b20b00407032400f62010452443d00d0000c1d4005601c0303a00110180c812880e251340c00c001085100d018402c0a129001000502c220700031003101c2903a401c01072404550b969104000ea06a0030948070442d42c0e50f03202c2c0d24450005409001d9004a0b000300000c940c11481c00e135512039a0f0315001c0c803950340310300e440d0346060051020380d03c0c0c2d600100790048020312030341d540b490034140c0c0c42660858483e6690341110001a480d16a0300c2404152640281100c0c600160782059604a88483d20020841940e032202e400060752107210741c034011807441e2070b0010002a500d101d0010b0b69020 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 254899865 1250 254898615 254898641
    0xb070f141f0509070513020d06210b180a1e05030d02210c0a0c1a0f060102061e0a05070e030105091011070c050603040f0c0f0e0c07110f0d06050a060801 67
    0x101d10f09218a680708201b81d00c3d90410308100586807614020400003074a8030b80d005007041104c1c10502d10080e02d03012010aa01ca005981c21401d0342c60381c7c2c03540c40425803183c0410806400082c0a03000081480722503600181c00b0380c0184002c41d80a0303c40da819944402c114940e1540d0000b035074400d06148210030302008e0b458001d0080c891a00747c801e00e030359104880d02d0800700200c810164042088580100c201050301c0000c1c140d062a00560329100000181c43d5940544140d000140800100b03003001290a4560091440d0f16140e00c4c60940c0039040c05000e0b4001c0c40030142201010303840901c10395210303011810040180c0c1c2d404c42c44001c106c80d0910b5949502d81c0f81003200c00d012607004409070007144d4040d44c0c001d641e0b03603c0741403a00d2002c8000d2700c000e0000d564407030002146007407482c1140540d010f050880003280c0b00c04540c2e89041c13040ca04014401308400c40040136030303e00100b6807a40480040d0401703810340040c0c0d6891080b541c0c21102e40e00d45035a80c0c041400030080034401e60711030382e01c4 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 254901115 1250 254899865 254899873
    0x806030f030f0f1624230c0a1202041202010e0915091503010e0703061506021f06120b011d190903140c010501140102010623040b04020a05031e010b070f141f0509 71
    0x2a0a00b06d440c1c0c1240182100c202c0400090044d081a120b4110b8000704090b8400854803592142a044081e40d40e40500768000344040010b14480e1400c45801402105c1c0b15000c4d11141c0f44410030310441d090b00070080d2504c001d402d590107400d92402c1c000c0d050100307801d03009000a54214a490001c46503428884030b10030f440c000e42801150340002d400380d403d100c0121012580110101c0c18000780940b600300700e404502c549204000c11409210302410385050001c4500103809049402000010440d00420000c5680d070359031075041c9455100c11080ea020b458070541d011014080420207910044804080381c0d50307100104554a908080700e8080c81e800d2009021461602d01c00c90380700308001c19000081c1d08404080081c40c1e403241d1008081c2c80003d0300564407500b0300c09014205800441c0c0307100c024103c17443c0442c8131034072070034040f8140d800a01e92181403648689641d408049401000c4508201e42e03020720b020101c0401c00c00001808820384110b612286c9039a07001551800340c208141648 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 254902365 1250 254901115 254901161
    0x702010509031204050c030a0c1a070f030302090a090608070305010608010c020303040b07020a1a06120a0c120c090513120f0f1202070b070806030f030f0f1624 70
    0x6400b104443c0040140d4099400b0f984540c00c1c82030030600c0384100350b6414811800428200449409400100c0c0c44550034418014507003c0030389011700c02d00f00001d0903c44c040750f400740001d010354090051148041c1002690b01d40b102c9241003242c8040c0c1002c0d1543c1e12428081081050034001e50010304150b000a000440144502942ea40400b4000501d981d6141001410301403081001f240d600d500440da189009000180300802c642d010317609180112102c07480190341c580c000901c0c01e052613000c856000110f04d0583c8488602420302001c4030540c1640310005100310060107254066200740d808840b00b0101d03898803003440e11101030544140302c6034880c81030170181c01c0382501450f01c10a0624040001e80112030400034856040018140d8111005210425034080001d5119100580440d5100018000d5140eaa40940784004880e2042007024500f4203c242005d06001a98a601130036614207941e02e82200c007944410141d008458485d442074a24140c2c058416005070411004032180 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 254903615 1250 254902365 254902381
    0x921020a0c0308090d12030630060c020a0f0b090d14090402032503090302070f030c0909020105041205030306010e0f09040201080402032d100b011b05011b08040b07020105 75
    0x42003840040d10190780890f8038400785d104c43c0300d1618216801403090142c60000000a4014901782c0a01440c002c00c1c111781100700301304018085039809105280080904150741c51801500b4520001011130160700d5901c400100c03480741100e2607a1107000b40c503c091a01d000035a280c40f04a0f1960020004004c032800d0000f1380c01011140072a000340e40150380d9030790714101084030a6484518020102c1307150120001182c0c540d2040800314400d5003035800a940e01c03500035145460a02024000c41c181c1c0030200f0003080c560f070100d10014410f04101d803c065484803030140c0c4000c106015100340e00004104061581c0c407400c003044e604012201110b500e03000101003201d0b4413004100038140800355001c02d0039560100301003a00a1a24082c4001034107150740040580108078001c400c1910984114030000348c1b031401040c041e00c1c01070b07486400d03021280c2c1ca070000c0850420401d0761700c0c0d507a03018a001840344e0f8403008101400c458444804078105458070340558034000b006a4116490401400028 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 254904865 1250 254903615 254903633
    0xc060a1505100f020c0913030f0f170414250503031309150510020304060216050312070303063506010302060a1805031903022503140c040921020a 64
    0x210094030381500321440c10b40050f07203011048000c003503011030014204000700606400000099112396110417004500712000e403010301075440307504003241700b2f99100703840011425402a401740c0100018080500e40d040e0850504181d42d0103100910034040302411404100f902c00c400508080d0002d519242810240b09401246070050410309500c0d0340050300d880c04000c0c060b1020303000003003180343c01e5141007030040d50f1ba0703100b889008090301415505076000c0200000da2022680302401030901d400f01e40c0d01c03107010b651003003204a05043d0781d07860100c1c00410300c2c0c2000a203000c0c401500a03807a08031840036410443c41c0200313511039922000041c40144c44500548144120741c0c1450452510382810001000d205174000a03010300ca1610821115080c4445480c4a0342c0a6000d0b11081e0a1940002804244d420214032002d05030100801c0014081d22490b8401e200100c141c890b911400300001e002c1d100080c00c29900503926541d45c910101c6000b0341e01c52440301900081c001e030f4816075603071100c0c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 254906115 1250 254904865 254904889
    0x30507291909170a1b050c0d03050d090c030b0a150605090303070609050102070204060b130513060801050f01260a1b080706090306050106050a02062a0c060a1505 71
    0x2100c0300c00100154203801d2070b0004a900d65010b007600c0d090250000036a90903404c1040300c1400030358004681c0154054015480c0380071504070010b801544220000c1c03041c504130031717101202008000c0040320403030368052280b104100d21031248020030914600b400260408041d222144862614440e4210190b50028440c101c46840c201244c03207804880001c2c1c1913000b0824050622803d0000000400006500928046100300c504201c441d0722001034804a0003010b0020780d40914240b0140000d1908803c0d0f090030107400c070000729030f203903c8009113800d440c400e4030561040700c40e000040c481da4000b2440000c403400d4008103150800522481e00303039598140c2c40c0242c1500702000c030300e14445119503005006006400211030442d69561801070030005280710940c0c016190500104085110320108e440010b030590082055440c4e440b494243d412500d05d43e16158440c2015145159080402800a172201000600703061b15007880182c0640d40c1d070f261001035005030341c1c4051000e5a00c2c110b81c000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 254907365 1250 254906115 254906131
    0xa12050a0c03030e030f070b0a0608280c05100509010201050a0b18040206040321020c01080c0a050c0c09010603020714060601200309030303040606090e0606090a0c051603050729 78
    0x41c50041100c0554254854001b01d9080700b0b800081c0f0100780701c1c0042811340a40c80c2e506040002c9580c545502d511140f2030406290014001c100c1481c0e554201001109079a0041c8540004541d4480015403910442500d07140030132030100b103590b010740c1c0a1040326841031190900380700110342c401c00164401c1101c001000c1c1c00101c4000700c7c0c15034a604040c0c0f4059036000c0464018501c1844070320813841c0308000302034014400c0c0d180320100d41d44114602400b0380080c10300c5600340403000f4170544181d085924041c05601c10603415201645c1c1e00c4a05600030405501c0c01640d9840505200c009041526101c66450b8002814000280d9200c10010789200c0120032139094102102e01c00c50440c071606403226810710000c41804207118140d4070403412609042c2c810081303146103036441d6803030b40d2003101c40301e0b03000c505103000036600c651540100e0006695860300a01d020f04141d45110a020a048180c00042001c154802005049450b40007003d0140441801c040016000f03c0c4140b20000c0440e0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 254908615 1250 254907365 254907371
    0x1090c080d090f1a070c080c100906081303030b041e0f09050c09070908060705040501110d0206011502161404050c0313082113030818070506071703090a12050a0c0303 73
    0xc810f5100c405c0e5a105a03224010300707109982d500c08203a40e5140706060601ca0310b40b0b07030305081e902c41c000c1c04000c080324002e88031103013103640c0d0f05421284040c0100c0203800785501d401c40001c003a90361384207503422000b0081402c00c002c6141c3d40c0f20700864072003406a0501502c0c0404c3c02010500001d812011107104581c03a249076603441034211204c02c06a07001181c24401d81050008270ba402c03001500030f0741e2080c0d9500d40e1550b200300d052550740302c3c7c4400400c01750b0003a0b0f0040c80a11038580000e1440c9555004030b40c100354144200c509404c116130310000b00c07280d848803007003100d1a0034015244c20016202205081d0f040c00c03c0c2a92000030100340040c040349000a806100c0000050b06d668014014010203442e444d044a50701407641103448228000750940f40022549020a040f213603849100030000c0402e1420901405610b90104d1030036140704103040c5008002801b020011482081036401a0004070150b00e01000710321141c409200500206000c10440603500403680300d98186c040c80d003c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 254909865 1250 254908615 254908649
    0x18070309020904050d0e0d0f0b07090f0609050301060801050115050c0709050a0516090f0303050c070b030c0c010b060702060f030612060901091a0606030c180301090c080d090f 77
    0x168010301060200942040c0c1000c2000180640480c2c40c800c080b005843d15506400d04c84100304001d429203100a0000340020300380c5001c50a201240c660048950925520503a1103407034004680d4459884980000d030700c21030503c1039040a01442008091701d030000e00c455414091800320404510040c0e02c200080072130904800030007048610000c1051200c20895400e00e09001405050b04499010105000d04540e14081d07125200400417100140e548a0105045590840c0e03035030302015484c40c40748154800456800d000000a502600901c1c21440d52858515803490075900780d10500c500c80c0b24140200d01c01b507203841040391006880c1054199407640c4a800103602401e20042c41e044034440d003010490802d0056100000300e5000c0c0c4004c102d0102c280c0760104440c80203d070302c030f608410140007050055020034083e0200210b0b00010240c01b11407080481e00f190a4001e050720882240241040040d1080c001548800c40e20b1402d400c41c01c0c140300740001901858400d40400304048600 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 254911115 1250 254909865 254909867
    0xb120a030f050705100c080717040201050306040c0201020d240902030c07060b0316090f06090b1008071403090601090f0203130b070c08040e0603121303032001020c0607030b030703021807 82
    0x150100d5040c0f01010415440246d00c01000c503c0c0440e03500b0082040c00140a5a806010340000d104590507900d9a1070361365030b041408017816064002c0019590240b003034414507000b50248641c0403140c40c400790400c58003810b001340440000d071f10209103140b0420a120005004400b20740d086508460085074003c0c00f240800c3c901071011480208a44024201146c902d00320f4000402d0726003181401c0c40380640300c1c1012401c8585041e42c0b26030207240b180b1052075103800388441a600035a5400e1100d104c0e20902650980c546c822a16094140c01c942c00500a81c003181c494807404259071502103046240c8500c1311481030a14000c054502040880001c52070b80c030842102c0c40c06944402002d40303c80da04d40011124800540e882d034400c1c090100d981d40041d6800081d181d010324030f01c0e02080c0840c50758405861400c1000e04400a4440d030444105041100740001c051a8010030003e124a2400d088010100d40461403058800d030001070042016a58641c100718030f4132183e500f0340320580c4640c04 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 254912365 1250 254911115 254911123
    0x10e1003050d0201060f060518090a0e0a1b060e01053a021315090308072904021206100902030a0605040912020d08040b070e010c05030c010b120a030f050705 69
    0x100051052064400000c000b943c1034005004649450b000c80d41040d07143c540c251464003601c42005003504a0140d02242d03031400c0c51503680c00c142000720001e0007410391070142c2c2c2400c00286003603801c20101121841e40b21450380c00c00f00140001d14140c1075101c80309000a0540c414401610142c1d10301c0880c01c00301e000800b00c01e44000800c111000c0d02c0c030010360459406904409101260f801c8100000500701200e41421611880c00b036890044e51400c650754451a40c1100303000780d50078a0000f0b100000c1e01503401941c03044019840d0f4081d81c0d450075204001e501c55004a1441e9603401075004e0260042103411a1400c0c0c82c1130f000056181e0381c1d0350302e00d2401012658803a641c0a03040c070b03403040c007407003c40b400030341e14429507509540801459000648004c074081d1401080100c003403000400241c4984000100040705242440c09018a43c131000d1444e040b550429005941d50b0a44038182d20700a40b0381c080c241e4190001e003080209a403405822000184100d40c00d200001410307a04001c0140 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 254913615 1250 254912365 254912369
    0xf09011a22050106020a051b1f030b060301063506062503090614040605040306022508030108010b01031107111507081222110414011706100e010e10 65
    0x168040010f907079100c00007581d0300040349094800b40108016041280410800c040d50b946c4003904403000d0883d509010784180350403019800c1050b6440300d125419039a1b0400541c001d0419580700a80c104400e0040545030015030b103d8040480c204480100945036141c1580c8d204804483c455120710110095a03206010314480c49410f040380098101010b8000800d90140c4000d030782c40320303001881c1d92020003080c80f036401804045801172004100282658000340101442c94000030081000c061502040d00d0224104840d09107011005000c081002d10480425150901c2c041c030140356641b60f5800648102c2d84083e0002d0568507013240c407612030500402203240a101c0e8141da0300018100b00071150007200c20a080010030402080c00b113030443c4030708101851850700d0ba030b00154150303943e585100441d40c0c42135005a22125030000598004c0300d403500804421a03c00c1c0240702040c07002d030900703c00901103140440300e08010710004181c20402410b684041d43c0d12411500c2d00c07912215003184903 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 254914865 1250 254913615 254913679
    0x130e040803040308090d050706022b1d15040b040302031c14060621180a050a02090604050f0c03090102090616300305061807080f09011a 60
    0x4140410466004000c501c520b000b90f5620b100751301d40700e44541d1122030403c4d881001404c2405042c0104a981d03000308500300c0b0180c00c07817015420700006810209030803118912000d95071031000701030b2a1880005191002c65401034440e400c841c0240d070303411880c058000743c0604106070010381050f00800480b50900310404090056481c1030766035002824446a4103494000070340040380190408e0320540c0c1d00c4824007020451481032501c40b040030000010031903510118690340342001c0c143c0610818074100c1c0100050201d40302280180f280c3c08001401407070003245043d0801c07128040c000400e6800c10100405142c0d40d403070f030540340d6000e0302072a020103034081d100180b200f0524600b1403009940a1042003000450805044203810349170054900556440c0607444c00b8032194403c0e80020b61044005185507000d401400880d40000012101c01010406c000107104001001084e8203034000002c400134411311b40c3c05e850000d02241c110100c207001c0c1031524880700d880d90303189038584030380184 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 254916115 1250 254914865 254914889
    0x90801021903020c150f0117010501210c0b0a0329010207060c0c0b30040206220b0a0302120a090809040b060d0f051807030c0509040f0519140a02090402040213 70
    0x81c4140d0f03506d04000e00c90503c41684448a0b44400c80c8180a02412070710313002840715001000d00b110394070000495201b100c0701300141c0780c00708400c04001c4c003501c0204090340c0d0015140c0610084001c201080b80100b60301700205820f5810301d6a030020b420b005070b4413240350200c00201545070561a0b98140d410032144142c0204d20f2880b629034150800c0c0300c003131615a140380c03180039959149807080c800380c1c0c02030340142040211000c030070b6081030001d082d1080b0285502080b951002c4c101860780005e03080d40002500003031004607009040d404a03130083d000075420045100d403076a454846100d05400c060199032207250440c800e5903003200ba01d8110103c0c0c04240511031210001c80010001245c8842415585008140d1194000600b00c403d0f40e602040c0031845038100410003084100061040381c4a200e42d000c0500090170511044140ba02007201701c5c44805203d10308004a01048c0f074840c02c00ba8003507268080580d07110001150440d1701941e006a88044104081807500040e401440c86408 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 254917365 1250 254916115 254916121
    0xa02030d0f090210050310150e0301050c0a17160e01050c010906090203010609020f07082b060e130b06090402060c0a03051c0204050310020c03040f15090801021903020c15 75
    0x3490b400c5030481070b02c01c40302c0282541c41140142c90501003511410034200e07900b08148070102c0400480c01c4050346604001101c401c02c94002402d542048541d0400e0f40c1010810b0701c042c40c0c020401241d003030280640610f15183c0300c541c8000102250095504001404500071400c0c1d0244041310035034403840c002030001c0c0309e42c1d05260001d016142801c0f0b02039031a2050006540e6540e100783d6100640c0002c42502d050169102c20341940c01280701c40c841102c0041d12803040d107400d038221208400300d4031000700e100c0e0314000000c020294000c0015a003d80c8503e01b08000400c1001c940f40d02501c1103030b0394441500c841c00825164010044524445d101d0411100d06058000024200203c030b558100c140d07807030101c0e0045060340100c0c403559415034004003504034604e80f160054200442c183c01100e0400369030303154510300c2266a81c441c20600030b40490b10250f50368003142c1c14010f0000740000758075220209214645545110001f80c040560100d8005140c41041c40750709170304d0381400c4044d44581 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 254918615 1250 254917365 254917391
    0x303030c0f0706060f080f0f010c0e04091a010807060905030312010527010801060f08070b0304020d03030b09070801170a120e010c080f130602010c0c03050c16090e0d110a06020a02030d 81
    0x300f60b00d483c0410511900d07101c230004c001d05004480070303011280c1e600c6240200b402d0074000644034030101201c0741080700c4c06007298058a003803268000c00403a00100821071504402808450494116600980040200d21300749812154118115070094942c44803101038440100c05421f6500540c80740700c00380100008040c0c905400a10941d41c00400d1007444560b6051070b59642d81c940d200c3c0c8215110284002405894041c0210f000c06019041c0401d042901900142071002c08032030404c040b8403150700600580c2160101e85c92020300c5100100310140ca1a00c600411001803000301041001410040c0b406910440c509090540d0260602d501c554805c1c038604e02d99042140400504060000c001500c28814040d1201c1000c91351240d0f5141e0980d03860490306c650110401d00460711940010701c800d000c2000049000b4a0b205100080491305060762504000251100d0001c11080b00d070404004040828540112640840c005940c0e1105c2c21040e411801034034080360515182c004610485 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 254919865 1250 254918615 254918623
    0x6070b040506150d0210030b0a08120310050108040b041502070f050a1a07090509071710060909020c03040b07020a26060c030c03150609060a0306050f0303030c0f0706060f08 76
    0x900e80504540f005003058810b0005040003078002960241442109501041c0241d1001050310f1003d40b040e0710300c82d11703016010b14100741668907045115002040000911800d2502800b03480c00b46004801c9003040e444681c11000c01510240c030900400c8031800010400781e048030712042e440118020100c0d09420007075124145103009680d03144c010b41d400301e031000c801d1442900c10181c0b03440f64040c041c00d000521148400042c00c12050000c200040458540d041814a20546d941d0200350f104d941808001803018540780c0c0918180c030300520203030001d500302006407026101207418641e210000350001030800003050380310240340d0719820708a294070550443c4a08407401001c007190740a032584072944a6510084807002c0160000703101241464003616810030152030020111420240a0400500b0950140c601c20b03010980e1840c04006504003401e2459541408a01560451034100401c02c000d109400c1030000d4100002408010440c55901c030101800b240120920881d4449201e5955 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 254921115 1250 254919865 254919871
    0x160807080c010e030601030b040510020301090f0b060a050d050415090b010303032909040311030318010f1a0904060204080a110102060603061504022503030c170714030606070b040506 80
    0x9004400400e22030b035004070200300e10f90202500038100c0760b2a41d22141c03800240a0804c032001d01620040c064006d150b4009140a00202c02000603581d101c1d8048004883d48850350310300420050040c01d00072504071040d66600711650750041215555490400000360103c40807020b41e0b8a041e0000c41800841c1c11214181d900c291001c00c100702c407084050b20380c540c1c100320b20710071070350801001d48803410446500740d04641309041440114405441681c2540c00460303000381c070040c510f52110383c2d120090041c2400c40c032181d64104001240c200c011080e0184011580d4050505440800c0070080180d0407600105401d9050302c0d04603059241c40030003204001000c500600c20040840c03118500420302c107024456800c200800120b100003440f0180d04480390307012040f04901800c000b4105072486c0320f10014407030744c1e0018220514400140600c11a200c0303284020480e07100308901160000800c2702c000081c2e030807094803036580000065040c86a20f00081c1620809401e0200300003001600380c0c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 254922365 1250 254921115 254921129
    0x91b06160c0f06140901030f0e1c0e04050f060904020d471803130e040303060b04080601061b0204140f0105060903120a0c05070303110d2d02160807 65
    0x22515540d40f400c13240e04130221034102c80000f08000c1e90a032580079521003060362045410124418040304111400d000c94620564086074100c0b50703c00c1c200754001c3c0d1b290807510003140c00700420700700a40102c600c0d040080c0070501585a40001c10150750301c45048114403684401c400d0301c110070f0a40584131a595103090304928031465000d260044012400d44100314510645105141d80c411031210031040c48912410000d0100304902c0001c03041c074144620151060070121201414145070003000c46a5940c45208548c60a2100740000784002c101541111003903d030960035110741624101401c00d01c4034000754000e00d8170742c12900032070800c120503110381200c05012515a1760751062016921420524036410f8202e10004800355904002030f02c003c403401e103001040729140b59141481e00c0001d40040d00803951094480c4200d6108100c800f80310040c518096070001c400c01c2c841d034403c0340c3d01c0007120b00b8044c9907150840c54501c200b003211080c220030360111a1880e51507810503180c4100d4003c8007 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 254923615 1250 254922365 254922389
    0x15040e180a0201080408091009030209330402040902180f0a080d0804050c090903130f0509010303082802090a080105010b0403081303020d080a020c0306091b06160c 72
    0x14000c454048500300d404140c00014000c8410198011191480e0040003214003000c28001030b003064032644500026510320341c54120480e8258010801000306c0103010800d040182645024840d001c040c002c40b1940045414202c501414000140030707028a801c840111403002ca504141048114458222560240c80402c0304210000c2400404e018601495969a10003d102203070b00e0b100b03500d55070340b00d401036040d03829035042c0340c3c0040e003010800c0d1054202c55001081c3d65443c20440c8000400406645041040c1c0500c1d08011a984c01070500c0054140035281c00081e5242030306420f884030080094180000020f80c96100000a4011541d200e00034510040b020030003a205116071b80c10b03501d0715080d00b804c4c60700d9543e80400f00d40c4401d000321a04110f003400000140c40e001c1900c4039041c490300d0000d03100c01c150b0100070724100d40000c03842e10aa00100600c4442c4401142c600b400380742c8000607101307021086001c603003a4810101078000030107401a4003000d000c4c3c954a201c0545038165170311 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 254924865 1250 254923615 254923621
    0x60c01020c0a2a06140a1e02071815120305070b0106110706020622023607020619050601020c0d1208090a0c06030b0a0314010c02060c0c19030e15040e 66
    0x107241040018018000031455880322461500560307000b61002c1b170340c00e2400d4071250920340038041c80c1e0103441040202592000c0b000f80440360503044403107410004c0758810084000326500c1c0600d980181d103d0722141002c42840001458469811070703c0c0d084d04202c00d10b4080d41c1d5210018171941d00d403802c08003580190240441c04a2021401d54004c1c0500c5441010203008694018440181d5010880e440003007840d0902602004100111822802c1403908100002e000149040301000074500000c542048080055011003024003400c0440540b60014080d41c1d01c000507071410303110b0800f01e640480c0c0e10184004000d174040d011070105040341e4820b0125150a45015a5803003081c17401010402240d0050040318840ea100000140d8020120340030f443e500d4031364038424040501c142d80581d440e41c50100441d6010890a6009140e940000d45070000350308884e0384074045990203526040307803000030310f050500c034800407142da41c4000e24250702010f820b4511485a402403140306800c0b14a0000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 254926115 1250 254924865 254924933
    0x3021506030a02221b030905011a03030307030504081303080304051005070206070c0510111207050301050f060c03072415060503040b0702011e020409060e0411060c01020c0a 76
    0x200107a41d5800340c465030021111400710f40b02015030780d20000801345e17507000852104000c940d20f010000b606860000c1c01400c03904125095032140710072803290001c1001540030649000040300d5020b4254078000506449520703040525100c0c16007009180324004602005001c0c15500550282d0b108030101d07690902d400410009481d81202c0500140e089a80000c5e925402202403040c41c91144055400c43c0c041d0341c0b040011244454a000d04080300401c02480c104407455003241c11600d2810424110740c500030009407140072043d45107001d02c1d004504819036500030002e0355000340d441050540c00d541042e80b051144118510210300342400d004564032510b2030b122402c1e00b69103a0707554840c5103565a890307481283c54050615002c6651358440d000c1415a60300702200c0345c904481016948918142441050340c505400030910001c3c6003040c4000100ca2440a0084600c2a42d440c0c1d2910300c032170038490090049251078415801002c0c0f40200300321180070030122501d0f0507040101b4000109107 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 254927365 1250 254926115 254926123
    0xe01020c0c2701060507110d0c06120e03090d02030a020d060b03160b030609061c0303061706010b070201030509030409020c03040302130903020a1103030d0614010813110118080a0302150603 83
    0xb40310b2070b840d03079040140403041c4950024080f09004001c01006414280042004110490b809807041e040300c00007480b01031391203200110300003210441440b500890040564803480394031280c51180702c003142d0390002c54809100c0f6a00e000c2d0010800340e02036450342410009000b54410140c480e003c1e40241ea68010640101981601c0808480a007560b88050900041140c0503081070780c802c3d41880c00921404174201c094420354400ea40100d40c0c1850300b507410003600d0300000c10b50890b40081e001400388644580c2502e0550f602460007007102d407200d100d081d05520450708295141b500029039176060810002c01401220710a8179800005040941002e04541c00c0c0180240181c01010f02ca10106113040550412914020300f50781c0b41a0000c007640c0e0889440354019a680d07240425513207019038001e24101d5001840c0071050445481994030561003a0400902a0504c82c0000541481419a21031038016003840b04c100d8400040360705010356146c14140c00445080783c480c00280c0c1c10704002c1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 254928615 1250 254927365 254927419
    0x20c01020306040605060c0712020d0b19060f0806040605072c0a0506090d02040902010219060905070501020f0a03050307021f020c12040f180f2c01020a08070f030e01020c0c 76
    0xb5242071030270460044406200040141c1e44059510084004070702010030701d500561f101981011840581c04c00c9600342e54042e8000b80c0032030300e141c60030091468040342d000c0d40b00350701400008103652112804d40740200600070809420b0545085910721154410002200010444980140f15070703910070000c81d4030800810b581c106542e1840b942c0141442d0308400180351050043d078801d41c1c001c06000c020b0802025080d500c50b070300c903517484040c48018410200130b80390070710141c268500b400210f1980d8080407100141001400400503082c5442880942c0002d145012099100700f02c0a5150000e500700841c224101d004000c1032105040d4840708980803680c05085e034480301d52a0180800c0c00300d01440070095042d07103800c140e0101c4011441aa9802012840450b85104480010085841094200c54070b030b41c1c4100501528150006c0c4600e51040b00c40c07500005541402c01c046024255010041480d50b0010503000c031092804680604080021b44040d540c0c60b55941807000305030450703 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 254929865 1250 254928615 254928637
    0x10506060f07020102101806051b0f0307170a06090b01031b12020702120f0d21090807020307080d18051f090e0907091109031f0e01020c0102030604060506 68
    0x100903038100700718548058224a40140181c03030314000c40b6030b4441d080d0303000100c01007110a8144851002c00209120301c3d1307045004070700c4001c458240d0652720030340d902c210441042d0584010000401c1c040c072902308028581707103e111800c1c075401c18803042c0025260600800d000301c0e007495240307201c65210744500f0f0401a040c40c1d00d00c40032800c41c0010380744440401c0345c01000e95020030450000d61912140070382c0582031040144502000f07400014200082c240f858030400422080507041000c0a41e1401d00310b90300f41c40e0010341d041161a027000c05100c2e042c002505805100400110340d407000c100301403240426102e000441c02c0650614408448a0041c240e01c036503203a00d03a0500140c031285c14248400c42d421b00c001c180e9103669011000d000200e811606550120f00300b4000f081050203000c2c401008031160138108128840082d0f03d96070354107613080155140c0c49108905d20a83d412951010701003000856543c07d100500e280030303520450701940100c2c01c00700d00141c0c5040c100c0803544c2d00440 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 254931115 1250 254929865 254929867
    0x1803010c080a050c091c03020127060506060702090403031a0604050a0e091e0c0f0a14090703021b1615050301090e010615021015080706030b0316060f02010e01050606 73
    0x1e546000d200400c0060181a0304ca01d00303206a03c1c5d1602d40690710010030048200c91003403109031307203002401c1d104800c0041c081c556107440c402140110a4018240c4180e004034003240030369a500200d5402d009402c00658008514414070041c1505640b00000e0300740002c5603144000c0080c02400b03c103100d00d00c03070541c00c030011103c1040074000c001c1c141500300f00c04200b5602c1c0050304008602d008005017400d201d80d900032603e50501494013401d810810300c03054459864035450412152130b04000c0e050040d00401200300000c603524800c0e03045460400c4c0341d618a02c6a00321940d02e1641da2400034400c401c6901c000b002c0400c481e07030fa00503462051042c0d42d130384a16581c280240000503001c1600d01541c250349801d000710f041c40300400c8031900c40e0b129900078002c2c6c0c1404500311080c0c1c0c00c010f54402250b06080c07014003801344080b4480c010303120641404500500c2d8100403c2c42d02c031003a0111450310203840c102003040b5a0044020100c080590700a2002d13200052001e800c032181555110340c00350f4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 254932365 1250 254931115 254931121
    0x121305060609060f1e06070503030708010602010504171e0d090c051f18030203030a0e0102100905030a0e1302030a020408060a0e0a02010f120509030915070506270708031803010c08 79
    0x2401c1e01a2070030840400005105040544012440c550041c100890303041d00f00ac401c201c502944040181e004000a1009106e6414039860704440c0044456021004c03043c0085d0710418082500403030700702c211101d02c860381e44201080b500c5004111044084a144800030b400240ca880c11103d5800c4481d103481c4000b910780d1002d20103440c1c0b10043d0003040c003c0300710740c0d5001015950501c040c0083c400961521003101c94080300081c00c2031007203c10342441c0303450718424601080d000000c0d104200d200d4142802d206c0a40303800144d950004d05000c03824640000f00f0030110080300e4010700200d82d075407011030307540c0d40b24100000103942e512401c180c401d81c01040658090742c810510700c03810f03401e5810400c0d02c0c01c4405c400d170020340d00100c1d034551030766100141415460810321381c1c10705900400c0121a04015a2740d6880c0d441d1240907103e400c45191043c1711007452a50220b204034049004411a442103503540c1e1503a4403030300500c0c16940800101e64405074107041c180940803540e00f0035503541d505c0f40d07 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 254933615 1250 254932365 254932369
    0x2009090115050937090516080a051203060f0d120e01050f1e120708010303020c060703050306040f1b0c1a01062705030f070302040c030c1409030102121305060609060f 73
    0x3046103135502d10b50700499501d07040d4481034418001544c2c020000340c20031400642503608000d50076480050f05078410440b9001064002c500401c4003441801c005036a87c94000001c0c00c8422120b00d1240d001081c05503083c02c0000c3d074007100356900c07060b407112190480c440006443e01e02030000c942c0e0fa000320800c01007100c20002c160491040c1403030780e5104d04008a9180c04000141d007100d0312070105008600600500d07804000c000301c2c85a04031141d074a8803880d86c0d401010782c00091f00c094000ca44901410840c64069084076010806c030042c4c2013050010804014002190710744180d07510003002034680c041c0c203040d840950580780c80742c9815200105070f200350103100300c1008402840c460320a4020900360b80034032401c1030019800b8000d00403141180104422200c441e10004185840e045042c4021a0804410403680c1038900740c1c40d86424001d40802c2c06441103042903c100120201002004d802c2400c0502c191801034046031000d030707510024001603200594038203510610302000300f1618 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 254934865 1250 254933615 254933671
    0xa0909021309060b09060f0105040e060a031209060e0307030b04030804030c0b0a0b0111060115052b06060e040b0312090607140a020117010b0720090901150509 70
    0x440c4054444030325201860308210071150301490480d01180c54001301200d40c545580215040b180031a044903011b12000c2c0082e06a105520800c000c000c0382900040300c0d9580d8980329401141c0140d814030391401e8040005181e82d2a601510f8085140c0d581c8000880c103000030820113981c2c2c810300034261621192003d513001d0f00020000c0301000b000e02e10f0500010382d25030000c0e02942404d540840c0c041814000900501c03040e6a5030000c540c0030300010132000041580300361414520381416a038401507040368540e4206603240d4034650510000b2612060b0181b540300d202110304554404000380c1d4140704000c10b0303540311794042e41e040d03000d8290f003103088070322400030005840700601291070300707049a8981a014a29411701049500801c400c1815543c01118094041c040b54260000b80d60400c3e07415462800340c02006003030700e24082c0d8828408001c0b140103003100c1c44018560011481c08105080c0a05400b110962000608900000340c605080c080507015038081c181038950b40003e00100150 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 254936115 1250 254934865 254934881
    0xb09040e0c30060f1803070215130506120f270c0a12110609030c09010305071d091b040905060f06010210020901050306060901050f04030f02030c06090f0409050f19050d0804020a09 79
    0x4e6000410407503005954074030780c0e2000d40280208040d26002c40000c03940101c03040da8062f80c01580d08000d12080200074040a81d4002a0082018207503140da210b03260781600008202c001450100c00440742d00407002544100512048031024881901c0e0b03804200ca5201d131800c01400b00548000c4d2a816142c2072015110310000a000c0368264403640c03001441061080c0d0041e182c540001c40140b0403000c0c0c1d030b02004210088820000c22606141c030b03a486da40c00303030301601010521070b42500d10b41903030f0381740c110140c243d8028013203800038100040c08142c04c80d01034600c640580310b5201141d500600b40c1c003d070303881c00b403058407914150b5542000703005140d800341400a04002c0b08105184040e200000600065400b0b203d0303000c20516940b06140c0341c40403501c04144244800e1106091755641c0d83c5012100200941d000719209803280f4145203010251456045a0702a10100500d47e0040c0744c08808014000c6084551a951110099441c0201a603020390444140310003400440450381020302 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 254937365 1250 254936115 254936161
    0x409080723010204030303050109110f070b1b03010303020105160206240d0c06050307020f07120f02150a031e0911060a02030d021306180b09040e0c30060f 68
    0x103418001c03000c0c1c1e40c22680709420440200355603400501140703404d4803420800c0c0e0010780d20246090701e001c1207008240180c000c01044a0f0081700001c020310840b04000c804840e00c8140c990b26540c5910340071303001e054100c1d41d0481610400c01d68080342d0303100007a014001d010000b00401c05601d58140d1724014103140c0300301500b1581940c008000101030303d0310360009000b25500c0607160b00b40508000d00b00260880c000c0150f500c000010f0001c4035041c40307a255051b40c4451041d512015902c00f00e59458840a411f100c0c03a60081416402b00d601600552074051420850482d0344107030a409504035114000b02904501e001c807960003290501000400500c080341c011a030928428848480691388402c0c102d0b100450074130310401c0f019821010000c5160f584035400111141403030010580703401481c1c0c0c1207100f41d4490400c0c400c01001402442c07118003015124003405c2007000bc242a40080d8070110f40c68400e0940c0c0700c0c00300c4842c04030b900c03801030058041000494a404100c036030b0340303031020340012 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 254938615 1250 254937365 254937413
    0xd11071101022506141201030302010605090f01060219140601030507090b0402160828020309130e1b0f090a020301080f12070204200d05190903090506030a061a041404090807 76
    0x364954883c5050031f4001c40c0329600100e90282814140b100c0100003502d0b5600000c4028010b001c40e580201c0c0c1ca0741c08405104800c03138a542c881c180b0004012524103100001e000b550004000c0c818003068100a58031518410310141c80031806000891062040302c004854244c00b01ba0000ba000300000c1807040707404400300c1e110420031545810061110210100980d00002d0b540c1d4540c2041600312803581c0e58201d080060b030000003d4240c46a2200c3c0d20f0103244440000b180400c1d545802c00da84021340042d000e400f0500c0c00d109000b00a620a0080020750300c42d8441400015100081c02c2e0030200c050780b04a410401c941e403d03c009007600c0980c6201c4d500b0007045180314464280060401203020100114040c1031080c0340a42c504c03046117020101a041140b2940072a401c01c681b03c045400503188181d680d48d50359910300040085030090204418400c43c0704100903100340281055038444801c03041d4541a05c0100400c0702c4d092000140805030601810300802c00b0884000f0127030f00c040300c05e0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 254939865 1250 254938615 254938627
    0xf200303040e042306090303071805010c12050421110d080a0e0a090504030302030f010e0105030705090912040b0c010c0918020d06080d0c11180c0d1107110102250614 73
    0x132034108941194920002c1d8400300402a15076885444d048852513103c1118081c80e04180008120701004400a440c20100a034044001c500c00e10489000b896400031a00104410b0a4401d051800c1480140c80002062048001515080103482d403a80e40c0300c0501e501e0101c0a6206803072200c0008501d41e80050442e400103451503460281c640b00394030030740c0d00684d2450442c051517000d81060700154102c0050300c00500240c0c800244542c1501c804985060566481c9807580c0d2070080351110145103610080f500290f080240b0000d0440603044038000e000d800e1280d5070440d039400c1280305030500d803050001201e10ba16619401030090080c5182c000c641c2070b03110804c4e9440d0401084001c80052010110003061182d01c2181484d0824210b50395081e0040c5158824140400a082040c4400c1c0c0010a10480040c5a21446a00040000d26030f00c80c507003070400b20406228524441e0260160340648030300070f4610691592602422280200010b040c00003c03220b203280703c440f0001c446020485 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 254941115 1250 254939865 254939933
    0xf061f03061104030308090c01050307050711030d0203031b090604030602090d0501110d06091107110a080a2102010507090e06060d1409010e1506010c030c0f200303040e04 75
    0x956240b55081c062541d90f841c5186001001005e000749007d480c0d03080107a22081c00e0b80d1040440c2e4000c036291a295031959414200b103200e80110030510b607410310603945100c20b41d80c1c01102440c03080b00b01c01c1c444541c4030041308000009106100840758442800c10040c4000340e0642e000c3c052401000c1e00c4107076400116650309084400c1800c480e21110008141049500082e0060002401403440c0c20710425941d0501d02c200e0b4020104010040d040d8449011280e84602c403503440100010401c0b501da910080c281100c8120a180c1d00044281440404000c00c0380140079181c050300d00355540481301d40c90b250307840d898080d010309601d900200422840d010310b01980a000028100d684071fa101c42d040021070329084500c840c080440c2a00150307290201d0101c003030230341d0b50301100a09103490358414910382200c51210308030000f045480c0c484130020903c0605181d54081075180140d00c80700d02000000c0669901076071044c2c3c01c1e0200312000040000d082d2502c90244240540c07003c14000314140c0c6 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 254942365 1250 254941115 254941121
    0xc03030e010513140106031109090321040308060108010e0a0e100204140a050a030f060513080a02030c0106050910170703020307120501050f10091a0a170f0f061f0306 73
    0x49038540c1e4940c0c1001d01090000402013001441a080300030030085245980d400d4940c01084140c2d80314003c8040003c0032050180110780342e07120414100380c1001080b03100062944000c1d1800c3d8002504000001c089500031016541624018412090156106801c0e0740242400c00390540443c0101e90120003240600d0001d0400b07400b10321040d14104211100f4064480e0b1140d00980c450340c031404040000c614103150003440c5942000011540d65100030040560800074500203090500005085000300d03801300180445102c050001d11009656000300b107080141591007070301c0300c8071044c0100004c040030301099541600850a5440c4242d8980002c0d0400c0030b11751244241164419070582000800e01c40c150b848054020009010300b4040b44101d00c0300c01d1409020f15165550041c446051418265138415000060160900c2034541c0006240c100c444c1529031101e00c501c0e00030300f07240500403d031950b00303062007001045d803580c0d00300031a0f190f411b40030345401804058103400720108038140 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 254943615 1250 254942365 254942371
    0x31512011401080d03050a050f0601050f0c07090204031203050708180f06090d0f020106030519240c0306060219060c0516030f08150108010902030a060e01080c010f020303090604030c03030e0105 85
    0xf0042c0c220404a441d000e420ba80d802030000d840f40b032400b410425050101d1103032540100081c80d0081d1100301a600b102441d104440158809104000c1d00144140241d0007c0041e2031240030341139410100742000703800340e900a4071a2004500124005041030341001c8042c02c40c00d80c50b030300700d07111000c0d030b400841e080c104180c0b8200d0407a0480743c070058560750841c020629020301c0b07100802070f540c40e5440300c43e142c88100701c011403080d80c0140d4076801d210710010307516102d5046450044645802010000003043c00d002c018001c81d0401d0740028416001288481c1a885ea60551071203c1c109941c0c3c090090421850b50b04c20b201c0144100e60741110020903500c2414481e895002c20075600c2039028006040080ca0210015141181c0700010b99000d0301282c1115204000541c4980300c104440b0007a01207900a0341c00c0307450080001030300060000314515031150070388401d010244140800c070b0312440110380c0608c8503440718022400192040603101102d5000e0702c0c0014616500380300d91800d5500035 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 254944865 1250 254943615 254943629
    0x705060301121101090807260316030206060f090f040303110c070e06060403030c260703050319020c0d050d0b04020316020706082a040504140103030e06031512011401 73
    0x100400b00800c646050290300e00e4209081c041d0101c4d291010396903554906018240080f000700540301c0302501c10176100c100e42c80585e41a42e4032449c6c0e0049100446c0b240035403d90040c07042c04085213250a18141c54146504003030000c942c01e5540d070540e41c0e401100503000f2400c040e507401c505200c0106000180c100801e00c500a4000c0d240340060b41c0e0303031400e4040c007802d02c0b552042004000080c1c002c000558100c3d882820302c402500442e1b0300d2105500e507081c1d111860040015000d00b0141d0050086214520b40074002148000350b01200d0102d010709a1000c455502c03000b50000c1c428010b8024080e04002c0034008600014008003080998206840418510340d64100342e1044980500828002d8242c80c0781c41c0c00140b074240300040d10034003150000e40351000c81c601c030107129802103070403030f4040e09001e0001c1c01000350342000381c1100c500034442940012030a11400d2118a42082101d00a5021000381c01c40d014403501000003840f0708110315482907507104010440401c0c0104c04600901103 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 254946115 1250 254944865 254944889
    0x2a0303041a0f1606060503060609130302010603020a150810030809090405070b070b0403020118030801060e03120307090509090d12020f091e0f030105130f0c030506161e020c0609030705060301 84
    0x134900101a00c5442e00640d100b50010020060aa01c603400c045500400e4200c2c0d40c000341e0090305040c1e00400081d00042d402450305440464044a0b54660001c07401c1c0503501c3c0c003210341d21100710722100d000d00d02000703104c2c440c2081210828500350381c1c486d420a00400640341050342d611b425805030390080404682c00c541e440200410b141e02032180017110f5603c40c80410081c5001e0f0360080c00309005019003014001045511451910700300101072070302001d0804150b690030188005019014644940c46c800c40c0d503400015030b000b10208007240c00c54420744601c0d200101000003074010f50045840014601028018020150b4888910143c01034080c0300c4190078909200601030b06900301090203000780e0400081c00312100d0521407102d031103500300f81d518101440030720740482500b01c15400a002172248406221908103240e2081002d9000368070f490880d101e250204000e840210321118016030003d00e40242281082c07001004084002000d81c4c401a0311030001407801d070420b03001107524141c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 254947365 1250 254946115 254946157
    0x904200418060608061f03020c190501180503120a020903010f0504020913020d1e0803070f08010609080d200a15140112060c0201020702040c022a0303041a0f 69
    0x4264864034015100504d0442440d282010105070000402651261008003040d08030781103038825415180a8400c240907a9a000640100d240304d2542c0d45100307235425407a0003603140040f00b4850b81c400310b03103904c500598140782c80d0f981c1d1005020001413522000940030800317505141d4080c42041121340c000000040c140c10540148001950000c4c07490b9941440e40140c0405030b035850036031000079544100c032900117498403142c0c03540a8001c0580108405000f0091140c0190000c40e51f08441d0850303500d290403a0303600d4004071010741d0244952801c07034022008081640f80314982c0d50040b83c3c02280e05680c04a41e00482d6840c1003401ea00c1a200b610340000000910101e074095a410344a081025039410350402070001d012604040b8014003080e078031400000e03aa4000c0d0140c40e0942d800500810a800440c81c0180d10381d50051009024401580002500c042e000100001c0aa002030029800e081c10080350000f50340320107840c00c40740304060101010b810010760040441340720a48509400034 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 254948615 1250 254947365 254947409
    0x90c0e0c03070f0e011205040203070e160318020f040b030703211e08010510030902040504060501030501050f040b011208040902030c210721200322020609042004 71
    0x800000112004c12200800d0200280e03484103524980307140c2040000f4250301d440c40000d00c1e040407903000e41041201a4200041082c003a078002c0b0302441c19807020310001d0021010006403161072203000b9881000c403a120310403030405a00000c3c10410250448803165102c1c1c5519a000e000100e00262519111048011084e0301181c1108015490035005141c0d05207140003414500b414010107000e641d1403101d40d215240309400c807105164018004200074100b90a001c006001309000c16100fa60a00c1e02042c60705040920440c81150814440340c0d10780d081141000d0307958071880c001d681c46603040c000425000e90520041d80901281d130401d55542c00303008070020091401d440d0003550410b6803000c0096050b000138100720001000020303030200138424202e940040811041041c0a90141d00d0344602003951017004500035031010020314400d00d4620381003c0750a20311a00290000b030305021203415404c2c903400c0384141040c19205c01803009803030b08460000f90002e80c49a201001010901c110203 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 254949865 1250 254948615 254948627
    0x20a200d17010e0f0c04030f0b07141905030604020702061b150403090501050d180c030303050907050d0605060d1703010e1b070f0c050301021216051606090c0e0c0307 73
    0x55210070084011580b4240b48456070400080406900c03899960010b4410200c4c0300c203e0b8051940b203600154160007604150003041e20031100b2001040b807480040500701e000b101950501c0c1c0703001050111b07004030303800216440e401c00f804240d0403507002d1154400503911030001e000c2c00c0c00c2c1e0b04102d80c0403020041c040c9141008059240048080082c24007002ca5402031540040e0380342820650380c0c42c0d0300c031070160b4000c040e04080310f040001001240d408018146e5565402c4901070344c4d0510440e1290f14105441d04100e21415a011030410f0840c400100d40d41c1040360b00007001004980b084005880c3c2e864800d500c680c0b40c680d200000401131020340b00b802001c80d0004015561541404404004240103101c0ca20000c0d04020807140c18000300310b2842c4c107600103400c0290017592220000414103510a40030364032082d0540035000d00035403007446041510002202540500c1c81c204032a21984020456000c0940f40580d407018081080c0b09200b0015004070b03810760b10785580f442d00c41001001 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 254951115 1250 254949865 254949887
    0x412020a06030c1d0a030f06050a0c03021c1107051204170105010e040312060314161205030a120902090c03220c0501120e0a03030c0927020a200d 64
    0x2c1c94901007a071166542c0c04010341c0450301222080300014040e610000d02000c846604c01848511000000010400140c10443c05101c03128010300108208007026801e90141030702c010308400c130302c074400c1d040600680c210320f800807068940c41e403030116562112410320764070761046010108002010040130390058001c2c0d0174100300400801241d414503c03035000c2541c0103000542000030341c07904440d010f190303a4442c50040d944055804040618030307090a496480c1001a200085008480011307280050319000d8203580d84040914a0003803200000da034044505407900b1a03195852001c840141c03204c1030601e02032440042c215882e4540051604d000e00509a105030180360540b40d00320000e035542c10f04409880c02401c000c490050f0001c1d0000042000c041c2401c2107200305581c140c141038041c2d1019510404543e54402216210510f003060a8990304180c000c0d00082d52010742e01202a41c05051109203d20300a4012000e0190001402c200c44c80c4a01721500003032503c0105030b4001d02c02c681 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 254952365 1250 254951115 254951117
    0x1724210a05070f080705061c0e010516030509060c0705030d020d02040f140108070e060c06010b12011a0304020f120a1103011a01080c031e040614010f030221120412020a06 75
    0x41d4003424065101d417118154451035028800200b040c00f0243c8034100c0108041100354400c203c1b00b20207540040c045c0c0016a84260090134058440721218828000d161103803a07124014112038541c07071400d015031b6108440540c1c55002c00c4c08901c03c00b29540c001062012603008001d6101c40c100704440381111b0441c2d105103e10480f0b0946800c159030420354450780030391035040080c180c0340202c005c1490352080c1e20b0340e400c0500443c400440c03d903030100050482540c030301030102c069a8031960004107c03141032010b1070030490244001070051401c004666a6144098034500301c608121034102d117001c03070030581100c2d1042100202d894074107092040c101c001000c8031006401c04a80e40029140d0320307028202c1994040000001081a0b40b00003c08100c00d00315144140c040c640b40c00c00308014601d1081202c51aa5044000a8507042c0002d000081d20b03002003404c24902e00440080f07201d10360640754070352a1b015204401c2c00e000308150107800141040c580341c2c2d41400c0d00e481008021015904080 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 254953615 1250 254952365 254952389
    0xf07020d030e0d08040213060801020d050609011a030c04031e020102010c0f0905090a0e03040b0703170613050403091a0409060b0a080c07050a0f0f031724210a0507 72
    0xb84900002840d82c820041e14205000b841c0c40301c0c00400c01640b214070b600f0341454186000026181c1d01580101031212580340100301548443c070410040c0710080c4521034150207010003038640070040c1401035410201e10700328180b034a507a036912440c0c00544149801c115000407113001003956028041c44091861b140362070f034215258104050048202c9014540c0a610710000040f0700c0245175205403000990181100e4030b5550703401e24040c0380c0d0301c04001240080c141c007614031004800790f0a541d000720b40042c401c07082000741070501c000800c0000c1c4280c08102804034005a1525003010000c443c400c800011503075182043d0304941a503a0703940c0002c00310b010400c0198401648100300d01d401801b2191001d582d000e541c18114980a43d290300909289000c0006000704000440b0781100a4481c0c0c0700c40401140501d50720b90411000c43d48a951403812100c01c40c1012006044641348800c014200854000c022001b4001d42d056005101060303403282900c00e007489010814a401000715102e07038 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 254954865 1250 254953615 254953631
    0x332130c140a0e01090902011103070809151315030c0509030c04090326060a0503030a020c040c0c0b010915080304212d0606090e0307021e090f07020d03 67
    0x34032444a81c840ca46220784091084105903455090301401003400c1405450070b96141c0f100c0900a0603603007003c901140800210002c14440070080d501040e4010103d41d0403e4801e20038840c00750201100b040751540104032001d00808000d10880241c0b5562220141007850000054129881980352505000040c40f00020303d54000490108001e42940d006c0744020041c6000c1e201155584810350419070301c8900490150072050311039104002c2150240080b550790700600d5100e1050040110058004440000040c10950009544c000036443c01d0400d01c01c4a8448100c030400a0304002180f0361520b1040c80e038140d0080000c801741410300c024500e4945000151f0021003402076803401c2c408140c1481200740a818080000846294100004101003e03103c410007102240c000f00c0d209131900202048400342885110354409090004502e400d00580800940039407900d010302d0440c40c00403d0200c55143d035030303e850041c2d0050407400310904220328040e003460328020b0f00b001094646221 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 254956115 1250 254954865 254954873
    0xe13090b010b0a09150c02010e01030912030b030304170c04050f0601270909060e010e0102160b180a050304150c02100516170403110d02100807033213 66
    0x20303181c11585120301c0140d0750380c0e040509545003455584180d89902c0c6100c44104200d07040042110020320076a16400303603200000054048403031800e005042c02c15603841e030b81c01da540281d010700d0301130200500f124285681c40d440b030070400403414001c82042c3c102400400c03150a280c090701d40c01c0714050696003405d24020000034150314013208a003130490540c4412090712425083e13540013404245109105204071801c00102a282d10079561140c2c0d8680a20440d00b86010720903103501c1c0e40c0034041144010482e460702e0100200140034825800f440c801c810504402c2013003010f411512600103141c60f41e01d000084129040b2400c004028001c210100200581d15800c035020000050b04003551a046070038151101030030305543c001c2840c07140c0d140000c04a2504805001164410391000a80c180d82005224100d092014000d4009041c2c141c85043c8500502c4c2c42a40454940b50004d03500e81141407045456952005400d10b080300c544c3c0401001c841810247c0c0d2002c0640c417114643c6003c1d0380e03 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 254957365 1250 254956115 254956133
    0x1401020309090c07050a0f0537060b1011060f19090302151f05031c0e0121020a0f030e2e0e06060a1205060604020f0f0a0e1309 56
    0x20001e0710034402c010004142048400a50300341c15085801c5072180c0502d072810000b4404c1c1581e082d40c007407140c8048600e40e02144400280e0f0382d004540c0b002139000c181d440b04180d485066508440013929228032101948800751b80c00c140e8035041c2d5070b00054481e4a0001401c281010380540000c2011300200701c4801b80c41001140c9134101d01c0c0d0001900400307070800301e0600100d200d40f1b00c0032101300010b20156815040b95402004000d4000c041555038410800d82d0700c00424450031060702d038030506402c2980c015845810105e4041c105585000c0001c4071031030340740e48030010381e400c8650b010030310b092034545c0584082d0301201c513428100101070048100303940c5d078001141851307222004500925112061244100a444503900c428083c03030b05807034070f59910755201304d5206000b16440d0384000b41c81400041d03030582568005020746a41e48454041c00040e600c070482000c0c61040400c01810701d082084018401e40900f599218104a032100810041c6080c101d100e002032070415901c00d0114440039 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 254958615 1250 254957365 254957377
    0x605030115120e011a01020f0a020901180b0901081c03020f09090a060510020c1008010f06050309010912050903161401030e1501030c0e06062a070305010c090f14010203 74
    0xc10141110141481c801003d00052403061203203500308002c0b800c0da0464803200580301ca100342c00380c034980e0a00800e05941c4805510010394080c0d444001000700110039191700188500200010035588120800704a050800703a00c4148a540b210300d030700a000c00401385038840d08042e403505602e4030740100c00301d026034000c80321058030920038840480d83c54409035226100500001e0071000301c003441c4400c0651200c0c5141002c6000e030041c070140c20070084c13040164905032181e106039404030070305022003282d075500010f00a541543d0f981c4500004901c203486070314000c90060b0754483e03490f0b11100c2170504050481074082d4030f08180705e00900c60340d0141064509260800e103000980c5810040c1d145180c010790f0001d100782990150004810700905205d480144c816504a41e00c2545071401408010b01c00d06c0c5001e007410300f600511194181ca420341d400040c0d5001c070125400d10781c03030340c8900382100c01303880900700490004001000084030004402c00141800201a084072003080c00207500e80c4246 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 254959865 1250 254958615 254958617
    0x50a0801140d060c090e15150c19060e01140c090607080d0501030803180313030303090809120c0a09060302060a0503060a151d0906100f02150a020301050a0605030115 73
    0x7081901e0100e8071441050100e168020005101d441c9450b01c02030807080e001d0061580c1240c505000a481d01c0005810102076000030380005480101c00358016660780107070207006030b030380038903542c01300f5002c0c5035800d84103114080c18000603000a1041c046c0e0031104030b104100c9900030702104004915080200b650402ea406950043d5540441d280c00e55072849110b200c0134065240c070002000740141e0201a5100c0c4101c92441c2c000c00c60310407031050381e81c003841500c40740801c0c0c0b050061000a10a41001da601441000140e0415001000181c884442003211100c9540500c103d06402d14045613020006c084a0008000450846d00410720500c591400e440a1000c0040460400d403140d4656100500d80414000800800004010102e01c5480703001c0b0700514010b01c107044107240003400640500401040e400e07501c8086a019600a8019029a070030350182c4441080501c0004405030b12603940c44500603a00d6041a00b0807147c20019008102004810710050120360b0134228468540700403 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 254961115 1250 254959865 254959889
    0x8060d051c03060819140610090c030b03190201091d0c28050a090501080105030618010e1b090a0c05040905060a05060f0d0501080606010c11120109030507050706050a0801 75
    0x10402060b070207042ca5038001c02079841094000e0102005036404c803021107100c3c11880c603049400e940c030559100f10503a188120288200003c2010710101d41c0041c08a4106090214840c108100028103010450b03c030480022117334496242190391007540d40700508400c2038800c0140903c0304000000043c02002080c2c170f14400248000c004c40c445803418031642038500180d28140b01400001c1c0030313821001202c0b000c20042c400104c3c43e50700988000341070360f1000d00201010342e5400744003140750242c0c00c82e02005568580309000160381c2844403248007a0185911440e81d10240309101000000500c50701459141464081b441d0b90300ac402c1b03404403503c10401064907294040010042119a0701160748448001403080b00000604080c2407a0f0700b0300c00c010491a82c0e0b4062040e1607030411600c4900040303500c04807400280318080b01c1a200c000103400790401d0154030940c2402c552100b0019004a000810000d0400034104280c0c1c2c05407000f4a400c82c182a20b1343d00143c00d8810602841031800d031 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 254962365 1250 254961115 254961163
    0x80405010b06040b1c09030c08070f0c1e0b030f060d03171509070c110d0c031a04050d030c02070501050307021c0509040b0402070807080f0708030f0708060d05 70
    0x400350080c48100100419003507a482c2c3d282c213040c1903640004070341d01c0050130311500d2070004a00352040c001079a0701030b03c3d80110044a45d40d5401e9561005a04480f988880841d03600440c070f12000f500b0140003070f40707601c02074603084080342540034905a002a400c0c8000300100044605002e03031458000405039000c015010103440c1c02d4861000d042c000c500e10fa10080300b003110340b0b41d4100707580c04140400d840000f12500c503441c00315600d082109010f0500e29140c0b64040c050700300642e040c03441c1409001d00e4520251250b6520222410320460b191003440703480184010301c0024840d0620025050404114004068901a460350201d02c1601d060100c0800050606402070002c0c0041003604140207003c049070501c040c0c41d0390844640c11f0300a81ca403143c030f988242014402c6800c6250003002c03141c240078140e83e64440c0c80e0300c03c40505003050400d11a000c00104400055805011059000b081e946000d4000601c81c1800130036046c407904d510199100440d1012a50b00401c2e1483e440300c0440c12 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 254963615 1250 254962365 254962373
    0xf0b04110711060c030a0e0909030a0c170d0e070503070e131e0503070f03080a020c1b06070b010308090414060d110a0f14240301361508060114010804 66
    0x10056050b4410301d4000080c030580490307440320310752041c07e10480d21801c080d126030400669034043d0f020302001080d41c0301094401b02c0c11610100b00c12038a44200d403841c25002110758019100202c111204a5124800501291909001e404050211442c446403a40b400890072112084206030162803c40302d546820041c8010300440000280c100c0b0440359998128600b1408043c1070210980025141e100480c00b881c0680c02160b6031950050020003440541c580b18070540b02104800342e60090041015500083c0f03401ca00c0b42c02180148116900c8040c1c000a0005a8000107150030b02081c402d420801c00e903980c0000340c0541c0d608006402901d5200d40702040241c80903401c05000c00410741400540542c25900310b80c58054256248204401c041d401a01802c0d10340b0881d181f181000d0005000b10481500b40021a40c84071401001d2264903083d4404100d1001a40ca80c2c02038450b010711040000c021821002404820300401841d8034084031081110801c143c0d2a0402ca80303840400c0c148 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 254964865 1250 254963615 254963617
    0x21009060204090203090a020a050108070c20030d0801090b04090b01060c151a0f180c0d060b0a0302040501020c03210d060b0409090c06030c0801151209060f0b0411071106 75
    0x2038a80c0f4030003155a820401c142c1e582c1c030310740c8400407441800c10302c002096030b5110380841800382440d622400c11005007540d940c07600c2d58840056080007520307900d201c18a660300300981110f4900d262119415541050b451809440c00341d110903010724240852440010048180c17903044608a1a16800c02c0d03165107440d01400d15035400200d0090304180303081d241150075007a0171640e0007045030450628171480381405081000b400d804080340c0184ac00080714001c54500415404100075000542542c58204450007074110324004d500095000c02d0611040d44c04002688140713004500500031040f04403c0302402c119180514854a80049444588808207400100107060b51692040e2256124184000100340c8880107496045512344005107242c080d00c41e41c20140c0d160b584011007603007001850a82c013a1038441c203c08000e0392108941e00e2004520071075007050301c80d0a01140c48000c0c12440401d880c2e40c407503214815864800d000000d1845502210501540484192000c400d181c1c001091 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 254966115 1250 254964865 254964869
    0x405120a03021e160609050f0109080a032001020c061501030e100b03030d0501032a0e0f04020a170f0609010608070510090f03240903050d0e0f0d12050c0a021009060204 74
    0x2030f004840c3e00859081c2d041806c502c1078882c2910003c80d58200c0000445540034030780725200c0103400c00c41507940070a105400c80b86c0e40884091541c18040c0190000c182282c0c060000c0c20030b2a0801d43c140641d0039903001c190b481a030804d290510440044655403502c8440624445000a560302c20101190328140280e4101c083c10407004c01440d03a403800c008940301126a03901c7e14110f41109520004051030b0342d25016650006c00220315a69190701440d000380c0d01400503a805080c2c072000203491225084210708031000c41010700b400c08100c09140340b400c1e0000d070180e003007a4140300c0301303004a0100240740400c07554112100304c0e0454140b80c05407140c40c0a0307000481d881800101c0481403000021203005850f51205d9507440010302c031b000c0002102e03542c60006000070b004006e59680710880b40c10012007000302c0000c1e82e805080e1020654644a80e064610000c20810608402001c84a216081c0e000c4450303c1d4061030700b10010b0000351259090010800b01e1903481c0c40c12402d110b899411b03500 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 254967365 1250 254966115 254966143
    0x16021507030314010b040b04120206091e0306060307150c02130e160f030b0402010302091f030e070f0b032809030909050709050603060d050c090c0405120a03021e 71
    0x9690111400d00501400d80070b020140c0c0d40d10070f44000074182032100d04030380440d582ca0050a05250501c031110800036520182a41d02283c00d004030f46181d030703032002c042c103a54481070494101c5001e880245170801c000203108600c00e400a4400b00040b00c04440c0c0813000d1034080c41c20b00110151840041c0d007018521044065040c0392091400c180f007000104d84d0f00c421180c10a8141043e540d03405941c5000c2d550000502044120380440c0c0194080c1e0007801703889100801c81c0788005908403218008006040b158000aa10380c0700342034100c001404001c1c0a0403403180340190341810307c1c0c0428040e120140060100d41881100c04d5100c4580a980c050980510f0009110382c104902303008003c1403182c0604c400007490400882c01440c02030340c014085480240000d401d55a4500800c0400160084161414010402c910542da41c8201c8998418015041d02c207455078144001d00ca800d851005c210b510a89c4650548000b0940000d426000091014000e80134500c1d284c0c1d1203400c016950942170 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 254968615 1250 254967365 254967367
    0x906220912020d02120c031c140405030a1103030903041a0729010e061e010207031704080706050f07080a0c020d0309031b0506041e0e01080105040c0b0f160215 70
    0x3480c1940450401c422242d10313070071034903190321015410074148070350131206101c1d6104021905c0100b094403410444071000e50b000140744940341440e000700800c100c4007202c103500002400d80815420401506003141d40600031421460036020882d5070744194042c6142c1e0301d281e029043d01a03071051048035002680480c04081c5d50140b9002030082c5102d1130401c0100c00031250003c1045051030014034072542c001001d900120080c1d207004024032070505005030443c014a00040b0104940801c1d810400307a0144c559595640751500080c02c08540f134002c00d040110400c0400600680c000988607440e03080307041d669403410140001d41c1d5401071013200940003140b44240e0024540c01180c0f00d07080b640503d40b0402402030081c048546081a8000e0551240050005120050b041003c0c000140b04040742c80580e651035200000e107501090b440040a60345810420082020141c0386000070050300d6052402c1c5440303619080c490340698001200003a82c0703800f00700c05550b5080310162005d90184005 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 254969865 1250 254968615 254968643
    0x703060f091a0601031b0e090603030d060b09180403020a080313150203040b0106111005090c090103050d0f0305100b0319021902010e0a050303160918020d0b09062209 73
    0x9051071078120740c3c0f540400d28062030800f0341d00034000c06490141c1030307683d0300c030f42d06140400f044070106011b015181c05200602c00740003030a800e0300c0382c400505400c0015a4594940d07108121000e156426007100c21094001404000303900007c0e0035448580c041451912595905c1d400f150480ea01d24014184111000340e0030226880c0ba80250701681c020300a91180b40c0c2c0740c000c2174a100c0c40e60341c0792650079440313a59203851400c029800942c100c000700058402c451a6800001e207800d40030780050707441303405c54905a00e1942e001060104820460b040500ca285450010001031800703512500c4d45440b03002000a2024004013094400e40803801d03811512800758214021407403840800d4440550300e00400f10303038080700024401340103641c4003008614550320032860107407142c09504007000b4030484400200d09001c03c1c17a054416003000b4240103890365a060003400595943c80701c0035018250390024010f8940329883c00041940f0144450025902e984541c0d03c010181d800c0003810b035500203541 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 254971115 1250 254969865 254969903
    0xc0c06030a0c2d0f02010207050d05030601020d0306050a0501030207140105150a060c0f031b0804031b0b070c0306051b0d020d05061806010305101203020c09090c030703060f09 77
    0x1101c080140340707680350008501022103149400ca044100940703810300340f1000303a20b1540b0440a500c2d049003d4400582802e44070340d95285080300341c0c241c10001c900084200822035a04100010300701440340340501c1910700d4600429085900303070003401d040640006a902c10320000e8400e542d04289200002c004902e440d0719004018144400031300e1103103649400004410f4071a40304090844c0e08000001c49518841d9410f542c10741ea02d08003103403101d0400362034201051301c0702c014000a60003105070384007030610f0481c150b071000507503003002d1102402408208007194600e8006000d0300e6000c2c10004503a110030000884900201642800040d000220034040b040c030742e00a480c4c8051140c0c0c05200c00c0c0c540104000c001c03082d00080b00c402c038035010f0010f0b14541c8240c00403504084490346c102e0080303031100b45d904c2e101d0a803500c0076000b5a020400400d924100700c0342145c0c1c03042603c409044024003e4002a80364000382c8006040c0c0e41c0caa03005448410b089500c8042026403013843c4410702400601 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 254972365 1250 254971115 254971121
    0x904090b0702060405010b0307060e0909070314061905090a030c05010b0616140105010302010804081e030924011514041d0901050703090807032102030109060503061f0b0c0c06030a 79
    0xb134101e5581d400d042a04425040c00502d01056801d980c0728850000150020311601800003031100c46280300752003001010814201c45400206108030107420140b8040c0030104404910803440600c0618280c02c200c2c030b242d400f041d4020202d62524001448e1400350409034094812020343d50f03445500000c001c040200524001102d440c0f20300052190703280c03401002401c981c030034400a800b1034400c0c8005400503540c18024403410541c101001400308202c2d900e2100fa41007103400f65420f40c4500c45811910500f450000301a81aa0722aa12030707604241000c10700c8076003007001138203001d003102c170100e006100030066401400340741c0c60082d004036820710354041441059551103440e510b0580415402d5100b40924103102e600500e100e0314000180d83c0854541004420300910381804500310003003400c250004600a04042a002c10481c0c10700f410541880400340c8440d02805040c0700040c0c050240e0005402250300032903080b0344510216018034140203d5595580d8050000010881000c101d42c0c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 254973615 1250 254972365 254972371
    0x50307090306230f0f06130f0207061a03010903020c040b010306030803070c1a0402150304080913050a18120804020a09050a0c110c0108011412010f0c030b09070806060904090b070206 80
    0xf42614854031201c8201d04003210950303418003103800c1301300051001d0030302c20840e00d005000d04000040b44110711400004030f81000000303d40c0d55450b851403038095510800721000c020402c60081005801640d00a5580c1100464040c05241c0311148104540c3c025440140119040301203150342c0c1c0f4209030001d108898089084841201d01d0302d407001c50581c42d09542c0c3c0705a80c00f800480c005000101056480e42000300308848800080000c140309445040544141c40c1c088807000c00e4504050358100242e5540c0d00500b4000050380c2d5501c00401c041240a55020241e824040c500f0389450006c995084e41682040d01304604050902000204507440300e20040c0c0c1d99550320114655004000761942e0010418070700142da5140140000d14000d0300504d80c500c03004200c0710280d0f0001680f2820b6a40b4420003848482d80d4207101503c151b0140607035180080d088440b48590300c1c002c2005840d0035005070106d4013607500070030040980d40321503000b052041d8201b4950101403400300002540ca150031 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 254974865 1250 254973615 254973671
    0x3c220f120206160804080405030319080601030212150414070f030c0f051c0b1c0204180b16050f030906151504050405040501020d0c05070618030e01050307090306 71
    0x809110140600c04036110f402841e000c00c1e540c0e8501c0d1a0481111140c4d800341c000c1d41c3c008000c10000400d6601000104911714076001c581440405191014109403002844141418010010030200e91364000c940d6500c00d5540d20b042002c042880082002413041109403161a51101c080c000c00f039030009140d0034043c900ea5001c1c0100020070070201e03100c0700307120400300220348c003444501034044048500740c034042601d20b40041c8ac95071040000e01c4521005d001c0e0038004c9058455001982400d004010713012000c036041d010301d040d5941c0c40c0a4020402020701c1c0003903a820209400062040c02110316015004907400d482e403d0040c5990b4944c44195401014141c1d9201c1c40180f5042c650b07e00d20801d81c0801c40141840d16040c01d1001900d00103000700c41701c0d582000031030a040054414140c2240803660ba29885840d907242c50000c403515101c0351449129141c03069000268800940c41e19501d007844c2c265120b4440c0b11041d03071440010b8000034009030070030399068000c50110240304055151 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 254976115 1250 254974865 254974883
    0x120a060501170c03060f030304060f031103060612101a0405010e0904031d060c03030108070e0c0f180d050f0105091002040f030b0402030a080c063c220f 67
    0x500c0006545a608403100042c070a0008030000d4a411482809150f01c4203000d4201c0f0f01d0703010400f0009046038400d40024000c44d16840d440c1d500c89905110300c0c80d100130103800b0302c2d10b91706007600019450b0013881c004400303000360140001c46003000c110003031000f0a410404400c00442000079070900390004e028490020ba1a04108449071822501c5103005641545030300c10052200040500d40410a0904c00c0c0c000208004003408a00200021402800e040e000f80c1200c6080121080070f00502801000840609010075100204034400f11000e003019852149080700850300494403131030b6004030141841c010f01e41c4104880c6410340000b44610a518181c61084cc088d0704000128051030040310380e403801240c004d10004d80e0500c4d60680090001381203c40b284070035039481d8620741c0640d04400c0143c000600780501003085140d490b2880c4c0ea0a5040b001c00c00669000284401c201c802060320101014040340f41c0404140e1a4048003c2d071800c0810307010101e080044c1d50042150741240d403030007 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 254977365 1250 254976115 254976119
    0x40b0405190e1510060201050705030702060f0a0603120306030302190c03060b01050f070c1d070f0804020a1a03040c090e0312040816151103060607081e120a06 70
    0x1426100d501e201d400c041400005070180d404946000b80304401902d61544640e030110030001c075880c83c100d0b10034038482e505041d405042c25802820740758054070320418813505100380140543c01283c01d81d8005603d43e81350741590303145400d640151050354400741150300ca01c140300100355819009501500c1c026004c8516442c42010070a0f0006403118000d0030505c0100e4041c4001035050b00004150303e01498400d04103c8d0302c1c084030401b980160011212024041810040d146542c4c0880b03041440c0c68244104526010602a204041e24801c040800200d640050110b6984480600140c41350201d5110f01501502601c44550303c140d405440320303080ca032030015440707a0b03d01910a95000c100007035401c28402c41c07641003419101a00c202c440b80000d02c81000b1021505681c0b215540c0034180c001921501803203004100c6510490b035503180e003410001c000307403500d511041314252036100c003c19079201400d04040705507504400444503101800940306140850301041d19003d4080c0c08800c0103016 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 254978615 1250 254977365 254977369
    0xc030601050604061b0b130507150c0605040201180807170a08071e080d02030f0f15010c150e16080d0804030c02130603080d0b04050c040b071401020414040b 69
    0x90034429954011400c00c02484074620415a134100b5248003514509030140650380c07a00c648900f01c03941d08408030103d041d034040c45010844078000708094165541040002d10008114039041003002d400d03a51164089402c6902c11800800c0400700701484454680c1c40307510a5403a072034244208440c0350380f8011003440d4000e003c01d08480c0da65100310228a0008107a0740c41c130034407100781c03404640025421900d0001c24289002402c01d072051010041e560310700714000741160740c00549002c481ea500c5004001c80401070191100705070030b0900700b203144c0900a251001d003030b0f05003801440050741008044030310700c0b1002078082c036114a0004071341266a280c0001c581c1d1512482d100c20300040e2102d021501103806581c0d20459540080c00080800c82c2682191080d25100c0d403007107500f6400001c4a40010910f0f1003500c4010740125010300150601a014a0550081c0d0085da80d0001d00020401e00308102140b40c42024900c0030000d64990b0303aa410307042145054a010f1500490410202d21024 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 254979865 1250 254978615 254978623
    0xa050f030f12030a0e0601050d110d050f01020901120b030a0611130906050102120f04050d0804050d1a010807030f2003190c0f1514040503010f020d0609020405063906090c03 76
    0x1a40c8c000e4103010600d1815110800b03801090041650402003c0c012840420410f200c2503212103c11000965101c81890005125103051040d8a080d585484050380107590045441c50120360480800320f0030915030200c001507840b40f50b404448850340c0f6500044c02801580014044543c03d03001d913800c072500742c160144248075550140e141288108001d01c16441c042450301d410034080c1a0483c00d2036114800b140701520486000d0325920100c1d2030f4000d1004504c1c3c0d2450240500324007808801c2e2075503490007140300c01100d00424511038003074080e035170110308804403031500001000c88400d40c1c4401c1c42d1f010309000e403440c241e07109a509040440e0301c05500501c20304541103d440c0e100c512a100700700f110042c10b0800c111000313100420001036169424001e140a403442281c2c01641c51800e04490301c115050340d40400622801480700304101d0b41e0303400079220070300600528500d14003080302d0611340e84900c1c220700b0011894008960709070034000103031951040708285d085880d601414070800d42e503 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 254981115 1250 254979865 254979869
    0x9050f0604050402130507020a0807060f0c0f0e0103091103010c0908162105120a02070f1409010303110102040b030103031e0206010f1e090c230301050a050f030f12030a0e0601 77
    0x10812401740728145c1c006035445542c0c4441148180c1d9040c160030340e00c03a55154029031060728501d8440c0c0442103c094140300b00102112541018240d280c013078500a869408203410607418540c2c0d0307400300c1e000d102c004070000c0b21144c0010020040c0340c0b804c1c07002a0114100d40030f06c2d90107102e0310140f450b081c1602c22864058840d921521400d211051001c9800250041c40888181c01801000c4510886080141010f903995170040d040359401c14507a8029030000f60b1003180082c00d42004e0f6560398548080c44e5056a805240114014818076080b50281c810742e880803203180d0f00000008103159112001842d8140d090740032742514600b00d80200c2c1d4440b001e000e400f10510b140d4000f0401190f020454940c0c424801c3e0f0700e11503003641e0b0103d400031212611101c1010a80800c43d400c1f04040d00c0c0c087eaa4403d80c007100190840d410900803c0a1413040d014481c001e0303889201e03121580c0e904004415100700400100d82004560700381020094006481242010b030400c200c19040b0180410b0040c1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 254982365 1250 254981115 254981119
    0x5120c0606090402033a05070c1514210c0c0601060302090a0f15030c080f0a091509110301050106020304120213061d150618151309050f0604050402 65
    0x140e1901c0d40410000381e194040e00c00c0364144902e28110a054a41411203a03c80d403000700000161800d19980000940d05000c0300020010200213400000e01c050b8007840c2504e40b0700409902e18140800d01f560034003c3d000001c011103101080b0b0004c100b10840240440345076450800d40c15883e42c0f041120746003d2894900110f800501c0140000d40c4a42e01500c0c2c01070006046024443d81d0b000701c41c500c8441501303d005d81c81d4050007601c44041c0c040c01099288213480c9002095031510159603540c1440c05004085800e0710307442840c0501811502000341050b071400e0420410401b032424502100744111090f009508220000440034002300650741151525084c10300d01031610f90070842042541c038060500300750b40d0070000c00e186113110380b00e010001d02440040d100c0d0610783c0314401c2e412040070075144194810000016a000081c1c5c8000c010070003070f503585030000382c0c4000002990081204080a20780500e800191881c0325412190081002c82106051031305c4072418081a980e088030065 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 254983615 1250 254982365 254982373
    0x1b04020a051c0f0204030506010e0903090a03030e130e032703070308030c070f051612081210081b0109050604031109070e131d0a0203120d0b03030c070305120c 70
    0x1a803480d00d0614410700c203011050000f82503000310805100700e030060341068841f0340c4a01c00621418413500b002d03640041c440c0d001141843e0042d8000b42c00d100f03150200030200030800c010b105581c2c450f14601403138180300010510201204141c03c981c1c030340080724152041131612240400411015030303003120b205009805000d04c6421034551100d0f0ba440903010011038031040280030003144100c0c80c1040d0f054404c2c3d000d416600039401c442070360100c60b0b820081e8620003140c9614001400c902c121200010302c2910581141d45141c50000b045040341e1041c0e1841c010405440c03502500fa202441c0003003c241c03a440022034403441401210b000300d0200400d10b01070150700440914101d120180c1c040070700d181c900d0301081000040360001d107102d4110b003011500d030305041c048050300d503401f040d000001c03800810443c541600041e0b640c03a0340700e41121501c18001402558000b064202002501c0e010f01140d64400c441d42c555075549515100a484500800d804c545003460030a0860300a080000014 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 254984865 1250 254983615 254983627
    0xf0e0a0609060f1101060b0304031409060405040f0f0c0206270c040e03041203050d1107111201060506040815060d0c182a0f030903080a090309080703051b04020a05 72
    0x7a50320442c3c084540b02884a00b001d540c0c10300109008101c01340003030306242a26410300740b401501c481c20000c200b0404602c140290003d98a82394107503421558125004120b1901c601e5a2800a2100ca01c9500545003006415411079800103802c900500300026084440c404040c46501100c2070a004020143c1154032503017114a0180c00000700c81c04142c0c156460146c1d44c0f61f41d0314068024810481c04101e0100345900b4202061041800c02300380559440d24125071031b038521070703564050b1032868400e41000c03a146840020940c0002e01a1001030b02681c1e840d6200c4201a41e50006005e5600745413409900203882410100e58101d141a888212104086d04008180801c0c1280c040c0b100020742c1d580038800c101c5400340da604d56015901282010400030708070350003003110b43c600005070285820048004c002982c0603031026400302140400142107030041c64212410002507011084c0c0e44a001004000c0c807501003026514004e4044500242680d1007050105a000b44805100468400d00c09 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 254986115 1250 254984865 254984867
    0x708100302150a03110301080703120306050d0212070512010905010b01140703030c030b041a01171317040e070206150108190b0307080304170622141504030f0e0a060906 74
    0x1400b0b00e05043e05001c200841e01d001091748581090740440700f982e001400400900c41c0d120502c213445541403509104076400c1402088818029190080c00784c1707240710a407480c2c010b00303008140180c107004100c48440603d1841980c00381030003910642c0e06502c1c2001e08180c960150008072201911581c5282c10502103403420b400a000c500c425405050b01d07104d1400d41642c5d20702c58085140100b910035a00a4110000100429034015445580c1804101840780e68910004c035040802e40c804501c4007106c02c51514a5681d00882d0710a0000502d50010301041c1c2d500450002e202e9481201c1101454440400440c3d441300103072040d542e0070310880030b4070001c42c2090300225260745015084800745075440c4045d600c2c0d40c0c4954090462018079060b03440f02c41c1002d10000b600300039600c000c40c0240030b0040a20f6040d10f83c2813030051082c0003d00e0310400d102400d111541100e045c00003110311529060601803c860034020003840060602d1004801c24a00050094150b403142d5480b1102c80307040c250 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 254987365 1250 254986115 254986117
    0xa2a021009050a0b0301090c0305010b0f070501060b070b0f090c090609090c0a0b0a030b06031005040507090e04060b010f0c03080721020c030c060702032104080d02030f070810030215 80
    0x3020100300704088030045240c0d00d60440caa40101004d500c8a03589614001c240c404039040180800c0400d81844010407a4003a44002e5411144425004950342e404524000303004249a500c02c2c1441e64002c1280c0b0240480c00702403070f204250b07080040784182c0e40d00342c8a54690381c010b0403040e030181d075120101ba500e0526501981d030003034590048a0307880000f000041c1d015841d5511411203402c000a038003096a0341409003680100080e5030340c9017103040001c240d81c03002e48a07025040c00743d5940d078000b4038a144aa18541d000f8140444c8903820740c1454103141020381030a12000d40880d0741810390354240d81c45465030f07180c0e0700d4050fa80c040454582c5001211000300040f88660720600c85540c1c01c8540701c4c188020213003250104000c40d034500141c60400d0610308018485401c0d90801c3c1300a00c18420340b01141c014991032207c10303840a80d141e2928260340d00840c01681c030160b2011040101210541010300e01488070360715914021344d1020401d18041380d544c0070007904000c048285d070541e911954 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 254988615 1250 254987365 254987389
    0x3130e0a060b070b0a061502070902070516180b0a060c0b04060609140901050105060a020a1b2102040f020301050a0306092d0b060303041401050a030f060b0a2a02 71
    0x3040c041100c9540e0340c45081c4540040d82c041d112a151402403129580d0030744200c90080c00302080c80960419a00d0005c2c0d102c801034814120103540000703141080010502480445510410104801d5500c0310b6000e1401043d1030540030100380340ca0001c0c56145060b07040802201d80c41d62740d1085070b441c9a1342d00380b08014040c00446d82c080d160000810680010b004010203074a0303181d10041c0c00d02c3c110161030b00352601a0300c031b80d00414040010601c56940421225010754012101c0103049000403481c0280b40c070301c0e0380080019002c41813101c080c8081d00fa00300300064000c50703003802584e0b908152482284020f10809a020540c01820800960f031504240c51940c007450381d084604000b00c00d445178040004503c202103500d24041c0e40d0411050007001078103c98290000c0d42484e0508520032150041038400c1414440049035100e10a807098015030380180a541050120603501ca6410078030750021035165001c6400c200084c0702d210000100184070700d40c0000007844407081c81e020b00094003008 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 254989865 1250 254988615 254988631
    0x6010c020a031e0c05100f05130e0c070b090d0f0c0f06020d020306090112080405010305090a0f060f0e010b0a0b0306010512040b040b1509011e030614060f0303130e 72
    0x159000003c10b205104107040b60402c84204001003105141c50018015180c10051045200140118040b64000c421900300c4103203003404c0d40d44d503642c03003410122070810741e01c8149602610001c00c0303284000c14000e01f08043c455400007501d900d8009500e61501201001070f000101907402036206544540708038620305028541840b0400c0031500c8076401d076480181c820308200d40003c2401258140030000c40c0c01081c00e5100041c0044180d92072031030320710480c0300e002d04040e1664085550354034203010f9015090344c400450b120707000c0d00d803901c4405400c8506c1028602461701c940d40114041c10700032040c0c44c3d01c0040a801e0010300f851912605500060503c904001042c0860030300651102c0606005e94050090803100d03181600e804000490002c1c040c41c00c0d46038008030400c0319103c500790705054900c12200c03030001c0c0383c8071301180d585c521690780051b08a9040c400d07038044c0005003100f0b803070082c0001d0725030840c005601c00601d5900e2107138a5100d03007514101842048040d81a031071040d080894 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 254991115 1250 254989865 254989879
    0x304080a1d091b0c10020a0e10050f0901110f060907060c030c060f061703041a07050613050c0406031406090f070e04080f0c010c03060503010b030c0d060e0f0d0305010602060c0306010c02 82
    0x15425442c174100300b005014003090740c00200c80754540e0f08100d086200c3e0358221b565081d032119091004000e4090a40e034014800c0000c540d1a5090780030385c92031000d41c0c4407001290000720304d158115558600644520301940541c040100d40540321741680c66881c1d401d034903107000c42003d95481000805501c011403d000e517503188d000c2206500c592030f009610f039501d030044d070f04c4501307014a01c03400132220004012650000c210300000a00701061140e4812000c10060320b040e03d0070f04085050406072281181d0141c44d043c004030030401591500f0305000004406c650003580c0d103159655480d42d50400f100c06540c0300010801c144403c1d159030680c8540301d0320809081600d49014117a258101e00e2440c0c0090b510759000040c07442d0f243c81400001d1104a000340118410140400e484030023000c400d90054680d09505820700900703400c401000b00700d2030211201550301d409240c2d1181e803a9241240000e04143c0001282403001403602d009040298442d451a1508001521f02005c680300072a00900 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 254992365 1250 254991115 254991127
    0xb0a0c0308040f0c151b150509011e02180d030e0913050303070504050405060a0b0a0320040f03140304080c0f010215010801021b0105190b13020304080a1d091b 70
    0x1300c06801c4000d0216084140107074070700110140500b04030811301e0b50f9402e400d002401c04a424800c88180da624103034000a0103440c4e842c1080c0c050090144080c08465030102c0100c90501e60b54000d00400440000207882241035500700000c00d2520702014000a50307004501c4010f10b08804810b422082c5080410840030341540d40a00b5500100c3d40d640100b000400d0800c55400d0070300409a021008444498490f410500d0018030b50055a12000030103641ea03134031804180b102c421448148281d400c541e0b80b12583c0f0968400078440f075010450300c400984001c40c81c0c0c020004140c600392181e11000e0540e40e51108140007501c0e002ca4001d40c11481a15602c1e0098040384603614082c005072400540d0f074039110852092080e104440a0105a150604012001d084408441100d810740b41c800b01c0e015012000203032034410900c3e440410075200005100c100000c0900400c0b0301c045030388034143d14103511444100720003c0d5104190b000b000140004543c1c18030180403101d401001c04c0041d080c52 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 254993615 1250 254992365 254992373
    0x1b04050c120f04030e03032106030c04060e0103060c0c05030711041d0d080c0f09090603070302151806030108060703090204021b0a0212010b011b020406030b070e09010b0a0c0308040f 80
    0x210540b20105041c0c0201d0501051582c8151004045207058008600c0c0c000708640a0400501c1804e00c02c600e58000c2e001b29046507018850390380c09000043c41030181540f103a0b04002040001e10049481602d000e1008a43d140949090071074290804007840c106459034840c00688150000c85583c89940c5045044081807203001c058030700c01e103007001030009074024200038141c040d014220318514602400040c82c084440003c42c1e800550549801545486140200f4030f405210382000790302c0201403020b034690b2022000034080d5840000310fa501c031102c0c101c050164a101c28001d00183d50085c0c1d00080100d80a030304022452803005e8001460000c002c1240228030300107061801c05500048080001c0d80350000d40f00d46583c1c00107000f001400712500019240c030b005032001d02c40031700141c2054030640d9a2680180300071500500900b4440c1f8102600400b002440485988075800300400401e9a10141041d00d11040441c2c070b80d0b0301c0709402501c050b5042040100115515456010004001 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 254994865 1250 254993615 254993647
    0x90c0e06190305010f0b010e0a030318030c080d021605060d0203180105010909020906040b010c0b1305060c0405010318121b021807020d020a05060408030c0d0501180e1b04050c 77
    0x254090f000008040b0003a13031110060f2080c2c000b80303504000c07601032080610f6585a50351000c883e41070170150350400303050040c03103110f0a0079403014181c0000f06000090b4603101040150710303000607038280c0e0b010030482e00602c1c81008080c00780c642c00460a00060040d58a0750f401190844022041c411003103030040f4100e07096803400d0300480c1006032107504110031030420074200e80d08507000300c6050150b1082c0d070000820340801d01d003018010f405180c0c04035441c0700588504a40540d00a402e1b030b445450000c916101c1c2d9406445400d000902d0104a9a14549031100d01c00300b0039884104000e1381086020122003081051031000000c01c410300c03429006a4800c18950b0303a80102882c1c01070b092038080300180c280800405400c2c01d40d04080e030a40c00090011841c02d9009900160320780c0c40361a110f00360703c058024003070680f60141c900700012808401060a06404442c542018800d081041462584401860003510041c08044034080c0d01c5280c0b079080280e000442c1d189040c100104500f132440c0e4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 254996115 1250 254994865 254994869
    0x10e040b220c05100302070b06010806060d060603090c081c03020a050903010f050109050c030103030207090f0f09050c1212030c0708070206070b1b0c0c09041407030b010810090c0e0619 81
    0xb12444141c4100124100b042c004030a0030494241181071088580f250200e05a008120303074100010b8100040e0a0307910702040c1c420b100580c50703003082440e0700c500b03000c2d000301200c02c41032310415a0000006005240094621001c02e914002623207124003415042e8003a4001d00801800e0190910103840c070f03a1400d22031803140f0814100040b416502d4803990104449000d010100c4a9100f00b0050002c40d40002d41b072411101c03c0100001d01c684104070045c020003203d040320103807034104030b00c010a11400041e40d601d034400403545100c0442e000085940e4800440d1517403811a0f40c00e000058006480070094407009024105041c60405154000b44140e81700b03e2044500360302110500c441c440004072552403606145041510306011008000d680314494010076200e001c910000504221004261113900d000c103400700c9050a85929225840c0d15090189044030703c165000080000510f000303910f002a00700844421060034445c01a40c070040051185030809071031746065070b1290308001c03d600 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 254997365 1250 254996115 254996123
    0xf070f032c130606050f030a0204090c121103090d1101090602040b0307030e0303041716060e1b1c0308071707050c06102103020109060e030918010e040b22 68
    0x14072103071120030000d00310005400c407018580341110601100760050111090a0f945c05141c9890380d80d03031340114029100d59008400d00c079007030000301004948c03c81050900c42440c0003080c0060b0a510340030b0300300d070301040780c070784c4140d40c002c2024001301c90081940c000341c0456000003241400c8941c440000381c0c1d0040c2d1000180c50800410000445d5052049601c8103018402561450819458280042907040340c483e4003840300061280950040c224611603c1c4d41c005000d1082070708803140140c41d0a0106010303201d01451004205043c60000760016032003040d00c60075001300d201e40d242192404002403942c41482281c0c4030082100309414111032081807181c0e00c00d5601e10b5141100d40c140100035050701c0c081c810b0b002080c40303060030b10f0a1012900707030030128114400c00c0794101240580054680588198600064102d6856020000304140d0710300381d910f100e280a24001d08040b83d2400d1040944408020000c140059503440030240c00c4056881400c60b110a240c8190400010141e0100c0f = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 254998615 1250 254997365 254997437
    0x140f0301050f010302030d03091101080606160c06030b0a1508060105070f0c2303060406020c0102131706060628140c0d0908010e1f090f0b04020a0b0f070f03 69
    0x5c600c0e040050698480325468107101681195039103041c003400e00000203040c070000d00005040d9440340300554000e010134503400b03e589861402c0540002459010b6600003d04201442540d030401314145000c5800060b045c801c41ca142010456024801802e00340c1000001c0242a002c135080411510003540201048000c492800800181140c140f1806040040780540030b14405d40e80400c0c00740c0e0054001d000540c1c0c035002e60864034020b219041420900e02505480031904500d8040014000500901100d0322503c40030f040250f82e0056009003070203120603010b181c1c030006091020b10803564070341c1450411502c8488010500b0741054070b41860355071051516030082030b4400c0f180001001c2c00c00003003200f000c80c4034180d525010540309003007440303440703141c10400340f641035205100303064214026085541c610b28101000d440300b654142e101d0144440b021540000450880d0a00700c01c2506d2649041748956604030f4000d1762010075800d01c1038030002d03210782c504120b00c43d40b20300303800381d1500b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 254999865 1250 254998615 254998619
    0x1a07050406032304030e01020304080d0201060302031b0a061809110c011406030c090c041509060305070e01120e1e010e01060f050603071103040305120703030c0305040c140f0301050f01 81
    0x7000c0743c0c0400e005100c0d405080c00034941c001012504280c01c035402d45018085516034800503403031445540d00c00d41d01031183c480318421055041d03008c8001c1d03a10850942d501c480c5103600080c2146940040541c1c86009000104001c0e40600d40d101003415072444030a200300e65800d81e00044034407080c0710400d0410001003100c00701400b0311480c00c1003480d03004042c0c801d040110100340ea680c50013401c1da00804468003c1205906c1e40019a0010001101d0f002205018040010502c2d440c80c0b250030701082c14480810440d60107103078580714444060b91180150f07a041c140c07481c00340c14950080c0005002d4600c0c580b0b4440e114001d0501660b417410000b0401c0d00c0718500390341c211100c030b6000c1000842044070600503903903404102e0360800090318000190080e007060040c00d6108944c4000d10381c1c4254041c50542445800c0034000c954026201001862540c0800341c041e14011a00202020340c03407542032160b0140d81c540c140f4100d50103400e440c00e01e00703200082803c4450950f02d0162f40310080d001 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 255001115 1250 254999865 254999867
    0x12051b0d120e0105010f051302090901170f03030105060307120b360f0a05100806040f0b01360f2a02030708030f070c020409030305071115131a07050406 67
    0x15215000e01d00b1002040990300d0304030307a00c040c0801802158402c480203c0107048081e010b4050714110340d0014504d1070196507441a101c42003500300319504c100d00071165075a0601c48084240c1e8103c84010781078614590710304000701c92144030801c641303a032596036184110791074861540c0c40414a101101c44015807019104482c6541050352220700311900d81010400b602049514241d0000f1000001142035107030014046d500c8030b40d64205001d40c0c4140010442403014005c0d64517039040c0100020030103641ca030f10081030000c4846401c0050844140010079250110104102c1c2c0c0c4020744400290b4403c1c001040400c6e40c694104c42e03456042d080c0d40b10701e02e8103600f858101200c070b02800118509525070b81c450a15010040210380308407074500010704054010030301400c140740c0c010b004004008c5907240c06001070005440840c00103801016134031146600150111600b100b100804400740d0750710800003440c8481c01350884030440102c86011086d03041c1840c11307000300348039150940c80303d0800360 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 255002365 1250 255001115 255001121
    0x1b0c07240504030b0606120702030919260c0d0602090306070c0c1512020a080f090607050f09040204050a08061605031014030109051006051201020712051b0d12 70
    0x6201500102440c03089440180c004088078202da5203d10907030751641c0c489000911500032007116035602c00d003510400c0f2200e03601100612504400306c5d050b019140c1c0e66042da400b45091409144986804611600d600c4090300d00d4216002c03106800b1101c80e8001000412100c2507582e84c125040d94021503944d03180d14041c00b82d2a445000b0b844c0209916525440d02c23291011548030701200765011060601c51188680d021420b1003a00c41d0043d0759809855100404001c402c442500c520a403100124214200215059005501c103607980c5003070041219107400c8076403205518a0b0321030380c2004001400e85400c2c07000002002d000740544124580307240803540e1150b800d07055204200e010403c01c0189601c1910402c20b030350306040e0010001100101003070060001c0c801c040d10911406040b158206074540040087d030b10113441041c404200f00029600742e02441d040203040120b80050601c43c9441503001c0c0142180c105032003203029402c0c0d000c0b03a090070306c0b40e80c450380001c034100c2d400135102c21540 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 255003615 1250 255002365 255002399
    0x2030708190228031401060503011505030f060601080c09120a0302070303090603020c10020307030f09080a09080a0c1707090e031e0a1e11070b120f1e1b0c07 69
    0x3d006444030508011640c020418180002488220140070040c54100258480c0d0040d10001c0c00800000000c00c0ea4000fa80030700d80304603446445820802d9a0410020a5245c058070068642d0800750304c0d55460288036030000c0c4642500041c0180c0300d900042c00421541c40980d000e034015000c5c0f64290f05008280c18496085001414010800f07094148000103080e11440145d4030300580303d03128103400302c0182980e800040400d900302107041c0d0600c402c0400a014400f19034407840c2c2e0480d034410603d911080040005040603100d00f100300000c108038508083c07980c4100042e210804c0e106c204807002c45001d26000800340c0d1021030008080412a01c40250040c0c0c1540c0c60750600ca4403450050514074042c1407000c0b072500980301402c00c14018182d583e40b11000c0806d0f14001502d50313140401c603421094411070885070304400304804d035010307103c2d0314000e8402410a45601e03002420b0b5006480c00503081c070f0320340341a940d07291014906080c00f600012101c60050031540e890b01e460081c8048180c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 255004865 1250 255003615 255003649
    0x2090102062802192003040312030b0904060f0609061a0924040302010e010908030d0e120a0c05010c03050108060a021804021911010204080d120b04021201061e0804030c020307081902 80
    0x5800c003052001702c004191000c4950256040744841c080c88400c03806855082842d58005a035241400708100362504400c00c07421841000b04030455651840c0001d5680c03a21403039098400c800344030f24206040300000d0004d030002802c80c040d404092200c102a418850244481d50800460140110f41c0c1c0103451040128003440e210031135a05045240380c981c441c00d002410398a94035018092028000d0002d06012140141c0b12510394610350340c05010040c0a420840c2e55500c0c2c0038076240305502910405050300c071207100404050303450201d010005d60180e01011001e20070014081c0f5a540ca40c00140407010151501c415269000300015101101071040320325964014041448084800503044826500a14028903060035640d400c1c0b0062684011040d0444c4c0005a01d011090074181107904941d40b6a4480038191445200206034241c540c0102002540c108003090219200e40080c00d80c8230700080079182c5031595652322910b0011110300c114401c05010001d031080d0328001e140c803401c1001d0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 255006115 1250 255004865 255004907
    0x2030106050d0e070308040b0d0501092c0c090c0702010806090702210906030a020405090109060e040b2706180a05070b0f0d0f0501180209010206280219 67
    0x10400050818003a6501003030300c083e0f8410700141014800c008100c0215040100c0079580d9031511f404111a51081400042d1141004000142c5000900c80c200300346018062501d03504104044010006c12114007a6143d171042004004481d552601404d014058082c1c2c21991100d641c40054a00d00c8018000c600ca280e1000812140903004207102c080c1000008841c2d01d0b510500c500c005103030180f80340207a00107a0110420036018800d07070052007a260704441000d256070366170014105442c250b00030103900349208804123001a91f82070409800000a819054030880c1440070307204500c17528840e850550b4004010b0110480d54103811840c420700d0080075209031942c9464940d6103d10300d108100b07119038005210300714940c640c0162080d003008000d060240c1401d400b40003014000030f00a092000c40c4101c100c00040400380300300d4801d01c2c010b03005489143c0e503003c0d400d5089143e008868460118540006510803111703c0100f0400020503030915a028050000400700502d2001d04e00342d01720 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 255007365 1250 255006115 255006119
    0xd06050118141206040c0905180a03080c07020d0c030b0105011106180a0209040605040b1e16210212060a081e101b1404121403091810050301020301 65
    0x880c0d800700c03009a448070302c24600c005504601203030340c03d500d003100c5400c01d0184400707210130000002444030440344a08028000c0762121013a240101e8100102c980d12a40308009800000780681e00300307a400a6020082410000642c01151800070740c082c045844d201064024002c00440c1320040b0b02501081c82c080304010344600c1010781d42c42c07015001503509c50090102c0104500c0800140520076030141081d250b50500b0b1801c103016000658084038002400000a08801c00541504d001c0740b00010340340f0140d0b00c46042c1b100140000b0f500c000c4c06c22411f11015008003140041d0070400d60a00c50006075134a02a400c50b40c10121301804691140718203800c200320700a0001542d100c80201800f09101500810206914003442c078081c01c4402410322801f42004280c2d090024a41d40c500e895000c40300141603507840d050f20880c050030100d0030800c0040c3e404101c035003048804d6008a0f4040703a14000004000840300341242e66070854130808142000b02200c0c901c00d410000385016002541594 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 255008615 1250 255007365 255007397
    0x603051009020c1203090705060f0408011121040f080301081b0f0603041e020307090c120507140708040803040b09011704030c030c050a0b0109020306040e1204090e0f120d060501 78
    0x1c110072136110b0f0740e01001086990b48180060300090200414440e5070f9810b84010502680103486502e0095180c203949222030b40c01c480840d542c0a000c0b1800c0004120462000b4850740700c068420b507081074100c0ea42c000069131503001140604042c10043c442ca01c40c0d0000d035115034107082c0120b409038980e06401800c0d902c0f5142980e80040c6d01c02d85085140003540340403d0b0401082c580654188948440042e160059a01c0103aa810881d5501c2d0b1264107090340b0740307003130304c900f41c94181c000782e00071011000707194803034020300a00d500c218003131440c20340d07100310761846c40d00640c001306c0d407038240051070842035030304544d9a400c00d403989481440d95103010748014055141c0c880f00a002d021081d400c11040010500840e20308a0b400551040340b561101d1014000303400448200340901d1400d85908540e910000d104642c55600300b4080d45012304017070f00c20010b00b035110780d83c2181d4440c1607855040c0800a100b11148050590b14003500c03003180c0018001030303c14550000d07042c8100900009006 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 255009865 1250 255008615 255008623
    0x60a0b04050d061d07060c021804120302030603010b061801081b12070504080105040302060109050a02131a131d0a1e0c09260c0906010c15150603051009020c 69
    0x14540200c0001340c0014007100c1c075500300c88140303070015003802603280c08030311301c0d8001003051105402541c0ca80c0100d20041d060b10b4840a0554010344203807070351006564141e100350015039101030050008106410a40c010035015042090a411071107100d4003550358650b802007040da4080da0640c400c0b8000308155440503941e00c210890306085124a0002600e130b0385c0254200d8004104100013005149010304009468031020300403440300074148000308001d2196070003650904010415062140361610380034821448241d890b100078031109001d807804100b1241d40f03850007400360902800d00c2c10042d258150181c8801042d110400c0c4c03400800380c0740032003105800443c20140840004010521305000c0d10405401d500c01c402e40844c00c2041e44030500c040c1d1a84294688010403108413206540411041c0c01e421070722140045c1d860951100030900c4084c0e111010040300a00168541300e2041d018104452904500c01203610f0f182131000500120125034010402a44110f041035070307610b962620303 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 255011115 1250 255009865 255009889
    0x90d090603151706100b190c06060e090609010f05040b0103080a0909020310030302070902030609040f141c0f110d140f04031208010603050402060f030405150f060a0b0405 75
    0xc00d0b40e906149141ca505962020b4041c00381482d950704000a5140419500d52040301c4d1101100c3d4030700c4c40000d0b074420141c00e8a0100d240d44004202041c101001111440e038181c00a03a000364030b0f482c00080035205c6041003401000250003500051500c03c99850030755004070318140f1120b2404041001103003000c0703800c40c1541c2d40800c00300d0350f0b01c0301c0c0c0c6022900d50142c0c0d00a213005502c000700744a4181840700340001280d1198003620050307903486081c41c04900007282e049810056403c00200080c42d01d030240b040e0184581c4000c0041481620301a00d0203140c0c0420011002400031710a1100d5080480c800e0365800b28600620344d03184080c0380c0343c2c1350404107500005028440c3d0504418180740d0003a18007002040450686a56407030a01c1c1544088074444140415240030010411130701c0390144610958020b0301c0d052a100ad050302d002c1003031f031006000740d41c5030180a16a80042d00c038400e2090040b4003100040b00316050001c20030100001640c4082d407048000c21040180e5196400d1003a4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 255012365 1250 255011115 255011117
    0x20a030303090201170114030d1403010b0c070f0801050712020a1d0f04140717070507110d060c090f0f0e0a020d0e0321150d02040504020406050607050c0405090d0906 73
    0x2030a07402c2480103844811040703140340c00503c40e40002213118016095240d0170f03036104504071800101141001c0d47c0407030384804242c901040800060108030305101c000c200b0100c062081b81d400c1651400b031900490303940d420040342d69444009000c41c0304c4d480092005008500d480031440c0900b50a030140c444a080c00c0740d290f01103030030340170650955540c022030148514041c1c41030142d0809446a4480540200c6040010030074401e6181c1c01400b103034074002c1c0b01d10055100c0c94a001c025440b190809011100c00c668407060800100001894a0048201d03103000c2d130322010021070a01c42003002c5551242c0120007140c8a80c00200f00300c4484000c1260060401c80d0300503501c04441d0801405024a00745a415905c000221280c44c0005080d18071440741d0071071901c0d645d988880135884401004240d03410303848041002840c0151a01c1d40c0000c0c0c1082c401400001e003941c0e2103010901c0f40d000b46500341d80036002444140b20701e0815004940d805a034141c0505441c4144141c05800c903805801100 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 255013615 1250 255012365 255012371
    0xf03050c090d0506010305010c2a240504060b09070e0112060b1605060a1505060a020f060a0e011a0105160c0515300a0c0309080705010c1b020a030303 66
    0x284508003100c00c41c1e0320000e001c1e01d404120480b0f418400c0d0b1350380c405c1c40222115031030410304080b6540703d00d1100044542e2414100d0b136150700e03200c03420742c081c8412409a404158214102c036014140d248895030740b60480300040f4043c035040c14103104840c0d140035200e026174500d40801c00c2c810703440040d540c49000309007080d0710b45880300c4070ba00307000740709642104e9240c0c540081c111700c0041d40e400620070390901c108102c0d851a600d101f050815515050481011030b035840c41c0a020620f084005003000103034910403101c5800f10305104e2032506005456042d070715681c480100003100300070302598001d040c0e2207505040c0c070800d00000a26500c01c3c0020361138106003a584010801208144a200401d401400755200130500040d168880d0301401d0503826000601d40003020906107035852100d08407200d500c5001e10f6855103c00c0c0050100140c244041554490183e4001040e4a0117001c1e100e00820000400700912800074000c000c02c2004070102d00c03443c5454100680e11100f011098075407500d004 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 255014865 1250 255013615 255013621
    0x2c0610020106050307030f0213020403150b0103090b01170d08090307020d080706150e0708060d020108060103090506010807060e03280606051c170f220b0a0e03011a010f0305 76
    0x200e0040805400c6a03134580505c403800001c0c45025402208000e0084401c850580c900110503130403840380d840010f21000100554400041d2030b54440640a10107050104919001e65101d17034102000360017512101c040c000340c1c10781407030081203c202c5207540b504229046043c40391000343c2e60b0081000c024403405851100400300203022042d10491544540180142c0c0002644403d9500e214060741c9000d8540100280e80c1500c512100f90150710050401000c001160b00111010030000b00110306040c0c4a952040009108100490081000a025000b000d013030090042150428000e0325100354084048962030302c44180c900c1d95035440288501e141c0c0007243c6451009001145d00a50380114544811144418007600c49040280314100000c404650307840804104c0c0200c00403140c25440a000311004100c560300b5420101112a5410300d1440d82c601120190f47d00000f00c1d6000543ca440380401181000d000b001e0f541d481e110403041c101c00343d041c0000d0a51b99160380c60002c040d124404 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 255016115 1250 255014865 255014867
    0x5060402060c0102070c080304061704020904150204120f0210080105010f03050720250b07150605030105041401060515120a1b02012f0406050c010b030106030c2c0610 73
    0x45406690b80701d0541001c83e61f035111021740b20340051043d00049055030940e00b100131002d8020302c1c4543e50050255609803250380340c50f078014445600840b030031582000b0208400e469801000c1c0b0051245085107404445441404441d1080721601814030400e00b0050206a070840d07120380c0342e0740700c46c9000a0559200030b01211031000d116542c144400500c0a004103101001c65000219041d2003c0000001c074010824825584540b055000358202880600c0000310865442862961000400316111351914006070855105807800c40360380e0a062803010340c1a0b4280a200e00410040760884604400d44603490300c0c0c0d100ea030150740c089568950006411030704651001541c18044100d001b141049041c001c2d00030941040c50a00e0500704842d50180d41c203134401840180c5406400c0a41003610b4010241d941c0c2d0081e02500ba115500c42640f840b454400b4482c000085016080c80c2c2c500510348039082c0030a807003500c0c003030001c504400d0584204682c5040340c160491801c0d40d04400803040054 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 255017365 1250 255016115 255016117
    0x3070e09100f0303080105120c010f0509010203120708220506070e01021c080a060b0301030c03030c020a09020f03060f010809060f0709050d0803150a080d051c020714011805060402060c0102 83
    0x2c02140c2c88000200c103060344000a181660400d44014801e652207614a542d41c044050b02c42d40024044000e4605a0b4440c1020b0101500c042c0101c81c01d14180340c0001214000485580000881c0801040400616400b10341c0a5100200c0c120725000d00320b40b00d8507110500201144c1c10710000c0d00e40500564400c2102d644841c2800f82082442c001c1d4080c0103103215420f40d080c01100d4140400400e0b10100320742140e040702e900c084000d1030240f071680c00340c0f00f14444140680c0c0c000412040040d0b40d200c0c03400180440030b03001014a07601c4c9403140401c420030005098240c1000220380403c000c2000c005040c13504844100405c41341569580c20442c0c0900b001d800498105101701640d4080207001d1005d94002da504402d00702204031305406005040344244200e040a602000c801c40340180a00020700110001350000718640b84000c40410a070ba01c414011200c50344840f458420bc20805c1c0304a4030640083c0040306108030aa0311200e035220f4000c0d1011348144000103027a1031a0f08258 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 255018615 1250 255017365 255017369
    0x40c030602030708160323091609020403060501090605060304140102210a0c0206070507030f09050d050a05010f0e071a0702030d0f0207080106180e01140108070314010203070e0910 79
    0x1820075581c07850014401854801c05072038414210020140d0810703802c0c040d002d03502905859010343d0502c0e58100411401440c1c01a0104080b80240c00700410060100c44900e0040c000e00e910141c1e403180b0754503013442100c00c164048080145002010300c5540d40710401c8941040d0041d040403240318040b038689009124512403118003038110350120000f82d00d034805941c8030383d0b5a0007041110281c041003ea8491600300c41140004078100001000240141c06070907400c5503171310344078142d541c48202080314205841416642e66100e241ca520401409029009281e01402c90a100065100801c0d554880f128001e00c1d5044504800c014142c824000949500d80e0f002012200000c1103c84081c083c0484514000c6c014081c260002c183c248050241e00e0850b909102c0801d071800d4000e050a00030141c001d8211340c1c95403241c0c2460096000025201e0207400428060700070145986842d80aa0407102400b1078941d0040c03007084030060304880c0b0175104e8031042d030f0800001d42d0340d4411018040c50507 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 255019865 1250 255018615 255018623
    0x706080901140112170a09090f0c0225031b03140f070504090203030f0d0b090106050307020a02010f051201080f0706020c0604030b040c03080409020a030b011d060f0c0f0c0a0f0b12040c03 82
    0x890046081070b44800251f0071140000010000c5043c4580c2c101d0555a1482c06640076030700c40e201d49000301c00711400700d004a100652001001d0b07074a03a641c2c010b40320780148004019048204c02481030149488807120004100001000da410380d070b03442c054682c1401d11030984030315a02d56608065440502c200c0300350110503c07059548240c441051001880f440040314041c0c20f481f400801c2c154001c404590040380c4030b4000b401c40d6509a4011104c812050501c0703030400c40c050182c280b0b060380500c0003034080c01c21400580290b02e4401d4009150a402d80e0101c41150301c04500c500300da8441500300d50940340c10070b10f800304940c0e4074109110b1854907039000402d11400041e000a9030717850b9501808140c20103950510584041c1e10045850307120010a6000d1403008080d485c8003450304800410091880c40d4a01b8180f00c4800c4085007054506a10f0310b00340d07080741c0a01c206500e060344d840c10103443c070481810700306802d1034000c2d00c2d0340c0242d8032040c10741a4502e01040c10b20000851220045500c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 255021115 1250 255019865 255019867
    0xf010f1e090b0403050d0e0d03050f03040c08010f1406010c20010324140609130c030f1514060703050d0e0a0c0305031209030a020c0f061b070608090114011217 70
    0x1e00d00c5c00c150740380c004c044d9071400110490146020b910f804004116420341580d80c00c0d040410418a0420550003c1d10031210000002400603d1400c28040e501e0302061914001a40400030492140354080003440c00b41045000c6940a00244103074600c1e100840c803460395145505e6a51005038002c16000307082c0607449980a040d14023112440c8200000e48041c5901402c80440c0c101c20b1194034010082e0b5140d000708010510407a145955001c4039550b09245404100f1040c032444420803170f0013103591080b041042480034002503103c1c1c214016810010b03940e5501e4105113890003406409038074001403103640c07603203d0a5000c1d40100b21720200c0c940c01c4680d1100352981c030b14000b96a60721000b000d4064500b521700041d000c03400403098070381010b004d4010740b64205040082000840055070032990002081c04840b558520f505030780641407103160020552039050070000780c1015001002030500380e052240c3d10741ca403814242000d04440203142001344982162512401e0300f0200b40702904c1c0c1c010 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 255022365 1250 255021115 255021119
    0x3040503070606050105040501051c0f050108031e0a020303070f0c0b0f06010e01031a0409020415090501061704030c02010f021f06150203070f1103070803040602010b0f010f1e090b04 80
    0x840840103180d4107104050402c2110b0352080151070300e000307a100700390104606001044200c0c01b404d250221510392548005500d00c55020000100c030000e070890300c0c1607480440c5101009211906141c03580555003100c9051240c1850020360340d100045c84c8204006035401003400720340c01145840081365100008900364a0103400c400040306003210454002015401a800c26501a00c84c0d8a00104400c1f561042a181c420900018044440b0102e03041651100700324190b448000b4140060824024007140d01e51500c3c0000b000401249040c08841101400748070010360406810078007a98203007008116140c07015816800d00d01420315061180804401210800006078401e500350340b40d00707610142001300d04908981c0c2c1d0295010043c20500c905a2250118a255100c208000001421a200c268a503d9458115082940100e0140c0e4540100401a141c00d818003e8006c1081c60450039046400c8002410080c0c040843c41d610ba00040710b10f85c10610400034007000c1c10b100c44803150390325 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 255023615 1250 255022365 255022373
    0x180f17030c0a0b060103051503060103061a06070c090606050f0904050c070f0f03120905190503040b130302040b1f0f1124011a031906051503100807050102100513080304 74
    0x120013103c165000034640030004406600d44c03110441c4540f0058001e2001d40c1c01e40d0707502c40061440580301901e42826a41071a601d84c0c1c2c040080c03005500c11400a001246820000c900ba00c45641101c1d0611038281310141200130020107844140700226004516030321380c030364009251700c140e03400502501c0180e20050f003030080c402071100030540301e0f50f02c19101c3c82c1d0b550154012900d4a5200501541100040d00c0c60700f601064001e40781030298050b2460103589800710b0019500c0415460027002031b5581c10000d519051003140590a4190303070004200d24200c1487c0005000d244000e024040110602140c5a00c070341f40050120000508940402c4e260501d0064142c003840c0c10070480600d01e100210303540201c21031a0b0021380c820000e031070664460211844907005038417805094165250350014440d40c0e0200c11018020b1403420a555a00b40f0948004003000303d90085241ca40c0811310400141c1da00299042e5030012811002849440d007071400e245000b60140098070035030012081c00280 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 255024865 1250 255023615 255023633
    0x1020301120f0804120501090c141309050c19060905010201020901080c070f05030a0504180b1507080f040e0a0e150a0b060f0a032a0c0807150603030f180f17030c0a 72
    0x120b002e00040c01540c0d0f694101e01070360501600514bd040b001404508559001e0313a008003403618030420076900031200e614007051035645181d82d1800380040c0341e1020025030f0380044c0c0c43e04c040c1c40b0a2000790f1400510b00006030a191000d4034014a8520015000c003d01c14444542050640d1203019240e80300441d40c0000e04076040783c0905a442801c1c3c00f81c91400e0300f298800d41c079020001400318681540d41650202d0140c004200079940b150081207984103841900000700081d11a02030300394560300f02402c88004544007a401c0c0c40d0154403100940c00402202c88900c2e9100501c4500800c1080b40740300464443e00400100f40c040a501081003e20107401d60022411024a560041a81200d43c40b03881c410110340d05039440031605000d50000403501d080c005180ea140220168503001c0c080f52080c00c1101d40b194000e41c0000d04295400c03450303036844032001c03441d0088d03009518540d42c20590800d43c0c0380400e04c40c4c2c0d48162030f4101000083c4d00244107544a0307030403d809490303107520306091411078 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 255026115 1250 255024865 255024881
    0x4060e0712050105240f030106031a0306091c090e0f04030e0a0b0f070218040b07030c03150b0702010e0603070c050607050c150702010b030a050f010e01020301120f0804120501 77
    0x1084196228403001c0d00c1510450b0304940004200c00a41344003100400d1950104503e0309000000c100495551468160011070090499680000781c00801d0b0400c4540010700100a510940021062004004000501600c4400a606420048038043c6003d4600310b9444d40312554144808081040e112265100c00d84114020b031600c1c0515656142001b0020389a401403641170303201401114542034011025100300d81c1b01a00010301d1541400810b0780c504030031a82110100000401c2052159250040503540c01882c1401c0c0003e080c1c0b800d9154a11000c0e00500030500c00216480c415a8400c0401005200019060540e03c0c1040309009103e079580417010740b440e128040100716514450303001c43e20400c85148c05040c10040c1d410100d844407002402d203504644d00d49040640c03c6d40c0901c604c0750780c1c911820080842c0c10b824104039095440d070305d000c4241a4818001040756101e17403040344041d10303070201e5810404480b5140054150207980c10144008600820100400c1415402070075 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 255027365 1250 255026115 255026117
    0x4080d11090d030206010513020c03030c13090e060601020d020d020a2a120606151d0a0e0a02070506010e01030308010303080a020f030705040509060f210f0a06060510081e060f04060e07 81
    0x4841c0c0d440512940591262b01d014910030351040000600c081c41d604054802000844040444155282e41000640d1110304800c20950004020b0159560b0104401612080c445c0054a195942510080d40311841c801014003a80301c5506046c8400304202d41880c000b010b03000e1f20310030103501d0300310788402000502c500b12492407034980c0206510101d01c0e441c02882c11195101106c94031043c005040503d5164040781e00901d2014021031900c03a07120446100f030001240040e213070b1850342441c43c03030841c040c2c3c4908485012280184003181d803140e03641c0d040d684c05060124545e198100c030f58000b41b1400240100405011080c000521b9000d0001c0c01141e404980c0c0c6591500c0304820000d0044102005651043c8000b404590507000e01807448030983c0c021003a10740103030406840c10305061701c52400301c91a0b5600c06040c0007526280368030441e500105e280040c020f250141e0b0fa240340c2c0c848080040d08892400000450590b030700d0f036144601b10700c05807052120a80d10103454407040c01c103a440034 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 255028615 1250 255027365 255027379
    0x60e011103070f15050c04090e0c030609010209130e0d0807110604150608010203090a11010e0d0b0906010e07210605060d092112020c1204030b0108060a0504080d11090d0302060105 79
    0x11020b04a90145c3c074004d45a60840314034291408407000001c04002402c40802c2c01034031200141a40e050008510030340b2040c00269a070716900341081404855490f00e0003c440c0f405005107444600052101000443da05095466407200e50003611310004610140b400d620400c0200800c000c0e02c10a0200811090302c414416142c0b41c041c15030a1b40000c46410700941c0c44140410080f90721104000340d2060107041c208800701c0300d02d0104200180010b030940d49030400600f8068184400c012150040003281000891800c154000420201d2008100d5203030001c107100d10b0087e02107130340c005401428014400c50740c840340c0410580140c040900d05859911781c8a410441c1c0c3c2843c3c0c440d51010003002d036034492840400c02007050003074002600030b4031140f00c1c1d80f41640200300d130b0300000d002940c0942c441c05401d6160480e40c1d490042c00030801c041903414902800b000030180c4080d1402000c0b6920082106106030901040d03d02903480e031a91b00050403003001e0141a004900241625000c1c0c50700c3c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 255029865 1250 255028615 255028643
    0x1b0106060201140f0f0a331202031b04020d050103060903120c21020c030f0705010b0d110f010e03011505040b06122205070f0915080304060e011103070f 67
    0xf0a01000220380016040c00b103000058442038840030801d80c05600340e0782c0003a001203032080569621039048142500380c04400300e030038031440c00c8204000003002c1d50012003590102c55800b00b9254100c100801c10900c001055035621581c0701d40540301031005108007040190b0f5642840d03c0038289001c010b6010400c05500030580d917507140103c241d0540076485078902c94080d00d442550315807098818a000707507400e0164545a102c10700050a0300b01e04d001302c164848450f824540d0840311140710a500c80d01e0001c10340780020300c0c1480c2e8900100d8045500081646c1900300581c1c1c6070070701c011101d6165290160141d004c1c00354114a00580e00b041c0e40c03c01c000f91090f02441650700c9410000c0b0354500d3307005d001519080d00551241840400c07110f042e00d82501c0766440d245002640d80014052004003a010311820b401846000c00c3c60080c8407125450a160482e01c503102e205034002c0c80204214403003039180e1640245c020b1000740180c40212035443c3c07114146100303040094102246c60500292003 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 255031115 1250 255029865 255029891
    0xc06120e060a0b01260714250227130f02041e150e0c0c0a0807060603110f0112020c0114090a030f021209100c122304081906021b0106060201 62
    0x102c0126014131280d86085615080710035211a04860f001c7c2d981d01d00c08200c142000c400b103c49413801e00030084910740980c02c2c00d03c10810f00940700c0c0e403000e50001c5064040039407030600c03011068200c100b12111007142040750522a0300e0b111080c0c000380d001828040340076100d00040325120b0301031030008803c100d0016081031929500300e440c8140410040784401162031a00b1510040420b022a10700302c3e1381c0a0b01c0da560f00341040d00030100507240c155644008000f40500c4241540c10ba40c4212a0341c542c001e0840c002a140c4849403800c1c0000076800308440b00b40381130075031048110f0310310500c60040d68a040810a43c0d0b6401034103048000490350318811900340d00008151785c001c451034241c1c1d03007000c6e000da051242e04480200303905e0401c0368030780e0410045500c07402841d6000515035201c50034038914a811a0000076408018000e482d42040100200791022580400040401c0130307403e0400c4840c00d00300084c1c054414003141502d400d07100448014415400340080b91865002803180001d0f04503 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 255032365 1250 255031115 255031157
    0x6140a110403050c040f09140f070f0b070b040c0801020c100c02060f0c070303110a081501050a0903031803050102040e0f0c0304020a03020607021315031e0c06120e060a0b01 76
    0x800244140d009a04c4482585001c0d0840020507001b00c0b4000354019403601c5d08403442591500030401ea03042181c0900c0650403e01c006030250403231407a043c0c01c403440c0070301441e000e229098001e070016034001c000c1001c1108201c901001003c1400c0250f466420000381107840e0b08440d88410b1905143c00214040da500220b1064413600c48001d002d407180c0c0c1d03020300800c690703440010304400f01035980ba6440180344072840a4401c40b91242d4581c0c0e21031405031104058000e14044071414040300340310510800780d03c400d5440c250381d814608070103540d200d10480da00d444c5c882d8200078000d50020802040042c0005030091103151400d008440c2e9455403000c041c45840161406500070300c0c591800e0000d418508010040b052010b00075050507413503003c0e10000c4030082400b080d407901c0c0101c42041481410140c0181d00148012200e0b01909156502c0d8000a07240c81518103101d5104012101e0484550054040001140680c1e4440c41c042071040014000501340c1c0d030200c0d054006c13040070002244 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 255033615 1250 255032365 255032369
    0xb19082103040311030706021b010e01060b030c131505031b030105180705070c0e1603022503090807060207090501080a051f0e0f0d0f021501060c0c0306140a1104 71
    0x81118610380312601d084134086074240000c0c6951208100d90340003e8500d10003041126111800500424441c455071802d5440703145032250a41e050040520048a0040c120f07a0000300383c541c83c0391380c1d0381c0d00e00107014900f41c903038440b00c1c41c41206401d13256511382000003140700d4003140c020b07415040c000030340d4140d05000c01c2c001d103038220641050350104803160340c144540065047c00c0090038580381d603a900781d00007281c4d000008040d00280522500300c0446009040000c0b05040650904405030300e1500000d41a00540306800c0481c55100c0a16015241d0384c005409900213640d43c860320307050040d50314002c81c07140d981094984000001c05a101150388004181e003c030207404100c5c0b0540e40401460002d10b110419291b40301640b0154032010400d2031038440148001d0700b21001d1101d4061f0400414485000940d0480100210700450100d20941580c04900300349520584034189143d44500da034000400c218900891107248070b0f021600d0700c1c40380062290501c82c580030007401400c0c43c05a4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 255034865 1250 255033615 255033673
    0x12060b010f09180e1e0c060a08190207080705010c02071502061506092d01090b1c09020904050c130c0917010207052d0c09011502010b1908 61
    0x1c5a00f801141c800f60007034040350074501c6002c034042c9030402205090180644040e058851000c842100702041440400c00b1800c0848040707090520380c14019108400c006d0954160a000d4003d900c0011925416130b03040c560400d200e0780d280d0601d0301e825402070008025990240c0f09000c000143d581c81e80380058100e003101da018003041e45070001c1d012452140c0c60714240c0d00c5581441404916190001ca40444861000002c42440311380c8548100405800d0071450400c20084014443e10001ca012a112040b03089030468800d5500c00320940240481c000081d4401c0a9506010607c100023f01021426040341c0c041c5446401400340301c00c80c4c84030200c500c0031418050040016001e80124400c48441040002d890101d256860604002144a8110b200740c6c0d420310341619189000c41600000d40d22400900c000c00c102d00005000040500c680420105804003010585100307410080c007800c405000e200c030601d5102459402e00075103010318061031040152034070440200c039160001c60400 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 255035971 1106 255034865 255034877
    0x32102010e030c01140a090201020d0c05120d0c0f030902031b03070308030916080d0203030c07031701140f0301020711010c141504020424090b0310020412060b010f 72
    0x21b000007a10030b14081e02800142d80005031b0341646a007904000604e1102e900d800da140408800b079614210b440072070380402540441d0421080d49603583c807107000602c1c240d5400c4040320104600a54076512650381c4521075141801e01140300d29025041d50043e0f41c0304d4403849a0782d4000c3d03a82001d50340c00b50072700388031800601110101400503603028040404411000039503034080030b80901d880060004c0c42d002018010840307035080c184a42c00ca01802d695880c4c12070400c0ca40300250703d02440e481c104441c12403606100b15540715038010030441c10540f606004440d80703a41e058040350403030304410900c44035103010030510400f5881407641300041e01e028814041500c90fa104090013138a004400384500700b03a8041c0c03010036102072050000e41c10a8803400646058000c0301502c0ba00c5200060104407030070403d4105420703901a04051006620705001100c003104142141800030350 = true := by decide +kernel

theorem cover : BRFrame.Cov 254856115 255035971 := by
  have h0 := BRFrame.cov_init 254856115
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254856115 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 254856115 ≤ n) (h2 : n < 255035971) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
