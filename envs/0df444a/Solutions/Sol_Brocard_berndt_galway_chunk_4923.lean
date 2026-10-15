-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4923
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:10:16.813562+00:00
-- url     : https://prove2.me/submissions/abc74fba-38cd-4a14-8966-dbb7eb39a3ed

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 885251798 ≤ n < 885431654 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 885253048 1250 885251798 885251813
    0x9030f0705150d0f0c08060a05010e0a06121107030f02010e01140138090f06090901030f061404030914010206040201092d030b091005040807032001050a05160507 71
    0x264681c4108103000580b40300e48001079010365261a00c2801c01c01002c00046406412840240e847c0341c0b1075072404000042d903606c1200011124403000c0c1030380d46180e15102094030304140b03036980007407103540b1541009043c0d00264050b192050003030342d03180000992034201034210740031000b51060590502c401035458503038480750079045030300c0d18100501480c140460081603030885500c44000081c50b80e0746000700003281c1d003d801c40700400c9a00b0120800b04c041040341034426120030f6a00600060010004103043e000074124040c0100320200e40c0e0015010880900d00c011203003100411034038102807000003c0c03030184039140c045c20300040070306051940001e8901300040c800c08126540403084242c002e860b41c02452607290306441720130645601c0385418400c02c502140e0ba01510b2260844803401c288050103101d01460300f02000d14604001a01c04840c0c014140e444601c3c200392501a070602e03030509114585c807500b421000002d90781055202134640c0c400410b07040080190921459000c0b07580c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 885254298 1250 885253048 885253069
    0x30b0a06080703031d0907111501180b03191a06030102031509090f0a051b0102030f040504180f05070501020d030c050417070302100503070f0f12150b0f09030f0705 72
    0x50f0808000c11452200c0d0b0005c55030300080c104c3d40004100081c0000180c0194a4280c582d000c0c0d8241c0303024410303020314121031803030910a142000f141a02000102c2c1e5107680550210312000d4159180304880310040c42160a1664044910401c0703904c00325428034188050980143c0110029451030618940007094a529600da0320301c540350041c0031030042a0104040010400e4940c00d407207090082d41442901c030003400c100c5e803140d64200c0302040003d601c08801c5560010f03c141c03030b8030300340340c01c00d418480140f2647c02c070841d0007030717608400c03102041d02040c0c0440c1c41b501c0b4000902d5900e003000300090801c00034072410010705050420301d07611160400d003640d080e100e6800c541d5800c801081c02d2140b90211701c1d400a50421560201320710b0302c603172010065101d5586d68803941c98801c1d090304100d460400e401e043c0f50000c0d281e4011116010059080980c0b001c100b04c41d0180065140c1d030340708a05034007241c2008001c04000a00300c0d0781d4201440408018001180540206403420011404840c007 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 885255548 1250 885254298 885254303
    0x40b0301140a171f020421060b010e0303030c0d06050a15090e0123030c0d030801061d06121b041d010504050c030412021504030e2112250c030b0a06080703 68
    0x540010041c004c007403580c15180103004802440c00702d007417a8041c0104a8248040035aa41c03810304110310803550007503030301032140e02000d00298510b40c1c07086800f14081c0c0044003002c424940f01e003c0015261b5072500000301900c2400142d080085420720302402e07078086517200c0c40400c01998010091071500c0c0f0060000760181d800344004a440310030000c1d080c90101c016440d40700d042141d1345c00615034009640c0341070b00d500d91a000e400c0500441552031168401020503444041081084040c061801c945a0007545e224014491440c56244404a642042d0085400500f248820a00c00071380f4090060041000780c0d01008076083c010300f04440340c0f00040024151042c0303500042c0703c043c030070040d0510410034408584414206407800030b0402403020007252103a0140102d0105150b11400052901c0858000800c50400405a1120943c1011b8003410070380350040340280d50081078170110020284101c860010a50071817074040e420a50180600400034508031007445680b80c000b80e18025240c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 885256798 1250 885255548 885255583
    0x703020a050706020a1106090f03030c090f1002010203090d08040c1a0d0504151a0a2313020306150408070308070c050d061d0a2105040b0301140a17 65
    0x18000e6000e03521031080080007440700d0300c0002c1c40c03102994405041007410900d40181c8a8079125623404d19a211100503804966030401c2020541310f8601d000101030b010005000c800c000070300d140000340c950b45100c8440d80907275000020006402d1052052030418009030500d0219801d181d21a8410200d0030f00942d034505001d0b1080300360b0a10083c058070f079040d44c90041032050b031410f03150500f08140c8801c5118646030526050701050400401c800c0d110b070001400d550303601403800300c61210032120896001c28000071710004070102c1d04d03002c9410003030740035000340560ba83c11300071309200884642018004521500703000070f00084038085103000441ea0400e0302d040c0c8402050800541d50096036121030750007205601380000304007a82c0c020a40607588480780500e007000d4840703d5600c0e84e02904000304681c158880d803c00c0c400344000d5a20445055282182c10036032107102c1800503a10a810081120041c00b0000040746880004d85025148007042d28460001c00b0241c50340d181c480c80b5a02c081074 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 885258048 1250 885256798 885256807
    0xf0e15040b092b02061003031b03140f0309070e040f03030f0216050c180c04060c05030f0408070e0c1c1a0a0902040302120705060a0c060b0907050301090c090608070302 74
    0x104204078954921104003c4904001c1c03070240281c0e03051902070ba42101602410000403091011950303980b080701d405485841c070741400d02c0135420700c100c0341510880620044089403c20b04414201506105007092100ea0344d80c140607000c1032401499a02030640f40103040300b00700009030880c80e01c0c07507646d42c10304020403280a1000900007078007a030f03410b903244464010000c1040c03083c00640e0070f00842090315803140c048130a140700c165074401120075100c500002c001c104803039441907002e401c10501800c2900d0400c8441816006554031070340c014001039000804c28050300c0c3d044151560040c9021980c2480c042140c0245901480b07019011072030107130b035070f40400f9490325114000c400480000f04510461510384d09420300940103400183c2c010000340031414040c2c040014401c042d213100501943c240384000d44101e4418105035000c0300c8403a1140a04141c4e0303200d1072480c6c0d0184c80320741c6031651607604106174001240c0607108103104001088604006a1b50031844003904040301d0300d005a0f66 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 885259298 1250 885258048 885258061
    0xf02190804060e0a0f0312050417090a030c0e0105100c02030d0c02034308070e06061204081918181d0d090e0910020d0605060a02010f0e15040b 63
    0x249010b10402445021365908102042102806000614402c0c0c41c0c120900198100e00e000b205c1c422074004118049592503034907828020300c00341160b500d008001203082c40d281c1d520780c0341c000244c3c0d01001c4105103070801480545410224150071201904d08a01280960380000b6607604000b8810300c140302d0310001803001e54405006002207410701050010109036003084800c0d204916048007404180c0b2100c00c0f601918641010740c0031608208000c020240c10140070329514480a0180396201004102080343c00f24406121881240110130707954a4030f1901e04840d55403a10041c0440030040b288400001481c442c011020585901d074014844141030b03000210001d1014071152500d04c810720041d000c01803000200958108000d40e15403141755540c8007038106d41141501e0041303040d00141d540c03002261403513014042442802401184059481010406544c044400040140d44a81c010780b1b1407001030251921600844c0300800f02080c0f00d0300a101c2e001c4000c0c10040c041d50203000442d01 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 885260548 1250 885259298 885259301
    0x10050d021621080603030408070b03090f070611061b033105010b1f120b0103060506070803071e020a1b03020a08062a09060901300f0219080406 63
    0x5007580041d00202c1c4100c0103146a959002142540002407107000c005407690170044240c60888031510024001141005241e60341c6400c0100000018855506907421010742004800014011521000c0341d004d00c4408241c2001c800506e10b006401d903c01700e503044d800880d1300702c980c0b00c680c2da2107024111104c0030f01d5420b10382540300d1441341084ca088032801072100c1944080c8907004125810680c08c45002d82246840d0307101c01c0d00101140080c0004041a4990703049030510800c140350000c0e0003626800040e1a54205900a66000300088200203009411154030120740200061300d2059004070a0004e54640f85804024550300c2c000752131120b03003c5001c100c2800746500410344800075460362040790b642d5100308c0f0112015600c640e5964581d440b1420317544403401501c41c507646098243c90500200c0d510189140e410885880714408403424038020010302c9c0222420b0560740e841550310341400b6980320720000d803187d9104010303409100029920000c168907180c01c0a1405983e0b6050000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 885261798 1250 885260548 885260587
    0x6050f0a0c020603100801050a05060109030308070504051806120c060d0b0f06030403170708010f0501080601200304050310060b0301031e05030c010203040605010e041104110423010e10050d02 84
    0xa4200c0d0021085c05007001115516070259403c80d0003c102980c0c40280d0344040d10b4042d6032983c08206079000610109115020250317203c400d40c1403d0385000e5441c400b05d105c20401c0701c1c0143d68981c250051042c0c1d4601010a6426803542c1002040341c4050507000070014440c4501c407001d0b0580c2c030541341c401600c03490080300c1c12403070040c08a034a9240c6810054014164040b154a40004603000100014000e00299069895080b510f00c800303414200151200140500000d041c80b403e052400c0c2c18030395206c074010320703503409902a588443c503103030038140340051800d08030b035911303007403031401e105e812592002e880c112904080c040303403d100004054050500b890744040e01e240000110211008415001980158843c64080000b681c1c3d4118407483e03801c0a40700107100401e0781490b101186066004500d01b0404c0810041c6059a100e281b00c0580f014103040c0c6a291480d45010801e0750382080240744070712410758945048a41c0d042c001041d07845030b4940c0311400f80d400f14a1f604000e030803038a8003 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 885263048 1250 885261798 885261803
    0x1a130b0a0b070804080c0105030f010e040f060903091a0403051b01030e060a02041809020609010c060b1002070e010b09030d2118050c030f0309010503040f0b070c0c05040606050f0a0c 80
    0x20b9940c040030700b00046654414020004184610b0520640da0b510034400c40303100707200c03000300604582d0816032100380c65400a80255540d00100b5003d03408591320b44a884411482030304e561010341e1800c00700a0005540d0101d034011201d05100030030100300702103039400e003151030024907401803480c4d000180c000345602c0101072124401c0108004400650790300a005694002e4040701940001e20440010b440c07200c40001e400501c240810302da2035019070360039155a4401c1c1d0001c84d43d148404c0218804c032280c4211040160f102c11800c020644c92040000d01604a0000140c9864031980110703a40d0b0300650003000410848000d90b50708807604200b12940100c08110500a1900c841280480c41c7d48034202910213000d5940200c80354038000800798504002e000140d403c1101d41001540d294100170000d455001800c001c042c002170150803240c0c450700283d00da2a0505600703082c048040035070b54001d035020b42d10300f000901200350000162010110b030044042c0d520310002804031465150400300 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 885264298 1250 885263048 885263069
    0x1803140c0105071d0a06171312020307110303090102070302010f090e0a020307170402010e040b061e07120e010e040507210225080316110d02030a031a130b0a 69
    0x1404041c030350042c91071302e00e45400140d07030300034480700320404c40b40a2080c421500800c0302c00c0d08a01d2840b45e10f03103607140d000050f0b020b05100034a854035100e02000c21030f40028016080040c01038200081000c41c0304c00d4a44c01e4000b141442c1060380040e50b15082e90102905001814420042c0300d0701c40c07202800540041c1c81008100d00b00b8001d104080e40041c0d40c4003010420301396100c0c07034040070380c000380d0700c01c640503524040e00c951400184401840e507000866008401000544034070380d0700c60b80010514415416440d03072006181800040c0c0c00307031804c8181c20840b46803140c1070345c5c0ea4040c00e40050903404460024241e100c4000a8a4041000041c1e0b0101446401e0300700007203070325030f010f84010002c10710100b40e102c804120844031480116002041800140046521001001d12400010560341801305020045600c624900304d0035a03884001179100048000700c05616000c3c44102800c1290340040702da00310300014140119081b214003203e81e0314800038541d981c5d1000030705c00400c4140322 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 885265548 1250 885264298 885264301
    0x110d050603032203030807020d1715030f070e06030d02030a18363b03030f060a0b04061205040302160807031b030201120c090314060702010e011803140c0105 69
    0x81c80d04144103200c1900404c00000c0024a45400410a80e10055655481860314414811f00040300040600b420502f040006c408140540341081000002c0384018002d0074801e20b80000860803060040c80700d07002744c015201201c49290000195103018455040102d00d00801c9803c440d5101c1c102d40c4480d140244182c00e40c9111144c2003141407034070f43d242c0802140c0c41001c4030400c050350840440b0170142030201c050308001012400d90418060030103c841d9030070050014095280d80c000703590210718000704070305100a0b40b5150300f54400a00d03124102ca42401d10302540030307000b400c4148800450b81d881c0c0000404243c8240041305e0203210480b84041c0507922400c100355101031501048420010000d0202c1524000303014000c1200d82c1652409400c852511006000c0d0030a50488010301043c0d41c3c01000250715244c1c01003040700390030014035a900d80103030001e0a64009824504843c2d251521400c1108000740c00c102c0d4071a090b0030301700003c4040900c13121942c4216000038006d94603140 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 885266798 1250 885265548 885265597
    0x3010303031a03010605220207050601150306060e130222060e031603020d12030f0f0c030c0e0105091e090703021207320705010c080a0f110d05060303 66
    0x1849104541c0001e902030b40c6000e800c00900d400c030780d454000d555000c007a20860307504c0100d08545903144010020005400c3c0480d07a41c41e1464680c00383c1040314a01c600280b0790745410350600c11800107080511f880a920344105020950329550369292a00c0240c0004880d4210900e2400701d01d002007000c811a58455a1150002c10300d04048407a24440c0c051121545c0590140d005450103a0390024404104042c566a600c401e041d44907807001c0505468074111580829a8401c2e224580240341e40071401c44902000182203c2c11007140c141030110215500d0800d0b41d0100540782407180649958034401800d403004c0c0791014141805e02c2d801190030013049007050345074018001c80317140c06021800d25100d906054580080005441c80f44c00640c1d00343c0440607101c0c0280c00489018040402d19001e0940c503140d00351000007180401144508013403100300f4006101c2d51205002d11f83c0c00b0401a035400c16924100d1262546540d00a515000400c81950382441243ca03070340b815080302002e030241076 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 885268048 1250 885266798 885266801
    0x130306021305150f2104080a081608010614090418171e0918130b0601140f030601170916090203160809030f04060801051f05040b09150301030303 64
    0x4030381c900c1c415258440d0024442c02d0a07200311045a040361582d030308082072624018002d07001400c201200da1045d00400f0001c48420200c00d0143c1d0040320800c1d942d250034100903088480281200e0903d80070305a81a1b400c1f90f1049000707040d5152403610207078050164081303a809001d800800b95001d40341c00601c0e03160307106801000c5c00c12403280189038560303003180c1c2c8904d42c0c0d400389041c20400007041d0250440d9050300c2030014031080400400901c1a42041e82145207600e204130780321882c080504c0844000e100809680f147d115509280002501088814410550007001c1641054400100200d6816801500c0d50008004004103c01443c0390042c141a0f55000c864019200301d9401d40010030709e20428000c60b44100441e0703070035100511039828101d07519903004044d41c000d40024001c000040105c28010070007090250b903054869410841001503070f01c50043c032542c60700006c004001402d5044401d8a04441003e80403540b504001ea01080c4501c0504000800e0700c1c000100100416416 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 885269298 1250 885268048 885268057
    0x6010303080609092104151218080307050c070e0108031308210706060e041506090903080112020307080615030f07050d080318070906210c05040b010c050d0807080912190513030602 79
    0x12103c09d00400950034031002402a2801c00604041d1003000001c103586e001c0da004040c0c40c0d121b4400c030340c903a0fa40c0d9428180d080c2030a0f042001503400000f40000f9043d08805184040c15a1070080d1540420810a1301203411208184080840010441d0014071061b54130004c01000c1c84030a0003030528183c50140c400300d031412600f20041c0e00d007690200e1988090301c0f030046120f60545400307226034202900b11680d01c01c40801207034140300b003440104030000700340400d6010300f21a103800461148003208050401c90502c500301340603072140c241001240d641d030400315160390b000030b0255a2500c03800310f01149017aa1514203041407042803c0026031160300d6100d841101c0600404000c12030121a11551040c1c200401902031034200c0014013951605500001108005040c00103054101d5a41c40342040040c80c00a40071a210804006849401c5441c650340541d83c41c001d04680c18a4072400000e9025103808029054040307000100441e01a204a5001540c460300c50030000382d4914007000a03602 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 885270548 1250 885269298 885269327
    0x110309090c0316090605030711010b130f0e0321070c0c080736050702070306062310052b0f0506040c02070f14040b0a06020601030308060909210415 65
    0x1030119690340ea1141101300c095600543e20b04e0310310340764100d045542c00142e841c0700855551301c074617003507a55881c4150104290070b403d90204014003d14220303401c8034641881c4c18119002001038155000184204a1070b01c15004180e5603a512084011505429174500c010309110040c2d0011400c1c403000254642211540c19401c1036090034072200703510300c0c1c41060b13010000003101c2030071449040c0b41c0e80007180d010400780304030b810040c2e40e900c0d10b4050360f2440c0d200210a02d4145081490010103e22251030004207070791480401c007400744010558444c1010440001c8000308880745d2600903612003141ea01c0801009004101214114500400056404910551070084c501c106d0f46e00214a1500301d640f0104459045842e090781d8240700c2d01140da105030700a0383c8010050f5603680d4600b400000c6e068542c001c200c15030440c640a00500d43c0589068402c18242040022010b40000d11031404043c2d030010f02825514060a640680201d400081c804291202c44046d00c80d03202c20406070908 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 885271798 1250 885270548 885270571
    0x6040f0b01050f010f03110c0d05070b13030518061b030306041a03070605030a0b150a020c06090d02040e0a0c080f0c0d051915060b07150507020c01110309090c03 71
    0x903070342c0c0104048031400303c080f0350203da041d0907503000081c020340c01603034680d030401d1000e8a800c1d450b00b40349080c500364005030804a480880c6030700601c20500c0056501c2a10140c407002c0e103200c10b480280c201d0041401614640350030803210103098456409586004110054142c002603072115001e403240c20441751180500d1412500003c00c0620183c0f00300c40c8580038001d0301700241000341c100e0b41c42d800208035111041e1283c0c6900a2a120340700e01004c8683d051075030300e49429811800a04240769030340d14502c201c0c0140304403803c0e82d170b8414141c40c400360b0489001038114503c2ea41d0300e0500c000c8580240101288610000390214040358031007004440000340d03102c00b00c1010401c511aa80050702604590002d610a654030902d00c0340384000078090b9502048810f51080d140d802e680c1142c0007890a80b801040000c00c00460038807510f01c000e50083e0902552801e040000d50307030300c680781b0003e0400041c081c5c161408a824821960f1001000d4051111444d024525100c1c2d81c1c0180c1c0d0f03003038103003 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 885273048 1250 885271798 885271801
    0x90310020c0d020c01121d060a0c080c0c070e0718171e060103060b061612030501091a0f06040e0c1801090f0303051c0c0c051608120d0e06040f0b 64
    0x3248081200304c0d11074016101c0c00f0314100c400455000400305c034001c80109a03d070450030110482c0801c0b00d50b00c1410480404200101e80c0d0070000e0a13010043c110031001a401e1240005502020030810b00356001c1c3c2409039125036401c1000c486c5d06c101300c1a018100d2000d0240810801c20130102980401061001c076520600c607a075080800340d003a08030002c0c0740d400000040c00041d0498108880c0c42100500d00d40c02d1a00400c040010381c0308440f401c8600d40003d00000c440c10780c05024050051222040c20400404d00300381c038020184125039814404d0880300882c80084d0349075016900a04041e0150018900e041d0100c4202540070001000c00b0030190001c04006600c036000c01c20a440c5400940f5000c0d519595007550690400c07031600782d51340c000c07040c2100483c0381485480c00e40314056a510603d400103051043c24124081c0c010100c0010003c01440000d10005959040d14040c0c82611b58a0702003a500134002c00d5030301c0086145002e8001030105011800182c800818024034039142c15 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 885274298 1250 885273048 885273073
    0x1e1a01050f0403110a15120518060f09100905160e100b09011202070f020f040507021216020307030c061b17210c22080307020607050102090310020c 65
    0xd802070852100115900308414400940b8840fa82041140060308203503203192116408084542030982044c0010b0034000d4000104c000c901495800c007641c900316804000c0c0860342180c83d800c0043c9880d41d96003030a404241c10345000c01510312400c80103001085510614a40780b502d0f010550380b1001000444100421507620300782d03069026958543c0e0b01d2001c2450610f805c03205800c00c0300380c0c50501001000210f0030501e5800148a031070f02c10b0041404903203080c4100164903640000d410b000e140b50504004002d5000103204031000e4080880c1501d400c900054031241402c6800300079054001c1140010400c00003180807400d840954844442c3c0461828009150708220280580100100c00e6940160220390004000c082ca04034a4a1015000c0501d036640c4480107580341c46483c10006110310340c5410300c400700c900100d5600d001c44010707447c20f00e8017546c80c0500d4001900c1900c2c0010320404118095044892000000d0141d40f211190350b00e89100a4108071084501c0e4011200744890 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 885275548 1250 885274298 885274307
    0x90303060a0302010f0e041802010318020907030921020309030d05120c030408160c26071a0d060b040f0501030903021005130501050108010237121e1a01 67
    0x892000a400600101e01c1c54004480341743d84403554509000c6e50800300da4043d22a4001c00320707009040c5407208001c4006200040c202d505000401a4048400d8901001685d40480f46038003c801032030701040810729820030000109164203071004210740300a41c0c4601d141c010002c1e00349860128203598003900801c00079100c81c4900c0c01c0403a00748003040002030313080010324060358209025401e6103003084421400915160315800701a030305442c2c40ea500708400714030300c04040e5012501042c0c0c4010184174194940c1da620b118000c0555242203410100503600c4044c00b0b54072070101044003800b4040d0341d40c1110340d4640c41f9004010280d0641480855154040d0064510f170720381c1680100754a8205004600c02082c0142203105600d020300301305008100f00b401824082c3c46100700060741d0318403c00050981c0e44442586c915920150440130384201483d0305010580003e07070605210715070741004035400405841581741c0d8200740c000d00c220060006030b4884446492102e0329910740020000041d00c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 885276798 1250 885275548 885275551
    0x4060e04050d03150e0a020a140a0c050d09030b011403010b0d060b1005030f1305010b03010911121204120c05120c012a08070212122113030c38090303 66
    0x241002c170300d001c6103501c1c920b0360041044c0509440c0182d0344158044044415900c5a518400002d004001c07d9052100500004490098600340091843d256907150b0710030043c14410342c00e01ca00c038404202d400d61000e400c40039944c44c00070300050054249190146c014500c03403030054020028450f00f504124003c030308480c0200c9050f07074025800ea40704910b0900701103070350070111a29501c3d40300d05c4501d40c80034010800454460920261402145410700c070000041d05014180c540c000c0d00d064994902c00c2c000c8805581301003850501d0b913645e07400c2c107010000701584019040207100041d50a802d1011aa030002100240e2740c085001285961160119a000b48084005031108a2800020300490020140d4030310207010a200b040940e60b09500b415030481582c2c0d030003040000d03a007a00d840034004983c400910b0348801750043c03c0c5004442e10310f8108043c01001c1c0841c03010344000f4020440406210880558280b041d5880601240b82030302d403104100c0f0342d07271102d0503011800740394020041e03d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 885278048 1250 885276798 885276809
    0x9100203011d0708042102150a141b07170708040b030a05150f0f0307030501050f04020315010b0313080c010f1d1b1912120e0f0f0f04060e04050d0315 66
    0x8803511502d41c00000309415a03000c40d00640c03252002c049440f04004103101c0c81404271810015901208281301000f002c0014094207048070b903a84940340d181c0c5440113640304c0b00c0d001a000c5102d50001101c40794103100d0400c1c00307000c550001c18001600081c1c030008500c2542c4100003071040b0780b180352134040a4003010140302d07030041c8000d9000d0014100b003c1d001948010090407181c07032580e00c2d121702d821504155000c0a644070070004010940c1810424031101e19000d01c1c0a4050398900701851459000207850f0349088119a100d90f030502c55081d040d60890708410000300000d80c07028600340c005142e004102c10764006000700d03101c1841404158904203104101c00b6517245400c4c8010040144184000d81d400e08030f101001083c0c11961118000388c407407144122211805290310043c02664a105c56548620b11035800d80c4102d80350707802696030210068402e985070301108800034010300515040241c004c3d5680c4200701c14000006100031040320582c0341000300c0b015403c000d00050301d00f4041c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 885279298 1250 885278048 885278063
    0x5032e232a07053d0501060f0c1101120b0d1a0c04180504060e0633010e090405010e190c1a160809030d090e07050906120a14010b0a03050106032309100203011d070804 73
    0x10952b25402a5429000528600ca000502001c80f0700082e0800c6820030050714480030748035114440c4034081560316084455000c100d803d081c0703450720100d08507944825014007145c039103003c6010403c05810110030140782c54103a65440c0b503c11040d00c0c2d040c05000740c0448107041c0e03403140360440396440c914140811042e52600424031030f80c400c0c012030600103041203600b5036864011003030020080c0001034140c90300c03104419000040341840f01c4402c61640009103185891001e001000e2019005c490001880c65401e9100c42850309207003001d401030165103605402101c0c40a00425401801d440554130303025019400381d120a0300071100b500540d14059000358007040014440c140305148507500600c03407400440c01340e0001e04e440c12102001c0e408143c45042c0031604141c01d60301070189a014107a80d00c3c0030420460b514127034401c148980c500c0100340b0300203800071071f9802c1018001e502c0130103103882c403d55a070f503905c207000d00c600d07200710308100170070f0f01540089191903100340c1c0114082e0f50450074 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 885280548 1250 885279298 885279323
    0x10918060b0d061401090c0203031302240318011508060f15060a050c0f010e070611010e0105090705032e232a07053d0501060f0c 57
    0x15804001c11441c0852544040c554190400290b0140a04400c100ba40420080740794900406403055500b804407031b00a6400c1801000f401c51551081c09031000d404a9200038282a00c4c141031040144120200011034000401c1024024480310326403c03151442000f0010fa11104003a41c180c0d040343d02035860250000000b06410b04041e0741c22903008103111040d000090300404c001801603002c8858100491804142107a09a2081c40424036140e10480280308040c0b047c4040c68880500d4001e50081c080120060b4020800035070081c1466040c4d103008212900b020000e840c0e0707464680c4500c502c68490301c2d100140160002084800c130240b0076038010213000d807010100f00541404408034850705102e245070004183d01c400c1e00d80c0243c003032041040c09411410640040140c1c0345800300f500300c034204540307800a200001c2c00822070141d1074940c5550180d18402070b03814903131104080f420010301e9100b018980240d61059040362059103c003000041e0301001684d44080519019000035002c00c13 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 885281798 1250 885280548 885280553
    0xf290a1a0405090702030d090c0e06120c010819141f06080403030c0e0907080108191e02040908040602030d0f060b090904022404090b1906030c0215070e0108010918 72
    0x1c920f642000e114010303203091452102c06202181c88200e8140c0d0000c0c13a580e802c0282d1325480d03d506810820030344014404007100d41320a69a005036800040c1008140000143e182c0070710314200b941d00168040601118001c40a00c503400c040645041e00071412000b85110751280c000340b8801120003940702c01c0f6443c0d81e1504c01b60004c00c640c07642d95040c004184421400c543c0c8011200b48140d41030744654030f8550506000900e451012801c0102c2d5000925508010490020084110001c040d02d501c40302c3c1c2c00d40c4003003000f603c01d0300c900911440f00400e010035100e8000c0050003103054801c0d000c004c0503426490510a9030128451944203002c1040508060304141c5070496002d4005042c1e10810100c10341e240d000000340240f040964140480e007401461381034080e03004000002c0301ca01c2031001860000c400010080d201c0c400500d40e9422080403a24002d0242d0724a05a00100c1140e0340c0c0340c100c0c006031100500180490000d420b580005c82c1f00000b5108107181c51100b1614880c4942496 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 885283048 1250 885281798 885281809
    0xf010b090415110f19050901090b0d020d0c0215070906080412021c05120603010507080606030a060506071101030507110303270f0a0201020d030902130f290a1a0405 72
    0x42d902c480b481d44503c5450001800b04000300700010390440e10316034031340007940701c180b4031340008900d502000740400c8590450780c0d015100d04262400886e205a80300100c5020400900c11008a071211078185000340070340a401040e000c3d03801528681068950790340e40001c0703a0070baa045c002d8001240000004c600401c4071540f0121210382c1c10300403134900c0d000350311019404580c08500c510000d0b200065101d40c14000d40b01c103540018055000380442e0074504000340c030b05040105000e005003804800a100f88060381c01001c0107040140c01141e81c0c0c00036080c410311031b240c8601071501090500c00890001c0d8818010f0a0140312007401450a40e261000700702c20090f1549031041140b00074010044640c0c2081c0008942481100010205410107200181c144130091f0500028546000c2030800540c442044200c2c074100d22003400610b03005d00d000340300c005007601c00f03940d601e0203626404000084007403520180840350840d032030403000d5a10ba2140c02000e8117007860061000041c80104102e0901 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 885284298 1250 885283048 885283073
    0x41a04061e0e04060b090111011107030c03020a060f02030406050609040510020c120309010609060b2d0706050a050601120209030717030f03090102090103471c050f010b0904 76
    0xa20b0081c00682c00100068241c0c1c1280d003040340c6083e000900e164083d81c011044884141d14036000b403203a034072807524200d10380c02003590190a00c961040414101807080c46190031140d4807040402c60300e20007400c0c40c0004d40017100d048411a00d40008212240b91000e00030344034a6000e402028040c0685800f01d0181d000b2101039441d07481140c002800340e5005901941c86600007000009082c0e260581e004240d5803d603000ea580c0c69010031508075042d68000c0b149a150725040512800c040303683c04440703842c1c1303c1c00314041c100600c0c110511181c142e0580101d4003d4000342e861a107418244180e160807071142d0707440c00358103620481c02044041c03450f41c80c419098002c641500d05000d400c4644810681c0300700c5509440b40d500240480240da01441200e030200700440104910004400501c000c0055860028900b5102d0369030352805880e00d07404c8503141500181c0000d43e403280043c031003410a4100642104c0f0b80c040c180b00a03603400414424034180d903100914184254480f81c84200d009040d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 885285548 1250 885284298 885284357
    0x28091503090809220614090a1e050c0d0f020703080702070f1e0b0703081b12010b03060f120d09290a020a08070f02030d08070819061703041a0406 64
    0x907004919180485a1240d4401071a0008042d407680d00858100b0034502c0300240562301192030903009952886c8100b10000c0c6034100380b4000201d070707240c064400c0744a0091810302d880c05420541c1d000e4814418ad0064400f0510945a26101d51940c1d40c040e622180c0034010300c0c4c2c04c1e003924503081040c0c3d00700c11240c82491455801c06010325864000003c0260b001c03001c01c1d4085032050301405205803041c901c3d0300d680b41c0501706441c208070050015002d031240611901d00e20b90300110100d182c56561050020b901d02004184050056051071220707203407070a00e142030307012480030040050700c09070020018145c020107080d44440e003400c00711990000d40010003072a003144141840000001c03042801804102c0c0240441c219052640c81050f14000b10020003904010821007442601e54000c00c01d02c0d0043c00010b200980306417108070a000904031603200c88074207034804803c0440940040001c00a588202040c40c2c100503640664400f0b900c40c0d07116400020301d5081d043c55901c0300350b00003082800b0703 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 885286798 1250 885285548 885285589
    0xc06011410090b0f1e0a17090307050303040b06040e0d0f0f0309020609090c21010f140306040605070c060218190b09090402060702120f0c04060f030828091503090809 73
    0x255885d034075450540000344003a010510640c50f44003020b104a82d20303030707228140c840158a4030b19141d640e69103c0c0000760009150007d4400410714582d140d4004810742d484c0401200c00220540704000c1c01daa100c400d80c01c0100d000541e000350900e01c68015001199006040c4601d8528070301c040c04031581000304421b2090b5814005404589807494000c40042c0004201c40400d50501215041000f00743e4804a00e5184601007103007180c6000c1450303a03001e60403100025180c1e940400641d00c00d142d1000007000284001292a9602d100c00441e0150300d07003d0300da100c1c1c5a071010700404107204072801000c4004600384940429450306024a5503c28400b83c4031038100f100310707030110342c4031887e080b58880c09070480d460b582120007003040008000da038102c2e014404280b034440d003521000f040e40400b070810040041c2c1c02c0b114072203010309500c49490720918408441e07460000103041f40c1c110300400300e007403032401c20300501c440c032034064040c80c0741d0480c02030340c81c1c15011000c214000c51080038011112 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 885288048 1250 885286798 885286837
    0x30206160816052401140d0c150503090105010506030c030a18080409021e0f0405060c0a080301080a030806030d0e0405070915030b040e0115030f03050c06011410090b0f 74
    0x40c01c0b0814100e0489104500500000c22007200c084640070040060554141240380108a003007846d00c02c032030507528252038200321003006007484064503016030841803081d00c5c4400b403480798644c4240150306c07404444d0300800c81a601c987c1040041d20041e5050f0b00040f80600c0440d00e0111158051034070b5103650286440074035840d640f03000c101d81095000f084c0d00d0354003003124248401c1054044a220320700d812414503001c0600700c036101c1d9000e103002d458002d64010441c0c045902d000c00031030041c0743c0c01075001c94403036070340e507110f00e54602a801c0100c002911400200305141800100c074151000d443e103030300c9041150f0400740001000001c00c540100801c0e2440041d61130f03200e25145038010759540e00860f50520540070f020580e000c150030741d800e6a04d4078103036800c0008030100c5070040d280c0c400d100c10581d82080c10b0480c1c0e203000d00403030504075020300d100010b402d10510351015031250042d01c8800780140344040c140d42c65031030791086204482c0b0800200401d003401d0300c010140340301c0700c1c442c15444 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 885289298 1250 885288048 885288067
    0xa0c020d0609110901080714030709060b07050706050f3403020609070f0f0b090d050303090a060b01081e0601020708010e010605040e0325020d12081006090302061608 73
    0x1401160200340d07501c0e6502c030196001e00c582c00c10321403540c6200b503440209551400d50b21554426582c420000101c1e4614555602036130284082401440c03442020300640d0f40342c0310b40d1078095002400c11102442200c5000a105000d036046e6190b04621072030700c6041890310031301340c0e903800c021580c0041101c0781e00c000305a08062030a030b4913041c20302076030080c005454a4000d103450071602d9003203220b1414240c0c0d4104000741c481080c840540d412440c1e10350711134800e1804545070f04000358000740782c0c0c04040f04202d0905800522003c1a60040d207017800440060001501c07200c005590705508011001c00100e004022a8038032a00203806104680003650ba5034000750840e02012000c0341c3d0359460300b0003008980780500500c1016454100a1450800009807550403900240b0825152802051341d58055558074124003c1c1603030400840110150b05120081c07132400c08882c440b6a001c03c2039008203900f80328501c0718003502e50250040f8905045805010114807604c0011121348904003c1900c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 885290548 1250 885289298 885289309
    0x90403050f0a03060f1d0a0f06050607150b0d050d0c02030f03040f050a06110312060316081e030a020c1c020a0e09060c18010e0a150c020414040b07050a0c02 69
    0xb800025038000131050f003400b88219100700e1680c03100c1114090802002c403d40c1e802040c10707800442d10301000034112080012040688440d51186900000c040780e54814003a4500500d159501007036000c20002141034200328221940c0a40a0701c01d41c8503c2100c0411401050004400d600040440c1c032102106181d00d491a8415000415514041182008141400542c001c06402c0a050cc102c40642c428821a940d00409150482051110f404140c5584043c409000a01c035106103226155031541d0540b9940c40c21306210541d40b1811080c0d4840c0d0300004400d03207508101b1a80544902501c40040042d08540840240808020301c593700c0010780d83d01c150340c030040c03800d03d024030000d143c031000c0076081c0a401000205000c108210400d90240b82001003651a40300342426404004c901c8081002000590042d12a0740414203240501c960030800007110140301711418070070603402900318100c200007514024012508000454015030095000c0d0000d007031a49010b5400c680c0503000960f = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 885291798 1250 885290548 885290557
    0x207090f09030905031b0907090f0311030d021506060a090512071e0303080c07080706110d11090f0d08070c090504030912030804060519020d0c0806011b02090403050f 73
    0x148241d03544941c0700805401c0101900100f600320042d010200c00e0a210108481e800c0c0700551007003c2d10000501458010218a40980480c40391016190344900c0c00c0c4203203401c1800d14074424410981d011184620001c1e5003640c4107841c500c500c0c3d96449420074012075401444410003484080100407800d0340741c45d0104030002009500070150289010444c01d01311748520001542680310003001c0c00842d41250085400681c1c60401c6981e40690b4248200783e030151110007011039040c2001c400b42e00070034130b01403c5140c01244082101c00d0151403480154810b004503181c0016a51103808690b180c240075121074280103d800500d080955619440148415000b1103803041e621030601050550210109020f06190210030b0500361050301c2c080e003103c600810080146450304000351102d02401c00a4891f0201d0040a5403540720203c824406083d0500c1034800042c08140010603561181c1c2044103050200c503405480700119409115030344400900950031f000b405c0121000302200c020061 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 885293048 1250 885291798 885291821
    0x6031f18080d020d0b15071e05100b130c02060109050c1b060103060b0406060203031906261605100302090301020403081216050903031602030a0f050328050415020709 73
    0x607521940040f05a08485d5510b00c624018071a224a403008010000300701c8941d20340141070030340c0144080180c2291000c6108005045000d40809501c000180e41c01c40e00a2080498586100b84030200d05034044030500307440d46005910031401044013240a522240c1c0141101080301c0c40d12120201c01100e8682c0ba0384031001c154003400041080c40020b00c41c40c1080001180c0c18070a141c980360000396203000141442e00305d840e49c19030030f41240285501c150000c0119006e654041904040c1105010141c02c1080c20280500780e580a080240c000001c0140c0354020000300d00b6240210341107000790800e040d010340540d4200008004542c1c40d030040c1c801c030ba1522000716000d1500c2e400103082c40310346403041400d1110502c99035807181d03000300503507640352042c2144132001c01c25400042e19202501902804040c4816000000e1290110050000c150700d00c0410303c0c1f804032a1541986201c0007405030001400c284414441014401070f06010096a8412554025112410301e0100e40414894 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 885294298 1250 885293048 885293051
    0x30703050c060901110304110d05010509031209012703140409050402040f0c020c01050c0304050a1202030f060402010e101707090504150e0f06031216060506031f18080d 74
    0x1900c1c1004010002c0a82c4261407100900010502c0c507070407041030001030402031050100381a22301d601d840b0340100f0a0000c3c0c0081c001e00140c03d0032003190351258001c1051426014040000070084201406040303071240d041c04100c1101c084200502d03082140a44040f0b0400000f4024058204003030340282005c3c0a04600002d4030f410301d0f10410084402d940b056480071401d02c9035035481d094010030000402c500c02c0c04c0007962000000c075002d00354411a0051684445c0010700483e1282607200c1407402c01d44264100c41d200710410005a03070356901201e0090005540303005000d60f50601208081d001a0b45041c601c8000690940d001c10304d03442102d03800001100303a07804003c185404d0248401c10b080706450a100c99003010140700c211180100000e106000701d00214500340c800300000701151342c0780312403140c13030b4655000c8681400c0c0f00310000f500d405007088040307440c03807034013107100c0501c00035041034202001c14105001d805800e24010141848426190310004581a000108101c0400800 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 885295548 1250 885294298 885294307
    0xc0819020105101e05060d0e0609060a150833090606040c03020405010905060a2715110606130e030403050102070b180318040f0204330c0204110c03070305 68
    0x400c4003c400b5a0350151900503c500120440e010400c40d031001a507030141d0f5150340c0c130240c880100b0040c00e0b9092805009204020403c1107100c800f140e03141c027601d1489405d010340301005440340c40c030708803600078407640e40c1008840081010504e220503481503032644101d04210710030641c908241074229803c103501c0e007240d001c2003142d140a2040e40b210303079a9428214186810309000900303110042c083c0500861000414446a6001d00ca0300700d02c000c142e40d40b032580100010403540915030103202c0ca000602c0c41500304180580035245030303807404c10300c0d100600040c0c2e101d108104480c0541c42c0e4984039603075a04c210a00d003190500040c030245000310000341e070350751035071032b01c5032100000a2818148030f80704140880350300000b1044422500c01e41e203e410060700590b000400502c968007410741240d20004000500418500094450343c1d1090b1405070243c04000c4407250f810380074203040e0002070030640f400005140070741c4450311210040d2a000d0604000200091030f5500052064022171004907 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 885296798 1250 885295548 885295561
    0xd08190c0c021525080f13090b09010627050a17160807170304120c05030613020a09200c0a020a0f0b0d0e030c0109080301050301110702030d0c0819020105 68
    0x10701c81100b4070b4000102c2407400c40c403001100c50341013030f043e00e103030f840303a0001804010300c00710609880c0b0407990050029070f150741a01401d8401c9800348152041e903400d000d10f8a01505e0803200850480b01c4c16114014643c1b180840b001040c03601d442d807803400144288012841c0d40b038110f6200017400481407020303804034480e00c2e0280f0b880c101191035a40d03101d00700d80500c109200410701d503044481c944808900c00d41489000e41c00c0d802150031200081942440550a10140e00c00c50401c83d2410340a80d00140c0b184000144103292200f00a50448031500080001c0011503100184050151401d060300c1000400c1c022a164005c2c103505186038024041c0c01c0c1075107005d000d040014910b1002090070249020340859180c040c801b1404289a601c14201064040501c11109890641402042a044640390241c1c0310341080c0545402586403c501c00a101c03a40021149105d800a006061182ca003510071103403444030190483d907000052150001000d56070a00916810345900003151a29112 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 885298048 1250 885296798 885296809
    0x507030614030a080702090702070e0412080106031a01120609060b07050c01230a031b0807020d020d1e09031505040b060f010c030809030415020f0706110d08190c0c02 73
    0x102028802c2d0880110f00001512460440e11074075070560700d000440e42d55020aa003800c03001c0d401450407092407000c1004101d0300c0340c104941242c01c0c1c0c070790400b50790f00c0c0e81c411030440d030803204092455952a40f000040c0e6025045001c4d11a01c01200859695100c1045005545481c1e000d01001000400d071081081401e0116084400c070038a00380d40c0c11441050500040001080c2c1c200c0c02040002d2030003201403080d009400c040701041e217540c00e9412007a200078501d00046960800500078000400c8842d44007007480c12a00420303648a510030400314a81211001721400d0150900030001000800564905400700bd5404840c0002429140ca8241100c83c1500102003a1107000c0d4208403008507a0000400c441c0300340c0501e803050b107540d1013818807031942c4506d8101c0c070036207440250207450300ca50002d00d54125203d041c0c00d85103072641e160b00580e00c04500d80d007040d8141d0000440000e000d441440956070010820f01c0e29200c50801d10a454110303107001480c440081c4a807264030040d030500 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 885299298 1250 885298048 885298079
    0x617010c0f020d0809100e16080111070b09010b12031c020306090103060504020a05121b0d0c1809120e090f09100914060a140a0e030307111005070306 66
    0x107030611105080c60910001d496007503d04001c1c080c08070f002d0210307410b84801c01a41c1d04c18850700c2401c100d2000101540c580d61101e400400b00c10107241c80c00415507100c18010150031a4488030314504092841c0c2d40c82d155040e0080908000b596640551a04e81c4e603021002050910390f20080e60f0780b05840c060008011980c0c000c0c2d04103070350040050051640390b2400c071504581d001000040d450711a0301c00070307074550a00c0d88015031000e10307801500582c000105542601078814030350080361456000c2400b40c5650101400b42418600010800401d0400741051508248400780050840c9503992001c40d021514922400020300031200340c0700f607040c4403003450380041c94545487c40754509950019600c000d4504504112511031142000b0001e0280d120720100c00b4101c01e4806500e003407030900005003803070b4041e05240c00707604002c50094001445080907254441d0b003e5480e43d602d1140507120782100780003201c1584108680034030194500c0c41442d002d03002598000c14200e250480d11200c10b01e2 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 885300548 1250 885299298 885299321
    0x615030d0e21010f0c030e190b04060c02070807030f0b0f040f110a0e090604060b150301091109061305010e040c05091c0c080309010f0c12080603010f061701 69
    0x30140200007040c0d8500420140c0d0484142c0c180c1c401c8401002c0d41c80c054030407404c00c207030194100400000e8068250704800d4401c051241240ea14500c2c00d00c200881054103e40504000d52400114012685c25000751076100c1290044850319541d80d40c01d00c0c50100c060340203407103c46400c3d410408001c030494880d03400035a108008200750516883d032076080844110000c1c002600948201e109850310203c0340014890680751110301d2038404240380c2c88050031502140e42c2c030b190245100041c60903001824071502c03010312441c21603081c0104070700200988010342050620500c0409090b68441008000c1d46500b461403c0c038a92a001c0058420b000055002d4803d90a00144880180d8410252040301800b164891801d01c1c00a0b500742c606140b546007d00010f181c40400700740c80700000020540070f4402e80c3c6d90000c0c105402011210000f006100910760348048001c05403151241907195084900180000f42c50070303400e03540f241107a060354010703240c01288907401840d0b2682885100c3d0141c1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 885301798 1250 885300548 885300557
    0x60304050105160c21090b0409020d05072d030204030f030e01110616080606040504020f072a0b0c010e070602161a09060d0f020703091809030e010c060e0615030d 71
    0x150145d6900b003140301554400c0e4060703008540034048451107081e860000744841c0a1480ea107a4990b5801030207507100c41c031294074590030032000c1031a0520941200c082200c400b680c1c1003010003080c1c02c0c180550112988081019020301012000c070b80e0012502d00051310989481daa120540000034040c40401d039a03200c2c0a4010380308010013140e41e2035060440154030700e00601d55940e558001445402990080751700a8400f10b12032196043ca2070091980b60301840c8012100a5004041c003000c2c40036403501c00c0818030f080c01c1007005441000107020f01d082054008503850710344051141c50205694040c0c80140d20180c000308810b82c04170038910142003a00c46441081401d540c11078a240300d4002e170b49001e407000240304880000c05034014003c540710349500b55550611401c0007031144a5900490000c0c13a0a640c0851081031144680240907a044e00c0310f00e0303403071030400041d5500461201c050b240180c650a203558900c200f4403400d1301c2a44400f40b00d1046c80404000d1500d0140500b202000b0b10 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 885303048 1250 885301798 885301817
    0x609102a0b330114040e1e04030203070f0f060509011b020f0a020121020a022a0114130e0a020703020c090f061011030315040b011b060902030a0206030405010516 71
    0x3a003403203140c202c03600c00d80b04401540b80030b00c000480c0c000980c1c40300303084048004280403a481c40307040080c4e4040e42c1154607240c089103c4181540e072100042c0e4006000d64020024400001c40b010724241d02e041c0a00340c22240100390b500c4030390544000316401d42a50759102e10315044c858000722007889109041c40144504503840401559543c2d103810041c0c14040341c50203452407000300c906260045003880714190348800c402440a5074461591a40f280001520320000c054100c0c15540c0342d01c072081c140e50740c0b2400305600f031100380aa8400720010038500c006041c08104c213500722005030b0255107405401179450721a42802030404000110440c42200d0308028030031141e000c11b40e40340e00440215400780c1801c1121b00d084c1d8420f515a44440e8541c00048108500070300e40e01c255441c050b4040d81c0502084101d8001103800f10a004d10700c0e420300d0099020030000c10780030b5100004061002d802c5500c0b039905900012040c0d00b04980454090b91a00108075450120f15039500d001846403c1c00e0614 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 885304298 1250 885303048 885303091
    0xe0108070e1e030c0d0b1501081303030e0c12060103020a12080301031101180608040c0b13120f020409080301090e0c0901030807020406170a06060b090609102a0b 71
    0x3551542e041840c2c014280400ba08020b98060000704401003005044e01130101c22898503080200b811614881558510840381c21903500804200348180c856188864a11130141d9090b002840c020b056440c15106034400251941c9440008643c220340c408014004c641c511300c1001051038194000160481c1100b03940c00c0010b5600060fa41502d9000003003400049507200125280c03200407a18020905040030001241600007105900a90165060000c09a1200c11194841c1308500040142c440790700340c00c0064040000112403420700c40d080c903101403841034000070709480e001e44c02500c0c0b016000004010400c600d12541022121a02c0680040c40c065030000350600e4051101a002650000700039085554680c01000500001c41542c00040c119689141e55030203d01c0085494501d09540811800a0803064a540300d40c02848103181035409000e100e00840360501d44020f100c074032281c41c1641011160b06050111804071807501d00000b90604c014001c5000d040e04a234283c00e40d000c00003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 885305548 1250 885304298 885304309
    0x13080c01050a0f0c020a0e190e100e070b0c01060e090d020303071b0b090c040f060e070f020721030f051201140616110103060815040b0406020c0a030e0108070e 70
    0x801407158101080c80402560301604d030460705034402980001118000700b4924102082e00d4020120040c0900e103140d680048081140c00b48400101c0e1503000b00082e007200c81d400c1e000180e05c840d0a1055070012640d802440516410900035409a0f0b5110401403041b103607404117095022421000801d800c904a00000e034980c80003628003820030942c44916208000100940400070350301c2640024a46042e0705199241c140200c42988a98203200704040d00b0382ca140641019911a18071105490f00c03000340545036998440000025406440300004d103a00100e0040380c51070b1401d45068500d10360b1f501d00103010f6001c4025403828400e090000041c4621080249411340c5e03010040e07034102c0070310140029543e00a80362440c110240381682102048509100344980c02c40a88041c000e00d42c46075000ea80b92034110f21082003100358500081d0100302c400070b00c00c0d00240a128010318200d42c0c40c00c050300f08910b8a0065010445282090410303590101d48658040d980e842e203110440c110200060 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 885306798 1250 885305548 885305557
    0xb190e0a02030c1c0c02100b060d0c1b030215010e04080324062d070807030c1b170d080721020d060e01090b01020d0503070f170c13080c0105 62
    0x203000ca540400090303482c0320508110307210b080422491280c0d1014201048003c1c007000301e1070b5001170042e1904881c1ca0003a50050100103480100303618100909030700103074024000012200101f1540325080d180b40b40c4c20100348003801d402913002d4240307803403041240e004069041e031180d920100c02808100c0450702d0581500e4001d0602e51305800000240c80d203a2055180c40410300e54014000078100c00d0110440e42000254000c9100700c0d0340781d8280c80380000300b0b40541c40e40540f402030308201400c0000d2141c080329425900c5030304003a840a144c001c44200b080e040e80c000108124a101409010544c104400b844020643c84c0c0021342d0302d04020010047d884500e0b000880460000c04280130203035640507194035808003101001601d070f81e0b00000d080c4910038416010160b180003a41c24865202140440c5025029250503255803240399044403000482e080000070000c0d000010131032084030068050041d0361508803640c89112007039150710b00903140d500980c01c0e5030081c3c0e0030b41082d90b00705003a81c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 885308048 1250 885306798 885306811
    0x412030e0303040b0411030c0604061d0607030f210f020d1811010e060706050f0402131404020d08070609080c100e0601170f010f0c1202160b22060b190e 67
    0x1820501e480306c012a1034403120014040d84610b012170b001c00d25071b600c03030940007600c955885014048008041440381d02d03c25802c000c7c00113025001d030358103030a0094541ca002d4640045a2810114a07606144111500c42110359034440e00019000040700841c00313010144d045e1034040b07100301040e0303035604403216000600c01c038140400061343c010f103640c40ca415200a980c10400910042c50400040c600c01c29080358200c1c4100004c0351800c007292001d1140c40c14085404400034015201c40d020021154050740c0c0c05c650340c60003000906c00151490190140c0341c1c0c882c08000351108805101c0d82e0401e002c0010000001d461b040c1903000c0000d00080c60b504540102c07560004e0714101c0348015052281440c01581d003903080038080da480c082c06031301000008a0321380d110081d1126006c540000e910410b40d08601502e210459400400d00c800d05c00c9410510700b58501c0d03c03e0560038070b4200c501ca40e4280c15155a03945a101c05410300b80f03052102c02040800c0c401c40c51090178004030341e08810014100 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 885309298 1250 885308048 885308063
    0x7150329040515060c0d020f0708030f03060a031a04060614010c120306170709230712180c05040506030a0f15060302150c07060e0d030c020411030412030e0303040b04 73
    0x4100140c581e0303c0c1e04800200003818056880f908450844e030fa490340d0744103480051182000c0e00054150200e04242540c420002070341c940540164072412a4001606103640011000c1000000610204603c180c40304000d200e20f5280c9024240b1380c1c102d45180d8046c0f4000400c0300b1003601360b6a0f0000045180c2c1c1e6001c10400e031401d50100c01200241070942001100719111952101c1c04040000e0b81c0c02210300c80c1000344202012006480194500ba0038201c1c4008000703400302d014a4064a40340800031191000090445885003000212502e80001a22481c0d001c0350b0134800b03418640107050b0702880540062000752059075130b4841ca20fa248a028000d040b40e040105500486600000d0007150006c214051070114110000340c55485050000c1d0188214180050000d018804001400500801c40708400703030541c4054032041004081243e1095590042100102080c2c0c055805a0b00420a9105004100700050115500d0208410f0a50710520420000582d9240364076072040c3d02031030 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 885310548 1250 885309298 885309301
    0x8010f0e010c1209060209040c0203180a0e1812031609050a0b0405120f010606122f0a1701090219081b0c0a050d03150501080105151605071503290405 66
    0x1800d4000740610382031148d2050030003180030149940040038000d49116a00500c0ca0300803894104170f440c1d03070207114084c42c91140c3c0002030342410303280070b03002c003400e8201003a201c1d0fa8851036601012a8402c0320040d481900c00004024895485a48600640002e48100f0519424000d4003201d03801180305481c8a445940d50040e10700d2010310510034444040300003442801d454403c0544058680028080345500c0c108803100c3e0b98440c11911042a8a080794080e04610540f4503e01180d00c901103400612606007281c041841e0b50454807402016030880c0141c840090b10540e41e000030000742000100214001403000e6005050203c140c09146500010341d10200251240e040000900d40134180380038200d9203c50082d05074100fa00e825115101e841c0d4140d485070b00540e03c4403c00c0c050690458080d1241c0c005400325100180304040c6c0715600c050280010b43c3ea01c5241860036089071811444030201c03100d040c0e405000f511450950400c0303110305032003103c1c84000f0306180090b01138416500d410 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 885311798 1250 885310548 885310553
    0x915090608100b150301030605060913120305070c0b18010510082e021308010501080307050615010c15150e01050d0b1f030506040b01120b011e090608010f0e010c1209 73
    0x2071141040c202c1244d006a103a41e903d0600400405044554500601d0440001040181100100407c9503404915060345074103080b011001807100034689400c3c4081d040c880004552040d9000340710b0100e814810b18656407090740700e4207460000c2c01d0320103441d40000050000200c0414807140c450b14500c903204078640141070400c4100d10b22241061a0361000912034110422180c6c1481501d2000703009000903640c42243d40d0780c0b803194100141c026005140890f20640c40321082c6401c0080c1450a00007450940d00d032400b894100e44014440c2d030350342d1000b0b00d610407034002c40306005041070080350003d0b40c50100455407900400c04000c150301040c90001c2c05540419112081c000407442ca6a481e40342c41e89081030f5680340a03a4151140000d150002504e0034189007031200d52a4040801d041591070714840c1c6402090012a0103410f500c1c035400866640a50310900d0024602000040b405906200d041c1c01254032001d020b400c1e5034141b650700d10030160403a820044a061440c00064103613001d0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 885313048 1250 885311798 885311809
    0x60c020706270f1202150405100305101512060f150f090f0f0302010e0409020a05060703051e030718320414010f0902070510240915090608100b 63
    0x3e4000f40220b0300c1c541c0004c90804502c103244d04070750f40700340c8480d044842d00b1040c4101c140034a218481c1d01a403158040e0704401c2c82500140d8103d1450002449401d46a0503245001403000b0384850010320502a02403207168903000b80e20050a4540c000e440d03c41c241006a6000f0070b0940742c040070700c50107180700441e080c030400020005003000c00d0001c82d090703141ea40d1944c02c030050b44002d80c0051040303441e0307a400386000d00ca5800400c3d801040501c3c000c0c503101c00d02806400030700302074007804030a021a614030141c030308003003a01e421140a1203680345080300e40542917450701c0880c460664500c0c3e00034402d540f6200c085006100d40c8202605800308402c401c01c2c20075404c0f5050315002800e02c08a410f01008510860b4166122003618a10090320741280d17134128054058081c02c20b9010000a41c0300811552080916448007500c0441c9581031300d400c1c405c0c0a00a40c000720450307984504040324007001006100103068021400e002c80c52030038400710f60700d0b5468490003400c0e0366a02e400080c0341e910b4 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 885314298 1250 885313048 885313127
    0x3050d020307200717060f011e030c1202040614030d030b04110c07060e1905010e04090b0906010515090d2a03030906080a0209010206071d03030c010504060c020706 72
    0x44400b0111500c0c050030007a900c0d50914170078030700c40c0040414040c590004c0803030301c2442001100000320340c681c6008a620700404900d465100414001003000c00071421b100040c6018004111402c0f030303035404030704c18042201c906078407400c03651240302049071580e074020442c2200d0313422500c1c022611804500001d0f000303041741200060240710000b03104a04060100e520340840e1641d8840000100c1400c0c14410b10308540000c5a5104880441c280210b40c018500504962800340c0f0000354400503a0fa12810302c40161600d0400d4ae00040c010882c0c0d190840d000443d48500030007040c1000d4810340030400940402000500e08030400180074040340c00507044080d01c0801041c41e170a070a0303882c1009001c14809025003000030718254001425a0b2190084803900941a030040000740d803110720440b02410ba400c00d10002d040708601000d038980d808c201030304da030714024000041e4030f003400e1038408111824001c2e12819504450710411410f604032040c907a49134040200009000d401c9180320700a080e2 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 885315548 1250 885314298 885314327
    0x40f0605030a030c0203010c03180f0816050a060609021c110903011107050609030a050414030f01060902040806010e011409090109020418050c1e30151303050d020307 73
    0x10b610194800d040d8800c1052100780c0c000c2e0000c01000c5150300c41102a100e00301103614140f00b01e002032a00113503100085101c420701641c522420a40c84200141ca030307036405402915107602007480c0e40d0a1205521a580040007030078001c610b8440f82c02403c110952a2030b94200e00e2a035949000103c2907001000c4582501004000708262181101d1200c010b802181069071075215407400603186c1c190010444c0c034045059151203042c17619110000e11030310070ba0700032550940240d40e01c80d64180d50134051000906016000940ca65080403001c41c80c10a05a101b03400f005843ca0042040e680c540c40718030385140042d00c820030f15644075a44607002d0401003000030340051800b640e00ba503541101c008204201c0c81030041d40c2400b0080c10400004180140b8240740e840341400c0082e416240c03c80150090b2040010b404ea00d50500404822140001000c00340245c3c2004c1c1410060a0010280b60350045410146081000031902d0041003406652800c24410f94004049480d080c003403181c1030281c55 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 885316798 1250 885315548 885315553
    0x1b040609020f120a050705160f0507030309150e06090904170f040510020303071e020a0f0b0117151311040e010c0806030c2815020601080d050304020f040f060503 71
    0x2d00c01c02d059810356000c40c0055074000c07585000704000700180d000c0c05004518942d0f400c4d040082003400765101000c48542103c8800210032103c0c009003060099030011401303512424051458005268003070300000e40360004220b80068121300c00d68420702600c00c0ca80090b5440e02c1c280e611498450060740340d4142c038070324501011461141c00343c1514010300c29501e0030f46406070711881603030050b039803130000351030200100c1c4c403c0c030780156840d21040031070002003024411102c9100b0a5101c000a10700010019034244100c07100500ca003040e2621008560b40e01a0010301c1c10015070b964100b850303c1c0241140494980410b250300500c03205446a0441100090080000d0100140c425000304803000035000400d2800c8000741491802090855038501c0103040b20700160381c0410803840c0400035600e42140010f42d80400309107100d04c5070056141740070b980c00400304d03941001c1c4190710b00074104030900c04000d81081000700588030900b000d192420241e4000c2040318030070800d600a44000d8100c141c040c03 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 885318048 1250 885316798 885316807
    0x50c0c03040f0501031404110d11040906050a0b030a081806072907140a110a120207082a04090203010e0102030a140105090103020102070509090312070f031407021b04060902 76
    0x400c40c0401680c03c85509880810042c05490032002c1c03009411034010740100184000c0c403c580c20100b411003400c41c443c0a0508454001000150884500900688641d81d44004009440c01c1910400b8034603c0104c005140007245070351400d03020b120754410346034908244032948140740c84500c142c980c190382c420f058081528428100b50080724a4204c06400c00d4a0140824001030060070422086402d403100503242c010b8505043d00c1c041804201000d00f4450034100001107290b000c0c040b0104003540d4050a0183d03e800c0c0002d1401484061071100b0030045440c0000c008040310b01e94141110581d8040b64001003800000d00500d11407008240c954000000c00c0b88410703d550020100c4206000941403a90300c450520070310f01c2c000d000c002e0142c0e1000006100714980311040c990b01010010480740703401c440d0000c54001070800c0d80c1040200798a059007080c0d440e0103004042d2807041a410400700f41c41c11070002540c0750031510056511994040019040d41c40b6074200d5070103404d52070030540d41c4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 885319298 1250 885318048 885318059
    0x1805130f14010b03100912140406030c0905040912020f010b01080403030b0d051b03070602010213030318082a03013b060114040c0206100302042a020a0204050a1509050c0c0304 77
    0x140404000c04c0f59951440004c81b030f4524042c135102d091071807908d00d0081c102030500c0d100350300030080d810300c3c9000e00c1030303945000030143d035a802104642803040600500f100d612002c040d00e4070780c8a480c40f000031790600b44100f1460343c2c80b1283c2c55002c3e81515010807100c08560114501c0b11012002034124051480710403440386590303220150201054085501c21582c1d000101d080340680e08180c039481c419441c0c2000407c0c40381c2c11746500a11500d00200c40c040d99002e0032803800b00390f000355081c00244a00312482d405901d00c3c520758003d40940c02400128811403903010711a6584040f4035200300d410030004441c0303070110401499900068215201940c4800a03842d021445a1086109a0400e10003d808a00c0441e016004100392010300c0d400c0360540e82000040c001c100d2605190000310041503071400311400f01c86c620425550060700c444040340c014401522002840c0000385030400c01c0151814010500390411079001d01000101d40d116040c0c910740501c240f103500d030424840400c01168 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 885320548 1250 885319298 885319301
    0x27032102040905040c0e011203090b03180f0d0e09061c08091003051f032d060615140306130b040b0307150815150a0c020402041805130f14010b0310 65
    0x540d0340303501211401daa038508d120200344c01d80402c004c0004840c03000c104004022a4059904125005900c014001e000b00e2140c0c0b4145030b0200502d0181e015010440c8100c3d0050b503001661141502ca0740024940080400e03c910380c2d4020074070003610109080b90910510100360740150348000c0c201030000c501031200a024003802c0d00d280b204c1c580c580a0202406030950985412603078040e0301a0030100006074800115042d035070300030600307203e110030981c0018500e1207014082d12030301503403650b40051020028584003c07030328004400c04c0d040080c07003620355030800c0380d0071500c0000da00801c101d00f480c1c0100700605244c072a881e4145c0700f103071004607003541041785d0b010103891241d481c510b1076914a0f8400030006031407000c80e5080720300384070300c90801c04580c4001c0504c00c480d4245100e0240b1643e01050480c0e02690001244102c01c0d480380f1140c0c0d0705809113680000c000301c061481c5403c9500c2d02505611183d4006008145036140010b03485400e410500c040c800080984900c22440c005080 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 885321798 1250 885320548 885320573
    0xf012112120e0309090108030a0c02010f0203130e0f06040c0504300b01050117010f0b092809110414040519020304060911040c0e040c020c03010e012703210204090504 73
    0xc0c17041d11140004924542d001013030319281700003035440c00c022800a4006440980c14441d01230118042000700348041d8404400c240b00521a5504210141c03501c041c1c0a001100080c01c0c0030b01c034905000800154580c40400d44082e2151100d800b485c850780d019082c10f005089101c400c070359441014140d02445030500d03056048482c00e884002082061030320078084104240112000307109010400d01501540700301410603031102504540e2812220704001c401d4208291800d031100702207000a03c04103683d80581080700000c9610f0708d0a20381400c850b22002041e5524490003503039640c001441b00c07070359012005800403840c90119542e04040c28040d01411051b10141c844011141e503911050606120307651054840d6600c2989085030102080058000d500d801021031040300d03440d680701d41d028461407603d903600a00001b03a05100c5042d50040f043d00002c090900020800201e02094100041c003444030001003008046400010a10307000380541e8200500d003501e84000c10042255181544 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 885323048 1250 885321798 885321817
    0x50901110f0a030215040b13030c080d0501031424150a03050c011e082410020a021e03030f0c01140a05090c0a050f0d020a0b0a080f012112120e03 64
    0x2c59170b0030642015840001c6081c0c800404501d524030000303c0112896903185042d502c01e251580f042c44458036480c02e0b98025498200b180b694640041081044441c0340c400c0840c14034019007213210011031484041c0325030048884a0403861000100000310002010001d4080201a44011030300c038140982d4a403011281d03a40030420600c1e071031940003d42c2030b41d0034102a9079541c0610b1641d40c480d1603412201c1b1203514843c1201848101031841c1d03200044100011410f50041c40f600d0709070700411000705107500c001c0301c0300d1400e0145003d140c1c5000c0121105440a605426910061400003078010211800d80d014981403010610401450ba07800040c0907180000032109940c0b81d502c00c00005880d140700707065000c01c5040d42d402040c1020351300c0020827400103150400c031545d9461141c103950b1044141d0800215228100300700c20400205541c0509203c0b0910f4410600403521114600c0080c0070281c200340f00c0d503821009040c807581c0c20803140d6038070a00500c1210000310200369650000d405a = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 885324298 1250 885323048 885323053
    0x1e0e1e100501140d030c020a080102041403060c04060f0c030c05011404051b0919020903010921020d0e01050f130602070f090221040201110604050a020906100807050901110f0a0302 79
    0x7184030103000803002c424401481040e0141340740d030b01603c488002450407a00700007080000a01e646080c80503000904d036440c0c0c841030b0f5150130320406003000c07001003060707090207420320040c403034541e1001d002d00e441070382c9040c194406560b9040c20344500b100800e000305290300b4405450306c40460032036100d004031b10800c22201189101d40e08803124041244241e0b422441500c005000c2a0a0803969030141c21080c00051528002c030005c00c1c252601c0c403800b6100b250008240740e08a64640109600c601f00a202410031503c040701c00400b0f08024031502810000d0204850700080012801c8034581c6c0362800e4075250035a170310740d00a911911107100707280002c0c0c184400025110034034002c5442c0c01c0c070890706030100c80c41e0748040c1c8404090081c209034100724980d81d810518510800c481806240250010100060613204014012100800c0341e8064400f4071142c040ca25000f001007904107285082c1540c03240710040c012a140c58004420048078490341c00c8120740c400e00825000c0c4500d00136030a = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 885325548 1250 885324298 885324301
    0xb09030f0403030c1e20040212160e0d0b07120b030109050610060212071205040f060801081218010804170d0e07090b100e01090b0f1207031e0e1e1005 66
    0x108001d501d10903d0701412425094030400d55094100006d1914220000c01c01810550142c41201000e00c0494a44442d002e0001c01c1211058200410400080b0704840000e040040d650302d203000703043c0280c242c200740b04c10842170442c18400d0b60000071424202500800049183d42051070740e5030b2007a2610103040407d01000b260b01c0344042500c650340240403822500c0c01e88140e881c924040a1540c104c42003120511000c01c00c244c1c0005244001c2205075180502035060003501414420215180008504c04101c0d00d0b54011540159000225090070400125544c0c1e042001140207101c00581e68034000040c02200103080742d2104000d0925101201c0c0442d0300d80c1882c0c0219442e2170005907005018450615805200b00540c4108400c18502a0b4915031745032071030300c2d10340c001c02e0516070340c2c4402180c40032543c0341000c00c85505c403a46240a000d031003001e001c400005c407444895100c041d900e480405064074010400865840700c43e400114240a0301440d0360b0711400c2c0b940e881585141402e0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 885326798 1250 885325548 885325583
    0x120f0b060910060e2407030201060f030210030f0e1212010806130b0c12070e010305070e09010902130302091003021002211602040c080a0b060310030b09030f0403030c 73
    0x1492501c100860000000c141e41040000e481c3c130014000e040d941700c060103988a51200140e0105002c202881c0c0901d40c55240c01d14001c0d00350f078510b8100d601c2c01c1e001d42c1e9003000980d4501040c900258442e082c001101c11181650380050a2042102e081c9441005451440a0000d800030881d44d2105282c0303a03610f0340ca40b12066103843d403d941010004040d0b0384040081064910711541040e82c5d0180d842c0b0705420b49200c0b441d02001101c00d0004151a0240c083e40ca5805020b15903010580c2d26001400f01c0824000800c0c43c0018050408015400709024003881041c07040ea402651b0000e18404d0f20346813042d140d80c2a542d03d4001280100301103842e030850180009503500021290043d07904015000e5503245a00d50400310500c00401c41c0d041011025807035511803e0001e80c5d4959034070f482c80c40d0000549040e1446071310451300910081040004a400407005041602d5022400c200103443d88203c962075800350b02d2000008440c001030003c1010381141007211542d2107482814404c10f2540c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 885328048 1250 885326798 885326809
    0x12100f050d1205030c0c0706020303040204050a0b090c09031906020d0608120f03040f0f140706020a02010c0605041b0f0303020c06090102100e071505030a060b21040309120f0b06 78
    0x1103100401d2020407010342c155181c000c101841d800524004450f040c002c990a219140545950100c0d01581000003800700394140380c0100c41c2e00880c242c3c0700748241c241040202d0280d0f4001000c0210204c0b01046400140d54140450f420b0b05000d0068404102102d0408000960016107661744140c6403400c0050790000c0802c1401144840b00e48031030910605001800e04c1e580002d000f00c9011070004c0401c0c0c0007846440380214541c2c06881c401d0b4820082401c003602d0a802600484103540c0081c145000603070b0b115030007584880c3e0018020825480d1807800c5859061380c2c05100c074803640c012601042007030b41c84034010100e078060f9003150306013546d000038803605101d518400c40c0140c1040d2a140400b21032500148014110380341203d100c00d0b515016240402c442582d1030001510010500ca00051140901d00260101c968001d1608000c415a6078019031402e07108440b8810220000b8140340c0103174840401020310380d51410801d240c91600c0cac90320b610b891100b180c89004010204042e0b0800 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 885329298 1250 885328048 885328069
    0x117091627050c0a03020309010f06030f0605010f2916050a0c05100c0803060102120d0b01020705090709031e170d0c031e09050a020d121b0506010b0901020312100f05 73
    0x151150704d10302910f42200710701943c00205003402540d02d40b01000c3d1250300c07038800c0c03d0046001d407125152040c034500d0000d043e10b4040e840f1400740362002c00e040c0031001041c40003904140d01c1ca03808c502c00c50301c0e070311603a4400e0048002041c3c002d0500525036060080200750503503428400d100c10044142c0781d00c208100c20040b1801600000c0c811901c0d4000500c0c0c0b00d0003583c00c500705004603a05c4180303004481005034042c246115010340c41b10a0180f05503010132050010300f0085803060030a1400180052402d45240301c05407141c13001762505254041010200a01c0c5604548006103583d494500c900d120b61244c10805076040c0740078102d8040341c2c0301e403181801091041d20000b01c1c400c1c00010000c06000c1400342030b01d07680242045d601c01030352a00c95220f0040c0c82001403080607c45004050101d180246040301d8001c94406a0307000038901103941410742e10900f80203034a07543d415004034038601541e420803104c0304d4110188045a105024410200e40d928450305888646400500c55110407 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 885330548 1250 885329298 885329311
    0x270f070c0201030b0414150a0603060e07180f061e0804050a020f010e060c07090e0f03160807060905072408010e072f1902011709162705 60
    0x4114000e0401580301c0d40144e90210070080003c60700007044131a003040d4400c19100c2d6604d809106618401c14200b28240030001c0070750b0f08003000454681003c041d442100144a9020021404881c00407000d890002e1800342494010b806245a11928007600010801c061950000000341c84048407a100c0e0000c140320740e50080250540032190740c00e11030307008014222941403100480d850704032911000003601484425100400d0807905e40304058003150008072543c0740942010702910f0030090004111810545641c81c1040340800d1400c003103016000d00c120061480d42000300120a200c00001d4080c20f9404280c1e10b040910700350618142035100b00464030011403187d0300100310030007100010384d60041c160705040c16001c1ca01c2ca81e1082c510b940e0640d0207480864007502e030350804820002c00301c00341c4100f09081001421074002902d40b08141c0550703a00d84200800180144006010752030a8446402c410060903885078000e01c1a2541624441400c402d20858210045043e0180a02914 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 885331798 1250 885330548 885330557
    0x9040b041b030e01184706040204051002010203100e192708130b07020f0f0301091202010b13050129090636060f0d0b270f07 55
    0xa060500c02d41c09004031280c3c2c000c481d5600e880400000780c1203140c80408911030030308481c503141e108007414a94404108000d0a0086904143d00c80b0941240a421031300f1b803912100555545442c0000c0192003290407150700503800b180740d8680c0d2038054020b14011800c900200c94415181d03070040071044400c0701c414000d9800041202c071481241d5200320780c2c201c51619038200040512801c505041042001128014030000303d0803c1100f030401d8550281211924442c9010b50540000c0c00c146400d905251150001c562518000e5400354080c2515641c08000300e0401104000080d00070060040018010190192201c6040352144107141c10703500800b41d0210b040e01800b03412074903800020100c80003e50100310030700741d07560740c10040c205a100580c0114803140485c1190302c00045810382866003046082c080030794035640c40b025604004544424561200860207c2d0000391070000c2803142c02c642d44c05440a4880e440702e1155139480e01401c080d1150303484050f0f07107070040c5008030b4181c000039 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 885333048 1250 885331798 885331841
    0x4060c1a0c16021c080703020d0519050306040b12030307090e091c2c0109080c010c02061c0905100510030506011406070501150302130b011b08070804030809040b04 72
    0x400740d004040141a0000e840d00151320b04000d188510580c0500042c4d61010000c034889080590412000b040806240380003403c1a070804400010790714074851a41c10300030040000380007621607501c09820b98400500b10f000140c0650326041c0c40c0d600c03e54190b000511201c10120700c5880190b0703042d0160f40340d000100000b00749448501d00044c0c4803880c05081000381c1080401940210804032600c13881174000c4294413582000140581d0706c2075001c0050703a00954050209680c000c258910300640546100e592409000ca00303081e040d03014480d494007146844204014040c0000f44044004284503041083d82c40c0c1d2000705070b0b035110034403004015a010384014440620a404030303c10600c409440c090500301035554050a46132289071642608080110030429840c04450110781080321040400100f146040003d207900500140109007021142d510400c00c00184e04070751400780c20101454980391a8a0400500e0b032242102c240705a003840520380140c545881558000345d006002e9241c030 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 885334298 1250 885333048 885333067
    0x6050a0b042309041119080604030305100906090b130b0619050909070201090c0b0c03090f0a1502070f0506090a0504050711061503060a0c020613050307050304060c1a0c 74
    0x80498002102400c0001c2c40c007442a90b00d42502090044d417041c074940440313548070000d200035080c0c0d16007000620800e4400c200320f50f00d004240b80c1c0c0c02076094a0082040d0780c404c070a0440e40000d640c000c0c86450302e8248000361003d1950311944c07074510126134400e841c50011011406030b0703089282856200004100c1104140a900008012400a410603030708140c07035440000d600039000c8461380d001d80d444103844010458603640100280c4100480c140c109034004016990307038041e000b0140c1c0500000c1e969400540d6a0000080c020b100f2401c0400d8000201a802500c5502e07910407a02c0c000c48168000c9024500541540d203100405048e4900252521081202a220103800c03802400310724408000c80260611050344110340400074402c00521410905181410080528581e245850745404100d0342c00309078203401c14407041030100c440590381480350952190b000300810302d00c0001000500c154000d040c40700041e00589048025080b484c0c0307001d000442c00c0f02c00142906081020150 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 885335548 1250 885334298 885334319
    0xc020c270a09081b10110405040b0102070915051906120c0c0c08010e1204031220010203070806100314071214040f02040c0c0c050904080c010207060f06050a0b04 71
    0x140034880c001c010500040686419416a1204e1545201e4a4404510566003441001004400c0550150800c066a20321403c980e00d80624014180304544905078032200e40c2c42008840080c5c11402402c215040148524201c0340035140b142d6800f840c60340b0795049200318040f03c0001200c0b010f03200c0d1108030000c014040018a02c04100906110340e041c2c859020413080441c0c04040c00d8014000560b00640d000f20600d8200b08502c00c0003c010100402c0c000203043c0b541d01601d9192500b000c82c420030565140802c02c0d00d0500c4a006c880d0320100401401e9644104407a000b40420f8030203400600991104806441d28040704c202108445000700d2800c611400f400803c800f03140f040000c5c8400784c6c000650503080c0c142c800750792403048010710b802949040d203c1c0390a954510300b44400d840c0c109a0300e0102490451141c50300c0b816000d00014103200d5010100c403c00d000c0800219503e0501e8a8004001c0c5008880c4103412841e08030701003048e0801400103400c2d1003a12041f2828a85080304454 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 885336798 1250 885335548 885335551
    0x11010915050a110a1a01270509030c062e26030c030a05030f01080a020d08031302040c17100b04090e030409060e091006060c12020f100c020c27 63
    0x42c2000110a10040c410b401403012240140c404c1d050004090401c0c0d0003120003102c1a0040b008540c5a07a44002105d40d10581d0640c00c103034642004905903031513070201411030003805481c0340b02c0c0c0103070810080807606080112110f0110764000d040740720080065098107841074099a2421000f07000900b0a41180c000742c16852402041101e1505829810131030070344e000601c05102080d00401405184400c43e20400c0c09070040b100180b81484107a00000c0221060800181c142c2000001003030113004008206581590040c0040c0400344990000900f200c40d24041401945508000300e298009103030285412503404640f0075003882c0c10004014024480b144099200d403004000010b00b00e1041c0c000c403c0200315443c4800d200d0b182030b030784150412203000c0b0000d004130b10b05007040c49541e40010210f00000d41058000b080c40c41d50364410383c0b80c0f0150103003481461040151400318203005c6d410a0410300300641c2500c040c114407000b0312040f00c100712950000080040c002c180c0e985804819107 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 885338048 1250 885336798 885336817
    0x30e01050f06040b0a18020c0c1206070f09030210050a0f090e19020c07081614010f110a061b200d0c1502030717070513090e100510031101091505 64
    0x81d1741c030b590b4940381d400301002a03c0010400c1d00401c110f18081d000348040c0748190001e0783d402500d006c1e081211038840000030401ca050003550045810968410718642c8040c60340500507031b00d000910380c4094001c1e0014074160000846c1c40200000071803180804c030b02120304080b000c42d01500c4000c0c258610010381c216030260944d00b4004842d1403102007161400030107103c4090410701c1407080c200c08030702103c1d400100d0041301e440240411640c0c8034072200303415034061034510f01000c10001607904040c2c900341e0151400f4106511f5031b501ca401c01e80246d10000890b155900550280340c40c03c1d104668031209495940c12000c5105003c42c040c4003600e5a2611805070f450f200041403100da0201c0c1c000f9110344002902c2a0319600d03403400c1c644007681d00460982041418209a544c0c814032460341ca00174402900c0e182e0141225211040000e40c01c14420b08000b0302c018640543da01c0210f40c205d03c0181d9142e050361400d100994001d000940035100c0030b40040ca8000e00c04d0380107544590103140d06 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 885339298 1250 885338048 885338059
    0x6091107051e0f070306050108061602060a1518050a05060307061e0306031b150809060a0f060b040b0909060402090102060f130b0903030a0606020d0e09040f0212030307030e01050f06040b 82
    0x3c124110703009014500203113104140004055040007001441c1072401803c060311554815046890550001451540f0441b41783c0d01103004a03003813003140c5840c032080e444040408200480640c040c801c50300b11038898400080d04001c1da0391181c0401d98bea44140c8142c002054018905d007424a48030907521801103a0740c1404518255642d940c04d0254002c1d1410109541d8451018001441079510031041000309150942840c10081c0855881e04400b520560b0400e980d254007081081389600441c008100104100d511141e079080044840d030300001082d8850440340c0d0005030645014826202050f2041e801000c041e580e1001e90350840700c0280c2000e1b00202101140e00010f074140045038480c00a640182d40c50f0b0503d414028140c5120750010419500300c3d41c0c0c01c12102c0e6004003590301140d811141102c1c0d40d00d881c204904010003401000c0d4000d01803240d4000c00075400001540908080c0d030b01001024514071070a8220360b41550340028069841d0082010380ca8260040050303910000d10 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 885340548 1250 885339298 885339313
    0x50a0c1d0f0a08030403050a05061e010b0306150a02010b0319050d080a0204090c0309060b0d02010203160c080d2028060b041b0207051903062d06091107051e 69
    0x3c11480c42e04154001c40e003651104a01078100002030006035004104181d5240d44030034101d180d1030208405004a046107c1c0100010308596110011584c4001034640503a58075441404001d02a040100c10203000384941e00d855901000032002403009943c000b000b40c01181d0407000c00300c2d2880c90140040d043c65400b484041000c2800784194104240580c4000400d94460b00c0c0c0380059402038101c1c0c0c0d2051806a98990140c1d0f004400c94501242d80010800402d00501e8403004c01c1c01107400000081c851140081980e0780c111030800090340e0190480480c400b050b41283c2d940b8606040e081c440c3c01d141020401d001c1000884d41070180d440303500d01190642c1e522010508582200081ea500544854103001c0c0d0283c040c00008003400b41644d018a0b141a05841814482e28510005107015501c0803c0d0707032954050100051500c0700101c142c0e600501c400b1040c4098903890065005081c5841340054001c0d5601d01101c00c005d0703000015004030118110b13850044c210454201a49001c2c1c0c52 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 885341798 1250 885340548 885340559
    0x60f0e010305060c03040512031e13032a0b0c040305010e0d05040612090203010c0c170a020c06030703060e0a020304060b060703270b0c0f0d180314070513050a0c1d0f0a 74
    0x4061441401411248ac50061001400036100d01e0041c01d802001000c2e900600c02090740180310f2550550081c0502c01c0c1044103064240030428882d001034040b45d0b140042c00601c00241000303004070b80c00354000f80101101c050403540c03109a04000000800c070200700800505020381111420300c0c40b0248002644050754000c0303429a91380704e02007400501642c0c081c0c0700b0425865050f940c1e42d140c0a041505264404030041e40d40e040100c110782c441c00700440000d01c81403007500000d01400b007100006900d410214140300184d0800d4030125441810524805110f007008002d03122029003640d5980c4ca0b00e000b1581d071021094004d034201c480c0b0081188046881d881010007481000e050100412400e210240c0c0340341481c0215280300200003800030ba03100c82c1d201e0001444242c980041c080c032140c000c0c0b10300441c07030541d16a000c40c1d080b19030250510300000e07041e4080d0740b0400b4503c005100d400100d0201300c89800c240406c0000c00c40141040d180f05061008154000f8040a042c0503c090340342d4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 885343048 1250 885341798 885341833
    0x150c030915020c01020d02062e080a080307110111220e011401020c0a0f0e09250312020f0d0518030312041a0907050103020304030201140a060f0e010305060c030405 72
    0x108100307030140e4001040c1020a5904208149000e0118070140070181010221401207030341b810760701c131050070b4104128a2160a90446403000344106070840e42c001d0250f01d0110303c03e400440748080441c0b21701e044040030300c506014524095000c41300103860910b280c0b19581c030701900940c010400018a010100c1c12030b103841040e501a0480440b00028004c03038600081c6040601c80e45140501c0d070f01c0780e00f00024007498041c54152070b1511710540080d51140b0fa0145400000809000a10408480c4002508201c0010b400b601d025407000052082c811100740c0e920415154030304ca40380d015244c1c008101d88244041c204a4041040b1058a4580c05000a1540e04002070a42d5000a40001e01c000c00c0584502190700300700d52138002c1050714010503000c0c4c540d405071161a040c140c000000404140c1b00b94440003004043c01c000056908014003035800814513405140250440c0800102e5001d03100103a06040f80d6021000384030300c3d59148020981d03a0000b40088841c2d209150300c3c29001250b1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 885344298 1250 885343048 885343079
    0x1209030507120e280b1b060a060302090f0912031003050a0b27030403020f0609060d050108010e0a021e12060a1b0509010e0409030e06040b0304150204150c0309 70
    0x21a901c2403649207078442003100c00b003c3c03d1035020706007006136030910018120200c1c80341114909600b81d51240303150b00140e0002000c03064142c610380101d01c00c018007800035512050942e80280e80140d0302c0e41e9000c0c520310301d4400560780d41c03c00354070210055a842080704010f43c0d100c2c0e2400c41c810481d0ba980e80e5440d1a182d007980044452074505030030044698003050308550790601c10300d800800c20038104d40f41510b80c442e45c04042d01814003071000e03640503140c0c4021284030040103411203035101c05001c8110001d280a0045030895400c040e00c60359010b40c0026041e500a0b00107059110300528031441d8248030031400803480e040131800c1d54070641102c080c801c0b0f03842402145404580301000e9054003610070744034180501800707000d1103a0600c99a01c000290516401640c001808581ca030400303a941e4200c2c01e80943e8007410009000c101d10141001035405584a04480c80c500003403400e4100507070040d406600718000d030781c0e2121f07102603214007030301002d1501a0030810000c075141c13100c2100d2041d1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 885345548 1250 885344298 885344333
    0x6081e091c170a0902010917011805100b03070b16060f0905060403112407020a0203011d0717060c18131a0901080304090902030304170d0914011209030507 68
    0x4401d80c072010b21040d640d40d090b4000715540c1c0c02c100d6481c0950010300100740900407182c10f9005040403d01c01042540306010b00f03990661141d008495600c0c00907650034980110340074841c103101c003410f0300f8140021070b14280c0d022241d01701e080c07810320300e06444c01103010481611130b25200c0b10300d884d20012510494111500035006040c84c2d01d01810040c104200000a50807650b204000701000b907a591041d00c240111080c180b01c045d80c84e40c00c4100d1820700d0060380070b5459441c0ca282103802c00003051107002054045016205503540e1102030b403081030701c4a080018aa0014000a9409800a0010711600301d8190040305030b010080049651401d4180c0300c80d2441b6954001a10f0313508282420b005c0680c0125003508039503060411141d103038000c621036034001d60785500c0b1000440d94280152005040445250954440780079074503642c44658504107004288003840c0400c03501e141c212004031072901038542020f206d16954130b41004200034181641004414001d01c0d0010700b41c1501c402c2041c8 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 885346798 1250 885345548 885345557
    0x2160803070c020a1514030925090b09130f2d031403040f17070206030a0c030e07150f0323090f070e0610090f080303090706081e091c 59
    0x9100c2e03c1030020281e4190850341e42c822002074040c0c13482d80d10428008003620780407140e54403a141e450100b4a48054019501034a0000d8204100d5008280410740700303d50803118140031075004501448841c400035070301c180352245642032140c0810300d4050121501d501c98100e01c02d0848040c403201003940c54503008407000b22920a500014940e0000029185000c120180d914500302561081070389004458000d1040c1040c0a00c15041e1050741c080d00d0342030703802504841e03481c680694401c0080c1f889078030a4011918051210416400005007001505d10380c0c0410f081005ca01c0703506030345000d4041941010103485407584440c0907034840c4100013940440d00e03a5591030800c503a41d141441002c0443e0480c0ba07201190401803411020b078060742241e8240d40c04089c84c03088100c22550100c6079040140714028449000403480f00000c0114071a1103250152001c482c0c44a008a6040d0800e48090014846507181602801d249043c1c040c0c1190715042140c55464a22001c0d0740700c000440c103000040f4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 885348048 1250 885346798 885346817
    0x3030a0c170301230111030c03131a07150b040c0c0303052a0d0b1f080a14160e03071203110c01090e07023c0607120216080307 56
    0x225207040300194100000041d10700359810f1159802425030300a40e0034052918207032035580564003511803810a65248020b40c3d580340020701d5419a29848000d01d5408800c0e0700000240840400e4450785103190a204041c0c54503586480d0102407000c0c10848000c90303980c8408101d001e507141d202c0e43d0baa618040c0c41e00c086628150401a04035035000700398200444408a4201d02c4045008609061100220f4490303107030303101003004400420103d2180da420007950403003040142400c02c2020b1300320f4070b039940354001c50b5920104501a41d05d14a00c0720064031514004c14181e0a100311001a40d403130a243c905060b01e2002c001074074103140ca61101d9801788134003560b00107251f40802c0085182141c4401040480d11000c0002c0c0f26800d6489903a580c404d9003000308601c00d00c284003028203515015500200c0028440c404011000c80d0103030a4045204800c4224441d00049240743c4180383d01e03101c400300100305170b21000180d48464a40e207514520340c248000001c0110b40514080d02d590350305e40401 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 885349298 1250 885348048 885348053
    0x110d0903060516230714070e130803040221120d0e01021c090201110318100e090c161a0103050c0a14060d090f0515010623130503030a0c 60
    0x444001030030040d14040030032001009241c000c4c50301c40c13040d0b413405028140c130403050342000d10034010020002c0c8807848010303811504d00c100040200548804189024090b2a506400c001410750b17541d0003884800b0a10004015240c5000d5000a80d141d00501306142c140240c203c500348045120403e50280011509600c099221320500300e1000c440e40086140c0f9110300c5802c00454102103000316890781f140080011640300d2804400d442c150714040300d403504281070001840e450042c10050007070070a401c0740c9401c1c81c41140c1100c03a085014092000c140c41c2c1c405900d4950b4041b072034070003c4c0702c03142942c40c0005e106d48280d80c90040da00e4009065039415890a58100f0040c603c641c1c2c803505483d04144040d5900700290003103c1c0c82240c2055484500703080800c040d01d540c0c0800b0b003041c1041c60030103042c0840494075010840e03100c468000340daa00e480058034420050300801113114000c500014408a00b44010000d40c5071003007240110707664601c002490b50307010503031003400600740000032801c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 885350548 1250 885349298 885349301
    0x15251214071718031e0c03030a0909050606070203070609060806061204030f050f070c210c060e0a030b010803090f0a0605090f0a03060c020a0506010603020412030521130b010f24110d090306 83
    0x6c140040340903501e05a0f42c1200204a001580242c02e40165940d004c070340c1c0c9a58035000c81c0c202c141d000c0c0641f801d0903640e000240c07600390036114500c08290604002855880d001b0100c5030080d91408455190352242c0d00d0454a200007100610103004080058007031f02403031080505400c912407950400072504111407049218240503c0d15403c0200030900d00004000304c0c0c8600035a0300e41d02d09103000c1607081c000174201c002568405409d00c0c0d120800482d00400110050030034010680da0405420380800511a03000141d1051500244081c0150740c81171401c4100135440350300040244000315100d44420b02100c044110000140e80311030511420080240540c500401450600f1402c252424000710488615200000c00b0820b0009965410f03401c410140fa0b0312801d0300e48481076900d841c0903600000e900844003652103030406000081d0030040c4000400070f556908000c0b200300780d81c0d01814001502003914460902c06000c980601d2000100114451f42c0401c0c0c1e2001000c0303156040440 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 885351798 1250 885350548 885350563
    0xc04060e0702060610140f0406110a02090a150306020a02010501060810051f180b0d0f0209181e090c010305060306040215251214071718031e 62
    0x80e18014040041d2607801007841a4420000c0d94501c8580050ba0b008854612940d482c4205106021420b040c01c4101c24001d40140c032034039100c0007400004130132126650301c80d620307000b035004401c10002110440c80d900801d104111080ca03041230503490f81d6840c0260b0f08440241c0740143e6644004100d03199024400715001b4a007800b0307092542c3d04010228a45002c40000706036004941035078000e0f100d2040c0001440c8201c0345001e0118582c0303460320098950702100b86844600c0c00c3c520000d050041501c00c4420000c00282401c0e5041c40ea1f200c402c0304448010640c0d00c907101d03002c05e102100042002d40d5413095000e1000750506050000001d002c841300642040e009074840810403005844410803159800041080a512000410301e400744511038000c4000320f402074030062604100c09507000340051459501c81205450700101c0001d80742c0184170b0094014105200800b540351103500083c00620245207501c209245004082450600440c111544000034007540c074084070010310051 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 885353048 1250 885351798 885351809
    0x60212010e09060109052203021c05040602060612010e0f01050106090f06020c0d260903101424062206030c0e09090f0d0c112707200c0406 61
    0x25040b820b0207040140e0350070050050058055840000c914180750b02e800c40044020121340e1541e0000b9940303002526161050b564903962194503841010f064014000d95013035810507070050030035513105000c004041070107018031885550703651082da00514080c0440d07048200c0e824000f10340d5514002e00104191403076409000002042c0d9400d010455000c2000445128109e6503011078851500b031124a4010f104280640c102500e6000c034402c000c8031003d0010800200c0643c0c00342c4203941d6221042e18916540043c154580d80005a003501c0e00f62104901c02c01d052580324400c41d52580890be5a61200c881c0b0ae440004000d650034504040d1800711026000c145002e200410760b540d4041c043d050944145441040c0c07000c0029001001000b105a80300304c404215016180204405000181207030f400f0b859007130040d6104060340c10081c00048590007100e4100e610320544241e541c80c1004040c200720308020f01c900c0c16102e01304010440340a107221040103002d612140d6002c00003112410741c0318 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 885354298 1250 885353048 885353069
    0xf03100602031903020d0e100b04050c0403050c09041a3108030606070519081b0601080601060f02190305040503101a0f06070f0506070e0d0c03080912070306021201 72
    0x1883c03040c18000119a10030380c1c0341d040c0580c0b104041403609014260407a203880c1d43e40b150303c1d064402e41c03410340c0041011071307001c0d2020031058903140031509881c4554000070303110740c0c04007080d07401c14240240340070792041c010f120b041340c03070400c000c0a8000d0b101c00ba00c0082c40d030715080040e4551030051440302103010005a100c804105a1030341c50f14114003004105600c41c4002003019828490203111005c4906100620041480700d540307405052500007c0c0c80a40c071820b4500b0100c1d4100c800034070141a00d8034800101001d82c0b9065046500e000d20903043c10450041c3c040c0c2d408010749907000603c41d1407080c1c0712142c85500b0003090504c2d15545200e0701c411181402e41e140110001c1802605807190144c8150010340501d01c0405c5c03d610551000a1121001a204805200f004a4294050307a41990348105d0301c0001d4007001845020311101a02c0d0000c801310801c0054004002000070880180c45040c101648188660501080754400d075083c40e000588030965010b496080c0d809420340074030 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 885355548 1250 885354298 885354307
    0x18040302061b121006110f03070f0804030b1006080702120d0b03070503061914040209060409020102280506090303090d11011e0e0111090d260f0310060203 68
    0x14020754a91000d0074501035070b014084071042d00d400b03040c1121544090104408001d081c49034071102800d01e1480b4030400200e2141c0450a091408540344d0541c040000056042250a480300102001a079404961484080000100141d601076001c0d2150034505004003003c0d18040001d000305500504280440d0070904241886220b40e8054819068142400042c4194208046490101107400450341031003500308015240c01448200d00d804038007842c05204041000c02c040c442c0360401d4400940c4103e01800241042c241350b030203d110107005104a8807005909002a04500c402c100e51412100e2040c0d140701c103110701044807517041183c0f50002c502e50324007898203a455007682e010031030400407144424a02001d094020300300c16204203050b40c0b608859402100300620896100707400c1c039401c0980d0030051940c0d81080e10744038100684138900c1c80400b0707038481101344d14040001e00b00301c2c001043c402440342103901038240e04d0444c5000e6940c3c2d09001d0ad04e480503007181d0b480413085600400 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 885356798 1250 885355548 885355553
    0x30f02040f2301021614031002030c030103200109092301080f06130506041709030d120c032a0c0506072c13051315020a030f14011a0f0406020a021804 66
    0x110070100d5070346d104507825200ca542c0010382015400e8503420b2025002006014000c0c1c1c00d04000c504880c4940c224030b1484041d00550110f82a61000d0540880ca200c3e20402000001d600300c08400e4400306900f1080c5a800c4203401c140c0c61013a0444409580003617407a142c0c45008010b480c5c2c10412008042c480d464659980c1c66694500400040547e03c5680100080e4010b05095075030145000381680c2c2d40600078000103000600f601c664044040c20a65503000081c001d203c1e200c240c1d256900016036103c04181c4d03400c2c042c078000010808204d4a003403c240858030911020f40514650303680c588400f401c210712000345085500e22104c2a1000c000c05c841a44c0e207140410506603210000400e0b0780d501c0794920b900e40c80c849480502004038007003503003190003010341c000d21050410345c074100588d030f008030342c1c08003141c8101201000103502d15005100c000c4840c41c1002405c0710800046141007050703100c00c105500030360301082c09a40b02c9140a02149040300b071140d40440b0340e01c4802114603054 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 885358048 1250 885356798 885356833
    0xc150c0e0f0a0909020604081203060916020a170409060b09090603030a0e0d02010c0b091011090a030b060402070c0305010b130c020316030e0307033f030f02040f230102 74
    0x107200314043e082e510302c9150215144c138002c0c3c90041c48500203a03682503000110304012a4011141d8610a110400008407800c0d002180406c40144560040428441b9940c41800001081410f0340b01d080c0e0034440012214028003c281c00b80c001d8088848e01c0d5030456043c07009071440506082c0c86500188642d41045e54080080400c19404803144a580c0090b800140d90141d02803101400358141c100420000c90f40000d03180c03104400b91102048140300051503400c25005108a8580c0004000002c001081c1940c482030f400c000e00810043c980071556480c1258501940d0048a0594413000c884180d40380100050000e420300000902800043c240d00030349034820f01c3c2d080035100b512204140223151044030780d07100d04170004d8110f602183e101d05001e002d550040d140601c0c00f003501650300801c0782000c02107100084000b105a09800e040700d805030042c01c9105040c01035150309002c005010300003110703c0b000500e8100c2d00392031070150340082503080400035043c042c19948907a188010030702c1d40c1d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 885359298 1250 885358048 885358069
    0x11a0415060f120f02030103112e110f011b0e010203030f0103060c12022a07050a18090f0303061503060503031e07020a2c011d070c150c0e0f 62
    0x40303103000703903844184400f018020022a1880c1c1c0f0782a101000200c100030304400141d018081c1210b07049089000c82c40071090742c02c0401071b19803641c0f016404004100c1d005241445074010a002a01c500222000c0751608440a00401c103145c184500b03080614117402403810500c400c02032025500e9403502d014100d20422062000401e015960b00e040303d84907125030314003002d505615505551b641e40c0c102c0945c5141c0c2100c1c0401425074150306403000c0b01c00001403024119035020305126405031405400601008884196208458071041c43c440060b01000c10740c030006200340c40c0060740a00302802030080d0300c4080700d1320061610700201031005135400410380e505441452000ca030716103510303000e40c207050103074041c0250403000005020828030038080000000084007080c13200c5420304c6070100b0000c07910a2080c903410018500c8018104800c02c03814075400346a90404c041001c01a82e501c50460201120f142480da0f514440444042e50000e1079040300e810441e100050704a000d4001b0307455440 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 885360548 1250 885359298 885359327
    0x50405061b2b03022704090f03091406090f0f01180b03180a0f120e09010b070b0f0c030f04170c10060b0405090c28120f0c0813060608011a041506 64
    0x30005e400d0003039480d90000310070954000c05042c05005103280c05059005103005000078a146204500d000d400c1200070b03210074200050160540c060b2001c2800381c406001c0c4400d5041042004c00d80080d212003a07005030044c20300c41880c507524901044070b8414160460f240c12641d4000b4041000880d42d600590b90300d46070440e00040c1c25901a00060300d03040c03a880f180750380181c0020f000150150003c0b000d8510a030040f490006540c1d11007590240c0c00c6c40c11284250304000c14008201c0d840301090071240d02520455000103c140031060841e95604605c00c602542d0b801445403004100d641d0181a0007050075041c1e0504090030140060004503000f840e18a20010115403444980d80700c2c0130018010201da00340303540b03c2214482c001e1028218076451040b081c24802c042100007014442c0002802d61541c0d828000e1700c2e180c03010340807904180c42c00c3d20300326143c10012031100c6080c414051a0260080342008180c0c0020610065981c10310030ba42c00303841340110030403260782c02c601100c00c00700 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 885361798 1250 885360548 885360607
    0x1c0605090c0d050a111507140a0f0602130f051012180515150a05010509033f04210501020c1005010512060106050405061b2b0302 57
    0x16581040ea6180036aa180350991041e1803120741803d010011a04031a068021400b210721165110288605451010b0b13003800b0404007041100041088004040c0420020b0826102d032540c07203880b10710b99415504c0c02902d6441d4006182c0b84008030b910f4940b0b008012100d81f00b42d8140c540400241c90749002e01c0b030b0b00107129800401900d40000c5074017524228941c4480b4189042c41030030201d69940341200010910140c0801040a081040c482e40c620488002c083c210464148001103032a504101c42498052207040410780c4001c800700002441c040208848101d105560102400e84007262f003a0f1281070780c000c00c03003440000040d0413514140d0001014450040200d0716043d4024810f00c07501c00440d02950103055418030b8281c019504a40d811501032208042c3d020255484207401e101e101d010807003c102c00c03c61401c201001d44644030041c0da801441e649685403007404d00e02d8036920a0030341c160a603015100c0c20102c41c0703070802c0c14080c2d203002c50400314080b001e1943c0b09071101d400107030074 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 885363048 1250 885361798 885361801
    0x301090b06041a1513050907050a0f030908270a14150309060711030417030a080a02192006010b030f0c03010e01050d080f160303060617010311060c060115030b1c0605 73
    0x25420501781ca0061501402e600041d1902e1780c402803ea4211312400c0300002d90201040c91f01030710900031403100d950000c080c10314041d00400041960401c40702c8103d002c1405408622241d82c6010b81d4000030801c8441c40c1d1140b01e1042c2c20401400d10900a10304060301c10700510883c80130005101d0380c00601c0e801c01c021507105d44168035195004513840384030f2401078403415028460022029111025540e00ca52a907038488841d400c00780e004042c0361451101181340380300746c482d03c510348dd0b1000510640050504a219404041c181402608101c80480c9c0000510120b181242003940d4000a540212800c550411030f00401c4110184030b814892203174025020148003203441100d0501102000c00303a0740d11507480b1a03004a040c50b44003a404607240003030014006001d4a070345080d00a0302c8060600580c00d5580e08405210b080240680081c024804804c0940301000420b01900345180c02c240d80c001c2065006040e600b564003018010311041c54410800010802c680b091554001d1020659 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 885364298 1250 885363048 885363067
    0x2030f090603040c05120c03060c0405090406050a0b0d030309170712230406180f0f05130e01060305030315040b060a12090221060c1e0a09050301090b06041a15 70
    0x1c5240c0c3c5e00312a5220382060031340c483d00303400091039116180301a01134800d16507072181c206001d4065441019005508040020005005640441d9000624240c0016012110004903070030b100b805c407044002c281d07181c0c907402c144000d92545181d0944003124030741c81d1400c1d5075200e941041c1428081814000540500440e140081540300074075044942803540703543c0c3d00e41c4024000b038402c811103000149025400300b1032209a5004009560302400c5001c5038920300414000490f004444215000f591500c80c0f14080400303000d21002140144015901c0e13040c0a4500d04550308140316131032040c4d1070310558203000c0e25114191001c6603910304210b0350350a90b0501d00c1000d41a03480000798000e2141d02c035940060b800d610619841015807048550076555480c00c20660301c50307801d040070b00842003a5130b005604e10b1b0700010400d501c1b080c17034081d5070643d45501181c251011075a048422924480c01c10a290810707225192424003219088861052a4408108400d00c0074003a00c05d090310001c1e10415 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 885365548 1250 885364298 885364313
    0x3210e03030f121317072001021e0a0507030b010806150117040822090c020c03070b0a051908061503070c030e2202220f06030c090909030e030c0102030f09060304 71
    0x2200b904101e0300f40c1d171072010620242080d802582c088a50703c2860080e1881c02407c60070303940c000e55043e00109040e86d1079030880912140401311030b07103a41c800e00d10210005a41840400c00461040c11003445550400c8640c0303050104c0109690221240602110b007113030381c03200c0c400003a07111151002c030103510f5906001009119008244414411500b942c4002c51042c0140008442007100c08200d509942c0750304a89502c0549269035055100070805d1060207100e038010450340c01c643c10058604000e40c041000140702c40d1080602003160300301041920705181140101c05440c140c016840c40c0341a6601400e014201440501041180300c281800f070340321501d600900c01080f1150b001e000d2140540310340a5802a4103544c3e5281e504429140403103420f0254400340c0315620b106545450405004400410100e4900c6040014103840021a1001c030301c50b410b820741c029a12241601d244c40145440c181429a000381158001c01c4241560f85001c0c041d0ba101702c00032121141d80351100d050011 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 885366798 1250 885365548 885365581
    0x71b03081b07050f07051c0602032206090201020d1e140c070311040605060301030506072f0c19050a211e050601050f10030c0903210e03030f12 63
    0x25070054001410400f4440b00080100340ca50500381141d0b401a128014810501544043e0301002c60b1845003000000e00c15401440c0e1081240071b000c0c3c542203150300e500c1d04808040f18103a8140f0f0f560300400f015035905100081e4406440c0c02d240040c0002541138200020001807080200610382d0540302000216100f103404a140c2c50048402c0300391030342404514020340d203054510680c03409000040c1c07803c1000959040b41d4110020380784031340d1010401c0d645418540e550f0300d82c040207020b44a40e0420343c4600c605580c03002500510850810300d00780700080b0f0030007560102da0002680d0800503641da9801c02400d0b500000c8181c00f001d258666410001846020024000f2000c811900c0c506040c4005c0600310394011800c445050740d0310420304c90b28042400c1055000a80c180c259040c131402500800700104041c608840103c1c0d603516052600d004070b4440400034000c100049102c00c0c1d002d10900c442c03400c00c41c00b95141011030909150188252003026044040e0030780014210b214410120 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 885368048 1250 885366798 885366841
    0xd0207240212013c061101090302250302180f06040902090705130b0d0507090b0705031812010c21060510030519060902071e030e04020d0f0f0b09071b0308 68
    0x903196103001110f9900720320014040d100006a03100314072141c840c01400340462060f01a006850104601401c00d2f20704404102f504031040c0c0036200c0080141c9407202d08400c1d0f9080140107100da4142020b24016819024101610690814900c00c0150780c81010301d41d0030a95604100766038200c0c910070403c07440040c0c1d0051030301410200d0030b00700300241c40d081644102400e64030010000d071909141b4105018800016145034000d010511500140b008501c12401c070003000200b00b941c0807180c40f403d58059450b00c00c00103c11600440426400015002101c10898010b006507401e102c0803550401e10030f0041d000f01a1224040740d50110340e0070480b00f40d20752605045c8082c54070360150501940c000c0710221803060f1800b0308941c6e0400000d84820b1069410f503074041584a42c50108030194104002020041c0d0f95080407502d540540d00c110707040342c2d14121010034000d41010401c0f510710001000101844141520300500030515100510000e6041c201030b081521562012101001517420344c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 885369298 1250 885368048 885368129
    0x70507270504050c013b0f0a031101030209010c1407030c0b040506030a020708070b04030807140a0e210a0b01142b051e0609010e030a0c0206030a020d020724021201 72
    0xe4080c007000702070346d205840c50143e070f01c1c04500f01c04e6000c0c0002c41c0c0051201a10100400300b20204c2c0d90b100780c0041c207040c081450300000300c01c425100c180e2020300c42c130071403107003070b80040c2c010420042503135150402406207000c140d003054607160128015100c004c00303d0445036800035052040100b542c0039104290780092034250036141030310300504405820b40b082804540d0020441114101030b10480e10001802d0703951440039400da400340b0070601410100303400040c0b407003141013015134410020051043e00070b404040c0c06516000210028801e9404028010102203c04003102001416150040701e0a4440a22544424105281408107000c80c426220810741d8024080c8003000a21502901c8218020450412803001041da81d2040d000c003500403480d20820040545001400f130347d8040351444016280c075034442071030401c81c1c0c0701c140708461040251603541045603c0e042d5285021840f5102103251065254046a20180c14812064031000b8001203a079032270322540f03000c848030045290 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 885370548 1250 885369298 885369377
    0x7080d060e040507080f0304060e0108040203120c0d090909020d0b0c04120803180f0709020a050d0c090f080109021c0317040818090c041a070507270504050c01 70
    0x80c0f06840b03081ca80304e401240e108641e50443e80d080003104031006c481d415140d00701600001001941c00010080c410ba0341030182a5044021080700c20007400e8803112800a41055648881c0182840d4516081040000c0c030340001000142c591100003421b040e000413011080b65600120407010703100350741002d4000e2038801c2d04c0a0800041e00041c0d80601c2d14041021030705000c80390500d40e90340381d0303051040503540b0443d001c001c0c1d9070050740209800d64040c81c0052401c0308000102c81540c010300e0444000800c003082c200100320000e07001102030100e040c003d01010503180c00083d400da481310310860071070fa01c001201080600400190300c03c40c0c0c907441680158039003400c0c200050b030481083d070809040c0e40140141c1d54904914900d21480354441100e007011704059102e42125081c1082c641e0200301081050040381041003002e004007102d005456a03c880050b44404441000612a24140c01c0006000c00280e02040300042c0c59003c0c80c1580c10034403003a03103e0010440050501c0c190404005 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 885371798 1250 885370548 885370553
    0x1605070803030f0a150510030609090f02090c0c070b0a09030b15040c02010204080a0b060301090f0f11060a0e0f01020712060b0a063923160b07080d060e04 68
    0x406940f0440e070b541a05002542c401131040141e4070f61007400c0d000c1011001c1c0500c41d601e4203864a002d0000203140004900362124210300442d040e0f5a4140d408440b569201e03000c5240c15001c19511200c1402c2071400c244540002d6a601c80b514011006e42040209004006520641a600c015900001d81910303d0030210500c00050325401c22440c0900e041c2040c074034405005000707e42c12500e0030300c0103060074102501d801c6040800a008180c2c15520f82c1c03560400f151002e134a207092240240800003946445242607002c18000c00c0005000e000c044c86030b640410b0b009400900e200b1800c1d282100a08001c4004034244074031500a81d1603840950b10610500500c0d5203d140c803010161034513002c40751500d03010b0355003000c0440c0c110681c0a0282940c07a1414601c284800d901074001e0030905c0181d2540e485c03400d542e9120035020102101070b20521425402000351a2080240000c0001482d003449442c881d640710393300300075018240016007201440c81030b41c4100001c241d540721100d003030305084c03 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 885373048 1250 885371798 885371803
    0x12110613090f1113090902032407090e010f09092303090906060f07080703051912051303052713050f150a121a010303110d0809100216050708 62
    0xd00000e85254070f00448820707045642d00c04c07540131400814600390101d00d0204000c000d004140740403a014000e024002c8030408810b030f401c42038000108040100303494590401880c3c15030700d50141315401c400200411120104002403410744030900c1000c60000860b003015140f143c00c00e0041f00ea040c030312280c51380070b89102002800300c90b00d04440036015910352208012090240009182c071804082141e1000980343c54024680140300e420020b04040c078032201c0124203044100c44601042c201b191450140d01c1da4401d003980201203140a02e02c21075a500d005085014000c40918070032840b85c05084c241c50b03a95011140c000005120000d01d0203000c400c0400781400f550300240107188440030804d0300c10001c0303184070352800c081d220104161600c08110b0318058001815140e403801d046d1060351160050b20b0303d6010718001e80321954007030142040b040c64540350f0885081002421800d10034030004c042810308a0348017481000d40c07521402e0b8044c2106201c01800200284030f40c000004020601 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 885374298 1250 885373048 885373061
    0xb0a0522030e10110c01181509170109120e030708030c01020c0706020601061d0f120d02070602010c0801050d050c09010314061b09090a1104030f1403041211061309 72
    0x207507074014240001c030106503012180c4c100710100e29080410189401e5108000380302040c0403009007204100d80e02c0302c180028400d02a150070010f6031485007401101412143d84802c140000c008100039401607c810f29203400d060001802c011150744040c0465a080012201600305030301626680c0d00e54482c0d09000794412241c5200c1402010701c00205079001007074090482c0c00369101c880d030752440165041c0360702c4400c0e01c001e0741c04451982c112604c4d49940e944100301541c2d62009020b85440010040e14003031300381e070003002103a050501490348954040043c6044800942d000104a0300700d2070184c1c00c03c190703540d8840e001726102c40000706001c2c201c2c11706040580780400f51110350b101e0030007000c001ca1b08011280e0507640200b0140c0810b09280c01407541c403440c0500e0000349054100e22400c0700754855070081d00da2440f1401c0440a00501c0112140450f6009004510301442d0516218205010000c080c1412507001d0b0a1402915000200c5218510515007072102c140c44060002c0107000 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 885375548 1250 885374298 885374327
    0x6170109020916230d050c0a111209040207050322090606020a0c06050c0a060c020c04140f18030d090605040b061005030606160f0503120a090b0a052203 67
    0x70031000c90b60800c203071100819224102d41d41c00d404000e030020340488920404050044d007401c1001414018480c0c2c1c4103c50154402c81242c55031103561000c010301034140d9051034112900002181c4900d41450001ca401c00750050f6800760712034860303003800d0342540946840448201c1d162803080c000300580c0a600800d1700c0c1c00341c00c20410642c03140c1d022030f51612100b078001c4c10800902d50503c403603800340000c3e280c1040c2d0b180c11034050400c0c5076030791000d4039410920781c0056131081614003054079280c0150101d1000326200010a860030460601e202000075101c54a803180c11090200340102c1442120401c3c0c50b001c906211200301450290014442201c00340e81e94083d42c0c01042d01442c140e11200d00c1c038242c1d6074500381140c440d141003001c1c59000341c03801c01111011400b400c00003103400c1d40300c40f0441d025201440d141d041c0c40d255486110001040640c400d480c0400f0180000e902800c000d421244000340003030160b481c000820203d0360f060720305031185420f41c420302040582c0030b60500c20101c0d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 885376798 1250 885375548 885375559
    0x303110d06030c06140702040e011b052a0c2b1a0108190605060105072a0f0e070807050702030a0f170c12090a0b0301090905071403030a030f0617010902 67
    0x44e075444046500c0d81c900c201c0c000041d04104050405031030107800c0340c900303a684803000090b10f00c0325040c440550605d80325420081000403800c4c69003210b0506c414400e2145506211400034001d03004a0380303410300780d0481403103640d50004101d0001c060718509010881c210031140491612414940c2c2494003803040410001042c600204032075502103602d100040c0150002c00d000609561810301501c001400507041240500103e00401e41c5c0c102a150f42460b00e205200c2d11005048841d00c4140c500c1c1c218240564504008204079100e290007075500c01507918040240c0e407074001c411a03443c80780c540c1c080e626200c0d401810003031000c01c800d1120391070b03c1408120300101c07403010b00e4505801143c211145940008241c1d68002500c58010312246130b004080f558000e480d00000b1455800c00c0c2c000283c41a0b076582d00108103c010008507000e8481c0e072215804c604154800603a5909c04c041091040603240c0f103109806050940044010b000d2220710301d494180d40e0302c8024000c00321803506a1062 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 885378048 1250 885376798 885376823
    0x2160308040302101407020f010e0319050d0906120b010e040903080f220f05010b0a03051b010c080f0a0e0405160e1005030f090712030f080f060102190303110d0603 72
    0x1134065901108024170f01c00003c2c0c01c00003a5000c020742d150003004917a05100403003c15680f43d650510660341c2e4075080302d2400704402c0d05c60401c1440c11130448145000d01400d00700600400760406230341002824444000309a0b000130340300482e145080c059801e50080c5c1007071107800406400403100c074480c1c58803045007142d69444503c15040d18aa4100b04143c401c1c0241c40140841d1040e241075110601500c0049008524000818440401036005403040c0d0401e802c0c0130032000d40f0411143c2d07884000d1070448605203450712000c01c58402e01006080b031000c00503503550b8160240d0402c4495400042c010855440d10b880c00380c8034050f0b02c141e40b80c0001c002c124010001c2c80d006031180e107581101d0b17894609550381c0b40c1c0304042101014200722024407414a000a620b00c90000c81c0f10314a00c25519600600814000a42780300e0024007044100b044010401005036400174a040c0740c500140c6440f1107024083c24183c008245190002c0500e1000085003041d0180c55084401101c0c42504a02c0f80d2 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 885379298 1250 885378048 885378079
    0x20f070209280e06091b0f01180f050a15020d0f0c050109030206070201060506070b061903050106030303090b0c07030c020f181311031218151206040501081501031202160308040302 79
    0xd5002100c0302c064901c107006220407a50801c1e004250540c40c7c103060629400e240c102c0c80c986501c0300380d4070041c00014419001d02550a002d01c03040010040124680d40072580e88401a480f001e050707400d2401c0280b4920f80544041c45142c0300600141c02c60002c004420741c608009442d078100722160400b541c00e203800066142001400c1301c200a0300030418494540b075200812202e07462585801034040e030f58460100c0401d1081c0300c2e40300114402e03180041c12110702d03d064000e00400400c00c00000b80b060000320040b94221014580301a8112004c0146c403088100080e0190081880d408250101d94100400710741c11039100507015002c3d002d0441010000000c05641307150b43c3c40007400480051150108156500d000040c03203040041c54000d200d8030200c0c8002c107942181e4203601d802c2c060341043c03000908241c4911409040c1000c081e000480a880725003000755010320008022130322095000c20040c0c42440480204048100c100310619901c0c10070100a03005400207a200e800c407407010181 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 885380548 1250 885379298 885379303
    0x201020c010f08192913050f060d0512220512150a110f03190b06070308060d061805010f02090a03030c03020705060d1a04020f070209280e0609 63
    0x110040726a40c0c80000d555000c11166101c9004400b01e100c2a450b990017461a80e0340503a41200d4844107a01400160260010003044004421101d00d542d0328280501a01c90501844a940010162070000d40d00201c0e14115103002c004e0f10012021003800320b9100500c940a15446040710149904039410b65152000c202c000c201910049000d0f6000600da00d081080c4003901c0c59210302c2d1418005048580d542c100314065011961070340c0344041c00001c020329140c480c841e40700a9544414100951444072021800500c40c001c030140078001071000060700c0303a41c0c02d005110040d0f4005000d210f0320851140c0c8801d1560070030703000c444d41c1d4246a50140300d10254804c0e20300e4071100610481c0241d02d182c42c00d075034040d407804040d41117001c1d041011449880b1036008021a030b0f10500d0000c0c0c05910400c40000b14180d01050912980c0104480d0b00c5050000781a10005c1d80c04031038003a129114a800007403d110341c401c0000007003032011102c05000c0c5c1d031688100806000c0c2015208140d481c03005064 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 885381798 1250 885380548 885380567
    0x305010506030c011e090308071212060f05010c020a03060e01020913050402030a0b090a051c1107080a0209190e0102121e0a0c0e04050a02041505030c160614090a0201020c01 76
    0x4d0000e43e4901d06403a0310307408181c0d00320001441d410803130100c5891b52182c090700d5021040640d03440f20669144055140c0c8074070120752038a02c61008002e064106000c009200c50f41e44211410000c800800b40305641d2031210250007181c1c003020800100c89400f07915030203900002610b600c10b44c1c031080900c100c0841030003024440da60080160240d04216940c9626130f001c041e2210f030340c521031808024001a000c000364030128440c2c82c6601d1340403196902c000c140d0401d0f0051042c2c0c0e6001200104403802c4000751040d4060340c100c646583d103030707142c00c04899906007e06d00100340c3d034188041000082010f5005046c003044140403a46d807980d9940c00c051104090b1102c41101080d408000b40079441e1941c400724510943e89090050070007070f00001000e03070f6400e43d0680c1d0ba00f640001c0402186940c508050211005410700c6411880d2804c0c14a005010f410b90000c45286030300000000c000c0d09621413040740700174041006440c1041074016940d014181030403409071250005940240d80036000c5207 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 885383048 1250 885381798 885381823
    0x1b0109050c12060f04030c230607021b0618030712020901050d050a200d030509030106081204090903020309060708030a0c050f0f1605060c210615030603070f0f030501050603 76
    0xa204030b4442802e0803130580c00c003d0081c1d0810a42e11900e0300054900311641c040540d0781c6040c08081000c80440504260340540032006540c00507640c51400803820045072090042151038585480c0e4170300d218100b90490001d6517515000f03200b0007181c40401a000b990b803481c0280e07a450413680e02e4405206a074401014042c003642c0c0150f404400007402841c1404030f5040700a5040d822007165404145050560b40040700490004581c01500e030600f44181c800500640c40180360441016441890710710035070082018164840c907070b4a05050003001101c030440300260001d591a04581031000068000340c1d41c4050640c03c4c2a40310380003c1c0300741c0a031803610000c5000d81745003295410364520b01380d10610a03054240307103040600004c12001d1295900c981410941c0542d0746a030199005480e02e08820034084210044090007116201d0701c4101054140746440e00f40d40e41c3318100000c5c03505440d07911448031104800408034100c520000400100c0c4d106000030710842e295141056104c0b640700120 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 885384298 1250 885383048 885383053
    0xb070f0e011d060a0e370e04140a05072408040305030109021c061e0905090a15020c0d110d0305250c05010c1e11211b0109050c12 57
    0x7040c607142c801e006118184035424190314801c0e0f03280105100000340119420303500d0b0405503d0b10b480d02002d00c0c884410505003000082541801d00100b4903680285c00541101c001c1a06040300c40010402e2b100744603000000c035142e00c0c1c1d1711203e112620b0040d1030344e640e089102402114181c1c0c05100054011945521050b045a0a04032400000d400c042c02075480c2e1000210035929000c528070450010300034221039a000c4460003244180e51403a964003034000107140170200311208102050205000e584210340909100031070340c0f004040d00840200303160750300500b160116141d401c000701c1c40c800c044000541d600d2070742c884026002c40300d048036590084043e8040c0e4034151a8642401c0710640e1090038200d200000d152900382c21541c4050041021648440c15440b01d12101e92000c41c03107081030320301b55011800101105464034285003010708103a00f02c020003020058400151544481c0d007902d5000000804501a40070b44542541941c2900501c110b40106013890598009005410f000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 885385548 1250 885384298 885384347
    0x280b010306230f0714041d040b090d02100f0f0e07080f0c01050403120c0510050a0b0901080a140c1203031033091802120105040e0c09040f0b070f0e01 66
    0xd071203440e030201141880f05c07020400132030441105c1e9550309420061021512081c9040e2601003049040600750b0402d070381c17000ca200c0e0141540090320082d0000100000304860b0005071000014101c01c04e000120f550604908500b0080c0010f191f10803a80580129400690404071007501c03108841d07046800190f0801060002c100712520501003280240342010039207102e620341509002c0000d44448215844000348603010140f801480f2942e0005ca4401d1055490101040e5035200c40c000010a2940b1400340904183d03c288440c50401030085c2282c0711000703080c20207984992044640780402d900c0c010004c210800c82907070403101c456110000f13240c810110000c086104003c030002c0820086008004101c81c4998240401c640416050242e107588880050a00701d54050300718500452401d01a111550000660740361003c1003a9120781e02030700c81b03003440c80d100506c5c402d002d400c5492100c107201400d60711038601c914030700203039071051500c80411004451000407100c004200014422 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 885386798 1250 885385548 885385561
    0xf030c170a09060e060f04081c031a01080603010621031805060703080406020c03040b0d0b0d2d05030f09030f0c180a0b1305070e040608280b010306230f 67
    0x40100020344001001203003040c1da101a079185e00d52094100b0b9255800c201607590b402c505228190075270b42c038141405d00c408003040300a804019408030185040100d8000880c00769282940080090106280040717400d03004202c0c00c80d060170746800d040b0005a1000340e030342d00b8a107035102d41c50250390780100302514282306030301d048460000240c0143e405650801c2990110360040008000034250380d02080c0c0c403002c071103a40314201c0f07003050324a5002e0307a140c0e5108000a8405607640004a8090443c506400402e0b010702c000422000c0d001085440009420307510102404050039580100700c0482d014a81c1c0071103083e417242144211260045004100e18201040500e42d10340c0c0800c12580c00aa000b14070350004e1142c5c00740303003000d04120741d44405105044d580440c109040c9034042da810700020b49841201603903080388101c00b400c42070341002e40303410240820344070900746500010005169612801c2c000c0042c61307506500007000c00500031550000708054005403048581c814807d08030342d940e8 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 885388048 1250 885386798 885386807
    0x509131a040c12050f0a0e210f0c03040b120610050702040209010e030a0c0e1807121a0a141501050a030902030709140108060705040b0f090d0f030c170a0906 69
    0x484450b0078083c070100c165400c48082d1069034450314684080003ca81825140e02c4111000b41800c10120381004911a0181d0300024008030b04000700e1002c1d5075111001540e00d003507801020401c088078003000030000783d85d5940c1c101405003400d410712554001d0b2034901c10850b40c14685100040880c01c140006400742c40c082d4040c0000c00704c107042074100305428000090414920a2084807043c900c03200034411170506120715580403c10881803525401c01500072555a540c900c80c0b038000044030103c207810000510340b4515500203c8440844a0401410740009461004c00300c5101c8032280000501c1d550540c00d44d9824900186c40d2030749403034000a011809406000c0050340c141c4543d4100103581c1c0c4042c4100c00e548204440085442c0d41011521030501601038001810020700384820301c150000d110407640c07041c12a00d03020f0b68a010f80c00201d025145c0c524809000d002c1000c84510926402c6140e00f40042d1042000106403c00b40250310320a0003003c80800028038401700038401d65008 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 885389298 1250 885388048 885388061
    0xc090504051b030c090a090501050624070c05040603031e09050f061e0a020a0c0e0105101110020a050316180b160f11100203040b1819060509131a04 65
    0x10f03060750140b18803100411501d080644810703071070740d030342e60701030300a0010a100c1e8030b801c00340850b0340600300030101d0280c0d1a403116034000c045c0503d1000405404000440302c81030020030001c0c03c24403c0594a00300a0080305e4000c3d405072a070302c0e200e48040392003403144400c2000d1707420017041e0790f2401e84200d003030007a02e40044071420244600c6021301e00c051202000a091100308581c0103003e150000e1602e40c0c0f00380b00b59070040d0f403c2082c03480103100c182e680304105c40500c1444d16040c000086d00e0000d01d031418102c218809900303480000e8804a0707982c014000d511803880142600d17101d007aa0402284c1c00d11520f8010300d06891160390038403404418a000b083d144449042c031200080c21900d1704d0320b0306801040d04442c030a11942448d0020f0400400105080000e40059401c0502d403100508070b600c42e22444400d00d94481c0c1030143c40da59a06080072007141607031815580360b51079a00160950788107216040c46411846499400200700d07000313011080008003c0c02084c03083c10b109000181c04c0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 885390548 1250 885389298 885389353
    0x30412030302070525170613141203090709060501080601090e15090a05040c050603100509071707080106081003030c0605070e0d080d0b040504030f0c020103020f0c0a0c09050405 78
    0xe0700c000910b520421040c4d01211102c0b1941501c846031511001c0ba55a00c1e806c6044505a00710700104084079450050885580b0707040f58a0f07a40064071001840c0c200f030641c011010108a0100031311801000008946041d40c4000408104042e219030055684050840c0e5840c006101400203000b045804900c0c1c0ea0058079a41d0380120384100480040c0009004448130701c15075070f8603420003080c0b20104102d9401042d0503a4444d284d0300b001c09094204050710f0203003a001e0100f41c000b0508580c403c3c00d901400a000540001c4a420325460045c502c40f420710824000518010201c1c0d4041c10a00e52070080300d40c591618207100c150f940c0c5801c05010010498414026201c1c03c252035600d641e6591355486100c0d010856070350240000d41011204d0380c1e03500501079442c0030b08100000b5007000c540070f40720619051031816000d8500c012000b03032188d0f4443c2c003201c020100301104081c10014541308051b100c0c48801078103544401c1840119542105c0107400e6070300c40d885089041c806c0c039401300c0c0c4082 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 885391798 1250 885390548 885390553
    0x601090504020d140712061509090804030f030e0402030a0f0c050c0706031d1606020d080118050916090b010e030a03021f09050613061a0f041e090803180304120303020705 75
    0x10354505011803410512001070b80c00c7d50b00c03070085812400d01da00c804000340c51401c3e010880801c081d01e134002035001d02c2c00010005860384800e0014140075800c0c00d05050030080c0103640d86c0c50b010180c50b02030304070100300d502880e00304a01c0d49080d81c040d000b5680e199401c4402011064603113a002c602900f07110f41b1141d403400420030030100e090424061499940003904440118a1801a000b4a446d1b032160701b020810100c08010301400000b80302d81c0381096003102c40032070243c4900c04044d050100700d042c84085464102c0c400030f8050a1a008000500400d803100e059500201d01030540741d1404600090040c0c100c0302d50305030040c000141c1c2d414418190f030b2002505130026640e651810030165440348501c48000403090820040740580400d9040414a89022b1440c208c0030424004010f4421485641c0341c50b107071025440c0030301030690800d01001080c400c648050030140ca0070740c4196810104040d81c0803070030801c500300108a400f110700443e4969100d01154030110b00a4100c090229041d0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 885393048 1250 885391798 885391813
    0xd020406051c030807110307140c0405152d1207030605070203090406060e0d030e010302070501020f030f07020a050703110d23010b0117130c05030304170601090504020d14 75
    0x1a1540c00341e019065405420141030440542405004030701d00178001410400c200088101528010054030504c03980060400414040b450420f82020031138461680c10038034142c204004002c0407c601c12214505480d0404054016110300d18084810040d0768010003600c3d07801790b05810a07010b601601441c1d5810b40d2600e90b282c1d90b609050b91000d0383c1000041c0d00202d00c0b5410b515081c402c1754002c05060a068540484038000b20340d412080002c054280820001c0e003410a034043d030110364050354030038000c65941d41d12542520749600140c84016038100d00b04006505980000350490086400c00000d10400d4915580c90100280201c03a41d50040310450460780003c140185010040c02035022961010103e40c00320342c00c4444100700103040003070003084d0704d065415008203950040d880d0041c12814210078104082e0300c0c0d60130391086405100000d07000070300b40790a104040d4440910015103000da40c0c0e448454040d103200741c070046d6000001e54420700010710200c90455000350710200f9075260 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 885394298 1250 885393048 885393059
    0x10150507020640144c0207030b010f08030f070201020309060c0f3d23010e240d2102210313141005040c03051011090d020406 55
    0x5020000e0301da1100569511014010454003e0072841044c00c1038882c0b12030399109419424455044641c4162113440c040c4542100d9440c644429020800000c4003200b40c00031182e00a40c0c030f19182c801607620804260010400280c81c00da41401c48000b44001c5003424401460035880d94000c1e20103d055101c2000032808c9900c898001c3c00e680396514001d441e441c04148032a50618810ba1714040c0d1214048000052112018032460000356070700d000d00207003a111600503401001218800704808140340b4648400016072a07203a4107890a0084c454040c3e1540121012045070b41d0080c0d500951000642d0502800d10840b0000000c3c00351091070070035552020a10845444915000c0050b00940310788104500c007580d0702d00618120001a502d1880c7c041000c0064200c04c050003400c040c10060031185071041000360071010340f03440e201048503091614200d45a4100761100300c5442c020329203020b115404901c40c48440b010b80c3c1c514146000b60354010080030484542040740d1080d82c54002144 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 885395548 1250 885394298 885394387
    0x151204060c030f090203030313151d0d030e0703020d0206070209010f140105070b01060f0519020615010806090705090a080106080a21020d05130905101505070206 71
    0x4a02034580068040340d0a4401015104610400000c0a04008000c03006071400801c07a41d000d21801c1d00c2c140e05003480d1600c904074211680c0400642e50500009211030201d07030007032211000d1002c00b160318030070311301406030144c3c0c40000a012241e080487d0810240c1880f086030304070300b44020081460301c50781d130740000c0c4010750a03088844001c8000100340320240682c806441d010400b42001e40c144605a03139030b0154840c0501801d0100060f0005151049001d4001d444500692092145111a41c80002980c55008540d1240d140348001d600c40450b5006404003401030401130128a1613a5811405468a0348503441c0d03513401c400740100014a201c000e2084102804001d0060111046d032820003201002c01183c2a013144251042c0c060804e6030005218650a0407034100b964072500d0024506000c68404d9102c8140d250901c01002201c040f070060b02400d070b6a040010354248454040101c800703000342000207400000410203241810300c0c54404800320b80d00020501ca10004586030f145 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 885396798 1250 885395548 885395551
    0x203100519090f051e1e270c0a0504060f090b010e1002010c08102114070605091207080703062f0c011a01020706140408010606090f080120091801062f03091512 70
    0x701f581d000b055122400e8a820940c00d80100005c450a2000a0070b2443d403405400907449040d8030740703a5907000140e03264050304880604083c018000500201c48032400b901030885039480900241d598400201040d800101c01c80a076100320038001d11984c0881094640e482d00e4071000e4640307030482c3c095014101c0041040304086c00107a42c0710750f10f030702000c020300c900e03003006851034401c42c0c011500a20154000141d29030403680c01c4600031440d00319584076003c40c600b60840610850540c421060012082d250081007910801c000070000b100701c2c120311b01c074920f070381c01080c0f07005800008082041c58401c0c10320012509403c2501c07880c0541c0c0e01d48482c2111807580c415000b00d1406101007010750344110303112004100c100000c1c030008600c68900c0c1050a01c1d0231540c1c69020010800c1d202549603000d50403c2800e02c507649a034079584401015018940039811a0522800a0006140140342d0305032070f00d4940a0000030760130440031004019882e043e4410883d4488824401c100305400200c3c040e6 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 885398048 1250 885396798 885396871
    0x109020408010506060403080a20031801021009023f0124060c150b030604050c130b030a0b09030c01020d1a03010203100519090f051e1e 60
    0x5a56a107040c00d2035094a00040200d84141c200b8002003010a000341c04403a003141312481c0544401071030700b55001500980c0521500300380700114070a4008025240340c040303c928242c08840c845500f1200c882d064400c1d54030029040031100011002e40c1d51612400301d050a5091a9505c9458084040f0b4400c6043c004a000703e40e9110a03d40d41101c01e58000011030904244c05864105d0400102610741c0b0643c62000b80080000441409020003d80c4a020140c03401010307101141040e083c800d030340741d1500c5213081c45a101c011603006070190b10310407001d5928000d406480300440d1501c441c0901403005051501d180003c20041e005208284014100210940340c000b5140440c0303040d111032015030504c3c940c001ea01c10420b001d5008580c141260440e03030f048803408070006201c00d0b81408415107500c1600024141250900c4001c1e864010380c0c81910300070884182c0d00c41e106142c3c51404000e503041102c0c0e5200d050008151306880e1490b692181281c03035900b80c0380d509040140718054202c40803 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 885399298 1250 885398048 885398051
    0x60f03010213050a0f0f15050706020c1005180c1201090c081c0e010e04090318060e032103130f0c12060c021b040e0a0b041a162c03060109 61
    0x83c8aa4982080400060004000354943c09030805242d2081100e0f46e001d86050544080c03811000c1510441c2181c400c1c56002e1001c0d52114038180e800c03640e40701d18203400c0140d07504042c001108865005000b41e6041005801041030010303450038440185540d4484500c195214500c1d0070104d440415444002d1419200420fa1500310a40076240e2060350340c600700800c480c65070740450316a440801406203610031180040d000d03146180665000d10b1030010910340b5207040c0c00001355035402c500c0602e5180c8054090ba0381e03106050f8480c507001d68031915010361201c410300100e0011239480465011131446411469106a42500c0b00354001040d0b60110500d4803007044101d0400410b402038400e041110700003007208200140880740c5125420b4101401241e49a899101c820001c01110303225a0700541c401d0428186800c02c1001502d004480c0c011140300c000c0030803880100110f0222004541da0f8844004044218505001180030241012454102480c503401541c090000500902000c1c00 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 885400548 1250 885399298 885399337
    0x10b01140f03180307080406031503170a021c2102030c0f030a0608011a130e0c0607030203190302070201020f0303060d20130605041d0703030e2403011805100e060f030102 75
    0x402000d54a140c0305090300e002c080304d001c2000507200b402c0d03da65330510900044d00d40040200c12803501000c4240d80074643c000030402003c4581242c1e00f40300c02c02d4101d814646941c40c80700c5150592105036264015540200071080b640c01c84000956080f50940d04041341c00396a035241d20742581c0705c0b00840421030341450461840c1d8a4035031880c521055070640140303c11807111060989650450102c00d002e034600042030303010148240201c031580400f50f0360441407604500401030083d00701e08400c81c054400e294039159410f6000040d0b07481980028080107901b841c070b50300d010090701035400a0107905c00303c0303020101a0740ca03c4c4c841c4c00992102c5000261443c0307090200400e40e140c003480500d403840d200108444444000ca00202940d030076080081041c2e001d04040fa0014921018515040e074002060518a403501d400642c12515000e18004841e0139054481003118030a0701d03010102c001812007040490540620203038440b00003005054980350b0103002c2404ea0b1700400380c402c0102965070 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 885401798 1250 885400548 885400559
    0x306010305010503191203022104060608070e15011e0c150612021c0b10061701050315040302071e0801110f07140a060617010b01140f031803070804 65
    0x1c03a40d4010301c0e04030020040c1c80e0402a00a00004003c2406000c41c1850107000c40c410740240c04071148004404640d00342669248002c092103d000d840407246541401800500e40d0800030340030b0103840300c001804a080c0c0310844201d01015252010905210712102961601a00744101801456151b1540e42582d5202d15000c1c05040e407032881103803030600d06442400020081c10020101590503240c1480c000505003010182c81179250004111110900800c43c0c2c001c614003400c8121107a5895005105860343c00100d00210b003405001e402d9444010080e55038000c404a031274019009006480607152905502101c14031309448080e005481050b0401080d00244584205a41880c01c10703414801c1c105440d54440c0302d01240034040700615a103c0c400380201340510700341c0540c40300341000100c4c4d1720440600310462059030900a540703400010041c0354007071031104066007a40a0310364581217240c44089140d41003c1c06c0340700610310410341038507001801c00040603014043c035561500d492401 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 885403048 1250 885401798 885401801
    0x31e01090b0307050a0f171603081201050117040f030e04020a0905010908060f010524031801150f380712090b030703020a030b031b0111011b03020702061b0303060103 73
    0x794031103030080410740e4040006c20940017603030058801c400007207501003070010030203450034040920b1003881d012082400010801004028100101c100c06445001da0741e52005584074603004040117504510b40c0001800110307201404101c103480303410644108101400860106c0e0072414400300858401c2000780560343c3c2102c0b103280148101e8005004c2c9150075660003a10000c107104450042c480000d504814050155034042042400c0d6840390700d9180041504d0f040c02602d5808103103a518003010350315000c103450011010744e100161100803452900980101d03403202e429084607613040121018203440f5100300e503050400038500c40c068684c4207508040c0f001c074081a9000e4240a0b032500304100c01c10030324050700e40c8180e89040050700d070502100190040c0c04221450703035245c058240b4003180c04400c4802001a200e0aa842e0500030044440180c22600310295840d410f10100c0c1030141c40d240310390024540180702502060030700703617458020100c402c52036035400f10035040441080741a5034075 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 885404298 1250 885403048 885403063
    0x905090703330e060f040c110a080d0c0219030e04112125081003240e0118061a030a03110d0e010e0103090602090d0b04060e03090108010b031e01090b03 67
    0x2482007421090070110b00040d45007911720f00360360059489507018510280285051510503030400103907110841c01e4a03050102c1c0d44500d450030b400c24504841040f40e20f01c0015651030107071200d0310324a95420180c07000e6882003d0146210380c85a01e6600c55801c0150703007005040b0b50807584005500c01501c203502024110b03030043c1400040a02561160902084503030406175206d845c1c00d1440098403412214050200380780c10240c0391005681032101075141b83c0400d0000c005c200242006444503105e102d900b6201d04e10b1f0a51840749c54440c844000c0780d8903902545142d02c00c0c9842d071100f20300c210302090400d1880c401c103a011940701090994171580900c4082e400140529020b04094028000039150301d40c0400760504240d9035904d11410400c2c0342d411610010401803103d17000c0030407480d00c04070300d00d0110340c12508541031006005440b40000b05580400b00140c4450450707a092860400c06908000c1c03600c8115804002c41002c84024100881c3c040e0a102c480850704004100c11f15241011 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 885405548 1250 885404298 885404309
    0x60c020a060c0807080706020d090f0b0901020306060409020c01140f041e0c03060b040608030c03040617150d081218160f14040b0907090303080a0b01090509070333 72
    0x12070907400c0001450540850b203084e44c0c050030300c0e40c0b104414100b4400034051000500740140c07a001c408000d00c5a41c828264002d03104400d540588d87d0759006040c00e0307000135514a40c0101c0300348010300c0750300c1654016110b40c1a030940001080b20541d142020202405d9030001098030b440c400784414800c520480f4a03104140205508045100d42d032411a0000300b403102402c4259a550546410b80d01c2d0b03080000200990000c480d1504000c102e05034032a03000d4415500031502e01d4a0b40600404d05c0d1401d58402d007141c1c490313402c4101034031040c0640c480050030200c43e800d00c00c00c10070300354003056000310b40212003500003d00c030f2038502c0c0c211628040d142c510141140038881d0080240fa507002c20443c042d5a1884200d0307441e001980c01040203010a045c10940c130511840070014544da014280d041164002d503031703007130a5131100c075181400c450071203400900040319035a0500c0a41040c002c0355412203c40d1500090080050034400500828001c0c1c2403040540c14030420f401302c4001030340001412 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 885406798 1250 885405548 885405557
    0x80102070f020906040e0f0303100504060311060715111e03040c050f01050d0203190606050c03030c070f150f1d0c090601051209030c15010b0306010809070f060c020a06 74
    0x88241d1641d0550001840d0024840e4081c81c00141c81a261600f00822004d07a5004a40307100042c02e15190b200d8008942c0d044040202003000110341c9028050340c0d040302c0d0403c03540c2d401d4101c48003c1c05140d5201351000d60b28510601d08403c81d0558a10421420340541602e041d224401c00d2a8908000b00050141c4031603c0c060084c4000300304441c4003807003241d8088526816140d04180140c400380138440891106910100400c50700f5980d104448002001c25a020401240c49a00c03c0e541401280e07480105a4020b0002801109030b40d001403000602442d1713200800da000fa940c00d200e01c1d1000446042d80394980031001e00103101c9004121010350304910358120760224580e4155542c200d400242c0c45000c08501154076a4002c80889002d61041d5000c0e0142c0d00d4210543c40da03d03800016210024414030003c80c000c01d0b05000c1c014140d541d55030540e450b40e2070705c000440b0401006082d0440502540340e00240c5110703020707428001090360303444101241060340100181100c05610420030700c03 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 885408048 1250 885406798 885406807
    0x10b04050a0b180402130f020315060406090905071407150b0916032c0a050c03120a0c06241e0f0e0403090906171c0509010e0607020406030615080102 66
    0x50382c580200303150003004100c201d03e0b6540d440c00060585a8181504424035142042c2c811560400350001c51180304c24001a1903409050818001188564492140019203501d81400214039580056401807690701e0610340e0b80340f58050394032841d40310f80d90450340f42c1e034901348580a00d00d02e8000c03c00400c4045421981c0761509280c01c0003184500c2d080001010344d181070900c01000d01c0000440c803516044262908090000c00d001c1d602e440180c42681c6910441442c41841d1a00045d010681014015400d06101c0c0c1c0f1003081d2103900c040032045072015281c81408441d0070481c0c07000794040c144d00c0003d0704001d24103030281c0103014035a001c00b00c420301000070521403a010344020b42c013241d061940c18151581c4c1c5040c00c80340108560402000a818010000f45800c030141000c014500b0000036500c120b01d0440100c001088105008030100e08244a1841c0c2c540c0581440004aa4058941403400da000d900103402c94030142c208840c19030b50b54010580341400f1810b0140640f803049c000f140f60 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 885409298 1250 885408048 885408071
    0x2030312010311031b060a140316080f15010807020a02121c11030403080a0c050313090c05130512012a020c06120a02070807060516030b01230d0b03030c010b04050a 72
    0x5c1c4c0301240103030700400c000501030001c24401c4044901030505440d01680380e04005070f170f210002641c0049032002070300800c013164103180c401070350f54020801c082021010203001c00055134020300c020440e0056000360301c0b625000d615610002490039640c01c000d0540340000b645140e40f0a40a184510100008020a030541d0040001140d05a907003007501541c451181000c100c442005c8800024444e000c0800c03c0700015844440910684408070b000384400e03404190111810300442c4a602c070190080c44007085582809100c0811101004001041040074592003009036141e40d4034407030964203180000d0307814a5050084907541d402c1110242d2401c400300100c800c055801a104007456540050748004010170b640403540007540c401340c14041d602e4010318072000100050300340004281000722400c620342c41901b02d8100c1c200b482940c60081d0030300d04000070b03071500400007020005070b540e01b9410281c0e07802c2001c1c2603890f41410000c62001d003804148400e440740649030324081410503202052 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 885410548 1250 885409298 885409333
    0xf010e10061205060f0a0602070302010e0d050c01140c0106030b1602010c0215100e09062a0a03020d020903010e030408070807060f0509040b090106030213050d17070c030203031201031103 82
    0x298980c50210115050b01d4810000e6514013a4104c01903104a624400243c7c540d0040b5504049038003d0b201d000540001c001809198190030b0801003041d0444000400c0310340c080d0340750f510801c0004d01d10382e00340545407540760300f1600301c0d0300180c600c0c00d02d600170810b01c0038030000c036200840034502c000d00c240b1006180283d40c58540310f14403203240540b040041c0039200c0921102001300852591914107013030500910342c407000103075103d82011340c00800600d44044008010718901000400c8145410035240c0b0840080d00302c69102c40049808014265069a00340510300001520202540d512072803c01176918180941d4001000390304a100c0c10003c180c0c0102c52989a43c185050040e9681501c10005004141045016511280035030000c10111307450f07405011060303505d0703040403000b85d00c41d42006505c1400300001042411084500652610303108044c140d82c07403081c091000303496100e6000a041d90441411411141401e000401c00e0109082004042440c11b0700a001c4200c8000000c00 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 885411798 1250 885410548 885410567
    0x509010b0403060506030d0822050d030501051c020616020f09010303050c1005041e03030219081b090a03020f060c01110310090b010e150412080a08010b041d060d02090f010e1006 78
    0x440402702800c000079100300000c0210340c6d03846010390340c0c081007151024008060070f015041c002c3c05503810741006145c042400c4141d80750010042c508003030003c1894008000310840884c1c01026684104a1a440741800240030f540b1945549490b1500003d000c0d160503001900441498240018400482c440d030f01c00f000e15505802980c940c1603694101078019100301002d15180c000900111402d0640c80300b0b8950140c980241e0084d0442c4640703200c80524000c4000c02d40d4010444507041005180400e40800c074984040c001a0504c800b2000709802c40e0f200c100b030302c0d082e10f03400020401540064400c040c09022845820007242940000007083e04c54080c24440c0242d640c030000e8103640c450201030340d000b05110128480ea032101403810742520b801031201c01c804200d00300000f02d05a80c0b10020395060300e03000480791001e010030601001248001400c0507402003945044640540c03035038040d040c03181c001c9142400da6540344c08150b5a2080c1d00500c034004040782e211303040c04541da1050401 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 885413048 1250 885411798 885411811
    0x101808040315091202060709272f03040201031506020309010e0f150d05150616020406031a04150c020c0918240901091e05070509010b0403060506030d08 67
    0x8a840380504800900030162010080d1a80d43d0061490202c1540081c201e44294020303503501c1d42441e40c4d02d900727141e0000c0010160001e000d900e811070045e10403aa00035010340b10500d0b8211141c2c1400c29100c2228400704042002400c070000403c0255600360041d02c6001800480840700c103440d11000a460303009081d9024100003814420341c039650b80d006542068880c00800141460705000c4030501c0d99446400c2128901d424640020400d034016101100403030300c068106450038480e804200010308580004980c8075540f240c4c080007140400048500d1503500091080841c2030504003c4101a50f50080a25a60030711202d100f4031035021070403d648403415078800c00c031501e40760411900c0e481d030f81003810b00c0391141d2407040b12032580d0f40c0d1143c80c0081c0c1041410000b0313190045174a081e10410000a02452490800b00a803841c0401884240b540240d0558400075100e50000e0841c010a9100e0144400c000c01c0510078003905210341600070310100c0080c28018412079000d0090344005001 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 885414298 1250 885413048 885413063
    0x106090608160e030105070306140306040201020a15090b0703060611010e100b03030409141807080c01110c13150f1202060708040b0c03030f0f061807110106081018080403 75
    0x480c80054003c20355a01d410100078001e004510785000020000c06a0380304070a6100e81c0021a01d205090100d0b456000781d0b0181d014003030112540d01ca00c2d0b404840c000713440f032050b6900d034190004112841400790107104140e802241d41440e02400401c940340c080d01002140e4940001d980070020002501812102049800b0a450980c000042d04500030f40e8404c1090b42d0414002203808000408014801c40007051038021708450100019a2030380280200f510a1f030054078410b0302c641c00345009580303081c0f14904481044004001290070f00c0040f03914114160b131a91160030620412b6003c0c503010b0b1030010340510f60907140405a2511200106000c0c2c003c000c00204141842011821100580b840c1c086680d51210100c101c07c0d030720307130040b550703d02c500c010350b00842d90310900901442d0088000401e203115902e48001c54030903440b07000d400381c0c00384905070340441209a02030203142c000300014800b601d034000c810a4400151100c500d40c040c20f0100e80e107031400005100f101980c0c1600c0e00080d1 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 885415548 1250 885414298 885414331
    0xe060310092c1509160b031003050a0c03020301051f0909260306040b010f020c040f2d0e0316140a080c0d0908030f040614091203120106090608 63
    0x2d2201c0041111480d201000000441032a2460800284400f0b40300361101c076901c09030341d42155240c454070580126910f1904034501000145049000707160403400140c05a03031f120342e0340c1da605403a00350809400c03610101030f4a4204207514080c411250b101309900583c00f80c182000c07860f02100c2c0300d14010440c020340e03152035145c288403c0c9030395241d14aa110b00002d08090ba49600710415400458281d40f00300d0420b540f030318855214100d50b5804100640091150080e56820800036000c40101040c3c02603586840e1110851031004161000040d464000d1804030240e8a24081c0c802c0b00f642084280c0c03007045426450314100d501004425080f400c145c00c051401810a401c01d10038020181503410041491040c09801040024510781c00b03850f9644d140d940d6114041e00c80c059072100300b4415000740020400a8011a10446100098400940b60582d2040040c5072107500340f41d80302c01d5a1000c01c0b0307030703400580d400c074480d01502d40c40c1080e5010f01e10303220004248450042842001024070709 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 885416798 1250 885415548 885415571
    0x3030c060905070e160509090402040513060c0f03140708070c060e01061412010c0509040c02031c0b0a060813110d0c091b0309150c05160f030e06031009 67
    0x50001c0341480e0b0003400d030340c1144e5698545121011090700c0900b20380004030400210b45004074101e96030207002400d4502075545d143c0821008050060081c05030080300004a400103082e4440c00c0e09002d0b460b2103030110700c4001c1c0402401c4401c0410462240d09244003400f240301d82007001e0741d80c0305900345800d80f1198442d20705080a8844100080e44ed5130070000302140111038000340780304600c0140c1e02170031130000c02c0103a1420380e16440c02c0300c000301e031040003241c45509182c0c200500c003a50710f0040b28501030b50f06400c00c011034681e00800080d1039480244104070302d04425110010f02c0c0c5450500c00034101810542c3c40f640b4482c1e4000e0510500024800301c50b1a05489502d00075044222040c007503a40d520214040c000b00d044011080d59405101d2040e140284502e40140f50403641e020149205400c07402d0003003140309018800d0100c1488001c0c00c4c00083c42e20711411500ca2580d07602e1000d1107160207814001225070070b82c49814103000b040f01400c80305a6681c110352030a0400f01380c002202 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 885418048 1250 885416798 885416801
    0xf1a1813050f0a03030e15010302010f05040320040b09040305091e060d0906050106050f1804060e0903071211250b07240c080109091110120c0f0903030c06 68
    0x304001016801220401144000c01107008041640a902d0031b10a00c044179807029142e0501004428001029500500c0035510030f014a0780c8004080c20040c0c601522600ca14844140d10646e0340c14001e4951030080f1141070038005c1020328581134852101c58100b65030094100d01034600c0c0203004079030144100711000240001c03800790fa400030700340741e541e241d2440c01c030806003503103c80503210740d4203010000035090300c10f6080b2003600b542e98052504001010140320303181140e81e400107a220fa00c650300800c8004c100b100ca6405055100c1c015542c070a81403030124030b1903140001401c20300440d45481000e800c004118425006499040e500d0724203032115445540c3d0307a580d000320003070502c085001c104006942c100300c014041c10300f4102015105600c1d4880a8910200060002580f0f03c0010010300d4440d0f0031610b52988144080802030700c25001103490340020b40050340005001c094410b0892590b0300c226030219449181c000320750003284c1c4c80580100b440f403000408203c4d40045c40824001135 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 885419298 1250 885418048 885418081
    0xe0601170a021305280e0d08090706080c1b0d0206070f17060a030b070e0406080d050f161709010e121b041407020d111c03050402120a05010f1a18 64
    0x101d0071301142c20610605c1c4e07a0014160314100540394461026000c07601c40c040c990042c40707110800000c1c50090f0070303d141280e00c080094240c502c002800c3c00203540300b0100e0381010207803a1400004103918407040300001c4c40c1c114080d00007018070018039035a60405a0008010705010b4030404407184548640c0c000c101070900c0390303101a00d10312403c800e002035207901801c000a010001c890500c6240e468609003138035a22501c00c460081041002055403601240d409082807014010010b4036030764041c2c54210001801241e5003d40300d4001448014641e04844074240d403800c185c81c0c2520981e60000000e41d6600140080f84404101400348001690303180c0041d61521007100d10f00b000c6003040712001c0c0d075070850f40c0c0d01d40b8049181009440d440140000e44406030300c202c42801400d0410369a800d074010080900b003030303070000b4619050343c8001004004030044a0300c40c800016140798041955002c49504403107110380f149040185a2244c2da40e2041c0c1180700300c140d90341c900f6640f030b895001c0216598 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 885420548 1250 885419298 885419341
    0x20a0506070e101119290a1116060f020f120603190308161e0f021908031609120506011d0105030618100e0601170a021305 54
    0x552020000410b41c04501c800b00d00380140c41540d04400b00240c1980d80240803e9a581994405070345c1c1101844444580300c1c540c2c0c040c00c0074402034000090318100160240303613081c003400f03544003e00c00c100d01c01d807181c0c815200090400d6424000da01d208411482c1c012030020700b10075111640f42c5081c800039030450304a4a210381d0850b58801e01000d1020216000700c92043c8240140e01c406008030240f202c1c5100c0a079450703525008039958461a4103590000c500f400000c002c0a01e821109050983e5551454107110ba16511102580800024508050400168005c040e240a44030001d442d4400b83d0b600702c51800440c00359201c45807021600130050350301c0750620386116062402070040103c2c0d42416550180c0341c0510900b206e500078800750000707101c4c05030140c0c44400013400c200c0c010042d506200c21488182c45004c0b140d00042026644030380300c64203054011000400c070a002401010303840040f5078010301215440b6400042c1100700c040d00c0c0c180e6082c1c9441c000b603403805018400e444a141c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 885421798 1250 885420548 885420553
    0x70f080a0210031b262e09090305030405010c0207081b030a1205031f1202040b0f090702010e0c04060608070f020a0c090501031416050d02030a0b0112020a0e07091401020a05 76
    0x40c42040c00501d4444841ca511702400c9042803240400d0340400c0c00396115080100c0b82c4001903d0011014154000ba0920807495415280020610200b07600a4080180c00f0395034150700da041904109086403081d0706441c080d5484400100264803001c69040c80310300e20b860a60300c02c0d44003000402e09200751044000c3c5202e2001070080d4290350402d0181d03024440b60f4220792025030200010040400e020b001e0310101c00d9507040704000514042d04841e11201026100300c844408000100b01604000c2c3e5041e00903035180e110829109608205212112600700c5051240342d103051009000c1c041d0203060b12040201055034143c0741c038002c014440b000b81e800012070403003039074944240005000a0000310346202c505010540d218100080425885400c01401c0343d0f814607100802c0f64603c083c58040343c1500130700e40301402244103601880c2c001c0c4800c00c100c4103540114410130060f8011034001002c1c1943c035805014009500007012000d80345588032140143e260000180e2518441150050643c03 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 885423048 1250 885421798 885421841
    0x62a210b0126010f0b090102031c1d0f0f0c0603010509060d080408071503020c0d08060f06181c0c030b060d0501020307030c120603030e0904060608031605070f080a021003 75
    0x542021980504941c4840b00340300103141c5a1645c55081c0c820410500d00680c410b10003807a9a00594140f103142409165001400d0110510b1404e1036440e402808880c40c1c00252204030004018441c1c0c0300440060400381c111800e01100054950006015860003408000c0c0015450341712503100345e80c4070b9000740383d40d41c070340d41d51300802a5509400c0c0291107a000d28a460400b980c3c0c001e0083d550144c6041d00540783c1401d00400031503403030704d0051000754030110008240809071100f0004041e06041120707060000c0c0303602401d02440c68410b0214808108095034001c000c6540e0764004c0b0b05a9034030000b60780c0c50b030b20351030000360500d1860711002d00f0787e510000030f00c1500394146d400031040c3d04a0fa2200c0401d854605200c0d402c6032680c0c8800380c0850601c0290545500d0b1007902d2581c0107100e1400050800d0b02c0d42401455170700002c204181c000c0803881c4160901c8001c010910003440030692020f003050a191016403640002c01c0000d000c0c0d13640e141c65200c0280203800500848201200c902440b = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 885424298 1250 885423048 885423107
    0x5030f100b030906011d06010c1113060807081605030a150920090a05010b040902031b04081b040903120c02010f1b08151516062a210b01 60
    0x80d03c5086c0306000300b00000d400b0003184005030302c0c412441048161240180250145c030b4501c105540d81c0c3d0800e0740440c0311a00745070340c0181031007900c001d0003001c0c000f05492810240000e10340386640044130028092404104042d41d00041d07032003001548400c003105400e0400340c94801805a0356001440610b441c009014101c40017940c080e91348034102c1d44c5110039240d0310184002c541742030046040d041c0c0204410b0200010a4004540041142c103070700c200c400c0e032038141d8009500a608990320940208000c0021415116207101d40c00500720f80401c0b5408035664054404011101b4982140351205403003500f40c1d0007944020760b025001003041c04a4000e0020b111504504651100040399000010504041c807a4034024440300d0051f01420b070083d0a40e62541d210b80081c000703181f1040381208560700203040c0780100802481e006c0306000071403d1400311000b403030340c4075501c100070042c40414036144841035842200035021000000208184d003980126035841ca103540c24164060b014816204 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 885425548 1250 885424298 885424303
    0x305030714071a0304020f01170106140f0304111906050d0b0f041a010f0314010501051c0606020604031106060f0108090709021b0d02071202131d07060207051005030f100b0309 77
    0x400c6101f16000640011400d00540e030800030a841c240e54203003c40c0c01400386074000d40220f15280c012890441c240340d40881e910312540e0040354119160a00341c05c0307020180c00c10400c01940e00180d10010004030b801c050004000d8020740022520080d1580304440c000d403242c90b40340000410181003031089848040c3c4140c03c031090841014000f64074508201c458510178400c1c005111890001440d880e441d11004490b1500240c0000d0104120014401c10014a0b841004020100ba401420042c0307818100600540c8900c0080541ca8009208010030355031103c55001c088071003401d0104550300d500740d04a180c4503c90700180c140030320000b00003240081d070002422411141d08101d40c841d00c92000300301c0e254030140c4260b0b0b1503101800d42c11001850f04c000303c034581040003100000c8030720803001d03101c03075075842d46c200016550800780091051a0381402a0340252009440440c1c5010310020001c0c898400240b044003a000d4040100351244082c130940c8000341460710210703440e8104080d0958 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 885426798 1250 885425548 885425551
    0xc0f010b15090a03080c010b03160323100f021e04030b0603030702090115020c04060308190203030702030403080c0f1e0106060212030a2a0f030b0a0305030714071a03 73
    0x7441442101c0c115241c2401d103408841000001038030380046907103035a036403140640001e002101c255480d00703100c981c3e40c3c03020482110700c03c99a4540000f07803495410000d4101c2c3c0c07030030802c0c0f01400a6140444001200145104901c2024007000486803e5106004002c0c050360007000014200014000003040b084805002901e0040003058166180c0c001019038070720600788020340110707100004101000440031192001415401511110b03005c030750000e0100c2d0001d4000f1110b1100c0815855002c114a01c400300300c28000b800194610f08148001954900444c80002c00c0c4190006025060550900080b00c10b2040442106c0e02c00d6500740070b5604040080c0154180ca61a113000015840e2000403000c401c03031601c0840902d151510950780300a021203058030050020380c0315250683e00d000410b07180d8a40082d07641c030911040d50400c010180d0340c4040b48540b041202120903c080744011007121446030f0301110a2080e24014000281011202d074070003030f800b48000105110400300600110b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 885428048 1250 885426798 885426821
    0x917160b04060207090902010e0607030912140610030b1308070c0b03060312030f0c0702040b0904150e0a08030c13080111040906060c030806041503020915150403050d050f0c0f01 78
    0x280c3c0580e445004000c221b0341000001303030000b900d50400c4080ba090810051201d54060700c0c010744a61b8460382d03c07400800c1c01e8602242c9060b41c078954072201210500400d500092080029009245151100e11100c44040c00254800601250313040c02c004c080021542c5440d0300c908500a007564810900300e080c0c0080710030501030b01480302100100ea5030311040342d120700108101c1e101c1c10b0b140c2c0350300309985030423140040341c210380c1d14400201d0b15502c107134181c1d10a5200704200301100f130301172403c0e4013507032004800c035580d60784013640d030000080e43c81054962000b42c8040c03544d00d400580c2c8046074415441e0340591501e51a11001d1040841400700600c1038408000007070110304e81e911012030351002c40200140005041c40c01180261809402c840d400a0007803032038a0340c2c00d0b1240c0000b4406a03040e01c1c180e1040c007420309550954102403005002c210f00c0c03115502d041c41c1ca1138a03180d03160480d2800301010071100142e0100e520591000341c9001140f46011102e545030b0003c519030080c44440801c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 885429298 1250 885428048 885428053
    0x2a060603020306090601030c140f090f0402041506020703060e1912090b04060804060e030f120a1506020d030203060d0b0f041a01120b10091b1e0917160b040602 70
    0x70703e0013240094000e040340c0d40007020350422446d10b071304011400c0d400204c07541d0108809406036840d54410b1083c500130b40c25500640402c1c10980304000841c0ca1444460000c082241002c2006580104e05035007101d130001408140e6921400a4504010500743c2607040ca0903284000b8007400209209607144a01c00d03115084469103880241c4490f00903403182c0b00c0066075200020300050326541010800b00c01e80c408482c20040c183e034520009802c044c4c9201a172880caa8104107542140340110300e007d14440a2800c202ca05042000303446007800c10b28041859000004100c0702d071180d03124090350b5a0807030407074001401c00c600000c5800c6001e5605480f51040122140c1c1003003411a0810304941c54810307207100c600d06070360311044100c000030041c00304201c150700000340301c103858050f001c2204000003d101c80b5185552010f031080004407a082040c0c58101942800d554205607800b0079a4100480c06150946506c98640b800e440c2a220070205940c03110002120415000500142d6803203809 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 885430548 1250 885429298 885429301
    0x14031905130311071a0d1e0c1d0607170d05070c060b04050c04050d0c120303090b01080604022407020415080d0206060303030f1b0a02070603051e010302012a060603020306 75
    0x83d81c0d6444da8041d0b80424400030320034643c0d000c1c1a40c02440f030030b80c1c1100b0228a2030302200c040c8420392980404484c10944641d02c0c8401140e00c1007144c0403601e44030507001c0050090390041080c0703009811000701032010300b040084802e100324040c1e810154070700341c00780070510705264000c000c1b0304e0020b012240c841c140300b8515028545806014414201100d40c3c605281c500800c101001ca00c1305815264070003181c4000c1f40040340604124121400ba85001c81c051046242009500350164007101594001105010050359410000603076460056425044d07924107002810642c40f904500035449460f06965001902400c0000c0c801c652142083c0c640b160758601c1c00b681c44481c100c500c1070341900200f000412183d54500416044101884881c898181741c110700d00d4180e010540720f9000d80d12005080102950602035903920004171500c0d81d400310b80845240d08110b10601009040c0900c0c1d880503207403106207510070508540c0090341c1c100f801c18a0b041c80340c02000b0074041a0b00a004500 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 885431654 1106 885430548 885430577
    0xf05070b040804050108010e0f131e0b01050306010b090d0204150807030308190b0f0904031202120f07030b011205040f15020a02100c140319051303 65
    0x85402c1c2c0d90741c0c140000505081030507401480105c0c002d6040002c2c140200c4400d6810159024002c900403a01c0c2c54900104d91441d504c92042c4411100c0703017800c0c00700c0100001c1c1240d03000c1c0c060314038603600c0300c249240c0d911801001c203030400810749075840107081503070120303042c1000c98403442120750700c48604038100082e039803060300098112000e11201c000200d22518031103580c24410086426048040354a000c030b9481c1d00303880380e26040000380a150240d846007070b4031010030504540d500c2c075444c2c60740446002500d0780c0c1140360700c81c800100d61030700900c02c0c807004c200b05840740419003007040c0030b91001e0a001001100d008000c2101c0c0e1002442c082c002020b195203c40000d1b88038640044001d02c1c201100354141c0c0d07460300f00300803420001c1d00551150f0a00034901c031121396035960403100c01c24030301c4008440070300740e4035240c10417070b04030f20881280030024465915500c508402a = true := by decide +kernel

theorem cover : BRFrame.Cov 885251798 885431654 := by
  have h0 := BRFrame.cov_init 885251798
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885251798 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 885251798 ≤ n) (h2 : n < 885431654) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
