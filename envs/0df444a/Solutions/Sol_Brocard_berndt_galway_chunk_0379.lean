-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0379
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:30:46.324811+00:00
-- url     : https://prove2.me/submissions/226dd137-deaa-4b0c-9d85-698966df1e11

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 67985614 ≤ n < 68165470 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 67986864 1250 67985614 67985627
    0x19050106110303040f110907050901030f060522061d0417090904080307090308040806090d0908250e040b07120501061b050c0303210603010908091011011404110f100e010306050d05070303 82
    0x80c68814420710ec1142404001080042d120810202d000d004050300042c24041c3e40018000701030640700f4094940300c03407418140080301200c04a074020b210080d4444003586641c203a80c448080a4040d1295595582d500309072684045d0030003007070000030000000014030309801440580228000740449040180d0307814a00f5103001c0700c1005020b00707810107100c41000002d01f80044101c0d01d41a0302d40078010810b0501c8a40c82d50480704840049400b00824064241700841c01912656502030028020704844000c5070020300590000402c031244d06400340c10150517001250340070f18240d45900d541080020700d5580a4421508202111480e1a1500c03501007400c541c8031005600901c200d00c00d90340d0312500c9214425245100707000070301404031558403170541c6400d0a001c2d40300804c044034805042d0144040d044600312079503da00d149a15150900d4009001c055401400a01c04140c4202e801e580c840704003c40581015500c40303001449a80b010200e00007140540d0280c03422505500b0004c104 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 67988114 1250 67986864 67986881
    0x606080912030a02070c0810050403181202060f2101060f03060f090e0a12120507030b0112021608030c040f06140904051009020319050106110303040f11090705090103 73
    0x40d0380140522061038020401125400007244500595a520031306d0468041c1413945c01507006881958a0410080c0e1998400d038010b500a440301481c2083c2142d100340c2c0301402e4000d4a581a104403000c000508207039000d480c1005e803000714a818a15001b049800d00c0140317184903208404942c00420480d0303086104880e03005071500e400c1c000703541414200310690070307180f20b0303040200d960b012114a071000a00c00b895005500002071203021004103402006038500301d8820940614080100b48158000c1c0b21f0040c1d4051706071074000c3d221141c442d1038402504000302e0181044021a4140000346003c2e000314401c10b58140c03001d465a00302003a004d1048425003040b001e0002c0744140824008400068a00e49002180d0200303042d52605c00d6510000e140f58070405040d80044140072103000e00c3d0700e603c01c54000081007084580e0b40c480f4101c03035907044449168140c0e003003000401d011a0403100040300c2e40f40030b0481c200700c441c00b80004c104841c000711404030009401003511605981e050050191 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 67989364 1250 67988114 67988131
    0x121501030b010207150201060314010b150306030a060e01020f0c10050f0108030f0307020c0d060b0907050a120504020406120b0711060105010909020a1101020a05090307170618031309060608 83
    0x1030501c1c0e60010350b403035903140100ca038040c0481400030686803003500200701441e80031a240e00c7c04001e450245000c6d0100d440c42c54440d40d100070321201c031f07031407101c050301d1240790010010b00c03410b100c544880c0014845c0a40000e000e5400b003000105081c5e0020040001d207441400030a0380c2214000d00a00700c40300074009090000c0300e00c00401c55031b8800403c1d25030602d400d6070785690f2901d8484007070f850101d0141c401a04084480b0801d018441c20b903001900201d015581b104c416985c00c181241c03d80b1511040c0004542c0000b40301071285181d07800158068070140c00050001d40794915890540d201c4c443c101c540d10001403c0002c1654030010b01ca054440300f00c000d05140d4182000a0b000b02d085009002c4c509a0114180c10401d11401d00444441c50031002155039854010004100398801c805940c040d2090036000203286958082415050203020050075203600c0e00b00601016040c0c00076030000900c014004105007940c2d02c20880001c02c00350384001a0a0b00c0c0c208054400e941c000c280744d1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 67990614 1250 67989364 67989371
    0x17130e041106030703020903010c0906030c080c0a0c03020109021e1504060c020607020d15020c120708041a0706020c0601050103110304021806031509030301060306150207062312150103 81
    0xc00101400d0071040001e804031202074a0340d0b20b4800440003400341102041d415806c059620219a8000c44c0000580d10b190750103000208080384240c076445402d880103110101c1c100300604080d0301c51017408601d144240300208a28400740c0004800e03540410303081d80341c00d0b0310b001003400524000010b14842a01e219607181010300e0000060020ba6000002034000d0400040110440d900d09114501190784040b002c80712000703a150082c0290440c2c3d01c100c2040c071903200c5545c0820b001c0c0c005e580c0000c2c3c0c8041014601070410b20340840503141d5600070401007801348800700001c1c0d2680041c0400e06005001800c0944c074150005054422505001080003820401c1c03001603124404800c026108061864444d5250403021038038055505a00c1c8600601400038444840804002541243c03800e07a41805600d4880c1c04902456070024020400340c3d00c405420001680074050f05080c6c543c140c440340b00e2103040807401700800c0e03005400720007100c0400010864190014441010085400c0c40c040 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 67991864 1250 67990614 67990621
    0x207120b010501140702040e0a03090f0b0306060d1b0e030105240f1c0303020c0c1f081009060308190513090506060d0c1d09070816090317130e 63
    0x40c10212010301039541000f19500b140c900d854280400c0b01c0206501030001c1100131400301980d520750040c860202c001684007040000c003d25042da005082d00d01969425186407a0001041520b0f803241103c000280d4440c7c84002a14020550041f02c21201d07403107101c01d264082c000c050031104024801d0f40103125440c580c0c00e202d1452400c9240c0084140c030043c1900b0100c800140000d2101501642116110392118007090b40c183c010f001121454411100140485410401004810700d02404400140022200076500c24041d19030071415800c00024900d0311820301c10300391000c40c2c1055410f02400170b2003003030507c0300101500f200700c0c4c1e81c0303015810300c0881c82c50342407048480d2050318403040c2c0361000b0a0996880d8011110140014282048003105140d00038000c5c0786091f00e45810904040403071250b40c18040728040c8500b03c81d5840c0c0d070155913804140c41c503081040030480c04120f40748501200203000700c0d11f078960401080392000c2d29233814507202129080c080e001204201b0701141803 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 67993114 1250 67991864 67991873
    0xc03100902120109090c2c010503060906040f0f0f0b0106080745030f03080106020c0105040608070c051605040608010e06040f08120106050405011101020306010e010f030617030a020712 81
    0x82c0760640e5214003010514070a1414a02c000c0b41094002e12035400760300020b91600418901580340ca075030b21241c80e50160380c3e10400c054030b40303800711100c010b0798008800150025a5110303138207428030b2042c1d82c00d084e03101d1551905c8021a8220300c3c111100c0c108100180301c66034004c0c22803a8480c40915040008580b4a550501040030802803021408081d400d100052440c2000410902e04401003400c00169241480c26034488a50b01c00d40110f41070400114090f4404071b22804103040c1a140d46250600d081d4040390b034548010410000c10985005034000a0310510030104c030070165441c00d0789000e040804001c111440303580115400e80c5868103116600c04045041d56001e80c205403940c0d00c030445800e1004640c0315080c07031511190010000403681c01e8102c03010740107076402aa03660600705d04d000d01d11400c030300c02030f5959400b003004080303024017075845080d00000042c1a4078000c589695a0300041d040f6802d68000100d07150004141e015440f80d0400044004044548840c03103104d00301c2d00d8 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 67994364 1250 67993114 67993147
    0x222270c17190e0709050105151806040503010c08010510050405010212090a181b03050114041a031911010503040c18020403120f1409061204020a030b0c03100902 71
    0x200c00449504400065030b0140c9002c403042c003088290700705012012520b42025242c812a01620000c00c2c901000820700e410840b10000c4640303408641c081c03030011041082d01d645202c0351021948118104804035040d2428020040ea400c115111400954104000c004c01c680ca1a0399000400a0601081000e41c0e070000e42411024619400940c2d140d030b42c90040351002519400c0701d03604010349101c0940301400c0350f202d441c0160302c0c0100c50442299440040301503a400b849508002e620400d140d0141d85440e62004a0103000211483e100c9480600401c0c00c00d01c04081240340d04440d40c000d10144980320b1041505860b09181c410700e076103000d507918003640301c0a00521861100441c000f080804080c1d0456003e0b40c2c00202000e550b0040340b80090260713800e1100e4000064505050400c0c60701e42006031200010001e040e00d0500010304582124032100900c1a61b01120400e000008034024491440c0104000680310b0795900e06180442d850945590000e00304a10400580c0ca80d4442c010 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 67995614 1250 67994364 67994387
    0x506041d0c06070606050a12031407020d03080a0b090907080606090c0313050a05031308010e070e0a0c1b05010209010f050c0d0507050a0b0a0203010f050103020705060105040222270c 80
    0xb0340075503da00c032078104a002010f00c4e0700510340044c110540400c1026078089890940c40c466070b81d00e202d07041510140161800742c981e0007034100042d2440800001c1c06861011b0b030100448000050000100d00024030461084d910a2040d42140c50b0500c0240e106015040d800001030b02c8105460a203960b0714200c6120007011590207010040c0d800701000010300c107007107015402c101281c1d107411050850b0700541410b4484c1203c15842d200e80c00d0b00b43e41001c0746100c00c580d0140e0f05480c40e655030600d184040c02044019004022054030a4121449040e25054645008400050312540311000141004440d0030054061010070321522003107401c000b07410b4025141e41d1078566254105450000d240c050034802c01421010008100300581c01698040c2d0304a903526191148800c0da0381c80150224418038001620030f422090060045040c160001d000f500350340f0000300c075409941c61074407882100c03540050f0003000b44800101c0603184c104001454054280b801044044c044120281004d01d202 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 67996864 1250 67995614 67995619
    0x604090201020717030a030606020a0201091505070c0f14090103050615010e120f0c0415090b0a051507150e0d0e062109060c030606040b0d0612060506041d0c 69
    0x4044240031a4800d00c40c1c100180403800c50a084c43d288045807513140d400c008011070000b4980000003a00a20028400040341e40684075040054200f0000040c4445c040c4802802e00c0420488003000400450000c1e0050500f803c000408504000040c200a01079554062140a401005201140c0085006908005800c003070300f448001043c01600c1c06046807040030b51241034105040f0030300743c010905c80c080152520660b030381021000c0030041200c3c11074401403042103d407401403104a22640c88043c0301000100340c010b00690703640000300001c10420140711a01c80101d21501081444241da0403800c280040078000149072483c080d0b62413003003694810821a40c1e0b03114007030300e48070034048803040b101f0344840070a44c058804100c0f60602c0c0c1503601c4c035464428040020400041c520580c3c1c040e0400815062400e1314002e15042690401444680019030ba1100000d0f29100361500301d000d10b208002c042001d141c42c0301004126224000c501e0a50350b100742040e44201c0010a0080780308404 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 67998114 1250 67996864 67996871
    0x30f08060d0b01030609050616091e0b030415050a0c0c06020702010306050303031026060601050705010e0d082509180b09040f020a14090a020703020102120711070b0f030604 76
    0x80500150001e45041d101501580e10b080001c014820160031210242e4044da007215800e850b0302580200180c00c05a80c200003940303005061080180500c0b030b018000f000700081cae902194982e00e00d1306040c1e20030345080711200b403000b40018251800b4010f40e648207030311502c1046100204d010140403444150310040c03007603600040c0c4c5001c40e8001e51140307016050240031070382c0f41d01c0d2400245028290301d00a08058078001c051600000c40c200c0140820024008042d1009850300c40064031b154204610844503075485245001c09080c00300302c1100c84003034980c0c81035040c0c20a6411202038140c1d86070b41d62506115000039039540b50308480c110044a40400c208a00304400c5032802004040c0900410b902c40c088401344814040d011003044942c5000b11204403080e542c481c2808040c000724481c180c1c00c010baa40008851002550203032680318041d000140c907100c02900720800c0c17503200f1560400825103c1442c034110074402c01680000d4011590218a410718103420101c0c140001450b1a110360789 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 67999364 1250 67998114 67998121
    0x606030703020c0f01091209120f0201110f0d0c0201080f090d0e04090204021617071a070e120703030305100806150105040f0906140a050d11030705060403030503010f060c030f08 78
    0x9003000102050382c062402004682e1007490305c5001c02019050407070002d00f000c100031032450927a000b50304036184d02c03140315400c40781c07d54015590a07076030280c07010b284d0090818081240e0018001154032640650700d00c2c00c42491440003601c44500a030031039042d0310381e140803c103e00b2000101a100000c290070708804600c2e0b40c2002a0142011001c000e41043c0081030000444c00c414401d0385a4501c1007114502412490640070598020803002401c0b114007440d400741c40303100c04c104031900920315180803000100c031000842c0c1c55904041308652541e014100800506506106507030304141821b140e20b8407145403405965039410301502c1041c1c0129180e000301032617030184c4225030041c002056807c000d00d40c2d07151624002c1407188280c2000544104122007a40740c200d01e05425100b00801070080c0040c2c0361144485030306c0601089805100b80782002c1101c0d0b0343c180c0908001c500c02e0f6141a0b6940c100307840d980701c03e003869114030240040003002c080001e820800e102c400980c1c0c0d18005400c0c1d42c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 68000614 1250 67999364 67999387
    0xb0702010210051005101205070e01050d020703120e0a03110303150f0310050705041a0f0409090c0317130905010e01060c0303021c020d0e0c01050f0d060503060702061806060603070302 81
    0xc4140d841540c1c0512080c6c46000d610790001c003040100b040603101040039a82e44a0240c3c1d01d5819072071124002401003115054484599000c1c258190103490440030b03800c0484030300c0d02101c1c004512210554007081000741010303480390008040c0d0840902440c218203280101e40d04224005038854851441501c4030141074604104000300260003840601150808442c00b51096100b402005007001c2d001e04014640c610540840710540401944980b46c070f80740c14141c200a0211b01d00481e0035080d0b284000000c00d00750b4001920b80300038081550f41d02c00d6480302c03424510340560b108101d010300b844010080160406903450444095040041c1d800c005468201d009200d07600e0551164807800526020b81580707070b03001c0d201050300715508104510364105480d44d1800405009400179070100180e81c0d03280c0800006d4100182500f20201d00c1d00d0316440082d0a00d901250b042d40107a1002c410040941000800c0c1c180c4204110042c0420f8207009002c942d02e884024000c8080c0b58002654001c8403 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 68001864 1250 68000614 68000641
    0x60510031802100c150903050d0513152f0a050c1603030206060a0e090a02010516050a1104060605030403050a08060a080a12020606060c07140607020a080105100b070201021005 77
    0x10354001c001d0800c11107010f8020f030401c146142c0903252048020300030000d1141d1441820503141e0192241d905207031014a1001c0500302c020300c16507035528007201c0c450010301030211105940341083c2001c12219683e10408020280c0d0107028441303104c2c4040e000100445520450314174280614050795a00070014800b45031450300030440034000e4018400205142d80450032074064102180c4540c0e2059403160005500b0400340c079540b031290051050f00d4010740c000c000511b0000d241c02501076420a15072221420b0041080e420f03108400383c0e00c0380e181d0a03c2c003845514050200b0341011411800c00d500c00925030700a6003495418025a0800b00744103030303941c12114005105080c22103c5103e41460401030701c1c4c100601180140c0b0442003c03070f04600d00081600c0c00c1d0032070300004001c0545000301c2611254107183d44290411002c000000140c0c4a801642001c0c254030030000c102400c0c00d408041040c00b40d68454810300f8014002d450050b03901081d022172004129401086688800f003498401 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 68003114 1250 68001864 68001911
    0x20d09090b0411070309030b071115040231061a04060804080f0d090b07020601050310020d021209030403050705090c073306080111030108030f0a05070501150e06010306051003 77
    0x1810012584c0c0c41056800b180490681e88100d0540c21551070300750b810796583c200341000681d2a0442540384c426080c2601003140d000703000030300f4100c80c0c13400804100b000b10703140610403009025610000c07280b5805809a0b200410313211041c640c0b24034004640038864003403070280078108070361074000c01c0600402505440304000032180c0d141da1540900040740043c5049102204c0e0741e8100000036503058000700d40d00d4125400503016140e00c0d420030103d08000e6000004114207603509100318550640c2c40c2c8481445401c0b000000d540d102d082d4141986440803682c403882c03043c00d5107000c104031002201e00f51690385610452030a02500400c5244012201d01c07101425000c0c1c41e40182c004048143c0c000c102124402d0b0000c108101d861090070010344424040c05403103510403c40740c1c51180b11080204445541131400604060786561124207480783c2e01c0041078541443c3c0345c140a09408010540d0704280f09090030000a460a40442c448506484e04042450769a8054900713004140d24010203 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 68004364 1250 68003114 68003141
    0xc030206031005040b030601052809050412230706090206071704050a0605030108030f1e190e010201090507051201060512032113020918100b01080601020d09090b04 72
    0x1202d290844441d498501c03988901ca01c182c1c18440b00d44414100814030506840f0f010304020010841580207503004008002c1c114507079440741d580041c11004074403482d40158401c902481d0082e40c81c40001b00b4070442c0340424242d041d0f50807094480300801c8003c032844c03c0d90003503000c900c0000900002e04240a150710280c2854920f16401c441600b80800901c00e840c030489004020548030f410031903040c0002d005a036500d51080212800446070343c005010215414000c4001c05002e0f070f0000101508403502e0044140d00030998440480d40081400c0308001003032000f004200c80c69200c003075403607100384200e902481c008803032403a140f00b00390400c2006c0c1c18040c1c032301080b0040d00900d03160340f0741c49101c4060b00c84a505100076075000860300b0803030040440307070321046c0011099000c010078588090001104d540215216860130710060111003d0b072074426100150943d005400034001220050616045410118040d01c6a58210f202e0009076600c810000a0b000241c3e80810014071810349000c9 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 68005614 1250 68004364 68004367
    0x8090714011b061e0e0f030d0504020303130603020d0f0b0f210313030209100f03110d0f0809090105060405060f160602120106090f0509150409320601060206130c030206 74
    0x114100380540d0040e41e504c1c542c801c1080020740e07040382d07843e220000009041c540040120314125152500110380040c0014140c0c0d15001e6100d200c0c401208080c0d105202103500459210340b880f890b072055071003942014205202041c0090001200c102d400c03424907216000d0010603150b9181c064031104441c0e041c58044a540d10301e41001c0008086240c40200d101d0700f42d0f10001894034030740317134503170421500700d4130782000d80d142581e50740d0110581d40e800854001c00701c2c0381400007062918104000301c41c040d0b00c01c0d40c0c1c2ca19004040c45080342058005030300907201008200515105d903011a102001b510b0310903034a684213034203090034200d08054041c20907400400e03100d14814810010328101c41c0c242d12030805d16643c5080c0182c194410740b0400b60b21040500010385110540d0060103034580b13005200140c082901d40d01c80140c4286141541500ea0517403500f401c1c0c3c0d040600e000102043d50348010031b600c1d8505200291340d458005c2c100c90400400e40344031003c1080d54100341002d136030b000b08440d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 68006864 1250 68005614 68005631
    0xb03010606020a2306010303050c030903070609091d03030a090501140a0204060f020708030f0a020c0904060e190c050d05030c0105091614150a0509030709090308090714011b06 77
    0x2036a40f840c1020035107900180e08045030781018070a48a048a0040c540075040c9603185072400d88840c1c0081c880003840380010001c04c0c0304c40e907090021001510040c1c0300c1801250810406408660415944405070411002401400300e4000256944240183d4003c90804042e01d003183c0580001510084900c007407000384084c050403500600140c680ca50b0b00d514030204041c1040383e440d4420702c510700180d0001c20800341550383c2d40700140180c1032140103c823006000103000c07805c012070880c0e05403540d6554403405046030106001e0f080418103038000380481c030411a200c5803541041c03881031600ca4820820308204100040c0705480d80b400c0c1c0900200070500d40841c5940d120701c0da128000c50407950380c2101041171748a44a0503009008054445000e1030704442a2459590100d084c074003e0020500100f0280d40c0c1c104400d03405850181e4000c281d240035031030701501c1ca1401600460503500004024082c1e402041e1007460103610910700704c0701d02021880f800150300c0d41c06a020301240d003022402c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 68008114 1250 68006864 68006867
    0x1020706020901020105160806060a0509090403091e050105090402030a0908070b040201080709060807080c16050a020906040605090406021e03010801050f07021b04090c2103090815010611010b03010606 88
    0x34100b40c520030b0b0024400380c1d641600408541602940200100c0e049501003a09424508094030b0804d40c0c07400c0413440d114901c0001407154004503004c4000a0b0f9544050040c0c2c3e005140f030711180f040464080c481d2030301740b100180060113295041801a6804030014840c1351145e0403280c8005e801217413256460344241090800940f0031a001c0c0d020039102400304a0300303032042c0202001c42d0ba0682e200300003a00c2700081140c01d1040640b840001c80d10030b000c84003005100000305c0340c01902c5440140322000c0c0074418030040d154020401d40c4101c0c0307401020850341e1940c0c12201d501c541d121200598521000490b8a1040761492070400c1980000c00003103100403056200741c0c003600d030011080555a4414000700d940301d5500d500e821200c1811880c0c408582801c2d040380074040d00c05d0706c0180ca1191181e0090740340800144c50203014801c07401e224014540c100e400040905421405440c69110200302d4030b0b46c031a07040c8903070820881d02c40c846810a400c00c0d4000505180d0041c0217111881c4d64a00 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 68009364 1250 68008114 68008117
    0x50127050a0b1b06150f010c0b0a140a060b1606090602030c0c060912190c080c0c120106060c02090402011101050a0f0b090105030601030308180312010906090c0c110f030102070602 79
    0x6110350118000c0070001c1c3c4900000070b690703201d41072003100002d40041a0060140d15046a4499410300454504480c0020424001188580c40281002444544010f03105000340d1025200160b034901d010b0f410700c00071092100301c0303080e103820f05024284e00740941380210052007030b03440180070188080140710342c80c80c14000070941e0016600490380682c0b17030941c2c0ca5803180d5000300b801c14500020003414010000891110500c040e16041800e020645612030316072940c088803800100e900131481c0354145181c80c040f540000d0400c1e00003003100c6d40c28032002814020b602d1201070b2064283e540010116031280c84059000a100c2c002404a4200305284501500344a00c1a1100c1d6044c42e04a415034100448014102d800003001000d2a07441d6450507962107601900012640040f4220500c80e204108010b25010001e00c918000640c580180442280c00c06c0e04019081c50601d014401103aa0007000c840013590003420b00124249464001180300200d00d141d660994004125202400341d10750 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 68010614 1250 68009364 68009377
    0x30201090209010501210e010209041a18090a0b13020d0b07020c06070b0613090203060112051507020c1009050a03060b0f030706080a0b01200a05070b04050127050a0b 73
    0x291100c4103641c131540103583c000f203000b902a1070450210072224001c2c0792a04001c1141c00082d000529203910000860251402d00403500070b078000700b94240c462420840c0d811500d02942903080309142c14400c5005403110711980c005445525500040b0784100094480e900076240e0040000c142c4102501d80001004412203a031030160040c0c900b00200c0d42841002c4880d1150301c00400c0761940d6494041002034071020595509041e80c400c5201f005803410012903018046000c0211300d00c1101b484e05a00d095030410544030444881c13420710104503000501c0748800c0004540305e07e1400d241500840b6180a01e501455000d00480000824403241d5446482c4120b41a162240300c00b044d0824156580068424130000442c41000650046240d50003510040c40514029036030345c07840008201203100300c0d515500f00350400516202042000c11007440240040c80406007480d2410002911820b0445000f16055440c03007107452440d080c01c02c0104c0500f0700180383c11035030350311200e500d6403540101 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 68011864 1250 68010614 68010619
    0xe090607030e0c01020a02010810030206070515060105090901090902011707051e070c0b0708040b04060509120604021513080f03040302010f0804080702040f0b04290f090109050c0f070302010902 85
    0x40b00d51002c0c8003001c944081031403c181c005041c0960340d5401110054801800c07070a250114000c0800181d503448024800c83d80140010004c001551150a000c001c01401b4113043c00420000e0320040d40706d000307a460444807070100000700d101c03d500041c0c1e00f102801072041140c90619040040e1135070442c01401c09450859154000c500007400e400d02c1d588106100500f04480406040051064240003080d16510500e2054200707680c0b003040c01c4142c0c10941142e0081040481d0784186070a20024860400e0440c1c8018401c604054012602e04500309100d2030b014540014030828588518101c00000c0c14900115103140303d000190395101d07001400308900040b05105850780080c490000383d4001c0d608021480e2400d81d05030300704030090074084008803100351604082c2d4416911481014002020040207010072000c3d41d440c0fa5041c2801206a0321441d1110040e201c030751280c01086054031001e13070740014280c88510340f98005004d801d07807540c6010000078003102016410340210000311b10a = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 68013114 1250 68011864 68011871
    0x100507050c1902151b0106060e01080f040f060e030720120f07050d0606030b07030501030201300b030f0609150f070c02010f0909020a1805040506010f08040c0e09060703 74
    0xe8020034100b041c03040d402940c0300c007030310409015803070740d070802405015042005000e02c8101c1d14101400d4840701d034042404164004824151940c2220120f43c0c0310250032050700c110303e07195480c0b03501c03000095405000343d0790721401c00c10001020001c6a40e05504080350183ca1084082e0032010801e00d1550b03d030141240d2149101c03501c90000b54170400000100251443e5070030b041c1405003e9110070000c0e03031010703200c41c1e0020104040005441c042c00103668045a15815400054545102c551110a03036050b001410a04020341022101e10f045c0112070204d4007100140c0002c1c503014451801704028041c18090005202c4009140d000c142c011092000c210356801d1032a80102034110341c64400f1440070303045200158030800d407490034082d030b9080034540241c641c1c2c0d001003243c010444c000c0c045040c0c41120707980c00b406605140300400f01124207000d00d140420009140d8606020a001488810030226040140346403078000a099440ca803103da500d40006600e945000649049022038035 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 68014364 1250 68013114 68013133
    0xb180108010b271009050906090c0102070b0901050702120d0507050d020303060a0b0306010201110d1e020f09060f0d090602070303180c061202090a0f080706021902060a02100507050c 80
    0xc00b0003c0300e1030600352404a102640e41c2d6a03c080a22000410401c1281d20851020450701e4242c400d06000d1445100185401e281551416103403080031a085415940646010002003d01c0d0040300c0c0002820f107440c68441e101d6201003540301801c2882c0c00114003524031601515640800604030347e42c0102d0845411051000c010390f12031105888140d081455100184011a4500c00840d04900103100001d2416182a13503103d1507000000b00403600d50300d0301440604010010004980e210300c281d01186041450710081403540b00d4860464040e0201207418000d0700103202c160780031718000c0e1a060003249083d00c0c0840c02507000c4a0100c011a01e0241c0880c242d1100401039004582d015161090180c01c0c850180c51480c5400074076582c1c5902000300f55460b8070390040d0140104480040c05010508140c095401e160150708030900f19404000c030b40e081011001c1521003441d4040d41d07400c3c1c3c0c51189203030072405c0c941e018101300b400d1410642405003d0f54414010b00400f010704003a0b80c503510 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 68015614 1250 68014364 68014369
    0xd020f07021504050a0501051b010606080610020303100510180311090a050708011a0403050f0a291b2502040b030a02060702060a09031506060f0302040503030703120b180108010b 78
    0x441c05980c1c2c11030170164050203071354003800041c0881010b0221a0086c0c01d604e1000c0ba0a450060f0045e200080200003030218609106020117007041c1540041c2d8110700e013000c050030802c269480341a100b031160300ea2502d456800351812910300011901e0244d0f0854480c10802c0c120252030640b03178050030030b8100181e0000302500c1001c0c00b82d846680c40c5a0300342d00c0d004040783c0320420781e12541350f1010100300002c00030324100050b4003000c58807409040103100c10b04bc02e00d070000000e4a07486010344040c04658900018925050340510008010101c1c2d0a0704290440f290050174015038000444225007400c0a4410044482d0107208440030b109600301c00041c1515800e1400009400c400c0a0184070014501400603052494491502d298115500e80712014901d4001004001e4150b4940b401d11041c0d5100c00302e040401c565050079840c0506d000c2c0407030340d01c0c42061005010404580b0340251160250f42058152980050052580c200c4030070207075400b43c400b0b00c0350800c2503180002c804d0090 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 68016864 1250 68015614 68015617
    0x80105010903030c020f06130314010b0406030b07141309020c0c120a031b02030d080924011223161401080f1b03040807050f0a080301060e01050d020f070215 69
    0x300d9150740d072940341c004d0540c20f216803d10a40480c0d6401901402155200810b0505020046015000e1000149140d03156142140c1c011780c03a0501413404c0c28400d00100c0c1e22200d0302604643e99192101c7c07040103c5825443c0340c003a02402c4460100a0800000e400c64a03401800c00c00c54144140c84006003030300208010410355150711000c9412440141e00402e0052440700380d0500700d032907540d401440540c0000d0401000c004608040f82011040c403d07540301c01c21005003035240203907400c10141100c451007842c0050510805070f8442c1c05030b4680c0c3c100500b6048401880c03000310f0032211200864040c080d1290b0f04240300c2c81030412440c000243d0000130692010030700d036060715001615180c1d019424021000109000300c1122480c0282400e0b40c55500290700c10750041e000b00361182d22614043c2d00f0701408005040341a805102c07a0004509404200c0303046071943c0c2401c1902181749001a03659001d43e18a02c081c092000c0f80c41c41e102c0303002c82c2c01010114400c480140c03003000d0040c8107210300d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 68018114 1250 68016864 68016869
    0x30106060e010c06090b0106030213080c010e04050a1805070611060c0301150215010f0321081807050904150b0102031923071406070f05121e0c03070801050109 70
    0x9418440c1c10703849540100c880211060080d43d000c2407611803600c030241c3c8040282c3c4403000203540041e504403134155030103174140035106000191890140c0c440000b44440020800144500e030f0754004988840120351000e80e141c2d0600e003440b84100748a0034401c0d2140510f20400001c0346080b92442e01201000c518070748144003214820b404c690030228122400242c2c000c1c00c3c019840390700040700101000c050030a0081c1088500307020701c41d040d0303d448010507031525a01004030120307145000d40c1b0340e0400002540f08004180628400c0441c040852805046a101030f400c82c0c4940244010711000ea411000103030010101401064600001241d07030b44544000700308211421080c0c82441c9103d00900d054110385100324024407004020348010b26801080c0c11a51030309090001f145662080c00500c0d80b040b0541004e0910340141da001030034601c907900d4000843d6458000054500085604c44006032100c5d00180100e80303804400c60009a0068070700e1004111070308000a0650f22511085d0103 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 68019364 1250 68018114 68018117
    0x30c031504080a0201021b0f1006140409020a0b04260a03020706080702100203010b07020f091902130e04030801091a0a090e01060503010e100b0906060f030405030d0204150e03010606 80
    0xe507226224142c0c141c004400c60011035400300205400e2a1144511804044c41000601401e8081e20000c1c4c0c80c007a0100b404000307650510404128003842200d01e24500d0038165000f04110760903100040802011350080d008060020402103005c1038a400c0d0041c0c142c80807107442120800740001d84e681c0d481c1a040090069102030300a118080c0708204858214410380119208088804400400c1e42c10980020004010120b0742c1c03015850005c000f581c12001c00d81c0c0ca01c2042c288081c19007902c0d4603010421071041d400154180007943c2110141e03004114088003140903040c42d10b0001c02446c005c1c80b4110364103041030f0750410f00031010062441c038204010226038540e4602200e01c0083c2c601190155059541c0d8407001415032028000d01d07003816150b07809010703541040c1c013218003100e080c0c90095005031018020452152602c07800c0790418140080e1341c6440e40d90354a81035243d40700d100007c0040900102d80001c19040b1103108200404880c2c480c03100711000001854205c0356603220310300 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 68020614 1250 68019364 68019403
    0x1030f0e0a170c06010b07030201150810091104050f010e01090c1209031b0804090c032327010914150402010e0307030605100602060108030f0d020f070f030c02030c03 73
    0x4000344088002030b2501d102c100c2c0c09400c040100b20203504100c0260f00c81760b074139900002c0d034108059080c4281f410448186e0b1510700031508051510355a0003420524201d0107a66501d4107052102c40e860b1305140c004002c1041c40185464000c1c0c6003010001c0c454103064452850010402c18264000d801500c3c009a680c810f16000c043d89000241c90310a03420740a00103c0c11505000c40c2014400c0c1030710b54081d9560f96926440c008903201155201e0500008042c41d02c18000d00340488110340540039001400c031140a03880345101c044076140c000d50704a08111481001c500000c80c10742042185030300600701c0d10072800c1c2241e02c0c1c0f0f03110300d041d0f00350941c1c0710700d0440040d005601601d11844100b40140850b04200e84035030300c04003103403003d6800840c0d41c405032030200700300c80d0f04000d0940507200c0e21001d1801e050354100512268010b0b01102c030f82098020412101e00501c0f03400360f4132102d4001d1100c1e2217002907070a000d0201013490342c05a02a026842c0e103042a41000942c0030001800e100402 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 68021864 1250 68020614 68020633
    0x190612170a0e040b060c0123100b042d080114010b030112060c02030c0102130503070501020304080307110301111801170c180312040807080d020105041a041103070b040501030f0e 78
    0x210084c0a076650990340202e041c170140c00304200c2445102c0d1314030142050f240a01c4003003048130110392001410328007600d10058061248500c401c040d0f42c1200c1007202c904030062036442c0c83c4000002c09600c01c500740c1c00c21000010342c0c560150801d00301240d40d005018682d90f01c1c1c460a0003d880b090041030444585154200000b41c0ea5601580350040303684180c138284801803490ba0700b641c1c00100c103066456441c00003440300d854240040c0001300b0003400118038052524403035903201e02a0b82c901520155500900340c0180e02e00790880d104030301152006554800740c42c01c201c01285094805a0700013021600b62500007150403040501503000b6250203410302085444080440000b048e100f83c040c081e444035001c45001e818041c20181c0400d5008e4142181007802c2d00340360107030805500f000c682c103000501c40030400318500400d050351884800c08143c0c2d600e08100158100c503403005905407281040c00901c9040e03e8000e00b080c0e8800343e0b4140116a200d01072503094070809111500c940c0c106c00340c1e4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 68023114 1250 68021864 68021869
    0x50a05010509040905010c030204030c21030f02010b0901060903060506010c0201050d02070f0804030c05120a0c0e06011824030921140301080105011805070e09190612170a0e 76
    0xa4102c1c06802040131508403130b99600d45003900d51146c081e401080d0081014001c0243e04c620502c040c1031204041c10400301c80c400401e050140d034080150600000c480c098003424402e4221551480303029280303800d1542d450074000c11822441c402680c0484c03031301c8049445503215103848005590142e41d01810711f07400b500c18400035031040c0c1c01180c0311400c411200001400790000307440254025412060142d00c0c14061040002800305181d0654025113a84800101c50800b80e1068440041079101c03241d030390b0401a1841c80c15192680609841280c00250b00980150304905071061081010315681f22440264156a500d00c8001c0c41030711481c440030b01d419142c4001c00d24036030440c5058402d100070104926450340c03003030f0010389607651544014011400004008036044c40006030820041c40c10403001004105421540c521400110020421224081402c2106a01c100d07400f041342ca82d80d144611651002c966049400c11088456003181610240640311010001c0d00c8102092035030004 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 68024364 1250 68023114 68023117
    0x51009020c0c040603060603020111070b041401300b010507020d15020f1b010510030209070804111c0c06052a0a0b07050d050a0b010c020f04020409050403090e010b04050a050105 78
    0x11520320724400c229250059503290b0164000450241100042c0e06056000040007920010000081da80c003082040004c40500c00840f02115448410005400900340c0100c90021801c400b0340310441da504100d1420720145103000c1a8501c00701020080e0b03204030801562280941400658046070003268180460502c4a02c024040b60800d401441d020200c00d1010998015000001c0012000f06c2440310059091050f503421050a00105100a113994005860315600905000800900c0e4000c01c00300004130903204001070000f044683d45a40c440481030145900030b10698004540f2600040e01902802c12601c0195585070a04140303003101298501400b981c1c45500715a1003800708600100d242c0010203405010103079281a0394000f045a480191203000d084000d203149465442c3c8072980c3c000008417181641900c001207440b404400040080c01180c5c4034210700b6051500b00000c25030f004d1810010317220480965491030340c94801009560041e03009854016190810901c060b42c0140e0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 68025614 1250 68024364 68024377
    0xc04050406090203031201090501120807080702040b040533010c1b0302090a02040e0601090e06011b080a09030512041a0304060f06090e010b01080910090507030503030f06011205100902 81
    0x41c008110340c801e5501280c69903108942400400345a40b0042c4003041490040500514203110456550101501d440c2610300c150b000c010010400051100c0c11511b4580244504010040040282d483d0505e40b1011890080c0d154258003001e0a0000603488482d24940740743d68410381d17a022100b8055511404510f0a8a90029940b41204c0001005a85110f04688141300e41c443c0541c899127003103e068411000500101c1c1484481d0105200b500c0201e43e04560002c0240b80016004102d0060703101c040c1d01038031016002084c0000d0340e02c2c00580022101040328400c000300d440d051314654401d80d55002d980070302c8104804035800000c040ca000006980c20a0040f440001d00c03a009d4200c0327004039441540035464158407418020b084070020300c624110000f00303083c07054140c608803150a0f2100c1c103a0560140c590354403c040c200740002000000090f540c031100712a600d0034a810b82c010405401c80700c280c000b0302940303081e0203403000900410b4001c180ca83c0d08555071170f060405910107500141c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 68026864 1250 68025614 68025623
    0x5060607060f02181c03140f04141c0512030403031d0f0d11030915040b07030504050a0f0e060f010e0d150e06060607120509060318010b0906030c040504 67
    0x51250300085002441419840540ca082c0140d969480081d035540f48400107003041c0c400c012070f1800031103102241081c0e850702585481d0081030103810000c0305005004e0400383c0c1c3d14141010a0110350001c641042020b20f1200b1a245010800c182070880d554402c9600001c01d5500f0040c2e000046490b1940507540040c480d0902140d83c944011401800e42c95241002c02d541e845100e100f4000c1005000d08040c1c0f0055180000701480141a40f81c0c3c0c038440c91500a004d1b0b100c51000342d044406450030741700074051980302e0580d10ba0660030300800a400600455100c1d01c04180e000400150b0f08200c60100d48502c92030342c201d69110410010305241028500741030110912200c101650766003007400f1014422801940c80058000d40d1600b110400540c02902e0b07400042803160710b60360170b429900d40301e43c0f1502c107041c1c800042c20b040b6179034065445046d4009401005200e0b07003550340780c003040740c2c805c0c1c04008004418009081101071001901c1c9290160020b008400050030540c00c8142c0c4107009 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 68028114 1250 68026864 68026867
    0x7060f06050d060902240702011b051c08010603090c09050711010608030c010e0f0705060a020f0d0302030a0b09010b09010309050703152a0807030e150106020c011205040c09050606 79
    0x4800c007240000d101d42d60100c0d00240d881e1509000c51501c5050514400709040c3c0b424040702c010404800309228090010b4180119890006614400f0b103140300f43c4903610100343c445044c3c0f4000140a4000c648d24400c0210f4209800456090310a100348003180703070800e07101d00506180100c034074000c042c003500308820822031824060b0441c3c024000c00c0014802a40215a522400c0ca020703400c40d1001c3c0340c1420f154110000440074103400080d21410b50300100e800c01d660381c406100503468860190f0801a260042070360b406960b54160b406540702c0c070109001400696811420404420b409019003840c5180074030148005512950200303024902c14405c446d1703895107035203c0300881e00c001c402514000e9100c1c481d01282003400c002640c83d54007444580f0f800d40030050400307461140020045410140e0310315a801045608118904041c420703010036848a586450000391103040e00a400c07804150080c90440b00a2400d103c0d80e48601d42250700c0c0d40041c2d040c4103040003c0c1030b01800d41540b0810 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 68029364 1250 68028114 68028119
    0x50703110418050d140f2a0604050601030b0a02120a051801021303020a150c060b010e1206070207060207080c040f020903060a0204050312040b030a050709080a0501020403061a0607060f06 82
    0xc0c0c1442c00d18580150b0044c285000e03c0f60000b45009035585107190801014481c5e408100b00200035210502c441000180400c900488010405004081721500b04d100301c40a01082c0308002c248981a00d00400840d03002f903075020031000591140c82013020410310f8900c00076051074407a600040d005076107ca40c494030082881e030f1090030782c1c102003000e01c80108034160070400c528021000308001c09401421004520080030081e1510340310107005400d00e41c030750b200700107580c0c41482042e603104401000900558541d400b13066a0f0401110401c0141c4180d81021507200d000040310b2017261460801084001c62541c01d00028094160340100c03a41c1c1c0a1002d441d0540e014800c2906c20b201c40b010042e1918500020185000000013011526260400c0107015034251070003103943c046852400400d0680300c14004940100031039201c1150340c02024a25400c02070107400600840c0d01481041c0300300202c400980748041e868954040d401441040140005a8180c001d2683e041003072100191003030703 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 68030614 1250 68029364 68029391
    0x9150e0910090c050a0b03090f0715050702060d050f060f040b0d02190e0924040b010501050c0f0d030e0709060803040519050402041d0a050408030c0c010906020a031401120507031104 80
    0x816500041e0142c0008810001301c42c00030041029010310040081607298500304902f044501c0100e945d07020004006008015500c2d0042182d0b0f200001c40c00405c21464540c541c2c110106068404901c030300082d18005420345040c1c0107003c40080c00030544214a101c641c20480d5144d1aa01c8040003440741e1003000503020320402c000d511500120020344604510ba0780205840840c0410500100c1c0d030030740600000c03074902084d03241520340c02c1c20030698600c02c20f1240e6140c0308110100c6401481808003100d034555058102540701022041104c04894456410000b5244203000f1042568014403040100345407000a14130000d20250301d0450407910340011500342d034426001035170381b62558214213041300030b42d45200d035100c0f05100b002c205a06003580c581485d888041c00311990b103030001c61208101d490a5111051050f4000001c668a0f5400440075015040381c400c1010540140381c00081d4014002612040c800e46c00400f81101c1811035031401e054401c98040190826640c0b0240450b01 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 68031864 1250 68030614 68030629
    0x6060602010b1003110f0304030c140c040e0c0f010c1e03081801022a01060902040905010f050319062d0e01050109020f070204050604021309150e0910090c05 69
    0x10205580003142100c000b0041c400f044944070020000c141c41e00600341c0d10301710134409855000324800010360703030790311107040480e8079521300d03000a80341d80c01c20451096840400121714012020940703040c40b040f1901c008141c3c40d9280200c1003600005484007120280d0703c110640b55890340704807021810310301044800c0748014041901107000c5010315081c80300303181c009414454072440d420b00035440c0050708020900c003012501880207864a60100384680001e00f03401031030260032451811903c0d599503100b03010240c5004c1c4600d040d00410140301003480d040c0420002d0300390000740d013141000012503882c540140300407040310702200b400412001d0f4103038161042c0091114030f407101240c21840c05910380e003110b806a109840542c810845d03c6001070401d001d036410941c04030340c0010a582c075440400d0191084103031812540c80d0f894008a61060190f00000100c4003000c88251420f4075190340c1c40210106403402956540b007a091461008100d800c00c006c20b512a44403100a60341e60f01c0800c084 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 68033114 1250 68031864 68031869
    0xa030e03030c07020102060a0603021e060408010c0206040618020303030f040c030f0809031506011407050f011118060405060412050705040203090a031107050a17070b0d0603050c0f090712090606 85
    0x402d00b00052403020741d80e04003c0700341c100040c241e0400c00c2a285600044444406030011611600790b20303030455041d500d800c00d42e4010b000c880d00901680700d0100c4002d440b660204c80842d0354070701d094001c80c25280d12a01c1802c449901400562443d1039400c880d886444000740101c80d0b00185134030200008aa0007036021000d4411043c545e122611042010308011803512090030303001201c000c100141c1e0348100d001501807900700c41c05548030410704040382000c1655207091055070805403a03240e00c5035a1b5000f0030081001610620015580d001000800d20491081661081c400e01062000a0b4100c00e03e61560307100f81c0c101e82c003160341c3e0b5001c6030580c2c008613541880c541140044006064000d081c0c446103c10641c0034010b41c0742803600080441610b401b902152500103035040c15120410810303400070b003001c8080ca036101c83c02c0030481005488680002ca50900482d42c0510003030400200090407188024010001c03503a41e10002c54002d401d088405a07101e880d6012040070402c1807050501 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 68034364 1250 68033114 68033131
    0xe0a0608100b0414190b060409060305150901050702030f0903030904060b0c0f0109081b16240f0210020f040b030c03150105070f020906130c020609070f0608010302060a030e0303 78
    0x900c0b10b01442003004455410704008600c1c04401d0401c14181c40745556003405052911001030000140c102041c19801583c02080605141c0980402400b50014414200308548009644140d1300c0e40384480c00c1e10401e58942001d64400d1181200500d41c0102402910394080d0072a4289000800052300740c4050b94400e40c501da10000e030904074507505002002024010340000d000c6040b21340d54440d810b110b9540b040194942c03c041c6440a12400c0c8100a071800c1035014100d0300513200c241d04410b1161000c1062280c10203401528181802120007600138407082d000707000360100940050001c0e612003510700c40c0c110410040400c00001d003001450081112500450302d0303141040e41c03505415129400181400024172030f0380d0000e500201031a1141c1d905a030b070752005443c0c007c041840303c1a0103582079100d0f807e00c1d81c084036490303001a0092069241e141100c0d040c603078070701d500312442d07103a80905400a000000180090708020006050b044d50740d00d0001921540e2100550450304161b806e0f18 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 68035614 1250 68034364 68034371
    0x30a05060f010302070203070b07060605031b010201051b12100f031a0a02030606040306020c12030c22050612060f060c0304060f17040b0a110a02071d100e0a060810 72
    0x480ca0500640300d412401c02820704515204a6400103a0b54000314414032078544000150681000705070f400501c0100009011210018859a02c4900c030100030320604d070040d840c05001030794902001240410a8116840891800500703000e03e1307108000083c0011820828840c0000d002c5200a2520700191701441440c050004400a03030040203001402c45101940144240980c2d03070340c0d19040314100c6c0d40c480302c0140c0c0c4800c568003040c100600655404807540010080004400f5040024003262690505603000c40400440d50304800c0c204d40900d0b500210240001d00e50303481c001031480d03045080100502c40302280d0000058003548036083c101010740002c1402c00c201604042414003440d03160803c425407405215022103400402040503210401801c0441c804850b00d50050b030604002e003040036620311001401a5503240740740b0404c1001280b0002030519121447e075042c0c0500300c013a0303130007040b030b454011600060407014080700d900399075841c80010f80f6101000383da020000d1041020 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 68036864 1250 68035614 68035621
    0x21b0d0513080d0e060c1903110d020601060e04090c031211070f03031422030b01050f04020c0c2106090114091501060f090819051212070e01030e0102030a05 69
    0x10880c0a0305688070000580c0880320800366560001401c4450203c1a129544c54181b40300350a0301d00000084a40c4e91042030003180307403d1560182611111310080403c075202a014941c3c1240c0d9800244074940026000410117134441c9016001001900e000308a20080c071a1030341c6032140d5008000c0015008907903071028428403e6014001c4070010000e03070a02004443c615140035002d40b401d06170305004d8040c005a4980d0203c4008406202440504a08100c088d22482d1071804441d0a01441e48203008102415080345094001c0710946500980945115600c1405024600c90800c0d61680c045502504624070b006082003141e10550640001041710014259103c0c031a2f0030140c074200541c0c000c0c2c51013072001400a111181110100d240a80321305000840c221074886581d04007032a6801400700c0fa0010300001d076034100d031880c061029544c1c4082580c42d0030016100c2d010403400c01852000020305410f00407003003c100c10406040c08540b00e555010a01d003260320445c0d0203524560303202c060 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 68038114 1250 68036864 68036887
    0x21209010b10080106080403031b110c0303040b1e07140a031706100e0a0911030907050f13020c030712020604110103060f0509060a050301090807060f050402060d021b0d05 75
    0x880c14140c005840c2c811103607050705402841d82c2014080c080500c503841d004030741014402d41c003030708516110a00414010641e010010b0449150801d845094843d00301d5042c2d480c9004401c41e011100c0c03004a1900d84a2040b0007094020018034240b52880e07800e0045002050700781020441c03010160015040204aa02e0080c2c80d5800c0e001124001c000428200850750326124018900a00300c4d0512400301640c14000455141c1c01d41c00c5030020b40e083c13142408a00301c528026501178562103041e80d458507119000d009a034600c001940381d11040030100d54040e00041e9006040014100068929040c21600c940c140a0210160700e00164012400c200a0080f03070303182c4c41a504400d00e02441032030703c1d01c1288103a1910350b00403144503a008201085072992066510401403070040c009212400a41c04c0950083e0800704007550001d044c0000700c80c1f86e10861081a110307581c0204030604141940103160001e405c50740d8000000c0044200c00715144404008040c1581c0c3d603980c0311642c1d0002d4149 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 68039364 1250 68038114 68038121
    0x705070e0a0f02120604050406091205070b13020a051504090915140702033103032003070209040330050a1103060d11060d0c0503010302040b010206070c0305090303090402120901 78
    0x10140c0746144144114000343c41c603030444c0c0303420030411900401c2c3d94030341d401e100000301526440103209280d80c004026440e40c024002d000114012840700c0350300d075505010320011007444040250b000c46001414442850048075045c11003082c1d50f003450409868190140171102e6400e810b817084d4178003580b0401c3d855550300034105500c1ca0541098180e003001c45001c0d5a81c0100040303941c65602003a440303031801890303c180c060364044010481010b0b56032800e02419080f1021800110703100810711100703820a0010860703150581c040c01015060b03072107440894085014052040b0100c1161380c0c80c48940003052101c3c9111410b001d40001c5a06008440b0411039000208559011405108104843c4d44020084141d141c019031240138415040700016050300c280340e080e0340d2262030903403000407981c4d10901542c16a4400e507003c006031208034006a13980c1a044416034001034000c400280024810405850f0508004e81103d050001a0700028180d81003104400300c2e2002980820840070403d00 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 68040614 1250 68039364 68039381
    0x90a1209171c0c0b0f0601021203150301051012030f110102210109090c0302040b0402130602060402010e01030e19230c091005010203030a050705092206080706021009080705070e0a 79
    0x410320034103003c6903140160810000c100000300e0f1409000110540d00a0080c04c5c068048800000c1c0c0e28a0090400000031541a020500a40c40d10002510f10381c51040c1d08029620030b81980400380420b684c00b04c07110b98a0380000c50403c005450441c55144090000d014140059034540c80900340e41c01a420000b80142d00c018684c03030078080003002040045000d9015280c040c0c8002c034500000d00c012901a00c5013142c00b03088415034942c00183c00b0340c007160450189200b680d03905074941c3c10740011802c4c0c4800201c00c50b042d421000035000d0894214a4804040d44501e141c042c0481b070107a6914490244c0021400d0b090700402c156000c640340c0400a5540f1488001c07844100d43c0c10000002c0d540d000041410300029079650100e40302900400613a543c00500a1010300c000f5864461411002d900201110101e400d007600030503001000f003088030546100342e0060010f1005101c202015025900c4c00b030b1911181004030780b012031400e2000b13001801500200d4911801c00c46001310442d0f4005 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 68041864 1250 68040614 68040617
    0x10303080f0906070e010318080301030507030b0f06010906030c0c020307060504060e120606060a0903050601120302010e0601080606061606020307050a14040b1806120f060a0905090a1209171c 84
    0x2104101141e85c11540380d0303504281c00c2c070740050704c0016400741940c00f640640340504801804030002042040c000fa04a080d03d00c62440704405480e00f40170055144d005030f80301c83c04034100e0720040c03242e03600c0303a800164450413500d04050500710940101c3c0c2406411b0700008002000018207001541d040001448000b105885046c003251b004020a900d512025102c5403144100203400305503a8131a001d00f50180d40c200d0180c40702c1d940d48002440600d4440c10045015508041070084400c0012401c0e80c1210141000f500c09030b07a94104200155000c40c040d105204240c1140801040861015622440c0142ca07039503038904180e84007404e10480621110046141004144403500680041d606080c1c1030803610380c5982072510015003a8000c3c0c0904040f88444841004403001503c1c0d401805503501307403240c00050380c541065900b036031400c03204928540d2001c402e817000950080c8210190741c00a03d0306180f00f079100d41c82c03d0440c04003200803103240c0d8480c01c0d075060b051941080380600002103 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 68043114 1250 68041864 68041873
    0x172b05160216031b090c020312060108090a1113020706050105090c070507091104030f03121a03070e061f08010e0121030c02040f0f0905070b03071d01030b09010303080f09 75
    0x610418544092035000050000ca5415010000c03080030300130380c001900031000144490f141003640203660350080140d0441961546000c1405540520f0f0102c3c0954a020050f0804e503401d900d4401840040c2641190000050714005480d40303a1880501122403080c0d501007443d5260808000c101d0342c020f00b69030300d00e02c000c0065100040c000139003501290907d02003c980b0f8030503085045100c0c005e541c0040c2440c28010708400c101507100b075003042c01d0b490181c800c0203210158020640c001000c030011a40550244005003e45148254407941c055402043c0c0c24100c0003140079003440140409041c000701d01d00c040140714115038a680c1501400d0140000c8104900d440742422420094a00140c14000e10905000c00e549440d0055001440c2100003030210460340351408006042220003646c56008c2d00d280030034025002e108607401240d40d56202003040c0e41c010404405508407241c0c040c1816034600341c640d1151101d02c0e05ca4000e50007512100c0480c0b40c6a074048031001c60081640006401 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 68044364 1250 68043114 68043133
    0x605030c010206160e01020a02060406030f11090102120906090a06020312090a020f01050723030a11070608010302330702030d11030426010504240504172b051602 71
    0x20f050740340e030356094040c501003105c9203141005034284400a20044e41002000070041000c2e50550048414130760701080c10000f40001902501550058042c11801030700400350300000180d0550103480303801c41c010810b903d882d45010000746409020f90090b00903800119841103020320b102c84081d07102d00341e0000fa0006612550004000002c04050181070040104085050140702c00000750301c00721b1b065203550b4052415540e01d640341c128207040c2002941d400c440721902e0001042c52001c6400580700c800e8540d08607070802540300b1030034480407555002901c8c10301e40c108507481c0400d0b0070a0142d41803a41d4001c14010f00d410400c1494100d024083c0c100030a800c0901c0c00011501190000401c4061f0140b0408500040c007a0311608800d441d82000e051000341704c1c1c50f4031504a0204051555504840b40007407140648004a174080d10001094403900e600c200103100500604000012070111300c11865884800c511350b0306c46042c842540c0e08200450030b50101d032240104000c0c1e000900c1d8246 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 68045614 1250 68044364 68044381
    0x6090e07050f09040c050c01050702070f060903050c010302030603150a0213080d080718170309191a0f040905040f02040b0a12060209190b0a030c0306030f02010e13020d0605030c010206 81
    0x40340c3e49034503015640d10811018070314855000d40341002d42170300080c0102c0c00c0c084402555817030303103001d0000307014014840016010702070f206150440ba4040060302c2c0300b00040c00150000d410003850650180219806411764141040c0c0c07540c46000010070040c0c9a4000320403101102201c5d4021081030362040e102500b8150b000203140d90700c0660361411031111000c5040c0410001c00301c1d0f00011509143e6200100e80504c00301c0688040441594440072443c030b91820f076070001c3d80f2841003401001d1a031b80300004440101d801402140d4050010524040e640c2040c10102c40f4211400d07208a0841f81c2c440f4218034040c01041842c6000f207800001590034060584d00b0f00d811208000c02e0170b40d00195520711600d5070f1881001d0550540c8d2042c84039540c031012240395030720010400000915002100c05078901074070232141540d4100103d4070b6a03a1503a401901c0d50f400f010140f0f50702c41c8a84a549403034018070b000a02c000701000802050079480d0405051501c8082030645066400500820079402e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 68046864 1250 68045614 68045617
    0xe0406050406020c03070f0210030c0c0f0321020a11010203010f09050901061d04060605010201140f0a0f0c0302070c0503030406140d0905060f090f0a021f03060503010606090e07050f 80
    0x5800550010341030700e981c07404400034490064084030a00003c40e0640600101551108086000795414504d0f20143c55007203089401049807680403e03022409a40450782c1d080019000c02d2007070030174002040d02800c40c1c01d01d00103002c00c040e68242d00020b00c1c401107036216914401030320100c4003d50440d41810201c85600c0c08a0180400a9941d076001500d00102504050000c0580307000d50180ea242c2e8140902d001401240d00780d50b5203080400001c1c5651051260034402d901001c406151501c0e400112881101c001c0d0405000c42e446070031800d50764086200d60b40348001581c80043c0d9601803850620f401034260b51000c4c0c0302e6081070008010441c1c00410040e080075150803000c4d5940c0030052080001d112031140948148121010451000d455003599400303143c0f0001124002c0d40001c0d08076075904d92181000750071074a011880c40d5291310858002e40341e1186410080798094a07030700802d085035469031044c00041c1c1480010404410380b205d00e03d0b04501c0c50300e0821302d4542050a2007005 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 68048114 1250 68046864 68046871
    0x20612060f0d03090603020f1903061d0402030a080d0b1005090a171207020102070308030118050a0903210605030f0d080601020604170a090b07140c01020a0209060405040f12050a0e010302040e 84
    0x285500000d080c440c0c003030010229100f007411b04c0803d4191027240301e8010020400e034007401710300c20f10114168002c2081901882d1185a005009046021140d501c209850704446c0715507040c00e448400c803281a9440c011850103100040d580c141c3ca5014440810808521603404002118550780740c686980c0c00210703910b0034080c075042c42207503180440c1c80102d01d80455940080d1400c5004400400d45030003101c01d51804403c40c400911481d1154001c020450360456001000700c1e141d41c410030440f130a81c8200e841201501032002400c27554440200b401c1072404203640c82d154001c0e515500409401c41d00c241d4000d0b400707200401840c80c041d030324000e40c0c501000740c40e403003213a0100354444042c1c03040b960360000e48021f02d00d4644a000340d03d402c10051105208040e80c42c019019200001d5200240e4400040e40051500896031140010b0000a00000c1e10139104490000c2d411404681c1520700110200c03116903c1d240d07140f9407070345d00400d03a1400d21003c1f07041500400c81000200315401c40c4941 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 68049364 1250 68048114 68048117
    0x6041e0c0b1e030c030105040b09010605070b04060e01091401061502070314100204080a03080a0b0d020405040602070602070b1602060708010306050624090405060402070803040f0807020612060f0d030906 89
    0x540d803401406560803031007160051501044000100002e90b01e132040a141205d0040d070f4180700b010411010007441010134000e100000d14103202d2000824a02c41c07000750454080c4400180410010b0344203070960305008001d4407110f0340d1510036401001c0900c555001090340ca804852650b2143c01e009494040501c03003d4035400f50f06400400c0c0610a01040e0100003d542d0119034580c0c2d201c85880d2542089501640814510000a04a014140609440e00c10005e0008200038540d50030800101405442a542154203204480015603280f00404950f401100c981d00c1c00e16180e00c40484402c01d994046085411080500140c15003024603141541d80c0300c1d5001c1440c0e600c1901140c4291481c0ca212203401c3ca003403e058003008c10010041220b080c00f0354040c4190342d80e44080c44181c1c0300ba184020080f400420001c2d010070b52032510035901601c201039007803030042160001000e641101210051036444d103014095180741520002282c92000c0d2205004045140c80103406238820303100d500c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 68050614 1250 68049364 68049367
    0xe06030705190201020909280506030c0607030201021c051602010b010f0c02031f051b07050a030f02100f0f0b01021603020f0303090303040305011b05040e0c070204090807030206041e0c0b 82
    0x42c0650003901503500383c4030090403002151919180041540c0b0040b080001e0507042c845c8291070824180c0901d45c403412001e4001e00c8c1e46045007060050350750103081d050341155801c0c0220400c1031650f0345030345103d40585001003140e003030420445c100c00c401c80810f041968580035120301580d03002041a11105814107101d03241d24410b00100e4144000404102001d95240a032150103290592002c1d001d0310102200b2203d01952410300320071071007058000782c82a403106109000207845504400c3c0e52202501c15900c03604100083c16060380d40c1246616000c0351100200300d6084014403270565003003400d10003045a00f0110803804038110103800b001e8007802862070602c2c0305403401c100300c403040c11010341100e82c8c41e075980c1801d900800400c5035030b12680420b6580a02814400c9080c0d84c10b861704408003e195480c0c0582440807a40104000c0740c22a4490507913001181008000d0408640242c000e010325142614000301d564007400c400f80198094000c014010441e02c1403c201920802c02085 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 68051864 1250 68050614 68050657
    0x3060f031b150f072a081c0203130801141608150319060e0c06040e0a0c02070f090c02070e0c070b151c030207052205130c0609060e06030705 62
    0x1c185204280b4100e280d03500c000b82007000c01503543c0c095010520011041360840c520080040c03c002c0340741c8140c02e19640400050b0320b61080e08200e0003807083c7c0380d004a0f4648400c3c00c944151400e03842d4480900d40c0d55450f43c110b44808055941ca9100c010070001c9035104503624400380030245c0240503c440079100e040c030203407162810411900d411210070b01c0c02c1212038003842c0240140583c0301c524621070085207048041800c0030300076102560b810811042880e514940300400400f0811303c08000c42c0b04030b00c4001a042c00700d403104006010901000700b030391481d986000e03242554960004c4113154a0307e08100c00701c001780e810b94200c04d40c09141c2d000e10b9190781d100000c00340304d0f2800b50b9034094071030740c400c0c0392030304035070a190118510a80035902900d542e90104030242c103072600382e00101040d1505560032000251300c055803002d0000600540d81c0119203880302c2c1d118680e0883d402090900301d00303100c81500700280300d042031002c48a80340745107002d1000400700d00400c860301c0c0c08902040d0701c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 68053114 1250 68051864 68051899
    0x80c0a020a0b0a0f140402010e100201200301030b06030d0e1302090a0807051c020307060305190c0906020106081c08100b120a0e03130b130806090303060f031b 70
    0x1802081d42005420b0a282803070798200000f014100c1300d520300a07180441800f4464607a00300f00788141d40507107031662650201024000c0140301c2240450442d580c4150000801a0300c14000214900300500c9680703039811807074100310400000e00031500c2a802103151000003540580c442c65a0071007916109c10b14104409200d0280c00380d0400154000c44200001c00d48200028652040300d4080b0742e0780000140c680c070307260804245518080e41581044c8401d000d000c1c004e030401604944850031501030103d100c44600700f03c0c0d0b5001c000400040b0300000400400b0750902070000a00721450140544441c0c860300034662904060302c0f5010f000103c8000740040c60000143c20042070b038444071958403012826032000e0b511045803c40446446c2456041c1000c03000000e0728020340100248540b0541408800f00c203d80044150b4254031580c200017051507401030201c18090004240159102d003041000c016026030340c20b660501a500c2803240c05004584460305402920342a5104040c403c5503454 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 68054364 1250 68053114 68053123
    0x30f061d0105041e1e150303050d0213030b04050d0e030d08150d0f0510050c16031103090301150e0606030c041202011707020d1701081e0304030c0f030c0905010501080c0a02 76
    0x4c884209291145d40c1c400001481400b000305008000200076410258943c212101400d000c0540020b90601204c203010041c0e500401c8090516000c04c00c259603242d0718041c0d102d5044604641d6a0403090f0460b040f25041541010040030031405400c040c1203201c070040408000a100100403610109000706e144c8602e600590f00c6a0006104000e07031352139051842da00c60f5113554030000c00346058001110411181c0568510b0b2162481e00807030b00c40c00c0d84003181c3d8000d0404000c51940010450640e05a41c00d200b8494551450850862410f1600c10380341d000120003800507005110400c200416020740908980507100c00300810503a01d13285d800121490b440d00c540d8101041088410710110755000102400d0301c40c959502c50078111a455103240c8a003100f0311031650954881c480c43c884004c010304812075424862000c403824141d90781ca41c69032408407940801d020b031398484400d10a0061442000c0040c1060300070500030341d45890002022300600400d04d1001c1000401c10350310b060b10900 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 68055614 1250 68054364 68054411
    0xa03020a03050a050d020115090b030c090a090302010605030c01170c04080102030106050405190506030106050717070f1506060f0807050c07090b0a060c0c0e13050706030f061d010504 80
    0x30400c0a04940341d02d8a5641c0b202450000e079a148581d03410743d0441403050203402c120f074001c84840c02025103410700c1b00f000303401c0c18140c05505024690101c00162120500c0c0c9214010244010400701410708000c1d08440322502b0542c025000038a007e40a88d03044484201002e4100b0107a524556540c0c074120514040d940042d1029400000001042540702c0f01074000d80e001200e0200000024004048070070350359100302c0303411071414801080800e024101402103580200740c0500e4414400d007858690b070340151811620300c950b0000003020301442c04150007501c090008100401804c2102c0034088106031014007040140b00c030001409070303106006403a000001c2e00c00f01e80345142c41c0c0c1c2416001d80f814050050041040983c0000c0c0d01d4842c207810100702d50040705600100f4284420348035443e1005110b280c40c1503201a01c880011403c00035000244201d54001134002c0344160720304150b40b1039522012000000341c40a4000c459000c0c00c460441e442210000f0700d45e524000302c03642a40300d40 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 68056864 1250 68055614 68055619
    0x70803090a06020310050117060918010915050108121c020904020702030102210a060308040e0603120c071406120a0e10060b030f0c25110409030302070204110a0c08090a0302 76
    0x20045c000309140b01d65502050314401d1f01e43c03004003080d490800541c3d4030116240c5034400602030100c4e030041031007100c18140c8046680082121545a120484482403801402001968071b900400c87d400003440700b83d1000b0030346520b161400d003081c440070302213094070032074540f115900159480d015540c0e541180c1407154054002d540300d1159001c2501d4103010f102560707805800e0b801c0050030001750b82c441c00007902d62040500d800c0504103a50194a2400102016050311070143c0840341025520301502c0f603856a0b60080c00b2550911101c1c50142400313201690061405200103400c039150b0809203a400320500b040043e8020303858221510304840c00f031000450703525110b0042105250b0000442c81103003101800c1c46140c541d04c84010042c03144a1020844856502d092400c001c10f03c49801a40d0f4010074030000d0316055940010112040410f040303010950000d0000118101b50040700c00045c500c12519041018025001e8542c0e0b82a0200814645002442c01d040b5900c039035034230000e940c02 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 68058114 1250 68056864 68056867
    0x307081305130209121204030f0c030203010e030d29041a06041502010e0703020f01050c15010909060b030d0203090409020d05120c070906050102031603030e0d030c1b08070803090a0602 81
    0x6407030401c00a601060b00d06004000080307001c551880e002811b030400414501000d8545882d42c2c075155010510711800300c038440c04c502c10004c00342e42c090160080441e1914003550fa03c0003004003e504445a403170320000d0380d4492100c1c085041d104402d404e2150842583d02042421080801500405556000c0c6900c2007000c1808104545045400e05901c1c600da0000c100030040440c1c0981e0f5540e0901c4001d510899000b42c00c680c0354807610107403070039100712000c442d03800b10020200f50304c803902600001c82560340c60f401941880954003903a8044a420b034041c00c2403030080f0400940300e00c1060381142c013071900c59607000119160b20030b001d29855004000c0e1140407000c85800d2040c0d42c044083d42c80207206544002c11111001d11a030000c17910160025464184221143c21000c10703901c006800303140e40c0b9484142050024041400e124455a800140641121402801d811030b00000b81009020300108100000c0300b0b01c08031510150000e000c1d54032507442c04080361806008000c0204080e00 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 68059364 1250 68058114 68058139
    0x30c130902030603010b01050f0901050702010c0b0a09020108180c040b0a1a0a0e0a0b1c020c0114040b0106020c03070b07050f07090203060a05010305040515070908032208010501030201020307081305 87
    0x1603540030b035000b0002203000b84002910800111140e004a0801c00c81c0d401c020085064598054401000c4152060611090103d01ca848450580c2021510350401c02d8403080c2c0030b011580e1001043d80c0c04034000249a011540c21841030b039851030825041c2c0e021300e503113420b840070b1070352074144203801010014444842e0548a81d000c0400340c015881000104c0c4002a070b044580c036150301680290b40c00c0f04906810701d940c0c004c541248515100048410603420001c0004140c803e01581c2e803000c0c081001481c9a09261070b0405206105a01901c21500111940c054698000c0307007d0080b21841011151502880d0800f582480c1611044812501c948440000d220310a03801641c81400c044a0000c0391950b20401541a5001141c0040c66034004001615031196800c107034a07000605860b0401c00d031a1540400b40c5140d003c2070200741e1400c1c1001c1c0403d4455007000141000c0c0c20204020b01840d407540d800031b5a00d001c0d000004040110205038400c5503180c0c04203c5004000c002c0c8020400c00 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 68060614 1250 68059364 68059379
    0xd03090b0a050d0f02040e040b0a02040f03061a04062105030f0408100b030d120905011401060509030c030a03020a02060307051312120c231e01020a0801080703021302030c13 76
    0x82c0300442100503d0709101c074150200243c0e20a550480d070711900d00c0256a5a01d42e134084086400910b004016030f400c1c48045158100e40036050043c40c4160b200003540000100b40103841c076411943c01e0312a500381902400600351203844594101c1444280c0402c50495141280c1140a120801c0c500344201180020700c0050001c0c2c0d40c283c184500300c0401000b0820402c1c1600c6440c1c680004001c200c51404120807412264880718070180510000510348601e4800440090800e80c00304001a4001c0740c0700305e50303250500030342d082001301710000c00c1c516200b60360194494064200181c401c400200010300c030240950100c40ca40a04008a40b0f0070907100c00022180c007109003006c1c8c444123400d003400c40300e99001e20f9041d0b0b00c2c0c41d00401c02c01402c192071092040c0c1048a1030390216140203200e820000f185801550b60080c5039140000741e00c2d0400380b20700400803901680711050580c080c503800c00150705ca10051080743c1c4020307400903940f0303035a502007070380702c1c0c41500204050041d40350710004444 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 68061864 1250 68060614 68060617
    0x61d090a15060203040303021f0f0501060e040b030f060604020a0909060b030106030c020d080115050717070203010c090b0a050d0905030d090b100311040b0a1703030901060909050303060d03090b0a05 87
    0x5590346240c504000342c840c00100d81d240101c4c0001005a0b1081744040c08030104400210340e4014030000108180700d0a01912003500c0003a404071000c01c01707050704017089203032501802c0003101c4180c00405942c0254036034036a5800003d02280e0049900240c055038a506c01d842d00009440714042c18001581c1e9914a203150358824402c110001c0e2034448400507262011030b18402010807079480300030300c0e420281280090301c154400007041c08001c01c1040006000d2401221110b202c3c400303800c0d2110540d0043c10300f55285200440104050b00320188000c1b982c00701a10607410003444c1c419155001d0040c0f8100505070342401903c580f01c08165460340011603003004906e90710410344001030382c1780e41c0c0030320301d200300c003400000c1510022101d5070f02c0034107140c1e0100e260410024543c0300e00ca0303510300c5c00d200a400310306a03203070b0942c00000400c03030000300034044e00000b82200001040f070488551982510381c00301800f1302e44a800c0c4a0b0644042c03511420304140074000c8907620399560002c494020744103 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 68063114 1250 68061864 68061881
    0x20a03021006030f241e060602030301030b18030d050903030402040c08070c020105030a020909090a03090b070804050609010212030a06050901080606090c2206090e130c061d090a 78
    0x51092060303485005100c0e01800c021650b00ca80c2111084140b6034542c54050b98500100004445c03d41c041c1c060130103107005280c4900c4100d00f800c002080703100601e400761400743d044401954410001000024482966268031240302c0b2210000c03d480302500500b10310501d0340d011012400c01084c09540a00880110300480c801c03101044510740080007034820f01821101c4001255000c004000903500500c010b5500a0341c40310010301d000c2d801c0300019403006099884d07004941c04030050408043e00142480040d2000b1102039040040954607003070340f8032540c01958080c4002094100c00c990007000016a074100c6103a4080c1c89261401d41d100c01800300e8807616110b118683c0c00000c0c00040415064001c550180056440d80e07100600038450b584000c3c0050b10064510094000020000003842c018000c1a079070b02600e103160039956041c00c000585000f10202c1e4101a400c0015030303110440c0c040714423a041c0594201c0409159062070681180c01542201c026400c108511712143d10031901c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 68064364 1250 68063114 68063117
    0x603020604060819050103150b01270303110601080a061a030d11070605190c021809100c0503070e04050703090204050109020a0306080a12030510051201050603060105010203091c02010e030d020a03 86
    0x103030b66a21960b13001d555080c4000f410402059041d07103c0003641e0380043c2203520041c10400f0307100d0015070b1340344403214400b85d24080565005905208160b8426689051415090300505565041c085050784405c0c401070010030250340c0d0400e054048850880250540e00000d0965404807080311014040a400e1900400e80e8043d6540210f00b9500440644500d004a03800056204000500596880c0d041d0711007a80d01c40044030485a84a02c0d800d080c6105039041009440001c40d2a0140d00036a4408503905092020034010000c1c4140e0050b0038010807101101e000c0349a0b2070788542070703004240000c0041c0d001400c240010032b03011000e400034070340121503a400700315203070340c52404540b0b42e60401c00007000000c0e025609000c03c1c1c0b1a0700320b5500107c404c41c04000c299501d0000450080e10301004141e980d45580402010346000c4c08881d004010a001071468004000001441c01202846201980003548034007070a6901c10030038072101c014090200d81e44000010400381d600c1501d42c1c0c1c00c40 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 68065614 1250 68064364 68064391
    0x121e060311040207030509060c030702060301031a0709050d0b0421200303010b0301270c02010515060910120207170d05070509091602010b060d061e0e010b07030306030206040608 78
    0xd5070b42400c0c400c03184035a4142d624103040503a520300b00031041d44014a100240e00c0f0601c110310260761240002e500842c407804100300e10070450036629007401030050011042c00303107403207040103680c680b210f07403002c10342e80300680300c41960322850300d600c145140400610340d00650a80d4000d4440c0c0040e0b005400014842c9040850010400c00540c1c9100901507400026070a2004120002200d03c00c0088008400c0400001c0030203520380c60111490101c0c0f00005030744500500c040d100e5044034500c0700240646500e8945801c0d0740200714079094280306041001700301e80380001c00d4404c660543d51030030f922140303004021818608140d0305820110600070b11916210114a44600400444012079000f030204041a0750700030801c1c006510500209c4159500ea40e240011a80c0d0710b4024080325020a034006805820603030b030000c00342c03030647c524030320800d84d1041880000910814181180c040e2503c00e50b0b04c1c8c0380c0e8502180603004685c00250480380204002c50042e801440c00703441900300c920600c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 68066864 1250 68065614 68065643
    0xc0501290103140709030f050c060d060e09070308091309050f01060608010602070810051f0b0a030c02122d030c03180d08041725020306131101121e0603 67
    0x6451508040c0d4480b030100e04440c404100094010750b4229402d40032350151070401205034049481507115601501c5140e540d0001840300207401c000d03564000c01c0703400c0105101d60941e13903810300c91301c01c1e107c0c5c1d640310300c00b1a0400ca2070012a07800261105a02105031548100301280650281c02c45006240c007051644002040a900c009008000c41d80b61000410000c10045c120030020000036042144012004114800e104c140a540c40000c004d2207911590301c00c807082008044600160701364045400c04016083c01d110300c1810b440c0085200e000c86030303440c01e01c820b04d4803042d00502411400d00401004010803101c01c0c9001c2c6104036004801c4070660414102d40c140ca5240080c1d0b06000b103010b01e00810007041e98445402076040c40a0001841c0c90800c0d0303104100c40100c840708160404140541e0744c11410244401a044418030700090240c48240d960042000030b088005030400c150f00d10107140450181d040703010358820301e19400d01e05131070281c61940501040c2c0029540c842024086 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 68068114 1250 68066864 68066891
    0xf03040c0e040503030402210303160306050414010e060612070f18080d0305060303090a090e0706090f090c051207080603071a090f150a050a080c04150c0501290103 72
    0x2901c40e681c884003031417441d559075003040080d031081e81c0e0380080c3c80605154021000700800c010750081000c00f2401c44446140c3e42c0c0141036401640000c1d00450800412942c400c14040c5581d06440c4401103019107aa83c80300402c4540c01a118000e8000364210180005560400103001d19110142d4a80c0e607410b00300120004010140d116a0100e070f400180503488051090744030303036006a030081c217a070f26101c4a040083ca0030f46480c1c1010451541c0c490482007081c1c0201f00c42c1005040c3d604000e004d01d0300c0c0021800f10301c001c0e84102e51405441740f42d01080c0d80d200b1400ca07443d0f41d0010200c4001340c00c0c0a280280480021185940a841881c0c4042000d01341c0c840350758200b0038481c241615018160080c000b80c040320700d200d16040100f20142e0841e407220760001c6d2004018a90b109134030349114034002807140340040c2801261190403c07090100341c2c01f8151035103041c081030070485841003061074620b0040040c40c04c0c40e008000075224102540400902040b00d62800740e800348011101c1000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 68069364 1250 68068114 68068139
    0x1080d0503060402180307060306090b1512132301050f0c030112021309080a020d030204050108010e0402010509030d020d02100203090601150c060510230907140408030f03040c 77
    0x6100810300c1800019074518290f0000c103002242d6071420840b8045c0b80e40400d1420043d0b03003002d004681c45280901c030300c0051307104054030a5001c94000054001c481d0001c20544940910040089201000682c40c40088121030f41800e500203810a1045203100d411001d526804210310115400d00c0041842405d0008c0b119000c0c00180045c075285901e80403e0501e07961220004a0300710190410504101205200d02c01e88180507003179079691010324aa0081c2403621141c00a024548144820301491340e000c020541035503046840c50700c85881d2030005827424016500f142d0752500c6011000e0a41d0f41e03001c00d40044e045c2c2980c0807242c843c41340e00c40c0c00e400d0b4003045905031540e40c00080100032072040004034280c4550b107407c103c40040440c2c0c6520042d2030007203e100340c25011203c420030401c1080c1e1205075106071034210882c100340301e5070f00050700c2c2040500028100100e2412245d075020078601220300030310440007142d64800c524007400d840e54004403415035441105c0903001892142208 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 68070614 1250 68069364 68069383
    0xf0a1505042631090e0712140f030c0d03020d09050d32090d06420303021b011206080601030b1302030331140306090d090b0d022101030b0108 62
    0x2400d503080f050038407030914000c08003040c0c2c81050744200d08000802c68003843c5040c7d56580103105208505000640b0249440351080c111407256004200e450306900010589000042c040d140151f5a0240c00c4010340c0503012085000d00240074102d80035002c036401c40d0041c03865100c078418400700450552800005281c1c0c80c02482410901044001c0c12850820641004140701c1e010004010a4a81016103941072000c6401c501c0c05038149071080030407042003251f00b600c001c0076000d200503085a5000f0b45415850301810000c1002108a488aa010306500c0007182071a242c01c0108035136070701001e42c0d103040a2209581c000705c19408a038200030b0744e00350b0a50340ca0300503000b103182a80450748001440404180080c810ba000d00c41c51b110514114420b100601001c0c0c1070b1a01c1000302e408160a081003d00000420341c4039070300113401940c000e0b12080480382c044107099110729070703884590080c3c440e2a00100d4035480034003000200c40da04944550580e401614911010380c2ca03985510740c2c40c010751 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 68071864 1250 68070614 68070697
    0x30f0305190506060708031617070c0201030b010c2f030304050630190f0524010c06020301090603051203010f0306050402040e0601090c020f0a15050426 67
    0x10081420140c601d500055000180030382994039010242c1c48041ea20b800503038540441c20401485c0d040300603800010143c220400208505003030800e40e00103040e503281200003d041c183c5a0740d00c0121a801040600161b68010643c6c90b07a00c0381c551420030301170780b407420000300d11401c00038034070803a0800000f99015504007070b2210b0300c0d20070f1845003102c00460840211600c0c00c00b0051301001490607010b100c3c001e03580c000c4000400c200740d8050f002910380d9400c1d2034038018541410091070600044250100202e441c288104400200300100d50585050f42c001e00618000400050082c801ea441281220300950a541003000d41c00f8071b0700750500c022300c0b400c0a4401d4152050022540d00d030f0090340c100d4801080003804a5000c40700e6400c00800764070000c0016622034020001c16018440f040c41c002882000c1d22400006640b504250b2b8074811000c500d080d52031001800f00640b001103106005e800c111094144141010107540c1540540d41d44031306400518144020840000c90000a40a02 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 68073114 1250 68071864 68071891
    0x509012301050415151b050a051605120a1202031201030b0411010f02060a020306060408160e13031b020a05030a0809010909111603140403060504051212070c05010b060f07030f0305 79
    0xf81002100d80e03050720441b40c001e008920302141e000907001c100c809240303480380707028042000d40d9104100ca418041da204070b0051105042e100e05101b4003164031002150b2140e15195a00105e1008070300c0e5028100182c1100407007a0008014045440c060300e02c02c0340718401c000307094110440111030180c5040301d0070700540e1084003c20000380a5401440e4000700240c0000c0c1090b075034039013032485c00340100030b00208000300724424000041301007045940145203104e04030042e1030300d5a0041a01001c180a44120900050100119a951500d00008220040882d000c00055090402e20b40d80412895404544001400203507011a80519445014a80c036183c1c103010404120f03030581c0422001c12000c1050102040418402420290026500542001505143c289400c1c4e14007078500c03002001007403052040c0d0070288901c010050f070140d29441c1060711882c851814501520f03070302044ad076100401250aa0390000940040c1c28442d020f42d54115070442503c50940440d8800e0701d03a03080d10102c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 68074364 1250 68073114 68073149
    0x8010b100804081e0310050a08030d0b04180b15030a030905060307020114010b0405031b2107030c06030504120c05070b0c070801180b0f0c0405040509012301050415 72
    0x41d0868030b9000e4001c00210b46401c1900300340040c84c0f20000b00c00400a600030051003090480304a041010b0304040d2032500390300c0c0c00d01c0c85103552401f4541c030700098140c5030040400191150340001000302c03000c0c0c01c00c54210042d03240c650349000017182d00700e81001c1403001c00b05449c030b000640d850210740c1507240c7d54101c1e820304050080c1d0741e0006003000305541d01d4a09402d03485032001701990003003200701102522107050a00b0181020700e121540c0a0310122201e28246664800ba101c02c04848030302c40b000e103001c910b441e143d0704003081a8000b41064808010008605030190001071085200714004400000708010558140310f4a900162030b80d881848144541e08201d0020400c1c103074074034229441180c0c0d80c1e0b551070a460b23a0003200f0040202025041c400c0002d8201015088135400fa00c02c0741524109000c0d8500313024138443c0900c80c603101c01c007040140d0b50a6225244032034140d200c492240d056910010720080c800c1c411503018a28080e541e005007084400e0040980300c122218200090 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 68075614 1250 68074364 68074367
    0x9130911090c16050d1b050c0d030903060603050a14010507080414030408060903041d070507020d110303070311070b0405030a020f0111030c07090501050a080a2006040305070e0108010b10 82
    0x6400620602581400b0080d0f40d0211851000702c10b0380b18415001003000c0005014024107040b6424400c02d070010050701c801c0005403000c2080061601c007500c068901100c1410100c9010380654005030401b80b07820400702c00c0c020045100b2a55074014125407141e0660f41c4046404c0f100101c0300c01000844030000b0078001101080c1c16030054602c60105c0382000e4550200324101a001d44501d005644000f0b001c1164007004c00c20b40c042c5420200504004e4940400050302e5807140c034800130f101d40902050302c800c1155a140035641102c0203800c894a404051030301030414181e1000600c0c00b4400c458001030f0300303044d00c2c04a4091324005009800c1c2c2201d290700f403150401d81200000d05100030f0288000c4000d00410151106404000007404464903005990040301d01c1a042a4069000c000741401080c1000420054190b4441c0080700ea01234000b03500566510080c0b43c950b80304100003000018440001020025256440889100c690381d4130b80c00ba0888075248030180d00b0001a81c800001e6a = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 68076864 1250 68075614 68075629
    0x901030c0e0d030c08040f060c14010b15090102011506020d021c0207050105030a060902030f16081e040309050307140307080109110d030e0402030a02250203060a1a03010c030209130911 81
    0x114030410101b41482d885904c840340115480d040701d030000d1031601d5801c0c103011107000c41c64103020080c40200035442c0d00d0008074070000060030f0341c42d070302e4400066010703400d91007540701c24154003900d60810481511198025103880c2d10701000340040c03042c2d0350250009103a210301ca10341004c1c01e4000301380317041c0f0700401918550401090540e180396520b100041d41216400210300c03a040d001d4001c0c60324a40041c001320320030400c10050080000c9001085100034030750400c11800180b0604130101d55031940703821504103440d42c028a030103008180d00010303503425000100d075680780100c00ba510f207151280c041500301c40d40c16138081d004048094500c109810035174a1996500d010b850294503001c020380110701030368021386000c2691940001c9a04d107100001e00000c0086101d0b051044d9400c5003900000c1c1c1d54403001d0b000c0b02001d5601d450000c00d2800800345281c021030050001c0c44154079260000e07009400000895000f107544130315048e0700b190684a10441d8903440b03005004d40e02001c0c0d0500128 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 68078114 1250 68076864 68076887
    0x3060f13030302090a0303020604020109120f0305090f03010c051e090a0303030b031c0e04050601050702030a03030b0301090b0406020309070b03130f03210504050706021516020a020904080901030c0e0d03 89
    0x60542c01c100040c45a05d03954910390155000707030010541800d092000401d40c80e801c5d4012440c2996150000c000140041504100305800d80f610319100c0003410000365407000024030181d070540c0780409130700c04650000040e044130019006a1052103140042140b224824607500540c131103002c0c401400061f02a82c00b0180c6024003408940d48001d80540312102042d40f1034200010a441080703c1800e841c0900486030302841c00c0ca0000c4c02d00400e580481ea0302c400000004051503120445000261400d43c00b00c0081a000354104940e42414103050300258400c1c1c40ea503000b400707803040100f80500e10000301c0340140840b480e80303082406152104145030307941e480b0031810000c4040340482d00c021410b5100c0c1910301030460024080c1403a20300103240080d50342c0103500b550441c0700d242880c40e04402140d548922100c40001d4140c00c0600102d00b00407201c8402940031030030400340414030640c0805458a0402a207040101c810024000e450365440051801d0340603481c0b0f4405c00c0000c4c41303584250710303 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 68079364 1250 68078114 68078117
    0xf0607111506060a17180d03021801120b06070b0f010504090f140102090604031b05040b061602040f020c0a060506090105060438070b0c03100302010c080d02031303080603060f1303 79
    0x301168101c0b25942e800281d560707414500510004150405003413207d0b480c010710700e090440c94451080b02203020102c460014030306101400c80034400c05052031300724103036060004040070b540784004c2c5841c8040000030780340b8032402d64244002184608140c481c0180ca05c1d004210601c2c00c0b449a0369881c040c1816030a4508a0b540074444405680c4829003c1c0c405107100b0400c0140c0c500c5d4032140c070074501c0a241d10582c429401e0241c2c628098070f52a049500103105155018000380c2c0701c1c004134010f498100101c035141b510014403034101d8507011860321005480341500744810346400c001c002452100780120b6074051410841005010080780c040d40281a00c21321410254001c444080030201e280c0c40444010100012500200305e098001c0551102c00900c2490440c00d20811b0122084685c0c08000e060211b0341c151030091150400a8400502c00c1d55001d41d0b136803030590f4003107000d4200048103c0c042600d10300400c81c1481d0109140303124a4403007142150a83e12400f0003200101200e80030340 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 68080614 1250 68079364 68079377
    0x6180b04020f0906032d06090a140a0e01020f0a030203040b0901020903120a0c0f05010213080106080c040b06040e10050a0603020901020d0e0d05010f1b090b090f120f0607111506060a 80
    0x340001b2000700701500c4100510149909490480c0601c4031681d0001c26141da080e2810384112400c9034000181f81e0000c40381100001c0d1460243d14140c028400e0300c10201807032901150071030740740b581500103500c40d40c841d07043c0f10b01680f158074000d0300381c4c050f40d240a0350680090714601c98142d414005400044a2450b00c01d000380016101c404050240303800c150b070380d85d4000a00b406034a04e50344011000781008402003110a14102c0c08a0f12416080b08951155031103000c1140182d0350101945c010b0303c451b4452404505000c1040141e8145500c152402517000200002d0301a01138400d403444144103801500b006948044101c4030740c80c41c0000c40342d00110a040c510045a024030a48079114202c000002e13020020101501007420315032801700030000d481c40c088c0f111426006c16116022019942d003a01022090001240900d0080310401241328007801d0785c140c004009281401600381c1d072190019144410b00c11138440a080352004c00c04168040454110b080c134200400701010366243c00d0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 68081864 1250 68080614 68080651
    0x1030b04021804060b09150a0905090f0609070312030903120c050409090602030103050c0619050306031926030114270906041106031005010305040501060906180b04020f090603 77
    0xc090b01009603010354000e6960404090241403144030660040101c2944c4002c0018440008204400501441980c141c40700003181070000d00b000085040b001c1541981d50500c0d142e500180d80c3c0c0042e00c01501c0d00ea0b603802c55000c525000344208201d180d019aa55213241501100c0710300a000041c080008205080000203041c044d1885800070542c842e10300541c1d80d500d1810002d281141210b1203030721400c5c04100e0360780c04038030582c0000742056a90809a489654080c0000d080101e6880902c8031610403503181c1040000c043c0303586019103a28000b940174070798220003204050009001e61716210600d140701c3c110382d242541801d004c940040aa00d0000107000400c6800c48005890440382030713028509100420040b2001511007600503601542186441003103034001c25528441d2034107243d554800315050140a402c00d5000d04110749080c030130385950711543c00d524104d4040e5000c210b89440c1c0030600e10718150084440400021007464144442e480800000e5440a07000006202d50380144 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 68083114 1250 68081864 68081899
    0x10b13030203100e0f0c0f09100b03070507050d08010f0611010908041e0911071e0b04150b0f0904020114130f03060506010c03080414030403150504020406050105040e01030b0402 78
    0x5091031a0a83c003c0490900f41005890785490031004556915030460341d64048140c56140000b00c2c814021141c2c01c50b50f4032040008103410b0055049080703111000410410b865030400d0042134203500c2001202c4010304c2050003120000c3c405c0c02103e1402011940420015108040f008604001792000180c0c6d122a0350340c408072580140d0001d4a4800d040020480109905925400401400509004038032024400612a2103150701c018540301c250303440b81405c212164030900c00d0585c040080005820182001c414200020700101442401c2107400b16080c01c001440041d10f082c054070b0b9841640321580151040314903030b182e01403031070801c0c008400c101c1c030510401c4008240d9905207085407400c0d424107405643e8000e0140d070600421003100000281d020320890340c40b6401031403941007045001c0b0490700310f11640c3e0014081c00311401c200c1c8580155648503d0083d071085800700011550350005550500407440742c0081e89210900400103e861140b04950051005001c0d43e00f0880b00400e = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 68084364 1250 68083114 68083123
    0x5041e092001050301030b0f0408040e0f060f1008012904030c0e0c0906030f0601120c02060f070804031b02030304050a0801051f0803090d02030106050d080a080a14010b13030203 78
    0x40681e0300409408400a4054031426840c80c440020710701076140d5030440d11201d810300809401d1030132503100c85002406202c1e010013a5000b4200310f020542050074902c88075000341805031040f91285140c3d40da004040c0c03a00c01442800401682c54910b1b19a1804500e11012100c0003030903003c40c203000400c00e19003081e41d00140090b5206521a41145080c0307503110b50a624020000c0400810030010744c2c0c459038030789064a034011095481d800f031a5039a040102c80c002140800100002e080145107001983c004c908184200c2119850030420707921501d007200c038844141c0780a00442c40702049100054040080c028001d8000340440b40342603680c0380031800115441e84202c0442c0d47d03400c180f01140100404503880c8038490170008891500306082c541c0c0b00d2080d0412548901401d0388000d0842d01d084d000711000b80401844040d842002c3d0800079815130240c407880c0d0004111200181c910b001038403902080503400b42030064503a00b00f0003e8141980030024540e091100c40d000000180d078100f0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 68085614 1250 68084364 68084381
    0xe0a050607090e2419170f1c05070b070509030703060506040b01030c0e010e0103060e0403030912050c1b190f050a080c0319080c120909011e05041e 65
    0xb92004509480c101c4000d201481c050051020b004412004048944024056495110f412982c82000070840610184640b1684c0c0c0000380c102070149001d050140f02040b280000d294540541e501800e403150501090400055880007080081c8025008079103812100f5500c002c560514500d41004a4006843c100a560045400075150810800d9500b0306001c3c80d5107d110a003014001c0d07105c2100094403a0201d0604c15040008654040741c2c2a0322a400440c0106000301440c00203040c2410014040c101c0c1540641c1d50500038078014480c18811000c80f226000c203040070b03100988001c03d1090f03280400b89855030303101c82130040020a0b0000c44c1f07095002421204062a070852500052025041243d40171030200d13084002075000c2500d003c41d40c172244064082c10340a44100e81d140401b02d90003008001100e41c41418944507408c2c122100801c2101800c170760104150f030341c89028040c1c04c92040b85c96588030038049400c00450500d600320764000d00c0160b070207156801944001404840c1e448 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 68086864 1250 68085614 68085617
    0xb13020705010b0103060e090a110102010b0a08060703050f0910020a050c06090604021201110409090309030804060c0308060409020612040203010b180a0507090e010303050a0c060203010e0a0606020c01120e0a050607 94
    0x1c81040e40a5a011b104050060814080184061601c002200c0e101c58070303204054024051040c4d048500c0e8070039402030740b19807001410b58201c1900d8400c0300b6038a40044800034080781c82e01c0003052110702c0c00900103104000b001d000304200c4c0144440da40181d00810071010a028083c410290400824800140b184046d0002001c2c2e40c50a40100b254079118140042d000307074034104c07198a0380d030b0354282203d00380c814181c2e012401c0c0320240760071100140342c0e03130010303202d101c0c040703808107800781e001a42180e40b6000e5602c601c1e61b038a421041004423007820301c0095000c00100181ca400d0304984c40c5c1d2681c024002400055101c440b000441d100c128900380d05400518035004000c0c42215a01c40c003500300b10703580340c14034002d418a24081920207041c04003030107205000c19010496403161155a450350740c001804e40d00c03540d6400e4450501e61003940c000030894144103000c00c156100142c0010306800580d1002004e0860070034490040a17060945003c41c0607005100000c510100200c074090304c0300703 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 68088114 1250 68086864 68086871
    0x10902120c18040b03030c1c02101118210f01050906060f0114070c0b0d0b0d0203060106110f0703050309030f0d0509060a050d09082106060301090b1302070501 70
    0x3000341594242900502070500140180034070041c00b10525801c80e404002960700051080e900000240b031750140c195122024402c101400b454802011282500c51106400301c9070301038111a1b15134140c44010210700f0b90f1070418003d1f881c20800c804440707604030201601a90000e00c443c400100c01c1c9400d800c4041c1d10340c2c07040703a07400306080092050b03e903c580e02401900032401e0440c000345003011400350030f43c100007a032219031038003911003011605040da112450480003a030340c4003001415001a042c1070f0790b05150407140141c0f0b04116040d010315580c0140900081d0f0308091003654500350300c00703542407603100340e529407440b100c000c20081d80694051030045441d486801c00b01b52074007140f030900340c1640d000f01c1d40840000d600304040d1020325104445450f01c0e40403048080f0388038043c08031000e44041c142000c00040c4440070000b04a0381400031a40d040c440c1852185022400c001d886060308139000300010003942400d9409109422801091004003002d00000d83c8140d80001c6010780385a5034 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 68089364 1250 68088114 68088127
    0xd110a09060503010308030604051b03041101141c020a030e01020c072607060804141912050a02030304060f0e0709050a0501050108090c0111010605030706050d0c1b0305070f0b010902 80
    0x200095040001d2200d490201d281d50306550b10034515000c06400703d8055500d4401007101c0a540c4122004141111035202e9100e00d07050a0068440411810b0700b1b01081d0070102540401f18200120b0314150b050329404010605132100c05402036100707244180400d41d031007a0201c8126402c3c0001c0504000e140010244039003002c0310582501c0000352941d0410108610009860030f01260020456096050510060365642001d100c14400100d041040380a040c0c03403801c0706001000c0013080039019a6075000000d602c01800c0e5568801e4034201c6025034810700003c0e0000300075422507203c8240c9054003040d0700c0c0c0c088054a240c07100c19009021095194410001d84009030301c01d20380104404d190000351350400b070110a80f101d901140003410070002220701c0080f03034425001400201809012034100c0c0d81c0c0d44a00405075003100384503c130740500307110451400c40c0c0b084080c070942000e201609800032596660a80b00342c1c0c440c0004881200c401c1032900d0101300c20404250082100000140c0e4840 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 68090614 1250 68089364 68089367
    0x2030c010c0810090207030f12090c0806070f05040f0b03090a120503160905010e040b0406030b0c0c010609090305090603090c03010510140102011e02090103060b072604050d15020d110a 81
    0x303841c4e082480b880740f05001c400b000c2a44040c54421a40306420410b0485582554000c017520003000040d0440c00d0141002507a6800001c0a0380f069419503941c8003002900311084440e4451446400c0035100c40f6601805007500040003143c22841880449100414959642c8001c140400d0404089100441005120144180640ea910380c01e8541215011304000003e40245001611a4011030799010a000c580c3c40d50782c8003a003c0e5400100400c07192070864400e80456102031b001c400035500748400061030558034010b10304159895220182400d0003441403103400e4100910407526881a100d41d00301c6902d0038880c0314000c0e1190100c4030a120b0400940910a031300644c03110341160314002c4c0d410a420f03a00103000654041d55540940c0d10306801c00120b0113419681c016603450140001c4000070030075010305a04000212440e400c20001e450403c500441c0035510600341c104224084220014000090380d82040008071401401d040155022904941b03070340c4200703400e2400003c0d203400441d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 68091864 1250 68090614 68090641
    0x40b0f0c0a0206010b070602070b01030507170c060a0e01090306140a052505090105120a090203060907060804060504020d0b09011a030102040b25140a0c05010c0515060102030c010c08 80
    0x8010521480c0c5994071030029a5200b0510650140c00350108411081085580440b041c0680101c0c500d40c0c9541c40e8101280c45011500c035040c4804500807404410b10804524440200c2c0c0042107071742031800340007042d980c4054107a0610704003c20940b0201c000756451180d402c0340b8110700e0151185141c065242d030200d030342c00b42c400104179000e00c00b14051095481030b5214809080c1c540551140051001607070305026460003402c14400c2401008004002948542003041c001c0301100c3da60f1b1144080f0540721800c1c0c3c000c2038000703220140060042040b54000a4010f44090082c0e0a8000310791210f1800072425907010540365103d407040720403903c50041d90007028400710001c528182c074000c118242485a86203922400d00390b05100c40c2036003021400e86659940190340e1000c802c02c106c0c082a150003601d80115940054500302003080e510074070024085a07403000082040c0010003604028103040113249904601c800c01841d8800c034030030b001d984005841909d69040b5414203844a5000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 68093114 1250 68091864 68091871
    0x9010207110402250201440105010215040f060e060402030607090803090411040803040605130902030708040f0c050303180109051206010b0c1204030305030f0a0506130b01050c0105040b0f 82
    0xb28014003200c1c0300480407040d1821119442c00040d0307005404e510051301c800700348509000c13034280201220b45016080c1c0605900980c00881c0042c0c0503503011110080b088421b0082d203006a010141207111620852002900700c1d004072102102c602280c3d8440c016540000c0e990001034010605200840c1001c2150703a80102c000c1c2020030049003880c83d11903403801100e241611845d200c4080100c41480780742240d001d0b000307039401e40755a65140c1b04060126130105101d26034082801c0400150800e041c400e903401421700d0350714020301351107075102d090000001d202e06941058001c2030008540e1740400c01045e050224032003c035050500e00d000500a00c040758070460042200c1c0f1003203490010023040490644410201c0a5180d01a052000740762028808a02c001c203100001c0220130b05401001a5200c1c1100b03502d4001c05036034042c1038206030b40080d40c113140c20040c00340c20702d00e402a081d00402c1c1c502d20107142090400f41c0584a05080da1800d50b0203803900030010091098542201003401d61 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 68094364 1250 68093114 68093119
    0x204050f0a0b1e040305010e03040302240901031a092805011d090f190606120c030210140706050405010e0f06011e030209070207090c020a03020c0d03170901020711 72
    0x15072890121030107240d10441c001c9600b820038a42c410040540410155005150010020080300f010001030b0390342c0c1e5110340002d0748241800481451582001d15060b034a140e0110b803018102000d00c801500a0183c0c10240340c0681c0c91084a08195103444d880c051203101c2c14810040548450b8014030300c44003081c1907030400141414014042e48914900d500c0140c6011000d04070b44c0d940300e440d4182441c61304000f5480d54050240741c59000300e0503500382c1c9401c601501007084100c2d610603c0690030741a00c02c004180311060703403041002d03141c400782d800300605081c10701c42240d41c00105090010340c050b260031608556228284000c2c05001d200d14030032035108400620030f5051081003d6611401441482c540030003900060701104109281180116405030180c0d0b900c1c14081c2003e500e80d522402040d03050361512150744040d9100103596081203405030064001904000248480c00001d40b1055003485600000d80481d510b14010a500c00c3d10b01d1300006840302c845207402d8815a81101071a031 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 68095614 1250 68094364 68094379
    0x1b0406081504060f0b0607021203040e0f070f09150c0602310e01030c0b030c09130b0f01050412032a030c030807050315091b0a03200f04181404060204050f 68
    0x2d17076584400040b0b541c0f440c3c0441c0c5c40031a100542d1140d602d54451900210001c18604050003c075804500c0894007402c49500c810106d114450011501d0f201c0341d01c10303240441c3d60b81780c2214025018140041e003050044101518090711400c4030f0343c40044825252510794003074050382c522407240e0300f4400040e00588182403e95491030305c1c0c00700b4809060241c0c4100002c0000801e00709a00c00301120300041001d0b04004410228000c880014a030301c891550154007080c00380d5501d50f00c104112010b4510f1011990b1074104262002c88501100044108078180760180c0403043c1000500d1300d48019100303a688a91740d0310b951400402010001c0d010005021091062242d125a04c03038040c0303880d4205031000318080d5107071a07400d01c00c480c4440d451a5424000030340d420410340e0580041504000070000f804510a28130b40d0911144100810081c5034081403100340000c400c00c42000400445030140807400c1601d80500901684007a181110b407958001000c100504102d055008803100403034164 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 68096864 1250 68095614 68095631
    0x1d0709112a0a0501230609240f1203030709080106180b010e041407020c01110615011112120a0e062d040605040209181b0406081504060f 60
    0x4400c01007082650303800c2030150050010720041000748941e01908000240540c0da843d8088000390040000b0320041a2040b60001c0c2c04d5040101c042802001c034811000e0000c102000c03ea100b011646205a40c454a20800c500e480e03604c0c1d101804202c840440a580e9a091520004e040c250150780411000d0341004410444805100030740b0b520401c8084000c01c0c20f030109030048440755140400e0980c0985082c032a0544d0400b1030305294030421185d02220f5411000c80b00640d034000d424440038103158031403000940e10388080400b0481190040c1046200d41a1000601341890000000311110110218520b06107118506859802080302d420800224000c0420f01e1345950004000c2e054191003260054403e045070508100c4007850003501a00c54140392038024007600064405a2040f0799940200c0ea05452001a1520b209402c41c0208100100c808016480d40013104d000c0d0b034401d070384d00340000d03022100b130100c0c941190561103613464a180a250500860f40012a0710100d03d2509140 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 68098114 1250 68096864 68096887
    0x80a030e1918060305060601020109111302040317070219081c020f1b13050606040608060103090204050103030809070e010b27150711061309020d1d070911 68
    0x42000c00901a610081458021001c081c50604650300c200d02c550102d00040400341107540c00300003a40d00c24800d80f2201d4407620012401c0e5060010082c0003426060148041803401107456200040c61010150400d0341c1c98444000d000315443c0d40691052002807803004600c4e1805048403000d000541c82824203050041d525501c901ca0324040003072941c0c0d440c04140042c001c100c030810f180c10240455441141c40f46450900120b0074144034001c406284000750341f03182601030b0910a280c0501743c0c030300b080d140034400c4a02501c05088a410715944000b20005a1075501a403030180d4081d844421150801c0c0d000186000700952004012200e9440140082e01083c0304075224070912510301e505400550441e100c100d00043d05071580301c03642018084a0722044006440c440703000d01451000ea41c006810300009100d04041080441803a0409102d41c010950240182014042e030000300c040039000d10000801001d201005079a1100008102c1014580204014005034000003803e12080002 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 68099364 1250 68098114 68098127
    0xe010e070f080c0d09021003020706110301030210140d09232d1e010618060b04091a0a03051c031506080c1c0b040c020102090306010501050c0102040e011707080a03 72
    0xc6210310303c0004d2070141500050300030b55043e907001041803110f04e5210700094000d43c0403102c22a4250b081c014181107641422042d641202c0d000750084412035461a01141c0d5050074040303090362100240000d0790003036030034880d07040003e2192541c020704610304e95558000f4100303407480d1425a442407605201c3c0500e68840c00b5200c4d0800007000c40034806c01d03007843d0b062012303040c903401e0005034101b581c202d400415000030007168008803401c0880c4c4007042c441d0341074940f103019107492407804200030405543c40d0307444081c00b00c00740368010588000b05000100600050380c8191284d07888144901c4000c80c8041c4108441c0b1454107040003c1c096000810400c82418070074101807201e00e0f00094804034001003201d03035020410100f00b000011005611000300142c2120b640a5880c0c290324680c4d5a0052089400044c4010010041a840c02d001151079030322004180c0321554003440001940d1484032545800f03006c1c0742100201c0741100c9220145050f009510080140c3d0060030300030b011079000b04 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 68100614 1250 68099364 68099371
    0x61806050d03121a03010908130506071a060109081006030c0902070213020906070803090a0308060607081c020d09060207140309060f090402090d03020d110c100302090301090209010e010e070f08 85
    0xf0004202181041c011508000b8000d113116059400d000c1c00c107040000400003040205030892030014270b80c2d103070005e02c0564010a88010800300e00c919240d800c80700031444080d0321400c1450300072704103a21000480c1c01c102461124003a071a44940007801004100300210014101c00401142030130302c243c00246800e40c240d00d141007855800101c2d8800c0f900d81c581102d0b003d64125820a6aa007403000c074080d941c8900034001c0e0000f50440020500b00e282120803a1800d42c0c00040083c01c050040301c20840411190781400140c66007041900c4a90f4024040c0d0f0b000300d4019200141c40d458241012001404880c1100711160030410519010f641d800c0107568140050003501c0d504c0d4445103020030028482c003044264440355034070340f0600305640050074101914499541c2c5038581ca115519a83c0d035807116002a500c560f1035581c00303403050b1090340a0070f090b40d0020700103d0322004603008180001000e8001c1010b0150f148014085040002a8143c0209140c940107a054100e2000284400b0018 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 68101864 1250 68100614 68100647
    0x10c05070311071d010f050d0804050108060a320a120807060e01021209010c110c0f040f05070203042d0506070203010e010c020f100608060103060207030909061806050d03 75
    0x501c104018010407a01c0d000e01040780c3e814138035820502e0902c101c18000d104003403030744003418000300b20307402d100708120005503201140608203410030b0300559015400401480d004802c04800080c0e442c1c1503168134100c0303403125400302e00385201604c03e0343c030142c0f54881032406103203a00020400c8251000d01940c0c5079400455181d00e45d4654039210000e0700c03061021022942c00480c8c3c82040f0002c0140041c0100c009800800c5088a02107068800080d004000b4501c3d401c900801d120301d007000580c6440c00c41f03008000103800f0800303520b1802203480503200e100040c0d02c04503052000840c89481e0105080410030407115440310100d0340080b4200038060036000c3c10001c1103001c1151000d400281c10076841d00001d0103948984403000350f0710b04025004400a1150403030180703540c10103106400580d07840e0390140415a007185c440c035001e58000320044041140b01d02002610030780c5446150044d000c02c1e40244420005017500001740c03803c903088184603a900e41d4007000003a070460702d42039034403160 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 68103114 1250 68101864 68101877
    0x40306020306030a140706120b0f040e0f07090c08010602060907060c02060f0a031a0a030b0f070c0209040308010806010b0301140d0201091a0d060909050a0318030f03050705010e010c050703 83
    0x6200119080a46031340006009030012100902540b41c08104042910000d5440c0207120a0300136840080d9100d0810f200d170450346121519440c2e04040e0040503003a800724084402a100c0a240345240101950003c076a1035a41c955862940354072001c2e80d4010b0120b40700800440c2094460b240d1034444600c2140240301d020005030003151920010b40715540c804d643c110b03071034003841c0b50b014010388442e0058006042c052076040c2c02528000c00040b00b920303008180320340543c1da00caa00265005018000d038040c03055001050005903143c0e20b94500c2030348a680c984680d07515000002d0b01d0085e06030000d400004042c401488030658030043c0d94600d00d01140d0b052518012800103980101c00c542024103500700c415400a03e044080005140c2483d00c01ca0800010380ea0b1a0381e481181c002c090028601d8005400b904003107442400800e0b000d06015402110b41030b5a69521419a44010000c42c040b400c080380200c107002c2c0c03e100b07a001065a0200a1040800449000f4840c0c419074900a090140 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 68104364 1250 68103114 68103121
    0x50409021815040606110c01110d05070c030219080c030102030601140706060f08010915181502130e180705130f060506030a020405030d020109080301051002030c0a030509010906080c0403060203 85
    0x22000c0300b07180655006442000002d4950384004d1080c04071441d08a15031244200d24006544030300358883e0300e400c01001500c0c00c03d000b23100458969203d00410b44140700c00c24000f10159480b403840031010a140398070403250038540560581003080c20208244039900c1402004101c0e42c005000125810301c2101880c3d03102800e00d010340c0140419041410141801342c40032890080560140007418040c50b00012000c520000607420307154030300c3c41900101503009d8001e0000b40850030140b402a442d160240c1000d04014441d004001c065100c215220a04800d11440d000d0a15046c04034280d5032024281c0c0e01d0620010500e0045d45806450745290385448074107030345031954031100207440001e00140d0b40e4280200702c803004e90000d015040c03280c010400c0e848005401442980c0c0d00f01d900c65445030640c0c5c030344400c0050743e0403486039440a41c00304011040e0703050002d010001e082e621a48406485821220004181d108141c10000038041810103000d002d00000003500d04803944048050307660b65 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 68105614 1250 68104364 68104381
    0x3101118030a14070501020f030c030f030c0f07050a06061401020a0201050a0c0f0c050307061e0e0d1203140106030b090a02030702150c0a172520030c070504090218 72
    0x102c141c80280030400c07043c0d402400004041407403800c4407800d81c02c850740385040209440d03c03032042c4141000542d01c1000b101421020000295a1001503040c545050400e0f01100f07141640c00418115481d03040350303e1070b40812402e03220303081c0503060014240355409190400030390380e41e0011401a05109000c100c0341c01c0a80b0a0301c40da003003950710249a1000c50210318002d50860b25a008042c0309014994010594600c14180e02400946440744a98580454034081e12503203030850310580c0299000f99420040303030681d903035121441e04d41c1e540050140381624158040f444183c00c04820941000001900c07540d81e14441ca4001402c080016903d8071400c80503442c1c1030741e550021a05211070400c0000c80008080640b10000c01c03501c50184014011200d10301207081200c2d422000803105001d2a4044c610304c421510450312814484010120b0304465401d2045000701449640e20015120f0748a110900c040e000038502078a003030000880c142c0c0003a070a042c00c030140c030a102c0c9201c4002034001 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 68106864 1250 68105614 68105623
    0x718050301020f04170c03151b0309060415020a02030708030a27050d0801031e031101050c0702010323040f110d06050702190305030c28050403020310111803 69
    0x41200a0085584420308210880035030003a01c60040c1d030051080400c1100c86010600c1080030b00000c000d002240e00c45000314200c80e0000d02041105c00001c07003a8080040c0110045004045000042c240e6261901e00300c1c040c1030b80d00c09102581401030018442e413540001c25901199440f00407103450303a484079641c10091400d5440c40481d4441c00c0d109589140d8005c00c00c903061809075080e6000d00000c6174054079001c00c280300041c82090510f26104840b8034508202504602c20300e0092201e1881c0c58500b425030f0130640b2181c008810001e8a0000c5603010300c03800000c0e2441ca24000c02046406c9065901024000e001800000b4108442c50801045004640700d142d0020282904402c4504200c0020300d0200d40b15000b520600512841c502c0101f031a400f07005034156102840d5903200031540300190041100c00d400060181e449201d0b407042d40304c40792000e11842ea55a521946540100f40c0344c10040c01c007411001d80340c0b46031454034445882c125070800b0104960300c0d18214200d008203180 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 68108114 1250 68106864 68106869
    0x3020706260f061507020607020d020f040903050c1506031c110105100e0106020a0b061201060b040b0d060b0406050a03020a05120f0a0606140405090408070219050a06090302090718 79
    0x1103141680410400d0390031502c00c140606002c1d200101032400300088842c1c203101c1d0f49800381d405042401b100006140140d400f480e260700c0501080d1111f68294045001d8032865141100450400300e403441c00ca4104012300c90340d060050401d0200e5003030100119481700d407100180415100c000c4046801c41e406004480c00d4814640c000b00114648100600c1d030f150103601407c07001082000c000a481880000c0c4040c0444e000b280b134010580f103400401c200a10780c542c1d041d40c07a548619000852019400152008000e545469680c44007100e4901d0100c0301c03a40c00442c0c05000070300c82800340541c00f20a0b0360002e402030400595a000e060001c1c0d0b59406151070005c1c417000d2040401009555480c041c9004010310311003440484d4407810107a5a42c20103c43c8521309000600080015140c8840a940c0050140d07a5491502c20160003081c0384803840403001a458200c40410031080c24002509002807003079141c40b1140608603400115803c4002d0400d00400540c000b04040081d00e50350717401c00 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 68109364 1250 68108114 68108177
    0x1170705070c06021b0907022508100b0f1f0c051906090210050a14160501090804030507080d090b0901020106260610050d0308070318030305091903020706 68
    0x641d03c1d40020342e600010003042c1603080c0c03200c00d40041030034100b42e0940142600d401410180c0b00840305030314441c8000107100c49000380d00200182a03441072107140d4110600350004102e000c50482070003002c4c4400034601d4010300c0c89420704641080700010682c1c00301098a449924100303141041340c540401111010035044900c1c0f0100c0c2042150703481908001c0c82610b82c200501c881c25826102ca0095160010105041c3c1e0008070745904004010541da000020003804040550703212542158585c1208540d108400242032081c40400c000c3e18009100e09402441080310726840140140454814142809030100300c16416a000703400c10805410100e1410b828080301e04010000c1460700c1c2203e0340c1c10b0103001c1c041450070341d10310304080503640d000d0302da07006110203a9801c840102008000e54201980d0f00c481c0b003000704203440f0000c10513002c2d6501146070b0410340d49080c200b41810380400d14810811904030006178000c0f07100c1e0300f19603803070415010001c500f0040c0c140c0d42c49110040c20 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 68110614 1250 68109364 68109383
    0x909060420150a03200906071419020306010e01050607060207050a151a010305041e05070902030406020703030b0105161101120204030507090e1f1a0603090c0f030703020117070507 79
    0x4001c44109010380218016668140003217a96010058083c12680d440c50961000c100200a26410320070002c00e2181c0c4542d0292010350031072030055040032500503968405459403c00401945010040540500b034aa4a521050351401c0c00007501131184100041281d0b4011502c4001d10000780800050b00341c100c40c070b940c0800da0a050440060016034070380e40c2000744903100707024035504c2403094512031940900e0661454440320030310030b812510341208407420301c900c100204076a10a400a1800707244100c5002d030f1034140600d00a8103451031451101d04101003800b047c21001c590b03008440d425600810070b842844c00074401200c5056000507911280d60000500200f00b000c00038018040741c0030000304120416800c481039440300705c2a20302c100c00c6003c03aa64040411059840344403a00000390700104101081c1001c148650006c0303030002c0450f0040802522941015000707a0300c0350000300d014100b41c80c01d55002030f2075014a90007181001c801d02c2c0002e640140114201e840c115002890031 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 68111864 1250 68110614 68110639
    0xb040504060e060a0c02060112060b03030705010209010201110304020f0d0c080f061510120c02030403060c0206070212030105060f16080403050703120914060c010f02041509050909060420 82
    0x210301070440385803120114402d110015803641030302d104500091700307940c6c040e107650703441e000b81b03d805d0010101c41a10300369078403084501140d50800007401c0c5548640005600d92001000290031541ca5242410b00e02004000b004010394a5410030b80806408075078a00350214141002c0b06425015000340000e40719284507910342440c0050072903c201c58a1844404205514060002d101c2101e18214003181041d07100080c402c00581051f0030240b0584100d030304060f079a4842d501540c80350050400960055810f20690a606111607100703005400001480c6514101c089542c40c481e0a84410300380d6408184080741811542d4400340c0136401181443c0c40d00c1d202c0c2012911000d092004071a0f407c40e006c04c000c5140c0c0180050b00c111203c07010915101c00d842d00510100b82c2c0030a000082c80c2d561074510030126240340c400b80000c0d01101c40c42c03038000e520070400a0001042d5401c0703507202d00c01d07100811044020008005070f0007580090541200c040c0c07411a80d0030006100c0e1826400f04925120 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 68113114 1250 68111864 68111873
    0x613020105070510020414030106080715120e10020406031404030914061b030301240203040306091b0602070602190b0105013c0e090708011a12010b031b03070903060f0b040504 77
    0xc80c5007c1500702c0007000100d0b520b950080da5509984240b10f440003684005000d1b050040014010f142003845000c0f820040c1c403603000d82000c1254200c0035100758003090a01c40140e0500c5000c215442c43e80b9004d1250406072000740905a60b4460620b07405840c000f80300c8140c5640301658055241d103190711004160844580e5100d40007402009a000c7c42880c4812003107540018564003040e280e0007851406042d80ca071940a401e0303180303094819443c809081030090000d100040000c0119038060004107007030000c024103003081341c80740c02c0c0c4000035000c090b808240300c40c415904591007400e00b294180554858040009043c3c0f20fa07044007102950804d603003007103140481c0e500c107040b03503140c0d104541200e0030800042002c0d02c0e02c00002c0e40c001e006004a8410020310810840c0d59600507041500c1c00c04803003900070098100000c500360100501c07400801619000c090942c84007031550551511183c0101051801d200113401240c40b21864140120158403040712241e01030020701040c80c050a1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 68114364 1250 68113114 68113139
    0x509010b07030809060420010302070503030a060e07020a020310020306150c0c010e04060806040b040302010231120312020d02090402031501110610030f023d0206130201050705100204 80
    0x800c0d4049058440004d6101d01c0c04580b16100726808060511000c0961500b002c2c003c442c1021103060540c2044808045441080518840c2c0c01d01c4c00d000c50440d040540c0d800f04c1110150100d0299805201c407880103a5002c101c0c01d8100c0450310300140c03242c0e82c240001e0005454468081280603001410810315200440d000c00d9044c0b081c5c8034016031540da24144411600b142c410444540c02c94804100000d10926810717421500030720001d4203100300c04011003512461060070101038290307220681c41200c0e805038030340020003541429203c51042c0d51005410f120745808141d05c0954000b8460a43d41d802e0b505648200304060300c11910380c50058003034201c0f0b07a000e44070349020540c0103014030007031032000072400c1c8101346900c920f58010780303190303100110b512640d082264041d18410001012101c12104001032011160b159022100c80c103402042d0a80c0b0034000300c04541029081005a0b55202200390301c0384c1c2d0a19065a9840c900c1c00c03c10b080c4400d42040344401d600001d40020507040840 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 68115614 1250 68114364 68114377
    0xb0301120c0e0411040e070b040f180207030203030105010c050f060f0702010b0307060905130f11040512010504030f0c150501080c0a0b04080a020108061516060506120a14070509010b 80
    0x40100700c0a0b1108030a4070300000850700240802401000d004090800d81c0003080c1046814003200c0d84a07840ba048103481d6005600001d001c3e08144004100c0c4000020305160b103c1c800303c104502c0c3c50110b8030001e4407444140905030510030a00703911402c1003800c00813002c9840292099030010304096140404011003510460015802c00c2c0703a20b90507280108007001100c40c5500c81503407661501081c000d400c1e44400011600540c0e0b8402c4041c0000709001d022804554100c40c01d0ba11410b120400222805100d4664107987c5040100400240c010f054514202c60500b003038075440303500d0300d401a6420796003003009010504013800002c0c0c4031400078098460103401c81d41060b0450f201c0209d10f54074040c510031171071107a0100da9198003650242c0c0c0035540096000e4400c000c1d00020300528003107640301401800d090040e281c50941800a581301d515040070088a0141000030450603996445560749005884040c02c640007005082041141100403c000f0b0070311303140c9694a0316240d0340f40d00800d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 68116864 1250 68115614 68115623
    0x60504020906060a020d0f020102070c080c0405010b0708040b0d0f02120108060106020d090509060d0209040c030b060f0d2a0308040503120906031612020301090b030c040b030a02040b0a0b030112 85
    0x3030108407180341c164140e4a85106613802042a80f103007406c00c4a0a810b680960003d5541c05c00c20000030840c4c4c25144800750041d500180030071f050013024001150030592121994880511a0030300140e1418125030880d100b00f8402503e0f039003c407602c1c000420003040a0902d6520002d0045150014070301002e049403080c809079039251b030f40d03050b050f607c1e50345e10b039180c81c00a40820300c103200a180680c1000d40102000d0310048400f650b42c1d011903180d22050741c2c16140d40156803410810000a4100154400c405603250340110314001c004c2980c0e898002001070a0359005004102014851000b18a0080800c404182c1c500d40da0300b88078a40d540306000b8a0301a00440d00c00c5411410014215050480301170f100c1ca240d541d4412003040b0102e4810f0390941001142c04104da00f0305210b001a602038011028006a2141400e0806241000000940e800366060031801c015980d8003060118085070107032804240c44294034000b45410846e500843c40350600400040703240741d0902c101001c82c9108 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 68118114 1250 68116864 68116879
    0x10207051e0901150f030915060b0d061203050403030c11041508060c041d10030506390d09020406150305040507060e030703021302090d080c070902030606090d1e06050402 75
    0xc601e610b4078013a084441d090049140c51051a0203641300703038441d860050040011015103034008289805560243d4081c514907030300070a201407200703007601c50007004102e01d050605003940c1640c1d000c5c3c400c1c081c9200140900041c020b456081c00315540e020060418028000c114140500c002e03400201c01d11b00924030a4401d000011b0031044060003118180ca6824441d039441660308065290070150003004100030f0562390341c00200040741003100340d004000a603400c542c50340e202c240014200207510710360528610499048180340c1c0203c02103d807440b503841c2d0041022880790001c500607000d10f62000409000a00c8283e0450342d0540c0050f001d240f2039015580314603661131048a2010f65512a2507041d00b00c2f1604100619280c0ba0040c549503001a015040640f000001175030240d2141e402d907824200012480b18019003803000714081c0c4860441181142008000300320300d400740800807801007500854560500010513406802c6d07441300108001d0b130180c1c51034010054203041d45c2c12030084a2 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 68119364 1250 68118114 68118119
    0x1605030a0912020901090506030a050f0a02091e07030c03090b010e060a0b030c0f0306040e0d1e020706020a0210051c0f0606030506010806012003130e0705030103050a060209010207051e0901 83
    0x30b0550385101c50395002021040c0380d07401c00980000620f80601aa17038184513113040034002400c1840341c8203500300010082c280000345070050003048640200082c11003042c0b21880d48408800c008920b8000503c1d150006441803001c500350b00030542114050061030b0502c0c000202c0d28580e80980e4403862003611041d0a999031460400601c0c04143d0b03102e10841400d04c801c0701c498a042e03000c0c552106004001040d080c058250050801c1300d442c001500003003001d940c280d190f810746490b544440c01c05100400308240303404402525000c0c0c450000744a031036207030001c1d0001c5100d03800340c81e208842c44424401d00c00d5102014001400c40d000c449440a0401d08000340190003840340a10907e01030311032003200c1d40c4803401116502402d84280d1040000302854201403002040640051070704141100a254103000700e02d00c0e840c02c0103050008006007000184000b07803002c20550070b05a0f2285000d61591341c1c0304010707801d042c000c1e0403041d080705684541100d01060304007070540d250303026134805550381d8 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 68120614 1250 68119364 68119379
    0x5040b0409020123040504060303050c06180703110d170304060b09010b0f0702121209131a0d081204060207030e10050f0d09060513021e01090308030604021605030a09 73
    0xe21001c1d010340480ca246182491035080c0c4410740c640c80c0d40c0d254501c1d2034141c8440000303044400700d80043c3c0004030040340e480c1c0408001c00c445500031048400b986076001e0b0440e00070b556400036000080040120900d40395440c0c030360505000005a000c4c02c1c1b42841100c0b180120b4030398008580c02d43e0450704254030480c4a08294816606840c099109a4a0142558450003903030344207907003c81c1c200404904400c641d40052104e81d000d415030070382555940d5081001c00c98101429084104a58940441c5031860781c101c0600800c2c000040e14403840030300c80c80c1040761213409085c00110300402550108410451158002c040b80c83c86034030340b10740d604210f00600621140e0004c400300803c070b041260b20105000100a132144105403500881d1080850307072031109540040d501940725940b00280c01086140c00c6079000d0404846144036460f6280580000303240c0e078241c3c8805800e00f1400408919544c8483c0c0403640148010750301981e10005501c1d00558035072201d8071140005a00200104001 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 68121864 1250 68120614 68120621
    0x3060c0703020d0c1103070e01090b0f030d030e0f0d020d0f050a0804020114040812070c0803071707140303040507180e250e0a0906230f1902070c05040b04 68
    0x150075900070b14a0b04000b840a8492003218403007035443e545400c18083d541c3c1d40410003070740a0960000c4a52242d450600c2080503100c3e80e4510901c100b04088083c1c00903100020041d105009628001c00c18a01c424500c03401c040010251607007500441c1c08018a20303030000350041c401520366807114200b11030350700b00700e91900860301840001168003020501643c0f00740e10240724000144590f0b441c04e95500e15a918000c4202180e042c1500c0100701c450510428030700c418014890480070b1464000fa0340d588c44416800c080c041b26101a001c203015091040502c0c00700300b00c00c10003040b40d95a0510741001c660f5000588209243c0c42c0f604082078030403041c140650205040c100c002401030811022490482112103100004150311070300c400142c5082c3d019009018891069001500c0c0c446424810241c4003448603190b00b201e04003c00740c28024904000341d91051101004050076100c007202c0d02ea011010065801056001203810006d2007030030691601107800c00c81d01004007129081c103100a4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 68123114 1250 68121864 68121877
    0x16030209070807020708100603050c01020105040804090e0709050a020909160504050d0809040c090906060302030c070f050c0915091e0c0310090f0c020c040e0606060a020c04020403030c0203060c 85
    0x2100c410125030428001c9040680204003801981d9007035858550741480c290f030030a02d0710102c03030700c4840400600c0001d02007510102001e1000b84074a180c142c40c3d9000600c40e80c031501b5961076544140a28005090007407902038207206209008a060070700307461029400000000d44541c00041c00700d15808c00340340ca03c0002941c143c4031315080030714080030441d0000300c2c04030a032038030316082103481c0312a034813407240420021041c1c44114980d0308000e204000c580d2903812005c203240c81001406404814003041d00d100395808454002c0600c0d852402e0390510003410f0030755030000f010030709111512803042008901e600041d0307600e0100d50381d01c101e20758a00904601142040b101078000c00c41d1419440025940840411180540944d1391102a011079140300b100c048250358800c82d0b070890990600c02d20314051800c441c10701c45446880708045d00c649001d03021314800c000001da0413070524000c1c45501c0074032000410464a03207070380e41005040740c82c0d0f50500300d01c03a01542c00000c008503410700c1a10b05 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 68124364 1250 68123114 68123119
    0x3090e0a0c090506090a030b130302060a0203010b0d020a0e0310020301140307031707020114030a1d0d090b0d09061407170405060a11070b04050f0607090803030c03130b1602160302 79
    0x58503c0c0a050110540c003560b600c5800a0781c010012010641e0025014060b81e2904203a914086040c18020300342070001e0b03c164445030041004020611800d0700399940d909001c00010382d03035419500240c0e243c60300e0240c100c0d0075004030503001d03a8000c0c2c168042c50407a407074414001381c0c5c20b41a404140e21088540001840440d921407030f11840ca444201401410303106050041420310780140306c008640003104d10950168070f44410070f032500104240ca0340000d520f2401409034214182c40605408400c0c016140c5003040411007241524250b04002041a002071f0100580683d810500f1100ca204440030b0000c00c0106640701140c4021240c2d05d0311031500300c0d0150480340c40d145040c40140070380905c0600b00326410320105010941c0703200c50728002d51080004000d40c0e039015082c141402c0009040b0818841805d070108960000801200da200c41201103045c0e4039a02c41010300414070071b50030003038980c07402c0c8400c20504144501030019001c2c81902228400701e00d000001da080f83c00703401b00a4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 68125614 1250 68124364 68124377
    0x6030312050c09030304032d08030403030507020c0a0b0d0506010203040609140f04050a0f06060207060210150305010e030c010b0a1d0a0e030307170108010c090e0a0207080703090e0a0c 81
    0x5080c056901c115044450b4410591512003030200007403030346d08550030650702d45141c400403490003e01d60f800726050100c000c000240c80140b82d121050715000051014050540394800200300a100340700d468040310000b0312500003140c56899070242c1d80c202c00c3c0d4903078619103001d0100301c0070740c0000240d03000c840240d52440b41c0107040605100c07004603c1020b00f40c20205400d1403c00594460103958802c040d54400011b00f044800207c074240c0302c43d5071010065412152040c044180d001c50900c03079429a8100119051500700555201007825038005440e40d46490f80b401a2104080024440e0541c000020f0207030906040421a55230b08610440041d18410f2214460600e24145e41030b5121074242d4000903001051401d07281103a004480c140009003031050501020261005960f0162800c1030080148000340c80300940202040d005042320840407a0020741e0f440d02c250101da24451b070044e103603501d0780400d1074041c25a07a400e001e10b084000d0841c0c00078002c44454800c1c000754101b03583c0c414 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 68126864 1250 68125614 68125637
    0x702011d0f0111030d0203070507050d0c030e240f040612060602100f090b0a02030618040f0b0606070503040905010e15010c030806010903080f090909061b0a121406040f060303 77
    0x40d10000001101140e144c00140902540d01c1881e1010b50310448207a2038155440041e0314000d402c0240c900d8500c000e0259242a40c00070990082440c03098400540d0b05e5a5840041c664200c5100da03e20381031410641c0018841034039014400140041b501a80c40d00703440c9100c045081c03030581b02d5602800700103900003011007103d0380c0290130149000500890005c0c072000313162600c2a1003682152814140d0303400105100450070302144081038894919120607060070b00340d550b084240d001d0f0801502005001012910965554086800300c0741c0c420216039450f6507880c2a000030f0002445541690354000c4002080c080441d0b030741e0b0688940507561b01c94440829902940c5104028040e40c1c10049134120100000b21100001c0c40317201120380c10a601ca045400401260100046c509501d94100c4018003a40d01904011038200403400c9159544400c03d107001128080342c41690300d0106800c12044601110761040d000b030040c0c1c001d650501501c542c40d0480002d5540c00c1c40010009510540c00 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 68128114 1250 68126864 68126867
    0xa0609181a0702031611060703030e0f030a090311010302040b0a030b0102011416230403050a17070b011701020d14090f0102041a090a1205100b100801050609030a0204050106050702011d0f01 83
    0x11003003074a2144603100e11b400341c40340200d0480d070012441200426030305d500380e80b0303258001c00c660303103440c89850002c5140c0740300340b003000b4071220851100070050103501c540c08001d07a0180d0180d0780a008046c1980d9110030722079000502420078030700098055403030826402840199042503511441c5030031001c1d0301518000204940001c1c81202286080004400640611b5072003401400254080ca004006080440c10a908030104840d2038001d50f441c10881c60000401240205044a9a58140036242520b071041c80340a0f10076a240c40580901d04000f01c00f49140c20445030340a00e039280700b2141d10042c0c4201ca82d0803071299004501c1108513041c00d202602040340000d16003048040e2030004144d40c0d0347c0c2075600304420000e0454081e0402200f42c00b10342580d12071450391003011140302981c8144407001425598041c05040c1c010000040c5c01e00c03140d1030800400b000c41d903001d00100019039403000b004082e1f8004100490000e24100040700224419030001410031000411010800c0540c400 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 68129364 1250 68128114 68128147
    0x30503040b06010c0b01060302040816031a1306090c0303020d0e130c09030b0a0519060501140d09050d2006010e01051002120a081006020114010506030a0609181a070203 74
    0x800d04001c022040d1400040b180e0450a001f8216a2009030311a820106094103018802540852842c1d000d002000454a010700b00541548901e80b00c1c044c503100d401c03114002c100d0290000e0030503420314441c04100404404100304503802a07090b14074540c1c20780d40407070f8501c4000007456807000100d0101002c802040c0d01c891440325507410704241d9566203641d101041c80c0c04540c2008031541d01c00402c0074140255084d1100c061010b001006500d0400340040c01010b034451660289103004109603842e0100c5074000030603d80c01c2000c480000c001640300601c01008075040422044d402405091350901c00240039050b10410a0300c0138042e800c01e8140480b20075001000e4045114518480907107040f03c01c02084000c4055480c0300302807500c00880031142d95a680b100046a03d44034207d014066208800360544104a8056540b07881e411a0f002c058219604060342003480c002c288422115070f414000c20451003030302c1140300d1824070600c501d2807050484803600540c00030424040d00d44020007 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 68130614 1250 68129364 68129371
    0x519050702030705010f0614011103030f1519061b05060a05060105070c060201050f060d05030d200a0203180409050307080304033608030406020a031808031216050304030503040b 78
    0x81181e09290150b02c85500703555a2284030180e00d42c1c0c2d07200a002c01c0010b1b26061100ba4420302b0241d0709000c200d08160303640c1c40000c092000c1060110007051824821181c5030714103c1e8010008208020044190a10904d280c410400458580c40101440712940e64850f20260b4010780035180c2991100948030107001c0092000c0d040180070056840001c141400700c82c050f104075400011640b07041000510800d0002d424980300f65004107081c00028400009c46103030b40520705010810351000300c40758034001409a6989070244010468003100d65000000e8091425908204a00600920188070131141c0e05070340076207150801c20296010a4500c002580c0007032013468581c010405141208890310302d00f82ca0740100e1200840e1506109050300d100c600a07110030806541b1307040c60400301079513400c0c049400900f440740c14a401c40280c10a0000c440040003c0e00a41c1d0b23450714030281200c6410400c07107c0d022010601544031004070310810589208640c540c680c181f030740e12a03031100400c40700c004 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 68131864 1250 68130614 68130617
    0x206150d030302070228080607020303060913030e030601090b010801140d1b030606120302010b01030e07050111011401091b05031005010507020f030111132c040c0b040609030204060905190507 84
    0x2900c04441c91b886003120003000d031082c484290505003080401803e00302c0c090401c0c3d003158000e2003445504d81d0365580441d00b03c041c07242c50041102e03081c03030705860b0340701d102d45101d906000310000014040040e0300440400da0003660350342c002d41c0e20385455014004a8003c203580010109010340001111100c03d07800c5441c1c00b08a00c03550503501d075904000c2c0c503915000784181c00740c5500d1920803d602401020303401c9409003401c0c400380c123900b02050358600b501d10500e8104601d0b4100040707003507000c0d030051400c241540d022820035a143e8143c60060440411a4070300700d4801d5080891262240081e07a02405080141b4105c840c40d1000450300741e040000166400541c5a00b42e201c01c1d5801d2084510841510f16071644070400c1200540781280785038480180300310214854410004503d100b04804000703a1540b0720141c030355041c208410308031504200d450350000070700402d40d01c2c1c21080c0341d412284215024006642c0350400001540c0c015034098814100004500d2807802603a0007030f0f51700040d0b9 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 68133114 1250 68131864 68131879
    0x3030f090902040602030a1403060f0f010e030102030907060e100f030c140705060109060803090609060f0412050c1e0906040b120106091a0d02011e0c0b0702010c0206150d0303020702 80
    0x190030300541240d2150f40184d015078000980150b8041c1c00016000040c02001a82c81c2940b13801004652100c4a000707965215044609040400e680103442d04680f212000d4021516417900f0b0085030381c0c42e0f82c60300881d404202c051040c05041d14100640105a01c19503a4549914250300382c00d8014201c0411405c050048030410040500300c44e601502080b40101300a14003545420300302c00481d0582d030862400c507003041160020b603032295030844100400c107a8006a5584c594a03510701e66010b82e0304409032007030151111109000b800640800800d41c100c1c5c3e440704420030146041c2005012001c843d8200000b607001826502d0940d1020030700d1b6001405034240c21000c0ba0202d800c40d0072540254101d19070350042d42c4981c1480408801640380c3c240d4865000c1c000b2500080c08924402030012241e00c003400094480701d22038001e41d00156401203a082c11400c0c5501c0c040d02a0020002a000621540c000941280403804205079407100c054070600640445807012030182d44507010580c0c20854 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 68134364 1250 68133114 68133119
    0xc06051012080a03050a021e0702060d060602061e04031d13020c030c071505030f09070803031509090c210309100c120f091203020a06050405010203011d040503030103030f09 76
    0x125044030521078000c20342d45066035030b4084c007215800740090010910520850b04604061030510b0b800740c0c40c3d40341d55500c030092480050900d118034031034100c0751410440002000c070780001d03016001e881008210503003040d9108010f9100740d000c80e03001d000505039516914240682d00100442c510303015160113080b000e4005c1d0354007a13030701440000702203500018a110b840030b000d12010010306682d2410050b045134410005240380406000300e6903003600400032605810041000400a010030750690752240381c00d8081c041801f9401041030300428030307000016105a80494100141c0d400107010092035400c0001d10701c83c00710584602042ea101c100010034807a5941c1100c2c0341d10b0219070742c42c003004c0d503a586420006426101021780900c001440c880c80520b402c1001e04060714020101500500c0b01820300b2482c0001146002d011036162030b0600040c8001034000314161504100d40101c440051080442100811100901103030414401400024450381280d2100034903450051346d401e4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 68135614 1250 68134364 68134379
    0x50f0105040c110a230a050c270c090405090f0d03020a020313030b061f05090d030e0904060506030c0607030e13110307120c050a0e013603021806010c060510 69
    0x4031500d4054078550000c1d851242c8805e503014240600011100240140c14044c5d607031182d644403c038500f5441032a988101040c84c19082c4100c0d41001c032458804d0415040086c0d65182c03641c08090341d079001d2410107001501c2c0caa000070f0811201d010034402011030030440d1808800a4200040d03243c02c5010411031240d00d640400c410202035405030411110038100301080040d24030340500e901d0121107103d41042c074500d07040b40940b004107405035480003920003107241c101c0300d102c0c0c5001d403030380c0c41210a03040c8014031806522081c070440040e4100c803205001d0508200c198010f41e02e0080005100f510050182e05118102116200070481c01045030300907141980900c2e0021151000012a40100d040340450a409201d90100e40c90400a1501c030310104020b10801e950618541400100b03415420b803a06617007400819010f06403c03403a61140c0c50003071745e0100e580c18442039100e5892031138980b40e100f0880d0225400740d0340503150790414203003a03034551002c2c0c14000d04440003880800000100e00 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 68136864 1250 68135614 68135623
    0xf04110f030105030d0c020d14100501120201020c06090d08070602040801060611100b010e04020a09050a150305060301050c1905041a09120703120e130e0d0210050f0105040c11 77
    0x10440c5101440d207035810300c014949004100c0020700f041020301802000907031620480c00c407820b50401e640d0290020074400340c40c03525172020001c0d46624548000020f0501e100a92150800d10036825101c06039120780c100301c1140034419049074070481072074400b00000e020000070400c0031b21400001d810301d942c40c2c2c00103084880307a5000201186900500a2880b05d05010300700e104400d806080140b0524035000901030b400301021b031030140d640012882c00c5a030151603010028107004000440d02d81d01d4002000821040c005484082800c15000c00e2642c901070183c14414441d40044508241030390600350301403072a56040c0010300a0810003c101e002c04412200004904103160700da48001000c24404181c42654500300c40c1c1d000a00f080c40002c2950420008000140c030300004000e501e40c00041c2440d0300c801418150f1460501208007003040400c9814009001303800707464400d02070451200c1912011110907560b1403024005214038076160f402603040040b5031500e80f14030400800301c1441c1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 68138114 1250 68136864 68136877
    0x7062001050c0a120504030806060a02030d0e0c010f110c0d0c0e070302040510081303080a1d0604030206060d050a02131121060d0201051206010c050a0c08010b01050c0303060f0411 79
    0xb5000500402d8154000458000e01412900d00b002185000c1c0c0b00140f280700007500c010f104400026200d07a92503c208141c5801e00001d0200b041440000c00305996120541c07210700d8049082e8408181c5024040d60b460a503803a501006801d5148020040200c07a00200804642e40c3d6500c040102e6072401048005101c4e4010751001132381d81d420807041024012402a0000030030880c0c0f81003190607221007405000c11a810304200c139841e1106107100001d0000741400401401902d45e80250108001482c140641c1c000d03001e55a4a031150422300c1440004100050030641c41081c1e110700604104001c0310f10302d070308003c0c00160060321031403000b2140e001c0d40d1048168001c0308011540c03c040300c0240368204c01c0c100c84810498803e980084d1060154201040b4550600f2000402c20790140100d181100e40c0641034582c0c00a80307217803034540701e03400d409101c126610b046615451540035030221405a00c42d1001076045036148020490400007100020f6003094a601c8001010300023040035181 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 68139364 1250 68138114 68138131
    0x14030f0709061a0703020c040905030c01140a050106020105042a0b0301031209060801050a09050402031c090e0105030604030804140a061a0f06040b16031103130816080706200105 78
    0x580034900150b2408402c810f03100c00322450350030090b83d40000e400290f105448a07040c1c40200d503418207814140d056010304d6881645550801c404540d914603e07080b01481222422800c00c007903602c48104030708032901200c0c02040c0b0841e802002c603481c0c205500d01d0b01c41a084079881d032005a29502c11110a820a9201700c4d02c80903080001400590441c0c00c030001340001d0301c3c3c415011340c580380c0014240c0c011842040011035689000c14150346080c000c840c005081907204840f940200300e00207161414a03c151690703150b08500105003480c002c6815405541c0690310340402e81c44603110f45400c0c0d2032802c4105c816209000209001503194015544064403000140d101a2044824820410340c132401e01d82c0700d000100020f2040c54100c038140c41810310f00740382c210000d00d00c92a0035504e00451140c403080c20301c4040707400040801c504013444240d5802e00c06988a07411700900c0c00b040c0c0070f542e0003191100e4200c1d030000d0024500c0f41c1c1401c042030802c69101403072402c181c0f05a6003195002d075075265 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 68140614 1250 68139364 68139371
    0x120c07060c09090f0507091203180308040509010602011b081302090109020d0b03120f03062103071e02010f0f02070b03151c050c061c0510051002011514030f0709 71
    0x111200138856030040380d107444024005460a14801001041940a209008000c07081c41d44181071061112111014400600c1d030003054407410011a140c2080c46400d2080b03009800205115106003c0c025110341241d8001030044001e0300b041e20205002031210800c00c01c600e41c05c0c03000d0307030710105014020001540300580e520001c800c1300041d20f002c4100c140c001c0e80303c28070055600c2c0b03c4900301d0300541ca050503100c0c0c507600e500c00020f403158107044552404c00301a400d1184100001301c010201244110b00c084003104000000001b007510080c03010b80460345076108050080e0244007040903010300303031040e500d007a6202c85525540750000c1c0c56480d86c100200030801c00714200403402844020461040d807807034090039a25140d841c01d491801c0d13801000e01144074941c0d15420341580c0d24500d5100c100780a40c0c600605078410206c441d10490740f06001c0e00aa12840034010b110b102800061300a03003204035400d01c200444030402d0f03d080300f9050301c01d86000340c0c0405030a00402010b02501800803 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 68141864 1250 68140614 68140619
    0xe1b1302092e020f06010314010b06030108070906050d031d010e0607051b0616080c0c0a1205010c0801080307020f0324071215060e031c03020703080a09030203120c07060c09 76
    0x101c00760b01425690a56105080710714000d00005041070443ea40010700b4000346200488003400740c41c0c15422180c00080100004c250b031400404e0a078103403203660350100041581d801c00c204001c000c525015010a2021310030748000f0101480508005c0d0701810b00e501d01700740c8117000c68003a601c00b00090750300d600200e5540300d00440c01c44021040705411118241814905900001c0710009814002c1c00f0b0b07040040d80c40400601400355100f01000141000c01d42980c40103480e603c2e01d44001c0459072540f0f0074030040751050069232824182c1c0d45400046040686580c28031030390402031011640d240c1704002d01101e542da5140212000000d03034a003211410704018034054042101203410450650420640105070f00c05080080704a4401d03140889a0441d42c5022909115580500e050a400380740825a230381d0307400d03030020200e5038401d40d241c60b620381c1d460741b5130012981040740080068200b0000107404e0304081040e00c1d00180e0b66030f510307445d240301e07a03441c181164006012900400c2d42540f04 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 68143114 1250 68141864 68141929
    0x30c1805061014070c0e0112050609010c0e04090f1401090209010603020903060a050402010c02090108010b0a060302090d030818070905010504141308030702030c03031008010e1b130209 81
    0x3140e801020954040c1405020b500c0041d0407061501100d0507040000f02e050024005040250001000c0120440c003c03541c49030040ea02c040015070b4217449500c50380e404120035140500c6501540c00302e85d604e040d003502e0502c0411001d0b000d80721081d00d002c0484091000803601890b1810744600d82c580000401040c00d20500c034608c18164403043c18903106000c1c42c8110784021446e0755004800e001c000a40359110f1006990207003402002942083c424000803800050551012142c12000c5421600b540c0d503600044059110740349034560080980c0316041c0000e4040c100e40c0390001000c001441c1050031119010b031401c5090340c00010042d899400402a030b00b042e200b03d50b5614211020854146850300701505424070051005205250010000303000c00d20900540381c45820030300550381d4a042c05041140ca042d40b40c0600301c225480e12480484c9100c00242d103a41da190828241e030704c8020b14504000d4000542024000131980811203900295110703800c2030000600000d468034951201045d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 68144364 1250 68143114 68143121
    0x241a0108092b030618060e1f03060203060a05060f0d050a0e032a0703061d010207030210020f0702060c0a032003040902160614070206161209020109030c18 68
    0x100800682100b01c1d80700416184840041d07001c00d00a82a65828030b02d80b5003180180030607440041c1d811903110034540c0c1019150403550442e000c0b000100929182c3d450000042c4c85a14400c6180d0303000c011007000002c003641c0141d54440303001404c0540050755040802c100d0340c4001202c11000e100014540c041d2821481143e80000024408120040a42d05940c0d0f40e8422100007178148403806100200c150310b05940c02c06640070040607125110343c1e0740391900c041c24130350100f860401401003210201c280c0520903504201d4059000f04074007020014510700940c080c805841480004010744000768640c4802054080c191000401d14103d540c180200302408020525028428603020004110000004d4030290b8158420050b61384100e40310b40904480641e500400c0941000c4119500d040089a441e20076403840d000d490040d59003091040c200c5d8540380c0d0702ca001c00c11440c998049020180e11085d003051041c1403c0381000e03141d8581c8240807409a0181801014069020810010a00 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 68145614 1250 68144364 68144371
    0x10c0201060302060a081b1603021c0219110d15051f05040f060801090506040302120408070311220203070e01051c020c0304090e03120601110604241a0108 68
    0x200800c2480c1c01c50780020f0051040340140420000004007081049040340c0700c111210081502d1199a04050f8101c0c0800c02c001f041d06a016015020041d091148089018144480154003902d20f221802007100c0540800d2081034608215900014001c2d880b00420308296501824038103510085032000b82d815600010070301090080301030305412000e91214107000030703920102e0707010400c4071480704a14000c00107030740000040d6080c24920307004e000c00400e016001e140030740e003503e0305d829501001d0403051155108110403980101d00410104002400d40c0c508100c0042038061000e01c8446a0b486c07043da440808603109600000340441c20303400c03000703d065a007000e081c01030074241a2441a4281d020200c42e03402ca254000540308201d80c0b05108885c00b43c0b00000381089102c5000d81c1c0d071652a000840e010300b210b41c1c1a00464001d6000b000c100c02030740c0d091802403890b80c1c1d5aa0352802c0000c3c039070b20300380c110344000510128804254010f03900c50441150105610748000b00c001464200040c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 68146864 1250 68145614 68145617
    0x504030c0b0c2808040306021801050f03062101020a03050708090f060a0c030603080a03050f100506090d06021b030c01050a05010b03180705061c0b040c020a2009040c0305010c 77
    0x8000e030400403074020500d59800079000d020054200350000103010251644280282034604c005404400c2142c50b0b4003500300c1b554501c10140418011500560b0148070302190810700305411320000d0035620b024010002080004000036121201d80542e0500366003083c2015008261658104000543d000d442d183d8003c464400501459807100074440d120b01000e054520599210b110201641e4001c3c1c101030020b691203082c0a503651020500180181000e5402d00081c0c0c0c4a1b1011403000c400461035a03050352001088039180000768030800600d9140703c0310481c6c100742c0074054480b15480e04454481040c0400019598441d01f101002e421144020f02585900385420014010410070000750b036400541c840d41480810a0000e0b92480e201a9a01c696440030300050b01c00a20f0016038600896403408450a2182c0c6110004100a4825811180300140d000c1c0301e010002c2580034285507042c01003071080c40307000750b0f0700d070003040e0740b0002100e050f181401040b408008200003480303220f07510740c9075 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 68148114 1250 68146864 68146867
    0x14010b09090919062f03070207050f0a05040915060f03060b04020a08070c0c09021c0e010902060306061c0e0604290a050406020c07060e0a05062107020304150504030c0b 74
    0x1c0718110b0465848a10f03000d09035a60390b0400003000b004002c2004180b16541840c00c1355031049185240541e481119581d005000d42c42000800f41451440700d0781080c1c0080000e01c081d802d1200b400010414064180c030365403080041000e01280ca44142005400781408802440d0305604012054692103044203000300c7c410443d01100940c4208040d400c00000c0c41c202580c9041c1d400d0510b040d462640bc41c14415100140e00301502044002c00001160a00000d01c90426141543d44c00c9a0308244065041072040000900070724001004184030a403404c1d418403091550401c1c4030482d25440d01510841c0c0c4180309100c01e1080340c08a060381003451042c1d1451640010840e01108000a81840c00064489021a00304540303501a100e2500110f0304582c8043d90710b0b40d000b0030003e0850b5101c1e01810480e803001c02c03e4100941102d41c060881c2605070030308800003424030600700000b000c0c0421404144004522121041e00030510690749a4820f5141c50a608060714407021590111291820 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 68149364 1250 68148114 68148133
    0x20d0b090c01080c120402030f10150e24060c010f050106030605030304120303020306010c1e020a090605010804080a02010204080d0518010503070e0d0320030309060a0203060112020d14010b090909 86
    0x5010045901c0c1124206640c0c0c06600ca52001c40e02e41a89404c0000190040c900e82c3d01031480e07a0380c0101c50345030290381d0800405543300a07280f20200103640307203119580d140c100c3c4404405040c100491a074005003205103040e800c25012421500d043c50400740d11501c480040054a501d809900058402200135514252508c40024800c90803c8801010b1540100000e0410ba000340340504807550801ca907082f084101485440302803030101c01c100d100703015190010402100e80e1003014140d0740180c65000b000e80f00c9488812154221020440c11990200000305600109018050b480300d41754a4158441c1d00f0401e0084114a400400c0f90421900703104100380c07564044070b41c0f5440b03c0181c5141841c141c460504950481300047e0074802a0003015015002520000c0158071a0801400783d40e0581c0f41c40d0940d005a02c425034090b070008420b0030040200f0b0710181d000340442c91510f440040c40714080745010300c0c0b04500341d000803400000490300c80780a051036502d5a61000c0e50501500c480d28 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 68150614 1250 68149364 68149381
    0x40e030a0f08040f06050702030a030f0209010c14070b0f0310080a0803070c050703060203090d0306120803180705040c050702030d02070e0c090418050309030d140a030203070c020d0b090c0108 84
    0x16001c80d0404004000c2c0115082c84025400c0600b2a9003000041c000c618044502035a00d81c4a0105000003d1402c135050216001c14801c0c0d891842050f501d002c10080692210900714183c64140c604130f020700d04000501c918100300a0000386081414951240340c0401418081d03181d580c00441c00d07820104003500002d06c01800c4030352103184ea04010410040500b081458042d10b504000e0115100100b07120500c840003c0b5100208001ea405100341a101c501c2801c0e4901401d2004051140a0001c10180100201c044511050960850354100d035a040001c1c15200030f580703008042007000070b81078203604081c0301c8480040c020340010494075240051103040701000400c960700d43d83d0b001c144001540d40703507080398010740010791017505801c0d05400c10540b0b0b03901c200c603918801d114034803011642501070f011800c80c0500e00c50000342411490f4201760040d6000400d58810099505039034001a40d0308184030030058058015000b907490b000300310382d14010040d81010705004210b003c000400 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 68151864 1250 68150614 68150627
    0x61701060b0405220608030d06050607020f06031305070e01060908010b090105011d041509051e0601030b0406150f1209020607020616080309062202060d15050618040e030a 75
    0xd07802500c04e0554403510600002c0380b500365851520045042c000000740011000015011000c0030f03d40400c00c00f56150308000d1544a00440203400c00104c0d014030003a40f610f013000c2c2d64412444c0c0d01c42000c1079140e550301802c081e540e41090641520300707001400307459400601c8074064a1114020402c1c000402d00040100805110301d904100c001c142c0d0303003071201c1180700d20700c0e44c00c002410030301c503295404a0251070340c4514081c840d802441c0030009500111526a0101c442842464002d1507803500c00c01140907000380c00155800613207954000804042284842d400700610313030344064140c00c07082c80003040b441d040004004401e003456410005079540c5d90840b4141c690488800350b50702050b00b180d02000801650260042d2008010400c01500c0400ea080c41420045500a1044070314400e407400b9a54100001e904450184401100409642e000700d80c000c221744040030481d65034200250050344000180b2940701410907010000781407500801d20703908a03034401307542031220a1000030001c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 68153114 1250 68151864 68151869
    0x1412040b040201050c0d020105010503011a330a08100512030405090a0608030c030c0105010f0e1501120e031206060313031d150304110a0b0f0a0509090109061701060b04 74
    0x10014038804581168062000ca031078001152007901c0c0020319860300a0300800c0c00340301c0c1d41d000354240038a48807203c2c0d000c800c82d85c0001c00100650f000343d10b0b203144025640103140c084d00e0142ca00f0100904003078042d030058022040e540e500c151840c40c203420003c041c004603a004a000700e1a8110100350a0b50210a0305c080e0f4100755560700391551100d8002c40500915404419140000149039100b4480403000b044080044c20091000340d07a42c81d00803491f80d9041c45800501002c1350003154102c134410a000c50100414902050160140c24440044030b2448181e0341311640001a000d03803040e552010554042070440304a4118545454805a58109408000c0421100070075809000c3c40d040c9140298500c040c012200240c20110103000c07070350082d6020b0340c804107070078403000f07070b510301015120f0a0390400742c2002d0030b26184620004403608404083c00911400b84400f41c10341e103507910054001c08500364082500c9280c00310840b003030031500d80022442e0741001400d104400e2124102c504 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 68154364 1250 68153114 68153123
    0x6030a230402060421020a15110c03070605070302030d0510150c150207031403011206060512070b0d1e02030f010605131a04090e0c0103050907050d11150408030703141204 75
    0x1150f0845d082c00c1c51085101030700942c041c03680c0c80007040c2100000080400040c0e2138541c88402d200b02c00440d039032080d8280003545c1c16406a83c040c0a2980304002410140784240100c0e8189074068440800742d6034111a04040f9000c0100100000b01e040c69120205805e0740c108070f0619001030311920001e0720952440402660001000c00405104620b001c40340e008843c5866280d58455456079a00d03c0f0302d00303060b15890b0400c1d0012800c0d1600b010701146044003000106030142c6000a904129040060320509a076525030b6245840003400c021510704030404ca10050740c9260100204250800c1030b0024010810240305091a11400f0761090b41515442040300c076200c3c0c0e05084112880c030036078000d5056107003018500f0509040c0024040c120003001d0f01c060029640300103901e50b8421081c4030b8203521a00e0011000041201450030348000741024008551041210740e0441059000381c0c007141503548002020414545c0c00217101d808110394241c1c0600c3c00c400d44c801a00340d402c000e4400740 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 68155614 1250 68154364 68154389
    0x9050a1b0312020102030618060609040e190503040e070201110301090e011e0c020c090601120e03070206161101050922090501060f08070905100e0403030b06030a2304020604 76
    0x504001065031604011039208452007142050320900901031b41054841c82e02800c43c2d5070306840a00906108180324060150246040906000410000e010908000341142c02804072190115102c5204015114000c0008541c0c96103000d0346014298402002402164036051111005000f203208036811a8071464001c10310101c41c5040d81c3c018008408154041e1118103120394040c031507601315058081c0590203132130004120f1001c0c01101e41c0c040784e4850000e509440b1000c0d10303201c10fa000c200900e101c3c000322800c1840c03903404201154012100c0314a00c140c684030f607100708003040240500f003803001e103001802d2031140350204d4a207403c0c0603103410021401e2a0040d507002001d42c8007821042e088402400703819980c84a0141902542c020740ca514043c419012519807082d015070390242d0409040300710400d07c1d05050030545031024000f03c04041e103c2c0100c90319a40c911b80914028a00e01d2400110482003400381042d04102188141c02640082d00308005603440c1c0d81990100d1348001c00c0d22 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 68156864 1250 68155614 68155643
    0x6010f020c03030304030903020306061021090c0807031509050703060b060d0603110a0501020a0c1202191805070e030d0305190608100b0a030c14060408030d1b0309050a 74
    0x16800c0c40010404070b82c051001000300018198841c10340400ca80c002e42c10384d0071548400050012800c03c0a603040049840103c00c0d44500303980c0200d801401c980d82100003040300496507455059001c540c001a41070b0301c059024021b0010b0f2880641000d44282c0c0304002d03001144e80c2c0d442e255102e91001030400c40e59425500407e81305c90303040303d084144082003000030075220301d000040c030944416418020682000086480d50001a00d003124540000c0205c580910b0008000c41c01c80d5140c0d000c0740c000300d89087d401801d20781400c210b005007411010f075489021070541030b102101d4000345070b03200304131001d024640c442c1c4010800e80018142032401203115524043c5c0600504d1800036002e0246103040c0c00020996400301c0c0c9164011000304d424400d1807013640420942d6005404003030300320701000302c00300a11080035070810200d100c0542824101540c9646480c00c40e04642c0300d490307125490b05901501a008400d03012102555401c08000002c0541c84440c0d86080090000b40011005400d0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 68158114 1250 68156864 68156867
    0x100e0709050306090115090c1409060418060302040c05071a0a020408070602100c030207051e010f0e0604020108160e01050d02040b03092503020d020d0c03050610180b060306010f 78
    0x420040d00c0e0250844003641000c5903940c0c000c0000844800d042145420041f5000000e4015494401c02554961102c0b070308a0f807058100768014050183c3c0b004082000042c50148566800d42451051000290381803031401440265801d120702076003000010400100010b8a00612318803d1100b10a100b10961b81c070070135080203125503080882540324002000030b01e6580000c10801e1084658000c0c00301c480382d28001d405901456100130000d070844d0758650840b90b807240000d0303a15000c020000c03d4980045082d0000c485811600d180140c00250070403082d96084900c0301d0308a2440310308021142c009031001801c48134005200b40c10464001140075040c0d4994041d20050201d0741c1040760780c0d04100c076030550313110f510a00060310b8030522024800000d003d403c4610132030f500070700304100101d0f00b81e08014004802d04d4044401112080001c40410800c0010178800d80700000072100190402c205d4203003000002110150950030103e080d1195110081500c1d000f040a007400c041510503043c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 68159364 1250 68158114 68158127
    0x4020a030c0b07050c0d03020c0105030709090501030f02100e0604120206040308040e010e0a020408031812010504060b010e030606100f02150a051605090f0618030a08030a0c0206100e07 81
    0x40641107488545010441241000003001d56900c50422205099220824070140b02c5161802a000da007150100600c80c1d40141c006541c000c95500d85001641e4031a584807046a00c20b800694481e00b2030029030f0b045041004030040b80300d4140c00c05100c042d201d0400100c41c2d124038061042c0341403500d406030046444220545000d55400105a91100d851b400301511000c000d100c1d122070501d0b5400400c140190510803607080c0c42202000e1450003500344240c11071600ca10103541e4000030300c2030302c50260060030311819001d5486540081582030700703c1c0c00144042404203050b031098004109002581d81c0f0b41642000241460410586644149100341d04003902104010081901c81c82040302d8001ca40d8080d80c4140c0e41b00c0717a0030000081c0008110385900030415241c2e0000c416000d5410a0300d402405030a1403601c8500c0c0322008464480030900b01780d405003003159034000110500411030703690b0003a0f10310b000310b03480241014035012462216110304c41c03081d40f00d940074040204403602c1c440c46 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 68160614 1250 68159364 68159369
    0x1303230a0b0405070509090a1b0816050a060504080618010e1006080d082412010213140303070f0807030e0901060203270a0501031e09081e1c0504020a 66
    0xa550124865007001503200000b102e08852a0041c40400304951621489076401044004005c00f0390600030f03a6020324005011091483e51104d624001440980c1002406c04d5201da180325120308915060078441c0c20703031164100805015080c08248100c1000140d41c1e948140412001c007084120004030700e00401040282805602401200b1160003085801800c2118040300840c0c0d20400c2408084a15200c25a40b103041080c1000f808071406648040d40c0c258182d008159034410003100000d542240d204100524400044141c20005540b01c5039000d000500d05401640c54515507984141c00018a2080144108804610a414544038a640802d460009400c0c1840c9503181c2c40c0c0650380e5081003038880e80300c8281604940160400c0401c00c0402000584100442030801c4019006410040700a60916020820351000d82e02c05015090900d806510140e0b542c3c41740600408180703a24a1902e1654101001000e0080e41985c00c011500d020301c01d40040d860b21584001140b9a4056 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 68161864 1250 68160614 68160683
    0x60f10080408090a081507020105070801050f03100c030e010e0a020312030c07050601030308151207180e031207020f1b0103050c130b090a08010e03040306020c0f060712050109021303 80
    0x4c040384210002801084605150444400542d240c050407801c2e40c1c81240d610700042e010200410040c107003c03840703941041004042e0755020240f81c802c5400c07915000800800251541d110390020902813180141900020f0b02414040030f0342d03000300340d1b945040461290f000c100000001c1641c0d88040c10740741c00c1d035480002d440b0656968240142046000d446185c9525200c1d54001050b140c600b00b100c158134a44005403901c140385c0b5100c40c0444003540c2603e506141c0360300c0019030300c0340c041c0003c06001082c00008803050604180003450700c0f04010711058281e0061014000718403007018050420307a000d10b0b02084c0795603080088509402603450803403402c0c10a450101d000d840d044054040001c0c10384503040c400313a41d01c0580e4240c51807030003c0400c5e42c000300030500100b202900242040e01d0a070f011289c40c0e45060b40c0113450014225900350000d8480f42c88c0d4049140c1c5809060b004183d0903400b941050f514101e007150f8138541d03102c001c228160f604c842c4003203800800820140d05c0140c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 68163114 1250 68161864 68161879
    0x90f010606030911061204020120072306030417031005040903020705010e0d0209041119030308040209071707030c03061802071b030b04030507021f1106060f1008040809 74
    0x803084042c01822054100701c507062226000f140716414044c1c1079031010031310a02c80f82e00d66240c580041d1540004091074200b0140d201c52014003503e000c00140d07008101c1201c10040b0714100d03c60600320840318242252180d40c0030810310010407076200500002002c0307181013a949840310348010004007041e80c4015000790600210341d092580101c0c0002c102e500a883d09414456120100215044202d100942c80165040481c0200c0da0b50620750280320409000322500318848a8035108600c881d60080b000181c40da4200011070814901d00e80c0c0100c0301e820010895526030395800d00b0b501004146008141e41c40042c0d42d075151080d00050010310351940c8240d4050f46c82409540a54001d60f010340d2040c01110071300c0181c11a19111404598018514002c903483c1d66804403078540c445002a40d0000001c61051000442d500301400300b220780b6240c01030a5540c580009051187c000d16481c421011402121155203488102c1c1d07803962024505401c890340c0c0d503c2d00f03049038010410b84641214a = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 68164364 1250 68163114 68163119
    0x270608010203072a0b0a140f01060f030204050901030b130b0a0b15030609131109010e04060b0315060409060204080604030e0306090706090902070302030c060c0d06060c0515090f0106 80
    0x9040d4021406001c0030754030300100c6403144207072200402c0122000180e50101d010140c0104108400a540003e040b04c40420342c0c600e0300f0710f1040c007080256140b03404000090010080c1e50340103112404100a5400c0a50401e86003000003458030b4414800585905901c80000e080e5003031014801e08596400b4001c0c3c511401d02c00c3c00c0e84000c040d83c10020780225481c50203001011100c0050720b108080052001c0001d1365201910f150901c82403c0445a4a00c104262400e9940d060b220070b020340a01c0c0c01654040c07071b203820b081050700c0001d010341e4083c1d040103142e22541040d02d9411940040d0554011950f4000742c17800400031f101d0745e400300c1c680d8001c8006001c1050382c0550061002c007400c90460f085500d408030700701c0c1c40720880e10521000c100080f508002010f0303c3e802400e0308030701a00549061003c0446a281000e400b255402502c0200082c1c0c02040394841c481d61000e400c481c0391004012403030341c1d80d003656584c440c030150b0041480d40c40042e402030001c00c80042c00105e00c40082c032a065 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 68165470 1106 68164364 68164379
    0x705041e0504050606040f0218090601020c030703141507020307020f0105070602120103020a0b18040203220503040e0106050a0f0c02012c040c0206060a2706 69
    0x40d1486060800030101d01c90184a5030088028000320300c5c0480c1000704070341e4411145042144140034080c0b031a103401a085110398000c1d00c032003c1d1703500c0e6840140e1a241008080759030600c500a408800c005051040200ca0f040388411100c0c41d803120317991281c48000c111546001030784240720740f030702500c2c1c4109680040304040c180246403524030f0301d401d0203a074080c4a0480c0f84407003a400410440c28450460300040038480f80c00d604000e82c2e003414102035507024803000d1044c1d40220200348000000d42640c03c2800e601802c80c0c40c00c00003441c1c456100d42052007000d002c00359410001a02a015004503404203c0f207581c3d40070204440c003015181d244040809a04001801102d400b5446805140302d041003001c2103000c040c11a00030411082e0346041002c0011500150103000c016107a4120f24820b46152010001c180d101040250840365042101544003a003040b00014450 = true := by decide +kernel

theorem cover : BRFrame.Cov 67985614 68165470 := by
  have h0 := BRFrame.cov_init 67985614
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67985614 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 67985614 ≤ n) (h2 : n < 68165470) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
