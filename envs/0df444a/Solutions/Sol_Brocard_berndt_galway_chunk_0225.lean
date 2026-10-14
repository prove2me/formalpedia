-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0225
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:34:29.075827+00:00
-- url     : https://prove2.me/submissions/97d402a2-4afb-4d26-b782-c07d1e3e6d7c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 40287774 ≤ n < 40467630 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 40289024 1250 40287774 40287781
    0x1f0e07051005070204050a05180a150e12030108070602190c03030305041b08030405030c030c0901050d03021204080115060512040201271401080f0f060105092d01090909050a0803 78
    0x8070342c203101d80100039400c01c1c182024130031030700100e51015210f481c140035030603001803449007031645440954001900c000f946403103901d08420a0f50281410450240c111240d0b207080254100058009074840b585542012508002d816014808a04440c11050300000340746071960700e003107145229001c09001c041c0d07150005000c007d03d07640d100603016210140c030209155203c00140c0e07254040e016040c041d02a1240801d9181000603101c03480d0b01c4010000352050b824002031040c0250340c4d08044e421841600e2410610841550007000a482c1010020580c41c3e0304403200c840000d4654400e42c1042010803a10b9102c5054151a03500142e0900c1c00c41100101e002100000d191020710349111074128100009500a0703030600b003100301e2401c0c2c8900301241e40e034101c81d40d0308031004c8490203890011400096840c3d84540020800701d10000c02d90b14101c604130704c01c901c0080058162403048189841c0c2c02d41c166811145210080080f45014044815580d036031546070480404010094000072012 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 40290274 1250 40289024 40289027
    0x50412060209060c0d0e03072106090f0c0302100908100b0111070602060901051509070c0203030d0207030e03121306030203040602070203030c071e060f050d090209091f0e070510 78
    0x464003400b000800e42920341001c9103d09440c4e41082d041240403414014001c2261b040100d07002044030b20760701101140c02803444a04400740341c1e40d202201c0c4990f0314869480020082c40300c160320300340112203c2d0f08085c198814030003220600c040b10800c0c4084541c00300f10109001842400c0c4001c002c80109481c003e400050f0741151440140a46034002c441e404070341c03142d00003000c91290f41c0450080c07200f619a00c0e2140f103400302000000360008260340009034440e000e200f41461480c4007a01f12850b04040d50b00d05012600411412000140a42c3c0c0d4a2002c1ca000c00180d04030f000002801c5161800d0103c0c030b44c003824114465403050580100c000303810700034039a06980589801506403a99410715201090321010140218181941c903094110070203042c0031100c0c1c05070740c1c00c2d4584d580003002210f019241504a04600382019458000d1a80140c892940d103d00074100c141c01010741d078440c4c0030308401d1201c440907440304aa20f401030a44d1781400002e40710044a4090720003074070055082a0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 40291524 1250 40290274 40290277
    0x20607050111040b0d05060409020a0302010513030f0f0201111204061103090405040803090d050a02060103080f0c1203071d0a0506030709080d0e0f040504020109030b1003051b100f0504120602 84
    0x200a00c2d441004600029520f80c41402005407031044c407030130449a0b84502c00c01c030032184044006074200250600c241700650140d4000c001d900300800403081000e903070359078019280c0d40f440c008482c4009014100c2c0115600413400d5200c100280c0050044001108250b0040b40078070301c9200100030400f0040401f071901841224650711000c1c00c140400c0c90603007410100ca500548001406110b814040a0030354412000d5801c00345d0680d0142100741d11b5a119040d40c0e800007480a40d509a00300901000380d401046002003500307514000b95140e14200344094501000c007000c40256015081c00c000c01079540d41440c400b62070003103075401e0300c0e0b0729800c6040b40c0d01e50dc1c0741c01500052046042005006800144c030400d00c4100b111541c440400b207000303000a0340ea003664001d01084048100744005081e00d4521039001c14025050705001d90340c0d0300e441e45002c1800c404012420048110032866050940c0140d82c0c030101410320b61500010a84002c00b944220700c100364130300c004041440204036481c1c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 40292774 1250 40291524 40291541
    0x11707090b03090a0209010e040c09051b0703030b010201050703110d0e0f0d0c1b060e0405040602130311040f020f0a05030402040b100503180118020111070e0403050304050f12070206070501 83
    0x420a58991603c1c1d48126940c4401d00c20a0f403040c01c1d500c000140408182040b07610440d0300c480c040b00e4043c5402ca1203000383c00003610101c0b00c1c03a030210340103040001403400b511921340240e4020030300090010000e42100e801414040815040c01d48004035448400c007150361a094046000440c440700c03080c0207040030030300c00c40c0003905d0048400e10740340c041c1c1c040301500c121801071140c10803203441204030001c106c0c15886200302061507044003a8031442c0c958400b550290007000094680aa10383e0078400904150300200c9a119070018551003a040c28458040003401c10802140342c00d150030030341d40c1c281c05845125010007000000050454441d6005808103210140141004000103040985150400c0b40c08203102610304512004000d0140280440d0380604140f4241c406140d400441e0207200c140b1f02e2001034840c150380003440d01169680c0f140300754029603d1580301d081600d01107041084e401106050b0358090f603810014580c6205c2150400341d4100c502d10707642e0080740f6200380500441c0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 40294024 1250 40292774 40292789
    0x6040603080403150c02010506010f27380306270a0203161e180e0708040507060203030601051803010f110a030b04060806130309090507050d0b03030901170709 70
    0x860000104049580c5000e4086500d103410b100740348101c01704030300321a01104c600340003565006020110a0060031204208058003400b40802101c1e9040d142c10040703240d00010103481c4075503001400c04080d15864242002024240c14080011240c141003408050f1441c0c2c410a40c050f6960180b1000c00c1e4101c5441944180c080582e1038039000040094004681200c0d83e440c2209000c0d15840c0720382941d00d1210307008040c600070b0842081c8200c91480099031005000c0903e05401700e084501c1d240300c1c03071003a96285e841d13203100d140500d4440d060241d07540c0000290341c4148184001681c0080503201807800c00380c02c4501c0003510a000030301600042c0003002d0100c0c0350000c00300480750342c4401001d2107103880d10144001c200c50f10070700044039142e2003050f2558109502048040703411580e01c00c00a4040d14003441c41da600d4441d0841211801c8d252400403980015081500040b20300a040c41010218050350406180d540041e0405001c003400c00494400e030b20010b00e45600440c400009030410 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 40295274 1250 40294024 40294027
    0x1103040303050a0219030903200a030305030a11121807030302030a03020306010c0605040318050a0b0909090705030f0f1b0904110114040f091a0d0b07020c06070302011b0e03150604060308 82
    0x2542800347c504030840c041954200040e1004451078940ea14665200d100003900050805d4910b07101114036401c0a00140c81c569190103940c0c000c0f1281802405e031648554084c0f40745401d01c1c0c1c1d001d100101c100158466203420820040010030b03004010340341c010490341000350b5079665084c0100c502c883d40c0300c401484180340200b80024980e001c201403400c100c103442280780c4951640e080000092043c81910021481080011920f00742440001d8111401c0802c90380140e440707800003404c0c41d0100740021b200d03034059082c0b40082001007285010781c1000300d20f800f8294040700040740c000d0348000c0005e4285844a88640c003a40d101e4914246d00329130a0301003175103039034403044031880410042c0704d01b1801d18217005c454a14203032244034034820804001d1036020364018136541e0300e40411000b040d030b4080d07004010030040b0b1500c4480040000b1486503000050758a90114102c01400d1012201c20400035075110246d5640ca000a1800c0d000b001c4503805030590b03444400142c041c00031900001c040f401c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 40296524 1250 40295274 40295323
    0x305041a04050c040e1f090f0206190e010e01090e090f120a11030c0d0804060f02030c030a0548070807030809010203130f0203010902031614011103040303050a02 71
    0xb011034200d4144400b120305104003450342040d07540c5d81d02d490002101c0300204085241ca00001540080851807241a1040390500e10341c00041c41da41065050200a403400c500483c103081e4404070b06900c03004242842011f018507a00000c1a40380036025801c102c401950101701026401c00640130f41011603c1207a6441507207404c010300c660055524a40820301618220034450b0003c002d840c4d017075035004020424440c00c000b003182c0e07030800075006840719503850085140c0c42503d400118490101001002d9403401d000c0115000ca0f03c0040c440010a1000701810185240980c202441140c403010b135281640980700000d0040f00c00c5602c00b03c0845000201d0b281003008100180c800da50194480c20b019603600340040f4242d1004564101c000385094000c00d001607000d92141c2303c058000740002a894080c1c2d8080392505804c55080701ca1007402d6403003003211015424041102c24030a01c0c0070f850603102c020080c1e40d20302581c00300805101001c02c50514443c400c12880010040010405409d00d1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 40297774 1250 40296524 40296533
    0x50711131d0703110609150406020102090a0801020a02070506030c130311010207060906080606070f0b0a06030605010602010b01080612150705070611030c0a030b041d010506030c040b030307030305041a04 89
    0x40315900221a880c0c0200d10201c00704042481002c498011010f610041000030401456602039001c96500480c41b9800090041c03180000d4030240c0000d030001a910394400040007c0d10200d9441990309070300410000100a60104207a0100c48050b0340c0c894076900ea0851000b60b90040d1b18145181c034040c000c00005108101c1c1d140344017014280c080c0c5103825100c40e0100c841c2500380c014807010a1042d004a01d06051210081900e0750190f00611021100c50b41d4a902100041d907240000076250b00c3c080c014003040c0d1080e00e005281d180020819031500b40c0010b000e5600040a86115014103015a10a48003e110744103014400c20300c004202d00c0c140501526541100da4103840103032910608200b070b501c55104882c09000b251222504002003804120f028040103034481d900192561070004d211071084c045090600015000468945491801c1c549490500b42c50300744281d003442000d101a8502104a4010f81e8040ca402b061640e2a4140090449880401d61003940035980410040c031 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 40299024 1250 40297774 40297781
    0x30512151002030d0b030604050712030504030c060804060b03030301080a080c0715050a0905040c1e020106080d0509190509040f17070b0f060f0307060e01020109121106010b0408060705071113 84
    0x2410035131000c000702001c0005050fa141c004030b50050490b40140f40038003118980d003d01043e044e110b46801481c0c1500c0b0f64400c0c501d038181d0390101e000300303a1180500c410881b440c0600d1014860a07401142150702d45003000e55107c2d84200003034401c07000081c4100b01ca08007400340d4005001c10b01440f07e41c0e40803001004006600528000c1d001034803d40011401303141034069400d03010300d50350301c1000300e540311110000445000d190b85010741d1360329078000075004402e10800d10142c045444840d2103030210000e1010042c01440d821865210032802400310380d4842d00c1058000e0340003070020644400c503181006261041801028100030080355070010016a80c84040c03190007051000e4075691240700074020113400a564050341a00402814031049100e4508d00132405030503c00407914848940b1005002040d0800a40c005540a030105040f54400c009450040c0b0400761001d00e020314106255440b0300b80504100200100007803100c0900202070f158102c1402c0003040b071923003401c01c089400002c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 40300274 1250 40299024 40299037
    0x110c031c0605030607030c030b03070f080d090f06030207022b060b0d0201140c07030f080d0b01080103030c0b04030311030a09020906030d0c110102030c030d0f05060d03051215100203 80
    0x80c001000503044034010180116000c40e031019004014035120114103801414000300c2190070980d590b8504111603808021510003000c80c913a103122418281403140d41030917070a12000044c000d0880d4104040011441e68508540e0369280050722254140300040301c180c805c60320748540b00500c522001820380b40e8518101c920744140b8040000c04605401c3c00303102081500080d000c01c1c2849410481500c048008010b8446108103650745181c4940e2105107081612805507942e01340400c0103540312950f4400c4000020013402e044100b9072541c0e40041020300b20980c02805140400e0215080601030b03040a032040303c00c0c1d0b85054503864074a51041c0100805d51099205411754030100b00c9504010500c010340e83c103656580910300b040c5403103081c0592240c3d07074a141184410090740640c0328040c4041d10350744042c0b80c3c010401181080b41c25054a0015006a1203010064200c1e00060740110450f00d40c0a5000c03040021640c3e58000c1e0344c003203440a140c580c0c00001d001035200e000784d8048020100e = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 40301524 1250 40300274 40300297
    0x6020d0305070503040b04060b030102040603020d06080a051c05090a0801090c05010e01050d02161211070e010509160903060f0903180308071e051e060703140613110c03 74
    0x621168400210156403007034039480301190341000030502080248494542c070501485001c908080407401181c01c99010b50b121900195012490104101030341c0981002800c00100409010300d003a22003903121001c41145010f0307040c24190b1074420600541c140d5840e003100510001902c0e03500c8070401c0c041c0c040c0782405c60750040301140124041d07001d0310340310084080603580c05041c20300300c42024000758040b0350700e0000d5a40c6407887d0400910180018500d00c16155a50542081c1c4424080e00d8092581c0107403403803e000d2001031185032075495aa0b0343c0444403100c00c00d221b09241106a0b2008100c0c1c00c00781a89040c4070005c2d903000c200d030300b18500b101d1080d0b0300d2030b0507514407508042d0070f4840c50000403c05501004100d02143c0c41038500d03441c4106496581302d03590750950f038051426144a1a005000c00c10324403d0f9100f00050021030340c0024241000d0110b12090100364146030b000401d014498551384007100f40c0c50907980d110410742124021202d41c1c1c0c1c410f0342c2000b6901e410017070300c580 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 40302774 1250 40301524 40301533
    0x309120e030115180c020c06070809090708040f0204091a0708070f0903020d020906060f0403260702030606040c02030706050103060203161704030f0507020303120a0f09021e190f0602 80
    0x1108409210403c04542607460141c61030601c4800400c050490300c090342c0c00f1031041c000c00704816500c800050001c140305200565994503084184002420003c00c0c450500060030108004034a42e20080c680940e811200002c41c3c0c041c0c2c1c6000e042620700c440400900c20a1032003008a4143c02c0700805d40070f020182c031a100e010b902400120780003289030100a4102d12205495001414540c2c6010342140f0018942400c0c02c0200702034920527086a401550001e4143c6044180c09c92544541844664807043c011b02e441d20035000310fa03482001506082c0901d40c1c0d403280e45803080c030a00a82c0c802c503900020a00c1a9607503800c22b4000703504240c6010040c10f24030308150b01040e008110410703a80f083c13518101003d0707840c0c0e1400c0c0c40581c3c10034920700034408200440401a5014401846100384c107130002c1c90740303080c0000c9100484281403201e484540c50800c000000d680c5171503805426041803202031a501a04001150302c131511002c102d403c03078020850209101881c8009001074501076800c45 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 40304024 1250 40302774 40302791
    0xe09010c081807030215040b030703021909030f02100219050307060506011e0503100b04080a0b011a09060c0a0f0b0108060906070914011701060201060e0c030702060f070309120e0301 80
    0x2c0c00054401805521240c0c0185030800050801c8031a0103081c590070100b2905040d034541416180351303c11528217000070303800140c6801214040070084e040c0c1085151840c442030030b40d5281d4907a1034405001901c2500e15201e50580755108001d5401150607065150a171030405141544c1e50303802084045444509240004540c0d501c03511500120030010042078120100a0703d040c1c0d40c3e9440541906020100310401007045646071000700024040d041c003c1100d01c4060900740f00d15001a0072513040b000300daa1b07240700c401c0281d0060300c003101e504641c1584d070307960145915803030000c500c2801420701a503603c4c030384280001059440d04968240080d07443d06d55908100b40e44840040340c04501007052190184502d103c280c15403910301c0c0041c1481c0541f00f0b082c004440307020400b6405500140e440e003d041c402140f2000e4003075040069158030b541141170041d0060340707544004012105080c1c484001440661194002034071040e04120140c0110318282c20081c5206c030b5200550f40a0b60a24012 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 40305274 1250 40304024 40304041
    0xc11011d0607050705240711070602120a090e040503070b01090506011205070c020414010f05010507050706180b0c07030201030b01020a020306270303090705040c0203070803041b0e09010c08 83
    0x100e40d0001824009000d40c0d68403090141d4441e0000d100540b00c038030505580d00c1500e0b8404d0300d1002180c00c100c030a44064505010014004c0110390b620041c95001808104500c0c0c1d000600c2008080484040645071030750964100c0d03c28102d070340280080c01d80300d4103000610501000400455004035840501682c960301880151141920f00e18001107040034240c1c00380550b030b40203941022440c07510007101c50407500014261649c1064401c415001003004001d0101080b10104c000c4c41c00382402c2d4200340060715119100c0300c0178424030050080c10072042c0c4085030b070301c0c0c0c0d141e014004000906441c1c40355600f00035503e1145000c00c9000c40d107403241071012076000003041e00c0010b6008000308801e81d90601415444503003800d0500d41d0305054036044001c001d003840507611400c515401002100d28000400c01900c403078094a01c1590420007045c4041035030388084960180e000400b0fa0800c03d50340c41c4003281220b03642e0041e0500180d1005000500d401034025008003261561074050071b866881c0d1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 40306524 1250 40305274 40305311
    0x303060e070c0204050612160602010b1503010b0306040204030c030303140703090f02010e030c1c05150106080a0207080f03040602030613110703030b031501080f15100311040b040c1101 81
    0x2007800c0401c0507880e607600146082e8100d96802180603080d84103200c25014240d1030301c044051126103c200c890700c103100c21035091090144242044519075503d4481070b5502c801c6100c107001c0c01804c480000300050642e00d698044400840e48944800741c25942e0f4100100201a0b05044007a02c000e4403020644103442030050b802c140d034100011203105161580192004421440500d4250003040495002552100520012220402540d110454040c03605a0a100038400951110242c0030300500c45194072000d6aa800100380b4801641c0c0c209a06100b122805010280600148000100020419190055402110140c0b42c2e91000d1505000042c10344070007844040f0115014010480031a21a4000151908000d419120503e00d50307c81e038840702400341c210402c59440194103412601c8200320300500d54a10941c0c0c241d00d800c2c10ac10088142405100180529105e0030180b2004c3e038440e48400c0140300d0044c0104038910280300d000e07100c1140f0101040d055481e0800c08001e4030b147c1301 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 40307774 1250 40306524 40306531
    0x105041a0105130306020c03040609050603102310030608010b0d050d120603060608011b0504050d080f0c1005090c0102030903070e090f060403031506230a030b13090303060e 76
    0x40004008240315004407640d401c08001001ca008280c0d07800808540c5a00c014100124880040e6a44d141000300c00f400c180700030390005010720010030800c80c14001c4980150180c504c84880701c007201c40c0e114500e0054401481805900181c1038040145550f0194001d81c01c1790080030092103c1c40b1b031101042940c0801041c05000c5400c1143c0c0707060614442e50903541031001c050030000350140c50351644003c07501715400060f0182e54440000d000468010f5600362203101514086283c40d0600c0b000c42d805440414005000d60300119131100440e100d1019503001481c0c0100300c2d101c7c030f01c9a01c07a030341c09072100f5214080c15014500a120f8154070100481d12411000b4004140c0e1514144840307180301401400101039004011060303446034070501c4240d000e64001d6501068500d0100c00140c050a5142e10401c140101d1a10301740300d109050b45040c14202c2c4241000751100e118000070b0b0050b185a001c050b1344050034003299000041c07035511500e01d00d40640c0d02000483d440d846c07140c03850503059 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 40309024 1250 40307774 40307801
    0x12060316090b0301020c010905210418020f07050102070308060109170705090603120406030218060313020f1306030f0c06020c01210908070f0605070206160302130e100905010504 78
    0x41105000201d6650014840c454000e0001880c0c030071020141d60031643d14100444880d00f10b00500c4080030000044801e140e40c14545081ca024074120804030101801c400b140c0d125900458440400301c0c41030180e640c050f40210096503940054a0000c00d43e031000c49205000ca024644081000d0740f026034888101c4540e00700030004942024100610700344c00905c2c1560500c070340c0c0705204803442d260029000500560300e003d03031201c494842d080d4200c100c141c0340900411050042140d04e1241e1400b4800c401e406480391181c4401d140701103040030384c0c421010001d481c10490004200803406840da80f510740221100207505807500c0c0b049807980c4890b0039103400116060380000745826035070712144001070b06142c0050300705050b40c0e803284030340c00c40e45042d514031414400d02418800760f4007038030754441c40c03030302c094081443c046076143c41128618140c4410198041440750405074030780a068041d18825114203940d01d0013442c0081d0724440b034014003481a0074400000b0340c070b0800340118030f020040d8 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 40310274 1250 40309024 40309063
    0x11503050c09061e040504020a051e130b0a1101050c0903011103040f120c050106090506120f070618080105040501020714010b030703020103230403090915030b06040e150a02120603 79
    0x2e1006104460600704103013440d9000c01c00c000110350344c8504c001c15036850030342c41c1d083c0c551f01003c224104c54030507440c880c03d041c0f41c00c1000840b02040d061203401600c10329a03a158a07519070b2402100c2c640c00445a40d0450741c603041c02d002c00d0030126406031811030703001c800a001018240c00320316102d00003954000c0c03594119006882c0003a1100c041c62050b51564a05050300070040d8840b1401c1d607004d40c2c8207400d210790701e905124480c00c3c0100e66000c11400c1000504200f803e0451450356072210f0b00c00d03001080240300c656901454001c050b00c0c01012540000c2c00141000e0130400d000303601041040303900b64040c2080400a26040c020250b00b400c0040141242c146550015400f506002000d00300d60b8102d0810103003001c10680142d4011802039032a441c50500340081c00303007299980105100e400c2080d0b94100002655400000c1e80204250b03404144100444a4185800d0b001400100107040413010024641240d40c00360460140c90104280103841700300031305d6201c25505240300c61100c103 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 40311524 1250 40310274 40310287
    0x60f040e0d210906140603011a04020c030403020a0e01141504030201080a0e0a050a0303050907180b030a0803070e190503061302010207080d030e01060504050c0a0c020409060203011503050c0906 85
    0x400c0e41581d08a040011078001e2480310b400c00c0102d031030501049586540c0c601c80c1120040c40400890b40c1701d882a8001c1202028009034882c030348010740c0322075219035000206680f1002c0c041c0300703580003150301034920321003580c0704d03001c55100e5039090080c0c440554854074005228540804620300781540c0d0f500c0c07685802d003150011030700d0f08be0050580314417030b80310451072140d00000c000288000340640007516841030a4640241a120042c01001156100900c184140507a2240b070301000e104202c1c0000b10590344501081c10300c0d8a290001d800d000c00402001841600304030744a0200000310795410717000e040e0b1142d40000307a003180100ca07055070002c2d0010340300c0302c4481b042c2c1d030065005004071090903650340340880c170302100c0c0c6900200094561046901c8807100740100b80240a041341d090140d4504140c910902c2d0042c120100c040004480040041d5291030740030341010754001d00259580e41e1500d103881c2900b8a030380848000070303290000286000b5908015039800c040001c04143c80c000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 40312774 1250 40311524 40311527
    0x10050904020417030327070e060a08030a020a0c09091203090f0606090f0f050402061210080601060c020f01020601030803060607150203072006010305030a03020315120303060f040e0d 80
    0x20024648590000c1e800c02020408841c2d005aa14003000100001c542d0b0f841c1000c150108001b506109011512010203400c66403500800c0e9803091361038260400105545100008016000721303405075083d03010001d440b01006501107078580d203032405003002c0d2114540d80d049802c00c83d02d034440b02400c441ca07850007003c201c5100f40c004007070072030040d07200030743c240483d40312803007107405d103601c4180e0155440382c07207201c407072400e008484000c010f001c4104120301d400d40120301184201e43c0894a00030500c00000c07910104500070300003814040d01251a80e6844200c090b16120f103201c010391040740802500c10a940c80040c400303041c0d991240a241c21034035000c040c04031642107001b044071903924020181c1407901ca40d101a6200e40b4540d52480048480c0341c02c500352410745090302032070ba500a81d0050021443c008220b070b072110201e18005035a540c842586699214131075940070760154031410f0002205d08004061030085030b0440d030000070308152101f04001c807180c106007180c45030401c3c3c3d001c882d480e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 40314024 1250 40312774 40312777
    0x6090a0c06030906020c1b0a0e06100807200a170a0f050a030f02030406050a200f03150d03170705071505060105160b0726150f10030203060316051005 66
    0x56100c1d40025007040c10706c500150038050154031100b2030304000004171540d40340880c580300040c44a0480140c0b642440004242582c6200a01500780501c0d40c0214640300d2140d0007000210710981c3c0604480c1c1001c00c400368841e1001c48007541ea200300c40b040721088210500031034500c003e00c0d46804602818000c02503916400a00f107040034903603030759500e1008844900040d403103684581000902c0d4a040f100381c0c011a00501c01c06400c45004141611400d40e2040403624485017409400b038503581c841d04200420f0359854080d9401c0103030b14a00ba0101504000308a09001f0240b507100c040fa0340c6d0b14001c07070f52409049030150460319480c05400303414680358422a0804818075180349010390080c401070f440200000200c46540c2000c08101120703520500707400c0010121310405000c00280041c0580c02d247c00ba05013000c4107031070407006c0c0d9942d4940d403204003121000341c50000c500004000c058008c0d001141d100b2301a00440305c94182c07501692401c441504c80003020300c20811211030713048845 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 40315274 1250 40314024 40314041
    0x139020102131403010e0102030606030a02030402150409020a031a03070302040908090306071d03010c0801031103280303050612030a0503190603080c010c0e090c0708160b01050306090a0c0603 84
    0x1995400c001c0322004042c048508030160200e0b4201858240103002498212110440c80502c242d106205021440c1d5402d803c6a0700805180d6002d40c894940f0f00001c0c40321a01403c020305018400a40091091055006403001c51000e031410400c200c02070300f440404000c030030036160307150b0001e41c0c0920041c03410754000300340180121125814001c0f4080071030b24159058031380d00046251130551541c1410031030500220031409500034003049000800241c20640c041c00010141040d56440350820744040009170710340c00344074002c040c1240d105050b42c800a0001001600028180400600a82000000c104c40c0030400c1000b1841c00c0d1155900301d403150400703000e88203c2c81e10390150107104481030003100d000d503000310380c440d940d96180d5001c0c508451039034103402d080c0b25044c2a410300d40c2e80c4e910317002c551020750070300300c1070b03813030203c1d00d00313506584500007541c070490300d0369200941030100c1c41e00400c0c140c40095044448944030700904035a2580d1481c0d0041c0744100f4405c041c0006442038001008 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 40316524 1250 40315274 40315277
    0x3080409020f12130210110618150106030501051206010302030a03030c02070e040803010e01050f1509040603210f0c0b0721020d1401051203040311121207050139 71
    0xf440640d910f00c0400030002e032a100c180400101150342545407140616102013030307d040c03800c5000d003007100c2280c841c10018201e400c2e8000101d081051081c003880120b040c00820403032480b1542e141c42000c7c0c01010700380580750145020000c1120544000560581a00d0300200100b40c3c03002e459504901500c040782d80d8004602500d0000180101e1880f80c0a001c1e03446010a580c036036046c140c0e81d06214405910180c8581007016030904507444152084440380022011940d4681d00000800c01400b901e40c03000b002012514106800200082c5800704a040603903100b01344032210000403283e0b80040300e005040e001c0e100e00030417030301c0d400350013820500034450080000e01380a0200300c030200d8100106524145031500c9101101c40c0c084450b95000d428110b400d01450507080e1011030b40c900590200030801c06031410008880d54404440b400c0700a604011520102c40016000026030824842203400e0360a26216030f0408488c8615901e00d01740a00b40c445500c44006030a0341c0d007040c814548030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 40317774 1250 40316524 40316527
    0x6020304020a030c080a0b15010806040f0e07090204030b0109150b091309050105060102060906190506120a0f060501091112040f2003100203010b0906030408090d03030c0e090103080409020f 83
    0x114451403c4e0000d106650140c100c8001d1810903400f540c45c02403400d014a08001c42c50301c00c9a0b04454410382083c019140001c10340b404104a2009207540051400c451194000c00200d0340c1080d0005c000752841462a95026641c61100d0b4040c3c4066085100340401008018445210682c010f00440000240101c4403400000041e600702d07800032205562994480b42008110350b01000000d400001138001031039a031a0062041c02e000c01607010144003143c951010a501342c1d1218100c0200840b00c405072a6035030b129160000d4240c0c07c1030000c980084c1488000a102d00413445082d485401e500229450b0091003d80d49600050041013101c0303401c5c1c000d49103070104d1300702c400101580a503101c59180041282c800c1501e0484400c0308008440e00400041c000510480140c9086031400d940e11a1651a140740c0140c05005440185400501801560b400d040d4540c01424400b481600d80c0b00034140000c007400102c032001d000c042d000080c10403007041118100e50041000740120181a13 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 40319024 1250 40317774 40317779
    0x203010e0303060d020d0c09060e150a0509070f1103030108071a03070c020108091e0601050109091802040b0a080d02100c020a0b0f1302032406010206010e040b060112020d0e0709020a080406020304020a 88
    0x10110f484c150000412b600c082c00401800b407801035180717041e041c0111070b0198202d26000000701145001401141003000c60200340d00d02074081c501035007082110344140c039160341e11801604d60720811382c459400200388861360740380c511503640d0840c0c0c00b607803080d0380c1c80e07610741050b030019100e100d0081c049040310b00c03c21080781c030442c0b58160030302c24030420940505078651401000609076078943c1c01c41e0b00710f5807820464020524400c00d11903805a4150f03008107001207104006407090000354030207aa1350003121801d0052aa01040d08100fa1110440c100020b40b5682c40880e950618500010a070380c5c1800d02103501c078100f00c035125a00c449a60f0900048043c0350f80802d04207148031030f1107841100c400940c413401045400c0d060358080020710041901e580740c0308038452403143c00740001d03088a0b03101004c501581d01c00c100c400f94009a01d0820341da54044007005000520310000148000c2c0507203807002c5180b62031030007107400f408183d81c0c5001d210f884a44070040258800341049a1014158100 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 40320274 1250 40319024 40319039
    0x140702150408090904050a0204051608060d060b0607050102040504051015030f060b2107030504050303040809150a0815060a020d050d0b03060903030f01090603020d0b0a0605120a0203010e0303060d020d0c 89
    0xc240700b41e00c03446c0a0b01e0840c01c1c6d031041c481502d601500600c80c81c00210362071945a07902900c51030303202c0c1c81103458410650250401c00001c2802d0400d16402c03000008000040c4081500240b0854274203580c100241d58a01c0003040700022140140c9940f0300003006407070004c2c3d100b03805c40c04c007402e544140082c9081c0da071a43d01c0d040764480d07508514428000002d01603010080f003000343c0e010800c0c0c1400d20440c9082e50301d80d5204d1000510081c04040c01051080040d01e80d140c009d0075407003002a00302c0d0303200074480000d00001c404441241600703c001d0f042036014207000c41994030b0407806400a007007081c1503420640e450b4200b4540300344010f54401c403046c3c496400704096405419100c0107140d481c10401400c0c1810001600701601135803d007501003006865400104a00701d401410a44ea203071641d001500140c45541d1260754880c000518107400d402001c10303851a1603208800030444004003040c0305481c0d000c12922a9807040d03d6018402c00b40c2020414524124070894036a6180f41d1075158 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 40321524 1250 40320274 40320289
    0x40f1407060309060b060c0a0f1e0b0105030609010b03030307110a020402040f06020d0201060605040b0d0b030106060806010315030b01050108040302150f1008011401030201030b0a0302030f010f14070215040809 92
    0x40800081c0d1942030f007406120080c41005d80101d030682d451850701500d85902e5a80d002446001010898505141000d11185141010300b0b4100c94100792806000341c10011240e007828080c00f8840c0c000c900100b14a000144211049140d014002d1411760b550884241c64110f024280110203020b0160250016502c0e88001d1003c5c0085480c40d030861814010f00914190300340200b001560315210b024407003250400d098034100c8119400c5190758059041014000e4400100b07450780560900700c01040c1e064008038502d20500c02a6020041652031070414080c0c0c4115101c06401c41c1042001404075512880e4075035849030003801129030519229401c0d6500302003c0b100b00000420900c00d000c0008c1c02c90018200602d00f0b00c00074000601708400501c003002061000a040c0340d81da2452034855141c2e2041e00c0700554009044d240c10050141c031040c040d10400e010341541b40e184c06001c00320803414100d0280120f80c01e90090080c24100010b450b03440d003004e08117070f55a07041071080c0c405d03503034510700d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 40322774 1250 40321524 40321529
    0x5010b161103070515180306070206010e13051b0f0402070b01050603041704060903020307050103090519110301020c03120a050103050a080a030902040c1707031e0b06090d0c170303040b040f1407 85
    0x42aa5840106e80d1200740908001d961192003604040140048507a001820b40c0c15140e441c2580161a04c43c0d10725074081d41802c100007070045c0101c00940a21044042c40560070b00000e4804179401c1e111202088100d1241d10802800d41c0002c40042c411801e00c00059070f409881078000c441600c0441841260a402c181d222100042c40701400b0700441c02d0521002002740300a0030280200b410b196551a00d0b445004448105a821040141c4c1442069040403155103c00740c021584c545520642c07a07200e03800030300098144100000842c18140c000d1240504a9405c50040d00c0d440384290356110480e446801e40301c0c205915602c43c040035a85030711503005940b41c65140c4039000305600032038100981d0000d2851048c075207000700c5204082515101d00f80e99000510002480c000034100040703540c0200c28040c1e42091000c89808108520750789400142d400800c1c0001321103e40741c0300b82d5900e2008a8000304405400c1010900054580e258113884c030344504040001c01c1c6207016403d141101c5903 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 40324024 1250 40322774 40322809
    0xe01061d04050d031a010c030c02040c0e030c030c010c0201120b090114040506031506060903030d052d010b040501050f0705010504030206061e0603070f090905040c0905010b1611030705 81
    0x110207020400000308040220b220f00d42c1014000d41041000c1001c5607001d1a01c0c09050111443d490820144601d208500042d4003c0080100c000c01c8a0004d104109980500d0b000b8822640380c10382034a000101c0701080c05059403109c4960801c0d50045540c140c110010128007615010518002d54401070514060810318000380381c2c0e81511001c00c425250080c00030341c041d03040202842d075800500c0540729445001901e10310743d91071107407002c00e10718030a2114003c40d00746040d00303010740e0400340d422540c41100c9e40d81030302443c801c0d0307006901c910002c01c3c400c058028004000c00c03c0194001c4002e410b20080c14145a0f051000549550303095482c12102180182c03c107104000c140d252080345000307040320b0307100021003803045100880c0480c40301611710310510281008174000d4034410707504170000d0060414180b14a04091400d028600010f0041c0300300142440c0001c1103801c00e00c002d46106207080c90105460030010f44031942016650f44a0303035010b01408202042584421070281c1c40c0b00d010 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 40325274 1250 40324024 40324079
    0x130f0203070801060c0b0103020f0105070203061311031c0c11030a0b0601120207030509060c240f0a0209060a11070f060e030f0a050d030c020a120206070806100c060e0106 75
    0x1800c001000b410b01600440203001001c40030304c000c106c1070445641940da0644100d4004400328005944074060000c00030343c113210b00b20400001020000e50680c0c4144100040b1407984904810513490740c0507001e420041c03407201c00005200741d104000001c082030240600e1019071000c18003003414010510410b44450040c40140b00007540e02c1202071020040900085003030140594005200d8032a13200c0c3c01d44181008600d83d03410b0002405410b414210b40380d2944e18018592a40c504560b40441d841880c0076003201c0003600c040000d0080383c101c0c03600104554030301400341074142c1d896103c11404000e14400c000001c1090803d03040060090582138440da803941060f0810140780c8840d12040e400f03103801c03c41c8208001600060081c40700c1310141408070740003480d042c00303e14110751042c000d0001411500101c40c01500850a02e004409654500c200d40c0d0f14002072040d00e1400d505d01c0030006200800007000b10b900355200402402030500040b0b0415039031518202c01107208600030a28101c03 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 40326524 1250 40325274 40325281
    0xb070e01080705040609051315030302060703050702060609010326130f08030903060c0c16060f03230a02070302030c01020301271404080d0219030c090605030405030d0b130f0203 78
    0x700248040e51110303052520318075150910340020300b062440e1090318021a60112039400c5540c054100c0405000203540c011402aa01d0a000350789110030740e00540072a00d40400700380c103603202040d024402c20002c0e0004044c6e910319035070b0502d01d1803d000c1c886a548014407500500d0042200100080e021403e0100542c0d81494500300c00103076542d0003000e140d4400c010391507068401180d400e40c4400d180801c252110081c614241c241120f088032810f004040d0040400d41c250800c0c08504100794136a000c1241114000c010101c400c510910605805610300000701c00c3c000507001480c02c58841d10560b800c0c800c000c120542640c00a801416140b141000200c01c0200c22100000c919500740d44244044e42070881c036902c609201402c05441140300243c0000481c003107804076401c110300003401c0f105144045e000103004100c0d000301400002c143c20710002c2c219200c1c0d070550f4042c9030000091490028007010a0008006841580303400800a171074030204e081d0588a428568006100c01603524036 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 40327774 1250 40326524 40326527
    0xc010e0103091406150405041203021e0d0c0311030405250e010803040509100609060320030406140a060305030910020a0f050106060206060901060f0809070b040b04030c14090f040f0b070e01 83
    0x401078409031b40940d2918080102080030b0300031810b2961010b0a0040c1c1d80d040b041003281c00c50b0f12800540e503600c2c40004800c4c840d40c20541c05440b0f80d04035980c00304016010b80c449200c281c4825180034042d5400304016256000703030720141d00c144a481e20f164980c903561320090320000250980c4044501d4001090402281c2044060644e20180401c051074070141130a0001d0310141e0300b401000f003016691501e440c001c9042c00141c44041e2210850180c0b00d207424038000c000703052244641e0328101503200c00718600c141c1500614003504d5019020718105180441030020f04944052801d085100350b000c03482c0880c000110300986a07000344004111541003800292901c00d028025500075411400100f0a09501c0100407075803405515054030a5242d4440062501005404c265103400d00007800041280085005000f1648104849100310341d844840850a0720b48103503054002e0320010010703252103035560784107134001c0c80b40007040c00525454840410064088546001090750300d03144280c1036 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 40329024 1250 40327774 40327801
    0x30b19091b09031a0406020d0e0604060c02121b0a0b090a0c050906010f0c1704080c0301050108030306061b01020705030304030807031419020c0102090d031e0e030c010e0103091406 79
    0x2440c1c0c0e051504040c0d00c1c598130310389402850402030f00c48840f40000b040c200300f910313011606006881c00b0240018400742644944500d03050703900f122180c0c500f0f94680507440c0003203210203146804840b01800c00c0002c00d040103001c00c464505000d1401581a10000150760000780e0707001d040c4482c010280780d5094509410b007c1d803c0c0d04000d01c40d000310b0382085496a84064400c0350980d962800c03010080b40c601e00b5540b0300d0400300742c1c05440b02e030100380800c90420010b040c15080c68100c000740041d036641d1010a0703d0b80320031744c1c400f900b001e02004001c0ca021800c11040310404040000140341c41015290141141c1042e1002c90024040d2424000c80d01e501d03000d515403801da0140721848070308101c2c040030141c0180100c100d00e0150046001c0c4080706080d4143c0d140d14801900d024144406407800500f1501c2000c1c00119051301611640715940c400d496074041103030064014040380d0303986001918001601802141010703281c021550000364002d04940d40748464034020a114248895420b004 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 40330274 1250 40329024 40329071
    0xb010b0705060c0702010509030a03020313060503011202220618050a020a08040b180601080a0c0b030c0d0f0f09050f010e0c0303190903020603010305030406030f020a0c03030b1909 79
    0x240060040380042440811055000158500100da980c8068801682c450081d054201d625000b0658100c045c9500400180b0014003c0200443c201d40c41303c000b52481d02081c00f8032000885450703000300c01030510151254003040c00100c140c2610f40c0100c01d40d41661000d820510398000f00003101c012409950103440d81203d0704400039402d1045c11000105080780041000c1c0c55154408041010341c946e5640c9410003150090036aa215070b111b4141c1c9a03604287e1004490a8074900400900000390b402502d01070600f10055500d0010600b000102800018200701c100c0c95840c49903081286035407040603e41440b42024000130400c0703191607802c42d48a550704001c2c540061443c5002e0303580100454413003407068100c1002c00040c00c4411900a80b29400082d002100000044203002d00080a0412217565580901a5100c2c1130018416401110024408604004040c20001c4c0c0a038218007002d090150a80c08a4a011040402d80320b03d141d1000d0720300d5a4a00c034904a000c0040e440518 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 40331524 1250 40330274 40330289
    0x2607091a0c0c1c0b0402040f0204090b030f0d0507060c0203090402070f121805040203090f011104210309060509042903070b0408060402091b070b150a03030807030209010306030803070c0b01 83
    0x400d0a0f0840100c6503158001c0d0010400e0650000041c00c550f00ca5004124130790700c00d5000c40d180e64035180c0900080c401100b441d446441a518a104142800110304042d40040e691746030038210165104000b400000c13102c40d080d400140300c2a40740303440740c1c406886000c0c010010782d942a03425003445c44411001c1c0c12400c04014800c14002c00350000c44403100101c03a400c1e200103a03696030b40c400c5c4609141c101c0b4050145542003141c0b90080910410282080d2040494041520080d02d500e14a18000755803000340030640201e010883c0e11300440160980005c054008580541c44080059090110308070340100e400074440c02a965080c100200009030540c803411514207410114025036819001780000d1041ca0000000b0342c681200c4801c0b0300d0780d9005015015210b82c2c4503d088101d451040b40e5410408904400c1807803540341082007842240e4140e2115102525480d4007203003c0e6114800c2107060580b1640d0000c00200e038a402113104140d141e40325010280c084c41d0040c4401e406a001d0711 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 40332774 1250 40331524 40331539
    0x910020102070b130b15101815030504050d0206060907080603010e0604050715020c030c10053006040b0108010312090308040806010801050601050708120403090b190206072607091a0c0c 81
    0x120786c1c0c0c95003c80e084e803110301410480f2000001004034060a962608022032498403822112038158058110b540210300c16015076540c090720300005c90791004116044c039440300c03048000ca40318902030301c0a643c000350054008118204c182d900b0507e0680242c0d01100d469014580400c00081110000c0410070120320250100b8000d003030000b56140c0013007280520980b00d01c003c8842960051045480040c0910916131402e003d000103c0c090901d030043c40d00c4283d0400000503110b140c644104100c164051315050801d9096840c0c4558001c4421118414054440300200202d070000021304010710005004014070740c1090365890030746101600060510009203c105c00180f122401d0300e03081160720f103140e400c41e0b5440c182103030615510380c49807503421000030b10340700041c26440c000021014a90212845601e84c10320440b0f0302e03084d40b428043c2205240b40c0c0c00200c0c0c5030811009401c102103181c9880b580351a8800001500080e01c10000c041c131001803100e180d404140300e10031490b4001c8806c4e1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 40334024 1250 40332774 40332811
    0x3010b0102060c0309010b0a030c150306060507060911030a06060f0806091c140408060a29040f020702040204080703170703170712020412060605150910020102070b130b 74
    0x40d640c2d4501a0550456140101c00109158400d5010200d0004000c1280c512241d90f42030808a156290044058200032034245c803800c1d41c0640614022100e07540e031442e182c0b264623100d160040814203030890b208180c14041c210503640070081e400300c550007108006a064503011102e070a05031154440c01540e000070782000304125010800490a640752013070030f02c41e203041050486199054a8614a510704041000310b035101000580a10171810840100210340c055201c5118100280d0f100448895858031044501d08103500034003071203141c0780301c0507040581d95800103080e03801a270003420a9a0010303400b0424400292000403044001030040c030700e88225a100140240802c1d02c54140c042c3c203100c04602c50622640c0c45001901c400f020464907107131580e2021511100700d00054901d82c1c10200085003d01c2c101e620400071030701080b80140b916480005004600054016103030641d5030174004070b00070a091003071441c0b0405022559074078034081391525181501010305582c20002d1000f0aa = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 40335274 1250 40334024 40334027
    0x5120a0506011e02070b040608010801050709030c0501050705030706090506220b01030308060d020a03050106051201020f030103020f0a03061103060411070c0315150f030302010b01021902090c0403061406090603010b01 95
    0x283c3c050512142c0e1030601038039443e40b0a074a4010a0b5225892a02c400500040c1c0325a00000d80350603281510003e1219440f034201c200c5210104e408007404166101d0f104211540c040d10052404034840d50580e400c00480b80c0b1804121856414141e800350080400c002c60f80c43c0b1188030214401c0f112004a1000c886a00c600202c0030050000409004080001c18101c0d514065030700003035a402001704070300a441e403501c6400382c8854030400340113010405010300b4254040c0281da001100000d4a40d05580c61034003040520726010000381d0b000b0301c02450100204109005801f03100710700b4001142d0740c0c00e1003014013046402c2454044035245d4148941c0c030000d0304107184601242c1e001201c0c0c2049003000c541c240010003103860400308058210400040100307a0540550171640613800030003442203d0070041e40c980d0355402d413079420040150f45240c01807409004054000c80745c4023002d81041e07225a40d65044642450b00e0145043c807035010042180303082480e0a902c09801d074000d00c00481c0b603200 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 40336524 1250 40335274 40335287
    0x1403010311040b0f06130f330e0307061706010c0f02091b0d0b0306060402120705030405011d03070204050108010b060d090503070c0f0f080303070503072105010605120a050601 77
    0x404501c515191110507070f250740c03840c03d0251804c40081c20b5680da09601d2607800b5080c5d545104540868580d04800a6a0300d048201c13224a1890041c8401d10896243d522001c10301840b0810014000c00080c0842151001c201c2d001c050459603c8034502c4000320061500c0c06c00e8020b0240c0c0c100000e880c030220000d103405080903181030b03040d9050b40c150f495401c0c6a05421540c000282c1c138459010402c10100e40240e00200c100703100650940d50241c580d00284800e901c12040c454520116240c0803410041c4188021a40305000364000501c04421100814149280e603c1072096030f0701c003043c0c000a52070700c1d118245c0100181c4002b00315a4406001007100c41c05200403e00d04d469840c1081c078103010090045403442c48d030003c00c804409484402c1aa40c1d18900d00684560100740d4a0201c0c00910000072240520702c540c0f502070465a030381c00111204d41c5031920f0315820410790b40a410ba50020744c002c080c040d212030784039142c545c1107071800600c00300380040040c2d0059040805120107a40c0060317 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 40337774 1250 40336524 40336553
    0x60e1903050309070e0c120a0c02030703180e0c0306040f09030801090b0a09050f0708070801030b15041e0b01032405060f120901050403030b01021605040e010e120a14030103 76
    0x107226031250f4070b4980c114103161069112a61040620f020401180d40a03030003081e0f54112982d040c002c2d9100c20700d180d411a10f202008101581c401c10180012a00481c0e81d40401c0d007003d40044a090f803201905a0082001d5442405004c008000d00280703162070302410383c50300702c0ca5004219208903074500a08021040c881c03c1000e0b0398071440001c00c0d40b101c02c0c160000c1c10986405000c5402d003900300c100720140894101000441030804204040c0c8038800b5681200d4010840301490303211041c0c54501e100e50b1105655005980d004400c20200e098070400d100011490700c001840c030022400501600c400301c043d440100c040b046042038466089880d541900d0f0107464140c0c0300c01c0007d000540600ca0482c203811400080030420400c0141504824403403482503509010303a01100c0016a9240c041007103070316110340c00700014012070070650f011113100c0d2001c000109109056103070250828181c100030114141c000030304d038221035800011011410038200406451503140d5100c6a000c1100807 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 40339024 1250 40337774 40337777
    0x4020312030702010b03070b070c0509010f06200f010c1412150111060906040c0e06100e01120e03071b0612110409060b03160807021023040f060e1903 66
    0x8000310b03076103602c00d600c40c101640307028089030813181c0c40310400a45508500740441d603040d0b0b03804000ca05428601c082c2c0741282c6000506074071b40d500301103040d103217550240d0200654801e0700b9245c0310026420007850800410420001500040010b401840c0c80308440f5101d606074400c10040844c00c0199a08a5100c8480e0403034407000c116020040f100c0c1a030100450303803540304260a121403032202081c80d900a500c00c544144440d6603e490a0040702e00c00c9400540c012840c0d1060703590a0b01694031040300c02c90524107086020340c1500198101c944404032251207600200d1058100600468824843d039410040b01c0139992030200000c000c500d88456040d01280c0b039030540e42070702189201ba01c000d029550418001c2980300c8102e40110b03002180c0d0f800400806181c0054054000c1c85690701881d083c1d80a0503040344070034010700241c098210a10f070603603840040051041840203205d4000c911820051159035003034100300c81038032054440804240c1203110f0060380610210302110301c56506 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 40340274 1250 40339024 40339027
    0xa0311070209010305030310080a020f01030c0c080f04090b030a0f08072d061b021908120a090507091103010501081806010807080114131112030a030506120604020312 73
    0x1821892195405035090080d0060749200002c0104400440a144100081c0810511943d0b1310306030035550300641d44019400000d658401c01140d4483e0304442005100b40c03c01c0c1e4801d0f42c050380d44643c00d50046030716020544000c02c0a0000715414002c9d070b008220101c00912000300261140c20115400480003090501b00281c03000c01c100039803142d442c112041c0d0b1f910300d05480d10007901404014402500f21081ca181100c0c0d914244982181c2d1500100d6660081c18100103002000d1003d05d4134840981e1550001e005412160565400d100e204080c001008642c0641c540341442ca4500c07503030021025a0704001d040e1605000b01c8040d60704440003407810f611280c03104610144800b44036403c9548600400c1c0001ca54400c1c0051090129000b6030000c000490602c042c030391100c070040d280b0001c40a5121451004500d218800000b0460020405900a07113040c10143c0b465000340c4690000c0307034440f41001510314000f10040407001e80e501c060801d034589a40044c3c0c0f10f07003200040d04e80a080 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 40341524 1250 40340274 40340291
    0x1110403020330031e13050607030c0903060609060f12050604080a20060103020a06050406021905010e10051906030f0308100b1b0c030304030f0602031506190905010509060a03 77
    0x4410300c54001c110341c0354044039503a0034260300042d81440d8003944074003117000080220304061900c000f94038910390400040d00d0701e504d41000840140610302031040c2004407444002c00803c1d0366215020043c000c40305d0002e441d919040200e44007071920340c000720710350760448600404184003054003548039a10162032507403814a00c2d019034035007900c0c4084010110280b00346e1340805000098043c141da0007196441442541d0f80000c40c0c980c86240a001c3c016006115446102d00f076a10503003501501c11f90003c510f01d15600d00070392421040c0907a072860680c80340d0a0002801960b06407060001454509200d4942541c03503040d580201d0319030080821a9000004030a401c00d441d50101624556820382d590f811100c45508c8044079500540720a801020309502c86841c0000886048a500040950300d032401c41d00d584009400041040302c2c2c01c0d4800d40100748964600c00145190141800c50b040c110055080c01015848943c00c41414071004000e000c039680e4800341a1100c0301c00514000c50843d0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 40342774 1250 40341524 40341583
    0xc06090d110109030c0806041709031e070306021c14040201050412020307090c0203070c0e01030f0f060e030d061409040c09020d020904090f0b0f01180509031b01020c011104030203 79
    0x126600260800b41c0b00345d004540000007089503030240c1c1c0504901480380e284101402d12a100c6c1c2d07150158980d2011a030122031000214040d00c4500b07c66096034101383d41d0307403141d100741d0b4010781007100b4a00e04060480450b4415100304003204014009402d0546407550020341544514020b1800d1454103000341c1045540030040240903240c500c90070321002c444a00c000e55a604200000c035412a070a103008030310519646020341c101c0c0d4000c0d80c0801118155110740081200e180015145240c8600b52500740d01790030002090440a00030002136146e00d098410405404c240c40702522581100c01800007051600d400802501c031900d50041e580e81c0c2c0040c05000038444c54000942050400c1079440c140050031080140c1c49000c0d0803540b0760b1344d6403110010b0201d60240100c104407100140ca44e05419100e034001644170b0701000440780350a0582d985c0e100480d42d03603140c80c10103070740020b032501d8852000e002e24000b82c0030640d1803034102400c56000036240e0000c0240d500d4180d464822103003058 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 40344024 1250 40342774 40342787
    0x7120e061b13060504090b090408030105060307230a0801091406010e0406120f0b011d040f020a0305060f040507050301020405010e10021f050106020d110307020d0219080106080c06090d1101 83
    0x2095110440c02c0c409990b4800a0120780042c0710703054407240f528030000d0480c2400002148034513800604245580e0801301003200c50340001d05400d0800883c202c8403800c0c80b101e501d01080415900e01c0044c0c8945400000804040d0140c00440401c0c1c14684000401c00c800c2054071740111090800343d100c046c110020500500c40b0f0350001803041d180300e852005104040840000c0300d80504008942680c036550010030b00c56a03081d0714000303e062200004c000c00c2c2c0c07070188642c64601c002e0074106210741c1c94379a42e00e032440503100c01503016541014041000010021400104000d4000f58200b51403c1d00107400a892079581c40d00560b00503000b4804036100784000d0f0840c83d02621741100458014400c400200000d02a18025104c4c07e82e591003420b0013440d1180d01e8105100040d49801c109030b0a0003030f24808480b08036084001b1544015081d0580c602c0344019085890000503551320b010641d614150941d80c0b1a4080c220070401a58a41c8500c13040000898111140841041030b002c0100d499 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 40345274 1250 40344024 40344037
    0xc010f230c15061002060103020901120512120a0f061511010e0703050a032303060d140102160b06120303012102030304061215080613030e0306040b07120e061b 70
    0x40340100300101c100003a0b8040b000d4040d45041d9040303001914a08416680c50000780000395001c1c16082c01081849528008034040768800d0054a01c0c280c1d038580441401d0b00000000b14003116174008002c80000c90344910b109401c0f0030328042c002c0c01e1134a804002c03246070036411401005203081184001e5030003500414481c4250308111540b031607072801c00ca6151500b11070b04400150700d15403440d1968040f025010200800001ea60b45183c40346804c01c00b03040c01a5a04a800e04509800f802084400384058440909018400b0021072614500580d01d94001444a0300c10307800d12245038100040001901d056540700b03821070262100c118008070301c2c0514800001c0d8184000980400c5d82a4080400c003071205c40e4003410f01680d20300e0080d00914605c240540000b990003c80024070920746c848090102034040e04050202e401c6000120341003074011501525284081c1c0c1c2031010030751b8005c0303d1000310752400c2c0c800c1018186448071680c99840261a658408620350107880d496070b0340f002107984 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 40346524 1250 40345274 40345297
    0x606030a020d090b0c090102100507020d03020901020a0c170c040207051005060a0b040303050a09141021050a0203070206061801090902061c0606030501050f0a120c080a050604050c010f23 82
    0x1315213482c14440c4000e0317000090290060080c007035418804001130082c00e000380ca10703802404504902607000c80081d0003208119045200c1e080c00c03440410049401c450261007100d00100c21814203800052810102c1c59815004610412265000c83c002040d000b52822489801140e1034503554005502c02c219900700c2041c00c00f00080010416812100804405180da111800070300d60340c03006140c071719023181c5040740c104242d0010340c1c00c031a21480c00e00d02d901c20f80182018450402c2100705003114011a500404a6400828040455010400150300c0034003191001c12031526100c005403c601c1c1885800c1d203180d00c44090754115503a45040d40c0e44000d8102404602e01c88000d070040c0038140510920ac0400d00d007400200340c40c141200d01c1d803158030000e094084410b14000c0c0c00002ea841c0075006803801c1000c1d580205140e0400c3c4440004e940c040c0d40200036134106410402d040884003200f072410302004089082025801c940d1038545c0d90080c1030800e26000d500500a031707941c81447c500c0031 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 40347774 1250 40346524 40346543
    0x1060f120b2706040c060801030302100c091503060302040e0a210306090507120501080606150309010204080a05060106030b0105030114101101020c010c020c030d05040e04110d0602090f090606030a020d09 89
    0x842c660b0000641e50b101d03502400324260010750702d04080c0c8003100d080c000980141c100c5079480030130f41d10340d4000c07040e49085442d0006240369103030140c0c107609100c035010704006500c07210708006600d0705024581c040c3e0058005811101195643c00e8020822a0395861800c00c2c44402150000e0203540084000c12640d5024005450701c450002e20080c0107840c2c40c81c106191000110300b50074002050740c82824040d100d1456100c040d0031201c0350f074200802c0c9843ca03640802011880703030414003160f030f0792520460040042c1d50410101506503081c202081f810000c0600c01004070705240c101c3c42403410740a0310050120000080c3c120786140c48a40c101da000d40c000103565034036490551008080c000e881d800e40b8285540038013010b44a41403103092400161017400140b10403261201602d03041440340840c000d10450381400b160f1040707503180302911901d5010541c5001410b1145c91b0b47c070303400030441d00c804152910200041d03050001500500960b80c4c003048114001c03d02c1d501003482c0c1604220303a038 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 40349024 1250 40347774 40347841
    0x6030619080313090c110c1c020d03030c02060a090305040504020306180903090f011d090c130f180c0207030b06060c06010806011401090f0501050a0c2301060f120b 72
    0x401034541c03e40303d840f559a10308151a101c55203c1d08041030942e60813009004010384480c1008002c0a0406030001c40031904410400180d0f5458810404a4460740303000ca010500444041e08040004204480b11410b220342c0000003a40301c400c07682542d00403140180c4a40f5900c012650040d28610611402c503040b600344030b00c5070300010190003101c40807038000884880e80c4c001119881c55103481c0e0265194586e0140ca0030303292206a042d4001d8515109a06142d010b0010072071501003507000c620680180d4100340000020418225042e12031484103000c0c01c040401d0095603140688400b40c2803100d01004200b560b9514001c40e16040083c604840f45961a000d00325103603503082c41a8285038040c006011410b501510490b41218000b41c1c000030814502001522154051014138040007208090780d0f000441c2c18000030300d035150582c04440d103400c80c00c0d0603e0840341d6036040a040000101c00401c44051416a00090941d00143c1005146c541c4003101d605028803503d1070704180e1128044 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 40350274 1250 40349024 40349047
    0x20304030c02030c0406120210020a050a0303020a021605130b1c0606050306010509040203060412020309040204061d09010b040512010605030d02060708061008010e040f050105090a0b01080c060306190803 89
    0x720766858000c9003640d801409034000c10044030424407410003d03150b400508030240c038000861181e0092540107a41306420345560302d900300292160110b0200e50f001c900c04400f99410481084078100740c4040000c041d05140014520355400b40c89400025200d00f900c9109440311041642d003207001502010010f0014a011000341c042809054040c0c031440d00000764502e0703c3c014450280383c0290250031076869903110141c20142e001c01031707001c0d44403c001d074140c1c82d01d50717100420082c2070300e507201c03080c00c440441540d400700c4001b0007131445507000500601142000404640c1224811103420070300d0240f0051440c050092540051707030500a0448814002c0c1c1c001c01c42a200e001990b6a480c01c0c3d9450204203d241c400d013103140b40000f020240180b21050044007115085805500202191342455030b903a802d440b0704a91624040c0c02070a248801c10075408400c90240866201822200c2c0448003c00e02c41d00000f04128820502d40d0400d098400c542034031500603043d4801070b01d0303444410011 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 40351524 1250 40350274 40350287
    0x15060f030f0603080f0307090e04060209120109020619090803030405010605120f03090603040f05060c0a02010e06040b0c0313150203010f06020c01090501050d0b040f2c0d180902030403 81
    0xa040200341094102048029103202d02c10540381c2c800c5007903003401400002c0711a13030b0300003c02c80307005e20000407030210f5001d48580c0c0e094491441128096910350101c024800c2e003040b050310b10107840c0e052009020041e6644000e41d105170f18201c44601d4041c00504080311945501d0780000510302001080c00144607040d00b22f241034400589008a607601d07251151565078841040042840d081440810345c24a440002503411034000d204001c1104e03a90b0f100c20341040401d46041070310810021312084070540a0041c0000c400840c8043c001a2034951130300c1d00e2044004080d50701c110000800640810030b11903401c240b00f600181c8041a03020095541c50095100f80110070341d50300801c00004001d80b00140b02d108161041c0d613510305440c503102c01910b90f500301411421646468040c4e103441707900c0d180701e0921140c15810010840072015010f500072190320301a4014030039100240c500100500040242c0c174003420340350401542c0c0701c01d11807400701c80070354201302d840a0001083c4400d040e4450b0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 40352774 1250 40351524 40351547
    0x207050115030804150e040c02010501030b0105040e06060409021c0609031b1104090512160b0108070303020607081f0303050a020706030e0c040e030d020318010c080c031302041506 79
    0x30080050380c100d0300d40c07001000b48002011240e00f0030052000040504c03d00460200501303261151a05040024007038a40c114020030050b95a900100f052041044c0440e005000940e000c03c1514020035240380c4507100104542c1c0126182c44418045441c0c90441560700f070032000003080d004d0301602d000b4014025848007a0005498a041007811901500149507170940c80140c070034210b80c0700d2040c00058000484c0070790740c50050b001c0014010f802e00b0024105100e617040240b030f003550b45140168030201c042c0c21094069118007024030000380c0000304a6044042070030030880c503a03500d540d4103004010348040c1d41003411404000000309078104000d031140d00526000e65240e292541411400c41c0c8a800e076440701c503401020300e1021410240e000701da0300c8941d9000d50f4030b001010400c440507a80207036407810f203a185188040940404c20f202d441c824181c2e610b401202800c082056074914040600b01803c1d4100c0c16043e04110f680c1c0fa070000c0061021005025109691614083c0c90782d4000c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 40354024 1250 40352774 40352783
    0x1020a1e062306030606010e010c020121060603050903131a0c03130504050f0f07050c011104081e150406050c0904050f0703060905060d061508071203090602030702180603010f050a0207 81
    0x40b408100c030f41c500481c0080c419030307040c0d64800d51201400e00450b42550701c0181a810300905080d20340d2100d181210f042000031000300d0125125103881d0004040301d01c01405642c0a4009210b6090b61040c0c042280040304c425210025002c0c5624031449640e205124844010b8400004c00000080040d102c6a040380d004960400803940c07810740190002d070341100c03590703070171311011000446450007900034221a81c041e200000d80c00500102c090f40d50340c841c2c0c11030f503980c0d13000030b24145400101e900c0300c0001e403080c03c01804c20500329210200c05c44c8000303040240400d4442c0c002035103007060303c0709495003054000c2080c8428200754288007080038040c0c2d0f03a40000b0382000c60101d0360305010302031039000c1c1d14080c0110b06070f5030164480e90024031081c01207132450900c420000855280401194000c2c2c86038212038221505549806089154540c1c02a41035410038010700000d40e848040b1900d41c00356580074001c2c1d40d581c010003e8010014071582c03131900d40c075200034815424802d501810714641304 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 40355274 1250 40354024 40354091
    0x51b150a0606032a11010204140306100305070b0306010e03030a0c0b1003020105070209041b0602030a0f0822060b100c0203010b0405010b0d020a02010617061603020901020a1e06 78
    0x80b41402c80c143c505400d9070507209088064000000c111520f00d1111208031481c211100002000049013aa070003a07100d800301802020030311529140030b1046682204000801b05070191a40c0da8880d2181103d00c81e00c44a010040001542a4050000c1c80103030440181034980e5104989400303040140c0401055900c9854103000501c4502035410b1718080e00d0301619440d0406205a00300302c4401401041241d0310350340c1d000500d81c00c44c202004400600010380103551550102c10004182680510f009401c02c2610014408a640841130342440100281d0b80510055218102640a0b200350801c86c1e82001c3c030f011802c2c54682e809031140100910840c000d000d8801003404120035a0000c0c01081b103a5541040070401e1102d499008201186050002244a07507460702c446e0400340c5a4541c1c680580c1110040004c0c00358205042c2002c100b1a007800c500342110100005e544203103040000b840e05442c240300c2d0a00749604402c0c94051540511300b40504288001c008201694a85909040103c0c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 40356524 1250 40355274 40355279
    0x609060106021f020d110310030b0f060d1416060203040303030e01050106020309061312080901020105060405010b0a05180406060309050601080106050d1203090b0901060f081507051b150a06 83
    0x20120785030101c00f03c00000486103481c00c82d40007009510054a40c400f41e5640c0c0d43d00f540b240d0342c1c0070240d449000c00728480c1c407500d407a508200005510060100482601d0041004200d507914600141d5441c2c01071900a642301401c03180c107142c00c1c4003012035540002c18000004440d5030000003002680c1c0310755000d2054502e540191800d84200303004103005604144140b80f000d080110241802e200201c1c4800781a940e20800601ea890540300305903890000003030070101a50302401480c0d00b05006131070400842d07140801c018030f0b5000d140000d004202001804505650303540068a0341d0200040c020402e4a0782c0d901e02074020f0140f850200c0703403030080100028100d0010320450381220b20280c080202e0040558507465030450f030020b101d042c9951745204002040c1002c011500c90b080801c00090540c4c02c140710302c101c190095010291584c041c8031011840c4604644990700020b032403c04548460300c01c0c04040000705e107a100c010441c4103494802070540d120501c0745000d0a4481c004001c01c94 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 40357774 1250 40356524 40356527
    0xe0a1b05090f01141f0206180604020d140304080609060103030f021b010e0d080d09020a080309010203071104090506040b0406060527040203101109120105060d0f05070504020301080609060106 84
    0x1200310b4500701d0b91071100c001007240b984802180c04021800500c020034042d4901003528002c00d401e030704500168091320030804015030441c034034490154008020002440c1c0b540c0011242d428045004003c041184908003840c0d208100307071000340001c1300c2030b05c81c1c5282124484c0d5640c0000d04c001d500040c100401c0200c1a40041560510840401c1100000824101c0103443c13001d4040d40d466084081f00078010003242c0800301800c600c5500500118903443c850040010488135504603800300c1e08100406455683c0010880b0343d8558010400111044401c000900611507100e014195010317800401c004c00c000b0440711071043d8842d140800c4290f8848040c01418243d204001e03050f207000300c20601401300014101c6a00dc0d03c0102103407208101070300b40c1d4040d950040200c0c5070f0728402144000107842e007250650404181c04008204c1480c00d48001410350020f101c01912010302211690148482400040d000e080041c00c15036484d40d4801c00203580b114125040f02c2e240c02254004107055 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 40359024 1250 40357774 40357789
    0x605060306060a0503060c09012f01060e01081504080c010c08161d090a0e100e06010915050d0f050d0804020111060903031f03120503091603150b03010e0a1b05 70
    0x1aa4050002c240503580c3e40c0c07c00304a031344001c0d4024180040f1100c583c0305850340d40b550b504294004002000f0b01000c0701d800d1401d60340d0b0f0340c003e014508080401405034540008010306a07510700240c001040d119414580c0d4184215040541694208980d0b01c0c0707159041500140154102018040442e628120031100300d44281151400c03118021078804c00361403c0300c1070740d4006813080000a07940450380c2c880ca2420000807010b58005031a04186940f806040c062640141400c3c401030140780f1007410700c0f411004141c066a4442d4940e0000c40b03040c049035802d01c0081c598080202c4038000d2030200d010346aa03808480032030000360581400700380d008000c80d04a00a8081d10015810f50312141c45070860000002c0d11a82d01d0503070110000701140d43c400e80740d1003605c002d0300c50365642d0810440c4c01d030408640600c580c2c07044140c01420400525540b004c0302d04c0e41d44481000920340207140000b030242500c0e5200c0402032049294540500c01d810540c0c0c103034040c03444112030950760368400303014a2 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 40360274 1250 40359024 40359029
    0xa0b07020a030311030d0e07050411090a0314030c06010b031005030102071703070c02300a051002130512010e0d020a050613050304030210090f060306032a080a0605060306060a 77
    0x403a039240300b0400030f8003840701c5200141c0d295054a00f4a04c82e42c0300181181c1c003a02d4100d00720f9000c10000c008908041c030422080400c190307a130318071f051080008100f1812440c88010700900031044071301000041401900c4072500120156270903940e44030105c001d160019500180e03003110b030300c00000e40f91805208407401c0680c40103140c0c5a00050111140c180d0704000e040c40c09220440c42c050f0700603502d00b001041b0410003850010004140042901050203111041242940c4540d28007000f05400165030340b048203241c0c3d805030b900c03c0f40e5038481030040c070a94005500070f01d4840640d042c008040d0402005000380c80204c8206203c0359504980c0e40604100180c0b42d0340207a004182c82e503241d409440b404500400c00c4910b05940c95011801c0521481c1032240040d4001e10207001c1140e52080010080c0402d00e803d0040303a0458482840d0b8400c52141481c00b06544064650141c040d5039401000344089000d44940320400d090400c0506001c07180c951280c052440010703a0f51815040d00707000d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 40361524 1250 40360274 40360279
    0x1e030209040213060b07080d0e010504020901151e0309150209060706050405120f04030302070501050909010e0a060801060603090203121201120303020c030307030603120807050315040b0402040906050a0b0702 91
    0x100c0e101d5400784918000803003843e0100d60b849280124070b4220f48001001103d20031024945d4411101e07500c401100e00300b0340c2da4100c50341400103002c01740e603c0c8060581941d079001d9850440703031780161060b24900d109244c034050b0508020018208070380c05034000b030003450155017224110115a00104224410f4080c0180d015030180f10f68804141d041c1c3c03200b03a0140c400d50407500d00944031510001c094105003003042030020002014001c0540c14854038000702000e007071041c10b1405a2000901d51581409440606100d03203001410420813500400020110b1030000c0141d1030301c8690050142c00480b2050340248544400164030610790803c030780c140c92001c1c802d03543c1a420080845042010040107804240d024482020950400d100540c005d1600b46c900056a0303181d440d1288040d0440c8030380c9010b11285030104080c1c90380142c1140d07070100c0000d03880e00329281d020b13001400902400f103036507030458408140407460f10800e503c1002a036a0450700c640381155038081c030350080d202c9c0400094 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 40362774 1250 40361524 40361539
    0x1602030409020f0d05130c0f0e0408180d052808070210090e01080303010f060206060117060a030c08010209030f0f15040206040302030a030309031d01080f0c040f0806011e0302 77
    0x30000c909540a0304105a01940640c0b512030141035032401c1e01d02c10307a0300700406e001190300c040c01c000e91902e0340001030203115401b81c2100d01c1c1840e03a012000005201034403c2c0c030001100d210302045040940c0103904018603a241600c40e03414296515200c050b80c00341c40c00701c1d04181c9161001c602a1018940782c0c00b400d254a800101d5080c2300e4822400a48241481481c41020424000150003d4082c003561001542c40b03600d044484042e1aa480d400001550821410b200591740d0200d042e05c0c032428030030803d4800c1d481b1440403550381c9a081e84040c06e0803407000c20100c0c0741407041d0002c00102e102241223a01d103484c950342031500c0305101d00511100e580041e1070b00c0c2001c155038110980c40303400140a43e06040c0c0d6500400e0400040e90000c50010f6507404500e4101a0000d502040c1c5050210500d1202c1800c180042c010709030140180b015111070000051103402e00000710f03805480401d400507001c5540e010100c3d80d8040c2030003503440c0c0c03404c241c05100c26000c921104c041260b80050500 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 40364024 1250 40362774 40362779
    0x60e0a0b0d11160213020306130b01020c12100e19030806011808010b03062d09010b0a0303081503060c12180715030e0c060318030403061407030516020304 68
    0x410305520095180d041d407900c440d040c1e0400901d1a010b0401e1500c0074070308100b2a4410f2040080707030b041d001582003c851041c000c3c001145c40e040c3d4048044000380d80005212810356006030301c0d002c400380d0041d40c840340384070807140c02e880c000c68442071010700100248a051940c8134044c0c2c0360940c03c070280740c20318950740b04100030a00c1041c600b6040302060504602c9001003442c2070401400c41c0d0002034540e9100e04401519040422005a000c0e101c141000c1751030542c2d01e50450705100184d60480ca1202403404102149000e5008640f07402c1c00030144190355a0b80d180181800004940040715407141140e01040f0341408500b591007814202000c42c0f8101c00700c3c84900c14800e02401c4503442d03d4900c48102e1034414100b0410000e003001040a00891803655001020703a038004c507010b00303a41c00c00e41d8a409036071941c40959400201c241802d04020528907200391850095078006800242401c1001e11305580e42e465080c050903450781c05000c9aa81c1d181941040e034075041585005034000c0004 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 40365274 1250 40364024 40364039
    0xc0c03010e1c0311041203021506010509010c02040b0a030c0609060201090b0a0c0210060e100503010b0904030c140105150f01030902091803070501061410090e070311070b04061401060e0a 82
    0x500300801598280058041070784c02100c411500301c2c1e04065151183c21980909241c0c04008080c0400380c801e111307140d00d25240000914500070103031024184400f00104000710b560710380000b132505502070310300d2800c00c0d5241003801340310030303240b11385404a80009000700342284180500f01d2001c0c0c1003982d481403a00c85480e91301c0206001101c0b0801c50141c80004e0701c82d554940109001001032070742c101c0c05801c1809044002c80d110703600061003603243c804200803e490380d08420b51f00c15094248044182c0d081c6c00e20a9000b00d1107806c5c4903295181000704401e050f10303010700d0b0407140800c0c0e0760400c40621240c0150b003150440c1744d01035840b540040015041c5160030034048089075800c0c080e2410240b070b6640300c900b500c2c11508003810500c032441110141e41069100c424032034209103400200b10345001c6d04070203e108040c112108040d1142c1400c0b8280c0c18800c00c482c0450b82c8100e040310740d03142500b400c1c0018030181c4016030442c00700000002d070842c4282100900c0b0040200400c1d089441c0051 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 40366524 1250 40365274 40365313
    0x40312090621291e03060c0307030905030c2401050d02100509030a050123040c0909020105090604030b0a0e1c110c0406080d03111309020a090e0a020c0c03010e 70
    0xc1a040e4480c03600125030b01d8000c1c000c40c01d00079407000249045640c0020441c1c9210300049925410480c1013100074299000158650003008400b14281d4036100e880085015090301c02c070150051000117601201010700150700008160004074540184803406d85034a00f1110030720403581d00002c1c100820001d440e08a031406017500883c00d02c146465514808242040c40300d0704240e0f404c0c0d41d01c2c48a0110484640300340281d0022130301000945240560b036550f0042c21a00423030155550703500390401164028021180c00190003081680c950342e0381c0ca0441200c0d44100c80c104210341c10003007084405200040e145d8907011481c0d0b43c0694003415020b0803184490447d103038610300d1048001820040c3c41d40d20400700a80881409004042001038025090300e5000c9503465010404100034082d140e480407040b4180d0301d60b8040543e540984031400c884185007604200d10762000b490034480710f400998001c100c5c21022200343c0d04e40c99404005c06017251080045141c0c103800a0007e40302e075030708540 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 40367774 1250 40366524 40366577
    0xf070b0901090c0906030b0a09121103090d0b0702010c02010e07181404080301030b09060702070b030601021606080105120703020f040209130e0a0b01121101050f0903010f020403120906 81
    0x20341c5980700c2d101c9111440f240e60001200503600d1505005100050790303039980c040138504041c0303c1607449654500a1355810070040080004c010010140d400f000e1017101d504420041284260440c1810400007200302559940c001d07629105142c1d08081c010302a1003100e04140d0301030210186441c00300322200c50078160007080c0f195038003441d0f10500c0d900903806007d1409100c980742c8030b41c15482e02510f2a800a08420810740c0014200030700f1550009061090f90700d0000484e480e0703202c2c030300180d2a0490345d40c04410074045580d00443d4099110000b51304955007126036070302d41d080c030804945e02d503e070601010303401041030f1984020b5400c25030020200e01f000a08844000c050344100c56086404040420700c141d00200c242c00103001c0f00d403036040d01600e051284144840044d0f969010491080c205607418881c0c0810750f4408450300c04159840d89002a00a124840c0c4810342751000b50311a00044900380f80342001421394600c200413540942d4080d07295098a0800903406078005407004 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 40369024 1250 40367774 40367791
    0x804032304050307030f030e0111060105130b18070f09061403060a030b090a030806120613060e070b040f0605131a070609030c06060603050c0901080a0e060115020705060f070b 77
    0x200800181c94038101300e148010b50152103803604182c0f041c41d0041405c070001c4000c83c1000080180a60241c1e40820011304451080700c030320b0105e006849042d006822149030301a80711203c0a0700c0d02203401c60001640c8140e105648a071110402060300356442100d5000d0140004c0040003100300515000d0021078203d6001090082034903581d58509910482c1154011030790740203c18840d007090b401003100da402020480300329103159001c1d43c440356581c40c0106104189410f10000006202140d0301002085280c0c0c000c1d1402e094440412228a41c0325219901801c0308420300050018031410990703007031146906003110a0b500e800f840010b030180040d0322400c440307010800200021803030311900d045035100f62a851804c0310700e420210103e6015500201c241400c080804c01d071120b1003011100d60f0002400c150b00d807a1900b110303c80040101e40a0341e0000c1c0700d2080003080501c42041c0c030010f00226642241c9039030f601c03602880041d0040c10712244030305030300b03010890004a40c030350382c1c03603208060 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 40370274 1250 40369024 40369027
    0x3090f12010504140c01020102040e060609130e010209030c030d08010b0f040f09060303170714070c03021005030907090902030304050607060b031c031103040c05061309050a02030a060608040323 85
    0x64403030307400c458040e14103c40d8810700020406410900340503003035000209000840c100351a0903094054440c009003000e00c0f82400040b10b0805503120310b1041c50251080b80b00f0440c0d40d80c802c0c40507000750301031440c181c464400c46c0e0b207041da50f20300081c00000c00d40190f6100882a460024078414582010094403003d900610010650740400b104410040280000200b040c9140d420040c0421442c807030b901c0740a00500e002c1101c150780064007c91303001070300d049841e034410346410700102e03c0005810007544400d003120100c00b0140c0c804c0141d0300682103003050340d140c0c0f5610603c2c481182c172940300080d055082400100030038a030400c0945240740c0500c80100c0e20004140019041040303100a001705504480c0b03008c64219410700c01e942c1c6140242c00c000e8614101502c032000d5a12840c072403c1c2c4107020000d15284e00c0880c04c4010070003005000b02c103200c0d41c01e28103c00c0e40079400403902160018504070340060301520800c0c0311802507805441d5940f40a2a02000302000c0070750320350390f100f01e400 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 40371524 1250 40370274 40370299
    0x11809021c060b12011401060e0402070803040b06090603030a02070b162112020c03040b071e0f05120a1209030e060408010203190b060406030504050a02060c03030a060b0a0203090f 79
    0x1118280880100d202d03150004001d208041040342d00300705074041c1c0c10180e1400b8a01070101800078003450549916040c00c6645140c507900003400fa208000300281803036030100500080001e6100c1c22402850704407002c00d181c2e80c440381455500e0207284680710042c0d0180c0303420048e8012000080600100c0516070064002d066142d01487c4c0303e08095040c00000d001d00102c15a503070110040c0c1020b034001d103041d0f103003403907031072407140d03240103500404204800029234501000400120b1b000384501d0040400c0344001203040045d0b6000c072a910a0f240d40c040c01e8250740d0410303012011a03080f00b88035192020079942030b06058004156800086050000c500b0301c21045e9a80d100141c0010302c00d00700050303500c0c500f082d58040c5100080c0200e0101e00d00b811091134840e0341745030944056a0305e5180001c0c0c2c95441c2d05005142c24045c00c2c010350030140000380d025400d500803000718443c80d0400001d220460340e40718600c000703110710703c03c9000582041c000d0104502d00411002e603000d4005110600425 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 40372774 1250 40371524 40371559
    0x9010206070f2c0405060603011a0313050706020303100504020703080a09110405090d120603030507020d060f1104060f080601050405150403050312010303110a02030a060e0f1608011401180902 84
    0x1084401110055114022000d15454139004142c0e01c08800d480103415540350400b80d80c90000702c54482c003a450300210018200400007802d004e103581e00b001c102c40300e441e940d44020b9220b1b407080c0ca90320171040034000080383e41c1c10203000b210b072030b50b6142c0e44d094181c3d80c40c1c28203180101066002224810300c401103005186e601d600605008103980000741c17000b8412030101504810690301c8801840d0f082c004c042000c00c0d003100c195030f2070ba0b40641c4d001030165010b2401400501c1c1e02401c5804c4c0703900d4001c1018000c41628041d105a403d40d071a4084024200c000031341d407100c070443e0b58900040d010442800316040020300140c2050900110340d082c41d0300d95171058159000400f0342070000e0610001001450341c40080241c070410a04c018210110050b00800e031101030041c0040d05103501d6200b61070314000c0070014041d5004120701603484808828210304101002e41c89020310315030800d01440c141d40445801281280c00410104510028001071040030b0b1508010036a80140810f48035690403 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 40374024 1250 40372774 40372817
    0x1030312020a18270e070302010806010504030501050f0103030f05090a14060d06290a05070602090a08030c01090309090b0a09050604110d02070213050408030609090c03010f06170309010206070f 85
    0x80554810a0400c1c015450300c130b41502c0f80009504549070309103280d61076100b0b0301040d540c081c0ca03020f2801c04030a980b01c00042c0c0301c034490b40c2d02c0141291700c1c040070040c05540d00640743d4103036882581c44100340103e250301220540035881c14a80d1291100f14100088241c420000504483c05070000342000a90079007a400c507040c3e81c0c07000195154001e0700c11004101000299903009040078014106543c06c40010030038014003400038800c0f9400208540d480c0e0f1401c444100030815902225034411346005d860b4041d00d6115411804543e10040100e600e41250003030200040c0d001d4400c2059504d403c8164000d044094003698100d0b58460403182c101c10010014850403603001030140c3d80b0640c0e0f105122550882c45039610844c0d01d0700b010700002407404800c60b9041402100c0d0003455882d501031040c10300c40401034443d85503280001c2c041d0000a5030304100c0444040203003150041d03440d4a6429240d12401040c1c80c010303041040001c0d4440d0080c490898511000d00c1c004481c0c187c00080060407 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 40375274 1250 40374024 40374029
    0xd0c0507180518030712050903010605060406020a0203010b01031b031a03030406020d02060708040c03060903030e01180c0f060203040605180418110d050c12010f050f061201020301030312020a18 85
    0x107070b140e50030403e443d00c0a55034100d606500c407009529050b42502d0700b1140f078115401240410400050120b0036a50940088014000c0102059a51607503403201954891502070700300c2c0a9400c151400d0015806031080c2440c4407004000c2055280070384900f00c0040126209000401d580c2105a0819485c01c00280014001d250001c5ca00920003005c06482c1400042c038410820910104010000c0d03502ca00420880350f0100010070001c0e620300e41640901307080020035400e9840c010a240b000d0001d01d10100e8210300954286040ca5201c0c0520b0301540101d000d01805a4020402003204503c508010b01e440720384940ca110b000700f01d110000b01650450100809410490089002400000c40409150041c100c904601401140c0d50b0b0340c0d02d03200c00200182c41256000160040f40c0c1003904011071048800d0401c00491a03d082980c40360310080c0c0d2a54004d4501c541e0501c04140140b084030705898041d1100d050311030190728000e0103540605c00e04000c01a01501c10f009aa081d803130b50001 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 40376524 1250 40375274 40375319
    0x50c0609060f18031602030c090a0b1801081507140a020601060908010b010e01050f0f03040b1e040827041a040b01031107020f04092f0607050d0c0507 66
    0x4aa00304140440e20710360010f0725551040082c0c41001041c03550003c101c400b000c041c0c0703800180d1700c0990300000e42081e55001c0500d4010148030104000c5a00755400700504035000c440e4000280c1010b0000a4800000d0050b43d189511a490030040c4200c00e181a580c0101d691402003014556a001407046408c25102040543d002c0c0005126158200070414040c0c40d9880082048031040d0340000c05c114403000c8894140300d000203400915007140c0c0100c500001c8841b4480c1d981c1d042900d0103204040302150000701c02d40c03680054404c2d001c4034407685030241382c05c46445414608a000303801075122503106081d2240172141d4081c2d005803200d00510b0056555031650400700092a01440256004079405c9410140341243c44400d00001310240d0304001d4041e60005543c1e401030000c40c0080c011074401500d22042012044007240c641c6d071442c44680c00f01d61042030610848000d01510b400781a20003009504807016003808244111513002080b80680c045a0000e81c1c2d828641c2c800d80200b861a14 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 40377774 1250 40376524 40376533
    0x7030b0907050906100f050c190507050612150a0504090f0303050c160809060f0403050307120c080d02030a1410030c1203020c01140702030d03020706050a0b06030106050901050c0609 80
    0x3890814080c80700241003c1d00c94450710318082d400622aa50502c55020034010b40030203981c3d10030b12400503100c2001c0140200c3c0c403889150152156550014207040328684645940850b0343d050800a0302c140018004602c02030740c80744541122a07541c203180076a041081250000365540c1c3d82d024100c0560b003d03048140c4640d455090013400d03114010a40300035440100070301010038100f14141060743d0b400050720782e1a418100c0000b45144100681d484244030041000b00034080b000c0700408280348070380648500911020015600c49850300409132101e04c06016103201e20702170790000e6034041e46001c1c0c0010180744882c4002101002542ca10461050002040c0100400d440d080b1010f03010420b142011540380340d40c000d41d250800300e0310300c6c10001d210b08045250000c1c8801d88203100d80c010306460b12040d100300f006000303400510023034410340e0030000420042c1a6503c41d07500e002d17602900991860307092500c103480590000c10000d04000c000c02544041c1c407414004d00c0d01070f111000252 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 40379024 1250 40377774 40377781
    0xa0507120201110d05090d09060e04090512070602040806010f180504110405010b04080c010201110a030b150a020d090b070c0302060f0d09080403020405060a1d0403030204080f010c090803040501080c0906090307030b 94
    0x90707d802014142c0c81c0a02070f014405102c00341d00301440c0d4504110488020401008500e00182009006800c1b10721081c1c0c080b03458010891150040e1042c1c500711800c03514941c0e0307901c404d00e001489921580141e8203450007e0041038203143c21240d8094092240b0030344911a2002140448200f40c0c08501c03240800b00302400001814055060f0304034092000740404403c0c132100f1602803050b85117203070038140c0d69003008025855184508215003510740c1d58580354a15800c0194490550f0b150001c0040c51800380400c0f20b5008400f5200a1600403901e282e046080d6424050540e210f0bc404a00114080c00301018400c02801401d00443c420440280c40c3d515510510080d1440584071034031442c6109001e2007800c0c2c00c081701050142265036041c0444e11070f418241e0091040307400c103c0385800740c0203038002c40540540010751150540d90320030356400c1d554510a9124051070013013500003000c0001045104661001506032198001c04c0b46191855101c00a80b4114041d402121041c0f540400c0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 40380274 1250 40379024 40379041
    0x80f0a0b0a060308091c0f03080601090605160b090118060905060106030b0d0609030509061204031701060e090a02120403090f0e0f0c0c100e10110a0507120201110d05 73
    0x1034010741e0042082c4074090440d07a80114501942c1320a40c043c042407040c46030400c0307021103e5a11316805c414804401c46030340c00c000340103008c03c4548a01103503981100007a0284904205c2d00d0a081c0a461140501001d0b6140036500501510080880d900c484900521110b02d5204400c4179102d18800501e82040e854000d060010580c8103a060600e0a181e0300c0e05516102c8814040641c84000010142014030f4240c60a0007046e0559400c00b03004103d0807030b200813201d115030040e130007612042e540180711060307108000b03001d006420014030b0010f403603d03c1e418121003540d0071044010f0054108000c400320001414000c0710b0035400141070300000c106450343d58199202910b070800c0e041540345804503902c0d62400001e040b07a680c041c1c0008545146883c10303c001445030310f245c038051140d00b500486280c0e813101aa803845903d140b801c041407190031590011524809001d440300c82c102081ca8850b4002005170401460941d520382c0d82d00100c01d800707800204100c2c21000320000d89030510540 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 40381524 1250 40380274 40380293
    0x306071701080606150c01020f030103080c0c09100501031512030905090108010c0e221b1103040821070c080d031a18090109171209060c040603050a06080f0a 69
    0x2104160f5080300c41030041a485503c0349050380b000301e400d442d0743d0f1484082010300a200c0c062070a1203643c030100010041140c40c0004020702241e220456410103284c0c410444502d07410741e8000305a200390442000294083e80051a10180100b00b08140a41d1540c0d2284018070030b1008600250007c90148191b2502c80525805030030141c0c002c00012189400141045054038002c620800c13681070a100c0e0480b80c039000a800d5030000000344a080e11503104000841c1c0782002d80c9001ca076200d220726007030010010540c0d049500f5840100b00c0c15032501280c1c68200a1000004500802040460007040307485140c0002007406d000181100c5c2900c800040031140d440d076134407201404802d40c3d1002d42e51481d50701103e030600c6002a5135942c4451462500621198400805016030442e02c2e081315154803014003003580e156200250350341d68a50b011503c560040b40c3c3c45585640c10321052007020306c0703584081d61203181c4e0000081c5050300c0301d000d0b03440c00c8a10710500301c5940c00340300c1c0e060411004a0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 40382774 1250 40381524 40381529
    0x19090807030f060f0e0d0c03030b182d130201090f030b06040c02070f0b120105030f1e0102090a031214180f04060302040c11010b0319060213050306071701 68
    0x280580206070841c2d8860300403946903000500303200d45980b80000700c105540c1c0403811604107101110b1031107103001e2000d0120700d400780d0241c0100f840c08055030740c0b40c14a40740e0605210040e4010001a0b5503102e41c441c0060a0031519031015509035503480c5265030383c5d110300342c001e0003140300c4841842c51070310004050070038607080401c08540f40d907400c01c005955004120341290045a0109040c081503400301e18291555110080b800c1d503580d00040d10018000c003c0076004080c2075001c0da580e8031001815075408100900c0d1000358442180c001c0001204000c003002d1800036000540b41141c460b0010765a1f2516800c240c0e42d8004100d44203540c6074012800c10300e0003000000060401c40d0f600840300882c001c454115014402071112101d55a07a664018009141d00070020071050841820083c648507814000703030490340ca08456985c41d403070009403070000c0c44054000800d52050035036a0703101a4211401520700c11810600100701550f0906c0038070f218070403075135590710714640130f2201c600f00c010180d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 40384024 1250 40382774 40382789
    0x10e090d080703050403021c03060503010b0d0c2102090709081006050f0607060906020a030917040b030c0f12040803090106060918200c070501120506010c020f0102121909 75
    0x1011118500d5400c800d0380e581c0030140307050001303969841e030900303034200200c0f20344c80c824510540100c2910b40344c0560040080da0010342c000c100f091f10040900540c50b00300c802c0502144c01c459420880002810400400d40f0584117040c018941c0d16400b007841301c60f069a803500030500c402c1e01802601d82c10400005c048030301c600c05004c0c03149007601098205410a00300d6000c0c503c001081400e110307058110910389035108004543d2000c00d40c07030060007800c3c0000201c0300d1000122011030445529415981961301d10042185951544416002954040c0c960480c035498140700c180101c0d58002070071407140340103c245079503e2405500003400c54109801207418003481090038480e62200004071189002d5405000900800100024000508148801c0d9000a0014485540b00c1010902404880080c2c03103a0301d03030030a0303800c2400c140c55040720707501d0010300032590001c0546841100704e80c2284040c0190b074001281038444610350f034041071000c510400100300c0b003004550b000c0e81444c02007903035 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 40385274 1250 40384024 40384033
    0x100903030501030201030f09020a0e070314010801060503150411010302030402121914070e0f06060403050714030d0503070507030e01050c0106030303020403020f03030903030f0309150106121104050d020112020d02040806010e09 99
    0x2e40d000400b46c00d00c0b408bc0082e01c0f0000e00005400c00e000c0e902415440301e190007160720301c0da52002d01038003070259401903501900980c03020040b01740c5000303406e500450380154070160582941c00110025000248242e034800c0c03803021000e041e074105002d9080702c40c18401850300d0411450070403c0c41018031003072840e4150301468003080703040082c414883c0c00401941140f0b216803a52400122280903641028025010b95180001c0640d90941001200601941a202d803010000070640361404111400c50100e4001c11500c00000e100b500380b021207010504000d410900c404075204e0850f04960012804264000307421b04c19451301c11070208a5010440c000d5103804c030800042034690107038005403854000e000c0007080c1413205c05e1007100b8884400410840056a58000060485049040b8048103602e4075601d4849030100d03004507020b543c0f000d490300b4a0411190b0044620800105000c80c1c03040d8248003c08400b0b40c03a000a01c02403202c10000c107019410455007000c031003005000307120180d00c03 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 40386524 1250 40385274 40385291
    0x306060509130203060d06051e0a0204050d030c03020a06021c1508030912010207051506010806030703020f060a0e030a12080903090d06090302030c1510171b03100903030501030201030f 81
    0x84019482d0240c0031840c5001d40c90340c440b0800704501303200b09031000300000c0c103080c10400600d00341c2e4155403180d50785c6154200c3c10303110103541c04100e03c00c40c002d4503040b08480c445107010900035800005021320910443d00d806a0301c2c0c84890490f003001c0c8003c030000020754081d01142070346000c2c000d2081d100288040745c1e41e140c5000e1607540c0c402c2c0c0311440c2c003552401d50184461031007941510304d0250030409540103030f11500c01408210a0403610070780442d00040100740f4074140003540f00e0581f64054042c80c02585500300300141b542100f2807082c1004a040140750701ca407411f0003c89401032092458a8200500b0320014ac442e490042c50034613941c1c0f00344241c4030b0703950324002200d4025030003010000741c1309075508040303082d48507400400c1c2e0144610004c0c0600b080d150f07070340da901c10320f202c940304c10105445002c81c07881400c4c0d4104071501c99000103d4030050515002e640e40040000030129580c0c10b4103100e00070240c6403058019000300340d50318010020f5581502030000300030345e0600100034500 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 40387774 1250 40386524 40386529
    0xf03060803040905070903080c07180e0a0303110904140a050f0c04050f0a0504020307080117010c020a0809011812050c010804030c060f15030803090111070312050c09090405030a0306060509 83
    0x781d4814688004e403203c01040c4500e002c0d42c15100a1034104803030698078107484000554580c03242c45040c070b8105080040c04100c12a6101e4251042c9030540500120003030341d01c040700580750ba40c407184002d1904100042c0c10b650750b48208180314040c6d12180c0000d11300350000004580c0300a00070200f0703141c040304200f201b001c0241154140d4108440322141040b20002150b00c03030549801054105100000b4410740c150414030050494040c5030300141c40d81c000f02e5907103080e40d001028002c05648054050344c0040c600502403c000c0700103140500343e0b688258455102044158442c00f1903a621030f070140c0600100748803410400c0400e0070003051505099400410040404c2d5010b003110303645100040c01c182e840d03003010b034013222400c8000c03990381d84909207542250b0080c3c035a96045d40c83c000041814005d608203a4480580548540084407802052000038000080082800d0502040f452116a45041c04240124001c0c0c1c002c2d510746603481c3e000380454116401c4081403007800d1000c2551507 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 40389024 1250 40387774 40387777
    0x20304020306070c0f081804110a050406080606130b03040302010b0109030c05280609080601140d02190305031902010e07180c0c0c080102070201080a02070f0201050f12070305070f03060803 83
    0x103e583d00e05074908a1a5040c52026001c0c044001800510005419078405400e074000c42083c0c442104c00b000014040480c45009118550211010601c03e0000700425030150004642c409030180601d450050f0004070340d05022001e8008d0205068044180424941d0903c90060411004c2c02c00040d080e0464550780b5506026201d400d120303981f84c903001000c5942000c036500e070000c07010084c4c41c0d005031a00030151000d1014004d080c0184940c20000452408010a4000200014044901e201d20075000e1181c0103a1010035010211a25000040054420002032680c0815031a4072844a0704621001b401d4890107911040b03140d01407001031080b020303071482c2500180740c0d010002608074154102030302d81e1100c52031301920b03903907540500142805041d0018000b4500c01d90700c601d05595198103181c109d010382000074008802c0ca80c0080015402140104003c0b03441821140c241500c11940c000014030441e003410000340c0f2401400300d1150011891001440c44d820144540e13030524040c60358a = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 40390274 1250 40389024 40389031
    0x6090e0613050c0d090803010503161212020f03040f05100c0201080606130305060a0507030c08370207110405010b070f0f03090e0103050309030601052e031508070503010c0201020304020306 83
    0x2e65600c08160003031024401c48409031900b0005200c0910b180c1072070b03c0c29420900c1214000d01034440e4001c2500803d0207128151084804143e280c070449445252200010200c103900350320500e42004ca401404001a000428415001c1620389052101b0301c90003c001c0d00d2100107200c0803144510060380c00c80c0c0000c6e0301c000e0554290783c440d10804100440d03185164005499400368800784003455841ea00034612403d8251001d016003104d106040300c1441044031140300310482e0071401c210411443c1c040014100a60075440002e05011290340200d0784002c40407030302131044610445403400c09000d030383c0c01403400144940c104986911010406c007410107000306081c940b00b8100c01050700a10311600981402c0c0840340c695a101d1038155030b01c0e4800e0f56250300c40d00c07600c3c0002845e0320b400c130a4042100d20425403040000c0c0190100c0c00f042e4203040342d2105050701d03041e42c00c9846410041d507100401030341e402001154038044c02d15084038554100b80c0304690040040002585000850740d82 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 40391524 1250 40390274 40390309
    0x306150e130503040b16050705010c0c0605031b0d1d16030b090102070519050111030c07060b0a030501111e040e01060f02010b06031311100219060e0609010606090e06 73
    0x100c0340700c03450080e040d481290803400e00e4480c0030403007101448841105410307081c89802114221500d030b10041d40d0020789100000c7c01c640d440b00082c071540384600003441d000a4812002d03150039074803006460254120102c207040d500c0da95400c5a00040c80411004145c0a0403800303030a000002d240d04624140e12800301030030f0048101c0100303200e80002d5045031020358000091b03031000107280c0206010b0101c40c0d1070a498a608010340c0c8900c0c0f0400701c00701c03070140b0241900240b400c021507039520090050012060752109802100001040d002e0082c1610024401c00c0280d60b0903a201d4641e5528002e5246585c400c2c005200038042060100315050544101c1d05048000e4406014105d0140c50951351583d044040031007030200d41100c44c8081d05040744a0030103400d0703e0009009100000000440c0c050040c2d11040c000303078544000c5404043c0041c018900440d14800d585802032804c241074a402e00181c0d910a400c0000680c081240c20103000726500200e100d0a0880002d090221903008a0702c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 40392774 1250 40391524 40391551
    0xb031302010c050706080f0f0609060103050a090209010e07300905100603050102040302040507110a0b060102030f03040503121003030e100c02030a0f0210032702031f0203010306150e 80
    0x20a580c020950380c0c6400f0707032100844880702d4458000900d40c02d82a900d1807079410000c4042901901400e046501c64100a01800320564614004501401019045104141d51340c5003190168a80d03a590f18060050250780340c1143c1414480100303083e4440507004d00c10006078900284609007255a8102e241c4000c41c04200f0381e0382e80c2130140c2482e80c14001c0070f401c03e01c0c2c08400000c0280c1034010f0422240203c408200903540c0d6030040e502c010000d409401107400443c00c00380000c5681d01020b40004040c8100c03401c0c107007001c000c420542c1c400d5a007500c040d80041018014030140302d0107268040000c442c1064082c0c43e5940c0581402e140117074031032040c030400402e030010301d01ca1180d988406400038200c5014140381d00304504c185601107416030040d080d40c040c0058a81c0240140310030186104c14000c4992814800018107a1980c00d080f40d140c0108519440c02401c0e0414101c90b052640100603a070f03502d03618000c011241040242c103006400c00008204540705003450b141e0044034104000d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 40394024 1250 40392774 40392811
    0xb0604090807120e060a02070504061203121a030307030801050405010f030201050706020319110706050105041b0302220602060f070f0518040608030307020703020a080303040b040201050a05040509160210060b03 92
    0x6452613210005040d8214901203081e034030a9078005100e03003c41e88160b034100b0400f900c8040070050130103828006000b064013207070030781d003d004a54020200400741d60041810380661000090555204080582c00030b001400184070a182c648141030043c140e03d50110211440c40d400a00300c0c0c007031598050031165001c0001500c4e40e03440420585100d00c1003201300504a004000e520b100d8004250686d50649004000318032400c1900c54204212030812042076503521402c002c9000c2e500c0030004840e041000c8144648030560303044400007a00340e6070054070440ca42084009a0080c008000c4410000303c0c60f01007500642003002c5070f00d8040b0070401d09189501080101d4054070042d44000c44070720000040018503036000c5600ca090b2482180c1240c2c6169484208039130340e0109440141124450710085401580144000c0490407841c3c14440e081035070350000a02c50030390842d0030f058a8603011290310300c026030501c0302c174800000c0d00c101005900c0c20301d0540241c43c0001405810707120420b00c001e = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 40395274 1250 40394024 40394027
    0x30207150302030a050f040507090209040b0409060c0212070b06120a0b04050601080f071d0402180403031a040507020a1b0902030a0213060503070203030705090a03120c0b060409080712 81
    0xa000586038088005480d140c001400400a610071034003159007910300307804503401c480100b0000d13006540140c018101c05007044056002035100074040c56100340c0d5400300c04410f4940340a10f448241c01000000b9984e040088064244060514040d40c271000800150000980460b203084d044001030303840541c04c0000c08015031a10300d95010280900030b40c3d004000410500164440c140d6014000340c82407851071501b01075a0306202d01030041c0c100e603c0c08002d880e04071260780540e44079000408074032130300901440224521030241c40641c00603444910381060705940008000410300161400c001d40c1c640500300945070080124000c0500c1c000c000c040342e021514040040280c8842d0350700f10f40d00c0c02c1030b00c40d000c02944000c000c0c3d00c24040c020000103416000b4401d903449101c090700a986541d03207400e0120341c550300640d42a0b6001c02c441d98080041241241d9156140c0d00baa195440c0344442420524032040c0010b100521450500114100007280c5400b503400b480d40c40b481000710781c1c00c0c8500 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 40396524 1250 40395274 40395283
    0xb0c070c05092401050901050d050a150603060311150a030506190608060f0907090e0c12130309050303090d060504021807021608010b0f0d050109021309230c09040302 73
    0x101d82c410141018000000c1c0b1422010000c94512016440140c5034000152828014142d220340460b1040c400c041080f2841c3d00b103680d00c07003100d00e00020010040400740310621455000700c000240d84d00e50600c10003c0c444504514610112402c484170011600d85e441c982c401c0b100d042040545400c041131080d00c0b0246542050b41c811452000c00c00d4a0300c00c000d1078004116420f601c07a514246580400d405e1a9481c5800f60a85548203100182044115010540c000c1c0024555081c200041d42400620001c80e60081e8a0b0a040055207400c4d410014180b000e02c0e040a8420b40042024060a540d8400000710f02580f2502c080b605030765030300004010f40e154183d20b001480d87c10003007002c02903010550002d041803254075004a0b0391a520741340d00300d916880c61160800d80722140c403000361070641040500c1078801c000208401c3c21507400b044003400820300d10a9401e8441c5500b50800800a080a00f007226048880c2c2c0d140c15000021a070f25040d60380301d14022103a907404541418030900 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 40397774 1250 40396524 40396529
    0x21e0a090f0209091609030b1005030106060807020c0a060509130617030a08090a0b0705031f0b090a091503030302070503040b0309030304030305151003050705270307050307030b0c070c 81
    0x9008000c11141001c02101a6001c4045944034108240001d400b12080b031908001c00440340e91180b0360702d03086a8501d000708034050542c4080e807254038000030b00c40d0350034041e84020700110303501c111803401d10903800392a100c02c8105691050100f040d0a00016906c2030580b1010842252090701107004d02181900510307444c0c200c05900c00b0310400a100e5400c0000041824501a42da028035550b10447d4154581080d290700030a02d081d04804a40c52922410146403c4400000e05816038100e071062281c208001c1e0b40040200c0102003400700f11846d0002d915070090041c4041808542d00c0c640036a84040000c2c0002028940d02090500a01c4020019603015040004030160b0317a060207500990740760400c030340840c00242480e0000e1100340f280c40c281085c50401609800f981075649005a014020060100d001c00001384081c0c20480c4444140554800c448004072482030041000d00d418501960001e500a911078401000000c1c29010303010390104a129005403200c10324500403c00e9002036 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 40399024 1250 40397774 40397789
    0x1d100c030e0109051f080c120c070809091e0907030515091e0106092304060b031009030c120306050d0f020105070c0617061e0409051e03130b07021e0a 66
    0x2041c4200f11030b8541c081d041106850390003080e511507a0758601442140000c40811813246e0109d02c01461600252000030710480d50305080103c0300c0003044845000b280d03144036403404111990302d4084911030190f00501440041c00b00f0742d05548070107a42d4000c040e0000400c0070a02e001543e030f42028012681310b50190100740801d00c1481000780c0c083c0c820f60250115852130541c0c459040101404040342c40f250b00c1c140c400140d6030740d84645009020703040d80c854150189011944049070b45100341c41e0300602c01e84980380c8081550520040035101080e0487c28103117000420302a0ba0341d03031610000180d92200900b075141d03206200403101c0c1d014414004111565101d00840c2d07564101ca1010b10103003400c3c1c030745646546c07004104008c0b400c0a5982c403e441c004030400e11007605154000c0c548850162013103c407001c0c041c184400e00c0380c903000602010b070b0b0400305480d00c814075035420450044c100c48050310300b010380daa00003480081c00700580307102e605001b0f01d17095115240c40113407400400302d4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 40400274 1250 40399024 40399039
    0x2030709060206091b010305040f02030102030106020a0303050f01050d0b07031e05010303030c020c09010902090406081009020907031e0507031b0e030705030a0b01030809010507080a1d100c030e010905 88
    0x68500609041454020200580034290004861100000d41c072102040400154101244003400540c01800080c1082d641440e5113074030340c1e000d03032000d00086000f000c0b19402000d5903503450a000702150400741240480740718850042080c3d5684400d90050503810200d01d00d059241e2650a500500c0c8240155035503c089881b42004166140e0019040f00e01946042c80540d4108004903202c0110814141d400303410784005001280e0280d000d031909550180c4005141c503105c00c0d0351840d1401d001d62601c0f5803906d0ba02041e00714184107440b65003000d01343c1000d121090391200301d0300c54907002c9070300f0021103a52100000c400c1c41c40f903044031088018883c192047e541e1141d400402d1240103800490080c4601c0c08006150301700040d041d4800c40d008a400d0316140d00319540e0f40030aa020054030390400905000140208034940000c01d07151045480b003500d00b40908809d5154510416280352144c81d81d20b00a850b2650020040342c2c0c440d40c589071202e103a916420051303c900c4600d412080e0000d05 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 40401524 1250 40400274 40400281
    0x4080d110a0b070f1709060c0a0e1804110909030f03040c0302040e0a0203010e0f060c210c040504050c040302130c020f370206040b0f04031e0b0601020c060901110c040203 75
    0x10048580403440e07526584860501145c0c101d07440005005032482541540460700007030072070340741c84054044080c00e480c000620460840000e42c8460001c89141162001c00090200704103038505200c0404000f6606403901d45410071400d03440c0d01400381b000000040010000b001c1045c081c944802440d4020410041c0c94a0702e03800e41d40c0c440d0907940480c00b0350303c0c01c00c842c1241c0c4000a4041c00c0d056001008002d0b40e956409462203a0300022650200842059144049183d10810480c40742c3c01403001e8a450300c3c6802d0030481605d4024001d5085081c041000b400562260103907500302c0d221780e03400480c0e02d91080d00c0c2285003126035418010240280442c0052101c213082c103034112040031147c0520101c04a0b100200f0061110030000d50141042104200341a42030014114080007001040d0400781c1c0c0c4c0c1c41345000c42c03100e0800110f0150752490340318100200c0e1200c00350048000c1c802001c07054800c00200e180c074400d0102260500c40c03001c2031248254010440b00d044000c025100303544909 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 40402774 1250 40401524 40401527
    0x5030c090d0503180307150c0507081504050c1e060313020909030c0c0405132604031202100c05030a02090a08010f020c0d0c020109090b0301150f05040605010504080d110a0b07 77
    0x1000684c0b0301900101d01e0b0400c40c0240350014002054030b03e17104a01e001405105402e072844110041c0480b40c50050200026100d9418440c0507890100396440b11407a2406140c0141001000c00a4912481d1081c03903496101e91004c10b059090801510f4459490712415003280c00c1b44e801c00402540200c0880c1003011081022000e00840e490712022a4841e80ca900d04102c203075601128001144030b005d905034008502000502c080c400040050420b8180c00c010100200d540310390410b0f10300c840c83c80007000210f541040840d00b0008030010401c024060318100821510000e0049681150003084000481e80c40c081060700408500e002000008045001c0b04065040701552507403502852000d0034005000d03800c004038155050303650411041c181540d07000102020b03500e450f0950750f40e00300c5c00d51220b00c0c42d800c1000340c5900f10540001e240340004020503038000b608014100070040c03004201003100020002805003c87c00c20a0901407125061460a400c041c8058035414000040c0100e15 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 40404024 1250 40402774 40402777
    0x913021b0d0909060b0702010f1707021f0209030c040b01020309060d090605010503060c070f060603021008040c1a04030b0c07150209030d0c051b01090906060e040e0f0d05030c090d0503 81
    0x3070345103444103082d260350349400c401210800e10480c4030714002003041400562190640810114040c01c24500062280381003980100d82280c40b07101503840300064501030700400b516504054110345056182c035078481c001c80d45a03c034546400780601c1d101c1c45060060b82c001c0c029101254801f60403a40c46440c00030001c406482140d07000c0c0d03510f034a000e00100f200d05000c2035503441a1079489480b40b4046195440300386044407000f05841565036924044016034855001c00001031517580c40b40074505103400d04100d659441d602042045481c44941c800a240203419503080300d0700601c00381c82c1030307541d40311440f618410158020400f103804403600c20340145c00c2e07002d401c1802040e000c0f2001c0e02c0c175160003a25040d1032031402400e03d41c0310a08107402000301c521078201600040c07400c0c244080d55071200c401520965080725000c502100d40091043c10144101004284540002c2050400c510843c544407500c1c503501c0c004201c0000b00081c0d12800e08e208842c95900003402061420005003041503da = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 40405274 1250 40404024 40404043
    0xf01140408012f0306010f08040c0b04060e0306070e030a03080a0b0a1205060601050909010b2d070302010e0a03080c0a0201020903120c0c0a030803150f09010f030c12080913021b 78
    0x1000f410b03489204801c140a0907640b1540040c1c4800d5200f000030300d0305039001000140111482c1c0b426440c0450f40d2140140588018001500c1d9410340b101102d082500b0010001e01c0d20040008a0442d4452030780c0005000d04903d801d401c0c54100707501e071441f144010b003404121407508000345640000d180200d91001d0401240203c0680f030300707034850074011a0144521105550b11811110041c840010000024405040c030b0a00002e441d201070003214042901070030b07150b1290080030403c002819028000d426039401040301a04140c51155800350030054040c0141007005008184601018002d5044034440a401012104501411040800c0d245c0c00341d61804058051070090520f50f041001d8040d0030780303900062403070940c0e641746000c60315542e0700d40c51190321640000408405494800e0315602901032441e615203010f05504015481085a07440421145c1004d00c5801c007207134410080d603406203000c132129950b4000c241c0b14400640034000d0000c004001c11109080314845c0021074041 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 40406524 1250 40405274 40405331
    0x60103030e01020f0303010f09021b011a041404350708030117012c031c0b0f010807021908070602120114060903030d1508071d13020f0114040801 64
    0x1028080141356100c3c002803003010000c1e4140b1000380b06118181c1c0180111301d040000c8a800d80c0c05003180d590a40366001d803440b00c00702d0002c140c0301e42070510713001d100114001030511070118105540c50703030110380c0d488880170b40019403642e60b0300340702a480c120103001c124400f50464891015003880c4079550300c04c0c450303055019104c03196254107800600846c400300070300c2d01c0d038041c404815800360703007807003c42c62002c040070300040204d004920280310145131280c18403400000c004205906024440d01d5200465050004031010000384c0c940c00511070744100550295002c508185140004140c054014000d010030b00101d024040300411a442074100c400306180c0340c151603503e80600c20382e441129070343e0380c140d082004044000a040d400128200c13020102034030b4219640c100d120f08003005034111418004a003075400070100c522034a801d402901e464400300d0302c003c2c1940001e9512a0340700c140da041c01100107250014845c0038060314001c03d03410000f88040800c8500d052031000d0410088070307 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 40407774 1250 40406524 40406533
    0x90603011404060911070213020d06091d0a020619031407020309040b0a08070605090a09020f07050607090f030308061503150315041e050c03070e04031e050906070212060103030e0102 80
    0x60351308400c0c0140c0341d2a0045031324203458804036800307000d14511128220022150208402c03800d0950900c0398a00034440d4003070020300b000350301005010320100800408012b900858140d00035039502c4040707030000c14540003000c5400c07800d000103402404800c0c4405403100603103800c001c40e050700800248410101201e080082c908100b0030000f03894181d0280c126648c1c040d06040c4031003805a13004145500000740310003510359940158005a030301c0f040c901d01e10a08081002c004104c41000099004a40c1d41001050b85051030301054089480380320140c00c11420074082800c0791250b003814003004e00d100e50015034a00c0c01e0218200e902e015070340054080e110b600b0021041e00c104d8001c890007564441400b111101204402c40c0b2100d10a0005660034060016000c48565041043c0c46c02441440c130f0051591800e42000b402c207403082440c4034007a0303807035200341b0151580c44401c0b01c440c82022940d8a40300d5003903001007000701c10340500a940394071507180040241500a01001420f42c004d90865 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 40409024 1250 40407774 40407779
    0x305060721060602060a0905160308070b18101821090608040807030c030909050403020c010908030c120310050d06020c010c02161a07050102120106090b070203030f0c010209060301140406 82
    0x2804032500b40c0303d0000107812030004140d00d0007140c0c000d0015607000340226840c596580c2090b00441800347d104550070302c0700299007800c00170400001d176030107021892400c48403c20007070255101c03030000700c00180ca0b954a10494a07000d13028105036000540140c00005010144606180e05101d07000010000c156002000100940b090074528811030380301c0d5160341803c1950303500b581d4284841100301e05102c1c0c000c5021070700284130b1140e035110314029401044025843d80016001b0303005a040620903410400c18500c4611000481c0c001c104103060123641e03241e541c0003401070800b13140d4108641c4007441c0d00556050103080d4010300500c018002c003c000c4035501100c144d07038076001116460040d0b40502e8003008000304400031420386050700d203202840c0400658600d8220381c00128210941000c440051014580c01403011003e4100400c03442d25103103c1e40c001a40d01d00034030103040403841c0d0000e002e1415020070340598400c42801f1b090389449513110070103981226040101da43c0a1441d00400 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 40410274 1250 40409024 40409087
    0x703030b1c020f09060301020c0610030209070e0d140c13020d0b09061e030a0c060309050601050301231305010e031b150703020c010b0a0f030507080f030910030603050607 75
    0x240301e20794010010300901075404140003000200030700c0c0300e605550030300034119400070510002d0b100daa5442c7c011034901d81148100038001c00080e205d00d00f009040842844070b51110356004d003e03103030006041c070302039030381c00201030b10b07101102d5842500884c103890550000300480e000303030150710085c5006010041d201d40502c5800761040302c680e548480189180510f01c141d01c4d9a0003e1403101400341c0f02808450748682c1d40c00b41441d440100013a0343c0b45d140030b0601000780081ca01401c030490090104801b0000003524444511400079021005000440c0340c00a1a5292003091a40310000340000314034030002544a07000442e1b1010308240d10703500b1035204080800c40c00703a80341843d0503110050304e40765011802500f00c1002115a59a202040740e0141c0c0c0d0346001100030070116541780300e141d00350f1070003c6c24000740ba40650010f52191040202c580b00100075104606800d65030540342c01e00841048010b45100c0d4800b91a6000d80c205000c4002d83c00002805807082c3c0e0140b5401c00c044141c4e0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 40411524 1250 40410274 40410319
    0x6030607020d140d020301030b0103030305070c03020606010f0c140304080d0908070e061314011d09070302060f04030803011211030c01021b0d0c0e06041407020d081b0703030b 77
    0x302480141c001d076000004840c011500780c4001010100d00d5428035480011801c12a0720070781040d40c11480c1480100304044c0d06011749580000c00b46401111a401c0d030703401a5130b0302c2006d45941d047c4005034141050852040003007203034554101002074008803a800c1220340343c0d03000380245050b0740540e29031200681d000d0b0041034101d500e40001894171074500304040c80c170703084050080c6600407100283e0303903000c034440c0c0a06500c104100c09041d016514000700f03000d948050348850705040b1201400c100100344c02080b10400c032a0151400781e030f2958101c1512003244075940004111010210020520407660441415114814100d500f60711000c5001c040d40d9041c50031862740141d01c20340a10049410101c00d20a404001400c0781ca0326a110740d44c0d110080403550000c4041c0840301c41000f0030351070240201007074401d038090015114102420000d4589900c01034090034000c02c80085092401d200092982410f000150b1544a10b5585030040c003914024104034030600e595203042c19010180e48 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 40412774 1250 40411524 40411531
    0x21207180803180103020d2405010905060301090c0c080301030614240118050303040305010b090a0b010516021906050306090a15090906140414101109010c060b060f07050105060306 79
    0x400540c20311019840801c3c020005914042c109502402001244a403c1c0030b954243d440c40350945a034407065004001c1c403103803113600140c1040f0041c401004180c661a0440741564400b01c80847c0070f1040d500141c9854010450003004c00d00000000424084070b540007403009190b00c1090f160039203c840311002c04c0201010448265800b0b070748070042560045044c0d20b22451401081d0520b15a6400081c0c01d6030031070340c400e8030980d44400c507050701c5180140780306038403005200302080281040c600007011030140020110a0701080030741030007076544018811054503c3c00401c2d0000c583c07500c00040080d0001d68045000700050340210b030641207513000d104c003084c120042054a42c1e00e4801050003901e0182c00580d00165643d10704076100c0c0c48a000603100e0380c05541c1041250201001e03c500d01100f00480d130080d203142c5502c480f00b504003c0700f19210400c6c24a08000c20704540d003454401040410000e0b580010005071040808100f03070081d02c81540240d0081119030f03603600c1410385500d02103 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 40414024 1250 40412774 40412789
    0x61823011a0f01020c03011a0307150e0d1713030605060109030209070f0507050d05032a030a0b0301020c070816051905061b010f020415170c09031002120718 69
    0x80700d42803442d050041c0500e6010105104540d0b0404155001c40d08641294000300c50922942da902c4005007001c103d01c1000380f40780c0d0750083c2c2890341100020040b401c0740c0c421512891140c2020002e1014540d28400442c0c0010700319a66040c802d44584440346540c03204403503450510703000070810343c001d810303103002c4a401074015015990396001c00c1b5003040d000c4006c4018040d05003c02d0020a1040215034410003080d111a9520300b03010b90701c00c10800501400103c48005501030b100c081c072141d401d41e41c001c0200e4901140540c0c03601700003070190080c0051001c0500c00c0303280c00600315000203144d8041003c0500411034090301c03003040c09003000d00440c0548440601d017008111a05151340100410302048111108405500c032026003034440c815001c105064000c6018060b00080c41001c204414a60031f0030180310480220140210710001d1001c10004000f040b491056282449080b2225507200400c541d41da0000840e45500602524442d0000303401043c1908850040743c0e0b00000d9a400 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 40415274 1250 40414024 40414061
    0x30203041110030f0203010e06190320120604050a03030e030f03061027030303140f06010c080d09030504030606051c0b040c12080c0c09010b0406030906182301 70
    0x8020510501202001210042680e01c00b031613500e01c11a48055400703002000500b00050809404000a070b2111700008070700416124400c1000616621400c6803c0c0741c3e00324403001010319030002400c48028000c0102c014001c03581000708000c030200340318140500c81d84041181001c10030142d5038902400000101b045000c00c007141c0c061034881c0400e811510107141503142d00e20380074103d01440c042c18514207494074005d00c042c000c140d01400380000002d1410908401c514103854207401d0b01001034601070600004041180901c50910101c030f1280071a0365044c018501e840c90300810f0366100b40300954034107142090200d00c03071401250700d480404a040700010307034022544594541ca079010700101c91110840c0e0000850100c42260280c2c41805910800d0710f030700c82082c40d5130500c1c06030084507100701c405100520440c2094803e40b02138500c5c500d4005084034451a00300010100c1020104806403001d4a070010090006000171000800041815141d00f00d00307401800d881e107148039001c4140c074 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 40416524 1250 40415274 40415303
    0x105040303030b040f1104080f0c01090509062407030909050601020d080a0e0a03030219140a030c020708070306061a030c0f09030a120e0a0f0b030f1b12010f050103020304 75
    0x2090f081003400c920004e00c0018082008213a80007101c9806002d9962001c000c14104003169007402142014050600508408054100002c003922528041d20340b061a0325408907880d0749600454250543c49060b51040d91481d145d9404595085000c00310001003401c08040341e900c3c0310780503442c003856043e0000d01c50b2200e003082c07d0700e1651b0010041c01c0c1c255a290540c0b04545801c05c41840554000d460050b50342c40e00072130080c0905410b100d0101801041c42d1048548500001124040961740c40e00065424003014102d0420000c0d6200c07140b035100344d04022041c040c41e503021404039544c91480c1084008602321107a8940001c603202202c2880502a1400c100281c038024018020000e0507605c3e4030410355200f11108404a004030005401e980d601d903814102030080a000d0002004500c039520301d003071070381c010b50700c0020180042421604081000c172038006480c034588070040d040d241d4490702034044040440c042489441e0003501e20b14030018155000744216402242c005510082400c03 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 40417774 1250 40416524 40416527
    0xc01090f0e1807030b0703050606070c090c021603120201060f1203030f0219090806061804060c1e02030d06120206120606090402070503071101050c0d0305090a061a15090105040303 79
    0x24010901840354070300002568a01800f446014042e620850020080d41041c540003400c964000b010315010b044100700ba1004626100b080104444080340c0102c2e060307110b181c04a0810300c40880180000290703c1d00441045000c800840d050300780b5500820030ba99a420708003803640014400e1049885203581c80001081c400e820085102411080c098540b000d4101402d6a440d46c00c64036500091207082c2c02c0c0042c0000744034031354018408490340321519520034140c1c1000308002d04002d00907035842c004030700550700032140011480106001b03003036400c003d0b95001c1d40300e6200e640110400e600c0d042001c1b81c8444600d82c0d180f0b880f42c000d4241e130300300390101e20342c1103114030098181a40840e05020708000c0f80c2d524002030962912030005940c0701d40c00d5142030348140c1c0f0740c02c44c06818410b0500265140300e00008406c03041030340b9460003203010b40f074003045582004407040014000c1810192101d011700d610903401d409108041d01c1707041842030413607020b0306a8000d24010342d0014604001c01c00109 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 40419024 1250 40417774 40417799
    0x3010b011403071403010608090c040501050315040501060902430b0403030e0102131409011202060a03061a03040318030203030a030c0908030c0a0b0f060f060d0902030703050c030c01090f 82
    0xf03054201200c00215280b9800c040303400980c03180c07000503440c1c405c0019a200a101c0d041072030505540602ca10750409000a4469103c00c0c0c40283d8007050100180501c802500300c0301c000c02580404541c0c7d401c8900e41c0b25018401d47c100048980c4a41e0800410404031022001c0c0c0030b404141015084c0d00d00380d4884121a84c044c20a604054032498003e40d0b0349400e20062a61200150004001e9490802d440b03140c000c09440452003031540200401c1041035441d050040554105c0d01180d41c1c5000d007030154000d200c1074003c000e103040f003001100288410f4030300031400346019850f040d100019926400040254a000080d0103400504c09944040d0083c1c01180c0074080728205640c4591300c0ba4806e07444c0d40c02c0b00002c04055031000380c040d01400054a21650400134075400e00b2101e151460214201107071080b81c65001e910000f41c2587c50380c12036402030207240c0e070042c20707030311219507074240b00c0da9900c030400c0c506200380282800c90030198080c842010407103141c15880d0804610301600703011345 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 40420274 1250 40419024 40419031
    0x20a03050f0d0525050c06070309081603081909051e010603150203070806090c0910031d010f05160e04180f050303070201050a06030305091e040e100b03010b011403 72
    0x740441031050031201d21190049920800811007512007240d059181e4030f090610102c0164103200d02003108050b410004500e180d8441d0141c20086071005117031402c040d0a11035215522204420303a00c1170820941d0102d44030b400303100c0c080e2940c3e00403200d120700ea00850300c4407a4010007940c04021084807029101c44003200c0702c03280d2400000c2065481c0c464105090803500d260000c6540001004080783e00480d100340c010605854001191401545441140c40b4200d00f4600c180c1c0d80750449903440b81b20b80c001ca011214080d180d90103502130004518007031b0a01d00c00c0030111a00f840e0000308101d804503040741084071260780e00d00c6a4040d910500001305203032210010034425010b504d401180345050b2454205100702c0040d5668604144000d085071320103000003504130b08100007003010030303071040607a180d03031200715070310100021041d504050051400c44400c1d086030500030041c501000100d1103030840c91300102d0034002d95901c40d00b018201c8121048503401f180e0b0004420700c41a00e0305e00038551 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 40421524 1250 40420274 40420297
    0x31009050705030a0609050f0106080706050c030405060a020c090c0a0c0602070f02090c0a020106061806080a0608070b0c120705060c0a030b03010504230a0b01120501020d090b0f010b030106020a0305 87
    0x1001e4450011a0500c640713802c0584002d0788444049081050400480c1c00c4003142c84002c1060900344032480e601c90015124640c20441d01140c3c0181c02c900600c215002800d0090049649401c04a0040c7d140c20541401c181f140f5445000240518140c0c402c0b240213603030130344e2029440b140590303d58009400c901c00036111a0130401801005845111000340900c11001c030b02520f5070340c2110002d080d5807540c0c000300104000d002410604011000d0100251009410441e2040d034407003007440700400c080d0340704c0c200501c541c000008070070150100038005210503c003682c001d2410492001e03018130900030f0003410790344440001504156284040c0c9910324080c135000c00d0f0510b2003c0068291a826582650601d55088407000184603540f0a01c250404020241c09030a01a4980d0300920505201c1c1d42c11050140032450104502941202d00c40c0d01e0700e020400a0b21000e0502e8200c0300c000f160421514aa02d0001142c0007121005032070494000e94001c020741c2d00281d40032140742c0c000110080707 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 40422774 1250 40421524 40421533
    0x1807080304060302030f070c020616030c0203100c0905010518012111030a050a0b03061f0b030f1005030708030415050405040e010c140403020a030b101805070201140603100905 77
    0x94205010320040000301081e035809a20707800e1460a00202c4040a0b140e9028800500e29120058407800240c47c040109040c0c1180d0303a085030304090700c2405141000960600500c04000041d01959003c19503514081d42c40105654554006403200d03c00c28400055511110381c2000440d8441c502d040342d0440f9105600c0a0400c90f0051881910310a080c2d890000c0700100400c042c03442140b00300c1e94000382c421000e10580a1400200e0344515004d0941500b02d10780c9500b20381f000b121622100002c10810601e29540d1400030f6504d0003903601a02d2080c182504d0308000651864001441c500303444100010f50b03d480e150007886069200c0620440c804d00400b80300018465a03940b051440c41e0b54660004034003603004910080c40840f0052a07454854000e210a00c0580c44e0000f41e002503d0703002410051946640c2c103407240b0710303c195000541e50036003086011612105600003034010101500240329900e040d0001c1c8030b4128044a500c1c0c0c26078450741c002c2e015080300d50071610700d040c014410745 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 40424024 1250 40422774 40422779
    0x30309090f15080d03050a020f0d0e190602030103060b0607080a030b030c040f09020307061d01030209041104060c05060a110901050304020109050411070c05040203010303051c06080106030c0501020609151807 91
    0x80c0420740c0c2c640c440701e081e07000350a40e00101da40602645600001c000001c41ca80500302601401341d00a6691034050b90b580c501e18080b2101c01045982010a00620340f140300400a240403400780d442404101d50b00341c1400300d140400d0503c0300a581c41d60750300000007030404a403588102d0040000c01c00441e0f040c41103803602813540e102e130302c501d03844080311707040200b01c6280030300500d4a002d115900c803c003009100400403406540310760038081c50800910b009070f940e582c9100018040d0010031500d5820f0300700090001603c075040004030300c54902c91420740b041035660b16204411101d4000e0a80c1b151541000120002d600c41ca004540c0244141402d044058481000c60100c0305c0c8500b05181c8903038000345260034000801c003800010310040320254515811560010b08038080c40c40c41001e0340300070f1200c2a412040760307009003000d80000c0008001c0300b40c3d00d041503480001c051180e1030150003080c3c0807802802000c101c018051030007800e500017684035900031a6144442c140d0404060044801c007 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 40425274 1250 40424024 40424051
    0xc190309120303020307110a051902012d0207060219170c0609060106022e09020a120308060909010b0f060c01020d050a06030c060207060206010501030216050d030c0e0406030309090f 80
    0xd041c0e46900940c1c0c0141c81c1d00d401c0001824103241650b60140c20350008549030002000007039a8421407504102c1c1162000080c40140c81c250b030035191003691079405104803014174200b821300b4500130b8030503800c4800580e42c81d10242e840d481c0e82e2a07900ea108003102001c1c00824001e04128803d00e50552505140503152002c25092042c1a03c44403010780240c1e00401201c7c0d41001403405164100411710000d00284420710462104010ba110010741c840c26584107641c0c40b080c145c0018036602e00146021002450014800602119a91700c960099008030303410900502c40d06094040c050f1200c0074058649040000b150040d4010f4030030b942d000c2150609495150240c240030b0010940c0c0411200d0440c80c1203d11a9000c0d0451005c56000403020040241d00041460440301c1c01e00380140e4070001f900240080c103001210240c424454181d00f90701c070b1641584004400f110030b81e03840380c04554003405c200a840ea24030003e00000c49503a0240180c007a59401f0340c04011824900003500b4009811 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 40426524 1250 40425274 40425299
    0x5102a08070309090e0d0801031b051c02031b030c04050c1b06040c05010503091e03040b0403150501090b0f04020f0c070b030403030c03050c0a0c02012f010605060c190309 75
    0x8110b0010303a003050100046185401a04014400d01024002014003202c00038003680301484085c1241c005843c8240e43c141001d45060060000941140780aa1700c4441803612901d40c010102d000780b04200c2c01c10001c407400c0300000b108040c010040e044d003d203146c1c10040903090160405407003650420002e01c0c0601001030035800419928044d00e1245041d0804080e8240d01c4c2d484941881002c200700600301c00042007202101c000c0c0c40c0244d21040301110502c0ca5402150011101c105e030000b0080280148603940c0c0b00342000140b400d100790307a21100520281c40d805c580f4244c000c42c40d10710781152460140c000d80110320b407803942241001c1c0c1070000140f400c01298481501500b0000600c024036a040c040c0e048a691141014011410480e03003a0b0300d984104030401d0100001c140c0c03000c0440e81f04140c0400e40c9145c0c400e900242e20072200d503205281c1e961001104281d840c00c0c1e40020141001401d035000070380448040c042c1580e0603036440f010b07420511404c404002d14104041404501c1e02c2 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 40427774 1250 40426524 40426537
    0x270b0a020111040f0303080603030711090907081006080607030c080c0906250b070809070302060313060e1c2303100e010603050f061206190e03040305031305102a08 72
    0x70b9201c844c0b5107142005024400701400b443c0c0290020007200b00070a800d480900c4c0e00c00d10a41c0c0365100c40e40d070401d410381080d9042d004800c140c003a110f41604100b00300c1e0440416900e0460580761130303407140c003030030303411036503810005030110312408000380900d40340703802400121802800390381c5020084a07824541800f0400d03000c51100b242a046001c2c00808000305600211900704041d460401800c0300741c3d92103a038407000307200f1600040060074601101c08014403013a40240140b20792243c042045817100901c0d0302151007000e4110103203105a1050520303c40d64031075001102141c10440081d070806510013002c00c2c420094200700056001d142840d031500030f20195400081600303042181d0b05d4030b080046c040611500b1081c0e0b6256400101003480c0c2d03080311900d00e0801d1015000c4003080c000e04143c460b01001400045400018460040001c1c4030182c1403c01440e0519220002c10000c03000c240b121500144c0412080b000e0b6a1130b000f1a00d00703038a01c208040400949031341d02c100440c1d00c0b80 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 40429024 1250 40427774 40427789
    0x120b03150403021204080a0210120203040c080c0102031206040504030c02091608010902032403010b1809071d0408070501060b030a0e0d020606030a06270c06270b0a02011104 76
    0x40d003040700381070f81409280e0384100c1c8650703494601840d10144035500c1c0c1d41510b000c7d02c0348100f141150b48041c0590900c8180744900c08095440c0d11301820140701c01c42107403080055901811440b5070303044d8030110480d920300c00c141c8140713081500c3d003a00b40710050800070012810f0012580c80d41e00960b860100329440b0301d420320a00140e152b02d464000309a003c040c0c0c805410140140180703e141c9511005207101d152022103906103c089540000f4090b040e0000c50580103038007500000e43c0d03807022000c010322503211501101d0620350b0305c030054240c1082c5030348103241c0c0902800104000540c05030040c0140c5014100100d034103610b8000300e01d070552040d02e03030890441ea12100543c408409000d001c1c40840a40060308a5161160200c0c0e01c4801e880402400659681d03039241d0b141070480d05400c850503100ca8146040720300e0b8600542208014042c91000c00d21034442c0b1394500c1149002200958003c082c41c070788507842c0284020701901b1a181d0b0b10155500c13403100c9020f81d40017001510081c01d20 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 40430274 1250 40429024 40429063
    0xe180603071a0d0605010e060403030c15110d050c0c0601050d0f06060b0306040c080702060105060f0708030703020307020f0a020a0b0f0c01091104060506070809060714031606060e040c0303120b03 86
    0xc240f80c08100c6405034030240c1401060003600b401c5507545801d8400b00d940500703040b40303240068034001035a0b40201c090700e16114030b460500b841c10714100d0b005d4115121410010007680e1201110036489014000d400c4040c0e51000c401404a8101802084801c5e8403032030741044400a1a134035001a6070554001140284000c02048040d10705401100c980c4121420807400c01e040202c40251604814012240100f00024084052503003040443d400315821100d01038690600da40020003951090b11010010300c101004c0b13101100001c20411903040d801020680424905000b2101c5134000d2800380c0c0c071684080c8480c00a10310280a10046a48036016052030507407040cac1003004440d29a0403190040b2000c0c006c650000b600e060440c1c41103403040386e00380e403a002107140211408980c00c81001d664000400d81d03070010341030380501e04082032051409000f410b0b01ca04200c90745450803200540710088000040010034003c2e905001d0030050b603400454800107440c0460310f45940c4140b079900031400b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 40431524 1250 40430274 40430287
    0x12091e1a070e0901050d030e01030c0c08040b0403031103030708152803020a0b04120204181505040b150102030901030b030106050a030302060f06060c0d0305090307060501090510060e180603071a 85
    0x40c880a03da02411080b40c41401006842e1070003064108000c040c541455541e45000034154011074041d0400381d03000f0b10700c590329a01d60f0358240d9990000c0c44218080b0b841c50000090780040030045c1e03440342e0300a1750380f4600c0d550398000c00080b03140d011a41e507802400108050240c80030b41d120914106003000d001b00c00c514070b148140002c04450758032440c0c401e1400d1000707100c4802150002030003140c044a01040780c0088003400d1806d280d41c84030044c1402c41209852650a4150b04414400c0d401204041280c0c3c0d00c0302100c02c2c0d502d24041d06203005800401031448258002d0340151020348020740000392094541c0007007a5000303140d820030381c0581d019404024840d003172015036652081e01680d4103070074880209001580c03407640c2801641490340361000203041501c00c0080e141c0c201e820a00901c2156136071400751000348000c0e5540c0f80365003103503c004211b042c001d0026403400040030382906006400010705d140034210260180d5410b000d003100004034815115002551141c560040c96500c10 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 40432774 1250 40431524 40431529
    0x4020d06111c02042304020c070e090f060708062e0c14070503210d06060e090f07051603020a121707020a020603070807050702030d050a12091e1a070e 66
    0x1900d00550b007a4103004200034030902181100080c040306140c02199440318440000178068020000c0380700c00f80c450283e000a01051b10304046024550480a9495681c5014001c40e12150226143c1c0c01103000c400100301c070341c24400c0c000b01100050140075801e4448505c0440040780600080710001a006210041407040301105009280d06150042150780c0c42d14003c692144079214046030701c501d103490044c00806480b0110382c0c111500100401c0030740e488103001b416416540800e2805016014002854000700d0403056000d01d815031540d60510345100c0140c110000d03032040440440c0228210180021004a0f01800300701064451080c1e51349101d21110340c0c071000602080031544031048017009615190b041320b402c0006882d00d107104d0b82d12020240d074544107405009415100d8140d1104541c0d9100d400360907451b01550b140c0d10340885e40d020f02420395242000260100104011140705c0045942c00c50b059280725103e01c007403200c1c54076030b0105102012900303100801d07080e009603205072 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 40434024 1250 40432774 40432807
    0x12090905090601030b06030a050d1e0f080a0218040501031505090303070f0c02010c050607021501050406080318190f080d1103030f0c0d0e0c03010e010209031504020d0611 75
    0x1005401000c101034030342075003015510441807001900c1c900f0340001141d12514280015440c05400200321401054101e500505e0118410b241e0050481080c10f100072641c41980b000c64038000564510841d51201b00505000354400d4a40f450404614950000d0940380c2d070084600840c0205152065040b14a20306026124001c10941250304104200540e440e0010020302240705149802180d0703215900c0162002c08500714040d10b03d1182d20204160107600045c4c40340303522105000d210340c0b640d03110140400c4e0340950050300c1d011b07007040c419614088280c001c000e01a120081141c00e96405882c20312001713945540000e030705071015501c144040f0504024078040d42d645407520a85495080c19010b4481c0405001214480c2c44800130400480205068601c0700707580803001c2208400511026984c0d4480f15462030188d401c0444696240206109a919181001c2d02900b0359440710744d07286400400003402281c1c054481a40d0101141c0300e4415050307080c90512095a503401d80c40c004c000d81 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 40435274 1250 40434024 40434029
    0x5030a060504050108070e06030709091b050306010602150a0f060303020a0b060d03090e0601030906020c0321040f1407030f1410051504021c020d1b03020403050304050603221209 78
    0x6141040e0040105e41030028124045880d0428141499111500000d050440e03688c0000c4172242010380c1d41003441201e140c0c080020440c1324a004d40c0a0381c4805240d1110024454603000d40c01248a0007501d0000224440e8001f0714200d001803009200982e50044070b006810507030050384219085410001000c2c903050f00120300f1661a5114899a5402004074580340504070300d000c00540450300d142d010380c0203080c145501941c00e42d164045841c02d0365a030380100881040c0c0410150003800c6441120f25640d000d1a0003080c0b8003004020750315030101c4411450098905881020030003c0416131000c081c43d40c0b60711524544907003000c2649024503040c1d0481125148a14200c18420741c1025424040000f4400f9500507032101c60485c00310103944840103506c9081800010603107010503072071740207440310941400061140d4014080860032405140030080103036108003c284080d10f000400345174401c02000c865496421070400c20000d02d000c02d0340480340442500451503600d86c101c9042e03400b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 40436524 1250 40435274 40435279
    0x6040309210f08070b010308090a0b0f0304110a031403040608070201050907140402070f080301050109120f030c0f0807030201060602010b011b0f03030605100908010f0e06070f02030409060605030a0605 88
    0x54420340e05000801e000003003600a200228000000007040068001d481805400001d8550f43d90780d24103088016a01c03180d5010f2081c810340c02e001c100d41c1b960f5025500b40003225410740d400c580d1107685a049908503140c2403580b00c0c60881000000843d0122030b583c0752030044010b1034035507160840107002040d01405203010f690408007003000303028001802c1d0048505090300b001c5c0c200aa600405d00a12a04801901e10600d0400d600148420500114102d40081e6202140a581c448081340e404c03010500c000d00c2ca14901c0c2006002c24440c101080200c0c3c02030940c10a9581140d03070f6900503600c40305048002d82d45600d000c001f03080c1c0a100383c0c1001002800d101c040030030308000f28111080e80c3c0c08018450544000c000090501c2940418003414028100358548040c108010306100242c4c070880c5055800c0075015035410000d80141ca40000504008116070784507410150f60211010100e00c08601c41030000082d81045801004001d064689940c0d6403800c00c41d840d48103442c41c6400c070740d0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 40437774 1250 40436524 40436549
    0x6010905090402042007030c02030c04180b0402010e040e010e1204051327080d061202090c0318030a030903020601080f0715050408060c04060e150405060d0603060e06040309 76
    0x401e03107507030350001c1d40142d045500040d40310442028050182032982040020200411001c080540140809444900031422203402144800401c0180e440c0c0c45491041c0c1c0b02c50000c074000141c6811650b507000307841410700d8880a203000b4041021034407c03500c80003441e13450317940000c8503900c00e01c142d0400d000c40c0080c42c2e2405003004040703000c1c500c070080e842070226070300e02117980c45840700c010243c658040d081da2140c6038000e50415142e25003000011000081ca0102c0014480310b000d10a0a0fa0f44d501034040407085e650300d00455907030341004144460701c107070100403d041528140001e0035900007540b00011201f070142002860104142c00030b40e141d03880f02ca0b4082d82032600184841c1200c00caa545440f0301c03c6c41343c900f210360b40070b40e5100c081d00d4810301003031005041510001d40181c4000d035494503041300c0740f03404221108440c80300030301c7c420208100911090809400800800a09120105031196a90340d0401160000c040906494111030144020142e10100320001070182d0300404 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 40439024 1250 40437774 40437779
    0x50604050601020c06130506131707083403060203070e030307020a03060e030d0905073305031512010c0201150f0501081e090f0115030b04140115031109060109 70
    0xc4c0d51003001e9404a07101ea000490143c09a025420f114009800082c0030306407070b01030a9003d40c00701c455900031810100d030a04c10340851560006988800c035035a0703000400a01641400780e2a10700f82c0c103210010140004e400c1e04800d07022081105004620507600184d0f24500000001c186000440315640710ba041000001e016030b4071440c1c1c81c42a241c02c10800280669080591803451180101c042803c50038103a001040c0b10020a00310101c4900406664056a49a40b440c40407400e17800e60340b42591307040d9a055080da10410141d540f24002e03602032074034400c0310360018100d48642010104603079102d0001001d541d5080c05150b0000c0720b88050034892509000394003c3c980c17818000c1e217041004601c0000da1072261403020003c0070045564243c01414691062520303070b0034a03001840c4560a00d070144422441250100b002c883e00015102000e84442c0d9500e40301c2c018100624500d9925840301451a080c10b000c2400194401c0209507000342c290f40501000034001071800d41402441c1008 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 40440274 1250 40439024 40439027
    0x5010e01020c0a051309170d05010e06011d01021204080102041e150507030c0b01120b010e100504110403060c0503010315090b0601111513030201051f12050309180a050604050601 78
    0x6042601e004441742d58901040e40340d182e008008186001c0d000303120301c492070380c0d00300309600007040040340c0c1c240d0038070582c4c1c0c0b074545c0703201d581d0310541d500782c0040c01e1384440c501c0e0076502c00c10358201080c0510544880002c0c18031400c0c4507030015000608142d5000030108540440800607801d00d08410018640d103e14124a05505541c010201018000e0019089040500c01c0d206203180650000a541095131120004030314061a00b400b100c1d40314450001003200f070340500d00d0032b110307111003005107500c28200f01c140005070208074001c141181c000d12000c40001d00340e000c1d003103c8907410f940e01030302d0303614505250054054000300710214914044007040441c1d0401c0615920190a00305000b4400300c2c500510f19014210b18001035640320001071240045209140e1a400c0340a54003d11103900c4002d400221130503607010b003420440360180e04100d100c20400900901c00e0082c010745c0e050007491000300d480f41d055131030802007044c2c0703030360412014813083e00c500c60300004103070f50800152521200 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 40441524 1250 40440274 40440289
    0x1030807031404030219080606030111191404030302060601021e0309040b0609040c1e090503070e0403050c0708010c111b0910090e0604030f0c03080105091008010207050705010e01020c 81
    0x20041c00b000800c140e003002214102080398001c660207010402200f0145c00300b0100f403612400760581d6405241c011070031030300d014010100c081200036411458104800281d012500303041004005000443c0072640c401d44060340600700450090300a05410b24140c0002400d192020800380500c01241241e80c165210010544082602c107450006414204200158517401103461160307102d414800c1100d0850b80c0864111b0548610a00b1100000d0100c6410380306049140186601540000e4080013280d03000b094040d0424042c1c01c00b6031419407440e0115007031001e0740d0000c4a040c4c2d15400c00d6500c1c0c581c044286406900034802416602425140200c46184400c00c5607200c0c802210120f8160400d005192004192102d01048884240b44a15454260448054022840100700d02240ca8050340e40c00e035484c4e52540c0d036445243c1c200340402a4101c03014018040c42c0320300a00201d00c52200748000c000e400d0041005094951030b1400041c03840300701c904031604541040081c44c090f1748030040d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 40442774 1250 40441524 40441537
    0xf1101090b0f030c22080705010c0510230403030c0909020f0a030509190f1109040312050406180318090c050d0f02070609080301090b03150a0b01110d05040e060405010308 75
    0xb0307042d50b6a40c4681c3c948680c1c070f010301c03403c411128140c01610004005040c0d01441111001d005580025507980010f582c011080800501207800200d0041881461648814075a54503000c0b4600030048080c84880c0c12001194201c021950350280a1021a08100c40368004d0114003000e41c034203000040b00e4011801400070200606407107078046404504180080c03413440c2c035030125040c001d0600c4d003070002090085802c2035842440b41910450582050351004c3e110700d0f00350300c0c0d8211406040040d44001e05005205803403440d5280750440e82c2c4280e640c0ea40c00d450307000b0364940602c2030071070790a003a004459900c6030b1400741c070b03141040803140e03045000e4801c908051040000e0003500074803400003903c6619001407a0516084a03d01008984c40146040c0c1c1c0c00024204510311841c401e1698400e0400e5060384c4d90b00300c440000e0381e0801240c20010321044180740002406140e50304692916040480c4040884c00c081024008444481045544007400325024081545180c03038002c000d1150b076 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 40444024 1250 40442774 40442797
    0x9030a0e041e0903230d06080f06011802070b0103080306030f0a050606010c05030d05091c09080a0204090f1203020a022103040219080d0207050a06030b0a05060306040b030303040f1101090b 83
    0x200039100c01e06002d040c07a1184990305a000d00d0348840510801117150307014244486100745882d002055080300000d87e9644000080007c01e1583d080c442e03000c024802507440d0000268081006000113031140001500840c41070003034a0700d0307040280400d0b003850220701c41a1010f07801a400c00700815030000321541c012100b802c152008500504000d030861003810b04c2030003001c3c1080305003e104203000408401e01c0a800160210400e00301804440303021140c450701d0816448030100c3d1002d4642030b0b201320a01d500c2100c41141c410007507503580e00c564040010600219038003040d80c601e0660184014140882400b01c2c25030390182d0202c00d07480320300014002074000c1c04841e80110880441100a0f0701500342c140c00c940e1804450800255545594098203005403800303100000c2a9001c1e01900031600c100a103200c0d09142840c09010140e0801424607900c203440e000f00014503242070004601480c020070454211039101d040102c0811a4024002c1c10003295a2040116528400540d007011842 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 40445274 1250 40444024 40444031
    0x509012111120f07051c030f031a0405070306030b01090e07140316030b07020d0e0102060601030903051603050c0d050412060207060b060d0e06010602010509030f0c01060b0309030a0e041e 82
    0x1c0408a03000024030b1010000500c14a10440180f0708006110400c5a01c02c5031207211141d00c0c0303054441100c822240c01008102c1d02e61940094a000c0c2e00038480303007042031514580070131080740041c0a445040e80d0b4440466902d04051041c088030394a00c50150a11041c1880b544814410840d940e10080c4034641c401c040d035000a04031a0380522480c4030754a250402c80308000c0d01da0070107007829074003621500d015120755100580172600074080c1204664058000d050a5038800c0b0040d0054812900100e04009003005005c580c107101c41d00540450b80240d4800303481d15480202d05150000d2016050f040c020140410007009108411200101d81e011402685074016403074400041c015071407100d43e1008022518903a406225401000c001a515040719000d0340d80c0d00060342200c8050701da684141d00b0800c0701802151540d030050500402200000410700c1d1381c2c4114401a8006139401c4500c0c0c2c00015001c68070603031040c08a00c0c3c0480495041020074400d0b0340003207295002c150840c030720702c1d00c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 40446524 1250 40445274 40445303
    0xa0303050702060d0c0906020c180c090a080d02010b03100b03060705070f0f0f020907080919080c07090204050907080106120903050705060705040504060f05061209030c030a0905090121 81
    0x680d40c098402e2504102800e201300c0e0f46170300029100368010f0040d0340041c41000c2e078094a62400440c0303001141c486004500d429150450807041c9a0322105160b42c0181d0001e4000800c40c1c8100804011122690300014004254004040c1004828100c41c820b00d17040c0a40c0c407071195000f24000d5008501030500d95a1504280b424000c1d00d4448500078021603000070240091088a0551041641c803c868030502580c640c041170f581c03800305403003910703056210f0000640c0005041190303450160095220034201a00f4409152034239055800460b500f58000c1420010303802c00300201c40d040703400ba041c02001b56040c01001002c002e03088210740701c03032515401003205140c003a1084030003294001c815105d42d45810800502240e1080c42503900440c5041000110b454501005405550000300610320b4240b030358064060003800980380c071031075010422004560910030001021080084d40b41c0603001e614001c00c010031000f0503445008842c11280401c3c0343c10b15042c002c200c0c0b00383c2c0141748454019 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 40447774 1250 40446524 40446529
    0x1a03040326040b0c0309101d120c0d110c01050a0504051c0b060117060906040b06030f0103060501050d0201050a0f030204090212090606010f080103031407151d0c0a0303050702 77
    0x380a00800141c80001141040400e030740c035101601c2030b802032520702c99a895010307035500c2ca88002c50310500143c000c03e0b942103516542e504896100c1e41c490404880c0461801e010900309445c096800559040c00620a08441c03401d0125207251101810014400054078404c581c981030003401c55070400800203030420700d8900420548015003800b43c508041a840c0742c0c40c6240000d00118291160000b02c40002c070300d50b100301c80c0807030811660010031990303407100010b001c1e070017901600c039a501c16110081280349485001c091840b465000441c40d02070352460421008a80b01070300418010300482032014050707600030007181e0b010080351801c4a40b070b10909004500a00442c4c000e512454000525030070018003a200d0140140100302c161441c2d6110100191612501008800003144c404401040400d00401000c0b24030408201c0461800c1740ca951209411061205440001d550300e0008000c9076043c0700c80325800d0302981000b400c1003965100000d13401012448002c0400100250740011034 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 40449024 1250 40447774 40447787
    0xe040201030f020c010b03010e010606050f0c03040905090a0b090a03080f1f080a02132309120f04080606090601050f0d06030512070213051005041a090a0b100503011a030403 76
    0xb4040d41c01191a0419642d003a4081c00d01e14009074460340c00c0030400040c2000620400040780e40c2c6842d01c0e403038141801e004109a4000300306102527800140800181040c040c091140700f51143c034094142c5c107425150207004200003031314030b041c00d40c03054008000180d008100e49810022124001946542c1d00034443c04201000325001ea80480341d01000548910000d4198081031003294510501d101188400341141c803030260140c01020300d40d61145001c00d040407225000b1b071100040d5a8407071028503182d0a183e00c044280b05103c00e00140410075808144040d0b90800421903800c0254240303440028104d0180741d00f035900c1c2810000d2070b601140459071002c1c0040da801004c0e5410048a0b01070701c0d141c1e07040f50f00183c2c05103c200244490034038491003828810660741e003280304018240400c0c040240301d00c0030600b40310780d21611000002c0d5920103046103d10702002020980035240001c0c0a1804000030508061080c140700500402c044075103100e90041d903034040c642c0c813641c8508084660 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 40450274 1250 40449024 40449041
    0x1060314010b030601180b0d081306030b0310020a050c0604030513050f0306040b060d020a032d03090603020a05120f070324092304060b040506120a02101202041403060c030609010e04020103 83
    0x601c23028400d00170040c00f4030182203555843e03105501880c0d0307119410307030980b0864000e5691580280c001e003d484401940681000c4480c0d1038154144542c004a0741c0c075110040e101640404c201294289800c1c000b103082102815043e9441200d02065402196a035000517100401502881c0d0009600b44c0724031800e0400207030000d10000b1090341e0fa04080001780c014600303650040c14000c4154030529104210f5904590b40f555410340150300d046822002500004c0300f0408021080007030003940f1b00169a2680550311100b220407507400c080c0d0001d000c89095070184120050030100c03851605940009003012944210070200b81c8451404000e60f00c00a100080701031850400180802c1c010581d21003a40100251010001519100208a00c015500403004e4560f0301c030541800040c1401d411002d140d4546052100b06000d03580d4032501640c00a400a0b01042008200e4803280d2408002690b040701081017104d245050840c00f240400005004501c0350030055400300301164425404200b5 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 40451524 1250 40450274 40450279
    0xc02060903032b05040807080d060906090b01020609070f121e080c0f03042d03140d031401081504080c06040605070e03060f060d0206040905070201060314010b030601180b 75
    0x10740d950000303911000c0d00b146842c00140341c09a10540c4101d003e452181500560f001840541051041e90701c48102c1d90011440214894846100148480b490b0050401800306a03401051100800000901c2d05000400d820081d03400700b101000080004640c880a543c0c0006a00200c2c0d90141071a510541c00c42c40343c006907001c0111000c00f0300c41c004000d002840d0301d04040d103000e426140529a9640541d0040605644210300d00003040414000c95510100445140101007030b03a0751507003080c400103925200d0340c0341c01543e0400001d99041c892481c40800602c500308003941084541d130340d55011105551603065414011805001002c0251030603007020b18200c802500d0203242150203002c0680d045000704980d07404920030352401207010352040035850340d59040d5035111810014074040b40d41082c7c0e0004400c0002182c20119405418030070244c0e41c00126840346940b600340d0b0074200032076000c030072a40b614658480580c0c0c0829690b0441d00002d202c0071442008414590080c0035903002190f = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 40452774 1250 40451524 40451527
    0x601050a050f12040c0f05130506010315030b1008030715090816050706140306010f1d04050406060501110304060c021311030403020a0b07090602060c0d0e0607030506130207080702010c0206090303 86
    0x1d0f210700ca0300982c2d481603204100e000c2c4180d540e404050b51003007050198651200e110207000317280c60055444075074080c1c0145800b281429107d404000307189691f8109a544044103003c00c1901600042401d00816204009514142c81c03508e421500001e6603030340b0040c04d41c9610504080c00f54840c25a60480301c00c4649068454140c5401951000c05200b2180440e49001a458017280c41e4002e0300c1c458081030b15600a1500135080071121000c00c040700701c000518054041580b51141d02c140b51256118010006245080c8030002d401c001c070f004074030500e80d07200300000e000082c0e02815103030f00c40d64180c4640c48100c0c90551f804002e0020008003c503074010101c01c00050680c0000c1204800307025403410a042d40382d4030401c50b04c04980d40100c20241c0c5c002000320b0403d281c1314000b031400c50503078000010030540e44246103007401000d440c00800240c03100c0a1100750315011500400c803403c001021132400f6016a60490b85025030003029040c171801d10004819511a502100c035180c10042c1540e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 40454024 1250 40452774 40452787
    0x302060714120c0c0406050f040b010207080a08090307050607050a080c0c060d0c030b01030501050a0303050313050a0308040c05040c1202070203010b090a090308010b030408070f0312110301031b0e0601050a050f 92
    0x501041e0459591400c0c40c1c8141441c10044e0f08103440b40c0403d071200541080842500703403040c0f0003e0000f070840c042c1148503402001452044c14416000b40705d21408140e652018210201031500d0556040284244410842c070710001d000010007560a070360182e00d4540f40c3c00806445400c0c0855100344c1070b04168001200c00c1c040495510002a00000e504c0802c00d85803044011406c0360024090150040208241032000c40d019034003940d030009802c017000300400000c2d9220740c1403aa800e04200c01044401090008100440c110500903003001d4808005504030f0b407000a06400c10042d4109038554001005015502c007034200015a8601030005142c4e41841041c407001401040b9058000580c0c8200100310441458103c90003141c1115201c0d040000980b60854040040030044081c40480848a030311251310340101d803116041410015201c1d891070502018454400502c0c00030400380d038005000b42d01c078903019590800b2080c40d001c0e8407210320308401c0d2494440c0a031f0700c051090300422003 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 40455274 1250 40454024 40454053
    0xb040807060c030e03090d0c090608011d0309100806460f0302060918010b2a06010b0f1e0a0f051206040f0b04050405010906061a040302060714 63
    0x18a141071140400708075800da6250704030119403010941003290382081141803c00d00c0c0c003281c088032190007440c1e603c030346a55444100c0d0440d601984454826510707521a4848541028070040c1c4079500c00d000341d1b1502d0741d10f400190004559580c98001c0c080d0a0340072800c2512410110041c00c1c15001c08051000204001018440c0005407400310742c0902189a0310400e81003414002220b5020302c500d14180d08540c204a00f541055a8003500b004120b00710740605507080d54404e000300340348800744d42c0e5801c03000c0141d501c00288810301042414030a8000c1d44009002410b0303411640d8680d405a200d8a6528151a9510402c402c18400030101c0700640d184584100080c5112240303525a02d05640e8500e02c151014011071200c55086030a01c40060f800c2e0800d0340103002448080b800c0051410002000901220b405880c150b41681d034818001c0c080010713b20641001d070450704000d940d0711100f0743e07000b2200d01c120f00000340910700209003074040106401880f6590f81d03100c3e00765510b6000100c1c4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 40456524 1250 40455274 40455277
    0x20405030d03050412021912020102090a030c030506010b03150904050309040f0b0307080109030503011a090405040510110f04090906140108030304060501091401090e120a05070b0a0501061704050a0b0408 89
    0x101502c080f17032142862400140002141c1100383d240c818840045000394540281a030446032150007595002c0080d41d00d80d54a1291400203148600c0c26031f841c490a40c2419850044140c0060352803407010420f21106001c00c8000740101e900843c1e81c0c06040d42c42c0c0c6440380c1580609411355400034213040400c0c0c061089504420020341e03007030b022101d51559074003800b1b003038484500001e40400c40402c01849691b8581100c464105135500751503103000010342c04103084072808c54043c0c407213400ca0341204c0c00745e1603140560a52483c032000e04038100340c0156200319041c450780c0710b040785843da50b040010412006802c00115000301501c400d0a640c0d4840b030250f201d43c0200c408480070b500c0c1c4400418480070710f1092807040c04180034080040e030700b409540c20040444d0058003940d80318107100c044089000c14003c1411070920750725981c0f10074141c584001c0008001d0f014007070781c508180042c401203900040ca013400040c0600031307107119182c500f4414100700b070001c4082c00000c00700e010001404090360 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 40457774 1250 40456524 40456531
    0x207090e0c1503060a05120c030d030c08100303080106201203040b0906090a0213021c060801060b030f0f0606040308070501050f09012a0e04050a09020111030f09040f020405030d0305 80
    0x680300b00030307141d22805280c640c0c0300403203030183d21a808401c01e00050810180d90710160b545541210601058000004d103041080c0388001c000940325a403030f040c8994031901c030b01d1f00003400c8a07843d4016411aa07025140c0b440501920b0708101d02c410085095074615100102076911410a445884514440c2412158012a41901c48488034408180040d50020b03015102d01015030151800c0d1000354200b108460075541161880c2c0d409101c00c40c0781d9034105d4840c8101070050701c1c2c0050b0761446e0503099829202c0e550312411031a201441004028100b01c0d506560060710180e0f032604641d12100021b180d402560406400281d022503250704000f015400140200b22401c055100e80c1e442148031400c0c0d90b60102c5601410500c47c10005085007202801c0070307071108604000751441c2080e804201104c400300da0602e90a900c501d08203007036503041150202520560005186040307051002c4c50704500c6003c21903801550780d401a002550142c2e41074a000d00002401c0d1a10b503140c01c0c0c4c008004c0c01054 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 40459024 1250 40457774 40457779
    0x60604030c08060f07140711060708210a020a021207030302130303081b16030f111912050307050708090406050405150a05010504150c0615080703060506010302030c07060c0207090e0c 80
    0x4d00801d4805d030061040781c842020181c0c8691910b1140d036241000503a03919801c0d41c000300140f00020001c4c661134003400100800214810b03da0b030008004518014003d0241e41d280c9104010543d8059408070303c4140103003200e4611b0b6900c16013032808500034401c01844101c40169410040105644030101500890340d142d81c50301d86c05034034401c2041c91f1003014420690185004c089200090113001e00b44180b80301ca041000b03a1000096000307040c240960081001c0040c03000208040001440303203180a1802ea00d4910308600c0c10800c0940103102d911800307000614003294640940e41c80d034126070f01402002c0d105004600703003016040c0340d00e61001500c44c450300c1512000309095214105032401c8801c14040d600140035450301c10759110302d80c2c210940d03009403a211520340e4021403888050003841a03500a002040c51403c0c844100c450281556040600400134044c2e0404060140c0b90015002280010950b00c81401a45480b29603402080a1410220342441c54000450311031840d8400f07 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 40460274 1250 40459024 40459051
    0x315180c0402190e040e030c01020405190e01172e0b0409080f0c030708040b070b010603110703030507020c03070b040501110a0209040605041e0602090a0602030a08040b060604030c0806 81
    0x6a40c10002640558448000c03c1c90742c07641c46030b184910810007041c542401500001c1c4a840b0f401403982164030440301654180e4000604002c60709083d90031400c483ca220003190303156418031100c100d2008040c4030f16407000310540d03890305842d0014000303c4800044002040502000750714030001496556502021031858052042000d0900f4058055515800425146000940a40c2c600284c0103500080e10314070050100d00c001070b8040c0300420107041d0096400381c4034609840c0602d00b040c816044141050f040507190b40756208500c068400d210b51608002c10660b450a0f0101d28148a06218075403500c180140004c68050080040c000e5640a0365185c00341c48041803074694030601300c05d00a410010000004001c551a03900c444d400c0762080e03e504071104a6004028482e544902c81950500c1e030016003071100d458140c005000030007881c0003031410140c1544000d40030740001840601b03001d80302c4c0c0c0000c005039620021a0042d55000344111005500e882c8200c3da0390400301e454180b699507 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 40461524 1250 40460274 40460293
    0x1002181005070302120f0c0601080a0605160e01050a030f0c11011b0207090906060b0706060e0f0903090108150a08010603060c0315120c0e0a0524060904050402031518 73
    0x803031401ca65600750143c0040c0106100170740040b071241d009821400d41c4035414040900d0026040c0308440c000c007900001000030b50014148142114005055500c0c20800c0112000303030103411860700442202e00342401501d81440001c1038014180c01c000c0030041614010074400c02c20b402100120201c02c00308000c00440c2e40e01d80e0940502404010301d1005a03100e0f0030104450403139908000380c0a40b00320804103246035507000d13000a94210103001c82d8442d403144411700076000d100c4401390f805081d180c0310702c80300e01b0010000340e00d03803141d14161410444c4100000b4145001c90340301c102d2184015120344d0000e40d4031039906000b441ca40c00221982414940e944003a1480380c010044690b070080d5200342c140d0320707282000703440041082c003c8811603807898001030300c09004400c540c4a80088480810240751180d0440d40450341ca0690b610401300d04007010510b91504e6041c2c890304441070703030b00046d2903c981c00000e1a0640039024180d01c541302000b041000324a62243c081500e806000b00c034040c06 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 40462774 1250 40461524 40461527
    0x30c110307080c0616050708060717010302060406120912110106140a0501050c1213050118030c0b0c0a0b1807120807060b010509040f0608070e0405100c0210021810 72
    0x45082c4a51070300356000c0003602c01145004801044a80c00d41c2d1414605040503690700c0c0d080201340d07400403403a50010010406c02035040090440a46500110700e0080e40c1580c0c00903915004a00a480400c034442c08083c0d00b080b416407015004030780000300c0d804420700500f0001d1600c2c0d40110941c0c0e45508000c40007034000c000300f0390000c4040340107291001290a000044880d5041602c04014502c00c985070006c0000050008040e03006181050320000d034103000024082140626140700316000d040001c1012075960b0000c001668100d107801030759031081c4140c00c2c1ca41030005070045c14405242003031001c001d020030100d075003003c00c0e00b007a111100d5868920740018295000e0140480d0b8082000c40300091031a480060b41042c1411f020342417141c003801150442c0c0080909004081d0741e20300601400608000720002031006964030f00103450159075847e02d80400d5000c901520751030340105002603000b4404a5583d001d801d0003152104c0348044514000d903002503101740902c07241ca640c80080ca = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 40464024 1250 40462774 40462783
    0x15050904050601090507260703060602060601020706030c03020c070b040e010605030f1303030905150907050a030f0b040c030f050102090a0902070b070e01050c0f01020d05090102070c03030806040204050904030c1103 94
    0x40d5000000740c01d40743e1030889400003401c4002d00303060402422510443c80202c14500411642081c5a4107003094500240c4c00b030111038440c3c21a209652110040050503a800039851003918150b00e404940c052003840301350081e02645440040c1401f036110f0200c3d0b4503030b4580c080c00480d0910510121640d036a504107a61510050302c0c2d4400c500398450010b11812545026036601e24420318001030003401a40301d440c1004880c540304000c48000343c003172007820b98041040e44082c00007110903a0f5810b285580c1c1140038100707220b00614480606c4001002d00c690880d0351030085401c0394400c407982046240c124001c0d0311150a05100c0c0100503c04108001180b0070744d49081d5100d448801c40341c89022068901d841107140181c1005070030004000500b0081c0100c607000360044001688130707484d07200103000ba41c03801040c3c0140f07a031040c030100b80428007080c50a070440340c1500f40900342d9114040860042c1c130031500401c1d00502c03e4410300007003503031040000c00024040e80c01034500d0f900c1441015140c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 40465274 1250 40464024 40464031
    0x23010305030412050c04050103080703020601060f0c03031104091104030b0906010b04091a04110403060506060a05250203190303051302060d0f0b04090302010c170903040909080702090406150509 85
    0x2503030003440300384075a01c203003960407052a001d54201c0e45d05080c44000502940c2c0241c00458644074046040420540c04110813800340449007015140e15140700d0004281100c50040a000c2640b0351904034050403840013107801806003008103010500180680010a42c01807000300c440450010001c3e11601020421078146c4240401103880c1900d4901020080c1507a903441d070f030040141c8440381c2c520b56914480d2843c440200c10072542c41c1d41ca10300b001c00482e94010206e600442040200e4801550701104403840d60340355240b00c1c1c1350365688055a08031020410b07402074141c03140d080550510b007a070b440300c842c1003803080d41e06005030703030b240c00c41004111440140290071a03000d018041d405d030340310340090380f104400002c0000c40802e0030000400341c80c507008040c0e0150f507562050140c55030744050001c994030b040b00c4904606003020040b15a8a102d5481540d6449030b449500d001007210130f0b002c0f40c95a5800800d0440340d4202030500701c004040a2812582e030900d803800005203410b150f0401c0e4030 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 40466524 1250 40465274 40465283
    0x803240a0b090319030315080c030d050a021c0c0b071b020603060d0f080706050c03040309050d0206041205060f0a0c020a1e020a030803160306050d110105040f09230103 74
    0x1515840c140e084011078201003000e9515000703102510324901011103040004c1d902076900426103081c03211700c012000b000303600400c0041e0490b07981d40040c2d441c0014040ba00340c0c01860f0aa6581b00c2d05882241400e0b07400c039444040b40001e600c07400302c45078880c00f00220203001d1b4481d0207a6460310300782907035075201480550256000c14440c010151074480c001c0d6034009006081044004c80036607420407490848402121000000f083c0d15046c010144156070317020079101d1260b491410142c60140c04200f943c4200303480b800b2141c0c0300d102103450302c03000c2d02c0040040d4800d00008005920304141c0310b00f01125480018000d441c001a0420329901840c03043c0f041c1c82d00901032006441d1540302c0305001c6074200c1c001040c10681000700580380c20f20044c0003103025809190300c034140a42b00145190b410308011042608003081845190768602c02051a9903010308681125040d01c001680c0c5800303154010701181d950310500041d0859243c0005d07010881c501c0e951000c01144030380504010a00780000380 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 40467630 1106 40466524 40466539
    0xf0f0509030a0c080f120d0e15071106060f011409030c120d020c09160507030309050610170106060e01050a0302040b07030c02010305060301110f0906090a03080324 72
    0x2142c5c0e42d420001d4082071000000c0194140204131120400f15a201c0d1105901c0004000c11840c422010030081302a151002001e0800311a424241c07103240281c400085440c03500f050403681c1504141c45d00b0f0441c0407a010001c0e0f080c1c10aa01580c0c040c130580c0284049135598a07046003005495030003d00c08070305140802414514103155440c001c0e0303202c4d0140248010390710b006000c01d4046241a81e120f602a017821000b41c00d6480307020b400c0f8010b40f01070100d400034000d4030b001034802c200031a10f00006108041d5080314954452403002404a040410315503100d0350080c40150700501e800360030241c8804210400b94803115040b004502940101411941c260056942c1314070210020064581e1100715a80c50303100c2e07899403401c62000052036604c20381e40c0310305503030716172002030100070762280c0301e182c1100180e0055400800d19485a0045503071105610031000c810b0b000601040e = true := by decide +kernel

theorem cover : BRFrame.Cov 40287774 40467630 := by
  have h0 := BRFrame.cov_init 40287774
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40287774 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 40287774 ≤ n) (h2 : n < 40467630) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
