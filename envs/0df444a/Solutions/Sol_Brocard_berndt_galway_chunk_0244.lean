-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0244
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:42:22.611497+00:00
-- url     : https://prove2.me/submissions/a49672aa-e2dc-4fcb-9eb0-0530137c22e0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 43705040 ≤ n < 43884896 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 43706290 1250 43705040 43705049
    0x160212010c0819020a02190312020a020102090f09060a1703041e0911040501050d02090d05030a0f0228080a02010e011805160501051801050d050a060303080907081e0313 74
    0x1200302c1403500b4420104a010003800d4032140d688181312118000e0f0740083c0103030008218442c01014422642015610400c074030f40d100812030b00000f2011a41ca6040d00906034154094a06d05003103c0340c001001a480401c0340c0c102c1e04a110540304000ca4080000041c1c5048004401d8070301e4180c94401d245a0b10700b50941e01040d80c00e0100040001015038414120b00c2d030130324041c1606003030601c40028501d10a901d600021140c002c500d1303070441da407080a5005915030100c2180d603204100000500b4030404075600d4005030060000304a600e41c55521650720710034400c4500c00804445550721400c540140702203070708643d62054480310f000703030074410007546a081444034000c2e0019498400c0c5444101820010079244d010f0b410011641c001041e0b0380c0c07800301d0f4500e941e081c07804640100c03031600803642941d102d02d080000b4081d0000710355120301c05880c0240d88000340c0e540c81c540030350703544d410700c0c403801603107920040b0007903030001095041c40308490106098902c1d180c041d000c0d02c1a83c441e00e410 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 43707540 1250 43706290 43706297
    0xb010e0103051002030f0f04021206090c01030f1a1002100c080402100513050f0f04090f02120a03020309060a0c020d030807030e010b03190804030b01090501030303180503160212010c 80
    0x10300601900f08404000512510019440d5280044a9030041080a080400100d24a8002c0f60455941e54210b03200d410200c0b0481e0091b00d8080542d641d600000007480f80401d00d040152001003000e40100042da89031005a805001605018051001c040c42509c07021405a9440040790f02100d00444a12202381c3d03841043c10b00346401000000107003a220007043c8201000f511392011107a104540480e941110000810400039020568a0850880840d885450103d803e4100802c15440c80d4609000359171140410a0440404d03546510103100a00580e000380500400c0f031401000411007081a480d2000c42030506a011179681200c0171412800b060842040206065052003020000c00143c0001d102c40d021801c0420380b2401c440002a1905e1103a4a0440501110340d04541c0203660090816000f5a910210400284000c0c00124002420416025035031405164054802c0341c02a014500c2d002203051a120040c0354041d040341c00041c0311003140b0540d007084c4642200100d07240c8 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 43708790 1250 43707540 43707569
    0x3070801060215070818030c030d050a0b0a1a0705100c020a02010206091605060c0717030711010201020306061b0109080309010b0a08030a0507120c0503040906030b150306070311070b01 81
    0xe81810b040c443c0e42c0541075a200100b20600344d005c50f9481d0071070140c1010300c0f00280f00f4800c1c01c2c00e501c54000506241c5c84009800007060f601540054401e40c0b106c0d000b0016800c0741c0c2c080046440e6030b4401d0302006659441c00c00b000844040051518500ca401100e54025007040c4c254190b03081c00c0c01000240c2c2201c4d940382c0a551701400040e500c40e01d140d02400340002000b4200d0040c400901549002d244080b03202e8202038030802a035000340180d16000c5a0b110b4103035a03002d540358051101220b5200e00e00300001e0321540140241c0380034401c018145410a40644100464816205000c4580790340f141c6100300801c2046006500444514002107034401064081c020040c038243c1c000d0003e40e00400600321810b070700c0002e4581c010ba012500700c0394048030303000c00c881c205522500680305000c00a00000c41c0000c59012904480c45100c02c29629910100e0000248441c501c046401d60010310010748140d00c2948184001c0d110000b26600301a901e0b11030242048098012014155899 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 43710040 1250 43708790 43708799
    0x60c0705031b0f0a080d0f020106030b010b07030212030606030105040b06090d03030608010605030303010302090609040302280c1403070b0a09030803010905040c0b0f0d0b01090909060501050a0909030e150405030303070801 97
    0x1910020020f403016510355221920781400d99660b03105114030b4008205030404102c0e0082c1c803c0d040704000b550851217074482ca5840e0046c01c66030381d1000d0800c03005403241080c1c81400748241002d591003510010261030031627180a05000151248101c1203a200104210301007090341d8111010b10384c90b00954000a03510708000708207084542e40c0d00614400d5006000410050355000700c180c0e07020340c1c141c0341980c00e521145001d81c40c0600e004c1d003c3c6507503c440a00e1160a40012400520032802003404040c031a03a0303040300c0c40c80c03442c80c0c200780c0b90160007100e810301a1500100040194110626021440d10340c0d0361076808041d0401e030402c07880640c90300180014000c135011300d00050211030391802e02d008241d51400126118421100c817045031228000c8105a0003059582e00424141100384900c00d9513260142c000c00e8240505441010368840109020b0901e210740c07c400e42d4542c41301140004030100708141c611124040409002040101043e2524280040c50207090240c07503150103175042 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 43711290 1250 43710040 43710049
    0xb0f06030d1b110301060f030302010207020f01090e07080403090801110c0706030204051e0a090e100c02060108030706051305010603050321060a09051806070906020c0915060c0705031b 81
    0x802040100480c04020741c0802140750500c8003065030110341c00743c980221801003405411594444080800c035804000180350f01074000b030250300d20899901c04000343c03844c01940c0c840510701500000546120014019074003410260341c0060090401c03031121655648103d00752040d0300b941584980f804541c03180ba150301000300101600203424250304141c10900481c04048002c00ea0003544826801148890303218240084080c14103850248003c04d90b0500c442c2e030b101001c20182c001649012111000380380b02080310740c142c46298000d90b14041c49510303240060000030b8440782002e098089400001602440340c1002144600051a00d40c480618601440240d4120150b403043c00c102c01c001c02c0e5507641c4514815a50f0032070001405440380100b000c003c4183d50503141451188a00780800780c2d0b00f2403d03000440300c1030360031030300d49000090134815505030039501c4c0d0242d8039424982c50040d1038040040d141e0b110071402101c01196944000030303d0161401040c1c48442040500d5603407a081 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 43712540 1250 43711290 43711303
    0x203040510150603390e03060103301d030f070306090308090106060f080c31061b03030504020d0b19050a0905060118090f050f010b1e060a05070b0f0603 67
    0x82d0700c01500350300d03080c0a0080e1784607180d01400380c00340d19810301411564001c00c2d004402220240c01c5450030340e1207150420745603d0b080d800e4000ae001405405400e806604801104190380d507035841e1941c03180e600c001040501c4070402c5c0785c2c14050f000349640000d04c1005698000c40c0620008100c81005040180500302c020b010319030140d041400070f2005541000800006151034a00605039589861146482e4011104107110300d14a02100071300000c0c00d0030f00240014040244040c459036507003416540359413140e02c90342e00700b90001402e00200b0b000c2d510403a40140041c103801209800f0707594000d100341d0708403800c0140441c25000d5003100c201c6071181c07640c460100e00c0c081250091a07194680e503160148100500b40e00e00754400c010341d51040d0000074042d41e100303034212054406490703d0740e228401146201c5e10380d848c01070f13403114610b0011541700d80401d01200d003c0103500b4140174070409a0144015001307101d02041100300280c0081c20787c0e4820348501d80310300f2550a000040504141 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 43713790 1250 43712540 43712561
    0x303190b01020a030c0b150d0c09050601020304030201080402060a05040e071e0504060c060506030708100b04180804090902010201110a1706010305071413030804030c06030f0203070e040203040510150603 89
    0x50041c0e04502c0080d420507040d170307503650304216684041d5560308240f6030031044010040ea0801140c42000c000c01112140e00425542c4114061046507a25001241d5030301441c840680003c004001140150501100520f101005441c001d441c2ca40c5800c450502d0381401d54602c0000784103030000c050750303000c044410030304c00c01c003843c090707181c540b80c2000200303040d0003070b0000741c94980d0303600c0030695548e000c102140040c01c81030241c521003070b5039000c214000c000b80705040340218200910716244113007146c2c8405440703603c00e07803050034142030850314801840202c00403030542d940c480a810001c18007801520f14504944c0da1a43e101844c03090071141c0a0f13020381418181810081488021a001000084038240182210b070312000900750204c0c00b12071540c070103001e100c1d00050100c1030040900141c0166291a2000e02192a80d0750806080b440120707068400076040c420000314518140c0c005582007030290f812a040b1490401c42c140440740c0785241c86501890f14002003045036054001c0300c40b1038 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 43715040 1250 43713790 43713793
    0x1128020a0506031906050a0303080402060306030703050d020a0507050a0609030312110412060b010305070203030105150f040305160f0b0403030f03140a1e060509010b070c081504060b060a0210050c04080303190b0102 94
    0x47e8515035000c0c3c4a44400f61000b0b104000210010301507407400c1180310029070700902203d00074041010040d440e81c060f6801510f5900a1450205072401c26503135520403034005640721100185507403000c86483c0039103d075040b0b5607601c03441100c0020050340c02400c00340000703040280c90003185140540c216a001d070701e410b042c1030411007003029080e0048181c0381150010788408141c4094440d0040841c0b003401038000c1641b10110b004010301074000b07244064104441c4500d42d0103616241086e00045583c400c00c21780709410401800040e120311103903814003100b800c0c04a8000d46c00490803030303a00c00c11101601c460b0390350011004500350080858400c1011440104001030400011400c002c805006050f00d2000008405042002e0104d2000082031400103484090b148541490038802007520700740d82d03507424040d0741c800618218049420300d44680d0002c01e61610142012005044c0003004040f9180051200050405003403000390301c80c60f0301e031090b030740021400c40705101207900c0d104445045 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 43716290 1250 43715040 43715059
    0x30c0e010f0c1103010e060423031611040b130b010228020f01020c03030703021b150a12020418050f090a080a031e0c020c011128020a050603190605 65
    0x22950040012050b1940103e82d100c0b180c2401d402190140c0921082c203003c9106074800c00041c44080d19181462041c0d115030f50110b0131030703142e5141d503d000d1841203c00d5102d0300050074002a02e501d20b4501115070141001c035128846000203621041118001c100842c0c80300841c00480d80c0c18801480c4041c80242e07852031004c1d0a01000b505070340d280000178069074001d84003101c16802000b6200380c0400c02412269076010900c0c3c001e4580011040381484072035a1041c1065a00d410207a1001c2a95000140e0341883c0394000215500c5900303107900c1c401d09600300008202c07644e03409001c1c1710341c480b020300100703080c240281141c0c20400000d0010920f60040e24000c0001060a41151840d007903514000c141056442d44440710550701080b010400e03480c000b002500e01da004250000000400d0302c1d1100c9504204917490380b0341041058204803103503140d048040a940c101c80380c40b04140081d211648942d100c501180d03190303206485d0421880c40302d03540042c00c0d001da0301a0101504058420003007 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 43717540 1250 43716290 43716317
    0x1a070e0108090c011101020702060313060507030b1e0d0605010801150902131a0405090109060305061f060f120c020106031202010e0703080d020c01110904060815181c030c0e01 77
    0x2103410f25000b9581c10000c880d016084051400d4060301d52040d001030040c1d66900b819030b40c3c9010044180c104071104c500f448005807400713002c1e102e071041d2600c02604c80794540012210b00301b8203c0a0102282c0d20032107000020011903068810140a00500270000491580100820031100104c3d4400100c5500400800c1c10403160182264200c40b8507154040301d0600209500c44280903036003100340c00121041c00043c0c01d41c1d060b003100007260700580903038189454900e100390200710f25003128440304405050402009100e03400170312001181d8613005242165080a10003950001c03190304006070b4680505105002c150181807801a1560008000b0141404901070301e89600d48006801200040382d10401c0006980498201600b50300082107104c5240040040642011040c07500892a20304007003400030340094020f136005281030680e40140e6070141c00d00d2141e100f0386446419030090001c010072205010b0f00d851140501a1804255038a0a0900602c8045503807074050400c148000d40b86d5 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 43718790 1250 43717540 43717543
    0x3050307030302090303040308120a050a0902030c0906040914060f070f02070501050901090302030303130c0512070b0a1106100e0f160c02040e0304030807050610052b1a070e010809 79
    0xe4030254141030240c0c0320414030002030b045000e180d00c00740406c1d03030018604149002c403002492161f8030b154401c102c2ca4950318011012103201c10002509035000c024846c010b49092144581d101e0401403010501035410381c0c5107461035800d45144007880c2c0c046403d001c0c011080e050069427152142c5800904400c1000000395203150f144a81070500200064898042e40f06003400405107401034106c0781d5030304244a12281c0c5118548080d9802034140d54080f074a4901003c0e110300540c082401442500d00b010000f001650060b140ca005103c3d103081c54500c018024441d86110700c040c03070104c3e03070345625101e01c8028a010042c030000002000c0c8081001e0a0255a150b4091032240d28180010321801d10104004021220103100c01d8803004c00c0000c1001120130082929500c10b00658815842d030304076810040c0b0310703170191130344c41902e850382d0528009802c03551078002007902001c80c51240894503204040081604054505001c0004004506800c41000b10002d4001e10b400c40740c0f0305e003100c03a16 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 43720040 1250 43718790 43718797
    0x609020705251a040b07150f0e030414060d05010b03041101020303100e0405011d0106090608070f0e04080d11030402090f0103110114040f0602010e06070f0503040b0903070b0406200301030503 84
    0x903d1051040803d000e1010710039040d500604442002d103540d400280c04d1007007402100d0507206400c181081200050007406002c1c1c4113070000310318000c41c00e0900708100300c0e100800c02d500c0c01d5040309052141c81101da9070b030300816000300801c1ca03c213540c80c10a424003140e100210450581035501c10020f10040c450001c02d090708461901405140545807880d003203014101500c4562068015074130003060511040d8449411200c800008000b035555841030701d40c54145c141305400a104c20350004000c0c009103602030b0f44d4014403416505240600348c400000071500c05d444003175031280d004800c00c42142000014030381c108544420380c180d15031440e603401c041c0407141545541040080c1010840d0145001c007a2006442c41c01180c4030440d4464500030700804540b1203140403031151a0100301030341d02034502c0041140ea0f603030712146141e540d61907070a0404406410802207210070068000482c0c2c0303d01c407503401541f281c0b40200386203405200003034a5000c0c816100780800020801000011f1001088 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 43721290 1250 43720040 43720049
    0x9180f0a050402010522060e03010908160309080303040f17280302070f1109010f06020d051303020612010305010501090209090612190605100e010506090904020f04060902070525 78
    0x4180341c1d80ba8030040b9094014910b100304120701815103a801d120003e440c42040d00c80564800d080316800308101820703501d00385030240010030100312503049160000b40c040100c60186c02c200104035610914070b0304e103030f00848041d03c2490a20980d80200080301c515008840c80c9045000d04014480590039420400c4007030342642042040c25646005009030151201e864200891b070308081c0d400d00b020030b0700a01c09035005100340d4070a00041118203169451000ba1000ca600504062100078802d5441d5844500303040c0b04007200620020069440f04010850341d0f200c2140c04000e03514503d010750a4520681054041c64014401c0410341d4070741e80349040c0d101d00100c41c400e00c4140950a0b00781054800c0242142c0c050b10340001d6401c0c084036810850082959002e0340d0ba2203aa641c0349410030040a000e80c6921040800008040f86131001042e40c1080c001846400820141d10014044034a60390001004e43d8003c80c5500c01c1c42401c0c842d140c8800c00c2580325243ca104c400140d5042049103024 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 43722540 1250 43721290 43721311
    0x703020606041a0d0305180604120b040f2a05061813140c070c060e0604090c020f060106020a050606090705030402061602041d061023040e0703030509180f 68
    0x240358290034116030b03000c42d02030084d256244800007810010420b911034610010034407240f018503441420820708031000c464004400001480c8940c1e500180404c02500540d001501013007640013060252000403c07090394179007001e40c0900e84806c80c0c0c480c0c140e00d9020038071941082c01407050001c0d549003516044c40c0200c407452160840100420000c0485d4035000c07003c05c14110401c41c0407007454008203e0640100d480c041201c0c2e41e6130303044a0b821403403c03003d0b4001605010401c0340d1000e6400c12500c0e0401c0d4015100b88000c00d0741003519000c000d0b401a00140e00455500b41482024041d0385d40000054801c1201c0e1700d130007407001d0000d03c4083c00080c0103810014005661034000b0f400b81d00296401482448801c6981c402001010540d4940d0501d90140c3d601080c1c103480c2081d038045c112440790320f143d0003007903082101d0070b2845030a83c0003a41054948005182c1010184032000c040c42c03080c2c031043c3e1641d00e242d042c0319460712000000c401508221040c402c580c6881c0c05043d0f441558402d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 43723790 1250 43722540 43722551
    0x9051b01050f0307020106050118061218020d0c09061a19020f012c0109020d03030c14030906040302070b07050c06090f04020304050609100c120b0303070507060e010e0402070302060604 81
    0x280129090300c1440048501e40b200030050204c5103506400a40441d2400d90700c0e003400280e0b1501004800b8030300e00c03400000c41e0801500401240058004100403c81d0301d041035500c0085401044543e200d2000c2214500300e440c10600070104544600005800381b2a01c0d11110700c1d244080c111684527980418016100b6181225040c5108001c0001e000040320001d0207a004004001400d07131081054410400034140c1004400301d805106500a581d00103004a9607050b098400390f0040c80c10600e07110800102e50750131040c512242c40118002d0408400038201c4d8505824001d05100704e0342c0010b000a0010030010700481e50025520701d1b10281150495503850a81000a01c1000c0f132007034058001c0d0011040200344100402c449200785854010303601615120000700b0221200c0c5030903c0f0110320581c400c0300007100e00383e0101441c00800303403c072880c14040745c48591411009900000014548a0210741c15580c4191920700340f400c15503056050500c10394000c3d40300c1800808850040d0381d500c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 43725040 1250 43723790 43723843
    0xb1201060602121e0a1d01030207050303040f060b060414100801030201080a0203090106050901080d030e210d09050105040b1605070f140106210302060f040c12080c060a09050c03010905 81
    0x22480c44051040c0f0307107603aa44003600348024202c111b85884200c4204d02e161303041d03107065009000700c481c0a135000010398a180e0360f503034400510740c4000f00282d40b003590741c95503012107849110042015008410074804014840b104005000030109040402c01c44131000420060740c121070840c2d0018079800c130158076a0303240c0d0b40c4180184210752025500507007502c00014511008035581f0720300c2d44155814804207017075403031082c0c1d610b05140c0c032400780c601000710b03911441001c3d0000c3c04141e0342074240412181240d880710350070346109031810b56000702c0001c280210b6250f41d4a060f1241212030504c40c3c1000381d19194444030a070b100340c1c00382c0002500c80130b800000714207621041c0640710003c0d0000c80c41c025490f00010031105010210f015100d42008900a4a42c50605601c15075010b5441403105041481b164014002414100c3d4406801d0240e0400c4000c14030031540b14450104000540c1e90340750a0151610309900301c05806a45403100e80c0d13000c2800451500c0c400454002c4000e07030b0f510302 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 43726290 1250 43725040 43725067
    0xb03090109060612060c0311180a0504090c2102060a0e0d0f0309090b030a02030307110a030c031101080105180402190b040b0c060705040609030b0c071202010b120106060212 76
    0x1048028652494040f01098080360024143d2859000341c0080003006160101a0100d07904000c03800a401420f1003581942070200301d605042c444081d0078041022369400214040d100750090132594000740d400103110f83d0301500d20789856160703e15200803c0c0220394010400e84d02c03400144c2001c0140d40001c030170098032403d64101c002070340050b0f54004c04e41c0a04001b403444406003e121195410008144a90b140005160401c00c0e0010003652070b1041594809421110003800642c00010068002002c5032244210074002d500441207035501d1200540014143c0700140c0201e403040c0e01110b0301c4541d0008591506a001c0d5055840d401102800b500310f40b4011080d81c803206420800050114080c980b01019011145540c170803101e464444880980d00c3e0f000d40d002d01c000186040c039041010449150020340c0004109000515042403034071001d10944104080c0b42c0544c0d143c0c0740c454194140400e0f0340c05035200c0c0c000204001424204000e41703d010114a005102c44040b442c100da2041 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 43727540 1250 43726290 43726301
    0xf040804030f060b13150909050f030c030904050604050708040b0601050906130302040e03030727030206041403060a050c120c210115090e0708071103030a091704030206040b030901 79
    0x10030085140002c0c01500d020300242c0000580306000f41c540d400705107035105070b9004e00214595440034034241681401000b0f401000c10000984041c8034100c1c01c880001001d000402c0c80800b440041d5980c0c0d00201d05100c00e8602c06006280114645410811095406403040ea04254048030402682d1a9600101d81078002d0940300740e8010780016080000d41401204041224401d035803d1050740f140e1b2032803948a000c00c030b991b400400c1c146c2c0344503c0004604810000180909190200d03160f459402040700c0e40c12070382041d0080c0814034810f081500d4200200c0707030302c07940c0390605010b0f901d041d169441c00d50160941400c102d0416002150070b0396017890039280b000310440f21040700d2008440e001d0001c40020312807550690348000d004070104c1e1140d42c1e004141c0c0c06001d0580306586500c1300450744400b00404a1f0204042d8141d9004076400910055000380c4013002c0200c0c50014600300702504082122600480c484100010030068640704103882c00c66001e4482c40e92240d039002c00d001d01408 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 43728790 1250 43727540 43727543
    0x6090f050709020408070914070c05010e0303040b18120d0c17151f0504050108190507081b040509040f0f05010f09030f0216150203070501060801020a0e0d0b0f04080403 74
    0x9008000c210b0801640c003900c121940c02045035038442d500c00040044a07200c80000140603180c0e0b00042050340185400c0e40080d11540002a01580018506003550001d90b4211201c000107000d00407240381c003440040e0560648006092410800103010f5058400c1d5614901d031603489681171f0700c4040c028454465041e00444c1107102c3341c0381014507000c00605000c1402d2055003d0180d2501050043d2800e40a403030064550b0b03440d1505280040d00d818200078042e02001c1800e10144181141c9401428000d0505450300f042c42d0414861038540804d0b220009518003205002c01c106542e00c0b451410f82098205a2904011360b09042c40d0900b42141c0001618640c2440c0300b0200da522903503c415600740c069a80d10302e0268007003d04a0702c611241c010360300125000b49040c403440030b40300707040510304446004403881c003030455aa260a44005502082c020795010860800c0c03140c0001080203d010202c41c064001d04a55460b13601c0804040d02d0742440041ca800024200442d607000c075000381d03 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 43730040 1250 43728790 43728793
    0x91303030c2307030314010b030a051305010e0604020a050d17130302030a030905030c01031a040b030c130605030c0103020406080106111e0313090501060509010e0303040e070c05070b030f0406090f05 87
    0x41c00b20a0416a40c00001c00b100080d10309002114800404000c40c0d061301e84100c4690b14640b14030603a08098100509094801c00408604034002a4248940c02c0f2881c130030b00c00741c5402d180030b00412420b4003480d0310082c0a0b0000c03010942c00030f003010059908a0744003803405601d903d0400151844180b40341c00007901889060780000600da00702010b20200d40003241140e4a083da01c200440c29108110068100d001070160490003030b01d00341e048451030950240c22200a088100001181501442102110a550742c0702c1406a81000d0018582a603003e00b81903113000d00c2c0c482c0c01055090b05202e02003c00000d0003400c590140700b4401c54400c002e0300e00300ca01560002c09092a102e911502a049079000c0400c40003840800c0c5001d001c0c100e800d161196814a10007100650b22032040c040040d515010802c070201d039805041d40000d00400d0349a072281d030303c8105464101e20b003040c0d98000c0b902100c4103004105000c405003400603401039110744045211801854002040700d00708200400c0d9 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 43731290 1250 43730040 43730087
    0x50903030f1b0d0503010f12120c06140c0a0305010806040506180a0204050c041707050a0b090409050a0c05100302070c140102010219180506090a030204090804091103070e091303030c 80
    0xf01c5602101440c162004050030b1300000381d55144181264405482c01400340c9100303d034142e05680541c024002080c068030700070810340001240c2141004040386c0302e50240c000807440018440d4544180d50140046000900c054207094940d40d030f4030240200010705160f041c48000c8074800d418440e0f5030308103034040c106000b203040040005c0d150b5005801098501500034480c411020360005e464402c560b800b814003100c0a003400f02a4a00360f01c45002e454001d80c07201e20100c00a00c04200840340103015509087c02a410300c403c0010710004c5001160405005220310b001052214807454104d5481600c0c9600c03e20380c010040c0c3c0640504801c04403400e403000e00a524894101c00301107070f0400341204541d1703241c0d12201044101c0c010303240c20301d40140d000b0000380010b0030301e640070801d002e0140b64503504007070780c2e000744100355800802c81c00010080070003804080d07134101029400000c4120340d1040c3c503103465a04050311349440c020180c10980c440c42c40b5000c041c05400300c02860b6481d401e50801 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 43732540 1250 43731290 43731313
    0x5100f0504020906010507120f0c0c0b031f03200d08031602060106030212060402030c12040f060609020c0c0d031803050a020a0609080a03030c0905090a0b0907050903030f1b 76
    0x301012101079005115070800a80258440e078201c440499101d03041d6416440d01030401c03182c10040405000506c8119145907001c9045074108800410807603023000c0c0d03a07140800200c8500501200c0820143c4901d110600001c2d16104c0d800b0000c0804002d0f604410341804001b41640c08047e202030041c0c4030000070300440e881c4a00e0700080c03e0046e6000c503003559903070b88800c808a10516120010112038500404c0c214030b0240c00444e08018000041030400d400100c00507900c0600f0b0b68125400d0640145501c200040d6002d96001051101d90460405000301c80c0c02e0740b1200c2080da8603200b0030507001190101406118180050038041d20051010b940b43c1c90304940da0340f40110146d00c0b48600807000a0030601c100d80620036140188081c1c100100301c1d41d401e80240680b141100c05100401c4c4010400d502c6288010348030350784030140402e60031081410301c5011080a0041403c1080400090307140380c41c0002100d1141080c0c405031503881c0f11940629075506d6407c040b11003a4010f4115020 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 43733790 1250 43732540 43732571
    0x1003090510090803090105060f010c060504020f0a06080a06140d03030f0905010609021206060301080a030c03050c0d09090b0a08070b090604050405090105041202010c081915090617070b0906070510 86
    0x5105e00c280b64001c0105445e01e0040007440c26000400c80e0010304007245500000b025500701e00d0300107101800c901c19581c0008009000300d03a503508644001110407081045080081c01000001d04400c40c6005000b9100804542c511818420140605840304600b8288468a501800610350408020004070b621103480101030b610a01c44c120584018001107640b91410200b1a230484051000410242d00c1650302900d240c10040c1064007030290522030000e40e10814070078442c0316441e5035182c024481c00d05a990080360203060100c1c0c05a03492050502183e14005048410b036958000200d0711a52402e00140032442a50016500035081400b84080d0020540203280035500c103080d03401d070745080104120308031200c05c042c01002800030004a0351881051085121814007604c0100d00b05001c031a500321009075070f034003d00510355100340c2008000c408441b100b43c0004018042c0c12450b150070622907140c054031940f54801c000c0000c00c04104001080980344007070290406102c071500015041 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 43735040 1250 43733790 43733797
    0xe0102040501030f050c030106140c1510090504030207050103050a09060e01050601080609040b071b0210020709150b0403080a02070807090902181311040e0a0c0801180210030905100908 81
    0x5001c44d04052482c00c1c941c1032401403910403000080441d055078030380034003203071f01085800030703030030440c00c20422503602d80801d00c06411100030401807001241000d1090200c4803500d030707200340302d004d20340024400000e41c0031a10a00f21072003440c020840381c0750901803000401da074002c0207110514000c80d21400e4441074100510440342601c0302c0800e503842d4800c2c0070940c50220b0b4010850340055000400c82405031203901d50312100c9101e518600d00381039000c00d009588800b6a040540e1213160100040f8240f4083c0d00014150344003414880303440c00d1203001c0c05008901004040003404a1010f151610801c100d03801410350b40220743c05103a0b07541c4458020481200d0981c0100c903a21a400c075440035640c5814012103d00b2150450b00001e601c1d00340c0c01c190300b02121030b40240c1f107141042d040301041095821040c01001c403003206a2030117a0f55401c51380c1242000f8250901440204056983c140c1c0c000080040d070704005c6030351b070583d01e8800d08051902c440000c8147c54030005005104021014 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 43736290 1250 43735040 43735049
    0x1120209090a0e10230106030603020a150c0218161d0f0d06020307121401050904020d0609050f010c0909050405072904030809031014190603050303250c02030d0f120e010204 76
    0x30804036981f51700c011030540c0c10500020390804c1001f4010010890350390030281004400f45000c800041050b400039880d200c2401c403001002e00e0590901c80740c00007600c42096038040f0340c10100005117003108900400760960105903c9070b0b08140c07a000b400e0725801401d034400b0b64012011940c81c40c0181014081d200320501c900d0072145410308014600441440050580f1401807400d48144d841c2d600300301c1c0200016000300c8013551552801000103108128004441020030004550031304e110308000c2a1200c2c0d41e200381d01c0e8506103401e10004c118081102c805036141200b14860190800281c1a54114207041902030140000303000010b1040742009085064800c40c2030315401000f41415005482003030302d9092042280d0f1000c0384e80b039541c0500d1402300c0c8085507404a0030959035110b25045802c2100c0ca080765806440e0313140403e1040c08185200381505e800c1240c84046076402180e6266810800441441802c010018000b40030741c2900a540600007800d21116010201050203900240f04 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 43737540 1250 43736290 43736351
    0x5010806090105100b0a0e090a0515030c0d03030506011107030305070b0906070e040b1309061d120d0203060a05030d030903030c050c1207020f0604090501030201120209090a0e10 78
    0x40307892944180540790140c3c601d491000f50550504035942060380c40407084900344400e0202c002d00710780724283d8592288050301e800291920b0100041c070352401c80144007520030b40051014101c01e03500d181220000c0c3d80c06150008250b030b04e5800580e460351003008605540d210f002e0001040651000003440352604c41c120090080d00d035015125950b80041e12550b000c90103102c80071540d4181755012805044004100c465a038840c40c86540403035400140544915480b0300301d0a070750304522001c4a02a1140000501c03458880c6004402103008000c403042c180c0d900000030504a555002000307000e007800806813034600d008200058004c1101032811400700742454804208580282e00380d4602c907030840d000d8110781d015520a07111541c08402c2c102d900080402400760540c0f07442010708094052040c000071594110300014106078182c051082500380100310b012995201c5004142d04402c0303c042c0030031141124400c480c02d2906c0f06d0128160b0310f14103c46a805174110101380c1c0540c180400 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 43738790 1250 43737540 43737553
    0xb0403081c090f15060b0408010b040b0604030201020a060f090206030901020a031a03250803030907030302120301050a0b0703020a0204020a030204060305150325080a0c05010e09240105070c0603050108 88
    0x8032000d503115080007602e90440e0303507001e00100305044141d0111205001001403803a0300d07080c6c20109a04190031280c1c40b60f6688640e201142828030642c01405022510f0500b05072071640001e54130180c13001c00501460325940345004110380303508070024440d402800e0350380300e01e0402da5842c001d400400040340000d003000b81b240c040c5203041c505407101032005400780800c13550480002007948844004910351080340507001451070014800f441c00784c002d1101401a03189507050003450a0804034503c2a08041000100141d80e0390502c0141251142c0800720b44460311414140e0404040090281d086070000032502000d0f50315900034826620b140d01c040040740c592000c0e40784006c0031144001e416901c007102500c90b81c4518032150400e02045114252640e8480c20b0017430a107016007030700f00c0390b00400c0c0300107021940c0c00503a0030704e8200301a207404543c4e2074592041c002d1446403035a1040346131030055001540e41d20a00032244415000b03440074410590b42d0800a004100900c40c20035980180f0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 43740040 1250 43738790 43738837
    0xf0605160e040903051b0a0b1503070602070803040501030f0207061e1409060f09070f060807030509030705070b030601020a080c0a060b0d0809151603030b04150303020303130602040b040308 83
    0x303104910320141c145d580c50303040c510040080d03038010b1482e400e02401489079140c1702c000034244004e901e21400c805030b000c0301c05019070001e040c5815950f400c04020754006000c20310400600000b501c088410901e03020072100c10a105500c002d106803400030301030600300b07440c0d1a0081d4644500c40b00c0c10f40b00d1981004203c030500b0400c040c420080c0c1c2d042c51560021008180020b40c5508a950013420203400d560344141c1d00c0685070400101c540c071000c080b4407000c040100b00341d054460150f001c41204051441d10000750303a41d030b440344814020140c41c24404800708982da44200503060100d0790007c0069035074840d141e903031a903a072299841110241d0520b4400740386401c10a03041291380d603214415509048040e000c2010040c0540200180402c0511a0701610a143c01514001c18020f0b2000103030f401b040700c24042a124240e03094032550481217000c0002a40c0042125408003885104103010702c81c629000e0041d00c03540d8403250b40f60a0205010007440442001400b101e00d55861211144010 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 43741290 1250 43740040 43740049
    0x50901111e0d1b08030c09060403030c02040501050a03020d030c060204090c0c05060c1303080d1e090201020724080a020405151801030908161401061d0604021e070f0605160e 76
    0xb141581c01481800f03901580004410030007540d00802071b0001c6504121001021840c242c015900580003d40c820340c60b2001e5040c07500c50300f8058041610030514030b90a54003c2410b2110b442d030002d007008030b02d400342024000d8941c1542d021742940130061082e903031030100c02084000d4942060f901e41c0200e20104041d0690f140440348984c503151004002180740d41c8840c59150001c204000c500d5481d00c0c0341c40c2052142c440f030282172314400c00f00015a021070740002494032045812540400c45441310841e5a55204800a1842c2401d4604881596a01c80c4410301030701030b6074005504007003e100960b11408042d0b000e88a10800940710502ca8801d0380c00440a646242c0320280c00c19400301711600300c00b29603462030341d003680c056085d01e810889090441800c44441c1d50003c00a00b20380c1d580d4a29520b0400e4079280c0004044a0a5041901403842d1444000038075401d00d15030100041c001d0300304412400140c030b000e0380280041106181068401d0003691241076200c0010361629050880c40c5403 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 43742540 1250 43741290 43741307
    0xb0723090f15040e0f0f180303060f01030603020303070804031a070f030c171023030d080603100e070f1d01050415080109050304080607020304060f050901111e0d 71
    0xc1c01000070101c16428000c11885100c41860100320070800440d0000e40c00b03429a010300c0b03c100d08070f9518034240418041110015041e201c9481c103d107041035143c1e400100f0340b0f41002d02200e2442c040400f041c01607000b01180d5000941501002c07c50300184900400a40107c81c01050984145001c0c07500c1d00d05011000c07070340e40300807486034055400041d20179800301c0110109810300d10000708402880da2640301080b2400c14203011030820510070110100f41004200e8500700000205408001c0001e49403030004e8403541c10002120000b41240d50100301d9114510100c100c200000d03284800380703644918503400303034098509043d40c00140d5040c114a1a904624501001540d140d00b4402040003034046402c13446d0340c01080c000041054003080c40703540d406a00c5030000f10b60b02da140c40718450400c10000c0400c800d54206010801007560461252625104d080ca056940e0382c2e05007005940702d030003081c4202505c0c4140d07142c010100c20001034074001e84225108840401061a02c22201d814 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 43743790 1250 43742540 43742557
    0x604032024040e041a1006030c02030a050f030a18030201050403080612150606041701020418110a080910050403080601110304060e0d0c171005060d020109030206160b0723 75
    0x4104102c108500c4032111281504039100b001d112400822026210503103407001d480020044182d48000c00049416119400d152041b03030001c0c40c10b003032514101802ca4001c920025101110000001d800070584e680311503010405a142020800300300c0c1002802000c0448044001c1601000480c110f89400a14003184204910083c0300d440c2e40c410000603000c4024208076001328041c000070901c0b440035045050100039601c00162a0b61600003500c0140c000e030600044e0746803501c00320503050290030b0100d4440190909044e10301e51111012a464103c180200100c1d103850030007404201a441482d05001c1c0e402681d8102e4185001e55613a501e078400c5100d8007010030042034082c0da8071300f0100790302a4894000c0b0040810580d54266040e80490880c0341c401c1c0320f80080c0f134000c1482002b48034498108500742c41c00000d001c11039002a1440c40b0900010f44070348004602070101500900c2103100d007a500083c928020b00f00302e0400750000580030480c01100320001c0c00e0000c0406917900361150381 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 43745040 1250 43743790 43743859
    0x22050402121303020c0603090a0b060409020d080a2105010608160e0d0201020f010905030a0906020d02060c0d09020301090b0601030f091707150c05030106090501020a0b06090606040320 81
    0x2a142c0024003809119404011400e44c09000110051941d5500c06544036005000142c4403101c0607213003140b140d10005041d244100e10309600040540c880001c1c41d0200740d07200345001da45d0145040c0566624032003c0304141c55990810031100003880c650030440c12501c2d69200e511030b07915001d0303062400c3c106079000c4000140c0d03a01c010002901c0c1410b1410351190040c01614003410325000854290744403400152580d0780f001401c0e074413171540900880010025840540410424807000940301d09000d052110090070201d00101c075000c1c2ca034480c02101ea4000c0003041198003d151621458808890060200b86000310315038125040740503440b409035100c8212580d80b610341e0300b0002d41d9009102c0690741d405005149002d9102c40e4805c2c03a24580981e102c00d41c4070f602d0710f0030061030711040350081070442d04083d000354000740400407555000f090458503102c80759580c0740440c1c078030300441d400a00000d99903104030001241080b40c0d4401d000e014bc4540c105c2130021010710100150f0243c1481d00d6 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 43746290 1250 43745040 43745077
    0x9060b0f0f04020a0c080d020a020d080c0a08150d0c061d06071203110301030c1e030b0a0c0e040c03060e060303040602060103030305070c021e01030e06010b070f020a050622050402 79
    0x701d14081c1d0081840c181141000780c81140240c481036240e401003000d40075040e90000c0c0e401145030301000640c0003401d0514209626282c000701e1001300d40a00c600410904c48400c000c240b00c0c004c5910380c01e0400e100944070031011481401e0610907001a0706c00c540101e038041c100b140c0c0106400e40305d074122220242145107448111f6a4010883c903103013928800f092380d290260014140c0e1000258005e600403440518100c4c20020382d80341005040104c0807903d680a1400c20000b40ca140301c89600403864400002c0030442064241c81d865000d10030036510034940384911003a0b5800da4481c1381941d0341000c0202d015a2170030b081c95075922540c003410b8090390041c0010000039210342c006c0c5074403600c103160280310181c85601003414480f141e4071100400c0c090105000c915603161241c00003403a400c50047c40035514000c00c1c042c1c1c0d4810200050100030b010020b0400399100d81101000400000d0091940d036101820120240071103598401c4004080f00070000b0340c0e28040c0281d50308240c4030390003030f0007 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 43747540 1250 43746290 43746319
    0x9060b120c07020d08040305060702031602121c02030a0e030a0b19061805090606030d0e01181505041d04030210021602041e2405220c020109060b0f 65
    0xa0000510481c401542001180c006859595042c141540714114854071281075190140c00d00200a056004541c07060100d8070881d280c0c09403010081e90140d48040b503510368821503a080804c2000100d201c4200d1403425040190b0000041200010700d0341d03180221362100040648400307480b98050a1a0741007800720351124000702003010041079801d40003441aa4814a20708900b4151200482107641c17041080032410007032080a40c090340850141080000f0008054230300c401d441c501a0400007940044251240c45090786405000c9005140b00c1e101800d00300100264050300425800040000c8180700301d1001c04440d9005507810b4015002460340a503040000b50002081d42a91010101400700582c442d4824544a0308480f201d407514580300f070000c0019a824409100c00c03620010342d403000303140d07110f21030300c070641d4011103450054001035070706c1c80034111020015201d41403500c00190b02107501540165866403041000b031080404050170404aaa007102c81140c1041209480a0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 43748790 1250 43747540 43747567
    0x1020d0e100311070c1e0b030f040b06030102090a0e0403020c0105120f0703091a040c050616020609030f120c0d050c0607200a0c0905061507110d14061009060b 70
    0x1000f0004507800b0904105450f143c2e01d001140d258401080708004540c181d450a85240340ca030060003000740b50700c1c41c0d070904807400048060006c0c03010b0940064603000c1401d42d50700303404440c04140001e041c090020f1312010b030304c068114151000c5000d4861105a101d076540200251102e4050030a001c95903983c80942000c0150001810a0101950f60035a44001848030704c801146007001d2201950f645410b19020303804180940219115640a221148641c10224558005035030f0503140141c49102140200346865080d00c0004c86a00503a000d030002103040001405519400c5c2003102c45030044580140c0e07440c4980c90002d2004d401c1000000d001502070040e00b00d0700c4a420000c40d051041c0e4031071013410f00b000c5000807103105a030180104916106401440d4101d08100d034549000d4144c204504030311f00c14110020301c0c2c950b0b07620f103000c1596500c071000c140640d00b01403049400c3c07000b02403450702d420b011194540070204100c00030a5484007071081c034041d00d8580200525101da01070504 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 43750040 1250 43748790 43748801
    0xc06040e07020a14030c0105010b0c0c040f090507060c110f0a0b030403020709110c0c0a15080916120201031506050406140d0f150905041110050915040501020d0e1003 73
    0x201944240350070340d000a80140740320f1042413a03841c043c5803190503041ca042c1c00d4580c1a803007503a03914014400c0071150340002c01d10f02c1034850111000908003c030310140384082c1580d034401a00900544800150140d0060700c0d4800c040e01c039508600000000404001e02c0e40304a26503aa0001640c50060001d203403080000d40d04036010b4011216000e0380d6485c0c1c201945d41c940c0340c0c800403000c046860300307450100300001040c491044a44041040c1099001c071000f18980c841d9604011905c0c01203440441c003804040c0002a010b00e0743c8040740e44a0207c04035040b803d082c100d0000b854003031400500740c10312102c40d003500c1666607080c1c81c01c1d10707041003140d079651200d0300364094a00070010414011041d114168034650700c0c1d00c002c0f44a84dc4501000040c44880d0320800c1340e50304120402000900f10214021a80c2c8102c901d0902856a00000c40f10341c060012425000f03a4410300c02c1c462490f0300b101030011104241d00715110440603240845400810600c0c9079005400410106891070003078014 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 43751290 1250 43750040 43750051
    0xb0301180504060b030d030e07060c050d0507020607060f05040213090b04031d04180b01060f12110c010203070309050f0109170306041424010e100f0912060509010c020c06040e 77
    0x1113030502810000034288404500814042640c0300c1103ca445242404108014100303800c2000c010882600c030180c40b08100c21003502000000506201150381301000d0b15560b5800000401000c1c03100c01c3c5400c0185020b031026449a105401030312442c0c542d900540c081e0aa1080d0310030300d591030380d40d0141c5000242c0d49a140c854940090041119260b80c402d03802c00f041c240700c12100b40710403030428101c0c000045c0c120b8000c00605250481c044c0e904a84004506000ca00e000107424030150024041d50044521000c0d40307500010038050500e0b07058000d00041e9008000355160b007150101001c4c04c8565400008105006104268008034001000b44d40e02510180000c201c40400b820121224a0100e51032450201c680c40e211008040c43c0400b4107103000207080030b01000b00754100082c840d692810350702d004c0012011000309220b2142030858024110b040c0c41905c0c10070380340303001006050103e6030144190319100d00254410710003c1c4140e45882c01034901842d0a0401504c00ca181c54000c01 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 43752540 1250 43751290 43751303
    0x70210090812030402040c030b090f0603010207120201020a090501030c1403040c0e07180909020a030609060b1504030212070f0e0a1103040b0604050f040203100c11030d020307090b0301180504 84
    0x100141501060021074031202d1038400385070340e80c5001e104100442e245a07012000b0545001c18200e0ba0741c94a2a40e150041700248400e0301580d01c1400281c06071041c210024250007080d4056035202d60150041e048940294641200094413030f40110211004500b10303400141c8089140008407018100442e0801d02400c1c03009103554866481050060064070041d0000b01c0f19890a02c1e101c0c50317280b40c0f10261a0296061148809940011307500c01142e000c042c00c80c0c1da941c8002000c0000341d070b20600d03200304040c003428a442a0780b580784404c0d401c0ba100690144d40305507000511840d0120346a0152032990f0b501c0844242050b0301c9000950004120304c1030705039210088801c201d610341c040e5100720301c1911401840c1c070317129090100f80c40d40070b0184c511400600d000e010041c4e03008603a00500240100b0000b030b80002280c5c00b210741e43e00c10304680a40c1d0000184511084e40160015403041001d80c075240c520070740d29081e40310a48000d02c2a01c1c004080c2456040307590115800031074102d0700411 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 43753790 1250 43752540 43752557
    0xb04020f0301080d090b03060a030206031504061502100b03060a0b060d0204030f0c090e0d0f0c020a03080a0201050603030c0d0e040f0212010905060102033408030c03090709020f070210 81
    0x96038105a52080e00046000d9200d80c0300e10300f60540c41070410707014010202100c2d00b14148880451800c00541c00001e108020110005220501d00058030a4590000744144812980c562440e072180481400c03410050013000402c14041da10307401341102100002d40203096943e12003000100401500c103201d40d2105003080081e541e807180d07001400195028101420a54030b40e440c000404400b15400f884140e030a26800c054209000308041e520542a8140b0007505a070040c0304450b440804c3c28003d41c4652040710100c10300c480345010700b03501c61240e0020462a01c540c800c02d0b030749018142c01d400791035106602ca061514410a2580e0038114090000320b12501106031000590304012041300c0c14008410040206d420a800b90603000207081c009945031080420b1281400300b01e0b0404881000e464040c8004c4034102c00b000e80c000140c11104c3c4a84030708001d986200301d07500c19219030b01c10f489008030211300e40b09036200312a8400d0a11105070b181104d16428450000e2440f00514103200350b16 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 43755040 1250 43753790 43753807
    0x212030c1207050301051804030c0201110f030f0705010e01050405070603020c070e07020a03020c01180b0c070e16030c141209071e06121107080325030e0c1002030d0b0402 75
    0x705205010704025156584c407581400c0610142c00300300402030b60900b50840c18070000c65044616050120380a29144022a20901085280c44050026190706200c0024074030f402c2d03030743e410213000000c0c0b0440090000850340165075007600c0d000d54000d4605d410405003000030b107000740d008000c00c030252004e4840d02030f911001c080f0220411200d20b40503800000c280e004041e41030124144d10882400d12421083d120494032040307042d14011020105d80020f42d0b4601400d0401001c2c0003030400040010903494a6122030300844150805200400e082181b801c4541d4010200030b0304941d0414080f5040c88400500004400400703014105540030300d01c0040f581c20407006180d42d038032002c0d0038200261464401d0003402c6000a207011242c03145400e00d241e680300d003241c00f03c0d101303070740c101081c0c6450303444e02103100d60082015101d05040b24060704024201c5a010b4010203581d41c0c001c0d0940c3d01101c242c10901075100044c20f032840042c0c00410107600740c41100d500107080d0346400741005042c503000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 43756290 1250 43755040 43755067
    0x316050a0b13050609010c0504120501020d05071e02010501120305070f0212031804060815040201051b0705040606020a0b061e060706020d0507110705040207080f0a080402090907060212030c 83
    0x3902c00b0160700c0d044040e00b03414000e0410802e0380107a5680020048282c2c0c411009045004d01c0c010300039404003170901c81051040c01d40544002d4402d40004004a05040c0009080c8116001c0c090340c040c400c4c0003400c5603503401031003a01c0c1269a00440d6104400c540d036000c071515030007481c00b02c640c0c520301d2003c1009030f11072154001701030980000441c0d45880c0709800198a05407101d40030b119505015040c0a48103000c190780000001c208078041c0c40341c80d28401030782e26010351310780690b010284540b01d0160500008401040302c80a0b1010001551101401c0f611044610400b42510021001047c4507050010103282c071350000030410180b21410f240054401da2000300161031083c1c0106000440e0002c5109281d004541030500c1448290001c1c00107840b4149442407a12440d808582c202c00d001c0070f0310899040d4561500c2c4550b03203140001c8041c0c130040c4280c0e41039006001c400001000f403000040ca220a4030f822350001d0450fa0720444000b0742c1c9074401400d041c0c40f09801d0120180b4980d4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 43757540 1250 43756290 43756313
    0xd020a090e0c040f060302010e0402070606230109060305010e130c120614060d0209010b1e0a050304052a091305010606020a03020d090e0a0e0708030d1e0e0316050a 72
    0xda00c0c01400100b08102c1c100400e40321442505006035140c498108010b0f81c0040c00c41041640a841c00f41e1201814200b04000f0040365000012001004104c00381c940305105d2503d904000980341d540d816512000d084003110024002c4000c4405810f000c02d1103100c07489800025948960107002071300c0d8860300c84a0114030282411241d0340d48446988039201120803021364040c400355000881441d81c2e0f00003c10305001885040820030f00000c0010008245800404003181c44600641c1e40e020400382c001d206920480f025071f201d02079013008440c1c003140d00310f24001840340301205c608410140401c00460400140090307201d900c0e0805800000307a805e00681005001940282c45000c1482c100a828170500403240020000b400c4024480d40503092401500712800c410b00141c02c200311f264a03454220250040740540c4800b2500d0081c1c0e10b0b107a0810103c0320b00701d82c90348581011460070b4030251201c074052182550028081c0d100081110520782141e60701034011100302d030507030b0341704c2406110 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 43758790 1250 43757540 43757561
    0x280605040302090f04050d081b04230d03050a030e0109060e0f0609030307051206060904110d0c021207060203130f050109030e060a08040b18070e060a05010807020601050d020a09 78
    0x11404034041003945051824542c0c014090100ca4440f450190f4070151580381110811043c407d4800c08903000003017044402e255402d400820b1a6195101c0b2400889030f03184800c01000b01c440c3c0340440c545c0d803c1c100404620303a0b5142d15003609014040c0c1098001e490226400b0060359600c845d6500031031010701032501d6002224001d4914105000d5560741072080080c810303a4649e2042050250b0103501c1802c6410142c00d51240845c0c40d01d0751000150740c5e03c144030856178081d0a180b030340b1003c0c2040c54014200316480400c05c20101d180c000707040e80c580404c8014021102001d02506020036500e80045500c140c003040040c120940607514051422621441074600760b56801d40038080640104103581c020b17504565450030041e490000421801c4000d2005001c2c01c10200403503070b60038a8100c1c080c120080c60003960107c507261030748060003040442d80c6a100380040800000c0e69401485998000c3d0000c0e405081c80780e00300b00620401d0200c002d02260000c080540002c0e000d20a40708155504 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 43760040 1250 43758790 43758797
    0x7050f0d02040611060c070609020a03060c0908060112030801090507030905030f03040318030203030304030f0302090a030303090c0b0309190203031308010506010305010905311a01060f0912022806 86
    0x32400c1440c02406105030b0504c0640c00c0c2e1001c014480802c941400740e601490703001501141500c514404142021180ea06c010b180710b003000030241d4050b8001c040300b0261002401202d0190782d0310034494008415017100500407461802c014801224260801903011006080c003107000c003a41d0b0b42e40c03481e541c480a41c03140780c0710010091008041e07100c141d115951800f030400040c03003411600040d46a1202810060070b03c2080c0300d0000ca241c0c081c0d0107403080c014004245040e01540d904024010740f602c4242101e82100304080070800110100540b40600c102d40001c14903891816144042d10303100100580e850b200503c481542c6000c403a20030b4028001900c0085868200b440001d425a40182c000307050540c01d0408010801e500d92841091010b0024200700d407002101c1025080402440005019007110780f0881c1c451040b050019412221540e4070750441c0320912004481003030785401024024141d0f00344140161505201420100c02580f40b82c1c0c41c000780003592288401c0300c0b030b408034020 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 43761290 1250 43760040 43760047
    0x6050403050d021f0903020709020c0a050105010504050c03011203050405060301090c02011812121503030c0201080c04050307051003020d050907080f0a080f0309030c010504110a050102190b07050f0d02 88
    0x1c10209001030300300310b419400100360016000071810015034500000d180d046039a010740c0002c1c18405c108500040c400080c0c11560390f21841c1041e62101d1900d00c050b034481d0b0a020000071581014820244640751580c005411642492030700e00201c58107038000e40070441e09200c0403a4650380e1100450081c10441d1002440b5045640c0107800e68050749203403481c900900c1020800b01c2c0c0c00041684c40c4104914201b1749220344260703c02c0041c284c01090004144071908044201600402c0d00c2003240d00236212380601e5035803003400344000d01c29400349a82540040c0300400c10743c00d18081c43c2c10120801d040241c140712807568018200d401c100c0d604005a03110040c1002400410301031203c1c00d0700103c02a0032100c5c00c5498a4815210f001c0180410000000004407124014003d07070b105e00f11040c2c02440a810a030030301c009041040102540704081300340c8002469030000501500181e007003c4036402d0050705448000240000a0100d42800380c20000003101038800e10090001078000d81d00141c8 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 43762540 1250 43761290 43761293
    0xb0d0c03050903091305070504080a0b010f0509040510020702061c0504030908070614030403030605030d0210050f0106021506010207090608100e06061c020d12080f25110a080406050403 81
    0x41d20310181800800b50020007001c20a43c6881d10410300c0204080d20125158503160012241482182c0c007103181c90140c1c00c203c00800c181102c00034100c9403044040000c064442c0304101b14590f0640c2c2c0103066a0102e450001158001c0d000f804080b80010700b0035040100c80c0910b1541d405200340220000b59840c01084205070b041051000075240c918010b04950303082210141600d4120303484480c1202c1d02000050030140f1a8001902a00025055076003030045210080e41e51488200807151681c2480000b401301d1a0884082d412a007055004000c140840e20304003010300b801901d024114011104049290652030040400411294000700303243d84032040c01070121501000c1c0000542c010100740605990380c000c0e9010030494400c00325240c20654400a2880004c0c642c0007000500207907000a2203a4200300c07200e10590481b42402c0c069900c0c0340c90500d043c0750001c6e04a0725440c20609502806110703041007000d40e04404d08980380c1c0788050b2103141c2d440e000b07036120200240001030300f0700 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 43763790 1250 43762540 43762547
    0x20607140d050f1803030c01110a0e04181b0308040f06021603050a03110703150207020f0108270a020901030f05100e0a0b04031e02160605090d06020903070b0d0c 71
    0x40000c0007460720a0401038000d0312081d03548101203400010130a49942c00c0580c0ea0144102e440001c21a8001c110394006003c5030f4001d40c0014641d0000304101800780f1003a8180b6004041c408060307012484002902591014220001c0c42e05804015903002d0000c8001682c072030080000d0702d0003140c3c41c0c03006880c0607402850300240181546180001d11402c00021304001a0700700100d42c1400c0000303c8004440745c0c02c0c544030b00340d030003d04155a0007020000768119a802004074070b000b900d908003100003281c01503c1c00d203070580d00300581101c1c4540702a4825220307040c2c82410901d000940d00c40c6c00c2940c00280c00041c0c01e070020345070b00407044154001c1144c1080b00c1d10305070005c0f44e41804142014080103807600d0040c0000341000c602d0200007000c152003081d100d030b2080042d01d0036050b56600204c00950f01c89100e51010000101e0400224000b03000b08207452131400c1c000c00d0200c00590716590070000c0e4001600b15500b500c62428003198209401c005040b00c031520002c0061041407012004 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 43765040 1250 43763790 43763803
    0x60b03070f0b03010303030c1101090609020f01020d08010618050423011a03010306020a0c051b01030f020c1e0106030b0708040506070c0b061e0d050102130b09010504090509010902060714 82
    0x7080c802011034200005002501500c2c1100d0b0142000154040518402e0301c0e000d007241c41c6c003004d035480c01b41c60404100d03041c0d00c030304071040c000c1e1001c902400201c0010380c0d540c00d40303482d0400403412007001040901d11502551030340043c8405c40300c8600c0d64a5000c80c060b0b0f08480d51a01083c025502c920384c085480350ba2090040003201d0740c0b070f060341c400200000050f21042c00050102270b00045e401c68601d000d045041e0042e50b124044400b10742e250740100300401c0016180f1030001e820026203c504107068000d40352111003100113008144603001400d10f034003064807003a560a54a0b44800800b00c0c01e04a0071a12600007074a500b1003a15003072500d14200000146a0070500103500c080d20041140140046d50010099503d480c0030882c4c50091a1f8545000c4c1c070043e1300c400c50320880700407c001074014003462441c45000c60a0280c55520060036402012030080c00a203050000300840e0202d030f085036401c0704403000001228111174002c5096507009035003c2d01d04a5640d10b600301c0104080199 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 43766290 1250 43765040 43765049
    0x40611190306090b15070605040804050a0b071101030c02150907080105090d020c0a060c061d03031501081003031710080d090510030c080a0b0307120b0402090c0a050403031d0a03060b0307 82
    0x10300c00105c205082c016004040000c0c10203540d41c0e000030101b00784d03803081b600030b080010300000d80141d40d103910800503072014a0440319030036810321711401c40d4000c1c012071950b18956006030041c0341e8031180d5100d6035030001f080c40610f03100d0b104001035100700070320803a405821200c02421841c90080340c040e203030a040c03030352480c05413064460401c40250722015548625034400b40c041441c034000320041c0224600c42801d00c246001c004184450007210801c220000700003038071881c040d9692016114401c800602c0054041007900e88a82070281c514501c140d40519040c00d101c00058441407840d160840c0d0048240c04590194002c0c070040c03070b040840c000f10491614041c001d141c10765070010030301d05003d004206240c0c2c440c8800802940d090290801401c1c5000d0441b403124243e00740700b0400e034004c0d102680100904001b15036022181e000b1500462801e0f103c083c6003916580d01200c000035483e039007903030000341e00e00c2c03507070496840850f00d20095008510204448603d4410141400c0941e0300 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 43767540 1250 43766290 43766299
    0x106050a1706070309140d05030a0b0a1406030613110d06140d1e02060f07110d0b04120e060a09150c11040b01090302060304050714010e09040611190306090b 69
    0x61404007500014007503034011828078000c5190300d418584249900d090345004c00c000d0044a01d400351703e42c1e00001652203489450310602a4940c80f0050088544040c003410080242103a50004130b801c0c02e80085030440c1025200710506520302da1244102d94a01e0990301408000003075203040d41846000701d02c040e20505088541c01c9000c000002d0840300c0082c0001c2441072111424000e958019605011054000d4a200d03039450484500d600c95a009803022120a1000340c03100406040051600c1c80c000c1d4040340040c529219511001c681d916501050340170003600baa42882030f502e440024100c07100003929880c2d1024145820864405600c400c0502000110410840801d840c0041c40c1c00340041982c00180c1110410300403030703003941c09810103900910008284030030024002500402c5503c0c2c5800700c0c004d07203c144c004442501050b10700e41c2d0b205008001060101da070951001c124045452546880c00011a50740c0d511092000e100381c0100b90340d40e00c01c0001b8034640c0921804d1a2088a = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 43768790 1250 43767540 43767569
    0x3070e040b0d020108061f02010501170c01020a03180b190801080c06221203050d0515012010050a020901080903090d031209020a091e0605030304151707020106050a 72
    0x70041a00d0440c1444042d0400030303060302045180d1070350301c0d82e515060380b4900c4003650f28083e0900a80030705001c0c403a0702114030381581401084100401c101c0c1c10284160301410b06000c240d102100e01c0c61242e0103078107400c0034001d4001a008000340050402c2c0005140b000100d29030b440c0c01509541d0141d10440e02600305a190020315620031045543c07030700c18001c1a40d1000044200b04c0b0194156402a480f041c0340c0b440c1e514241a0803201601c054080c0103010300c86642e0b1a9440c002100740070100c640407030004941d42c200b44564000307489000b007204044681c5001b1a400304416035000ba20884000c0f0390006030443ca5591010083e42c3c8031814000035071034030b80007001003003100b81c2c0147c0160400c48902c500200a04c265008060351540045c0741c280d9682d184d4800c800102034003110b110300101c550b04102e100c2d1886028150440d400200690b040c1807400b0080307044001102494820480000c0100748080105420103020b00101e41c0001040c0e8201418000360705196002030300050b0070305 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 43770040 1250 43768790 43768811
    0x6090e0105060303030a020a020106050918060c09030703020d03020a0f030801050a0905040f02060306011e02010507030c020a030e06030603150f0103290103032a0302100b0406031707111503070e04 86
    0x3c176600810070240050765948071083c01c034018041c3d40c01c44c6510011007428004484102000c03c5912034962003601e419495a0a4001081c400d0a07031007509134016580410240c6004c00c00540980c0c000e0060720242002e03681e90850904000030b0480100b9604801848107007040001200902181d40d41000fa0341003d40359a021040d1070f0800034403441000000601701d9204184800d80340d13070080400a82c080c800d81c00603028141c00c0f10307400006032511503c3d902c800d04c0010b6802156426071549044281503c09000449c0d00050400f81c0604c40c4500700e402c6205410580c0d441420105000b10865055181420903031107010244444458910030f540d403402d04014000741180d9160400303003104210b07941a46c2e415070000c0b26540c0c0a901d00c000c1c50040c95000308111164228107282045074003000000c00080710082c1c00082c0910201340c0c0c2c941404c05000b0b005141c0c1d24014143c01070300e1020f41000540c0a0203900024903428004814441c4407904070b11340b00d0602108880501405511 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 43771290 1250 43770040 43770043
    0x105071808151003020604060e010f0c0803060411091507050c04050705030c03041106030903031602031303060b06090a0f08060604020405061603030b090702010903020f0a0b0112060f020d06090e01050603 89
    0x500906485148002080035103d881c000400250f6000e03000c1e94459030b580b1809460400b583d820303980441e044134000401c891040144d035410f03a501c9104036045490310303c18400107048680a801000c603041084110640c0c0354040d044900d0030f80b05990751707104410f00e01203042400c0396444bd4091801c00f400d00c210340d90890700340c6e50b100d42842101901c9070340701d040666075070001813629074000344000709010003118084000c1d13120f20070700030040c08d4806c0302c02412030b540c0c4500c1a244484141d0100c05000013425a04100c035018401000a030030044544000b85040b20594458020000310203000c2004810500417694840da040f501103080c03a10b84000300c3d1461050b6190050b0100360313010312400305402a4084602d0b090082c00001a9281c8000080d00800c50024190003501c0344101e06c3c403014000052060002e0740c04640e8034541d9281c0030390021b581c20501e40031180a40ca076402c11820602c40d1003e40f108500118000c900285403540540441d16025007419075039040000308500c9440 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 43772540 1250 43771290 43771303
    0x11040608061221030105030606030d0516050a021302130b0f040509060613030503041701050c0702040905030403050f010b1c120e060c01060e06010f020f0a0b13080c0105071808 77
    0x4169801c1000072690b401c240c0c01c244120300d03208010241141e1501e600c01010001c0d5040c0e40094080b20401d8070f401040596800e01c0480780000070350200030120742c46140e90004007540e4481d104680d0082c04960000704500940750809854542c007180100c465600b00107500c00810725010070a15251091031100700300e110341c0c00b425004079190004036045440300002c9a14289000043c0e840b400d03281c1c0780040d125400fa118450048440e808514420792040c030174540a400034890341490030072280c3c07c0c840a0200401c00f0f4840740401c0c400000031030030510a0000556500000041381c203004020404034070441204585200700800c10100002c40d40314032031004940300d04080e04220211400240310380f08124000e4540d5091010002d220031101c0000d07401414262290b01100c13940d10320403650746007810300c501503070703840001248003003000c003000c3ca034014802c00d440c41656052501c40395a103034040085030601d40c3d580c50400201c164041c0c2d007502d4500103c403c3d0100d4501d0a0f9035159500c5 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 43773790 1250 43772540 43772551
    0x1030b01081003061d19020a0f0b041a0702031b0108010e040308070305090705030316020405070809070b07020616030804020a0509070f050d0f0501121502070803070305040201030b040e1011040608 86
    0x1a035410040a4000240c10700c002c40d80803400481b14104505154140c0c240c2c0509000c0b0300510b403c10001c900c12003800e07046c000351540c40742c1c014145440c040031881400c1d4441900c00810200704032036400b6032828030002c4000e0318406c5290101c8a44040018443c0ba0140d20212210008100b4040040d03400707658160403c00074940418a521006526070800c1102e91025526102c000351000c01c04a40490707403d03403d0300841e01000300b603660203402e54a4031030840304500075030040d503410b20031480d41c003018000300303070001d45020b00b010300300c400d204c00d05c542e804403e81c0844d49160401007146001c1110748003038003003682d11101170b081c1010b0240602400c2e014050520201140a84184c0c00940c000700214a001d202841203595540c0c001418410290007601c4410307901031a984020094000c0f50303903003030707100941c24034554410008600514000c0e20407810036454030540b040315a103c2c0101500c940d440c3c0d02800009540c200c0b40d03812603448402d01002281e00303100401a154100400c1c07944807 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 43775040 1250 43773790 43773803
    0x306010e0a170f2109090c0403020904060b1c0804090c0203220806090307020112020702040f060807150801080a11060d02030f07030b0105031302040f061805040201030b01081003 78
    0x2000080c000a2941c1d6894008140004990a4060700c21900050039890310b4540c405844c00b640309920420b42e00e0031640b408071402c01080052041604010300915400005103007902d0405440e5400641e402006072002c0d5452510303200c52500a2800e2140b4102d410030b01403803016651100c1d501d25010b40140d01c500b07a800c1d981c40440b40030543c021b00858070b00c0075650010a84407514003245030070140d600d0041e8440e5128400010719400380c000704540c0040d40586a0b000940c031104200406940500801c80e00a0b80343c10310b038409076903280035840103405100050031b14142401c800c5201c04916003c6801003041e0f500c010407841002050700307500150414048030900c0389050110f181d41c4074110166403d6480082044150082c0002a90084007190360600008104800448030360005950f9254010341d2540c07441c00602e0558032804560101040200d620b07942c5803010b12180e440a459842000c1c0c0700e1040008542e850310444443e10801d00b02581d0f1810034601591282c4924040103080 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 43776290 1250 43775040 43775057
    0xb0a08031c0f02071e0b011d16090801090515150603010302040203040f14010b0a0b120f07031104030c140409030c0b0709150c0c06110309060d0905250e040305030601 73
    0x400494044804c940c0e00102c00349942280310f21101049140c2041c1500c60101b501d0000c05c1030400e05611101120b0b40001c00d54090716813440d0452050010f4a110b01404103201e400548a903080c000c40046902800c064075640c000a014000c04c0b00c0000c1040002da12440c4001d481d507603031401502c1c1529015070b0016120354179480c001042071074034070001d0240800340c05040843c48054000781401e90050f1041c0440e10364406c103003580c501441666180c441c00d45030000e0000401c0740f100c203500000d5441c011030401c620045a0540c0e03130060304241c1d00ca1028401c18003900340118181c66031420103880c10490100c20781c82c01400783d111602e00804412010000c1281e00c0d100385811006061307002d170000c13842c0c60b5100000d0002c0c520004201d40f1403e004030005203079400364880c00c0001c41d1040145180400c0e00f010880b5580c407609110488a80d201c6400300815001c104840300310000c0b500c00b1041280910300210707900c1031070707202c01c42c070240f00010440001e41c80300a4a81261003820246030 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 43777540 1250 43776290 43776311
    0xf0105071410140702010605010305131416060e0406050609030601060503070c050601090603051009030f05090411040b0a200d03020315030a230604020d022803060b0a08031c 76
    0x1040442003030550303400d0030f001c04044020207582000380160610340013044515034034801502918422100c40034640c090302455804207940c0170405c214080c2141c150f4052049203220300e04c400905402941c0015007809500e0610700b0507100300e10103404201c40c0d660800c6000380000c0c1c0d5808050146000704100480441c3c00907010342c00040c1580d60141c1510703465a11004520001d0086103c1940c40b44036481d040d1500700000c0c458031080c1c0303415681314480007045a0054030703d5400500c401e82c01558420101031604e941d50083c00140c642011740507901c281e14100140015014040040d00c80e04210100071124800905081c040000c0d04001d40c81c1d44d500404180c02e02c0d03c0c2015a40c06001d18002c40080210303610141c11050202e00c40507690008000e80180d8558080710300a4005506400c61005031900c14140d5210b4251000c0010802c054959040480c0b04541c0c000c644e502c3c1c89407813003006440c002d00b075400a40000780c011030602201000b030b404410f4030119005071107a40e039455000c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 43778790 1250 43777540 43777543
    0x6050c0307060e0102030a050a020c070302121905060402031501081b0a0503060403020105011707060203030130140d1704060b01111204030204050c030903030403050a03061d0709050f01050714 84
    0xc0c8400c2e04418108074115000000c54040d520440300d4440c201d2030711300000c1c95011144281d0b11411030302030081601d5401c6600b0f002c0c84070302a00340d20001d8411000c051032505008a02019814410409001141403a206151034000071035070400903014040011300c001c0d400000c900c00c40c48105040900503c4108002c1110301c0e0003a001f20f905401100c1c204014190150041c504840341c2d803c0101180c1c9000719569200c0c041d5001d0200142c004000411414076009600600e00804203613208400c054100707061040d80044030100d50703017060b00b2041d0030310300c809004140ca00103880c144800000c06010800c0c124000c000c1c0001c1c2059640d1f40e28214592103403e040d40142019800c031258401014840340c0b898010b440120f104501306030000d01141d0152068074019a5400011810340e2034030358042e1180c2d008107002d07074101507035a040040c170f01c21400d89104100c1c1c0400350008031410039940c000e108800a4000d18010129101c0d03403010359034131004070344005810851503001c0314100403000303 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 43780040 1250 43778790 43778797
    0x120c11040203090309121903030f0e0a0f1106031e0414060705071e0203070501050c120a0815010314010612060b220e010e24040e03030a15030c06050c03 67
    0x60308188003200b04030303e0000002c010000703008102d900d01440420f2030300080d80c80c00320034070840000d1011060200024041d4001040942e410302d03002c0340394192103244510304441e44109841507480701c080d0340d00388240d07002d0858014109480762461440c02400c0091002806440e1500700e0425034001003c0c40000f041204100c0a0a401c1c0ca0244c100301c0c030010103d822080301580e14a110b50f000882c80081c198515155a07405409000c0c031074030700001500c1a0b0403400030307003406000701120001100341d003100401c10010a6200c00d1414200342c0d020002107070850403014141842c10030080f07241c21031103400781d045601600d401c6c0b452400c000c2d0880003038103080d803101004580c041543d00c02d40c407a070103220010081c88032000054550350f0341d000b0005007080c0300d40c0f03d00c42e100d20041412528900b249020751070001c800d4441041e0b6000100d003c03203680181e0011960004010300880d00b849004030301c54540050380b034202142c1951258640e1500a00c074444c103102c0001600c03130355068244140c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 43781290 1250 43780040 43780073
    0xf061003090605011509050307030c1202130f090b06030102070b19060e091c05030c0304030f050c0d09050307080f10020306030115030803090106060f0f080c2502040b010c120c 77
    0x14010384d41c0d122140403001c143c182c02c0d00040fa0b103035a4041918140000c001d42181d0304450342034855450f044080c2c506101c10102030b40c000c045440004008440741c09600e8201040e8030000900d03414034240420054006003403184240d004006150124025441013a08400880502d01000001c00c50400017003c0329440004401245410404141b00100d0245002c0f047d0a050941140500404460510089601c0c002001c018400325002c284510320103450b000070750034258540b03403150f04190f2400c0044000700000402c0d21909215508003400030000400d6030344024074405c00e40210041d25105400001d9208513800300006a06507025004500000703070f080c903c05016912030901c2d032460380c0102ca0920044d0300700360001031054440c0c142451180700c15503c0c2201000035441c1142c10050150001c9100d20043c000003105402e00c003d080c1c020185003107200b50303410461041c8002e8a8001c8241414820300a08a40101da1003a02089a00c5024900707250102e545107098203013015090345 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 43782540 1250 43781290 43781303
    0x414010318200a0303020a0506060103020703090308090112021911030f04030f02030106030611030702070602150a1d03030702100b0406141c0812010306150320030307080c0607090b030f06100309 85
    0x70f0000500d9000705804031007500850a0b038129545070801541a441290001000140a0501040480c1ca5040640f0b01c4c0711051416a440c1000d00480d0400d0303030010a003650038442d05a0785e081c0c1c62a00080c07192400101070000c0c5080c980442801c2c10940142d20000e0140845144c1c1c400440d40c00b136005c40c01841d8010010042862101910103850b0021101107002d4404c011022030243d00009061031121212100c40600c0d6641e11031180251881003040343c00103000414010480c3c5050025603c5400907600501c08160681c65140035207401030400c0e801a0700d070540c14405040c04202070307000e009090355405244031070b000c1c0c42d4101c4102000081e003540c0c1c01043d20711801c070001e01100c3c1242d001e10403d120000003d10002c0e041149448000c2100301250380788040d0480701e0020107524a4010141c80c101110b580754006182d0002c1201c101540109041055090b0003800c150054048840d1150030352400c21200542d8100c00303032030548a80603003d41030340290310a80044014560054 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 43783790 1250 43782540 43782559
    0xd02120303041b0b07020904032a08030a06141c030207030813050f010203120a05060f03070b040e2203080a0603020402160201020706020f030403110d0b0408041401031820 75
    0x810a04460f9050011903105109501c0010b80d010180c0c260303041260000d00210b0360784c0b15590155400c0e0701d9070010180ca899404041040e80c1100c00c0400f00b964042c071545666403038000c0d07290701180c076142c1016855103894034102455488103510202c559a465030501107858843c02d0076485e000f81c1d640010310103480020300252010070301c10310201f01c032400d54402e2107494150005a03140d028800d4180406140c01e00001d1001080d60449504084043c0600804a1040000ca800e18810f5004040d9020001504220210284072440c2c1d0200e12004892416050112420411120540301508204511020840300311280d4094001968010300455691801c044000c00b8036884602c00c0e03026000c3c3c0720000400c94004140344050040b218080e5240c5070556540c2402900d11001098010300c4001030400059140720308580030b28092964079484514002d0300d0784a80300c0c0708145c0c5040604141c50319428902012000000356404090b03200b840100b00c4081000039201004164071143d0707103 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 43785040 1250 43783790 43783793
    0x30506041e08180a0b030403020307060f2027010504090c0e040c0e030609061306020706020f1c05090304050108010e090c030727020f07030c050c091503060f090c0d0212030304 77
    0x210000361031030400c0d83c1041c2820b82c0c90071780b40c0b254081201c000c0c0c0540c008118200003d11030f40c0c405042031401000024500c8540c058020001c40c1c010113008070310710001420245007404200016460100188a02c6a03000000000701307980507910030440d800f030300d540039003c071305000700e000340d00e00b61001d0402c002914041d003005182e15117058441c2d000703010701d03004140420008590a0300c03442144d003e41d100b136a00c580d140c200a42c0034520660b4416428440440900000d000610210b24821030310f540c41c821540a070b07412264041c00c00986035108010401c440d9030400c000b50b04407050310000000a0340c601d4240c509084014039000d50500074181e0118501c4503181d1051000408040c0c81810f40520f2072442003244580c510300722a4003800d000807030000784196100603c00d48035009403060802d208020441c4524240c441c100e05291040c85001181800c008035039105092812802c1a4103003403801c280c4820b02094402e0060b524404c280c004d541301ea910345195089624100e99503032515 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 43786290 1250 43785040 43785067
    0xe0309010f021c050a110d0e0d06020405040203101509051302030901140406050a060902040503190c0b031905090303060a05042408030406020d05070c1203030f020313061104030506041e08 82
    0xc070802c8089640a000c803541b01200251030021a00e003038441c4911010301c0410014040c0b00c0c01b0089a0a9400700408030381512179001450180c60865040c0e600703203007400a61481c00102880203810081403c1d010030541c1d454443c66030507002104801666621a60203040c00351000744159000701105205000c01c10955601591040020480c100422601c0303e540205902c1a4460540c1c19840301e410214410f600002800c00c2038451108a4078a540d9801c4001241d0011110b42040d020044141c6403141101d00803a039112100300d000d50302d076180040001c0e1800303080b0300450380961b5a4100300c01384140541c401a01c2d03544c0e203101081000d0341e6000c01c00d5a81d030260181d60011300800c08524400c60140050700c0ca010381c0231080c7c2000c1420003089440c0d100252000703404054607098441500d4000d44011070140c405100e00180c804440e042031300a0719220101490064800c01c42000460000b00744170303070041d5106d00049258220500e50320071106010f080940306960010303458140005 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 43787540 1250 43786290 43786297
    0x32202060313030e04060503120307030b0307060f08070801210201050c030d090606080c06030c03060f0406060503040506060a12030c0f0203060112050c0109031a090a080d1d010e0309010f021c05 85
    0x882e40d203044e0748803440018042960b101d40300c0e540d01076001c5e002e5080700492560243d9401115850001445050140041c0c9400407590008010900c03815041c0d0040d58800903890707001e9500e00340007519500d45180c0000c10101d600c48500d040110700d86c442e045a114000710740d400b81d40202107940301c03903040b00790720700070943c21004440c40c900d0303e1400034001601107034061420300c00800181c290358030300000a6150740300400107036015555490750205655140b242d20050002c41d0b64550300e030b25042c40d02078548030000d4038141c4201031419041150711074141c4c02c4dd8540d0350600c1d05401c20300a174030b0070f00320500d15524000c0d4140102c0d400860542d1075200324110f024002d034111055064440c0064451501c01d0001030112000318500b075051002c0c0300c60a0390094103400c2124189206525008202c2d00034901c1504086d80716200d200e815000100c01350122181c0900030040070042c1c00366203680c0d2044c070503058140240c0704841d1a243c3c1c0280607500420302e40d4040d00340041c8030407600404035407 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 43788790 1250 43787540 43787543
    0x1506110105090607021903030608070b030103060509011a010f200102030403080a0c0909050403020f06090d090501050405060304020409020a030605040c03030f0e090f09121603140708032202060313 86
    0x600e0400007420030440043da09000d400540c020300121401c00b03070305440c41e80d140ca070140d0034940c41d280002680c00c4204000401403a441c00d44940320f50441c640030003516406440d14a85a04210600c0903002d002085169029002d0804003100c0c0b440406c15981c0242140e4068200990190790040d030403010b400840c403072071007a501e480d01551541c8210085494000d03600c030006400e0401404203108980c080ca802601034011214868102c11056181a108072504907180d00070940705980e16401c00d50941c041c20007401c0c101e041038204408528203020040c0086d01c101d484520030b00035500c0b03801c803900103940c010a0a00891925003061240d03850301e03210031030019107400000c0340c83c2c0c0e107e4020404a41401002805030b525080c00c00d001d00071010300000128000d104c280301e500d482c0d0100410381d088101d807031181e681900d42000313040006100c039280005001005060006120002100c1d440694a0319525212600b150300c60303140c551070790000350008000006e201750302018500700e20505 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 43790040 1250 43788790 43788793
    0x7350907090c210506040f020703030c0206070905032104080304060503011a040803090405060f0a06030510120507060507050114010303080a0501090e0a060207110306010e0915010b04050105070303150611 89
    0x440c11100111240c0300c4000d0b10b01e070098004038401d4189845134026541042c0c0044c000319642a03540c0341e6204903400301004402080d552510b20031003d40510240b58481c01c5801c000d0600ea16040100740c0f0340144c036031200740c0403145080252890032040265000360511c4021a80c4441d11003c0c0031700030394000c2c040c106c076495402d542003180178030080403641a50318000203907060030141c00a02000d000050202c5038070905000e401c2141d0b45450700c21000401c040c3d0780102d1141042403001181d24991303000f14402075060072a034000305600041c400c04032003840c40c041e95a03466608015004000140c02c400303200071140000000e15901140071400360508000c00c02282e640d8020810450f2170940344200b103074214010080c0440d4040d40a404014040da5942070072130b0340d280010341414826000403400450385410301100c9082040401d0344100e03000d100c040d940d414036000740c0350b40c003079072280d6030402100081080c05c26109400c42604030010621603407015442d400c029160802c1c20001da50b15 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 43791290 1250 43790040 43790051
    0x70c0b070f1518030804022803020406050913122322030b19020702060706020319060302010c170d061403010c0206010f0501080907030c08060f07080735090709 70
    0x1144483c482c5600c1240086080205000c0503942520441c500a1050764020071584007504860718103440001c0030f544841d41030054900394070401049868039000b550044004100300301440f0103c08002c9456074000c4070f105540804e0000c21140610b004104421198110b03280300c01d002d01c410003426000751140840002c5100818000c035038240e252001a001620001c0840e441c40c0f001401480c0340490110098907100c150f030046002c903402070038101e031800c0d0b0020030801d0004075460790740400c01003201c1c103000c1645580c000a00038404501c003d4511122402007411181000003203c0346010f948000303000c560764076017482d00f0a03803d07074100d079002c0e5081c1030f0308a0000388082140f9050350b501d800c1c4014624184401182c8041000b0309841c070f00d00c140c50001c00072915072072155000b130217210000c04030340c68403012500100740701034251000d019140d008c0c45442500050030f200d0304002d0710220101100c00803004090268180ca17900c1c0d5088900701071000303000740483d0a01c10b03949501e005010 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 43792540 1250 43791290 43791323
    0xf060806030706050d06030614010302191503050601030216201504090c1808071409060d0303050a0219020c15030610030f020d020307030b0a0603050615070c0b070f 72
    0x12040412908280d01d81c1000d001400900d0103440542050509141c0c0050b2190300e90b9201c00842d40300c0744071140c240b4607601c0104214a408202030608140324113501151034034181021008800d840c40f181d050603243c40000d21164030aa06880d882c413051107a42d1990891401c180c6e901c2c083c0c040f1071b40c8100c5190003d040d168109103100c40c102c2d40c8101c81451138103140c0899440105140a55807003007180c1090f001903034803106076072200500001d1000c0e00080703142c070300000d0681d007110006a002d020f024040014690f140c04500510680500b000b0415550b2018a50000d108014001c0c403c6040300341040c0082e40c0c00140259008426103034981350070781425042c0201e00041f280160300c0000d1b5400344903038a2003508446984d010964016003003001c4c031030744001681c000f140c0c581e00103030f514440c0705c04610702014440c0c0104070b00d00b0100300c6030418601084490303404071b5040e01d455100144000420040811442c0101201102d07241c07034540707900d41040c40d85652b00c03080d01c2d2005000858034 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 43793790 1250 43792540 43792547
    0x6010e01020304060e0312030405070f05041404061e0e0c011101090506011a040f0b071b030305160503041203020d02060f090a02120c0a03030519030207110f0a031703010f06 76
    0x184000503002581400e10707150084800b9541e00140302d4050290108140c11180480b0140d030040e4400c1c07000e0300d903840c10b10090b045041e00e035a00480c402c44c00c040040580e030480c2c54400782c2080d000100031800380d107000e42c0740d10f1060003e90170050440c1345c000761018100c0702085644020302c099803088802d1055088081c00c1e03440c07021018007150000f500401c90055501030f0302c051010071040302d40c282980c40f5100c4c102c030201d551007601c040200203418000c0219103441e00101d0440101e03c0c2646906503280144980504040c203d44860300350850f2090040070002e0b140144100c00c0723542c00c45406450003c0d01c500c8000c460350094072408020688143c00c00e000c10744a0b18411004142402d00c075000c0217140c1402c0041998a4001c41c034496102c1e403214504103000d50b0003526003540c2c031607456064950360052130000f0b004043c414000e600005148400841070700764112a00b0740e1010300d840c00108950740d10303070000f003102c0b8070310403403203410024040618100c480071071164045030350742c09068 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 43795040 1250 43793790 43793807
    0x102190f0e01170c0c120304060903080703050403020c01110a05070326030405030f1804140619050306010306111c0f0516051b1e010203150102011b030c0e090a090203060601 76
    0x380d40f2009400041c0d141030200000c0e040030006901250b4551540201c4040a94801d40e030640d0081e0310b0301018401c1c990000d22107a00084940b808000d186000d4030000d440390300e4a0b8402d030402003030602620075010104181c02d0134603040700540702c1c12981d910f4888401c6030028100e9104d500da802d004640c54420304181c1e44602d81181c06103150007071759410b4154a0788498201410000a0500d13071140340c840348142c500404007006610064140348007000240184844400790103c00d0345c0062002c1d03100440c41c541103d82c41070000c00c8800c00791100801e01d000d281850014030000c2e2104600112564000060203120414204040d84031340640c0303041d40d018010308602240e010040d00070725004c4942e01107a50f81808090b100c44c20b032141c0c14a02992008040c070710440e90040b0074481c800703c4c540c200081c9074500340002c1104a10170f28031010061041c203459414075640c3c01c02e002081c2d0046152070103c8100601d50012481d00c0d10280c8000c1c80d403000142d0103449240009032565002c0c9580 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 43796290 1250 43795040 43795067
    0x50f060f06030a1104030c090c02100b0a260114010f0602030304020618030120090a090b030a030c03140301090c08060d02060306100e03060f041a01030804031101020102190f0e01 78
    0x5186103640743c9403410050108100300c222401010800000444c20110b40070000d030144100109400411980c02458180d00c0f141c18030105144c00c5030794800c1e582d4014058105c0f14211510f0341000034a06542094050303c0441c80c04a50814409112000e04803580e1b9040c0c070701d5024072411240d2140c80032690307400200c900130340107201000b604a03c1c0c4074400c01c00a0404000f0000301f9164014031311030b611070101000e400300815000c10145a107281c41d40b40726000d410f01641c104030460300200000e0f030300c443c2030300e02a051103901500041814030900b10142d0038141d404419682e135950702c41c10001010b07411900c90002e40d0110108200d403074a143e9450310b045c0c008041d1070464a07054208454900041c0041e404d11207501d107c124140c506115040c440c06a8050688451509040c0548200034443e40039520148110060000540050a07681a20b801c4180412206406001030b40244194a0501088540085402e2026500c0881d0b119203120035a500180420030a0065074108030000700c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 43797540 1250 43796290 43796299
    0xf0c1b031b070f09020327030702030106030503180d0f02040b130c0513150f030e03070501090b010e091f02090a0b0c01050901060504021c02030c090604080102040e011212081008010609050f060f 85
    0x40b000c417291f09648082c080580c541d007580c0c681881c1c2e070f0009007142c00750b500c00c0383c468102182900840140c48a901594201965031401103000c80e45c0b24008601a00c2009120350b60315400c019407034842d040c007084d00c10340342d072401c22402107461005030194100402c80d0715542070f140e034081254002d404262051903030030303150300700340301b16014040d00506034450303e06009201c10300c8003a0101c0c0090003000300ca140904450230465042c40d400f0280e400006003040f039a9400040840e00c00540a0480516041200d800580700ea040c540091405642e6901100c06100003081d880201751042d440603010381036150080081903074580a01c0f041c0e0046035621003407407040741c19000c84200c0503002036138000a0551301c6c41c82d00b0300020020b19140c00c60b400c906001d0398085414800f2003614540c4601420240643d40c0040a841d9900214844043e200d142001010808540c2c09441441d07104c018055140007481041e442d1a040300080c6400c441030700030725008d400440c5803400c20f480039082d142c00151 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 43798790 1250 43797540 43797571
    0x150c120f0405190b1612020a090f08120a030f09120305240a060503090309030102040303090602010c0206060a0302040b0f10020a02150306010801170c060703030204050103050f0c1b031b070f090203 86
    0xc0c80502d5840b2170392092091011a003140801615144000c15034441d01d511a800102c3c1010b040c82c00d1013969402c135045e10b034000d091042d641a07840342079a00740d501526001c1140c0b0349410f40f420241400c008000c01c26502ca150082d4115010341100d881803001c122940b00900e0001000041c484c804044c940d00000048018490144560021a031002d680c4017221f213000d5403140030a08a0f07000394020740009000c04414041c50740d080c010b40c681000c0e05c1c801071107142000d00000b40d2016080c40024421075654888801a4541121942c503a000c0100800b2402404107400703900c40c2c1e10460202d225000e00300c04915410801d0064901408042c1e41d05c0c9006d030b003040d2000c1000c03010028040b5503442408002c4c495541c0e44401800c0040c840d580c0540c585141100140503240040d140d064415045000c00030304180c1d1800780e4526907001c2c006452210b03a900300f001d08610400d05038003028406202e440001420004254048400c000c0e906d810081d130f1400840c00b02c0c00140c98085d0140d41ca00c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 43800040 1250 43798790 43798801
    0x1206040305030c09120f0640020f13020408070f03211407030207060809010507020c060f040e0103120f1106010302040b01050f03160f020a05150c120f0405190b 70
    0x3501c8080e5014180c00d6140000c80809450840c240b1500d01980d40074004111070195840b10089400021602202c4001c8403c0c48c5800c0301d0002103076034603032041522402010f543c0e804076000107070007019101c1c2d046040c1642c6050302079803142c0035004c568810036900150281119203e101225002464841100104950060001c40030741a80c1304011450b005800400900001060350500c250002c090181c900788018000040082231118140d141601b00188a500403400644140048890540c1d5101170310b00d400c01401940c0006181440f0900003004020700c6900701d6241c1e0341e030798986040e00c20485804462000c00c0e070a03840b200d5040b0754010401400e05401820195005042035420801101e0103801355800c1241d41e40c1a294040c06a4500260059940c462a054602c0a8104019661a40c694130500e00c0a0341d40383c15904000a404800b100b01680c0824100303200306500ba041c5a011304038800415035081d41c20303000d42c0b141c0e00905016401152040e560104103203003141e40b407 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 43801290 1250 43800040 43800061
    0x1107120c09090c1503090c05100507060c050c010626030319111207020a0c140d0b100b040b0c060a06030b0a02090102010b030f16050a26010603020409030e120604030503 74
    0xb01045800206094010850300c080c0341e040364845440d9540002e003038940341007159407165030342e000754060140c0c15070000c0c607030364440100e80c8000d80100000c5842c84144000701ca85109400101103554030f000000b16060220301c482443e60011140c60500b07600c2d0440c001d580780c0c0320907a0365805d00b02c001d01040c0c81d0150250412011110341d005014100b424170010640072800803102c4800503000380f000030080003e441e02040240500d03041e0111104802c0c03002c1100c82d41d521074042c0001010302d000940e130941340c444840c041d240a290f290b4961341d66020400c0f00e900001d0600006019500001e111000ae40c410300f400c8a82042c00f118407034480d0004a0000d5000a503003a04654031210b18290725141040300308090071001d0010094149818944007100403150007442c814106030702c04010003580394145141c00b101d03070300c90310702d02140114441e401090580d200942090400491809258200100c074100d50340c00e68443c07240312148050181c0303403041110000c0100764144041000c0c60301 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 43802540 1250 43801290 43801301
    0x9070510090308030f09060708040b0c07140a120207060509010c060f1d0d02010c14030721140109240b0318010504050a0201030e03120609251107120c09 67
    0x300341c1095103120b80c4030385482d0100d81c001ca03071071380c4040304103418045030141c10400280e0003011071502d05a00c2c2025641c008109602900030500d0700400b14040303092200401401d20100d0118085814030002ca1400308030110f15501c083c00980600000010024052000c41d078001d0416034800341d0640386c1e5500c903030003020b890029a01156407501056440c0c10400301c44100300440d60020024914401402800c2d82d00520032002001400007041e00c94015003000d40c2d41007400d0341001a040d9000d00d69007028040f0b002c02180d00c2d03c0c1001a941000d11800401d94142c072146c0d4424020850312400c51910429160300d541482070109a0030002c80344040042d64200c244c007072402142c641911103441c00e6840981d000d540e16080314072954119a01480758070351000040018505040d019000400005c00080c8094020301d035200c00640049000a400d40da0150003145080c40c2d2454104010300c411355480c00c2c1c43d098460450b01080307808c42062072240e4aa40104501c035040d0405144002a02 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 43803790 1250 43802540 43802569
    0x8070203040909060b030102070501060f060c0b060d030c0218070e0913060510080a030207050f040501030215070f0b090604030e03071a0906070206040b0307030f050705091c0c0618080303090705 85
    0x5d07540c1c00307000d4281e9001e00040011600a0001149807803d0004900b03010b8502c0e4403241c107000354a10341d80e000410400a85070700c0a0203d03401c90510007241002d880720342000354000d610403421070030150009412240760380510410b50782c8171781c1d0004810602000d618107030b4091860007540010000054880d03000180d001c05031040d6981c0050ba20040300385000f000120481c09030304401c0b028405400c1a00c0c008070b084034215014021940b454011481c07420811107050411003000545606103e0142c007a0044150b220380c10401910b85001d40301e49130401954101c00140f600c220320180382c85c0002d1180103a0780c10441c2d0410204105424071003a40c084140c49070400e1080c41040007503502c1c0400380c802090640849603491030285401421a103207501c88914580c5414280b28070160f0010654040c0c803009d4400c507001c040c540b07165800442003444020400c4003e048003040c6251700c40c40c452038041c00c5044a0001d2515054690303100c0c00100c82e0074596a2040000700f0042c40d000c4004030003a13 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 43805040 1250 43803790 43803803
    0x9040b090a05060703060e06060403031b05011107080702040b1207050f18070302120c04030c120f170405040f060503060c0a050c0f0d120b010801140a050a0909110108070203040909 79
    0x415075a03a07180d041000458418004c40eaa6a00400ca0084404140c0d644050112020340c40c190655501803e5203041ca01c010340000c01c10200724003080400d50240c12030040c82840c5540b074560300e1400305110b9200d240c0890046003842d40c150f603241030000594075001e11503c0079007500d0341060300f4003003951440c0040729804682c408a1140940c643d0030950b0281c07490b6a40503a644c18500c03410503860a024080d10800d0004120070808110001c456070141e0780c12501d204104425818051004106850040c01000703686482c0003200036402c000b0002c8a0301510300384680000c1c1c48804c003c0b500d0b030b4460b10313070141c00c40c80000d0180c840d01e500818404074541003003400c001d0280c448a2034031100c0168426151700c441c1050100703d820807050701d08240600014003992825031b0008120082c18880d0032195544030030710b40e450355a102c050744d02410020340a42c8078155a08010400b4098029050b14040140400d944071035200d160028410700e0f03550000c500d802d1915988400420100d00150ba11 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 43806290 1250 43805040 43805053
    0xc0c02150d0e01020a0e090103030816090312090501180803030f04020312160312230c0f07050705090603121b0a0609140f010c020a061505030102040b0d05070207030209040b09 77
    0x1e00d40c0304582440045000050b19052600c030054a82261004104d101f50302c3c1900400c00294400d008644c407412102d080c1281743e07007030b4505881c5902150801440f10019071064016a03505c841c0480c2100c000766510214440010000b102000c4a03014040064208000254003c010f50010507000361010b000ca44100002e2441c0540d25009690710110300800042e01c0c1c414507601c0705c00c1c2e42c1c0c42c10301280200803520044900b505c1442d01138945c03c4c4030070f002d94001080002d843c41583c006015180000d69102281c3c81c0403070b1540200d00501d88075034107083c00319940d401c0014481c182981150415413501155030059444400100300b841c12611035079260b0400107441c1d001d0402c070349105e400307072034a0f1143e051421410803c44003882d011583c075040e0a020030a60010701c44030a0b503000440001c000c0c04030540c804c0c01481a81250703425600000700001c210412200030980080010300802461312a10300c12a21007070303107200c081e51190000d008600030600c0314400c0c5420115601c03c4880 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 43807540 1250 43806290 43806307
    0xc09040207050714041802100207030b01090c08010914010506071106160209070806010e0d150608030304021302071101140705060f0a0b030705061b03040e040507051002010c0c0215 79
    0x141e902121040320240c0000c0c0081100e1030b5802c01a882e0610101c5081c400d10b0b1700c01041d4803c034100381d6806403042010008040185000f40aa80040d642080310a80300c5d41c0c440c802c03036024101100038140019481c00000402010038894200c0d6a041020050156440c110410429400a03001960680001c1ca0110384583d10500100010150080b0718440400140100814400014621000d00c04002c040001e203030381c001c4411115040c1182d03420b0800c4c11600b4220303d40c1d4103208440c1c500d203144c010301145400001000c0c40c0314601c201c2c0c001314508500f8032080c05901442c24014007148036841b001d21590b00520101110414580466003480003d4850301d1030543e0603038602c1004043c0320140720034180140a02c0c2c000c910207a008005507880e0001050342d51013511042c02c011040b07900c5001401009100312001000c101c52090071034205803e00d21340f10380d082c0c82140d01c900032000901401500600980c206005d0540320165180c0795a000c0c4943da544200461204403802c001200 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 43808790 1250 43807540 43807549
    0xb0703061409012409090e0105010302090106182102040608010504020a12080d0c0e0310050106030f02071709061209030903060f010e0601030902061c05010e07020705060304030e0d0819091512050c09 87
    0x84001031f080c004a20fa501d540180850b800781a0841420441807001060aa0f01c00760300707542c204c0b582c558a00401440c45400380009039400c00000398020700f000b40018402e507054101c2d50085008491503180d2a41d40e808c0401741c10001e00000308007502c24012204860f01682c4040c0542d010b500b400d603136911501c00000c1c00e0411188801c1440740e5280010711075164103120700b40c104540300d0703011854084580c5914010740000d18a4134100c903000280c0f21400d4440b101a0703505590205040315207400c0c01c00d1400c0d1643c0045081c10300034424900042c10602c0b042031542d040703a520120701c8a40b52642e40044025100301c0b2030980e0021002c00c195224010080c0c2c6a514005001d5800502541800c207101114040581007201b10345c802e100c14082d55645104481c0c2060741030804e00c0d600410310010916044654030058520000850000f446094600744180002020340c2c0380f4170559111020850341400c4030002800041042e0b05031084241240d0080c0d400c01e00e020030346410a0240030015 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 43810040 1250 43808790 43808801
    0x8070204050a050709050103020c1b0a0e07020604030f05190e011106072003071a15041b1e0206070f030213030c0f080c091506070b070306140901240909 67
    0x40b140203503150100060160f10400e40009420300346000d40c54001ea42c0000c696540f80803511040e003202e1807050701e401342e64100c03a030001402d404049546a10741081c020f500c2e071408450039000310f4241d204d400b20151190307040754110040c000c12a0445418100d003100c42000d02c007091414001005e02540b0801c1c4100001403003010540d036034040f64114004120008815034070707800c0142c1e105000e2040004c1e0300d1103440c80d0300300c401a486e2240780c1c0c410807082c8464020100c0203800070b107065003400d0f810292540400000280743c40d00d940c440803001004000c1500c901e90140180c0010001c9040d1300d00ca440f046400c076455103005414200180034101d41c41000c0d078011103050401d19001c1115074180410440100700900161586403d6640410f054101c000d0000b0107201c18605a5400f55541c41c0980300c150b5000303c0d01d003199161541f8041d005001e280215110040c51100030342103480d0900c0118144c41c6005120400c3d010707207042c824054420503034583c040c058641c0c4081852195032081 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 43811290 1250 43810040 43810051
    0x3020a05072f09090d0f0203040306020f12150d080904200301090c08010e0c070c090f0902040b030703020102030f030a061206093c0302070b0708030f060616030305040807020405 78
    0x40d004030808519014000c2c140364203001e8010826842001441c41010500a40c4000c1a0420301d03122444164100c2c00c41c415504002c3c80c1c584003150030440103004001404980900c03100641c06910f810a5410f4242901d00741184d06c00d01580d0f0031000030707501c40c014007400318000e000030460300d5444a4201046142c001711929003180407004000380e40d0306010700380d42c0c0b1350039044c20078103941401a05010b0703490091060011610008110303040003070643e55000109800b0004001108c7c211610001410340e10100b60f1080e424035050291616001c10164200e982c141c00440c901284204001003e810040c190710700da90ba1413030b000404e0b00440d83d45a900303610514000640041da071405003820030006401c8080c408007440d048103182c10b030714202070008178141c24070100322300d0380e250492074041c2d142c204c0103040201040740310030050200c016501400e40b1300085242c6594460a100203405210900c440c0383c083c103156040400e000f0751000741c016000340c0e0954074110343c64001c02e00b5644183c92 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 43812540 1250 43811290 43811333
    0xb06071e0632070e1e1302030a1b2105060d02030607110106090504020108010303050c1606020304170303040c030f0809030d0507110307080304061116060c021009030f0303020a0507 79
    0x907401e100180c20b440e4848803030704040704104074500100340c00c100108100c410201c001124000c50365610700c05043c0550004000750350300c0c5442c100791009000d45d2401ea400c0c100013103241c484030707500580300184000c0c05c04200000480e4284550f02c05420094501a004141982040056202840014400c545c5503d841c5604900f00001d0390071524150300c0078003154030708802e220051703074461442c60440340c051034015203074540c2c440442d0078200c1e0300b000c91104049840c00050095000303c05441141ca80340d000080c601c021140b00c40c1c9074030003101e00412510840c0d40c18000500d0340900690340500584001d420002d07200d0201e440c1480420f01c03040071a0b0b0205800c400c0060366006445810b205802400c1100e103082030b15581c074060f0380076400c28415a462a504071703000c00c005248007281e824888142140e950038005c2c1000005060590082d4000011086150301a0411200f125440128449182c0031604c003103000790880900d54007085000c00c81040400d181c484c030388101c000c0061 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 43813790 1250 43812540 43812611
    0x203010c0c170301030b0a02070515100510090b040302120f01020f0d0b030102090d030e010e1f080c1314060412120305010801140a09080f0d06090b06071e06 69
    0x410303407800d0001c2c84800611a03400c0005000040408014540041e0402d0003d80c4450052a09908044803507131790f9101e00302100c0410601447c01403840c402c503881075880d034030110010740f01120351b02c2003802420a0b000c3c08000c200010b0408000750f0356851358100c1a502c0010f03903200501d0981c0d0151822051420000c95142070480c1a440382c03400b500800c40c02189171410b41404500301805014014040c05004040d500259010b00e00d02450b8900c003c0c030309500b40c02c92042078024a202500e00c80d001620410000710100d02d420200c0e480103411402c8883d05d503151410003200c0a90120300d490b0030442c203010000342c1112150814210500c1006881407008100b24010120f40c1c050344030b4180e42e03041100741071903032410038407203504080c03800c8000c268602d083c00e14903c58031941c00c9400030000c002511003e07010f030591215040c0d40e48003000384280030a00081011500410f40082e229010f407545070080c980b808620344242c203100340c4011405640200a0040310a404620070000c03c9038003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 43815040 1250 43813790 43813793
    0x6010302060d1b11010c090e040312020d0606020f0c1009030b04060605090c0702130203010b090f0607050a0b0117070501050f09010909020c010207030201060e0108031207030b130903020c03070605091009030203010c0c 95
    0x2e00070729686c2c5a0900d400ca07620b07490000d042a100c2d41c0500040e05003c0403659000480715190101d40c3c45a101c28410301c8881d07030300c03200250382e0b82d00400f4400490080c0d0000c60810324040b80741820b0400c8565440d0f08184c15900c40070b032912009041124484d0ba2007100003040d4480e814803505c29028034810f5919186540107004072500381084000030281304000521070080d614060b107102041c00e4400700f08030f104d80d001103078843c410400007502911511030000200110b114280c2e051345c40980c0d00c03440b600c080b400c54650700c0406014150200cad4080c0105010b10340341c18054a200c002c14544125220768402d5414103e9000208483da980d400080060238035809024000080c40d091601c044103615007200d00c0d0308c17401107500038080d94141c81d010403c1648603400c0030708008030041c2660b00481c49a00d81c8001001400c0049025000303a10480406140124502c400c0721070b182c480030f02d0310300168104400042d4a550302018000c2c3c0d0388002c00540c030248140c481c0300d00a500c1d516246010b6 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 43816290 1250 43815040 43815043
    0x1d0306040f030f02010e060c0d0905060a1e0b061801031d010501060905030a0203070b090d08031608090115050f0102031303151107080403030c0c0509040507090c030b0306010302060d1b11 82
    0x300c0c0c1e9041d0139a810601c00e404040310006181d80c0c40b515000809488080001c1440080d2021100c003070018800d920a201100d03440c0d500c841003040d4502c10b189072010a4228035015114143c1e1055448003003403001b82a203600003041180000c0381490001021850f060440d80303500030075115030415030365036001408401d404ca004040640300c00c500502c0359000d107900080e611101d81c082e58982d144007251019403522940510244030341c0c000d100d01d0f180d26005000b10b0314162000c0c0c0010020300850049101d188061240801c40ba01140840c1c100301e06202c1031003100c860101e0001e045200400c03040300324842c0103840c01d01841c40741c00040c0d0517010214440d4242d134a400d403e60400c0400b0008080068849000c8070700302d0f0351500309070302c0b001468140a405070380d2070381c001c68200e480c0c0310401c030400c80042465010758044a900b00310036030300d05008070102ea5045040c030347c05a000c000113101501d40741000c1c0502410811000c5260070308404450703c001c84091801b030210300454480c03d50f0800 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 43817540 1250 43816290 43816307
    0x30f0207080a05060c070615030503090f06030103031b080c010212061f02280c06020105041502030606040314010209060a09080d02060435030c07030305180703031d0306040f03 77
    0x30074020308200c0e4880d01d03a0368880c54040e002c0e0200e400000f4000c01004440d0700810425005070281182d10740da6424140e849031f202d18025442404540340250a41c580b0318150383c142c0740c25075651002c00e00841011004080c17048000d5804c013074284054240c00300300b4001040042c6c0081425131150400c1170900140354100c102ca07003400f121362224400803550019211603081c40d0601803003003000030807181c03040700f1004001c0900042d00050000c02c0303003a01500b0a500a5100d001c0c0d03180b2801c1b500600401701d000c1612092f502103000c00c41000070492505510003243c05260005140514400011b1041c1e448003100c0740c00b1072002c4400300041c4105100c000c106120074000ba24203450a0b40c1c0e140a940242c96a0644004185050111250350b60401c094900e4040e8890f980c0c900f020641d505c0180c1001c903048001a0070080028085140e00039160640303c4210300510090b419a034040e6404240e9404265601c3c82440040e0450b940400940c0c0c01a030040500c580404010708000349400e0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 43818790 1250 43817540 43817549
    0x1050c03130f1e060e0c0d05120a0203040902120402030f01050906011203050c1e0c1215041b030b01091a0f060d11030a0c0207150c060f0204080109030f0207 69
    0x20050003080180c000108080705450391041d880c0c11407002c6480c202d800d10315642604100c494045003a2400c00c001c0d41c1c841a00406000d084495406078102008144180020001d02a4112034542d000c18921040602403003506401036904064070b8808103012a08825a0704040625400c00e010540c1800d00450400c07100c004002c6c04540b07010390880c0e40d5554180b16080c040c036031001c2d10b0800e151182e416182c500c1d085600383c84600189107000104000c5503c09000710b4056640c0c0090245040c1032507098900310400600b14042940d141d84404800c0200151000b03850803c840801603000c0d0350302d502642c46503000090035414a07002400301c07168801c07011b23031356400d400740086c85a541140d1000506422a0207035512482180340c01d02400006854440060021041c00302406039900210001c986035421a00b1640c1c0d00c9643c8030b80c1c0c80c00031061a01241c8200c1045021408940161082251030701d030261401795a00c028900b1512880d07015800611903080390103000340e041c00f10f0070080 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 43820040 1250 43818790 43818811
    0x90f0c0b0f0f03040218040609020f030a0b1f03080d060f0e0c0702040b030f0d03140603070303080a020f12150114090a14040608010c05040f0603051303030b010c230105 74
    0x601d440600110720480240c05411400400080e04555030b80031151070210f08800031441d2400c003807034000082c050310002284a440c2a41050006040000b501ca24040c2c02070441e032059124055240e0003150074035107407010058400c0d804404a00190020311519419500008980f031420b11030741c0f00002c968026110b00c8403400144400d0707807411015590403a0301100e000901e5221500000d1410340010103120040c002c8429206507d0781503849207014202c0c001540c00b240e616a4101500c92a00780401004640d01d400030072124030301c590181c02031180980f111450200320b056079449501c011181e004190000c10058100d659015103101010640352031030b20704104c1800000b9100381c07070902451031114182c6002d00f0040e5140c0d0002401032030b240000b00b081e00610500241194018000c3c800f50310407a07080021814400d01c00c480c464a100145040c0c01812603400714090138404020604000f0400540c0001c40c694544403444050052030300c2168203014241c46003034800040481090 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 43821290 1250 43820040 43820047
    0x10501050403020a03120e09130203010b0f10080403020307020d12120b03100b0103200405100822080705070803030a060602010b030316080c0609030a0908010e0705060319090f0c0b 79
    0x140c854908070820740342d103d18018011b0030381100455040ca1403140440c2d114244070103200d1041d15003d810001d4600a40c02403040080d0f0300c045c42024400c3c42d0749150040d034204e440c00080c8c2d01c18030225410611910607285040c146400194501c218020107617200210420841d6415400070804441c0101030303502803240810f0200004d03100e4281d808000d101946a5081d005241e110b584018a0000c0d40c040f80108203800410001e1150440e01400780a0040641e50075400c0740107400c4517128101035118125082040505001540d072904d40403110804140f1a8100107202845002c0c050b10f0108000d40c0c40b460100311103403d482e10303030b484003056902d0f2204202c61501c02004881071807160380560300c8019010f1078003200c50b100703866401d015400b0b1041032041d180380105c000d291018943c1d41e40c941550b21030401a00303e07585a108441141d000400c10042803d00030043d5034072000762924101c442010769405c805039089284129107155065902504100390f00c98000060541408603505 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 43822540 1250 43821290 43821293
    0x130e06240313020a0306140c0301030b0a0b15070f1106040f050f010203040b0301060806011e020c01030c0e0d05060a0501060e01080109020d0204030c0e2403120c0f0d080a05010501050403 82
    0x1150984000c05a0803888000001020511480150803400f40d014024412403a070f28144200280907003aa1a1440b2140c00045080f000100003501c0c143d81d0414544e04054442a0010303000709500740b2425003090312404c1d2a10f5180c0717014080c10341c2500464042c0c0ea071050741e00e0000e0412110a00782d85c03003000103220600c0003020842c240c4c07054076070139035003821f0320b186050042c0c1c0342d4040c65212010400c400400450403d85c00000d035030040a0a8035864100000901200100d9080a1035003005030700c4644081101e6200350060b1084c0f0200b400c08554400c0d07000c011540607214544165855401001446907600300340c0310307450040c070301c0d403822211440084000824094040c803c03001c24580208204112154a6048900031a80070061b562815503641800303c00c4802100c001030105030300100000308910300001b5101109001b4050041e100600e45004010341000b00000650b00c18800d00480340790302000940c0300740c0d000d500c8482e550301c2e00d10003100c250340058000c9810440b05020800 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 43823790 1250 43822540 43822579
    0x2d1e0a050411040306050907030507060f0206070302041d07031b030c1d0a03120915090501020f0606031e0102040801020c0102030402030f0c01020a03030207030203120114040e030412022202130e06 86
    0x41c2660345c454000304807034440010140c42c00589400107480390103030300e01c00540740f40c10810720f60300b6155680941d00e490344c4151069040340118802d1001d1001000810240100d071101e607036601200da07050000f00b1f0400c450340d007001c0c03030802400e0b100030076680c009a190064200e6140c0c5514440c1c2c2001c2d029401401c3c021900e880da00d840002c1141c410182d2030b00f10180945144005424404800d141403010301d00c1c01400ba52440c42258054001c1d400203074082e100101b04940701d40c0000d07000f8005a5a1001005803141100c3d070601420755003804041041c9100380010044008140005602c03820580101030410003049011602d59002c60240c1003d071341c002c1091091244c045c00d0050300e881c00c0b424161300710320800c1e80700000620088004a020300c1066a14108410f0903102008411aa03081042da03034891401505000401c0002500041c9000c08080400c404035004115070a00315007415000d9030080d01c1d0050b610151004140440301061090640c084000c44541c5c140c3d0a0071800038 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 43825040 1250 43823790 43823797
    0x106090504122001021812030703080115030b0306040506060103110a0806010c08040312020f10021e0c150103150f0204030206030610031508100f020304022d1e0a050411 74
    0x8000c0c0091491554600b50014090301c429250f100020741d42c40319040f0040c0c62020a060416203c2c004403000a20304081c00002d031502c05515481d10340050342044004c040305140081c600f000c040e142c503000760f0152418007d4500980c400e0000f0000d17820000005004d40b016038094802111050041c101072690109590350422030a081c9140710807410f08200e2151312035504042d215502400881c0c15642c1e001525050711001c0034240c0381500000125403003039101d00122450000540314005038868901c1c0014040d1004403006c44103404003040100e45607003400d910603614544107513202d1410076002d0190154040040c0000c514040c20759000803c00d0002505060148402d00400012580250706c03007403040c48a20310620700d995494000c65903400c540e42001e2981c0d400c140000303001c20082d0095a015503401000f54813070040c040400440803030640001c1030712090b50000800d503500d82d44a0142c0001c246924544464079040611140f012150f01c4140114a00141c1502c01003850054 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 43826290 1250 43825040 43825073
    0x524060a030902010302091507050c090108120c150f01150203030c03040807260702040f060305031207050d05010f030210020a020f060c0109021302090a0b070506040602030601120c0306080106090504 87
    0xd482280b500040700240180482c05810850303812800c0780d42d40c03403c0040d1901c940f03d102150b114081180902107080400e00ca41035642e0f014401956041b40908090200402408110359440301440c0e20405800c1d0180e6040008881c218014441d00e1640c104a544041c02c5000031440e60400107a011a28840103002501c03207003010844108000030b801c8028104410346041041c054084503880c83e003584040c100301d04c07562900c03201010185070341c0501011280c20102460500c18003141d400c4444400800100c1045010400c11000701c8191003028064107006034401072260541c4180042c00760003141180556208440c09401aa2041d0050702d0310007050700c201d074692002c888028098149404000e6008404030103445400c005540a00710103941240c49620b2541d4548a5600750720900798050455045800003401181d01a001150044410314182d040d40c0c0c01d65241800700c030086043c1e400080d8603035108004921090180c140506100c120801c454100b60f5218a44011100c01 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 43827540 1250 43826290 43826297
    0x90c05090f0d0b0403050a090509090a0201050a110601030507060906020c1012060e01120605010608090606041802060a0801060909020a0504180b0901080102190804050d0305060f0a090524060a 84
    0x7814219115503180004195000c0e11109207400e1519029143c0e4020354520400a40e009000182c7c0b498000c04a90041c101b05010b01204c41040d001141c40d42d00c2181100140030381810080000b4604010050096001d40b000c0d01e032550900c0750040a140007540480304660200c821846640d0b00c688008030058550305000e0301e80081c1c0324225000c0c241e654410080350074000000501c3c03052f0400c1c40720106100c1c0301d0030000e40c2c3e01c80320f0648055106441103100c3e50b101100144840c20668001e0701c0d4100e500b01d2010800c00c0da64000741803584405280400101c3d441c004012542e04441c1b841c001e4901c00505500303140f080e002c0206180501e214540b4005040e00509000c1c04450380f1254890a001d0400a110742c1c60b0202c180c080d61051000099407000000f0400c0010b100300d182c117005640c4100544114070400e0800ca010301006001607522008100c002d1b40f26a46640d1010003c0440140110382890080b02c0700003510501e0400303442099028032072418540e590720407102600d4480c01d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 43828790 1250 43827540 43827559
    0x41112010e01020a02030d06170307080706140703140127050406060806010f0f050f0a0e0702010e011e060510050307050a1110022205090a020702060705030301120c090c0509 76
    0xa000d0901000c03094455480041c40c01d16899003c4007c00c155000104203200040e40c074800c000b0094580320040c01c2e290030501402002034240300041a965010351008144d55003c0e06c1144410030054440c840400d41d1010400c0c0c40d801e41000580c01042244000520f0b05601501440580741c00413031141c6540d541d500143c20054158018400340040f6001c4030881e684401240703440040e5406a40c14001c1c02c400005490b16054403406202c98001d03006550341d80c5044042841d8040251258065540383d0b02507001c10b560034820034082c000070607905446045c2c1131460000b1540c9a0304018001c0c1905d01d220740c46503421104484d004030191810594450400c0c07011614aa031850890007540103400e80d40d1b000c040030350040d2603400d54a0f182400c00750610002040c1140c11441010b80100c64200010441d40040e8040e2034071a0001c0c108078688104ca13a66142550300903007148102c0c403509411f040034049010065000f410304614208002c091540014259020318104640b0408104 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 43830040 1250 43828790 43828819
    0xf06031506060a020307060e0d020f01270201020109020d03051306050f1204050a0507030804090b0907020a060e0304120c0e060111070306180503030703060503161a090d0b040312050f0411 82
    0x2c1080380e1b0032a070002002c0002e07010711200345484906949880b0018401c2c00040c1031802c0c01031240800d020105a202c0350703045952902c840b25900c3c0c1000c00e0b410340d56180c00071405a141c03013a5807207030366100341e40742661140454100074100d80c2542101080201c01e10840d104104800212500210001d02110090b80e641c0380041c40c2423001c0000402c140103000000080103945c40c0600305580d00807206000200158050140c0004102e035041c0050b4403a85150002c200c0b258000301002040c00c065078079150b00d441c02240d15a002410031655114012001c201c2c550f80d10340c2041c0c11070403d01e4076924201182c44110759070031483c080507101540c0e40d10700701c1c02801e4010280185560140540c3d840f0f140055000d00181568030840d402402041240702e500e00030400b00100362000c2c1da400714045017950720300070307030581000607001d03040181c40b1401800f00d100000d08501c2103100760b48105031000c0f5140400181c0300040c1c800010888142d0522001847c0c003400054180d80540c1c4d540c00e85e12a4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 43831290 1250 43830040 43830043
    0x71206020415023717190207030b010503060402180a0f0905030903060708070903031101060b070b0405010f1e051e010909020108060303030c0405100201060504060e0f06031506060a02 80
    0x5582c002c0c480c50003001000300c00240c010800344803506922012540c0c49802d04820084401480034001080d81d11030851400120754015820212094009007414981d0b034508a0385000741c030880c1100541c0c040c10040040241614109016002c1500605803d06089c0e000c2651000d2025009600d4400d15000032490411580051400e04025a061102048074144641c0360b6010703080b001d019002c5c2e0340010315820700901c1c42e40e020b85c03031541d41ca407274071455510100c580300e0304181046034079502e854001810f51400006089010700031040090681454039001d4212440e03a608a25000d08200001c0016054207110060512840e034012031f0969829000c462034042c2030000f07000c00c241040001c519201c00d41c2c064203509100785c17106010f540342c407403c050385d80c041116503103485141000140440d0504400300028803517503000115215441e4800070b400d640154008004030b000d000c040000c0003c00c05c00341d68005074160054402080070340c85d01100d4041c0180790b240202800a40210010310 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 43832540 1250 43831290 43831297
    0x210304170c0304030f050d030c02030901051602060f13060c020a060f02010b120607090602060c030109090c0305030c0c0f0d050606010305100320090c12130204020706050a06050a090e07120602 84
    0x1e44400d5036036554032484c007507a0543c0d0010b03003a1014860b040040910034003070f200759011500c490300110b0500300720800440365644400700841050701940c0c6000011303260078016107a420210242c498954605550507a81d2042d0f40e40101c042020b907d500f500941ca03a1148042038940c24034000e03004240c810b200364090250049902e8005480401c10902c2800c0890018041c9070310381c3d103201d0259038a0710100d03a02c0805071094549080c082004120b0b03030205a00c4103481d140b0407519058404d549481e6a829504548221900f940041000004500e0071400e000c021880895060380801d100791a0329075961f0b0010580b6051555960214481c0070b040c41c40100117541c03020b05e17030340c421910f03018501000c000840c0d06805802c0d56404070b2086400a81a900350380007104802c13a0582e2509408800701c249088281d170011760030850382e8085151405050f1044011083c04a0708918000600001c845986e108840c4186042c000460070308000c19248100c2e0000c040d140000901800c110f0b000b4030 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 43833790 1250 43832540 43832557
    0x103020a030e0f0a0302010c09030b06090402030a050d0f09051005030a0c02030d020406091a040e0a0207111008061002061e420303070b0a020d061703040821030417 72
    0x3c41c00095010003c00018040d0225200e035009200710040c0f1201928000c1d024007000340318007000c40009000381051040c466005000034200d81800742581c40e010700700145c607401000000c458595294503141c101031108005c007000e0760703d02d8001c41c02d480028030b00e001c0a030400304082d440340810100c41d407080003520a01600c9030385c21942c407030381c0b2003001d02294600e10403102e40c610000110040c400400c3c043d40d013101c90002202039965900210f0800030351081104555502c1000e65032959501c4500b9a00100301040c0c88030031581c18640c0030040d25050900110086600110412825a840717010100c8010740b1315052400c0b50b2600e0b81d200300310340850000b00c84803800ea000100a000805440b101408800c2d141c0c080c1c02010030010f01d9100c1c8600c1401408881115010418851903035004140040c00b10000041d816111284480f480d44d40071024292544046014091400c040c0a02d80035042055148400c40c00001081300c018013004002074905001040b800c440c0c554448202c5a03a40d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 43835040 1250 43833790 43833793
    0x12a0c05070e1303030506030f030a0c03090905010e01030311120a0e030703020607030e090903090a0509150405090706020d022107020111060702060a110304030c170d06032001020610050103020a030e 87
    0x70f18080c40a0080c802c041001500000d00b00404a429400d01044048014030004042c5141c0144220152250100080c0031020003907804000141000640f096501070050364186600ca075145060080a00c0315103104001c10340c01c11000e200386001d0701400c03164038085a040c0304071003d00001c00281081446d40c00650440f0000035050101503010103a5002d402c3c003120007c0c0b254940303594840e50b0f13004984840d03404c540d8401041c0410310305003000940c03007102c4d0415070001c48049008281681c800340c8080b9a6075000c907206124050b01030240c4030109010b403004141403076a1421440b003020910403d07184c00c0fa40060280c095911488240d2540c81001007201e1140c185510001d664803c01c80304001a5882d04030700c3c0c0702d207180000c226400746e50113568a424111881d240c031180044000e481c880744d820204401000300c4000d000d114011805000d40e444619240c103c1c003160442c2006580d811034009200300843d1400d002001c406840d0286401625070014a03000c0e00200b140e0401c5505030b = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 43836290 1250 43835040 43835069
    0xd08070201141612090b01050307061103120a0902180906130c050909120c0c09070306080c011805040c051e0703020a0609020105070c030b041202070506040902070602040e0c030405012a0c0507 84
    0xc1c070041b203502504036002a400c03140302c1c41d0f986004484440e1070104044c5e0a1304104401800c0c8035441e010300e604160700c01d100147d40c84a03940050702e8280103407810030110001d54100000084180286c9034081c410811a054003502e80e0384030051074a050150030302c1062200045404242c04100c0d1202174440401141e030744a103403000850f41c0e141d0000c0c14a10800c14000041c070028400e00484084030035483c001c040d100900d100548a0b00258260480c3d081c1d00031000280c1e503075a50048400f03054050300c425079a8032a860300e00210201d0504a62040c00c0100442800260700182820030190452000036680040c1d20049030540704500001c0d041c50540e500200a0280e050612805944900b411071030710b08034004241d031202e0661281a0303220609220412490015400071b0000c18032500c2d00501e030079100c030030708402c2410a86111078024000b200300400c01c8002d108000a811000b1100810200d80002c1e0300310385940100e06008100941034004208101048020064040407425819 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 43837540 1250 43836290 43836293
    0x20913080304140708010c0e0906030c13020d05010807050102120a0c05030403150f051b0a020f120306011206030f0303020702030309030604060b01020c04330b0a020d0807020114161209 81
    0xb01003a0302c1c0360510f070380c02280c10000c0c0180051044003405107480d121407001444480400050b10402000f550b094003400e42982c14076078607950741c0c010b05075003031b14016200c265203880041103801c142c00c01081c0e0b500116050040303a80000b114400c800c00f14080307590b500c507001000c46800d540440700511921000c1404000c020300110000f682c404052010030415901e45c2d0b040055410a96085100c400d455105d0060143c01c02d0061a04584500464402201000300940b528030703060401210142d000c4180042c42d13034008090403802c10305003000e0041a0441d1250000b0081c041c81c002c040c9540001c1c02c17402c5407404e100380c0e40c404000405585071881d0500304100900001c80d2854014010180900c06928240c8102141258a006100922110802c51006070022540b01540c4100c1c0000001091101000100070160065002d0808005030a0024105440150040082da4144102880c1c1e0302c04045c02e140c0d04c141118508a00c88000c2502600c110b00035580f06074030141800704010 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 43838790 1250 43837540 43837553
    0x6090804030605130b040b0603150103061506080103080a0e010306030203030a090311120303040f1109040c030b1005090403030b060d09060204150305070c0b040309360216020913080304 81
    0xc201e03406501e00303010998440e079104194a20f000c00041030b920020002c2404a8421682c2c1da5005a01504860455044640d41c82a01200342c1c0200d6081b9164034110060407211000e00000740942d0134101000d50450b62804024001e09a22100300300c007815090280781e01c40c0e0014401960081c0642e66108030181008001880e0350009980c10300d8090b0b0f2408080c2440c001814030074100340081c43c01c60711555142c1490380b50b0200c0039180e0305101d00e41007041c0d42da99848240207900c02d20180203d64510728140307074119001801c0c84038070081150100304036120301f80d40319446a40752800203100b10320303000028040c0c0103c1503c040307110710b092014810080c0c19401801602da803241c08030703215001c1c171800303c0039101d0440340e1340300045c01e01301c07404005024a000c00ea00203200742400d9100a4075042d001d402540714000301540303c40104000f000745081d62803c82c05810003c203080d45400300003403407040309143d00742d0000d0007007941800242c850000711415050050b030100707803140d07a03040906082 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 43840040 1250 43838790 43838797
    0x18020a02011a010c02061c05010b030f0a060e01050d0c031202160f0302060901120b0303070605071808060c0a02070e09010c0906030207020a090902060910090602150f0a18060908 78
    0x1800558038000d440c401c8845215900078a010059403180c2080c0f40076404d00c070143c1c021000c0090070840c40f842e00e0400070260f002e0503020f00840d011840d16842c104164200a1070050030001106103400c07001c2c002c1c0a4444e0019066440554094003402401d24007002840c0391980003618589042c08250900c0b540444d0201001c8010780380350854a0322034401c074800e400c4a20009610100c100036003119540110328400c20700842d40c000281101d1030001080c1141d120900440780f11344d40e0010001102e070011841403490701c100e8031650071503081014507592100c020b030900420300e101080c40c0c44c0062003040003501038102e03c00e03090624244031032410f0103000c0c410345041c0032427461100828580c0c8244252005250000d01401c446880d1102150003040d0000c0e059070080c40c00c0140d030216403a0051901c01c01d000540d00d90a072075260081c001d0404209580036481914800b0500411130b02da840c81a411001003e00080d55000b100c0e81c20300302100c020001000d841c05e240800c802e020031503014 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 43841290 1250 43840040 43840057
    0x60f09011b060b0a06030510120203070305030a030518010b01121109030708030307020f06130f030302090d11090108011e0b1c080406020118030219030e0a0e04060b0f01081b041802 79
    0x144ca038060380b5644140c0c01c4d03440c2203c0040c1c1015004608206540c420031400d01d5182c0007a058070303880c1d03491340c448d98256400b000e50f40022a860307070240103030201880104242601a80300030007212103558002800d140c0560764080007503071125000750369803803007804490310500000c00301c524045d80c42c42d4440e01c9070404c460040140c010002d11203541900810107620070100000e4040041c10190368034454813201c0d6005900b01a03091041030056100c021103c907856005d5480c0417440000035082200000c1f050b08100c0c041d03410600021010020f02080d50400f81c1c8060b000310b0300780f4030203001c40d10030300d01301c040c401503141c5440c0903005020a140051081d652070b54001d010250001604118204a011000b001640001e080f60990006078504189240c0310f86010000c0e050f41e007001546110350ba420100244400b41d041c00304001d000c0c8260500381200396030a943c0b00b0b00f22000640078003030040c010850b1000c082540104201e10804540c06414000007a141d50080c2418210007504003000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 43842540 1250 43841290 43841299
    0x30b12011a01020a12080703060f06081501020f0d0c0f0203190c1a0306060a09050a06020d0e040b010e10020a050109030f020105060904200307081209100806060f09011b060b 76
    0x280c01c107510200e80d01440c1c5412145516584600341003c650303800e801499a810582d0341d1b240402c810141c03540d8400101078070b40d03c0340d820341032426122802e1001c240b1030030306540c81920075000111020a950a40c140325050422500c9043d040482c400070980c0f000960502900310090803104401001041c064000e0341403940858072240001030503900e0750900f0300349150601c0042c00c140b44c094020a405209841c00c10341990355080807580d50301030b175007001d001344e00508520004182c2c031030480510f00b0ba044a0070300900c00c1d100e00203041d1401c03170200035004d08820091400340a00820a010f0602e61040080003600303032a013002889080c050203000c00650810011030400d03e40012414000d54010b4407100e440c0d101489000105524200e20036054003130200c2c0001c640c42c1c00d0019482c00340304400358603900c0d48603008112220881943c09414014660301b0b00444fd11070100b81c0f110f00703000106013640e880100e001070f6050741081201c00c1e42d1f03410807080003080ac4a141c1015003203001c10744 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 43843790 1250 43842540 43842581
    0xd24051f0305030409020c0c0a0305030a0320190c050607030212010e07020d03020a0c02060408072105030406080604060b18040c020d0503041e0209070f0909060b030610030b1201 78
    0x46095803121003034403000d0300540c401c3c401840000010b40c020160485e00030200d441240c403203008104841c1c3d080d03005035155000400c0080e401c54060049010f0b000081ea002c4141070040341c040c000c5030140b51645265200c8103103012055074081c0007000c441c00c2c0c201046511500d417902009001e503103c4402e4080c2c849a4a00002e601004030704080d004070301a8014000c7d08205110890094100c00301c0201040542074070785000d17848010050008d01450780282290b6030602140c1070302101c0740c22030480c0c1071030041c000c940480c0c808000d0741d080e038419103004241c1c2c2e161000001c0140240380c10980c110f0900046143ca903000100491710707580030541d400d1024001e182c4082e0389680c0d8061041001c10b0f420800103001a00b6610042e40042104d0015102413000e42c0201e41721706030484101b00401e03a91743c020a8000c0e0011441e0b0020002d0040c24403031141011003c3e10b07180005031505006643c40840c01c0307440350082d004119850005001090120740f00c403003c0740139140c1c028240071041e0645 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 43845040 1250 43843790 43843831
    0x6010906150e060a0e030c0607140105011413020c120f070302010605010f0c150e03070506090105090703030c030e0411130302040510030803070f05190c0203060907060e0d2405 77
    0x405041d80412001443c50342041c1c0d54090a07aa0703120300c1380600d5810f004400a508160b5984c002600999018451340b010000c2e80103505401c582c07040e0050102d404845240d84c14030b40d0340b07864014064440b10720150701e82c080c03070258914140307101d03100710040d0b1800720b010780007045a0710103490028020741c02806030f2640c0d00010350300d034001d800007200021402c6103000301007440c020b019039040d18100400150088610185e07801c46d000700f00e04031150b800c04018880003410902402da080b01491018056991456501500d00002c00c40000c061017024241b200c000e0f5a158481e03d0030710020380c0401d5448981c00d039050351400c024042248210302d07280124545444030740c0607105030b903400001513186481d11481034542101904583c41000010410300e40c0d030522031607889081d144540c48600c8a1001441054140030005000840640c492501008107c0d800b0031403000e4640f061b82d0000c40102641001c1e102c00b04102e03810b621000e0940d808040c500751a80c0003030321503690b0880007120074402 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 43846290 1250 43845040 43845047
    0x3060f0601020c040b0112020a0c170406120f0e06010611010609110d090203070b0c03030a0c050309060402040c170c03090d0207030b0604050c0d09150510080a140304080601090615 79
    0x9a80e03150060f44400d4003140203080c07585c41034494440505140e400040300ca0104400e91784021080d0300058131182c0640100441c144850311111045031034035050504003500142007401100700e13404d402e5140da103401540b00745a8442040400080241c401d150303110380c0007819402a40f400c8280790340ca890400121210184101c1941104001c050b1349000144041d400282c0b40d445416a494002c5a00014082d410600200211070741e400c0a95105c1ca40248100b04542d480d0034800d05002d401c0013001041e44001c24019441981110009141420a2021035140f41c4480c1110a02003042d814054002d4510000d0351107505e80c041181e810052000d0202c0e15400300d031000504034103074000130400c03625042d0411640480d5401c012070501d82e03498014801d5450780c10080c2c580401002264800501d50f005451380050300036110b1940030b00c1d041c1c1c05592440c600c000a400700c00c040402e442c103c1414404c92f40280303c00e034100d41981d61100d0810005113494030481c8015254800500070340d030f01 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 43847540 1250 43846290 43846321
    0xa060b10090605040911190c02010e0402120f22080324060f0c12120601020601060305010b0706020d091a01150c0314070f1b05091b0901120902030d0e0306 68
    0x54a81d6034500785445e120b0070300043e11988580004840c018003280101c2c0d1054501c120a4110075505d101c90452507000151042e00c402c0380c0380c0d02540c01004056038402c28603002a0b042541490f4a500307595880180d8445909900300103241c8504104000d001e115144002c1c6019980003488010076100600034861300e00c2c04070b4492504100d0900440ca41c42d04030101400e00694040d09603221302d901c580116410380d0083c0320407024a8081c60038004103580c10030007940506514202040207506040f540e840e0360050b403200800340c0e0740010342a11100415086640402e0b400401c0180c0d248504041e00c0e14100c0900820003860200316202c0b049900c00c5001b031803d80d405490f6421440c40300e400341209544079440559a80b0855403900000a848001c2c2103c0b640d5601c0414408508081c02c100c88000040c000a8141d0f40d591115503103e0409800c54804100900303103a004c1000700c595034000380c83c5400340a503241c0030fa00d20030b050940d08107280140a48084003541d4143d507842d041001c0d500c0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 43848790 1250 43847540 43847549
    0x70f050904030c050118060921050f0702010e06040306060e090a0b0a0908090919060603090203030a051b0a030309110d0b040209063015070c03140c0a060b1009 70
    0x300c400c00724020074014103091042e00d000304d00118812203900510803480219000c210b40031075607613594209100d07180803a403d6806101035212901c10701e0713540c014118024034001402d44035002030100c1c110780c00381007401403501f80030741a26200c0b50b980c181440204658854021149880c90010307514840105601c00c4060381301172a00000d8450001c598011311503000120f65901c400c0040c60503c0e41d03000c00c0c0341d10598040c1d03200841d0640d08020758080c2d44142c6d000c08140f605004006006a5001c01541c0307202400c3e20f40309456054050307041210000075007030b9002c207008850701d10045c5070707043d00480032060041e2039995103031401d84140007444a240c0e41c080c0007280c2010100f0300500e414070300d2a4000900820a032101d8000d0344488000b40e54100c84990080201207070740d100e0b1181800806c0321100f03004003404180c03410050213091880b640600500f0401c60148285002940d401500c207040c440c5012602d11500600d014402851017002203442a4001c0241c40b055034420116081034a = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 43850040 1250 43848790 43848799
    0x90608060f040b0c0306010c0203011a010e0102030c0303010306051b070609050705090103050606040507031b020a05060705040303080f0601140f0318070501090b0f070b0c03070807050f1605070506030a020c070f05 93
    0x10713514100390540315000584280c0c100320400038420096502401102407000c8420302100c07141c035010307002402c05441c47e408107055410900c0410312040300400ac0d0f81c1101d400a101207003d9139944204c1c41c47c1c2e04140c1c1c8004000002064003020b01403036501898240b4840d1040302d01854440301040120b41092000401c6903100000080d0681400d80103190130480c0c6040106004503c2c613200b00c00145a03080c0c0c800160700c004c41074410f21500700305c01030b040206824400d00c4c05042d13440082414400a2034191284004030200e5a43d9218800e50618090400b449a4458010741145000b0b03500a90703484442d0201ea4125250310000460081c08a0300c05031101039401d858030001d40310540042c600c4e40c045180601001011030305011086100b09911000596207243c203910103000500050912820007805100301c10307031140c000088030304180008600b5940080b0920380035161990b950082a0400008001d110304804643c0140110360814016900c01e80d44500f081d44034040c81b44240c0c1e620 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 43851290 1250 43850040 43850063
    0xd111902010f030605060f090108010b03041e0f06050c03190b0f040902040f02040e041203020415120207150b030c030f0309210304030b0402180f040308070207080601090608060f04 79
    0x10741c05001c0080e00148a401c01041c00359442000460302e80000390000a203050000d8070b840ca96a0000e603d07030140c400d850555040d03041c0754590411050901228185d0081841c1900b400e001c0303000d18141c107599200b203040c402c6203009000c40b8242d0300150f440700d400981140c11041080342d0780c003a007034840c400a0310040410030943e080101500c0444404e0340c2060359540251101c82c9140002e1028000480c080060782c20b00717280c140a2400c0c0c040090041510502092041040c6000c03501180c1100d49840100c000c03030188d100c030083c030801c0c000030400400016480b075048400c1c0c00c424981401101075032903480a0605240e11800071402c100c032250810090814cc3c1e00d0003070020980c1e001d0900c0c294407101c81200c081071443e40280c00a803062803d41c4100411854180e003010510004030800020608100da0400040300340907200a0a101c040300000302194420020000100144402c482555075140480d0005080780d0080c21843d0140c080040c1140ca429004035009540c00f440d050070 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 43852540 1250 43851290 43851293
    0xc1706060c0d0e13020c010203100b1606020702060904020c0c09090f07180b1206060a0b120f18011409070905090a03120b1e030c0a12320d1119 63
    0x2440d80003100fa0b503600c41c0e00141e4132020420548007030320564003150300044e41d900b845210701d01030050543c00700c84c14103403c20101340b464074411290007800f40c0c0420003585445042c80040c2260180c1000f50b03800c01c0c404921200d00000014245445410941d512012502e6245685498400e80e4802d40c2c859400b200d0204031400420304550310120b4070706800102e04405000140c0e043c0020103101c1c80e0369109600707102040c90807910901c000c101588100c1d01e00042100904100302c001000f1070141c400700d1001410740204099002c503404414030007040041203011503040b030514107480c1e01c1c0e854800c1c2d0502265065032842a1030207030f02844003c140c1c0b1141ca03501112072640c07100d85950f549480320a01034107a250f280d020f0401001181c001100c00c2c00580515141085240e1243d02c1154208002c000d20700360210305040068100481c542207131014000c1c203107030040011500050b02c250884c1000c1c11075000c0b0722512034291070350f9120071203d592086103698210040140011142c035607207000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 43853790 1250 43852540 43852547
    0x150b090303072003010c080703050106030c090509060a080f0307060f0c02210705030f0301090b0a032d02030703030f0207080607080f15091006121a0415090c1706060c0d 74
    0x40d4000f09035440030020b0400980440d003514a074069080115000c0c8007480040764040c0a418003401591901300000d008141c001480703000f071445090b00070303885030022400c941c81d41011280034090030400c0341c420a058400d101e03500e9005c543c0c2501c8091a001107a19209414000c8010804050380103003030400c01940c401050080305401000855420002c80001450920240c8202c4800c0b034001038a83d850030901000742d842048250303200d02d1002c5021720028100c003038041c87c01031242c811080072180554020224000e03030340002c1d5040c8503402001003059807100da8100e0b1400300303500b42e80580baa5074581a035200e205461080104061100140d042c0d6002c1116580c00080c01011480140301803020812401c0e064640d0002e91208071418072142e0380000c4d559440e0400c6040400c01c407800c60001046d1100c0909030144610b03100c800d000250f0207070b41c40703000140c14240400c0020f02040540074110552904001e10000310180000f54249422001d641d0521790b5940603003d42c203140f040c101e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 43855040 1250 43853790 43853813
    0x31e070302060a1e0e0f04091203020306060403020607050714060403081e07021008180316080c0304030c0603060504110405010c0605060301060b0703080f13080d020703050904050901150b09030307 86
    0x20f080141c46440721200d10000454a00d04a101c0e40303036060016124420f1103425030b40c5c0e001050140b401c003082c26002451100f140f01100003079190060b125250f44000600d280702c3e56002a50141020981e00103000004c10900108c0d200035032102d119100081c1804054041c0d4880074100d04414030807401841040e0f4280480110820000c0349807c00c035900140180d4800181840000d04c24020081e40c2101140d041e01d4000d4054000c5003407441c0754148000310b004800004240610108028803139034000c0003550301640d88000c903100107a0311420010018080303445a50321540c02d000041d03d0520b0080100c41c2559010b039120036035051542c540c080600001341005805650712880050b01c405950f020703002091090f5038030400e03030400b0010150a50005000e1810711a1142c0c103010001c0e0490003101c80d4441080000341e01e07050142002d54146c0201c0c5c0d0346a0300320b07092500300460154103610040309104105d0403652019100c81112141d4001d00e103402e509513004006900100f460401403 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 43856290 1250 43855040 43855057
    0x9010f08060103030e0d0b0a1a120712140d05070302120f03040803040f080307170603070602070e090f16060224060d02060903031201170606010c120e030a0b06031e07030206 76
    0x181c0b0100d00b03141d4600c7c1a10004517a040b55003540c074000c2c00c1d89200c20441c8014030720400c40d1070048081240c02e01a0301c03078404d44a10f00c010003003180c0003c1080001034440804100302c109441340032083c2c0001503c544c2c4000070440050044000c0c5414010040050b0b50003071005c01452400d56440c2c0d5503900c040d52018000352500402c00100e0000100c2100003188541c480703645010110010f10034450008402401d031038402e400840050080c40d600003808012100e00d110442c640b91144c0c83c4143c00c01070340c00e082e07001e81e0142c00c180c40d507039006031440c140807111603a007201c8224900000440c1c0b804642501c0c0e034040c2c0042c101103150381c81d20030481000e403030000700782e14688400b09001a1a582c00380600103d00d15540c401045200d5222030070b1800d251026000d480e4504d0190700080009500323201c001c00038204040c0c01c03108203200d03c01414401c0710107070490f10481d00604004c0c803982c174200d900c988248544d0700325101200c0f251a00030303c02d0961000615529055508001040d0480c103607 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 43857540 1250 43856290 43856299
    0x809190204020c010e031c020906071205070501060303050a080106020c091519090e010c05071a1509040c180b0105190212040e0907060e0102060f10050604080c09010f08060103030e 79
    0x1060080002849070700300b009402c0004590303d0007100711802e036080d0001110794007544140120a05612b9083c11159031503440701d47c01c038103015490130680e05c90103010300c068005d6203011004410150400020003c8101c0e94644030216070f40d80200700c0c0e0b1811034040c4a908291072401103405020a84080c819058004048113450280c3c100e451101d00b603298003c04555071602c03101503400d0021320405c2241c440c60f18180d850029107403240d6a007004841002c8140090440016140b0aa0b40b40a00550600101403080030700b0541010f1401040501943c07078000a6800d0f00c0c1ea01c12020310030310120200c1a101c09040c00421104401c07050310707614070304080d8091860000f4491034248001d03c050a80d00802d808142448100703103290074150b03004102801000c07414500c05a80005030340f42d0107540b10703140c680c0032b550303140c5141c131042196409079401c080003140218400c4008240da240b500c405031860219030f03030780c3e190756012a2600d00c91041c090304200c0041c80070078440c00c0c454945050240 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 43858790 1250 43857540 43857547
    0xf060d0f030e0307090f0b120616050306031006030809030c0306070c0212010e01060f031203050f010302090907030b070504030515060108010b03090304050d030f0e0f09070302090102010e1b0907080919020402 91
    0xc4017202a541c4880903000350300d80d91182c4008a00d07055000020824a12004107150b1900400a90729190380c085210144100400024829078003004442c0783d40040e40418001c1507603034507203913210741c0140644e10704c03900400102c404c0c0d07400e00040c1180324200990340c23010030706003640034030610a01100b511903080d500e40c0c0b102010030600340079000c000c21080200210392460b5080000b40c10b810900f1820130581803505019100800d43c6155042d01c2c0c0440c2e407c0ca0648880c42d5540c5000303166800104030b88042010042c40ca60800302400c00c40e03018005850440750315081700114107404882c1d4034003156441c40140081d01e150300c041c5a200394072000b120f03e8140c446000401241c418101140040c0c117842a000c036440e8070460704c01074800181c2d50003d81c405102c2c0010000da4004126200305940481c01a02a038400d400032407065610034190749440c0c0300360403029002400d07400c1060080601c0d401090b0380d80d10400d9528440c01ca080041e102481002160490b4a65441c0050303034172580a0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 43860040 1250 43858790 43858799
    0x203120103050307020108010806060105040b0a0509090106031a03030403050604110307030f05030403060e0c100311090a08150610050403030305070507020612011712070206030406060e0c030f060d0f030e0307 91
    0xa104060107940248011034542c40c0b20300c001051088160800c1000e50084010311100380d0700b00f002c0c0c2d000d032840303c0e40541d1550044c140407501809600c58176a070001040f00001410768056000c6c1e52078440200f446148101e0070010b00d07030b80c1d1080c0d03c8000e000354407040000f00032070720907d000c1d40301e40d100a040e101d01696944070020400703c0c2c0b800649072504009003c1040001a12800c02d0008005001d0700c5101d0a40000454140001c0304040900d0b4640d605018040a2002222003068000740312904280c0c41d02180b03a030303d0544c0d4494010080c1e103200414101d01c0c1070242e00302c4002095540e18078050461740c0440151a01a0010051240600c60f034001a642d880c094003107608580200041985800d000c6100405208441601c980200013407801c00200002203400b0640c05441484e0740340c07103501d4500001c5c032141d81b000300c84460390300a12401860b1000214040d80e866070b4039200035164141008941a0105402049040501e4071035001078050700a0030b000c0301c80141946c103c20f070346 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 43861290 1250 43860040 43860067
    0x906090603260408240105010c0b0a0c02030405030307030323130602090a090e01050601080c0406050a050c071d04030e04050c121e100512030a05030705070c080109081c0c050306100203 81
    0x610050031950f02120840204c003807040308506d0050009181036141d80505440383e2840d084060810303d00103440d580030000450003041240c008040150803a80c0e10178650a008004098508500c825541501e04400216a510b060750703000d44c006928241c41a140c50361000025400100d200e500081c2482c0002050740580c031138503d500700e8510010525240c0403000602c4907a00402c0611051b9081c0410300c0441c0c2d0110030f41e41014102d0610a40c0d592000c00800e00c1c10107030707500070001c5e410078202c0d05002c84400210316020324032070b0325540f03521002c407810231054910850300d0106079101130110b07002603504030501c140c1040c2d500007680341c1448100c410085400c0d044800900c444502c2104000e141002c044100704e8011802c003943c18400c10b0000100644006070600c410800c000c40c1c40c4c0e051000700c1c83c8840c0200010002049204821324110079141c0000d0126520070381000550080c00100340240c0c49055000e68a41d0b1859841c44104078181c1c07010006007003107100501c01000c100351b0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 43862540 1250 43861290 43861303
    0x50304030b01030b0f0c0a05090a0e0a140c0403030f030207060b0414010807080a020a0311031e07050109081501060503100302030f06010305010b010f0c02060d091a010906090603260408 81
    0x99008030065030450800d101d04c0000070341907610125050003048106191801900c407480340394030300140d07a16440000103c40c040740d5001b0700004040c080500c00950499401000303080c425841d4440c441e07a8103120900140039501c40580800c0200031199242d92190f8010030400d44245000210444440086001c45012169510f1113000c12001845100d10401480000f002e4140040070245000c1e40030980703c1a02c1d200003010f440d2441e1703044850b0350382032105850307189248083c0c842c0843c441103019990b150b10321405010821556020494150129054211201c00030389044241d181550841d80c40d40014a11540700136215400710050740c0510000c20171402600090015504505020382141d000c009040d0502040711030440043750868000982c00c0d4040710100c0e00c40c0c01328810000a440000c60080c105040c0c0d00104200b84a0742c401c03907060394100882000030541b030703e8589080b1076580c0805007404400c4d41580700b0450740014a14106140c440c1c0141c101a80c4400301c0d0710301407 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 43863790 1250 43862540 43862543
    0x3020f030403020a02030f0a02010e0d080403021e0103050106050423031c03090c0506090a0314010b060c06040b070201060f050d05030d0203010b0d0b030c010f0503040c1e0503010608120a1b05030403 87
    0x200b00300c60140175854100400101d00054002078840a041c41d4006010941d04c44e050502455030a000368041c085034109440c0250740203003078807544c02c9103154201440380110880d180400d00e4840081480e0b4412016242581c50002454080c9c9940130f4410034540480d46070164148901c2440242001c801e00031001c0b0800c0548002c503074035049141921600c400c5808c07a80c02220f05003d4000181e4070315008004480d08900400e100c0b4201032a0f13a4050502848110707004400040c041c864150001a128031650140700c070660300c4d460b2080f04a0980d007452044075403071465040b06000b0382c980408000800c0780b281007100d00e1310700031018400591700240e00c850810000802d9451243d4641d0142c41c1100908034050420b1055100001c1c02c3e0b00c0c1170009030b07402c0000100c0090304110303030740441c02e002d00b0001445080d602c000030122030810b021030003118025420100300040a06c00003c249030f00030044031186080c80000c0c04101d0762850100d0f0483d4601c0c042c04607030004248107000800155 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 43865040 1250 43863790 43863793
    0x1b020a0f06030903030e010e070608130f08031911030105100216030303020405090109020f0a030f0914030a02010e01020909010e13080c0606040b1008060f040603140604060605030610060f03020f03040302 89
    0xd0b03c40c100601224059882e02020340d0502d2802c0c0c0c4490004941c50003611280d007003d4246490310380b8081698161090020803d051010f90007041c0300505010f580310304122001d801411003124203a405550084c0b1106400c0e039004d00040c03105142c01e9642c9005d0507954030442d80c0102c1c5400c024440c00c0c80c0c2d580190302081d4001400d004c1d5081c10701a1034050006408250f14121031000440440d1013140c2c815020155540303009400c11006403c030300c56440e00400c014101c0713092404d01036165400070701c1d00c0380558607041000e0807595045c000d4a0710a0710051040429030320386010070030341e240e00608200510100c4824040080c2600e070242c0140a195801083c982c42e04100344011600c291180e648249040086003400f154008107031540205d0a0340e800d40220320301c9012a01a040f550401450460740d051100400d810000309140300d14010343c000e118040d5a00141a200c030703810b480d40326076445018400e01880303010b102030303800448540c0740041c034000e256924005113410990f800c074010f = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 43866290 1250 43865040 43865051
    0x908030a0905010c020f03071106160c06020606190905151e0118080c101b030302030f010504050601080403050702130903020a03030e03030c1e04120c09050f04031b020a0f0603 77
    0x40c0802480340700b00042c0e00d80001c00d50b03024900d807480c0c0d823801510300003420080c1e0f01d101c00c14035803100c101303880491804080c2101c908103507240002c05c14496000c0e04006118031400035000313191000c1c55045180300d4840303650000d4140207c00006d00002092015032a025548419280c1c0700d6440002100703041024501c1d108182000041600401c075481d502011010441400b001394080380b00301c0d040e1400c5683c51005038582e40140c5200d00100d403041d00b814500c110700c205043d007580086108070700343c2c2044405c584e01c99080200f242c01c00d480712400204402c0009002901500003030803054001451607020500244004050307800d00c0c4421030050b000124407108240d0103006203000300c03900c40003a508520300072140c101d1500414800c104445060001c1c0300400c8180011100038014541002e14110205d00300305007480e1140c4200c2040078035040000b25840301e14030aa81c043da50541e511824485050402d4810f40000c07101039a001c1c1c0d00302800075a00c0a5200f40740010710300398070080740 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 43867540 1250 43866290 43866293
    0x40504020409170711060304030807111e070504050108030a020606100507080d0b01180806060114070803010f060f0c1a0c090d05010c02010f0614060c12070501060906060e0a090c030908030a09 84
    0x110131705074583d031174000d0f007080c000d11002903040405254025103d06d050106076054081c494a8240408604106103199100000c0c03004000303d5424140c80060342e0500450745e907229140d83d02c9c8a07030031400006800080c007040981c501710844d501c0b02d41c140d20f412803d22995407a80344541d4405031840c00e010b5602c9850a2155800850302c2212807081a40008000d140c440340a880b450003c1c441c0741001180100c0c641018205415070b500c00360800103042d203030740e100c0c03014030120180f501401c0c010840c1c0042c07035650300c0e02c03078080024803551002c0c1241d40c4a50200101c0122400546003500c004014010140b0070388410015220050040d4004200d0b1300b158034010382102c005015050410341049020300c2540c5059580260018050390b00070f50710008582d40703d0801c004803910016400c80010140c00b4080d0542008081c0c032450041017080300c0d9100c7d000d980f80c42460481a4000220490400c403c40700d0b544815402c012604020460782c41b5584c405003594012502d2441c031681d20110b500 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 43868790 1250 43867540 43867553
    0x606050a1b0203100f0f05011202030613080405040510031b030b1608040803090a0507080c0301050a1e0c0e0409031206060309080f090d0218071202030606090405040204091707 77
    0x50808080140c0c988581c000c20b48070313071624202500c03483d12040058840326141d4850010542a03200c10032282d6140d4001c000769507070406040e84203225440200d9240f02c910242824041e0388203917020b203451710780803d01c80908002061450010300d1504000045a04e01501c26006186011001110387c01c41c64511000e1501070040317009c000c185007040fa00203030041c40c4503030425040702d40b02c0d0701c03503a039201c2043c138003404d15100030214015408005114480002c0075040d0041c101c2c02130009a49020249084600f04076017a0a2210304400440301d04642c0d902c00da10700c10051030310b00318440c25080807078187c80e014601280081c0000c50540d03600b43c0240310f02da01610591800f4030084140d900d60560074003807404565800340000854070303ca80e450481d002880d56001c1c12035032012400304400c8807004421074406001c9a15922020902d1039244203e07403040100074041d40c00c4c0745401042c00002c1900500880e0490794034603401e408500c174001031411390211456110740d14521407600c01e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 43870040 1250 43868790 43868807
    0x20a0807020309060f09060705030c06090c0402090f061b010c0f030f02030103030c02090a0f05130308072109060b0a030c060210061a09030118060501050103111204060513060606050a 80
    0xc5045400912603d02280d43d03e80c11540c03440e45104010351505580000282e86210310800100b180c0700000d039200c2000808616644a5000041541c1c0084c0403102408160b10400803180d034040401803c040380c500d044005440210641a42503051a40508071107084590341401000851040810003c0080c0d150084d010030604219066040d940b540c3c5d4054817601c1003010092183c404840012051805039210300d058040d0020300740b1003418419018440c1c002d1001d0264005520380c000110002c0c010352a9070010003282c83e100382815504413200c402007116180407038085403220b4480503540d03150072206002d54000c048100c0f01303d213441c00103403801c0c1242645042881c00c101040000d02d00b100702c41c04410760441c078a25682d0300791800090040c400580e054000d0740015213590207101d02a07000d1410303100203032070800000d1032003c42508140111008480201e50010000300010b4441d0019604480141c1000300096a584e03200d10a90300550004400140e01180b40c41c3e800d5801a0b40 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 43871290 1250 43870040 43870051
    0xc09041a071e0c05060112032a0201030f021317030909010b0408011d0c011d0616020a051509100c05030d0219080403021005070e04090b060f120706180b03010603020a08 74
    0x3c40310124960301c260310340f801440b402c031550418018040c149801501d003450b500071055540700099114807642480d508040e0010f074002803914010841003c0a8800c03111501e0310701c000484201c0c42c010714015404850b000c040c1c5035000038008200c00d0b482e680c070b94601030001101c001c0c0d11141006070207805c550007564044030452450002c801050000303ea0b0307208450782860301c4003003069806803540d1285004004140c100c40d00103440c280c100c0320a0324605405d842118101c0190f80e85000b000f030352441003103580c0950b100c10001241e240c507101c60081e440134a941070040901d411a110b4a083d40c02c074000e804603c82d0005400b401026a038139490b03190a0550808841c0e501301342e1002035171060280c24100c030a650354004a044240121815502024002c0040c00b04000c503180c0803200103030585149015103101c1801a0712443e20b204c495500b20b000c2c00040080c0b501d40301c81125581c1c481e009120100ca03401901080e01501980218041d14040d1000342e0303078803106140101a280002d11 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 43872540 1250 43871290 43871297
    0x60507060b1008040807032c011d01052704020408030a0809011a04020c0f060109020a020c1c08070602070f06051e06030d12020f04030501061a04080c09041a071e 71
    0x401c8040b15084103d2030742203030f04002102c1d201c1069203000c0d40e074400070104651032005105030794a040c0f13000d02e901241c020b200fa62856414903036146440403800320958a980400e02c1804603151310201e40748a00c0b16114641c1c24072203031041e02000305040f0703441500100181e4100180c00306003241c228110a80100d204402006415204008807515281c1064860320654001981604540d8200261720b100b0300820266811540c0d41d5048000a42c007010140015026443e00c5231103030f01c1c02c0f009190308484841c0b45400c050501d591407003001d50161008513200b5509202100108007110302c4144d0741c0c7c1c03203900001003a00b0040039000034000300068290300280310004020b0700382c0300411100080c0c100c03420400705400d049400800a405407400c442079110300458008107000054200348110b4007400307801c04026080f03030340c0c5c1c402e20710481c01080200e0340441400c03101c50520081440d4081d001c1d1000c090008520b452040200c0e60a4a1110016904c1c0e0026100d0030b00108207000c84614a04 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 43873790 1250 43872540 43872559
    0x705010914030a08030403032a021e0604060c09081605040b03030a021e0a0f120e01020615010e0f091311010f09121a010305010e010605220c18060507060b 68
    0x40000f582e407502a0001041100e001c8003180030076000b90000900d0041a510803400d070000300007542d442c10042e441a01c014815001d40c407000b00c0e0424014903a582c041c0c400340c5520303540ca072a088090001d1410721030070061045400508120300b480b240404095182c0e5014030945000c041100b91070142500034882e400402c010341c0401e40010706960791110b4417036060141c81e100903610f804d080c81c20300044e21108041c103503d400c00000d1503004019080e1034a40d00d4401c00c0003c01207940d2201144d840c1c8171a116006030818941c000c81054881100007401000c521281038041546141c080d00c4e4101111650904c0c1e60402c4000c00c00c200319240280703442d0b06580180034000301600310034421045d940500c503403040d060091034496000c045600b6000c00000396940d16000340248111200001c89501c4c040c1d0108181c64000022502054905603044400208854000050000300c0c1c03e0402d02140080e06080c40c880000902c0040400781c4482c0d0322108141080000e843c1e0103000c0c06d20820054 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 43875040 1250 43873790 43873829
    0x51e0f0d050f030411040b0a0608060907020a02010206041506151805060a052721010c050301031a15040e07091a030303371a03070608070c030903060e07050109 70
    0x182c1680e501c0b540041071420040c010601090041c00c11081c001d410903241d80001c00c40301d03000054140207045c00e48204402d0b580e0706101720789600a0110003030040e00000040303008500f03284916540c2520b45e0704001441d6980d601940c0401c034840c800303c0e020411b06900202c0b801382c40c0c400c0328010041528a94170f0f1074460607004019208104004c0540c885000b480005000e0700e00e46524071a40181c0035808421004106000020f000c4100b641d66600302002c0600d814441c6e815241202e5214100c00352056038080400c00490005258a415001c14440020950744034003442c100c1c07040d02d02c082c0c1201070030454580f0655a015000e4042c402e00081d0051060320004112035110100100c840882c030180302151050420348501c1c6191000d4000c0c50498400751079010802c10315007a50301d054000100b1041c1a00d078403440c401c54020412107000100c0c3c09001d503890b840f9041c42803500d102100d0b02da030b50f09421590901040c44483d440407005200b69600050390f140a000031200808404918 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 43876290 1250 43875040 43875067
    0xe041b090611190606031202150a0e0a050601060302210103080a08190204030c05100c0309050f030a080f090f0102070f0504090f020d05010b130209030712051e0f0d05 73
    0x50340306141c100aa031001c01800c0350300600042a440070300c1205144400d069003481030140038680001d4806252000e9100115800003421034100c00364480c650b85103a460051000081500109400c0580116035403440040d40038007109010784040e0324016200d0690805800e0041000030402e00c903248424018008075a00205944140d607852801074502e41d2a2411165001041d9103032942d05800443c01004002146102c50140c07082070790110896800008111003a004411014010510860b82030102d414074807000c0b060319030090b00f2030784c144d001e03a03445140340c0d400000d01900a180219030802d04d4074100d10144020070091008081c0b007400e103025444641201d125003886195201071070000c1003c81c5c20103c0d81150001c1020b44c030f200850405a02800804d0090752084100a119404175041c0d442aa83e0a51003e00100340d09810715001d0495442d40d944141ca0740e00c150703070303100381c240a45603c0488988440070140140f01e56400e881d0b4600240c02e80f00720180102888800200002d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 43877540 1250 43876290 43876307
    0xa15060308041203050c0d02030a030b010e090406090204020c0d030f050709050102060f0901060f03060905070b0c03040603051806040c0608011a09010309020f0604060c0c0b0c07230d030e041b 84
    0x38003c1c00e0710381d8901d44e02c2c0c1920360384220200059240144800400310300d40110150515824a403420310001c0880001160b402e10760308201640001e61401240c0460805d500a4071820f201400040c54030420181a80c07a20b41410301640020b6110140e41e81d07040018040c10b5009034840c181860300030f0071b2400203515600000c04000c00c848180340085d06508094020200401c17003410080500c0d512410040050000328a040e5410700c160f042c00245171600784229150303004800301550410f4146041203018020250040b8010360003881d1094918400b4440f8038003131403280c4c2c0b0580b40c4500e020000fa0800c401640141d9610a41d90550151700300b90f4400c071942d8440918000074018201c3c40003501c405081c503441e9810210108001c02c50320342100120175014010181052059a517010074902842210b0042140742c000c480e080012040042520135915500000d5400000c42c036404102e01c41c030b0900c030590003d43d00740200c0005050030b1140c1410103115181c1c13502080ca020901411800 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 43878790 1250 43877540 43877549
    0x5180412050d1e0608060906090706050a0201060504050901140702030c030414011101090302010c0e04020c0c010c080f0f030f060907020a0212010204030c08060417030906040f02040605040c020a1506030804 90
    0x540090010030a07a00380c3d100140724203201c0e565411910a200354503006000724000d00781c03d4425080840c580400004105101d420900c00404001d401c0001c00c41d03560300b003c0904020756480c3c02c80401c007540e8a020341803051403103000004000c0d81981c5e840e08020406801e0700155001007100c00500e0002008942c240c4800510541c03080604a00490301000c030540001070729480c1007821070800d0703030642126a41d034405560358409410b250003088104d220340c1444244540c0501d12450360b550284001040c2c1900400c00130303040c2405807002110a0740202030041068800100f04160440d0060340340b07400c11001e4655004130314011a02079942d03011142e010b4403441031002007040302d00094040360081c6600c0750300320391910307628131403a42c0d904026601207034003000c40c16421600124040603240b02d440c0010040c4520344031911081a90002080305a0300a6217030000070569032114019504064960341c002c001906590900e0110b511001d0042c141480c2840810008a08044241d90584 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 43880040 1250 43878790 43878797
    0xf160f09050402010c05060a090209100608040b06061e04050102060c1c0902130f0b0906040e150a2310050301020906070312060f06020d02060108060c04060c0609170405180412 77
    0x40d02c5a00050701e600180c580001c04074403412081140f000a1500094000f62003a92410b82c01d803a000150703c80b032005030060000081044001401081d0000c0c01d0942001c406400d40b450300c1d12540a100340c0d0001e23a0b0f04440884000103081146503410042e05600c003600f025110b061005803201c82c0c49109c858400c520013a911283c5c000195500c06071000c1c0800d1072464104543d01801c20404040c142c071010640c882c01c003800000b815130800e80100c1101041c1c0601030800e00d4428000500c0b00600506000102a61862000c211500b922400c10340e00c000034044a01c6032904041c44440740040c0c0d0001c50003a40107100c0801c0300d803a0102910350b0a0351605196041d140742006500007410703181d101d160348020001c0c0000701c1a40205114000030600d0f170982d1034076a222185161b0b600000d03505220f510704100410440b540c401c4440c2180b0600c12040400c000d082504c80d40740303c3e44000b0340902c00c0b80d80014200040d04c1c00c0c0580305440d560031940c0800c1c034603180d2101c4070080d8442c0340310010f0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 43881290 1250 43880040 43880051
    0x108030a0c14010b0627060a08010e04150906020903010e0a050304060e13050a06080f0303010f06120e06010e1e04050613140d0c1202061006050c010e0304080f160f09 73
    0x2c1c440290000c1203115009402141c80b000e039401c107204007000d0b15096000b14011007001c040703d810400101c440c55415500c9056040c0d1070603080b0000c1d030800802c00e40301d00c448500b50080f00c0c41035008a00005000c1c040c0540c43d107101c4010113003103035520550b00050303074442142c43c0e00048010080d9400c65901f402c2c10800020420042260321118094a5002e20b142408001c01c41602e03a003c001a240803038121004180b40b00040788d900e00c000e00032401c0b05882c1c034400304000341c403450034080c070200e00c0c0b5070105200b0100c40680f0310700003003a0400b041110300e550400a0b106c0100541000140d105401d040032802c058803070a45841014048034035001540c020310062244504c0c50802848800702204d20800030084c000309100b051030403c0358801101014540b00c18800600d050207401e480c0303010030200385080b605030313090b0b40180354980982d500d0b983e6501103508107001601c024000c00740a481c64000e4020340e50300b0103016209040b9410589802404441c180c40c9168023500c6503400001034 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 43882540 1250 43881290 43881323
    0x9010201060f08030415110a0204050c0904020304030f0212070308010510020c13020711090f060f0118030804051203040f060c030c021513061b03050904090f1a0108030a0c 75
    0x900490b4201c4003140050550000740d2010000090080303481c001c9031301c039544070703540c104403200d0010b01e0708940e00c2d80c03005800c04c0241c94030798007058000050b107030f0151810b09640003040981e00122000e80129040302a0051500d030180800c07401c808034945d01524256580d038000d040e01c42c06004103402855403203484010703d4020020305603811401041061000c444000d0400654000c101c11500d20f109580c00940382e051910519004403800c44452680d0b40c1d0300001e00044005814038641080740d10f42480041051201c80c9602550040307401503a41ea00380002c0c445503814403036034410990b004200c00c0043c14002c0f51440b040c0c030881d01e0100301401c6903050469412083c2c990195000e981c105159500f035040100800c0e00c0c6007000e804458280e9240301c00c3c0c2c0d400040d9041c440281807000040c0000900c140024150480c00800001d021701d015103406075804c1605504480c8442d410001c1e08101e60b000c0300c0b00d8010700c0c00d2002107103415042032000b40205048600200503001040f43c03400b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 43883790 1250 43882540 43882543
    0x50a051603110c0a050d020c010e010903030305060d0c06030207051c080609070507080a050702190602070501031503050a050102070209100f0e15090a06060320030414150907030308010e040b0c090102 87
    0x14283d00e03419080740c1c0c1e041d00c1e9082c42071321840c0740120b62016107d4000708100c3c0b540903403822020300710b05845010b901440d54800760301034a40140b416500c1030703100e801748001404203a50003010f401e0320383d00181ca0303c3c001d2a1103032801c1000a1401c01c500c03605c0b1202c40c9101e5108400651004090796400c0c0c0f40e4441c1c4400707444500880c0001007460001203000b100b8a83e2000181840a00803075080f292914400c03045540d102c0103015540041e0003481d401d100035406500000304c0403c214074071410071541c139180e01e418000070501c00c0b1001d940004a40c81540f62100d103254102c04044448098589040c80101c0507081c031f80305002c41412a1701c00106d90340c8244070b5403400c500f0081e02020340392801140900c020721560141401080c0380100c0d900300301070700f05031a20b00326981c443e407185541c980340c5411241d0441085020054810b045040031541d01000c005070146040f9001000d8075400d51501408080c0141c006002c0311154000304030200340c200c4941074000c08a442c1e41750b80c801103040101d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 43884896 1106 43883790 43883797
    0xf07051c020a050c1507090b030f0411010909090b040312020f03190b0307030f020a060e0108130512040e0108010501080102090604170102040e13020301050a05160311 73
    0x3014014041ea00600c241e074a00e081c030604280720f0040d52441c060181d00004100b403403200034020440e40001c2c106014101b220562402e43c03411040c4101e60307007130042001e07004c3c0282c0000d030b00d002c0e4058001d0070040c0c50006400c3c405c4024500300100e15400546044000441000e40382043c2c18a610903604800307201d0140390320310b840702c118881e0300821405403c0c0b52140c2c0c0e078414030b0351030794200041c5000b5403090911340d107003e40034010005030394200e5001d0707402d105a100100c00180e80c40414a07a01c210380c01a040c0841800d401e0151508281511401d4188000100415200720405640341200c5200c0000e010070b1b80c884055a00341d005000030250042c90600040c003010b00424406801400e00301c00050906640c2c01c03880303c64585c04d8070214040078860b8801d80560400780102c27580240750b00c030103120500342501003039510351100e0045001c0641d94203046d0908801c1c40b044 = true := by decide +kernel

theorem cover : BRFrame.Cov 43705040 43884896 := by
  have h0 := BRFrame.cov_init 43705040
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43705040 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 43705040 ≤ n) (h2 : n < 43884896) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
