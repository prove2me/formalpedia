-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0034
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:29:06.581354+00:00
-- url     : https://prove2.me/submissions/68fe41b4-01f3-4008-9c6c-e73250c20103

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 5935259 ≤ n < 6115115 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 5936509 1250 5935259 5935271
    0x2030901201b040b0d1121010609051504050907050105030a09050319030605150d020a110307060603020108010803040e0402040b06040e070c0303060506030603100518010903030501080607030605030a1106071401 92
    0x8000c101e0300600184c070b00c14103220300803e000899403c0030700803c410450724080d00c1d6000c160b203081d804a50300140041546440c00100e00b41c070483e84121301503000c041c01c450451411006000c00c8840c107803071200543d8007101080202e50b2041c0300640e4424030360500410310300010765a091441e081065005015840f486181e401030b507061003000300078241164440355120750105100194404e0b0302e0442c0d04240c002405000c8503001d01c040e00d54005025048075078545840c1841c038000c0840b40012400a46c44c0e6000040c8070600100b583e040c1e8580d8590612140c4640d402c20004010a401e49a0410303800e000001c2c202034111040d0348101da04d0b0725201c0b140741403890300808841c1c15070000b130710810040c01800381d15100011118a8407040080004180d03c0e5124440c00e80d128400c035980180d03081098004c10182d058001c18103e4040404441c6941c6800034141c042d1560f07406410380543c00703400c6d200041070b050041020b0790318002d03264500e002d0450320361440d19450216142c0301e07691550 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 5937759 1250 5936509 5936563
    0x1110d0f0b040c05070305070c0f0303050903010507030605030c0f030709060e0a180305030408030702070f060302040303110d0f050d1104030c0312031104060309210908061302010203090120 83
    0x10142000034a8100d42c104207a011010000d00749000f440c4004d400c0200204455040008a85240000c1c11840710101480c540d6860010a2580101c1c0e1440c003035400c00e000320781ca5502900852003540c00041c050b0448080c400140304451805020040d407520941234001b8040c03030325100d48005042c07a48810030180c940509410140d170800b01005a40c80c8020030000d000c0f80d031240580e5002548680d440b0b030b40c0d0700c9441d4100c3c82c00d0340703030b070000d00403d520741c880050104e0b09039004008591194491080301a20602ca40b5160650304080c03901041c103070034903244018428030003403401250103040080c10b0b50440d20782c0305064215070821607040507141d50600034007601400c0500749000500d8117008400501c021a802070003288140030605803140800010002204109481c0905c04110102c400020810007040c00040d4420748442d4040c2d500032420340c0c202c080f2108051501030f0000e501d442d030604011101c242200c40a04680c4604a140a4a420081c0701d0002c0791401d900c55151160020 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 5939009 1250 5937759 5937761
    0x309050708120d090203030d050702011a010201050c03010e180a0f020a120c030b15090a15060203040602030406051e0703020d02010b060705060406020705031207020109030905090708060d02010201110d0f 89
    0x240c0024840d03a00c00c075120003100c01d590045030f4450a0042022860a00d90310100346180244130a80c3c10031400c0104200d081641580306c6409003581468003403c1e5100c0100581c01c136081a662620742101c204018008001d2031491030740c010a1228004400c842103092030b90800e95045030455001030703001c075103030194901a0601c40113010692100ca03080640380c3d440c002c01803034a01c001030500b549400041e20064603940100c42504000d40014443e1403c002d520005100d00502401030048035040858941e10000582e000d90700c0d19002180b80030304000701030700c982e04501510300341d05210783d060081400440c0084c0050500c41d800502c00c900d6140c0020b820b442180c212640680030a004840108a00003206500950045001a80d4003090b0a290f410b602c180d85006040e0b9180a040c0070340b9030781c150711514145000c0e907076003e280da88800400c0854641a505000000c07900300c08210103140150861107854814000080c0c20a4044583d1035650000e68031188a583d4400043c41d0360181 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 5940259 1250 5939009 5939023
    0x7020a080a080909180606010e01030b03010f021902030f07060b0f0d03020609070503010c02030901050c1617010e150a0b010c0501050907050108010914010b0708071502180f010e0d02040204030b07030905 89
    0x20340c9040101d17145100781c183e42d2407200500c4541040310071a143c1c1d83c16402030f40101c0998001400030301a0705620203a10010b5072202480380701030110b500c0218909840481610a881c18100c8458139044003038440402400480e02c3e821b0340040c00300c40040f85540e4441581310074911a40180090f03250a0011600f09a11980014003c0c4d05003104100055070110841d19681802d08106485e0030011118619161700c1c2d46402581c0361010901080764010300c00403142061600000f0300c03d070f0f800101142e40315509482c40da0a0b00f190744e80822021819030300600744000040c9441c000300f0341c164486500356802039030008029040f40c44144007a591150340e00b405401056000d00c0b1a030081500601074050520a821440c80042107480403c15094103c40f40d003904280089420044602e4040c002c0d804500036080c102103140f000a171078101000c941300030020507190010300e040700c00305212282d040558100e900c26030810021001502d0040380324052a4244d8000603e43c034145008c500e4506 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 5941509 1250 5940259 5940271
    0x218011a0304050c04060e1e06010909021803010204090e06070504030b040209060303120a0204090b06030f01030605090304030f0b10050414040209060103090501092d050c010c0303020408010203130c050f0d060207020a080a080909 100
    0x503d200c100481039030800c28450841e14042c3300143e50389000c600210070103801500c044d9055000240000c0e190b44a500600c481111905c10340308036403070f00030056500d48124480180b26901000005000d4034000c107145030301c190090240c920f000140c000c0076810791003c8844458a0303a01140501020316280314417445242e0644001c0e2850030990415246402c0510008091175110000a0340c22071042c8103a400450307200964210143c06882c0c0f40f181e04070304981250700b03d09000000105850640240003440d415411400003a4880780c0910015201c0100441d06254883c807007400050340c244162103040d40204440c05002000c040350b050024420071340021640b0151a04601240303020450f803a005800342030520f00366a0130725007070380a8090740c6d220300c465510110400c0700c0070560142c2154010f05c5103400c800619280c8042000000e030f92020140c00542c4011428002025640240b401600081450400c2551010150318007140440c0441c0c01003000b00c0d000500e8241008000c0d0410 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 5942759 1250 5941509 5941561
    0x3052b0e010e0906030c03030c0703030e0406030f0215130b040f0605090a1509030206030708070801050103020c030409020f0c0102030112060507020604120c02010324030218011a0304050c04060e 85
    0x2030304220008060140880460384500c04039030100d2000c1c3c3c1c0802c400649080007405480e09c0c0c042401c20340d6201c1e0514842500801c604074599100c0e40780038403412056951219030350181d0216034090041000d1b90403c01e081d00d134010480303c04c801401d07580250061001510700365450303040000042d0040c01c164052424000c0621810b2542e644a500040c19100541c442400c24219517008640803c01ca070b101a410200002c184505150720006c1d551003981507445a0007540d0b40c0700c00440c200c0c0300f2881c5c2d03140c1035041404240071598954004007001810003144900701904448107034226442a40510300b6504040130389010401c0e94080d50fa130140860001e062949480d4650703100210b40d0115200c00c024032a000c0404580c040d5102940c40c02000c3c0083c4d1040b101060285030800c2907000c207a00c240c07003600c6001205102e030544a810703201d5025804c81040740300a15805d4640018008544a01800b082c0c80c0451b251440742600800c200c5070809900d0520301c2208550704075084210480c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 5944009 1250 5942759 5942777
    0x1305041406010c0b040503040302101101050907030302060c0a11010609090c0603020c030702040c050c0d090501090b0c10090302030409151701020a080606090105040302040504050303040b0f01060915030603052b 92
    0x6a030000d41d0380c0700d80f541065480707202d9034441c80e00300d013180301ea501b009510441c80310300c60580580c40352600c2c0090407440000c20081d00d40c1c0c9a16503440065210060050344058001040e079142d00c805486424070a0510502807019044c500d400d640540d085042d04907940e41010003803204054002e80148001d0804610300300d500d55805440380f04bc00f401a0007984c036029034a001900c80c80072207582e0f0300c414042e9608030542010042020116214250005081990101e2103820740c03021038440c0c581c22402410500020710fa071402510008906400713500080c0000194800e4501030150256200c01e0b4106c2c119040c1039504620308901021900660701c1848220442d5800a05168100404443d40742d160b5442e5001215035108541000f0341203410301c003d02c0f040100000281d07005078482c80d00301b0b1030b0b50384407000b0340a007890904c9294001021007204100070f01c41e1130706110110040703103004911103848c1d40321507203040d1420f060300750008000130f0900c0b00c41c20781d4404c900a0a101e0720b042107403 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 5945259 1250 5944009 5944021
    0x5060901060f0305041a040606140f0a170a0c0303030501050112020f09040b21060405010b040c090b09030703061b0201061e030b0604020409090b090d02010612030309110613050414 79
    0x48518107800b8001803507580c0c804502409180f0750f081c0c0701e04034103040717501046c601450014003402d110b101e904114401e0740c442c1c20052920210f00d0002c1000504a6541c0320f141c034408e60501c0d0030000350303d040c40c041d01510002003014141041c01a500984000c9099450030340010880c80c00a424004413500c180300b0b074240c8121030400c031568560107e0740850440040000100050018540f032495a99030140c0c0d40007901d404605180b103240124002c10007868000148002c0d2686444c4000000383e024209000b143c40c0b8101809100030040e048415040d101d507104030840300b00640c07450220314000d40c0035030426130900610026001950003200080110307948420b8404080c00001c000654003400288a51202c0d030540b8020a13100700188490200c0d81403401c6c50320404d5407d140180100f440450400d4014024802240c032080c080402529541e01d085000b804802000c031151001c2240d10342c440d66030384004d0002c07010000d10101180d40340c40104022102c40088090703c140442c420401 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 5946509 1250 5945259 5945267
    0x8070b010e0f01060e040f0c030c030b060403050606120f0312090c0a08070b0703020109020604090212100b0703050306030a1406090106060212030622020304150b04020702030c121e0109060506090106 87
    0x41160a43d0406105d080780100010340503045040c00d42200e113141c441140e86150b807640003143c94030010f41b401c015095418040c00007911a50001404650020700802c882e41000d50100403000c50710002d0b40c1108011042042c2135074001084909100d113900103001d8031003018008015080030880715001350610b0020788236104d417507502c6110b030325000200302d032030a040c000c0d0452081590700500c40e0381d58503202d080d100001d4000c21101006aa03024000070300c14100e11941c101a0b0b6860344485040109650b030444481d80300500c002e0f01801508040c80000d80240d03a440601004800600550f00d460300407030303003101c009901410841d4000c901e1790400e0180041141d801010540705864006140203141c5404000e0790942207103180f0000401050041d2000b404107074080c0d4000c180101445d0300104002d81c041c0300000380d03268000200c0c1e0310192800701e0042140d006410301b51002d04c080303000408484600f04200f0100d99464076482c0c13081107001e10a0f103501c098110307913240d520750400c2d100070 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 5947759 1250 5946509 5946511
    0x703200601050f01020c0303040801051b0a0207140a03020402070501050603060703060e0c1b0303090109060b0402070203031204020a09090818191203050424020d0906050906030406020405040908070b010e0f 90
    0x14020036201071941c3c0c0c141d1003844074010100e80075007103c0c2e07202d5440030014003c2c40708803220741c0801860201c01c640d2480c40c100b101c170025010743c001c00f061402d1643c91641d480f880748019134402150070000006032640c1c00580340701401500000303150b01c2d046080c0b40c20603000409910806151000501c00380b46140b03601a040a1403000784c54859a048220f00c0341c1c5c15250010742281d120101c208005003105411041c143d40c8034034814001c03e500c52007030009a0103200c4000354180c1062041c80c45005400e03010325882030004115140f00d0750740d60f1a101c11107001c0380e425280482d000903d038801d040010030100a0035030a071001f4a0402c14a0454140c400c0540074001c4818001090142450720890584026020514007041c07501112070007260000d00e03c0081c840503002c2c250a22170050701915844c400c4540d140c5a0518210803c4100007250380020070072120741d0741c24040800c5e240c072544102810544140d036080d580320041c9c02d10310408a016401501d505c04060b00704152080403030069 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 5949009 1250 5947759 5947769
    0x50d0b060903030a110c0a0f15080f0f070c140106050414010303090b0309070807060c030f02060106020304050409030507050a03030501050315061c02030109020910090c0c020a030803190509030703200601 89
    0x1d41120a00d040e4501c1c288680020300660001b6210340204904d01141c04070012500c91840304050390b01011327004e9a0070f001c200c0d40c03c3c00344030794200000e07208019a44e14590140003403800d0511850385650f14484040c034030b8510a0160740d40c00c000c1c00030781018803c400d0781030607200b013420f141c0d80742d07640c020000f500e9402000c0054a0101c0131030240942000601c02803c1010165011981c4420004182d5040c40d0015400944106094140c0a00100e20a0b0586a09034040c502d841c1c1008140006001401c6048003001810030004000c502c003880105603c40c840e980208071035140c42d040501e01141042c040d0301c0c00c60280c0501c1a40e9456240301c64007111080c1900d004260b0600010303005080b6410080e421548000c04c000303800d1000c280f4081545c043c560100315102c40f00c0f40440700d840e01c4c41e40080d0801d80402090020403030540c05194860f080c03c01c011a03241031315040c6400c2da401a00c4140c070940c00416040200b5407c4040c0c1409031045000710855000e00d181083c1d5120018416 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 5950259 1250 5949009 5949017
    0xb04020105071b0305010209090c07050706050f040810150510050a1209060e06040b090f0a0f0c080d0905090f0c0d0c050c0d02060603010c02030901050406050313020a0303050d0b060903030a 83
    0x44002048001c43d80802d414850042441aa96503810814040d41c09648200c0c4210400e00020300c01c081420191040240c2000062400c1d0382000b00a480d03a50108545145030441444002503030300c410011107681c1c4222503000304d6052528501411b844d449500814854803001041d0248660711205607807840041d4030b4040303030055402e072000005102c0000c015012034103290000c2850403000034082d000f01e00c0307405002c04070b60720400c8140d150600300480ca049504400b600b600450444101641900e01a9070150301041d59401c1061038a46480c5c018000315030342200810541c50020718040c1e01c0b044003613510482d80f82840b401003051098010040c0c446958846105d030492198080c1c031445e2440c41d084403003002031000c1c082d58600040304c101344030358200440042c0c0a0301c084180e0b0460701d410786915040c50b05200083c1c0703d07500020b1000d50f513001c4200070203015a0380d91908000440c082d880c0c0541d52948500000140c0f59800001c0707010304010450005141c40010407200d101c1000d10f4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 5951509 1250 5950259 5950267
    0x105041103070305100f03060b0916020a060911031608070f06050f0d09062c03040308030c0307030e030304140f0115140402040302040203090705010207060c0507060c0f120207050a050307030b04020105 88
    0xc01c170348610307a0a0b0800c0101040904000c01001400c0d40454040802110758214035034a4244030022a03100300700319001030b003180356444000750f034540018040b903102c1d980040d00c0c1e41043c00828a400680440041412410340c2c08010703408040c844040581301101c8592500340c141070018080f48030380090164100700000344c0c948200825031040c00002c0c0d001e041803024500341207a01c541c40248500719082e4002107142c11944490000882d02100c4c0d1000000c2e08690300d01103118150380000b003c48050544409074194080428001980310354440c0c0c03440503044503e02803961500407802c40c0d080c00e681c58003201d50403c0800c101d140d0201c50700d10044a000c0702601002c80c0103805554002500180044203104c101d1102080c400144c1d1400e13400c0307880140e0355040841d031030108680060040e42200c01c0c14031809204028083d01203000b043e003a01c00343c1107580c03401d14440b49070a283d001600280014405031411500080042c0f030b08038018481c0c0341c203584500b0000040500000e0511074002 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 5952759 1250 5951509 5951521
    0x201080603150c04081501080a080903210a0e01020d0801030204020c10020403050102090306100e060402030703090f03030f1107030210020c0a0507060801030203100203010b03061e0a030f0b0105041103070305 91
    0x20104030b03002540411040785091070003c00b001c680250083d09031038015010140c2d01c20805000303043c101d5502100070082c800311915440c809078482140d541d0503014021030042141854070410400c07841500c001940d50603403d10050400b040c0d02011811508a900c4c070400c825441060181965011500140c1c3c0b07080182d0300515003c0283c0c0100722090000c05c00100340041036001d0304c480c9000790242d0f0102ea807503a80039261404517004042015403d03001040c014102607001d540e12086900340010202c0b00d0f40c03502003070400085402c4000071b807100050301c086100e90091a2071000c032101c2803400d11140d0358000e0740718400000c55440c0302e9804519508000c04c00c00070003024a41007030a07600103d495070f10003023400001b40410b034028456030700f10652104043c82220f040f10425000d05081d51282020820010b40700107075034180c0c444500c041e5649035030702001030000358131039500a03039a0a610320b40b40600d030307105034081c512031443c1a03c983c1c1145800000c41e503210f00b60b86000a01c2d55205 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 5954009 1250 5952759 5952763
    0x909090b0f09010605040e06010302091005030a1b03150f0b0301060605090111070b16060b0d020f010e181009110f0405100207080601030804060206060f0604120201030605130506150307020601030201080603 90
    0x55030010346c0c03042c28a46111074403080495241d058030300035945895107544802c030141d5880b01c948180c0b500340e44804611400700d0840d21200c0064944c000100700d60300e59036101c032040150540100c040751555036540394150a06485070501545060b0024822640b901801402e81c2c05040c0c0902d06000202340307807c4d15107130b00703200340700c05040e8000d60307139488070350004a000c2a40310481045810714500141001c561504489490303019500602c2102d10f507100e080110703003800d0400d121941000485a8641e01c91400c04d8030140b007030040303122009580b8036121000c02554841201000300c00c1c810883c0b100d44000200868040d00c109850361554800c4000040b0318005441e80a029180074150021082115071801481220669405c40d4482c3e00c1c2c14082014926840c030603181d204c0b008000401142c80c0102c0f1100560f0300505000441d156a00c001c039500d4604100081c54a940d140c0c00c10043d0b2074100e18a0404d044003d21943c04c42c0b03840d6030044e5640e081804080d06000401d00007652990b42 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 5955259 1250 5954009 5954021
    0x9020d0b090a05070810050a061101020c06010305010b0a0603060308160c03080c0102041409190e0307050708010204050316030c05090a0e01020d05150402070302030904020a0306030803070c030909090b0f0901 91
    0x8060030070301a0b0302d01000302c1e00080000740c40d070f8400640740da03010410a50080042c00d00b60b40c3c0003815040400d103003050a45607014581c0450010355001d1008a00041e4280525402140104c0003c00d40003011002c01400c00701581102091600e444018000308260700107994481a109000b41248941c6003030000c40c100340c6078401040d82a000901040c82035041d0040c000701e6031304002c6c0b40400d1481c0d504001c014402255010145403c003001882c091201d50810a42c903012071042d0b030720b081d00c0760f1901030801100340c00031201690000f03000c0010741001c020f100f61300c04200c4c6100c0b4290742103540e1008844114480c4d10b11a00310000442c40c0da202039400548210385440085540740203040010f00900707421201c242c005e49000250406c6418503000305d50b5469416805035143c0b896142c1000000e4100c4a40d42c2c01b09503480704080001500d03030005501402c415240d9102d000c02c5494000d0a00040d074100c040c00710300302a0100002900703c41401e401010f040180c5c021991307414560740c01001 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 5956509 1250 5955259 5955281
    0x8150301020f07110f040209030a0605071e090f050301020405010f030504021c12030c02160e041403070b010801180c03030e130c0c03030e0f06010302060a051903050108150105010203030109020d 85
    0x240040e080c0104070302e0b030401c034981030020786010345c200302c42004000403800f40161007034051300720103030701400140b550740001d0b40003101d802c1c451801072501498044800d8030720500340c082800380d00d09000c01d0f24105040307002000128001c3d460070b410280000c00e010200c0c0621030516480d0f1003c13a04650fa4406960414014a0f0104c03905004c2800c00e2550300700c10030940c0c00424030b00b0300400c00c1288040703490030381e1141c8007001c20030107860480c01440c000c0f4002c1040d00e01c4202c04412411404003440100651401003000383c0c20303075040509003401c44a8990304813030010180c070003640c001084480c00504407038060402501140c1c0103c00b2505156100901040640c54860030342540754004224441142c02a0340800ca902042d540d1540e444816451070551588014010001454048006c10760240545002400c0c080000060510381c90b1a008035000700e034407400144101d02080182906614040907801c2040d458280041d403a4031060040451043c1c00152130603100605401000f4500 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 5957759 1250 5956509 5956537
    0x90c0702090a0f0906020403060b09040b010b0d0e12070219180b01180f090b040203010b030109020903030c010204060f080606070309060f050705030723060c0306010804020406150e03120a0815030102 87
    0x4440c605d4000000c2d80640000c45070305191080401442c00c050b1502803080d03034400c0880405034205981188950012081410301d291104440003203142d0900c000703280b140d920011240c46010a10401503500352509090740c1401e10204100b010200d03c0c40500302119544600089144503140129a1443c24408a0040071031240d03002400304800e040c0300c8202c46000100300701d40e050000810047c1d02c820311461903d20b000b07200511210a29a0091101140082c110380c03602400f00740f07503426138000d41c1c400340118503c00701c02c901c0310303070025800740e4004000c0b1002480c000c0596000347c840a483e000303100c100700400001c00c030300780d0107001204c0e10b0b5600700c4222602e482c03080c64800310042854030f0312105990075800296807100001462130166000fa8a15421903030365100446450000500c01c2c0c1e48680c48080005003110030340c004201450f4a0340c0c0701188031400703100349490241c9207180031182d01420081080d000d503206a0721034104610801055160a41d00c0c0020b01902940207468150 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 5959009 1250 5957759 5957771
    0xc0304030c02220c09030f0204020309071a030403020601140904060e120c0304150309020d0b0601030f060902090f010801050a0303050f0c0601080f0111040b0307210501080a0b06090c0702090a0f 85
    0x30855411141e010560310a01404131601488080719000c030380340310040044c4c40c03510f5240014600780d0040c2d50301100d08000c4549699491f490301e440342900c42182010194004140320a055060003154090006203a09075100404000410064040200090600d9542d001002c0e00c460f000e100c2c1800480315007090755110451000103d84a50042c880c103c05003102c41c4481c64860302a004e21011aa0002d10f944042c004948440b214500000c003428101079450403411648070491250720702500c441240162510a000c090040804401015905111203900100b00550700c00555906880e8107141c090b0300c0c0e60340005000400d00030240040d2003800341d4000031855200010f030b030000208075600248070250240c01e4030410391186015150004274108009110580074a11010010030704101c040d008851494503c01222801c0c0c0051005070800b140710340070321985040d11a00078108039a15a900d08001c0e605101c144560300340207010b41a0f81d0005803480740303540d11000d0702c100e02180074010 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 5960259 1250 5959009 5959039
    0x203070b0a031d0c03070b0c0705030312071b02030304061d0402070b0702070e0408040603110c010e070603060b09030c040b011b030206040201080a0b0a03030e0a03080d06030212030703080c0304030c02 88
    0x74150f60222103042e109541040320010324009424481c130784010b800340614038145030340002c1982c40320303042c208548548000040c01d41c81c10001441e04000b11504402c0c942407002000b4941c9001c076003001c60f1002c0820a200250303802004407011122182403100084141c0d001c1500000700c0312028a92161000c254141402008080d16204620030390a5420f6282c8420048102c40d5082c2d42c0504010010f10043c405603000394000e007442403070341200e9420001d07480d441a0035100d000028a80b075070020842000070035054050300026041c030540c0c0c1810000c5044c0401e6442082170226407040d03803503078100342c10390340a0040126200d80c40c0103207a04a07502410043d6680009403400c0380000d4502c400a0480a5944604080681c00070311a1a4840c0341d610211241408a503d45504c100300c030000000080c042c4000780b000c0710544c0c07404a809881d500420240000e041d54018180c0c00421441c1c0000750b0260f50176030701003034141c0c03c641ca03510f0300e04080b1042e20f41090025000794001404000e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 5961509 1250 5960259 5960261
    0x21c0201060b04030b0402040509030a0509040b0d0203030c01060501020c0a030503090d0305040b040b03151008040b0703110409050a060801020306010203030705070c03020603090610060e1c080c01090f050601080c15070203070b0a03 101
    0x1b100d41c1c0240c50911568650400c8156a07124100350300000480a000303e036020301e03040d00841c0220f000104a24002480e0780c001030f0460703022103440d6001e607560344400c0140c2d50f01407212600c8510b003210140c001c20300c0c40c0c4850303403240301d01c0ca40746100c1e440100061081500680940d4041c04201071001d895544500304022a64000c1c0c4034100c0c0a003440000019502d0070440c039241d8510350707075140d50564030f656541c4000e00c2c5d80038200c2070034191240c464000c5a00030714054002000510702c04611810284050350440da0a60840c003101c3c3d00400c03c200740c0c0e036000412a600429036151455a6003854102000b01c3d100f16000254003520000511080010005000d809041c001c00414425503942d0403e688188400c4482904820b00380c544852200070705202a441c14000d80900b490520b070101800d0031158011000c8039121103001130341c3c0c10b0003410030587d03014001700c9004180c0e50949000003450786031403458103070584100003407400440d1024085000240409030029032a82c541c200090 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 5962759 1250 5961509 5961511
    0x9060712020601030b060405010f030f0f060507020c010e0a0b0909040809040203011815030309091107050607020a0507080f0a0204020d0b04140610030603020d1202070b0307030507091203021c0201060b04030b 91
    0x2075204030703601740403401c2840d1500c5214100d842c424071940c01c40b480c50391641d410404d0080252504940c1041007404a8103601a0340d10444080c1d000e0007c4900000014000c242c0588025010720a18401803000942035821192011421600c60041e036455150082e00ca02c584e001940d0054008000041c44070065a1000c042c1c1640d004107210201d5044440308650919100180010341560010050900540c3c8030340e015904212002c1d00d404082c3d100c291819001b41e0f00e100c016840001c040050000c18030681c005024424040c007000101c40d46030701d0792a8044040a41b0a0394002060035450105501a2110f041c028009108054020100d00000d00048030f806003e420451200152144284a080182c2c0e5004001038065411a102c41d200c90702680329503001d45c490000c001c03038105c4495000e9481050b01d0317030780480c0303624045000800c040c4503a404064500040d51816001030340200f02d0b5426200245001407801c59410f8049004d000301c1d50140340e4216000402009115480f2156 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 5964009 1250 5962759 5962763
    0x50307150b0108060415030308060f0607050307020909060f010b0f0408060a0501050a0504020a0504140406050d060f0f050c1b03040b07050f0705010e1e0301020d051303090f0501140906071202060103 87
    0x88455504d40003408262150b004e460a0803403030301c1720244002405540e444c0e40100025250201d0138440d0804100341b607102c2d0105079802d60022031000c08518010101c983d006000001611140c18014038000310328030180a003141c05c1e280446c600402044090a0354024a0150200d8445003041c0c6c203017400410003801181d0141c10360510114050a140c02151041d85003070741c803140b41502d800d40c507000c00103d02030b03060f60054982c0c500107a2680d034040c401c51194080c1c035000030020880c9490104844003d5400d542c1d02e4107000800091007107103007e4403040e402300303210486a40c0070743c00400e05510864001110070381c40480d0380402c3c00300c0020318030300e008000c0084643e5a40c030358006659018803031016a901601841c01c10b050880b100990f209070640c040c0000d410808243c101d102507640c101c0d030240440813500310170018940d00c001c201340100404200c0004150030540001e103034540c0605001d0610310300140c0c0e104161948012a036086410400c0031885880d42c4600a45401c028402 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 5965259 1250 5964009 5964017
    0x106030b030d26040c080f0d170103020607020f01030b1002030703090e090d0c0606050402070308040b10031104090201020a0b0408070c0e070207090e0a1703090706030203090712050307150b01 84
    0x902034494003c51020b001c00980c154914440c040b030200c9104035603401401243d0a6442c8800000d43c40780401040d030144a407440981603036089294000e12078516405003158060840004001507141c41c0d086a00d00d5805442c0d0b886090740100042e000740c0300c585d50303036900310302c00071621415554084084e01c1140d00c40ea5446610359910b02400e410100b05640348138981d0030003108251603e028076010041140305880110b406035541e4006412a00045020741c003181e5408200000c00080d0041c0c160300402404c0d1a042c030b1807e60711003401e1100c100050307500035940c0c1c04007441960700811028055581c000040da2280c5068944000d0340c0e0804903040764010b01d040c2c0080317514011040902c0c403500c0c065009041e002d182c042d940c40a40f01d01050703100740340102d0100c180403441600c034458960505100d52aa00d040035504189442500e034880c03000c25205000b4008801c0d07012445104454020408109616003030030a24118440c40300e00602040f680e004000030075110340c000002e602002d0322 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 5966509 1250 5965259 5965273
    0x102040602010e010203040c14030a0501020a030203010f0509040f0219030f050d0206070c080306060310090e0d0f020a02010806060903011b0201060501020c09010323120d0203040203070b04050604061b0602030106030b03 96
    0x20f1401e034082642e0081181c20441001d1141c1401d03140303200c80014009013121098a2151940c03400c90b8800c08901001980000052200750700b4918040010081600c684403180340545415902c480b081c4130081c8202145120003101c0303442103481c0000380d60401c4015000b000c5610b00107642c0c22805903000003601411001408850050a00a6006400c1a20540381d980d802042001c0b55100401d0002d41070340c80710001c0782d07009440c40b07545907034203011004054990b0f05010103842c59091041442c215480b01d400240141d9011000b6500440300795881030f12441e070100000e004d04038400381d5007403215140c049a04050f905401100c21a2002e0b000d803003201c41d032a028412110702c00d00001e45600300000080e40d403882e40741007041c039042c8140141c07500e8145000c90301e00294131500d4050180b64020007808150304e001d000c44001013602c030044903e09403525011828074081e5100e100d090013800701c9091440c4401c078134619015940058115038035a10746030050003c1000c1e15126009101c3c2030 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 5967759 1250 5966509 5966531
    0x70c0201050d060f031b03031d06120f060909030f0702060d0b032b030c0c03050309011d07080105090c0f09090304050a030b04110301110d090212030c1c09030c05040b0f0a0305010204060201 83
    0x3000c003400b607940503619480b00c1646420104110360009c020903401c148200b1001d540c01c0c641020035030041260301070724600d0707003401da040044096010704100c0d51034100f00300b400d00200101c8110703840c807541900d40f1034503500f10500500c000e060807801e980e0980207458088032044583c48280c0c07040e25821085610480481c1e40403811501c600c080303000801c21000b03000300404d00400285a0000c260340000c110f1a82d0900d011440d40c1714203032482c0d003d0748040c00a206429080c0940303a03103e400d010060980281d030310005203101c50110741160040f08000003180a402e414801c03180a44405440000626520700c2c00c002c0100c011901524144000000c146041c80c040c02240c1d403525020418030302340b4210302c010300300410222504a9011140351180700a00c817080c80500b00c0f1a920802a0001007011400d214155002c4001d020401601010500020b5104000c120586600b92000101781403154007241c00303070002d82c04142c0d1001c030440c400010000150010801d45840c1c1e402884800541 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 5969009 1250 5967759 5967803
    0x50d090602030304060b060904060311030d020105090c09091005130b060405041122050405070f0f061e0e06070b06010909090b0406090302010212010306050105010806010f0503070c0201050d060f03 86
    0xa40540c100581040011502007101d90700240300040004160b98608110103002a00f1541241d004a03262041c00d01174403000d01d001d002d40f142c0c00040d400207010602c1d0038403100e61980715501c4124441c00344103000c1201c809080003440300c6206e1066041110307013040c45d040c0ea038000c00401d003103440c03518450005400342000d000c0e190140e54001459218800342204100501184c1007900d01c400744030b6a224620201035000d840d000328000e10150421a04008801c44804910b4000ea00c0055032508200b01960780022940c560751142221800480007481c42201d02c0358011050b240e00c00c1011a440052000c44000c1900401007601c0780050b143d622034592081d601c0c07215001d00004500d0780040c01051041c1c00500f6070768441e200052801c02c2041e00b61403a0709081e0020742c1c2c05603840d00184803550f0004c1245410905c00d0030481c1c00d400d0040c40040051100a0440c020023985028003021a40034409440c454820200207001542c0c50b00c0b0404c903500744910050f07810032940d500a103014202 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 5970259 1250 5969009 5969027
    0xe010605120703090501110a0503010906090207080703080411060406030c11010e0307020f030a0606180b0102011b0c021306060e030606060a0203071205070c0f05030c01020615010c0309030816050d 86
    0x100c41c0d610000341e59404090380244103150040c2c8155489180100d140466000100304030717491600c407036031a541032202031000c5178440c0d04030040c041d2041084001003040c55003510020303545480c0005041c0c2e56468848585045c03010b010350444004a0049401070305a081646101c2c000e549004803c95800950380c2a1f5034444203521240d041002544007500300b507405102002c81c0030381243c80c840381682e5450221103c80d808051101c1c03c0e00c40500880c4d6240c0640c005840091009110601c0460fa14610b500301c5448034000348082404020708548a1001c5440c014410500410900765035840181050000b4036201d0b107c0d001c0d0701c00203560341c50b001c0165246810513600650410a20340c0c1c1d040106000300201c0d37002e00c54103212203800100f035400d405000d001c8040995140c2c9240c8024145845205460a03066410080801c600b240d01c0300400941c1050901c0c144000c0111404c0540c0d15104130340014200b80000140c5190541d440125524514402e0088072a80e0505210840f076144e0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 5971509 1250 5970259 5970277
    0x1020c01050901030906020405090109061508060105090d051912030e0f03030703110d060308180916050a0c0203030403050f0609030a02060619050607030c0b010506130323070605040e010605 83
    0xc00303001030364003544a9480442400c0c13180b1b400520b055100c0c00001d0100809074005a0702039114141070060751001001d80d18016480e0801da580c0341403d4002030b1241c01011205800750185c100580c003480010050b0a24000d004d0f654610060340904020303850f034011001ea040402d0904810001c0a0000500c03890094050b00c041c6007151100320382107024010010041003012424441229080128030618009620810402d41e03920080d00031b0318030543c40d4001c070502c14a140d0013003150150740d5204804c0b81c0320807860010ba841c54020020380340c490505001a425100110380401048000900b01d80e0718018581180d0880c0c1d80c3e4804541d80f03100300c1c4130b29001a00701001003603035800c003240c010005402a0041e0700740355480d40040307021600580300540009030b641e0750301e909014040c00b01d0340c00b40c50300340c844a250454034400c4d01600c0889210052138034040e0000309070b03c541c0b4050004002c16808055502e01750395030000500070b8005000c0c610001f5407a5000180c030034002c20484165070 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 5972759 1250 5971509 5971517
    0xb0f180c030309040207020a05090903121602030a0c02010318051e01020703090e040302070902181f090b0f0705011104030515060a1502100e030403060b120a020d05030906030f070e01020c01 83
    0xf03500c1c40521002e900180d0303003260440302c4501e000c185540c1c4d140585111f00b01c280002d41d1550303c480911041c58101a20903d00c0c49070840066889a03404400c0300c0c4904881e040c2041868407a00c0101c004101c468000c1c0950b0010000d041d0410001080c90090403100c0911601c0c1100c0c2d0000380d0f402c0b0b105002000b004102d44000402020300b2050210380d1040c06801510407443d070340d0a1000c143d0340191840f012a4491340703d210194030340348402110891701582580c5101c45807840c050151101c030300039000350800c04071b084038440c054407044548803540705000b40100700c22001c90004580046c00110340c00d02405000c84050180030340203074460032000740700b5501c1d1841c14107411140800400d080046004a40c4020400d0b00d60707020340d40380d074060000115a918610f08281080341c0ca29009103105208504101b11030300030015040f11110340440d900048401c25180141c510303c00c041c00b50360494030220801c0304082d0103e41e45032069655496140311041c07007000481c0c5074525018080d01003 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 5974009 1250 5972759 5972767
    0x80c06040509090c03030d090203010e0c0918160303030b0312120105010804050a050106030308090c01020f070b03060102070305010c0c03110d09090506030106120f0606080714011404030b0f180c0303 87
    0x10b450000c1c80316801c4100901910158500403020a00b0365120713085c0f10700095140e26104085080c00d10a80300200c01c11005003060b51503074000034202d4000644164482000c10a1041c5100e01c188076515101d044041c00c00d1007140c1c1d91030080c000d400b07080300e881d10a002c0c41050500820541c01111452201c603881c0742c04a03800c100042d031308004044d205540c00e00c03926801f030000410074400c0d10091030083c1c4510b03405140c0ba0a03007a01d01100610f20a0440d008441d03d0114510001052000d4031040071007592a43d4901004074584051540b001d4081c1d82040d038040c90050304949011590390003507541e512013400388030764181d60b0840302180f680019203070030b1f0801c100307155070b44483d401810040011402135550300215201107254403007030b0780c07035559800000100941441407030014500a000342040714076026040c40d8000c3c50b00500c505005e00320303030309a59520352901207602842d80010080a6400c1c2800d07695800401111a0728403c9141c0a9250800340c001170391070080b0400600451030 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 5975259 1250 5974009 5974019
    0xc0309030a050f09060309010516030b090a0b030309130c0212090108040f0303060506070305120601020c15161202100c05030105060d090809030a03020a060f0b06070609031701060306060207080c0604 87
    0x5a54040411505080700030300100d80c0ca90f0300d05d00103602819a03007001040d14108071494501c822400c80f140c000341890b01d0000152900c628083e00d81c0040340d8040080c5201e690070209085103d1020003a0344100380c0b901070604500a0390003800302c0c148560031070700d05043c10024404140308080d079160100d14010300090003e2a0180940d01541c4a890003054255503000460b8041d04500e01c00c5000c10780c04070b0328225a03150b40e50354941c040000d00c010440d95611101250f01d500f082c4034240d51030840002c0d401c88442501c107014140c0f0303900c100d101c070717080e641800000d4541c0e011403108804a41400c001031039151049059905076500109500d2030011001c0746a00203140b00a01190010001e00c2600e8803607400b8400c80341c3c42e60081e0050042c03002a440c0c1070301250207070b0703c2c2d100d041ea1070007820145075180c560680c0c000b15441000010700840509081e40c5003410a142d41c544d40d80c0c1d6000100d103641d40b64000104442c020f400300c3e41c00c0c60312485002d4458940d0141c194001a040c001001 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 5976509 1250 5975259 5975267
    0xb040303050316030e070f030203160b03010302090a1e06080633040b09010303051308010e0604030503060310060303111e0606040209150a1d06030402031c030e06040c09050c0309030a 80
    0x41c143c1981c1c1000100800c62102e2141800200d51001c80081400c180070025800e00384443c0740004880400e03075490780c0c10454044458001030101034064030110000070039006e840ea1221002d80002110035400000e184404000742180d070180c1010750180201090b441403070010924140710183e40e400051620500385c40000003c1900c0080c5e115807030301008031707050300c03281d8070725011794000c1d035075640d4520109040030100d140c5503110f41d4080e80351460110101d43d0204110390016850720b0050f0381c030788401002900d08802c100e07040e404030303140980000400d50000c950990a5115a00355410000c2068038004641035031018200213070044400282c41d803506030700a14446070001c04403050360308110000c003080e400069503500454040c40b280d544103034010a400041c504e00f20fa079a455807600750301090301c2e00d4171503000071996103c4101c0581890300030b070084641050b080041361090300d024142a1190700c4644222401e5600c0c100100d400c095a40d02100c0c40b508265000310325198503920b0840e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 5977759 1250 5976509 5976541
    0x21518030403080d020301060206010506040303021b011205070801080c0a06090b03060102010e03040806010303120614131808030a060515030103030804030e041d010e0102130b07060b0d08130b0403030503 89
    0x9525000c1040007100080c52400035250000d1269801038596051400280c034091040c1c000740c0c0304007400e210820009900080402d848409500c070b40d0030058040c2d0050340d10804001810300b241d420a41040500c80e030090070a4108d6079030004071001c008480043c13001c07000c224050b40c0d00040000506000c110b580900864202c0700c188000940b40812116180c00d6400541001e010380d005080104141035101800c40269030300c01a04110aa1a110503041c007501c00101d41381c01100360306841000e2222030361096003454016800505d60b00300c24904825150300445192501c14580310b00440c503404d0040d0100403090501c04018a1642191000d80b03452000a004800f00b00c03040492518a490b00d0003081500368080c040c21842c24003080541d4251100780c00d42c10701c036038410300041208640203002c3c030b0f040702e01c000d45031070b924203650920300c0143c103010b038040c0c1e0055090a407210400016a00801140314480c240c2c0b92041d0f00e650030200350744298071000c1c002480900206005040c042501 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 5979009 1250 5977759 5977801
    0x60405040908071e0b0109020f030a05040203010917070b0108010902010207030807140d050703120506100c0206070b0c03010f06030902030303041203090203060711070504021603030506030304030b0a060501030605010215 96
    0xd0615400c1d5035a04c0542d42c2d003001d4071021500030045041000204c80c511800740a403c10b065040000d00481c6c803d09000041908291645a00102d003d6440c2940103030a820b4200b94a10140e01c00f907641e0030382a031f002070011241c0382e014000004518106114140718242d059014141c06c5241d511582c40542007070005980000c03101031217103841c01d01041503800c1c890447e112582c50345040c1c20040c0030502002e0101e600c140c240810001eaa60b00d00e00400c81034103081c20031028025440c0003040b550302403624000c22040c2c1100501010081c0702c80a54101e5040c20964403065498900807030649524110094041c1d100f4400300d4002403c5d4280d0302074075412481c0000f007000958000030f280c40c205641410105803048140300080405100000107003d05450075842d1403d901c03480c01503030700c0e03045c0050100b40e80c034404120380c0d80c4e040c000c490055411044400081c246500e802d00142158820540401d1408030300050704c2d4008154130040b03501070300c0d4150304d90b9990f07000b4a070408659a41 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 5980259 1250 5979009 5979023
    0x6010e06060f04030b06090a0b010806091801050f04020a050102070609031112060708040606090c0207050d0c080a05010f0c1d0d030e0402070305030a05090f030301140a030c030b040611090604050409 87
    0x410003400700c1c0c0c0b002620085000d003010703c10302e0070454240074460001401010f941414105d8196503a41c0109201ea04a6401d81d400c1005035140c100c501000400c0d014441800d500f080180301d01030a040950324003480c0200c800f24220347c1d444006a80c3c3d002503100d60800703d01d5995041000c039000c8441000c8020016141d07054521207030500e0f504100c0c080ba13490b0049880c100510091000d640b0650f0041c004c0c1c00c7c410403c0307250b0b001010b581d03420203100312889210400c040100304841004010001c0003580304079160366100c1e00c0c05034013030f01c11031810101040c0707402c4804504900c9640c1c100c510900740c0b480c40318004000400d001d80050104400d0b0144213111150740b0305612a48002e052183c000d503900341c0caa00b0580a0341d01541c8016288a50301e07031100c1c009064481c00402148d04560b10408141d0300450008003245400c005a84060000070f8080b900109120000041d035100b188100002c000c1c4406601202a8601842c0c0880b0703040002400140f02074205940100c8841c1d008101c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 5981509 1250 5980259 5980267
    0x60e03150103060f050a0c0507020402030903280f0302030105010504050402070c0b03010909061404031709160f18111b010902040f060608010b030f06010c080c0703140d020c0306010e0606 82
    0x981000c05140a9200f207540f5a56250040707a00c4c800d501c075039a001900c10b02c040c04804d81c0848003d000e0300031500043e21450b80000818440d907020422209842ca004101e40420442c800030b08418001303551041000c41c650a0403488028442e100301ca05030744050711124245030400044c40001c0d044031200700d41d02c8401a401007070b2224454061402892105408079100b03140c3d1070090241e4055031040403080d65450203100c00260070001c2c0c41c0002c1000f10420708540c1c1d60079082498021000410b42c4a803240180204200e50400300c0322088e80d09100082d054101820603201c2100c120711158403281c0d03024810410f00405082c0315131391003210b010003c10540c48540029041301c1040b00c60445060b622001008441e400074040760042c159a0412421850200d152101c902401448281040118410310013003201d054140c40070205068100c0e0682503e03403520300e105000810324422240b01e0446545e40031840010108100c0c407014001d030280c4c0c0d182c05c2902501c02c1010348442d5201c20140 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 5982759 1250 5981509 5981533
    0x30406090506090102090a0e0c0d02030c07060c023703030e010f060b071208010303050d091703190e030f070b0c04180204030308100308180f04020c0106030209060a0f060e03 76
    0x20340c2e80070310300200c001603840c0360a004000c07940c00140e2151000d1140c40341003151100045003503607071050101d000540d40340e07502c031044403080c890b078600100f9841c94180350b0f03c180c1d540050603128207107800c521001d40b02558180e003003d4025015000c041d07681401000000288245c00c00e018407a11400040380c007004d60b006075416030f001504413980010002c80e004040c44072904034400585032608094101e0750654900501a1040c40d42d144541c1e52141422820002442880500720503070030803268032030802c00f0280c1c0680c1200340c00000313014140300602c0100d01c00070044540d403080b4120158a0310031107650302c40300c03c071004203004042e0302c091000042c0741c51100c52811320526800d20040e40c1d14110700d00980145005004522107911131081132000501c5e1000700e07016807149030029109120b4040000300c05084440e403070750b041030006c141c0400150781500300b10141c13803088a5409069a446050260840030b6118104400340e03200d50030400507001d850403d12001c07029095a007004480 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 5984009 1250 5982759 5982763
    0x150102100c0e1302030106020d0c020a0b0301091d0c030c040f060b07031707030b0f0402030a0b040e0102090411070305040608090f01060e0601030f0b01080705090d050109030206180102040e0103080304060905 91
    0x200d01081d0210380d007000804118946008080000c0f01d402d0011411541003150080d91260350140c194140b0070a03000d040c0541d0b0303078100040000d0202c041c0c5c0310f81e69030311400544041c3c0b0181c0d8030340c00d40c030070b4417400884a0320300810301c0411540081c008200d000d40640410000d0220142881c0031295140d40201e81091244003e14505000e51181100c900905c4017140d403103440100700004152900300130080550711a6042c00780034004603009601c0c0d03142c0e011541c1c0141030000c0351a50062410000303d81281040d0080c10b1f4040f01120104400243c1c0710f01c2205a100f0803000078006503082109110032030282c580c241d0001da400b42141d0b0ba900c41ea09505085606a821401011501e18100a0103690600035113800c2c0007015410303c09401b0788000030305004009010001071101c00b08888109495104250f5845500034009100003651424041e49840c1d007980c06459507900312070903e0414005000711400c689101e192006260300e1616001420740000e00100c4c1e0058946000402140701 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 5985259 1250 5984009 5984021
    0xf0903070603090b0907050904140f0601030c08010c0503040206030105040203040c0b0304030816020c010f030c030b1e01030605010c050604020402090103091b0608100609051201020c0307030201150b030f15010210 93
    0x5140c900050307442030390405005403180117001e840c480d0f1000b10240312588900f2121a0040e45c42281d040703540a01800392400d010006024103801d00c00c0f41c000009100300403621504440340e007802040030400350f40b0100d69501c0122006900000d00b00010005420a80d0055521601882145074070341d440300c00c2e00714154000e40d001d80004001e10140440513041c0c00d40c01210440a0005001801d001c0c00080c182e00300c0030201a00b810b030741d0071042041c00e01a810480e80d440d40200164245200140341e400c940380560501800245007000118055005005034400d181d000b4008110940c0c8603802c0001950146003100d0406840f80400c500043d0b0650a141860b0380c080e040c0300c0454201a40140600c20044c034180d02081c01110030403490f504000110107990043e11900c00000c00410003602a01c240c0b11480c40900c40011040b00785035040d03010115852406a00c9001140c4d5485401802d000c1514540d0100b09040085100e411000032100400780e01801030f200a03014010300c040440b09 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 5986509 1250 5985259 5985269
    0x204060b071401050c07020112051503030c060a11030c0f070302030f030420010201020306060714070305070e0f060109051309020a05090106020106030311010c020c090414060a0b040c0306140103020f090307 90
    0xb010300118005000e000e203561240c0c1d90040b0324100202600000c11030840b2103c00030f51141d81c0c02c081900c808100010440c161806000c50f656406d00001c595a114800c0760780008041c034200c00c1101c20384c01c10342101c0c0aa41c175100d08030304000c01140c40c402a6407040f50300b20306500c0304208a01690313898001661140f07028a13482c0c1220a41c0c100c070401c0f0a100d20581604592040040050b20b0355407005582e445900580f182500b03880c0309150500d00544c0d074001901e584138070b0304002049229011146c3c42811050781110380d80c2c9800e001510000c8050080b81d07408015618400e00b1086aa80010481400204103412290756040410071042082e082080142d441e10824400d05030082103401921007004000c20106142c500d000f03456442c031f16800c0c0c0c0325265400c040386c14040c141b0100b019007080b81081d51007030705140c980700c00101101c1e00818041d9050081c3c020300940079200740380403030790545001200382403074900460003540b05000090781550144a8815152410000100601 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 5987759 1250 5986509 5986523
    0x706030204050906090403050d09020109080a0501050105120a030203030703020904090215030121050304030204020313080409060e090d0e100201020409050a02030a05010506130302010c080405030a0318081501030206070204060b07 100
    0x81c101030500030f04a80040003140541c070b003903051100082d40081195408203840c40000740b1454075100483c5c1e402c01c0d6030b2102c405441401c0d492418480c1c10f43c80917048070000c9600c2e940b140090030081d40c98803101100540940c0040c030000d100903000c5c3c0c00406500c0c000510006a000150f0b0008618a03c0005618546035001c80140081c020b21655118500421541c00c408050782d0768505a992040740002801290080003266441141c00240785031168440c1c0d4841d16161034002e050700502a42c0700e1000d00c214101d010600364100801c15a040741119a9994850340860040c042c6014089200c03e08640d820000010a5070443c0701e40f902a01c8002809a902d081010108003940c1d81a0041c40c03244004200c5948003008200c0680200d90782824003e1450143d4141070701075003e150303c8070344c25000d0f48070a14101036101900c030780d0000d0390001b4200c5d1191030380e07a9076940740038080107001860950401070000d0724000001d00800341c8010400309aa5440d01100211030308000b204031445 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 5989009 1250 5987759 5987767
    0x70b01030303050108030c1905070f03080c010b100215060a150e09071403070f03090803150405070206060d020909010f020a020d020c0d0f020603150301050c090310050402010c1b0807060302 83
    0x582d041c0a0607004200d034000460600170307680425030716034090b40812040a8a1350800e402040414071140008113050404940442d40d2402e01182c5944401a071502d02d510b0a204c030000c1d07181000411604042d168002c240702e0181c241080c0c20980c0c0505450b038042d000d0100001c003525013090302e00b0b0440c160355840c400840001c0c140a1a054081c01c410140407511988100174182e9200707032644021b05183c60283d581044c20142c004045e00c5002800046000040100001102a4247c1009010b480c01c1141d56500d6400701c3c4c4400c010741302d03030398403003035201c070500c054039000d005c094216481000010f0803000303451804c0e040303a120741c1d403150160700101030050780190184101040c0c1c49003540c5806c0001219610b10842c2d1050540091141501001084c0050b4902030103140c0f02101070020825420b0400640760b060300103040a078440d2040d000800d09001c11801801d003d01c0d070684030099004031581d6440d07404001102e03490011048001c001a84400030002c0c1402809203480040e51 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 5990259 1250 5989009 5989013
    0x2120307021501080604050604030f09051329031b040b03030408010905070603050403120f090204050403020c0a0504060e07050a0c050106030c050a0e07090b0901050c0106091d06160e15070b0103 85
    0x49824140e00c1546982c0245c010030001c1100403840c90f61080d4145403804a942010304161030854054105540161040b104002c000c0a0f9a0064025800641107229180c140c07051078007180010b01c1c1b0180c1c05401010007198003405401d00900c06d401d00910210f443d00204020034a580c0090340000e8007a916004040240002440200c01804561405000c24603080d10b0280c102841001000e241a5071000d084170b8a818551246515a500a1081c405400d05080003940c407000040054859031a42c000041c061606100d00c40c2114000c0312400d1040e51000b400395125044840000148500d60344001e001400c284901405140f041441e011161304001c103010785520541c001c038400c04249014801b000b034001e40717100c00321020700d00c0b01991800031100481d6135001f089403191444d0f08000d000308010003140c0122441e2030100510801c10b12100882c00d42c9c66006480c18030341881004048040940720f0a00f1018440000e0a1281009000030309a001da0307004c0a8280c89040d405401402 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 5991509 1250 5990259 5990293
    0x1a0904050105041e080301030f080405060c1018030206010504020f090a09090302010f0606081b1e0304050d020114011404060b03010305010903090503010b10080901060e01030c08060a0207030806040504030212030702 94
    0x8484d000b07052240f01c10f0303505540e0f603c0d2a10041c0006484840c10720b1031002041340c420100ea016000250400c2d40300c08c1c0425103e581c40501340c200c400501d081c48024020312440c890501030241c1c242c1e009007590391821003444001d43c0701209010424008021100b00e946403450040028690314500103101512410000d007101d541e0040c00781614101441000f220794482c140f26006128030512031031005e5007080d03031780d40391145c2040b20820302c011641eaa00f507468840d0107184242d007c0c9007902c00c0c200190104074204c80c1d5284941080708000401030106201e1041144084a006800010502c0c0c81d07026481158000741e10480d081d0303440b90380346401c00d540500540020a400d80c024052040030341c0c001350141403100d8a00c810806542c00140c1c00c14000d400900c01400511605902540c607418144901551030151003401e20448001c5a90b5a269208031040c0700d82664a00311591501800c20002d818003801c01e40c118816541c0c1858104403010095010380781540040c0340344191044050 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 5992759 1250 5991509 5991533
    0x50c04020f0a030b010e12160b040e131505040c091505010203030109020a05070c0f060215070c140109050601060302030603120301080d030504020102160b0d0506100903061a090405010504 82
    0x1a006a00500000d000303081d222080d58000c99141c1800b103a00e01030b0200491720181364540c607031307440b548070348001c3e46000e004642c08840c1d000745107150303004540b1903e034900700d031091f482548035511000700003c00b10030b907240030001c0c03841c45480061150310347c1174218010f072601541c00b590402c08000082200e080e15100b091500b81444001c1c41e006854000081d44070300051003618505600058041841c0740706604440740c6960080300c40010719113846d4a81090010f50049101610030000d50017200d0054040d09489402a955480d22042080e0744070580982c85580881140d903c0318200000180180720407400703800e03503035070060700d80c5080400c261800140c05190400308804100502041c14041905415036240342404502c076100c52004070318024018040e000801403460002c070f581d2001000034a029000039405200c41d894003020001e080003640c690340d01003821101300f000000d0450f0440103c034110000310101d800c0c4201301140104a04482c21101c99548400300410840075170051 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 5994009 1250 5992759 5992783
    0x150103050c04180c05060307270617040b13020406030b090d0201060501030603080301030209130515040203010c0e01020c01030f1506020703020405090312040803060f060c1b120d03152105 82
    0xf414070550319030f11104002c50013120300400740040022182070103000300c017018132100c01001c140301d0880441c0d214021054010729000800b85040c02e032515400c622038030301036034001142d040561945502805901d009400c1241c0040d02d0700c3c0000301183c0078110181c41003854001a00300000204002402c5642d80d42041d8141460590184082003a80040d40e054a034140d0700241c00e91142c0004181d4000e140f04004d205102c0e03583c868880702c21541d1220300581c400d0700240054412250140d407140700f031460090041e80411a4009150700c2500449508001024006020b01c5d84401c50102007206800c5040968410781e030800450415200c1c00c2d90000045025606140d401c0203401480140523101802003000031004c5041607590501d041d0500d00024581d0b0b9641000001c002d489a507144584074071b5986110200074182800841c1103240070344200544100300d0407803401d0303005082d100142141c01828200116a4000c05504866079041d85101050451031603d8103130715024900c615 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 5995259 1250 5994009 5994041
    0x303030b10110c01030f0207060e030d050105030a030806130b031c08010803040b04060f0e0a06030b09060103050702030912010b06030a090c06030e0c0405070512101404090206030105090405150103050c04 89
    0x10a60042001041103c1c03800c07024038001c16200c20300c2411602900441070080c00c2c29241c22040710108500000a001142000305d062090b681e81d1400c043d1211140d05002d03002c00d040400007040c900e0600d000f662200d002c0d28000484200302004039161240c070700b055049028090404d60601038001c1800c500500d0008025407400c2c4c10b0502c0c500d143d00440c860682440b84941035a04001d02401e10340d0b0548401600344000f003680c0b900010041c18140c182d860280703483c4c9000c02d00c81c0d4424090244662210b400840c60038400f58240003001070311160f41c61065517140070305c2071103550300c400450003040c907510003151035025401d0040040e20140d0084051600e00f5a60500320440466070144041c401c40e070010700360395000740c2a107852203115403034403150100104001a00d450719111030150340c0e2248070120000b101c0340034001250651a00030b548420107000403c014039102c580154050f100388140c80f806005c02c045807002e2030007030b0001c9801d0340040c1d20b45059070078144980f114008045031 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 5996509 1250 5995259 5995277
    0x4080d0b060301050a06140f12070905010206130b09011e02090306010e01030512030403090504090309081011071101110318010e0609090a0b0303040503100905101506080601180303030b10 82
    0x1001a5031885c079440b9000510002805841c0c44107051015260404d8041c000c6a59440704602c5150411400301ca6003408600050f00214079948001036070743c403500884035480c80c0b159440c0c40c0d040401d10001e00c0a01959204d01450501005080504800c0020100d0160b101d4103440300b01803c14405030041c2c2d86000000c4010030102d28001a032081841c1500c003c03e07502d071524103003101c4403101d40d00402c0d0030500b000120803c0592160048003162041c1c030940301a0b181d0500e888080d5903035100040e880340781c1840ba0034041541203215500390308050500f056202d81103440242582c01103020050741c80841c01c0c0420442d6005120080100000c80e50301d032405803103000090140d0b2020f402c4110b0170b90384804149498a08200701d60180c04020b0455517441d01d020320a102400055504943d9802136050072081d2a0141c000c6540284000c0410341c0207505203e4226645030380104114100045011152804041e5100400145010355008184104c10320180207210001166110410111030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 5997759 1250 5996509 5996519
    0x80303011805130605040c050a060203030901060e09120f09030d08011502060105010f050327010903030e0105100b030415050f181506120c1009050a0906051003020a0c060504080d0b060301 82
    0xfa1000c54599000d0303400602c54031681803049070450960000c9401108800b8081540f540001c0a0341c0304408000090042e9034460420400030041a1401d00e00380d8083c0150040552122020700703400c007803aa013001d003080819000649062032032006000440c10040044c003003070424981030310380052a40000d0005500d0080000d0000400e11031000802c10044013190f035820080c0105640c0840010918001c0d0500700c403014000e100c0d65504902082c50070444c00d020301d0f81801050301c65800c80001c81380141c50301440091603800100f003100c81c100c0c0c10040c40320035041489030340c3c0565400c0c03070303551840d15015402d04003510328001684600d622070113450840035005c002c8254040d0302a60002d40503803088080e02d1501c600200400e0b80403440c2440100340300e0780010047c044032412a16445255980c0038080d00310b81c00e9000703442d00218100c15000390b10703001ea00102442c0d0481c3c80d0034211007c0303030789441048a8098600300c50507800001d18945841042c0200c0c0381809049440c03910f19407401d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 5999009 1250 5997759 5997781
    0x3020111040b0c0f160b0f0c07030303050901060816030f0311010603030302070308060607020d02060d020c100b040606050408030703030506120d0804120302120f0406090b0103060605010f03110315120304080303011805 95
    0x1912820071441d00003d07c2c0780740c03c10890166640003031008201da15164803480c01074080c044c12100c15a083d0710b0b04400080d6401d001031881c21094203030306603c80726401c6450f0300a5842004000360140036034903c404d40c2c8580244030f4400214001e0740c00503150500d40c9001441510040d1400d0b21903c01441040050f948185140395441e504440c0c0641e10985440c600000c7c5c041d4000d0801180079a00840400910381d8119000d042801c84041100544801090750140668011085075910520141d0000303402035000b2030300510010804030f20550301d04817152500c040020807078001012101444108002c01810b48003510050074151b01340488a956602c002034004c05403000b1070015004a802c0c480d1a82c09141602d40041070031402e50b84a0030408041d0069110f2140090301035100c4c02030603842440347d402001402203890f851a143e00080d41e00c8582c08207065540201090504000914100000e00c010103008000e55141d600d0b0030132010403803401e105034480b514240001c01000043d4 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 6000259 1250 5999009 5999053
    0xd05030903031302040b040908040e010503010e06040303090609170703020105010e0603101a060c03030106090902070c0302010c02030c030105070914040b0d030c03050f03070801031202010c020c01050703020111040b0c0f 96
    0xf60201c200039510b0240000341c0545210080340741c001c3c0c40d043e00b940a000d4004014001e880305110301a00690342c90051608071480361782c50703100f550002c401240000c0d2098001502c285d0003481c0108030240151918440070348210f0540b90302c404001107101c20590280036450041c400e10341c1e0880e481c6003c901091b00c0782e0720005011107103580d4203516501071120003031010800c0701c0501361a4846d4003444000d5500e031700a0050303101140b0008c00c0000d2440d1203000b1a40d48030380c025a510902440d641c019200d880c3c54100c101d80c18000c642c00d18906840034851325201d0104c03903039010b15440c40c200c9581036813443c02079024060750070005e41c0d00650f141c2d40e001140c0700d0b925207050b0042d2111400d080f103240c09601c0d0824500e50000051201700c0784e00000c100e060700c0c080c0a5030009079407040c0c0260308072045610302e0400358101c11075030001580600090040c0e64082e00020451449454240400d580135030410850044089500c900e0020100001812211107500500098100301c00041e40161 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 6001509 1250 6000259 6000271
    0x2040c0f0807110708030403032604021503070309021008061005130b0903070305070312080c1303020f01020c03010603050a140f0c0d060b040f050106030b0d0b010b0d020c0706020f0d0503090303 85
    0x280c4080e88920700c2400f0013510004051180582e9107a68a0740780c02414800402d44000e0204d0040b4142e050361902c03074421600465004104082810204801c0400c80d080100038000b8560b0380e0407000050303114401554101c1e882562903000d01c1c40d00c0310400c070f803586118820780e0401c1000d10591034664800b03103040042e2000c1541840c0c450030780c0170010f49481c441d40c0008000d40100c102c000208490361640d00300a4409403101e07029580e8450030f2640c94000c0407403450712413556400c00c001600308100800c502c12410300c107603040c15481c0c80200303081d144a644201d4403507104035028410b2003645581a00c00000c081c000d00884070301082c00035507030700704401e0031442a00504120420072141d54840404400081e01c2840304488140510b40144000d21400313000c80d082070510201c078a0621040700d4160b038400c1081e40c069090030214a0780390070150301015025030821640c000b0344010810100142001c0d4014451440b0100300b43e41030440c005194070a21500f413050007660300002c0203072a0300003 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 6002759 1250 6001509 6001517
    0x5060406290d060308070804080606010507020d110604050a0b070b01140102060103032105040809010e03010b0d080304060902030a05030712030515010806010225050f0d0305030705130302150702040c0f0807 90
    0x2030666034002e0040c25694402040300c800000c01da8100500c0c8405081142c4590094030010394076140159003900c156030f402035201d4205c006240005840310f91040c90a280940807600f03258503074010840d8245030750401c511810700070485904010085c00460302600700d034500b00c2c1045500b40700203940c50506000042c140003041c2c0e00018002582c4181c0910050028424400d5007049e0801403591703400b042d5600d000a0250501e00440d003014040e0700311080300074000c1c0411210b035441d00d4103140c2010b80708a424603100c499950250350704224042d107160084014503175419651811031000030300e80884109040c1001c04100310103030440c2c8101c501c0030081c00c000005030b40e1080102d04080c1d4041020301c0d12102d0005488403602c1c00c20000c01581c40549080048500d0802003101c800c0030910002e001450800015001503ca14003800381000c400c40c4220540d074482c1d0005100282142400083c18004110442945854041d0340180c0b00c1c00d04082101c0288014002e2400c0350041c03000e03081c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 6004009 1250 6002759 6002767
    0x1170403030207080a0801080606010206060102100c020c04020f041d0105030a080d15060305071b0c05010e130504050a060f0203090606011b0f0c030201090602120307121404060506040629 82
    0x3041c025012640c00700c1d44540125a030700d50190024298070001e0154030040d00c1003030001640c65000041c400d024090580080840703da94504c1c0101030901d505160301140a0080c0c654016111800030300b0000301c0d001c0220ba125424411100d0401c400c9078002c3c00d06890309401004103840108450004d030782c00030b070002ea585100c03800c51b10181c00801c15481421111800018413650715078070550060710b00350703114000034191160200591661250192001d43e007003004002c00e6004903c0540011800b4102c08414520a0440011280111010b54468000f0b612038001c0011921a41707541c1e80caa00300031421814a0080707d80e48100081405e4188100280c2a0f110001180c81c0030701010740c00841981c01c1c20152070400d400c461340f480201d01103580303d02d010901034000f18000d00113400c203414442c21030f503510350126045103a803c502c8003c0b958620003a05200240b80455110f1030040324046000e080078414001220059840304004486001006610038030541080d0b01d030a002256154035 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 6005259 1250 6004009 6004013
    0x6090303052505010504030e040e03031f0e0a02030906011703030601140c0106060201020702040b010e180601030f0c03020306030d05041202010e1203040303080403020105060103060303090905071e0207090e0309011704 95
    0x500340c0307811000b00d2142107510380300c1c00c001054104a01c00c40c400c1d075490003840d0015040c4410b13180c03c440c030000aa001800050300041e6040251300c1503101c041408505c559582c450f032040c40313400780c4005001503000030801204880400040c1e00514041c000c05000d5141c0016140c0c40780405000340741080181201c1a410018100580701c400b402a4020410503903a040083e00030f61002408900481c10401388440540c01684c0110008a0107400305840d101440d03900360410034014074940c145a40c1da41d042010b02c0187c0b113140541081a1001a501c2c1820401c01d403034034003040546002c004040205007e0b06201c030451001803982824144225042c003c0003812191401c030403041c031840040740c0001819800038459010300c1c000d070000c010300e449000044040c0e510030f00010b404142d21417020000c03950a940034070360295680c900b9a12020b03c80940648980062240c0700050380700a0084c00002010b10403a003620140078001c600c1d007803401001803d0080128107040001c49040c0c00101 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 6006509 1250 6005259 6005287
    0x2030c060609010f030303020c0a0c1403010506090402030601170a0c0603050402210706050f0405030307030801260d050304020102010209030105011e0f050f010f0c06020a0c06060512120a0908070e0901050708010609030305 97
    0x100c0c0c80d44048582d44bea61181d0b41241903a0f82103200611035820030001c1406030802c0805a40a1038015000d0011682030401100c0c801c01c2c951038842d882c0c8110000c2c0307800300380c0180300c00020704840e54000c01c13107061500400ca610880d541c2c0500162080000c20059810300055000c01c4440b141409502d404510500788524001c9600468150100240e08800c15074841d02d501d0580c0e083c58280280740c0c01e86006908803210680c0015a00c5d48a0900c041c13406004d08065940244140f0025141c401c5000c080303801e681b420703845040e8045404065104ad1110083d4042c0a00715022500d10490302d820001000408540c4843d8144039254846040c80c030310a8031441e540741d4000c4030035982c42e00b240c40000c040301d80e520f40039601107190000c04141751500388000c0c00c2610010000380081e801c0c2d419030102a62140070f4103414003407803400010300b5035420b015140c010501e20003d465140f030a061400c0c20b50f0b2004101030100301c183c80c01842026005520720080d240c040c604a5124448004585 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 6007759 1250 6006509 6006523
    0x31c0c0e0901030501020307020f0304030803010504020f0409020a020c03060a020702010c0807020109080f030a030c080403050901030b040e070801140711060f0405010f09050c0411040f0504021e0a02030c060609010f030303020c 99
    0x341c00840003000803060190540003140074030002d608807000038100c42ca01640380c1c01903000040048004200402007458036801600b4000104581586042d41e0740121a040381d1040d0440170140c0c01c900300100503441e040c0a19a80041440e00a520b0201aa4002402958010300c020448400400c06c081564031600c000700191019900301c0c0c08054543d07005a990360000d42d002c0700002d00709510b2440b4584566070107230250b030b80740e190a0700307050752800150050109105555000382d0f80f0001f40c0004807003000510300034080a0000284503c017100f01824420004100e00c0030301c20100d2000d03101d41c030001411341d40050600d504000703d45a0707181442c0546001603510034a641840c00404c107000c80070442c981c0146d0111020021a140c02081d00714501a0388500c2c2c5101c1521003080107181802c0d001808884440f094450a0b04400407080d42d40390402540600164004102c065040408202c09600040c00b1141a8542c2d032500d40100000c016500005040540201e04d1a0380e0700b004002c20 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 6009009 1250 6007759 6007787
    0xf0d0903020601080606030d0807050c0a0803010f03020a05060a05031f260607080106080601051309020403030c1a0c030a020a030e0a050609010c030207020a03110a090f02070308060102031c0c 84
    0x6108450a40c200259074a50a0041d94941e000750000300700980740000c0e004c0191009601c400c1e04035500e900c0d0a440540020b6080d140070300171000303132400040b5108000d6018003d8040049085425401808507a0301307680c000600a407030820107201d02941100c15a03901c100840c4500d080e509a1031110451310b2203c1d4003900140c800358035524541c501d82403403100205103600856081d41d484040854110400388030b54004682400302080c02c030351082008051452442102101e00b03683c5840f1042240e000758030030f80029007100415410800c11404c1c5141c5448056901d00603070a00901e09069813002900000d5141d900243c0540054042d40090950f400700c030003528012035590070a151158801c4942140e0365181021080c01c050007807003624101c41d00540b03504805821666503400d10010f00340c0c003d50065908100007074681e04c0d07005a1141c100c0c0c00f0300258440c1040c3c03402600412000c1c0800b0f056420500c0050aa00945003c10340060480c03140800d036102c1201e400c2c0c80c2070a1131140 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 6010259 1250 6009009 6009011
    0x30e070e0412170c0409050609060117070201021201080c0f010810050405040609020301050f07030f0c020307020d03170405010603020103050106080103110906040b0d030302070b0108030304030512092b140c070b0f0d 94
    0xc2021340d1340e0b0100900110b070b02d802010f0010b540e030300c0c04000e00d039981120171758003040c69050207100c0d038a84a804103500c4861400010301d4450483d80342d03c001d8200341e004401940c0803612020f6542040515411195428244400c2c581010030210810110fa8000d8074016955400046c0034001315400580c1f000b40c005d002040542060300d034141764110101d8070003011900b04000e40200100d18070030150b2b100c00641c00746041c042a80c0c01c01040e00503040c801e60412001d8100140c00b0f12208032a03070b014600c00c00000400c68a9440090700703482059200205020203039004002140b284100801482c60441c1d48400c56501c00000400918060400c150000d481c034408800305905940281090b5000c0c40500340307240c0c0c1e280e8020b982c0703110807240140001d005202680d054079415140320340100d030078030580c0c0740004070076072441d400e84016030001003402a049a5081d03054100080c058034081e03e000452a05500408155030380c0000c0c0b02e000d40708907001030362001000901c07082e10040d07611190 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 6011509 1250 6010259 6010261
    0x501030b04060b1002070b0702040b04050108030a11060105130c02010e01110c0c060a0f050a02070806040807030f030c09050f0103020d0501080106030507080303090c010c110301050a020a030e070e041217 89
    0x8208049850031101281d01d145000c3c108050f52500003850410301e59250300400e006424006940c04a030030044040340c1054a6440761003541d80d17580aa903002e0510500210f0319001702070300041c0380200b4482a48041d42101c0014000d0781c862410b0045a4010450081104c4020020407401003162000845c075551911140d00031146084006001d20030000c003c6484801000042100302d00c110049800071500001c00010302c02c0c0114050501c0c03002030300544800c507980d042c185051a004542c1210fa80900180000406030410000301c1c059040e403808100001c540480940707800310a02409200e40480b84171001341d41c0c42a0101c944103c0050400e1005503900c0c20140c0c06480680000c690700d0040200200b5002000400c4d40d02c50f4cc502402003a00b807204100640b00c0302140c00c0d051714000c0e090008001d10703440034043c0b507000b14030003030300107031381e000c40d2030700201152403006000100307400c446000c20400010121260301b10350404a1100c1412542100303540201c1521161a0300901102c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 6012759 1250 6011509 6011513
    0x1050a0c0c081006080304080714030f0f0102070b070309030e12010f1104030201020f0a030905090a061d010806011707091512110a05010813030e0609040f0617030406050406050706060504050103 85
    0x704402c10f01586181c01404503940b214501500c81c007aa003e500c480f988076400801c24940844581782d01410094180d850000600801ea400d10b00b0003002d1b00409d0307400060360340410800b03c43e41c0b81e101320a03250421440c00103980040c9400c611000c8144036844c9456400d91142080d030001c04540f203403020030009401100c290304803540051006078094000c2400c020005c00011407050308030766042e40d5008480d824542008958000a0485130107140c1c1d55102040034451034200d000c484d80d02c003079400c03450762400070894034001d1705801003592101840e0502d25043e8001500b4800e46038a10008103010000004081da84105a4014110549208144800d001000620104840c1d040e070300521541d0b1194019201c1910940e60a2040303038100303450b1030200e80f1a042c03018480d50003d1180385400c0d007060000b82550600310f601c00701c060f6a0101001550030300218140d482e80d02101a608281c500800501103009512640c018448000381c4c0104011260b440100601700040c0b00308119610380c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 6014009 1250 6012759 6012763
    0x201030509010e0d080108060a05010b04090207060209040612060e070501020a062012040b0703020304030c02090603160b040512010902030a0b0711010606030b0102010509070e1b0739031101050a0c0c08 88
    0x2071280c903607c0e00407440411428881809001c1c181c0300c4102a40d86410b103003401200081d40241d4043e07408036400d101c1e00040359200e024000c0240341414030b1403141000741c1461421900710a44040c2141e004050820050341c000c540502002d80180c0e0001c0c8150140e030300c00e100d01e95507604003a01000000349600c0510329078a8001e000c0c0b4090b001d240d04a41c0c0307402094049100079907015000c03c4080c203601e401450501c1010b54825800350943c2c0180c0070082c280307900700c0040c4e007180c8003551011409001c6030070f141a41c0380c0340c00c20703540013400503000580120303071190500385c005019440c10600060400f80625555521158042e000b0000d040c0c2e40c04004008107201c124203030055003440086001c00c031001801c4010b07130302e050b80051905c0c2c0b0303603409007501469200140790030003100348040f401041d14444900360440041e1204000d2183c0501e064000c03000c880b40c0d40080540a001c240302240006a50038001c410a0030301c1c69403002c1d1031005a4500d010060300500012142d44041681480 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 6015259 1250 6014009 6014011
    0x80904050705130801050402010e13140103120f0302040e0a05060a030506070507120f140a090902070503030103030f080405031206060705030c0a02130606050d0b0609060a02071d01060503040201030509010e0d08 92
    0x30300a9074145942c030384080d11700340c036030580d4042c2c00903607161040011458500c0940c03c0d64000704c0c0c00020803000300040c25102c0c0c0000d038005da41000c403880310480a03c1d0008903182920400d841c1c214506800c2c4802d25080d082c01038400c001c050340d5076001400581310072103010701840e0804220b03802d42c5001d20300144594003401084403403021429425071194060528801c0e165056250417464018000c0403006980003201000c0402c20302134000035010300548002c082d01d600a5015690b01e43c15801d01602e143d543e9400074080040303a038100404a4804400d4440344440b11224101c19101c400024000c0c0c0207002e0081c4c034038040040c1ea029828400595210030600c255440804030324512a082c0486813940714003001301c1e604100b1924070084503480110b89175002014941005081400b05400d074001000302c8002d64020101031045c02401d58000c1c68024103014900d074198108030000b0518080500300034141910344001c125610029004003412040c603a08552801c00209001405210 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 6016509 1250 6015259 6015277
    0xd0213060302031c0509131112010305010e1609111b06060102010c020309030703020d02061207050c0f0106030f030315080609010207150603020d030c06060801050f060f010309030219080904050705 86
    0x10a810700360340c07005454120141c4041045e00e900d401c103e4020240602c41e1075803542c441c080c540d00c0f420001400d0300d5402405244100c804800055815440d1560854050884200b0a640941c25007282050401ca03e030094070300960020485480d00c080700c501d207010780d641c04400e5040440342e2404031140098084c4c442c01c0264000c0c0310620b4a5001070b41c0324403a072031b545501600184401c3c40942000a04405107a00c06440c180c03070284007108088815505460400014100003150030100508100203250640808020094280703150703919142c1980000c001021306885440e01c0700742034088424500109401000e9904916118030698002e500107441103907860916001e44009407682e104100030340b80c0c0030b02004c4180078181c900340d9140d80e14082c21281c07251107000c0403650201c20b014013805502c4003000316030b0501308201040301c656103558500d03040524140c01c8030082940064001c55409110340b18045104450615414034401c140f0403641150500c028807001036405001411524 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 6017759 1250 6016509 6016513
    0x709021902100501050916050403020409030206011505030c03010303140702040609061e1505160c030c0302100302070b0601080703060302030109080a081f030303020307030b09070801051504050a140d021306030203 93
    0x101d069641e02d04407207080c040c05411040c0d90001800640c50940d24100b035000c281801802e10740c0e6680000c081c1e4616050480060300301c0c0c0010070201b82d0a4107451003510160404509515080e084102203000510001e010040000343d804803605910044800303070713900500700b070003019194100c070030141c05e052194040a4008254011154007900c0c003500a80f04000301b5140032004814040355a40c101c09401ea05442c0b4914440d0000b5401c0c00c2894001c5100301c407041ca0291450040184420400c0030340e0084c1401048034100041d07032080c2c1180d10006c00d0800c0f1006485500046004044030f1300003c0d00766117811041c9084c40050400340c0600076082c0c1e541500f907503d80c000c0b204d4101d4000c001040b0601d560105100081c02500a158070042c20320700050b60703601050004402810507070f0100d001c078a604c0300600490500800291114140d1904c02d171030249050041510100203205401e46901d5800c0311203101d03910034418012094009100c45101c03e4540c3e04a401480c032403008030700c01c3c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 6019009 1250 6017759 6017773
    0x1140105040e03040506090316080c030d03020306061603020f0106170c01020304030b011202060702150d0c02030a090608040807050601080d031803050a0c1403041401080a0b0307030201050c0709021902 88
    0x1e01e864092101c460b03034907101840c10185040184045034100b4520f56515000d101c000e0105800a103100900615800008000040b00d4400b45402d12130844080d82c101401002040381c2919582e0407295810300c4046800d034000b5044c10b00b2404d00348880784840f03c1d5404e0820020790000815044034481d45050705460b00c000ca0f20005903601c1c429807000801c0a0b0702c4200410100c0c00c81045544910b0000d8822131504c0b20950004008404101441c4001d401c0454034035071810310b500c01c100350407141d40000c600d04820002d010b800c942e45841004204400c050009040007150004e81d03545036030006c100c0e00e203075845103139164440c0814200c0f40b000916040201d41c0c3d1420241074440b0064140d00c9031803400071107103030840f1014210340094074012012006610704070400c20042004152021141c621700c601807000500981c005070007071a01c0d904181170600c142d540400e5400c21280e090030000c0c1d6884038010082c0c109103807540403119251010500e40c43d001107205a550640c0300715400d03a000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 6020259 1250 6019009 6019019
    0x1030501050303030f1602030c030a09060e0406180207031206030b010e0c070308070305071e03050105010e0303090303040909150e06010513020c0601060e04150308210103032a0b0405011401 83
    0xf49000444522181540d4907000c01c510011500d103d1184885500c140d03441c02201c2c0c50320a103946e00c0203181400103400c0e041d08024003580170446a801c0381c000c41d030a00001e440e2050580420f0240d40441c0f6900d03500041c2030b0205400750b000102d080e90185014481c0503502d0a242d600c0c100c00348121502d04030480002a401040c1804686441d541a180c0f44101d132030701c441c100c004200c01031441050044038641011501c40c40040001c4500c043d5a021070558100350004026078000d281203800b992082c0001600c0fa038011065406a0300c540a000074640c000c0e06006030069150309481e0059898036401441d0030750040781481c1617907401d5511888841d81e10381c1c43c40403842400800d1003a41c2002005008551244800c3c000d00f07c2c00800101c1c1102d0074014005070016180c0c4200c0301d40c00300142030f400303107c1c00a1407046200c5141594000301d44c91a200509200700e60318100311070b80d582c6030b800c15035a50414a150710842c3c1040744402c040c0b81c40c0c83c00e240246018094946024226800011 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 6021509 1250 6020259 6020263
    0x30105010e0303030709060f11030c07140f0d1209030206180f090402030a11010302040803040b070501060f05010c060f150909030909110a03020d060b070c0e07030605010c0b1905070905010305010503 87
    0x100502c00c541d031b010b114501e000740032900141c0302041401000708189160501e5542000030305865060240a8040640b400b401e48019100c0824014011048038030304469a075104034520f41c0068010700c4505549000c0d00e4100d4040c450750300000d60081022075410707400d6400200314200b40030f0695003603824109036000c20140e41003c880c001e500d41d02990384000000c0003141d80c0c0c0d40136803042c10003500701070302c540c101c42c1107030440d401c076405c4010041209824010f09000d414000c3c00860014070b185818400020002003020307001410650319400c92080100869000010908030407240107a115152a9810050704000b501900044c40c1c1c3c00340414000304502c18a1300b14080c07034203030b51314011800300142c000c0c2d003190348106d1200784e6401d00001c110315482c004205040c82041c0d02d140c030500300b4040204050001d801101014544102407000c1d0344c121180381c1074107801c003400200303941d0750501400c403081301155000701c5103040c0700c00c1c020000e820600e030400399002600d050205030780760001d0503 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 6022759 1250 6021509 6021511
    0x501030206030103030c02120607030b03070504020403030e06030405030f03100504051e0112050115031a0c090102030f0706021e0315031203070302070c030506011206050121020603060402070b0903030105010e030303 94
    0x40d601501c10401040024000e9002101440c03010b421580d0040840710361508000049500001098a80e5055525803400344103074806880219070850802d415601c00a052490790110280101c00000c041014040c00b0026a54a10750308020141c1e1380c502107500c58041c2121341300d4540550300b80300c00301e6000b8200c60b01c54400c01c0c5d0340706030700086a0701e40141c229550001103015103855589042e12249003407144c41420140d40203000a0821301141c1c0c1180c6042c160041440f80c46c84010300c2203030b0b00d5070b03130220465003c00101c0d460151105180d007001c0d8001d2082a105505d42482106a0300d5400461406184101c0402c411400178041800501d80c0b01c8484e110300e9640c46200b00001245540240d018064450060502c0c004d01030300c0340e80b86031070003500f038010198603140d8041f940c08001aa0040c94050701070f001c202001800c42d0000044002c0403031500a200340130210020f212034985905850800740c01103c00209810001072043c3c40364400e0048900062940003441240c4c20000704507 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 6024009 1250 6022759 6022763
    0x50d0b0102010b011707050408060f01081603030206010303050a110303090a020102010605040b06030c0c0309150327060402010c030e0a0308070b0915010306090602070602030a02090f030c0a0b030a0603050a0302150109050103 98
    0x100c0101000f0703466005c0041c03070081054040c01000c0c080403a503e0300070083c4611599080380c2c20400c0b54180407001d8a441614014060000c03011502400025030101c0e140b4116a4541409500c07905010030a490594240760320340d0003880080100029000d0000c0c4441c0c80500030380003000020340301e60074030003542d200d6600d85800c034100700007260030805407400900d000d9078441c05a030305041c00c0b0000145604211b4204260050000c02400502c10104c492511247c2c5e102100b50140d11840401c0d540707500e002407000e0305001c0c00442c03082c28180204004030b1948802000c685c00985c4914200c03103160890002956000c0071400000c82c0301e040043e5403954410468540c05850b07203155100005424900401ca1310340c1c1d02800040300051080c00510b00400f504c500168482d82d2100a11800c202001402c82c0b191388204006200c81d1980ea05c55015511404804c603030707a5640030341003000b808140e80010070610401000b04241355011030220004415460444501d9a8409101060355428000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 6025259 1250 6024009 6024017
    0x40b070503150111030d05040f060506040204150c0204091b0303020105010b0406020a0f030e10030608010b0405010b0d020702010207080a06090302070609080709050a2c0c1912020a0b0406050d0b0102010b01 90
    0x6280600c0d07015806420076040b10101700d9103003081c01200e0006468090740d0468030000009181e40400c0601d0142aa011200359011400c1c54900107110140b1950003000205214040342c0300350954481d40c2101101c1d64104451520340240c0a83d04103501ca0244800d40c015441e0100210343c1c0a104811a41124038030b034014203e0803007903114005280c1111030f00301e003808411010031100380c4802e04101c10508081d100050f0440c64040b60f607003541d04681009200d18540001888035101c0b4506641c603c0da00b4400043e2114100d10050745060725030f8002030064404c00c503100d0200240394110b40c1078540b290b03090b5900c0c2e964490043da0307010f50a0007503c0c2540c0000000340203410455000725070260b00c596003c0364038881c903520900504600c00c08003801c0d50700c0111034006c00740e003003103021a5400e05944a5401101141a03601c110402d1b02640341181380c00782e2203405550b00c03411580c01a1001411036552259509009401540500d40c1c444d4107904052050070190700601c0f6a04031a20181c503 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 6026509 1250 6025259 6025291
    0x203070b2206060602010b1305040302070603050603010207050109050303060a120804050103051b0d060501030c020c0a140a08060a02030603010507080403020604060c0302040b040303030b0a0b13060c05010b09040506040b070503 99
    0x199019604401440700355080048101072004110b45005000041c00a40c000040703510141091044103d1010b9400c09440d0401d000e020000ea40082d030b500c101d4070303145400a5681c4503180001e004e4850341401429560920301d1240c00d01001000640c0254404c49040a003030703076640010f0502d49803028014142240c140f004000d554080d4015503880015042039008120b5110198002c907004400361000f03455840e0420f0006507054812140488030b00e0000b84941c401c8000001c64003081ea0080305425441043c0c3d0900b240c4608440300040d00c0c040c4107903802450b08440200080d0811031310f03d0711a6081001141080f07000e40e031682d000326010b50181800e0f9690381c4502010748413141d140e50804d5800c000c0003500015010107040610305c0380da40400c1404246080107400411600710225030801006600224505c10102c03c3c00c0380d4540c141001860321506140380105852403401380c01c009841c080008110010981e81c1c07159100b82d08414041c0c44a5030308070b0b0030340401c90762030400b00c140c21 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 6027759 1250 6026509 6026521
    0x3030203060604030b010b03040201030e03032403030f160c05010c3203040b0c010f020a090315020403020402040308070201020d030c0504050f06070f0825020105070611070b070801150203070b 84
    0x24005550100c03014081c2864a60703a903860f00d080300c0342680311502800d800301c240070446d80d15000348000455401c004608605200b105410901890481211880458046910540c400340180c0314001d226404036911110b40000390046007029400c11150006011400704085d030113501c0c0845065040121510f50500c0107201c0d108201c6003092844841045041030b21181004200a1010300443e0060b0b0742c48036041010a42034903a1400c2c07200e03005005200d960542507010684004aa400491240164900d110024028840c41c3c0029400c0b90000170040207102c01003000f0280a8402c0c1d00f00c2c0c407a80344c0010304408648400b8588400600100b1080006d45001008074407400340042005117050042d5070741c001d100c0b180c400100d403500c501150a8400e1a0402019581d6280ba031201c0c0c0c400f030201c0d90000b00144034a81c0d00510555580c028910302013a01c2c000d070780c04550b1101202e09941407140002d002c0c0e40f000d1040c0040070900b40360080e1a00e1011040e140001d038807034a001c4035070300c80d4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 6029009 1250 6027759 6027761
    0x90503030604020711120d0e030a080d020304170d09021008060109030206090103110c01090507060f0203070b070504030602070507030209070e0d0803070509030703030e03060105040615080604110703120e0105040f0303 95
    0x1130402c0d00c2c5452400c1904815640b15110500c40c48041001080398850100018225408a8440510a80103124800040307880113046642582c0b4403440183d4a03511031070007e0111800120000c24500040b42d09a107c0c0c8207588003440e40340c002c07544824103000d101c00448552804442032800254910800c00c01400c00902402e40c00c2414100440c0d60b5500200b0050341d60000c0c90740d020306a44502118050000500180307019200c140b405200300001c003c3c001e940c910604070002c1001c0c400000061005200307038240c034040d42d40900113640c1c654990800e00d83e2064140010fa00c128500f00101358506e0140c2c400c0c03c0c5043e40544000203070005510341e0403880e00010000414001c0400064030780d030360240304500280d48a030311201c604100c101d050501c4d021058204031f0040e40f0344441401a110615501e100c2c0c020985080c01d180d64901c00428040c001c1851f0b04441d50502003442410513070011071415804843d9001007101450070070041c0d090303071019240a001804000100030102e846 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 6030259 1250 6029009 6029017
    0x916021009020619050d0c050403020102060403110106031203090507080115090504060902060310080c0f010806091003060e01140c0f0901081503030304110f0904200d060507080402100309050303060402 88
    0x1000341e800c000644240c0c543c180b0080c1300300b40c000354001400b02d0012000344500b5445a14525207181028116070010f075807200e0140c0043e060200958120510329000d411220145034810131a5000490144029001d8080c001d4104c50310f002e960004105020148160403220303810100c1601810725058015000b000e010300300340d91458a40e1001005612540001c50081d1001060003401e0361406030120300340081c44014910465400007410300c26a070051290f600400201c0758004140c64022101c207000d0100c0d07100800c9542884061110140107610050150780403620382c03440c81e0349500045101c1e01ca03a514840d4150000d110194141d481002c50a80c0b01c8040743c48148103450f40c60009246800072a021520080110040301d400c0c141155842c004e64802d480781103113801c00f42e660040d0015840e621080c0040424864030700d59883c61344150086030000000c105604228000038141c0c081107500b40d003e003100004a90803d442031085001d05030304100a5419900d0f8041080040c0d44 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 6031509 1250 6030259 6030263
    0x60f070f02070b031003020306012306030a090b070905030106080303090a08091207090f1a0a0509090c040608010b0109050303030408030f06010903060f060f0f0308070605041406010b07020916021009 87
    0x81030a4000c0740b0903640100542c000e0205641500141c2c0c95441023600d804816082030f140401151540c140d10025403008024007070040700c0082d1280e0301c1c0030421008044507000036084589040501ca20203802031240c40a9400a82c000d00c000e43d1207003005566444284d07024402a40102500e4021641d28806012510802411140c10130400d242241c9800f080e600051070203581c480d5180403242c2207110703082c40c207a60640342d00410456540042d00c8540e052161500511003d4000303407000505101c1c8a0f510b000041c020400243c031261001c0c0209070a101640c0441c81062010903103180000a89104591007c20549142c1c3d580110446c00c800284c10b160610030001c5001c0001000707401410304020070030b200066002d2074030142201410403680903414540c2e42070010b20108500100316039009411071800315450300c0f00c6c684044045000c60325a1054000c1c3c2e000070075000d002c031001701010303402201c1005035510b40b544110700e40e603041d03c00703080542d000c86181807a00529400c5694098 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 6032759 1250 6031509 6031513
    0x12060a0203070e0307032405011508070e040e0601030c0b0c0a0f02150304050c09240402090a09150603050a02040f15030e03030a090201021005010302101103040f0306020a11060f070f02 81
    0x402200881c0c83c0c50100c0d002100e07001b401c0c120702c49a0030307001f0805200d40b0030311031030038015545881c100d0710710614100c0d031001c2004612000252000d005149038460f411011740100142641c0c00f03806510b0344003c0c001102d4050340c410000448591840030345106000d250060a100f10955450942180803090202c2e0081607102c00c004004205401a500c160b00880280c400144207204100c0c200900400c013240b0001e0400005008907017500c1c0b81c01703c5071010348005075100c0c10800000c45100300c81c1c2c0010b0240c0d0400c0807040601d07141440c0c10007290b0b80c984003400035864070b0f4028410f0340282d0040d105a03921403503040206101c0d00e4281d4941b0001400d0000702d5009107080030381180d00417141046200e0f1100844011564100080c03080035104c244100040d50440c1c1c00500b0b0180d00c400040300b0441004007081c4000c50a104480c01030100c44010440d80c0c0c0d03645440d0f4043d400456180003c500084015462440007107a90791142d010030954640a07620b44000761090710801203401e0440c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 6034009 1250 6032759 6032777
    0x909010801060e162706080f04050d1101020f0c010902010f110607030b04020706090308071101140c0a02030d0c0306050a120507050108070207050d050f0105160503041e02040f0f0b12060a020307 85
    0x800f441c06070401440c224000288031701d410208041c01b400c0010f0030b1964400360001c1000702058001c6151190261103203001a11101c0b500c03074460190140422202c0d0380c100004001228800543c04410184d1013030f2509401604a0b1405580210b00c8a41391406904a03500090300980702e90311010000000030030050404031640c03100700482d08003000c1140414100001c0c03281c00d507004000c0381a210400300090001c1d030001c1d25101015130010b801c5c2c1c1515000031074815032160007031090790120000a0000c005a080740c00c4002c000d040270344580f50190202d030781d008c51558940c0107805801078000d801042c681d4540401140c50f4940284a001103004110002c20b40c0da9680003030001c402e0194004040507440020202e08452001d0080e400071880d651300c095a05812600381c90344142c1280803554070030f0560068807024400308100941c00b0b4600842210721902c1d560101c01d1045817082c08006441e550005e005000d110140300b1030307142e44400c0000d0010a0701d0f80042d40c0c84400703807800e1044 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 6035259 1250 6034009 6034037
    0x30506041415010305011502031206010917010c0905010509011b080922050a05070c080f12070305041106040f03060b0d0b04030249030e030f0909010801060e16 70
    0x8a001c080d0340108910800481c48181983e16002d0180588031540052402500350301010303540e4440c00d42101c03a038541800008500e81e014982d054000c00c4114400c40c40917418000c124000d10300201000302103940312034041031551151058461002d01a115952040c0c600500d040540801c2c0004440130401080341104540315416805407120200c0c4442d0310303980441a070304090350b00050a41603a146407900b04003440d5031000f0b0200d8107903006455135540c2e0000811520f1640b081c0144d0165600300c50b410304c502694954001d52090b8051503000e40c011a0070010024a031140303119030a0508141c03001400440e6890307111000c1f001c2e00a04071507880d1010368401030000d1046500b54096003080b1082d400b944440304140e55000c030703c0b0400702c881007001c4400c00031800f464030b1501000260140700030b144500a50082484440c690110f84d1202001c003001c00b03640e849260307000c0c020540640009811300c8140a80010740d070740c0c0d42e07a04e41035544400d603462100e2840a825402c00a440e512405 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 6036509 1250 6035259 6035291
    0x50f0306041b051e0306060f030c070506040b01180903051e04090e031b060103020108070309111905040e0106050907050702061e070b0f0411040f0e060f010303140c030a03050604 78
    0x240d603040e58980c50349800441484801380b65407a002164282010400c10600d0f03038406003110b4046020040d1141c80c0d8865100c1c0b400e190046c1c2d00010101e01c82c86040c4010300003118029030489110312040f240e441e0501c040c0c24281c0e0810071004000c00c1091114100400c2a4580c038100c0c607040c407001c281400d03603820080c010707904210b03503601d468ac06c000740d00199014440c6a41e0800030f0314800420302d65140d41d00082400300f000300071a00b00f6568004030000c114180041d1003018000800d040703000c1446010342d000160891007900d00c900e00d0310403407100e2160306024000803180002e002c501255283c0ca0250b07216406044101c0c0d0140c41001070b5000215400c0707001c210310381e100c201107840e56070030302e40b0f441c5081020300f003828003042500c2041b0000d5561283c081c4100016240400c1d40004141c01c10090000310001052034001c01d001c01c040d031240b0303080d068105c80c0a80e41d21041060708408040040c800d40c07500301d100340c20170424200442d00a4110940104d40a0400101811112804030b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 6037759 1250 6036509 6036551
    0x10c0611030108060105031207020405040c030f0302010509010b010c0b060d02030102131202040c031107060b120312090c040504021003020304030203090406030813061407110609040504080a090b0a050f030604 91
    0x24600d50080010f0242c0c0340c0811095000d010160010a000100000d000340c1e2801915070081c4145d0315080002c081103c080c0c0414004c5a1225840c03e4452042c0350180c00303032104658100d6550b19083d140f944030740c419005000d07110f070412440400350b121107017401b40d10456004142d07010341d02000b002c1082c04802d10440014200d880b60400104240d1041000380d901c0c05149000305030410310280b1298803254101c4d80465481000040c03490303041030124810a40ca0818120300e40408103d01e44c15030f21403000580301e41e4480d025580c02c424a00200012100d082e0390194010000390680c2243c0390103980210b400c940680100c074244580d00c00003509540e40d6800445405c000807400c1001c841c01c0c0381e041c801900c590305044040c044081c8540f40030f0f00500034040c0811044a80d08071250b15010300b00e505468010f0018021482c250818103c02c2d07104011000009242c240d0000d80d281d104010f9a04190b01999060314124450145032403c0c0c1014054590041d5140d40c00d0956800c072429079 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 6039009 1250 6037759 6037781
    0x103050405030f1201170102190f020a0c080a1a07140307020c030607110607030c020d030f060b07111003020304030518030f06090610080703020a0501030203040512030c07020f180f06010c06 83
    0x40b0950360404841c0100c140031b4036400b107440e0b0b005001406250b01582481d00114000d8609a4910111800100d10f01900e4000103410b00b8000400451802d00c0402c003980154025000c00440300d807005010b0308164011034420707000424440019460b1020900210b411000903c122100411811700090600d002039500740c01080801c07000c01d60040c024032072158021b00c0d0341000c01c4214410302001e501c410b903040100040590320010101100b1499100c0e0740034180b6409030303580b500213510344000141c24800805224548912a1001c29842402100d20959065403902d041c0b40b0020351600d62030703600d017814a034580a200303103c03481d10008005492044030010001d03d250f00b0000c09103020381040350800c2d481e0f170308410028409610340048490403204213290060340c3e640c1340d0421500380303c00e40301c0701c000256000080c007070607244400140a6050003114080c0020610a04010f92054001480c2d4041285800040c4a40489400c415032184c410304007094100c1c25540c42000302d40465402c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 6040259 1250 6039009 6039037
    0x7060606050904050a0c080c0310170115150909020d0207050102030406050a060609030302070b0f090303041d0606070222020c0a0b040b09030901021b0d08040602060702120301050f0103050405030f 86
    0x240040c20324160040c2a000030245204218600240790300504d0b8040082c903043e01560004040743c564107101c03000c0d0000b014bc60060181480705a18894043d00c100800c1080100e0241000310344040b10030b03a000302d00a642c0e200c40d81c580c2e1230b1070a040081d4203e00400d0304202c0d420b01120002c20028001184a503114480001d50f5262990181c4121005a086042044159003003440084d80010700c02c41543c400c00d04881d1150a1188440039030700c64003c1c641d0b054040400e00081d000100b01d0b1210342c044465000e003e55582c0c080c28440240205100030b5400010380c4501040c1d0742c1c800511640301c1400310009440c007a45500310078a02840c1c40307001c640704003110082003388540a2519a00f010101d4007951900c048400000d5403030138403c2c041c002c48500410f58561980d07d95200c2c0c0612035102e54140e4542c1d65410b006502c03000110303082e40143c01104104a0f90710312200c00c0b40d050320001400c91600f1021100114000c00000f00103c80310b10082007907194848030313000030b0029076000c603031 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 6041509 1250 6040259 6040267
    0x902010801150509090901020403050111070605071e0513030c141804050a03110718021b07050303040b09060403060504050303010303020706020105070e0906011b080d0b06040b04030201080403050706060605 90
    0x1000402520059115504950303481078070344603841c1d0100850b01c042400b01d494a116454010340c0d14020f04c01d50b07100604640c6400f601006201c0200050801580212010001540d03034170300603101d416801010f01c44e40e0030324400720985503000d1009405480d07040c6008101407500c036a034405040c1800d13088401003049080a014452800e004001a98101d14100c0c0e0018241035030345039502c4560030002001c0c08030b00c101c02c00300710b50100501002031038010f03840b210b580000e10480c40258082d44007050405c00f90020144035040000f02c1508460002c1c0007503190a1412600d400e0340d8100d2002e8580c402000c01c000004600680219030080b80030740301441c0d8a524501c0c0280c501a1290700910035a41010304220210340c100401b464030b0b40040e00c2011041c0d560000485541100b0f4208110a000c00c82c4404140404007001c0d0000043c0c51100304008010035080000358000d51243c070002c000e0800090005500c80c0f03081c0e5070000d205e41081803c1c402141e65960a8420b150000c00010b54041 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 6042759 1250 6041509 6041513
    0x50901050907080102040b07030320030c03040201110105060306010e150409050c090610050403110402070b04050703020f01020c090a110c030d09020108010905010308071119060801030506060a0e16020a0209010909 93
    0xc0000c034018410100210b207041d10301103011f10170340030300440078061581d1051404502ca4482d80e442030802d606071161662407500e00011002c3e40c20a55080e800140301c2c159841100805124043c0100790041c02480700303a207050300065010400070f003030070410f940740a48036109881d107004040d2154800c40c041d01749201504184000014014083d620411803d00301d0140b19401900b01c80c16a60489a0010360718003d0000c0380103807142e03110040a9900d010100001e0210102c2c074401903038401c0701c0441e42d441040004a90312151602031a81c45a400c002040264020b03501040f221007a44456906003003046940e20700355003026001d1706146450340914004c40d030740052103a024000080c810412541141c454052034014070000030803040d03ea241e14880390769101080e03407413040380203059542e80d51144d40041035420288001c9400344140c4010030741c2c500c2e05031170f948103680649142c1c60555450610320190032902d61410025801192900009602e508031940d0203008440030201e0660f850f4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 6044009 1250 6042759 6042763
    0x1050a0501060903140a02100302030f01090b0102032706040e04050f0601030c050d02010e0a0b070203070801052a040806070f0f02010605030303070c1b09060314030406020d11030c010509010509 85
    0x51209211600e880c0050154070b400a240c0016650850b082588400a0a0605103444100300c2c0195103c002824455005079241d001107114940d18904901c29990f11245041650285903407207002d42c009000c61030481740c4c4d13402c0030b000c040001c012220191141ca070109080307500ca40c10080241803800100000e00400300551031001c0314a100400c665032458550302c14042a41c0a40b600c108011450101560b01c1101039080303c4100600001c41a9601d0614a0341e80d800244100e001e8082c0440001e0b06800602c501c0c1c2c401c1c900000301c00581c101070341c0340c2d5140d000c1c032140c44558101c1c18440401c180000300b200c0da20506003902d4501d4241c83d00c400240602413142802d508580c100b14040c400340e14080280c0e6040502400c1c42140048180360809102e41040c00800c100010002c000402c0c0a560304070b00102ca003d0081c000580e500d51000e41d40701c0c070640c045e001c0035a0000714009078061144a166910001d40016241000c003204c09060075118159603070403480e912203052100390101 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 6045259 1250 6044009 6044011
    0x50c1204030506101502100c110d02010606030b030102090d02040c110a05010507090b1903020a0504080f03040311011704021309080a080417040e0604020d23010608010e010311040c05040504060b0c0105 88
    0x10150301100c0210b03045c81c0003550754540c0e21681c0582512075200d401050f008403d810180c15400d002d0301c00d03031800020001d000303003071038414030b00001d0500d0301103801070a06108a500c04e00000c1c0c030364401c010700ea8003400054040030004808003d40710141d4400e000062241502c0d09115600114aa05241000505180007070b0803080c40090200100103082c01286420340e901c0103642009a102d0311441001d490301d00030ba600c1b49226004082c10a449800701100900990380302d41c0d1030b44142021071004440c103a140c031003403034072866450000c20050301d00407034120341850300e00748041030503001680e071103410342c02a0034031801264030002448100b0100400c1d82c0740ca82000311f0104d041500c1d241d05007011400241026001d00d90001c0e40f035064082540121030086200c035005044083d0a100b41103142e03000740f0600c00000e65500010460348070700315646041f00c0e00039030060010340042080100030324802c2e01c81400d00000b008001540e407682c0c0a060010b0024900e0345840b50620043c403030075510 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 6046509 1250 6045259 6045269
    0x13030203060f190b03030d200c0709180206070b040203010902280803090307090509070f03080a0f020111030f060109050a090b040b090f04030c0503040b0d020406020f010e0706050c120403050610 85
    0x1042c0a070610382514001b050f10044614441e0214140c1c0c120025034010504204c042c070820500022090342090000404208440150b50100001c01c0303c02c1c0d2007007030018803950095000d0004c210400c0400d002c0d1501c030790040d0004000041120702c981c009803410303500305034404401d0a04105080c06415030840a0003c00240c0040e5203030000103000282c40b0710309070240d00e805c20f0b569008203031100d4081040c070004d40390101d40700890b6070300e0382400c4902da0001c2d0350000000310000c0c43d05041603c1030181c0494010200302c101d0441d10342030070b124014003009151904101581c000010241d86592884000f400c40c00400105200e14400f07020584850703881706030141c1000c100380300101040814444c0d00640500d4109001d0240d403400508510903a40711001c0340401140280702c80a240d40180101c9001d90200c0d501c2203c0288003d080e1240701d0350740003507034020540400c00c050007000200000d40c60b00c020f480459034403450180c000e41050704291010b034400c0d001c102c4609200640080500 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 6047759 1250 6046509 6046511
    0x7031709011103010b0c0703050111030103020a0b04030b010308251b090209090402060a12050708070f020d09050913050703081b07030c0909080c060405060603010c09060e0613030203060f19 83
    0xc06003031482d080900c410310031140950400111511004020310062015550000c001d101660a0444004c21a0001e0106034400c2d04440800240c82c02d01400b02c40c03ca0790f0103c841003142e8a1921000f00c103030030420310010780244449031403030031150004001080c039100d100300303002c2d503a500441d050342039120340c00054456204001300c5140781c6d11618019800b5134110307900d66403011200b80444080810b419000015820181809603a50b009000c641c41481c1e5556600000501d20b03030100da85103001540000464401c203001d015a08050181640c0800f5441010f40c00c0c00300caa03207103444c100791680151001c000108814084859501c0c00306e0b0500e00354401446c042e170541d1507101d2741000c40d208a0749c40341e540f007061070100030080080d40e880c45840c10a5030f2a510b014101143c4801c0c0488105100e9403034040e800362042d000b110990203848296540001c0e20842200f80400c82d4003c140e4566622003403440000183d404001e12841850040c04020003414501280800c0c0001800c025100c0303 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 6049009 1250 6047759 6047771
    0x603030f020a030504050402090f09011d061c020d080906070501020301090b0301150b030a0b0607030509040b012f070905070507060b040203071b0213021b070f05010804021003110703170901 83
    0x442d07441005e481c00c0e80c0c000c8400503943c85c030020018021056100c2c2d40b80e08210480c000182500350945404140030103144010682e075a120100021080140f03490390150703600001410240c14016030302d60005102d520410300e840c0f11075001440d603820815046815a40000040c403090b642c5015000c90400150000e12501c12840301d950040c40450040e243e0000d0040001884601c031034200b24030f48400541919a94049810001c101d03500c20707040c0a0085040140d0703094254802c2c00c9418051440380103c81e100301851420752000290302c501000c9601c90342c90040b1700000c10744202400b4138140d0b00c425a85806520b0000140c64001044a202d1b510620030030900700c1d00585050486a00e0340b0046205404a20000c0c07503480c10f05400841091001c03450700c081b89840588003515100300720803260701550302d030410321221500740109800180948045401800c3c02051a201c0e03805500780414862080500140f081e00065001c4c1d0002c3c6110303e42c5889000d071502c0154120907008002e01c41 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 6050259 1250 6049009 6049013
    0x303110c100807030f060902180109030206040b0a020f0f01090b0106030e060601030f09050d0302040f0e0402030a03110312070509040c03050906011a070503041e08030717030a0912030603030f020a 86
    0x860301d01114030505200c2c1a00000c1c820318403941c442d0350304105007481045999140d00d4040003d400c1108015074002c503c0c61007000541c0101351036012664020700700b0f0b01d000c7c1080480141c42e00120186401e51280c0e10b440034881400780040841e00c10101d00014000642c0c0c00e0001c400d80060340080c09041c0b91101000001d000803a000740d01c44401c2c00c000c12002190f03d808401003046080181050007010b46661859516400500c22140040c4070403206681b00c0f0454041a0f41c01d0b60029459404200300d48002401003030808845601c0400341e905081c0200d40001032080c08550100c009000080d148800745020710030240c400074286400c010f5460000e03181c503501e0406000f003110300580b134a00e90380300c6401c1034100d031101d6a0007000c5c1d9440320ba40352456442580b51500f03130b00f1712000351308001c101c440002007a00e882ca50001004052403528203200402c561014200c422401e4580c908000806c0c400400c02c4079104140d60002083d500c3c0d0f0400502803d1b2074240102150401058400 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 6051509 1250 6050259 6050269
    0x702011803020604020114120403020c0906040b0105030105090705070506010605030a0f050103050c01080a0608030f0405030d0e03061513050c03040201080601020d090e0a0605040507020a1202010501061205090a020402030903040303110c 103
    0x1502c139a0a080c0000c2003c03480030001c0c40da024005400c40915141c0341048201540400c0450200c0c41c181c2d940e003a241c96202c00c1000340c0ba641000d03070b4001740f030a200402141c503103900c0c0385802041c00d060052400c0040d40b07078242051001d81008000c12400401e020102540744124158401d2108040100b035045070344280d11090207100d05410441c011011540420040c0d002c480102201030485c0c0d66a0524280030f0074507002441514480e01807412007001c15030080ca280510a100100680859590710320078100e03010300c200130503030008641031040c1411035807031284500544001280b142c59280600c001800e141c002810541150882e01c0070b41c4030550825190f4054031f100610b009403503907a4500c200003e200982c8031550184c1001c091120b003540100380105803034014040408503491040c02a820390358280728010024500e11200743c444501d5620568110582c581a119410b01540021381640c10564901507031f03420000d000c00800d80c0003005043e10035150409005040c0c10880024 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 6052759 1250 6051509 6051511
    0x1030b0606120411130203070c021302030702031207030605030a0f02040b0d02090601050705010905062805060105040b07060207060f0e0d0801151107180903030506030109021e06070209010306020307020118030206 93
    0x70030400000491504d00d0344d842c04034800d1042600b4045440e8500a40c00a0060350b003800f040c0d014080104a01d82c545205000301c3c0d2088941e9002146402c0d80d03401c40c001c00c26002001d400030507550f0b410100f1142d40c140006150503001c2c45582070340e018140100012115000b00d1182705108021410b0010b807038001c0801c2c0e206109003001500e80043e81001409042001e20003003450045904000c1d00103124181281020307c1d01c030009015440301d56600d800c4030300c25102c99010620900c400c01c5030b01d5600c1c00030001644613081c05800c2480a40e1010f0980303180380c0c640400c141d100c05200391801700c108080c0942e18124035000303000f5454a102c840f80001104402810030200781b008242c1c601d4108a94001010701000c011140407101e5140001014941c104800181c00d0101080c00c62805000318007001e600144203030014094801c007100164407080907650805018000a07003d65104107846009500aa4000d43d4030b1822020003400c40341d90032262584110010441030202e82d000442d2 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 6054009 1250 6052759 6052763
    0x415060807031103040506010905130b0606070309030503130303180303050702120106030b010e040308071419020c0303070602040503060a021e0a0207090504060e01050708130b0c0c0f0601030b06061204 88
    0x3104080d2607100e0100e0191480304890b029140c00082404200100041c03541d040341d00106080009031a0004500305501c0d05030f0010309445080404500c00346841802410458441d0a102030304950325a0b443e8195080600720041c00d100001c1c2c2041810740250300f640180e01c50888008041341141d40150050141c2400640100b04038502c03110030050941c801c0000c0d54000c04800b02540e13580000707190040701103900710b000032800300129000d14050030104120185000081b0304020b0404503a28a03180400080c070308501c0361064200307054400340300800919000c0d02015070380d0717400c02043c5032500b600948942d150500c1044014040028a42010500042520310680d0303010361040413840c22041ea0440841646400d05000410005600411800f000503000703108540d50b1140646104504a0f44200c01d0400c0601e01c0001a84031140c640c3e109185540e0541000d0030244001e2501c911401104d440d03078080f00050080c040d050396031a80c0094100c40703c510302202a80c4100c0382140103440 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 6055259 1250 6054009 6054017
    0x3070525020603040c030c0f030308011512110a08010f0b160602130e06030606090402090c09010207080604030201060612020408030a1d0904060b0a05010201020708090d03140c07060905041506 84
    0x404008a0121403160100a400810068480c1002d00b4600b00700031581c80100d440d01da8081002401d0b400698803a81201d0301600e441d51035a280c1040d00b01d07013600c2614020304001e01007450401c882c1851164010350118603c00580300d0492080c041d201c050103801800f90400944002c00080003c0f608651040c601a070b1919019005494072401038028805041100c100c194008142c881540c5000c07403094204804a0340582c8440c8188082441c040c0c6d00650070440c80c03030000d42d000724000001e2000100620440300b0b03103070382d4122160408d1002d42e800c47c0143d4640e002044080d91000364943c400c0b581d000110319040c13030510309554030f21442200d07600f40680d03940740c05042c082420403008510405443d1601602d080d02d000401031684004052003400700c1d41c00850300c0d520510079540b1260740300030842d1030040100700300710711204030039000c4007002440034284200418450107042c1a142d0f4000a103002802d0201c050040e0391140c0169016600c1c0088045800390605141c00840d031250070 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 6056509 1250 6055259 6055297
    0x61d060a03230f060a0606030c020c0603090312040b04020102010b010914041a030a03020f070605040f030209040501090203150103020103050606090904030806010e0402040806061309050307080c1c080402030d05030705 95
    0x12840c16142c01601e080e481500480101400c040800f00358076200751010b040c200451034130b400041c0e0480d004548254010390200c130300010f071803d00200440e0010700d12001c407414101c550914595907401150b0485205444600744401c65809011302203100009080420340035042c560090f1000c2c0d80e84810904c66500d54204000304000c1c01ca01100141c40981552000400c81c14042c0d541d031811175500c145486101e0b40011643d11960964040d0307464110200042c51454082043d0300401800a950075540c4203100001642c04000316100407902d40094009503145d4000501190801421036000d501c0030000d8060030b80c0d51180c440c2d130041d4141010030041c0c6440c8012507040340902002a0814400900032a158000181aa11810089a9410b15001d4030707003402c41621418040240301d5403081c00380c100000d0300342c005089501005401c441c03603c2c001d54030340c0954408041c0d020f800b2030381c4902030000b503080910550381c0c09007441c14203520718140b0700c900130030b248074800e0340c492066100c0c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 6057759 1250 6056509 6056543
    0x6091b0f040306050c070c080c100309060f0501060c0605010605040e0612070515070b06040605010203040302060a020a08121501020a020f010309020a0504020f0a021e03070308040602120103030201061d060a03 91
    0x3030580700a960882020001d07850050449510f65001020640d10408815000208900001800903080c0405070400341c0c0e0382c400040c00d50151612510489030f498591b01c413500c07100014410b0303900038025036540a540c840242007003411550103030054070400100b00414454001105089600a80c050350501c00e0390b4204500182020055044103500c07000040c105e00c48400e040b0003524029000b2034040089440380c004100445040c0d1003200c0c05a0418070040001d40f030104060311170500603005490000003560344883e140c0d404241d0446142d1084000d0100380d030402e00406040c00c1c4280028540580c003034000410302c000c19046241007540b5490b0f00411911a484580c2c01010003a01c11b54903503140c03203441e15031070300079100800c014400e8102c02c0d18030000c0408201200030381031004c1e41c5451700c951822a0000001401607503001d40030007101f10340031a4402264002c501903400011424188610403240810301010b1044800726102480440e0b991209108104d81e40f001c0e4014240300e01c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 6059009 1250 6057759 6057787
    0x40203030705010e01020a02010b03010b100302030405030412120f03090201090905070203070f05010506031606090915030212010f06170c040902030a080a020705011404080d08071404061706091b 85
    0x1c400402d15402c01e00d4200c0250015009403034560000d070000e000203454072090500300c803800b081c0c9542c000b910304c0303840c5031180c02940210b81090107132060740c1c40c10340c54000112058901d2041101c4041e580fa41e0000c415510000d60704152a051405004130b04164000900c0c0007140c1c02168106540c0c3c002013140c1c40c0c000c104642c01142e100740320500d030100b03904000d4020041262258001d002d0b0300c1d50702d0405082031b202c0505540603500c132141444e04107c6544010200e10f40380c28540246540f0210140c0e590811203030010840320004224149856120800e0342d04550080381c40384044144618103040c0481d1a99264405940000d0b41c4103050000074074140c40c089020b89015030001724205079643c00310782c00007a1002070301c80100c0c0304016402d445241c4128820520300b07411590040100c00c0c0716601e0704c2d0300403219107810154456104105502640203901c9140860042d20002e01c01d4a09107158a60018040360050641c0c0303040001142600340003443c40c940e540b000112a010002e078 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 6060259 1250 6059009 6059017
    0x10b091003180f0b0f01060c0b0a0902060c100b010206100306020c0c0910060201050c0702060711030708060c0c070f050102060103081e030408040e09011a0d0201140d09030f051206060304020303 85
    0x403201c54007580704102d0410f035803108102d107000d03249128010b000a80040c00d10003418100c414683d210743d021592600d40e0a0a541701501000050f82c44031386d03001c09650390700e000d090f460810001030201c45ca42e04850030700701c3e400c0711402815504050104007202c0e242d041840101ea401001c003680e40d0304c04c0d0b00303c1e0b401c1100d03a9145960240e17034031042c0151007241580e07807001d84903141c0003001503841d0320b001c545031802100341c0258070890030040c64002980899040c0300c641c901804881c205138a81c24440e00303028045801d4042075038003081c81a10820304010b644010131084140c60002420400000d441c0e440500000c0c0034403000141d40491031042005540c2c1404e4500b05035a00c1741018a403220780c65000d44204800c15500c03a001c2640980180308584280d0070000c40c450358003c00e80107204402808240070f9050049810411022548120003820001d074080c1001404001038500038000c2d04820b591201008000c1c0030b1a480032419207000c0c0e401040c12034400c1e44079584c505c0080d1640c03003 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 6061509 1250 6060259 6060281
    0xd060605040204060c020901060305040c050d02040209040906020c0d08060307060809100c0c02040f050f040213150305160e0c030106180b0d15080111030a050a06030f0302100f0203010b091003 84
    0x2c40000c00141e42035221080c0c03414030748201c4440c880b59981e000114240c80d0251009041c0000c1003100700141c2c038145403051032181c8041c0000d800c140711b040000b001c40340741c040260340054000a040c9040d0600b400704160070440e03070500850a083c0000425603074440d600814080c40780d504c0208600300c200b04a20800c110046809000220102c400100910001141280180c1c04c0201040007003101e401010702c01c1c0b43c010000c0030b0542c0ca5408105a4800b00c3d501425055555460324101204000684015602500c01850078031451094042c072070106a0048034505407107014060b49500701c90031030f41141c0b03162a0900001c91180a848807104595010b030440401c000303452851100c3c01d400204c0c44031002c8500400309903407076a074142650511500200c1c1100200b0001d0050b1a00c0d44c480e45c1c0002e601c140004002d900c036542c0500308041a80c054000da07101c404000e10b4640300f40290390040d040c5075000d608551400c5006503542c0122130b1464412051400700e404424440c5d482110001 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 6062759 1250 6061509 6061511
    0x1020f07030302010c121b03090c1205060108060c0306030703030c1106030403030f06080304121e0c0e011707050d080a170c07110a08120d0b03010c050904140705090d06060504 77
    0x240e40b850040d0080109408250119010788004074010b010361042c90f1007900300140e0035180d400c10045c220005d000040701211200c1c081e81e00881c00d081204440b81800c0e204a000f814594100700d20715240403001401501c510404104000c2c007a03e000c9440070440ea8141881e01d2003901e0703403415440b20b0003c514520b030802000300821003410b070b0682004103078044024041080c10303124030040b610303440b4502480344400040e20482000072502c44c400c50075401e4810390041645c0d0f255136400b19200c0264409808034418800500216418080031244480d40380c00900c41d4a00d064045403c0055024000d04108000720760362380c0e603e01640c00001c158681c14180c0c001494000524442e80d000024162074900410300285541c0c200310041d0b0f005d8a60101c010801c040398003480071540e51204007400106a2200d040f80360f5a02c0034016003034054043d480d015140c1e5842d000b07120403580050000c007a0314401009110b1030a42090440b1030704801550610a40076260030300001404090f0b010359045 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 6064009 1250 6062759 6062773
    0x130608030703030b100206090601060513180902090f06030703080702010e090711070e04050705060906040e01060f110a02010c060f0b03060907030512030130020301020318060a09030e040b01020f 85
    0x140d040d03000c14862135040b207514985d0380d40c9000882c1e854500f03c40e52072241c0c2c0401e00500c025406140585200100f44800c43c4403d03448482500114680002888000e40c0310184201185011007130107600c041c0d400000d250620702800082d40e208440e100c050405003000400d6000c2d644500400004c00002521844070f5044c0070740002c0c084134070740c0302072601e90090040200d900c4141c401c007a4003694000004002e414142010008a540603150302540410200300010383c01c2d07101c4245500a2075181c440613450010000c1c00b50004005001e0072106807c080c0e4141c0050381c0090700400700c16004200010141e81c044800402031900003c06503141c17003400c0030801c60100000d590341c1942d11500540311181c112841d1180a40000e000c0c040701c250341640ea036030722040102382c81c2c0441200d0b80203143c5400900e4000c00e08a0388107841800d12503c0c40c001c00c0380700b488104000c60b04080040e40400400e00e090318014115000703142d456201da600c0c0c500042581c0e100700300003c2c1a64460095802c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 6065259 1250 6064009 6064013
    0x31b0a09030201080402150310050306010803070305040302100c0b0108010b100306060203030f0c09031006080c03061b07050a0602040605190f020a060b0307030203030c030a08060a050a050111070905070207140a0506091306080307 100
    0x1030348032b4480d0f40c0c8648240c800105102401005840d0002d916484450030282960b0030412050140e400010412085403400d00100c0d00c48140d80b8001c03c1c44000016001c060354040c041c08804402909041c1410058200511640001225030000300580c4407101c070385441001541c00c1c03181c175100780e03454424001c2c4000c0c16806580610701b00c0d902c807411151940105014982c5920040b219901180c00e51740d80114403005103002405481e00c2002a51400c080c20f5485d4003c907041500650005000441d502071403c6815504031607181072420002d059144a88000b980c85c10011001010b41da101e03d64403002d600d0810000c00516402025a0745410b013a014566594218010f000c0001340e0f040c1c0400c0356400c2c004c03410340580b03d02800b024520782c1007030019a0150101485c01d1918402c1e07040c00a03070700f180c40c4a4030340124050350103054110300d898103403140041036030b5104d4030a52000408010990341c120440c2d00c400c5003a07074607880c801000c981074401410140d12445a44c08000350501c1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 6066509 1250 6065259 6065281
    0xb0102010f0c020102180a030f030c150c0c0b0601080114011103130902070201080a0203010b07020d111509040f06050907030c11030a18090903020a06180c0308031b0a090302010804021503 82
    0x224403111401000c441b4079000c410007040c10f03c01c0c800075010b28a4000d611010170310a510840000380503440040c08550903141c0030342200d0610b03081d14000342d090703a60101001058500c440e007004091801c58071650410141070500003141040c6070610010072140c0c403844a060003038900d68141c0380410130160355070f40e4200c0040c2d4004103040340080d1050001a00045030780c404d03a0705031a0203100701030400400b5402e025409015903002d40350b68000e40d140c5180c82d620f9180c0707184444034140446403581903840c00d020554030340d02541500141442c4082c4000c0c0c80c0d07c00c0060780311449140124500240d03003401e5400e81000307a01030b0100d0100040e49a0340c2508100c03403400810558018900c11036490320030400315140400001c005130490580e110214004c1c1c0c025010051188881c0030340160b407a034603840301184503407007210402804401c211600403000c1c0d00800b541c1c5020802454558a02c01c0140481d8003408002d0600804a000c40c00350b407102103d9140000b04130401665030f08190f03030410 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 6067759 1250 6066509 6066517
    0x8030109060f0512060f04030c080a0f0210060e16050c0601060201020c1e060f0c04050a060206090601060804030f0c0804090204091a0406050a09020906090409120e0306010f0303030b0102010f0c020102 88
    0xb10300800908000101400c2610030300c419580b114001d02403645840600c400d4a100241041d420442e00b4107500c03000c44c0c41c010007041521026107440d241107482c43ea010f810451803981042c09123180c55010040b83c0f03028000c440e03012009480488032100c464000352440d0140420151141c403952001043e056015801009a0b01a980c2200c9408a8102007040c118021811a0440d9001340c800b1070b60f01807002840b0743d0000900b00c081810a81c488001c01ca00311020780c042c20060703220300c041c0204d001050009901500c280d2401d08498500340e00c01034002c0d0f941d001d1080810000c4601d405c14000610291806007115503800d5540e20b0780c80c40320030040c200d0301d0703558a00709480340c2aa100e6468117101e58002c0f0760015242071421840c2c0040d0000a400c00010300340c02000030014110f45640d41e21030b9018082c80350740b805410704c00042d002850310f20742c0c2c0345d0782e4065032082c001403112040b01d0300c1000480b580362501140e41c450802c0100c2c05405000c20350007545040003c0202c88503010b40140c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 6069009 1250 6067759 6067769
    0x30a020d02040609031a07120b01020a080c030421030c030c0c09110702010f0305010609090207020103060803030a0603151116030c0512040812090d022803050c0a050607030206150307030803010906 86
    0x3200400a444802203e11b4030199800408500016000c0e00f40e94601d402c200d1a4180500543e050021b09071a114a07903440414241c0007900002024845500d0302c111002c13030131401d517000711128455654050820a00c0b07850250034072081d20743c1d0333030f0800010381d0303070305007e4a00380a0a115500c1c51280028150300103000403800700d101c403103a43c0d20300f030710a10510341241c0300341c1c0e2415245807500c040e4030002d501891090f4101070303c035140451050f0741040154050040000c0000d00503245040c05c85040c4140703500c0c05a41420300340c00c5400f001200080d1201403186040c0030506001c0362606840540040360000c204d0300400b1102d2800140d1040039104992105080d9032441c81031140f28005882003070300055118008a59940150070b207801d040346450301300001d00c0c402116802c41c0242014040d40202d81c0d03548200d1200d4131a0424589000c01001c080c1c400504250f01940c0c040d44560300200300a81c04016101e0810030303603a04010980085421a000685d03a513140c2c09040c01034612800340d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 6070259 1250 6069009 6069023
    0xf071e03050405040e0303040c05010e040f020c030717070305040303030f0e1504030201050106020a05060a020a0509090108070602010b04051302040b0a0b0d060806010812120a15060203031501110c0105030a020d0204060903 97
    0x21990405d0300100443c0c0c402c99000d0540c05d90f2a00701401176804401c80092140c0160359400101d81c1100140700501c5600e00f110011900d880080c43d040c8002c41c0c0300400b61485c04024050403001076003080c203980c296030b85403c3c0483c2040340d0b040c824004144114500259106c0d110706440c4181c1400c0c0414080d501030f60081c451a82c0350002681d0703495180174024440c3e44081300184c401d060980c09005c00110b149880362a1000030750014100400a82004845811181003002460f409114800c120760050700c1c148042d282c00d24100c40c92040901000c0c3c000c0b6100c20300c1c00c0050f41e0790310941c009091110020354440c405000780b00b00501c100e010b0300446204080011803461000942c0c60b180c011102c1c80c0c60f2502c034824009800c1c0c4140078104070b4042e074441108a001e00050000c0340080c0510b80d00458aa161150200600315510040281400141c9610a87c18400450034075106034082c200302d80e6a0b2030b550310f0103009100307400c11420351a101050100d0340c1c82e4000e03000d1080724002c40d1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 6071509 1250 6070259 6070271
    0x50109050403030605030c0d0201050906040806011706070f080103060c0908060c0c06010902040506090105070c05150a030b150d0b0604030209090609070e0f040b0601020f070b0405010906020307080f071e0305040504 94
    0xd1694030040041d0b401d07408230501e0750020056103d913005041148000d08501d0400395206c3e452407504000707801a180c1140d030304130380054035001041410360022162400241800100f0409442a0810b02000c0e207103d450f072603c0d9051a00031039141005000e11801c40d5428074000100400b61b80140f10900300c1d40c0154800040c103403505000351415100b0080c041807130901885d00644903980802070840d00500980030000e419590403880164261174000450b50700c29090800508944940408510901c903141307a1701e20909907042514201c4503000c100080d2480d1110004030503000759403009500950751000c2191404000c48c2c0b4502a0b40c06504503000d0940310744003004101411980140c00d82c00460018010a900052850300010b041c010f4590302142c41c5406424003c40c0c3d04a17032010040014200326559000082400814003403000d036080800c182d40d00042440b070200074103507001010514034203108011070b81c01c1c400c5c000030440326444089403401808035000351150a200b946090 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 6072759 1250 6071509 6071519
    0x10c0b0a0225020907110f010903020610060f08010b0307030f02031005010305070507030503041e0b13020108010f05060301150302040f03050601090c05030915071103070308160309030203030703020309030d0501090504030306 98
    0x122400b0a507004150503d40c0d0f4800702c048400d000e03101c42d2203405100d0644111000c01c428451541c01c03601a601524030b40c03a001c01c4010300038406600441c10441140c400c0c00103035901140d400d040d81d0105154903a02e49a102d0100d000e0301a183d60340c65414400424000d0000307500d031402c41154000e0720140070130b0765002c01c00e03515401888400f802007002000020001a8030058001c0d030007075105d10705104405640c0340c1c3d0b009141d0888100e20020340440000c81990707000f01c215401000e507041011036003410300d404100c4502040c8203c17038080d0180002102c2260094060b50054800d078003500943c9130b03903418480c2c5c2c2c0e46020312400d00a035141c0030912044078414000c4074410904040284403038480e2013808000104020300f01070805c142c1414612100138144010070400380a0fa49410070f40c01d00c3c070010079041c0564145001410b251010000c0025004401d481d801191030a00513140d82c1d400a800b411449044a52440c1030310f403500104041ca2560701c44c5005500a80e03080001c15118 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 6074009 1250 6072759 6072817
    0xe100c0b0f06100309050312010603020c0708240405010e0d020303040c080a030509010503040f150e010b0d110907110706050d050901060501050d1509020307020105090f0a0f080306010c0b0a02 84
    0x1d440d110f410492000010010500030b402400c410391054003124600300380c0440d058600e02e02a0821700009800046900115a003003100d40301400244014019407090004144140742d2018401e20507588064005010b00c5829400701074101f0a00c1c0984802401d21100291641d100310f408503031004e8044000308404800103000003070a68103803680d600d807409600064655400043c812940f980c0103500c14000200313a2038120300d01e07a401880101710141804c3c4100c4c07c3d40d0300d40500c240280d0007001048007241081c00e52403150007007990280301c00d8480304c0c1d04951505500a0340c915034440d0b1800010035a52200c014003000501d104104401c0c3c842d003062a00741c0d4013074800c190001c0c000b480740141180a0348e11003645581483e8003c460150f0710202001a60421109000035035035510800400440a009400c0100c00c2c03840a480304126a81e2100c60503606404003900c106008000503255074029250060b01030b4100002c82d02915180d8407410180d48200204841058816490380c10f107040 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 6075259 1250 6074009 6074011
    0x60702060a09051002030a021c0605010906031401140307030b0903041a12150d060e03070c0b0708030406020702040b0301020705010903020c0109060909090203030906130905060f100e010e100c0b0f 86
    0x80f0201401000e04450080c1c0044e41015011900c950340c01c015041c44c081e0351988000031151800c1c0042801ca240600140284000394009010300d410459580e81d080c42d0b010f0000d0545074500404c00a622907400802e10b000969000200134000703080c2400941c10000029000710f905600804d065518140440d0889009100d000c00603a40e003000070900d46030b6a8004241414000b034800d405800c400d0721b503c01520045161f0b02d06a810008594090180420010000d005101356151038007085d55200d00280c0b1000b04041c2c82c0c10f5010510f07204550740e9402030383e0002070040080d0745900c0c250030441d00a242c0500102c0141c41449d1003902c05500620400c0100ea110341c071903203a402d03d0300c6240809000301d603400303d1b4980010001401c09a0350a00948550310009020b60500c40c01c0402c030408a9801926484c450484101500302c80c0d900e03d07d9000c1c1c29205450503120309060440181c2d030002c01802035a1340180004480321070b03a0390080401c445030740101c640a09035254244d541c158100 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 6076509 1250 6075259 6075263
    0x40f0209090414121201080c0103050601020d0509010504030f050f0601090b0f0d050a0501150608011217130302030d05090f0402040503120307050705010204060c030201150501050d0e0304050301020a02060702060a09 94
    0x2140070015002c03c50b5140d407114039407041e209668001080c40c208a4440c1e00031002480c1902d1900010b101103841000082c480f030341d00b0f0908000606260300081d640740c044540d0401000700000f4020740e82c3e440b8909130f4004640c44114074040a00d07514105454280c20a00e2201c4c074882c01c80006480c5005004608980340007800710160680350009004a0014a40c42604c10784a2200d090b070015400b403140195075078000c075403890b07103c0c2443c00041c035512041c0c1c0b04894141065040d60081072102d0102030540510800c00da9031251001201107220001e41d1020398180124020750f401d064205000349400941124071088110150017000128001d600038560942e1001400c0030035200c07400011034024003141842d608141c1e03103669290980e401034002c400000c00b000d044900301038090085405501c0014130010006040400081141c040c0381c1e4446031054841205420720343d8107008484c041d020180081d50303141359605019590301821740740b0400510070b09000408da100b10b4480c00c100c1c25 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 6077759 1250 6076509 6076519
    0x30c0206061909020702030a050312010509100303050f0a1803060f141509060312040617010503031801120906061d100303020706080411040c02070602010e1603080706060308040303050306040f0209 86
    0x600f0803200038000d40040340300300c0c1c0510458810801181e001c0001d4034a244540d01d22485a42c10501400040000503080c03540d000c24401c0144002600002a9a01b02000c80700c001c0c1c840700e0f503140c12100805841e462064202810802205010b9030fa0825075030300000b068188501503804005880210080355485811061910216028900246415004036000f000c44400519800c00b41c041a84680c5c0700801094486203150141d4280007841c50041100301c028508005030520541c2003410300e140c141c3e0400c4045100020400060791003a034400760480400c0141586404011003507090700d8a922064645410004003120f102d05d500006481d810360240180901c3c0900c00e4400b100060004c84a01050803140000da0b140c130b00c266201c1908070342c001c1c0a00b5190110203800c54000d8040d5000e40e800405520240c05250b1403608222640b2015607030780d508807414035000600c17007900010301300100024000145070b4401c01940c00380004480400074110070740d482d4001c901c5811800754001c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 6079009 1250 6077759 6077809
    0xf0912031b17120105040605040e0d030e070801090b060a0503010606090603020904020405040e06040b060603010501090608040602040e07020f010c0302180904140609010c09090608060c13080d030c020606 89
    0x32401c030060304031068400c00490100b03005508440034950880480e40701110a40790040001c1e18190149000070316007500c0c104506110071030203607207400c82c484540d0180b40e150349166544c5075040258000600a480080000403041d01e1302159511095844910481e0903141c0440c040c41c040c800d45c81103440c0d5480344000d5a10740705098020b90045c4a10703e5100b0f90130720000580d074940703008180011041c43e025281c940f4181c41d100c180781801411860080388248014070640c0d82007881c1c00203880190500b5840f580d124a0154040c0c8100d401c0305507120044018040140e80014041e4003001c0c15400901c06107051a600714100e02640380d0540f0850040c0113541c000e82041549643c020b401100030803052a2031132151031400509440c282c081d0380d5180c8102d8600d80c2e0010000010b004007607070a200c454507009001e81d0311000070303003800c2500000244032408964401c003003c00401e2020f003178500ca034203107a101500408400d0155805401040002036180c41c10442003500c28100b403010501c1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 6080259 1250 6079009 6079037
    0x100c02150c030106120f1404020103051f05040e01020705010608010605030d020a0b13020409050d0513050d05030307030c0c0609030e0a08010b030d050d0f050c07050c03030c0309090a0b060304030f091203 89
    0x40104085d03c401086640f40404840008140151031040c080440344401c5803c00e40300060440d000107050307030300b1201d00401c0000c0705040c2a1190088034000c480c0401d08140610b8114024482c803500208190301e4100000303403241064005201306c4204805a66140847c10380c240d032592089071004001040180c00102145210804000e1450003e030000900c00000e5880c0351401040d00d43c101c02107600414071402c403041d440100c0028040030340700d1440301801c2d1395a481c3d90b40009000002032544580310188024030464614070400d4000c4810b110300b20706800d020305441c0c400c41e0342500034034410380003003054141405262001c1c17801600a01c0104a402c40c22241604000008800d154980c050300101c9180c40c0a000c0c01401d849032407956518440c6049860034825102c124040d4000740b29074074045c40d01205a4407140026100c408890f0b40c0c80300008000c1c40400d000d10b90042000c810701052581c004561703480747c4071a440d1240074503101e0384400c84c1412441c030004c4c000707043c680801403 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 6081509 1250 6080259 6080267
    0x1081f0c0c08031503010f090302030304020f010c02060703050304020913020d0b0907080f1b01080103030801060804080d110d050f0c040302061b0106060c030306060503010617090708100c02150c030106 88
    0x8014400d62801940800d01035a07649078070707402074416000c0c900c0586003c44031898203100304061840c04050070440c613492541d01a44074000100042c0c450104847e9088413640101d9152420f503a00130191fa0707907906140b402400729002a41c044c0e014058200000b10035000a900f042480b40d0010302658044c88150358040c151240182950018002ea40340003030240d20030006c40313140564080150031104240030580c0c8a450b401100c87d410028100c004101003034000c4256810b581c10b030316140030035540d01c0c101951244240340b04404070318500b06072040042045005084210041c020910584d02c8030301116140340d000307846501a40c10300704000c00041c07400c24002d0402d001c0e91101007202002181a03a405c40704c043e031100000c221700d04240b2041590501c518000351900f82000e60855042c458001d0000710400022a8080c515801091107801c08020040041c110034080f103030307400d41070018a0f001c0d0110201f484050710131250720f500003503c003200452048503120320460440c1e1030140e04603 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 6082759 1250 6081509 6081521
    0x218071d22140a0b010e030106030305040b032a030708060406050108070c020d050109050304060f030e030d0e0a0209010902190201060e220b0702150105060c07030201030c0e041506020601081f 84
    0x35107695612207014400d240c500218031410425100140850001002608082c510041d0724401e92401c5402d100080d0071005403019200d46041280c0c0b642e50b1a02a00001c07862101400568524442d2030700c1746445510041d44100001d41c1e608409403502c0c0705000a0340c1e4030f0700401c2e0114030b0100010314405c1c402c0802d400c5090000b407031144441281d071540d608588101c00b0580366034000060900c0400d07041511030b040c0c40c030203140800c0074410402903a6160b006104202c4d04694403440c0da1100d0f01010000c045080d80c000f0441051035039203062110080d07000101000d90008040c081201c200c0c018405c000071102400c2c0c0d0392100b030361003441d500703140c1203040e91100c011165041c841000c0340d00c000841e44a604290000e00e10003180b00324204800805a10072480b4400400048a8409011842c401265420308000c61100c0d02c0c180c061380e0b100c090060298005140c00c8080015149200d6070000701c0316603400380ca085980782e81c4d0464079036a09081c0116000d031402c103040400081ca034064 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 6084009 1250 6082759 6082819
    0xc1209010504030c0312030506011805010c0206040b031003110105040506030f060a030b0406020703080612030d0c020102160609020f090c0301030b07030f09050c0102060906090718090218071d 84
    0x141d46880d80700d56402807070002070380040d6080164203502c106480c5d09442a207030020003d00713108a4545c0d4807024150465440c0c043c1a04000489546408540f66101510040c00702c000010b07449140c0050102d0001503d484162103000c40003000ca80c2c55401103045400b0341d500501000d00e144d546010019500e20301600090b0046030604000011a007204030b005d028512601002d65110b006007001031a0302400740880e0f01c03d00036840496003c010000489415190a02d400b18900d110040164024011500100790508280d020241040010b600c0f0b07040e170034400c035145403d0840300e0040c82040350b012510300c03004c044100010b1010071811011194000098500440da0412140720542540e000d036004403201d6001d513602d04c54039030301403110301c0e40402540024203d6181103941d150303a504441c4110305510322102209850103c640d000146495000f80c802030019505415083c912542100e9443c0000d01d1011442e8034003000101005290380001e087ca540000000c425001e100319001c10 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 6085259 1250 6084009 6084017
    0x3c0412140c03161407030507030605060301060b04033f0809010b090103021207051503270c040905010b09010e1f05010c0308070e0d0803150d020a120c0801060305030a140c120901 78
    0x40520304d1080205030003552140d00507080107481c41c0f404405444001d011180b01e0f90520505010b0444207500340d07000c80342c10008208800c0345141c6100491540803101d1b070301403851030a017150007029000c1905001d010304d6458958950345d800809088801c500b1304d00d5032140d49600100058604a1544131001c404801a1018940c0d80d0001443c0c8200d460082d4603081000f1040000b02c1d007128040f4071f00e4000a80c00200300101e42610140c0341c03504510304500c1140c0d650603607030030710500350302894514101400c034000b50358544240d07040720302003103400302d05d0680020185129003910310300c030204940041e10707030240003191581c0682d07040d1401021a030070081200c61400d119500c040c0702012440c02144019035a00b400d08441040e0011800c0c01c40c080c0000c40341c0c80b40107894201d1604120b88410303508890b80d86007854034401d040c40da90710060003582018004001e01c0008002402e655031315444008040c0c0131180701018502580c00600c5141c0c1100c802da1b040002c02c480100210101450 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 6086509 1250 6085259 6085283
    0xc0f010c0212030d05060a0602060702060a0f0605060301030f0606050a03050d0804031b030e0901090216080d0212090c0a050a05090a0b01030b030f01020d050703053c0412140c0316 79
    0x2a81e5450f42d0003004010741c0310307510354091141e5410541e92243c082c0047d44090110f070b00d080317034001c0c0d65014007405215000d642c540303e0580800c000c2d4008405050000d15056480d6540e00388601240c00300003007583d5052a002c8000b0740791418081c0c640850f5444000b43c2445000c9110a50300000001c02c15070030f0102440042110755482015080600c1c4a40c441d841105000f4051204070300c4160080300320b2a1040110012008407140c80100c0b960380920b4440e9603951050701d6501900414200a60b080b00c46c105208624602203041d03100d08100351006642e407582c500c00c02152140368410141c2001d0301c0000701d8124a2560400b401d00703401070401055481581c00030a203000d41080d551070250b58003040c0310866000700d000345a0429007074581440b9a050013540e01c0503030310aa844c00303402690f01110218a900c8091100f2011241031801c1c4112460581070081000d04a010fa80000030000d03540c0c0030151581c2c6040c0c1e0100b900c284025030170280c0e00c014080d070911040905458621081c2 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 6087759 1250 6086509 6086539
    0x1090303110102280809010204081b0316030c080f0601060509010309111203070302070506070503120703110304060902010215040c050d050304030204090507050907030209010f0507030e04050c0a110c0f010c02 91
    0x140d08203c41c901404c040c1221402092000f41181405054000564010403040000220000300800007408644d40c0f041206841130000c0c0c64003c6a120b0000c0d00031418000100b44840c845412040352089415a810281050714581d00c4003003d00822003c81c400340309000455109502002605100b04a2074502811020001e8500304400d08014401e40c00050f02d907041581c14088100101015580641014115035076661a4007c0d3701d43c40116a281400080c44a0b229411140740342c0e21159620343e0328101401c001001d001a280c051703016115140100d4010f09044540303a2042d6005140d800300e5900304010040108420b1000b6100b070320081c0000300169466125844c0480d2081c00108080f6250005000c28204000d00c141d0038548180492950f0b40d820010803403405040745403082d5940c92518003560082014042181c0040c94041042088002e010040c400504e880c1c5844001001040300d075030ba60720400d0b8660350405c80181740301d20154081d45d8075119840c80103040c034002905007 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 6089009 1250 6087759 6087787
    0x703140c1c0e01020c0d02010503071403040602040306060501020c0904060e03070812010501020706020f030a08060409050a060504031215050609040212070206010509010501050406020c0d02040e010603080301090b04050601090303110102 103
    0x20305107116600220310040651500010b00301003188080c006010621021800102c1602c1c81d00d0010303061000010000b1405c910440880d041144048a503503181e00341820304c0c20080d046804100c400e246040f01c00300e1035600009206048560042c5070f00070070390350741c0c1e00d001c007038800009881034611041c8010800100304202030010302c41500c401c0141585400300091402c11a5480141550001c2c501501400404000c0340da140c0424180200e10b40c40d104c020600030314400b04040d1050003500880c1c0100205504090b00a0740241e968080c1440e000d2001c504852310310f0002400c0c40c170100c40400450808001405409000a00060a00280ea46400d0505908581c8040140c01c8080140031610305000038030301505081c60039a040a05000b400380d5034151050800e840340350940b200c60115079458001c2c05101900400074030140b6500e00c0c1010b02d031341007070241844031030500107070b4151420300c0e1180910854050f07403a01580c626644059500107070050031540e85540800c26501d041c041 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 6090259 1250 6089009 6089023
    0x1905060406030e07120f0308060312070f060501080d020c090411090108030a14030606031311040615030513020102060609040606030803150103050a05100b0a0309050601061e05030c0703140c 83
    0x903a01c0c04110a1a44484507082c00034541141446002c1800040302056000710403046d000d6040c00e0000302d90316248002403801100103107607a2010400503d0710300701b02c40808113002282c8071b8001409a6602e0341912903c40c00350301008001684507540100051402c0e40c2c2440d0014000c0011042c844414000306080c10801d0b0000c1d0710030b0b4000200740c0c440c03682c40405044c0406a0042040c11401c100000490394800900700d0481d00748481901003e0001c1941035080d40c1e4402007042000c00d64070404e445402d684019000d0201e032524001680c030301031881c45514401d50582c040d110070303030303a510421a400102030819282c40b43d131810301000041c1040300841c05608542002050070f000400010240c8038010206032006007000240f109160300312070048140d81c0780e070170401d80314211410708600504400c08098114850000001850364000c107101c50364011050700003030100c1d560107003038805100c15500710301503d00400070107005c03a200341d0b00360303c242c00c10001007880d1480312541103243c141 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 6091509 1250 6090259 6090269
    0x607051c0c02010b01021002070c09020a050d090308060406080a050331032402270409150603020a0807030308010b030601090905070305071101060b0301050906010203070209010f08060c09030c19050604 88
    0x135590650135625a010005000245080d071001d5241081c2e036510000140b00718414071078000d80100301c842c18a402901520b030180c510762010812403016003001010401c0c1521014020307881c0140204103008082124485160000000c0d4640100344036408000e085131009a05a9040307511400182450203140100840c09400c021000b03492201c03c10040043d12903101029603c108041d1881240c2002030508558408000c0244800e10341d002c68050056842d00174800b0144240920300c1c0e19145c0c2c4003070309890080e210310b81101d480e15449556190345000c05008200d00c08010006030007d00000c41d4409010315220313104654903074020003540c900b52003040109440e030003080307000c5500001c0c50386982020070082c05050325203e140280d522041c02900e0148095000040c5264000c004445003039038080e14080503907940745801e50342c01c1c1641c01105e40c44d0180d8408503000461704419641220070041c0900075130040c1da0100046081110712903603404a4a400025290b0348120140c8002d107 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 6092759 1250 6091509 6091511
    0x30b06030c030708010e0402030a020d020a05040906020c0f0606060d230403020c090606090a06051303050706020a05060901020a080609070309080a031a06030702070302061b01020304030c020f03070501020607051c0c0201 96
    0xc201403202419113007058101e00d45c0031010300c04010260390005100b041440d015501e90401c010107002060240c0c91a820458000d410040144200070081c0d00500c0700c1d13440f45059484840814610355107441c01075844550010b8107010100c8855025880900c1802684a9001c681c204034210010308000865094000d41c101154414090500c1d0508940c040002c641291622180500144103c2c8250140004000e0040345c0712000d018050700c420040c64100045400700e541c0c070380c030083d42d95150300c000316034900804000c503407982414001d54811480381c1d1130303103d1a03565007000d000c0303030090041103c010552640f030090041010304000b44692522070b50301103030840c0d203d07000d00500540010028040c2d00108100020141e02040e034a003039a60485005544000d552407032007210030ba00820300c0740343d4800400d100425400524401465100f40c446500004c00003007010b03143d0210b40b1966001da0030000014a0a40c800c1c0014241c0030f4214003030303602d2011a151001c0c204c03103044011401503 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 6094009 1250 6092759 6092761
    0x2090d08030103020916080a0f06081203010f060306030203060103021314010e1608040b06040507200709110c0d140c060903040305060f0c0703030f0f090f02040c050403031b03030b06030c03 83
    0x25050403009251b00c66030140c1c00d4844008005030092208a0040851a1642e50303415001c110581c00e8000d1001000880b0458048c01014404d62015907c00e20940e031075605d0a440016001f0702a0140fa8100da80040207003403180e02e59001d000c0c42040540042000c80c0d66482510750300d0540c0d85200c5c2c0030b4011155080c01c21f140680180242c0203c1c81e0408050091513010800000e64100f000c50380300c0c205039000b04103030300d401c441910009031703100d80c000e802c5d620800195a01580015488120740326a081801550158410b40845c4d10a500d4610320b55009940702c00030031400b440c1c90948005981d071445290644120b285410850140c0700e00b00c1c1034100040400030300038100919500302495696445180c2400c2001c14281d00c5040d20090a1503260384070000b20b22590741c01110b801e2000b007410b201e00d00107031400500399005443c7c224440c80ca00814402c645120b00c080d00c042d6681a21011045450b0314025810310110710741c01c40c10192101904034480c0c40d890040c0d405207040c62103003034403 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 6095259 1250 6094009 6094013
    0x4020d0e010b030309031902010e0d0503030a060914060d080405030703050303011a0a0f0e2403091005060625020423070201090807031101110a090303020c03010c080f0a02090d08030103 81
    0x2c0d58989249a44643e00900096074150b4000c5140507071080c092208070f204140600c0180c90314060384d5a400e500003001a410303014040040b005510a00010004220341070302e032070241e01203800b2405500d103070361071070400601395081c079181d280d14050090107500d0801da600c4000034900003041d001201c0a401c0400100300c3c0703a000f91442c4400c0c0da1244401401c080f030b503000090521410380b440700b042041585007540035403154584000c000da00380d00c7c41b2a0007215008220348a5000b682c0d011418030600980c070f900c010a51003802d004d034400608213440d000c0011411003000d844864442e81034600d685031000166079600c02e4040c0080b21810807038024140505112605200800160669042101000010f4407100440300f440f0b50600702142c10074103680e452801041d1070710700315204400005254282702d802c562018112442507003107405503009a400d140c00d85061450b01c0021806080206440c071180b41031040d400130313000100505200d1072100043c2c9c00c0c10182c2050707408100000042c82 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 6096509 1250 6095259 6095261
    0x10c240b060306060901050a0c051606020c0901060503150103020c010c0e01120603021f0509040c050408010617070603020a02030705030301060c0b07050901080a020310031704080c090903070609020a0504020d0e01 93
    0xd4490360444a05003140b03860004180503100b411410b40c10003000182c241d90741c501500a4041c0d0940180407a00915203002140900c00d656000b0940984200c202408980c034000c4050ba04dc4e03202580e9103819a21480c0214403007401803440307141415001e020840b03440c2424803d25040e03612568821100000820005d0040354040c40410103c0d4104001400503850720f86418420707024007040c03010b0707003400107030116200c6c02107201c101da0060511224001c50b43c1c0c03000c0582b0136a1000310003001030310303960400c16003411404140d01280b600028800c020460280d17001d4801c40d05140140c0b407030000c681d9585800d6510076000a0302051030003140000b03111015042e540d009006007445c0307103020094000a0301e048401001c0114180d0004000f03050510080000301c001d603403218a501045c426000c141c84550420301402078503100e4404a0001403500d107060340d00451100c0040c519001d0316450b0b94000d0b01c5040026070304030f080c801e4005034503203035407000b06142803082c4000547c80e00e154004c0d44c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 6097759 1250 6096509 6096521
    0x30f051b0c0f0102120906030a0608011a030d0e09130c0b030f09010f060303020a0b0405010b0301020406020303090d0306030c0b0d060b0315030d020303010b090d06060b070b09060105030a0b040b06010c24 89
    0x6045500110b50000f42c102d1520854041b040c045070000e45950b60b090b40710000d8403050308040115400c0c80d00700100400011980c0581100c128103458401d480b54904640d1040e410003016032141e19407020400002c00034003007030070b070710b01441c102c0007200d85a491151b0b29600c242c3d20190224042010407510713240a00c560903401c4001c0301c00340401469614000c0d0354024403603010b8a807001e01008181081800d5100304111203000e8025521360703903034031001703500d0b0f41003103440110501444c004800e00c01e03c80c0c440c100c10b90b03920560200083d4202030f0540d820742c107c0c494a180c803994410010825213001800b441c030414030004592116050b40c020f141c2000503203000f10080d98014030042c00010300340da040d652030302000c1d926221800000e040100280c011750f401041c4500c0e00007034810074060074601c03c920404004080702e109980e544281542c2d4000e032640600311a158002241c0002c000c40c0540380c2081741407402c141c040751700b070b00c071a14514022740401d5402034140e02c0c3c8500c18402ca02900b = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 6099009 1250 6097759 6097789
    0x6090603040c030c0905010b0904020306010e040e0304030201031104030209010e0916030f02031507050405040906090204020a090e09060403080708150307062102030405030a08091002040b03010303030b030a030c030f051b0c 97
    0x6d00103540b4100c1e6050070f50283c0e40e509442150044002030f083d0744110006900ca12000780180181c0101800181c0c0341c0d4480e0009900003030411091082c0d40c01c8460031942101c0e07010780005400ea203404940b607030f12000a03128a249009000c1301510b2070080306598406076000c0c0004002c069401d204040c1740c0f07851101e040300d4802c1d1074420040d40c030b50800155411101c05490124400f000c3d80340c508018544003070001d600520105101d081d075070f4081c0d4014159460b016189007a51580c50400c0d0380c0308401ca0300100011610400118001e00c5008a0b90f0004c0c2003004030048000b2200c0001d04040f581e800100003d440300c07418806c04d220300300e092901010300c2e00b0114618101070301d805440b0320903440000b00f44041c00c0041140c0c10700400c40841c65000d840000c64680f81c44420b0749101ea4428070040e00003038113107011091b851901241c601501c0c0d0745a00c811580b501f040c0c1e0140c81c04400d4a00900500c042440500048505601401d403000c240d80040d01c0300341600c2e010022148000d8045e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 6100259 1250 6099009 6099011
    0x6010617040f0305030604060308040803030a0c0801030804030609020a090c0f0206060f1f11030304060213050402030105090f0402060c010903021e030405010801090b0f06120709060302090a06030b06090603040c030c09 95
    0x1d00010400a00000c2c0d10541c140c0350255076030313071585d02080240c0390b41e9000a251920011f0000303080c02010014501421505805102c2003040c24004c80b148007003030001401c064070410082001070403561100307002d28400f803c0102410755500c8500c00300e03440c0c0d0700040c010a6000907a90307000c81d4140409030b4800d0b412510121140c41c4c2101040450700441103603040c481c00c0065201c03d050250601e130320300f04d210000310380d0760b45814603195020750006501d91405c002010300101b510f15080c000c0c0ca05855010b4198241543da188840401c128080c00a0360420390030402d03a001c0c0803007800380f032901e9400790300100313070b61000720641041c01c6081010707602c06070300203110900c1181e900c410064115001c0d4600480d805810030005900c591071944e0441d4001c4e40054124000403d110516110300380359141c003d01c050f5100000c3e0281d02c038600161380e01c81c08036101441258042e07801038001c090090155820524407001043d00c6034400c0d5001d0764150034403141001007040f80070190000d081c1c5044 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 6101509 1250 6100259 6100261
    0x2100501090c120209030106120c061205070e1009031502090a0504090203030f0a110303040606090c0201060501020304060c05070905130507060c031b1109010f0501030b031605190b03070206010617 86
    0xc00800f0603840c5400003003200d400080e00303101a40e013508044040c140d00300e54404c04000d03d02c0c2a491100880c800c80010850000c0f80400008103441094030810b09a10380403c214503400410580d40c0300c10803001300b4085000c1010000c01c0c2c04400241c00c8502c800c1006a6860780e82e000c2184e95000395000500c51400e180306080161804001d031020320800d880318a4542c0da0008082d40e5000405404240a00c80070003000309102090700880100e4042c0442004004041c0100300c3c242e8200c1e014440c0942c0c42000f0800040344101c1b5003496041c054410703246e216880b100b412013030303d80035241070358002440100c400a000040c0700710700c010941402e0207110042d040d80d01800d060742c0145100c250300700000754101800b80c080c1001100090081200360b81c0e685900d0b21701c03400f168500445000034a00495041c035030400003003441595400500d07100c40030b40b4050812620744286110509441c1c0c49000020300254030b840514040c08032600941040e60400d900181520800e0350f0b0107142d0b5031400 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 6102759 1250 6101509 6101531
    0x10e030702030304050f03240601090509060d0b070302040b040f06020d0c0f080313050102070f06050105060405130b030f0a080711090c07020d0311070303080103050c0103060e0c0304020301060906060210050109 92
    0x4202c070201d030070030388605080b03502e0240020304201c0c42d1f100d0b030b0007044c0100c003c0040007234000200511841090f224550a50380303642c14000001d000321210b41d0000f140310305600c045a1a81240d03544031240380f03805403600c0e44901410409800c81c1e031181d00c958564490501c4840d070107200c402e0070b02c0224078048018400d243c841070a2030b000c0e80303400340401c00000085621b401000050311304064003d8001d55031080c0a103010b04103041c0d40741055424030303e80800030805150072011102200c0c0014081c0f90400948540703c0000c1400002190b4903210b02c0c0e1881010101c00c1c0b20003140b05009040140d240c1300ca40c10701002000501c164103100340003d400b0800c00c4050041581c111a405485003500c0041900d4107070740031040c00b1000382161180010001c1010361000310300741078900c21801e480d038464040c80107409452283c0070b5244840b12541c0000c001030800340146621600003000801c40302c0e5940c80c0c900440c6c8103074105500503048600204107141590080f0303401000011001c00c10700f242c1e5 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 6104009 1250 6102759 6102763
    0xf1503020c070b0d09020d1b050103050105010e090604061208030106090605161e02040f0e010605030a0302060711031603030f0c0c05030301120602070203030a05190f0c0b0402010201090b01090e010e03070203 91
    0x601804650201c0030419242c413900781d510000c1401d501030045075110429040c00806203059410306002c10902d9400440d641d44603025481c100c400684810003042049070030000c0f218402003a0307640090f074650000039050407405000e90764074062072695aa9505010000700020001d4100b03400784602080201c140302c0016203034203081d0307030044141009050078550b903e1380f0f0b40a049020f9407003410f0200a60041c503060f88500700d1402044002c100b915500d0080c1511180ca41001a015030046000110b04900407521100f04103400c1e4103403460b0500808500865021940b41680000d65502035103243c4c400a1003a141c03070301014107000d0000d040c560380f030f1a41c3c1e200500a18061028111441040291a405441900d0341c0202941e0b124000c0704002800c54014090074481c0706808500b00041074040d40707078400034000c41e54800405190640700c0b100b9104001e08100d04544d81c03924070720007091944240310b028110000740842c41324040d00e0844e00359801032030b00003c0d94000300f0050b0016600 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 6105259 1250 6104009 6104023
    0x1908040f03050c030d05010801061806050f1203041502010605011d09010603020a141b06070c05030301050103020a0c02030d021e030a08060d020a0305030d0f0501090e03030a090602040801060f1503020c 88
    0x22526082e40d8580c0c035a42c40504602a8402e0140702c181010004143d074041900450255080c4182c845111310004421a0503034210b489815000084100c040a0700c1c03d0400d20081514040c004907854039a50306007612109909210704030060755a5001442f442d84d108400890190b0329000c00c290f04800017000544d59003041c403c600500d035001a480d8481070090321094080303914018116242c01107640366402e4601410740882c02c07401001e0020300e4290290b00c0c8841d490b80c001c00114210380c2800700540c02075201100341030911000c0030000c00142c0e07041050002c10900c41c1c7c0a40140030740f2068a1296a10091540d42c003a0003e005644c50740e54840c84c0e1981c044004c40e0600c80c041901d001098456010b6007014200313000c0040c6c040304202d030640100004002c0000704001c00d130b0340e0720b480f01d00321603408007500803d40040012501ca03140780d411145280f0b000d81c1d80145800d03564140c15084030380f00c0d0301031000c050305914104641c41103034084549c00c02040c10306614140e101d0040e50b0300d03000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 6106509 1250 6105259 6105263
    0xa14090a0b0102010b1002010914060403090b0903010b04090809130507020d03050c1b0313050105090a0302061803060112020114030103020d0b0a09060c05030108101109010c0218010603021908040f 86
    0x80e5800031030301c01c0ea1007504030b15411400070303060413080300d44240001d002c2d10200740107031618032000c172420346820000181148a5601a5030301c000e00303410721910030007a0340007607207481d415034981c0d0b0409055965031051a10b40c0b07208881c56aa2412a403052142ea00e03c09100130078010b01d0441001003c98022482268440191078001107550356400749070058000c500c01c0c2044884a00e00c140110100000204890398242c400d604907a42d032030004498600c00c0b907407196049900c3c0f41040005040410103803080001c40101000814aa40c1c04603160403000d9105501d0311840503030180555030040a0b01c1000210706661610315815600401c4005040c1c4c113004100720300d50030008500e0f051690110086990080702403021194502c03006006030000c3c040e000c5207014048501941e0000c62050134105c1b1484030210381008000c07401500d01e85400f60059030412020816100340400e44061a4068500ca88006072a03010380e070b190710b240d041074143c031001b03000d801c1c0240000b10f0740041e50460019 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 6107759 1250 6106509 6106511
    0x509010501050f060d180303050711030405030304061b06140121050a02060901050c0102070c0e010510021b120f03030a0501081b04050c04030203190b07140306120106030f030e0a14090a 81
    0x1000d0900340e0300031b05a020440340024401901141010380c5038011a02600c2d0540e642c81c1480070296009440c3c1c4618401c4d203a040e0302c200320420176980116191071540c2804021548840140c1d16a17070103503281d6450806002d84140014003543d0795443c1c0056800b41e41968107150785190769a45030f030720341c0b9a101c007a00c0390f040030400314030b140c2c4101c0c1180d40c3d201e071a400954840902e131400c900069004c1c09200300b0712100c10008a110b04149840140c6420035a0040c000004507400074845074010310200ca4000e51031030035450107108100002c1d260500090011550782c07070100c0d030b50421070b441a0000324564014140039068000d0110205151001c2100d0009070794994a007403101600c41e980c1b0080d0140101c5034a11072100c1701c12a000741840c02440c6010305580c1d070b00011078044014640c04507150f0350a00c08600b080c1001030024510740d210100000f521611303030b02c40d00120302000ca8200c00240e400c1c02000610304002040740000e00f0ed0250701e920300c0364103e000441c9100f000708804085 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 6109009 1250 6107759 6107767
    0x20405060303040302120106080c010c030203031803040906031a0105010c120521040605060111010b010c030503090a060e030c070b0901050d0902040603060e0c1e030303010b0309070f060f030509010501050f06 91
    0x41d034081c4112401164018407080c070754041040c94a019160714841d940316801151100c1545501030001d0885481d030560195186075641250001500312966944009100911020070394001c2449800d01030b42c000d0340c0c1241440042029204150701c160465410410b000c0c0c0c0300000200740490700d012508141c14104c1d10b50220118499826084a0b0043c082841c40c0c0b05000510001ea40454091182a80c6540309200525505802c0c1c0b4a0503030282d002a40724040703080403903c200040d5030086600c0003074802001607030322906c060711004c181c400d20b9070704001000d020451003080000c1c0203140d11a103207802c111050002800d0340c02400898071810351032b011142e08642e19a44584e015640c0810200601e040300c030005a61292034484150040c502200c528051059150303448007240d00041c01180707103a00f820302090464001501c80c1c2c940d40700300900450380a6828910320050301c4183e80c1c0750581c02e203c0c0c00043c2558006030000405903d454014080741d1140c50745e888141c0e505644207607030b0b = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 6110259 1250 6109009 6109021
    0xe0711011506030b19050907030c02150103030201060608070f0206010603020f0903070f090e0303040f020105070201110111210f070e010203091504050405090601060c020904020109081504140307030507020405 91
    0x14184440381c806107a110460302194154150f070120061a0b01510070070b0582075020b02d00542e281031030042681c88290a0009618a0311039000491000480c1c8103a039406d8004c07100200403994280c10440260f5120b1005125141d4452001c0d54480c0084c54811007004072100065140c90040c0581c808260b00000c0103042c244580c0101e5800c03503000b6045440d640c0d80e900c9510600711242c0160300e007060038841d509040c4100001a203024a401c80310403020020f10394010744e155407103620304a0501040824980c2219028821100820301180caa0340d42e50110382039030940d551401001c0c6451590360004e0101145c02045036a80c004041d040c0b41c00c2e503041400c0142c0c5580101400c0640c00048800d101080c00c40050240080342d0059034288820b4541030100b070344503035090046900062443c0c03495809846e011200039046030060500704202c50305d0f20145400c041030041c07400038901c146000d1000b0803c0309440c140d1070b1200003010b5030800d15550f500a007540304030180a4400c075190404926 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 6111509 1250 6110259 6110261
    0x30519090302030f0c011107031110110a0605040201030c03050708061908010c090305010e010203010e042409060213060e010e01030e1e0f0606010206010b030105040903030e10090506010b040e071101 87
    0x806507800604590740c0312804c070342859072903404280c102e0003c1c004415214002200159800036240d0004880581d1802074060100c26285113480700c041060880701741d004c400c0140080c601540c090b02000c03841d0700e09400007405407854044100300301458070301080880c03a030049206c0c1d000041180c0310b401283c40c903012000c0035032036900801d0413540703003946540b00700d90020101d41c00c036886a8024411414008806401c0703000034070844003101c51140c001b4002030b010110607107112503030b80e40b9130000d044c66405001c06c030340a034201240c0440c0d0008103a03070103003252001e5000a0803d0b103801281070a01a000a200190b0514414103254a03030030000e4507110103021940c481c0b20384803a0b81c1c03141c1400706142540d8401d0f800301600940103203004214903500c0441c11a058074000d5a80901d03691802007888020040b400040d010141d0307039076203600350701000d00401d0003520b0000f00100d2900500d0030021f081c580103900140001c1400c0104001954655504540c00340d00380c14090300401d8440801c42c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 6112759 1250 6111509 6111527
    0x20d0804080106030b0c0717070f0614180105010807090f06051e010909060807060e03030d06030b010f050f030a0204020c0f10021309050403020c060a0507020a03060203010501020d02030304030519 86
    0x40024002040108a00308158001d40450380501d50316001d64071030b5021b05250303126080f4050000c11102c1841100a01e45100410240d80b2600c420141c007102a110107044031910800301c07410418440a00400401d9001c00c652806000c03030003006a5494103480c955108490302c1404086a03c0e84508407010070b0319402000185070213002c194100034200c19004032032982054960104041e0032010458020610586040d0386c4c00000a114280c2454000e03215064402000c50f0b251004001219142c80d9070b0007030b00d00551050b0740c41080c2d0350600400e0f6101541e29044903028000c0300180400c6a90001103914003143c0642d0010390300c0c139120410300e00340800349000c000e2520405c1e000304019810faa0003000801d03290030707480301d600c1e44420001e03041d03440030348010b001a8000b00e0012a149003060003082d03a6141d41c1030007458501035601203194100554410b550050340031004100300c0d6014000c00464000030302c06146949003c3c0c0d00903195019446180500d0301c8807241c06e9080a0187c4404 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 6114009 1250 6112759 6112763
    0x210308060f090a050402090702060108120d020c19050106090b0901031407080304140f01080c071716030903020a050109031e02010302040e0c07060c080108070603050c07020a030309061d09060409020d 87
    0x7901d000c0f9240c801618059404900810032400000c0d203462002c100d51b81a03486040c09052100c0c410121506940c01200d11200c1059080200303640000c1c080080940207001800c50a170064540e0800c1c1307003103841e40e91048018508000c6120000d660703e40e480c4e415603901c4400300b00b0b60b9404001c01454654140c010324058480028040f50780b10107814011100d1030b089451b03070410700301c40380111080c6009540ed200c0c03519003880148002101584203000b445110f17a0701ca420050651000c20400b0f104480a0f004500c800710709000350706103c94400c01402c8282403041000b8035540d6070090241d43c01503161100202407500f01d01b10380c4250100c400070000c0c00c00700b44c0c03a42080c1d000035a4940c400d040841e00540760a2516488502030491141201e0400d009070455900e0f001082d0054980203060880d15407081100c0740059030b4208460014501903542d800109040840240040e051590381c8105e420141d90802c01c16903821403242da1010098802080d05d040910204a00d040d0f13100340 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 6115115 1106 6114009 6114019
    0x80a08030106080402010e03010c1101061e05060a030204120602091002010b060a050a030b0a030807150203010b0a0c051608010203060f0d150902030a08040b04060801210308060f 78
    0x10f00c80d8050300604000702040d030603000082c2140e004506190124440000c070300c032420400d00c5100040c3c00301400302d00212000304170002d1074080d90b10446d0304c2890000780c908502c51080d01030320700401e004050f18820050900e00f400c082d4000500550217460494404850b81e0f20500501c0701c48403020705042d1905000c0602107410f50b010a800350140b6445070704206064580b1801d100c000e600403100c454407203600b842c0080d10000800c0100300641d0060005000300c2030801d040b92460360081c00c041c880030300540792003424181c403030075450b060000d2108005841103064004510814044440f0041914124100819901c2c089001350461500003006040c0e8021a848242007a0005048405408081c1d45042550380541c021011b62030380800c08002043c4c0114210b800f401d0804000c0407106040c031181200c4148141004d010040010013040c49600d6010300c070200d918002d09 = true := by decide +kernel

theorem cover : BRFrame.Cov 5935259 6115115 := by
  have h0 := BRFrame.cov_init 5935259
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5935259 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 5935259 ≤ n) (h2 : n < 6115115) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
