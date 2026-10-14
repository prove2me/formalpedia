-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0914
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:55:08.891876+00:00
-- url     : https://prove2.me/submissions/67761594-59bf-4353-89a1-75972c9dfa85

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 164208633 ≤ n < 164388489 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 164209883 1250 164208633 164208637
    0x1503020a0605071208130212100e0c0916051c1508010b01110c1309050a1218060311031603062601060909112e031b11071802070209010305060402031002 67
    0x11a803041c06c00e0314030b8006003400383c605000200f115080320124800382c4001c006490b25919624000d801c6440c1d542c3d417506000c010560090803210f18002408480c40e002000c03805680315100d07000000c01c0c0d0302800b0f0303079046d0f004103500c614420345103240f903448018941c080e144202c4a64001400340514902050b00403a481405ca50014042d925400d250520301014020300c0500350759500521101000080310100c910300740c20459214078140849010020001c00308544c09881454141101c81a81080300000c4030750048007588500c114450300b800c1140140401e81000ca10442d0805441c05500d040044a041c024000d00c0207100160f20b41801d03406481003940020440d00300c0d0042100c40385050418410340d40c4440e0141403c0e5000b1f171503290401440e1281500210b0b60710b8100401850080c0322014100545040500c100da24400e440c41d550450392003900b50022190a070306104031060740480d01c25030780007044454596183d003061500c915080d0340c200c0c0300b07209050340c103084030b166402 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 164211133 1250 164209883 164209891
    0x806090c1507060b09131a06090105090a0213140a09090f0b06121504060e0c0a0509090c0307090b18040f0602090109030609063204061503020a0605071208 68
    0x140d07960018200541185540006408903001919100fa41d5205d480b4000003d00c141000308402088031968205403c1c0c2000240811141200e20404c000042c2c90740a0002d0440300282c0b4882d92554541c5902e600034020401c405002507128180010501c1541e40c0702400c80c8421103082c00304a94412084c0115640018010003084032107410740c021400158280740d001c0e2024141c0000501d224200c50702b0700f00c1d0041401c0c01124034800307000c10f000d880d20070b011003102c003640104881c40d40040081d03a41034507840380910600610f0005100b5500c1400015110b20024048459a5841e00000310181c0b103d880c07118040c40f20481c150040d007050401030790007aa00310401c44141c04443c0c85440203036000c1c002542c103200140340700000246d100e1040000481c015440024070014610b200c40000d1104034542c10280c10300c14426052404072481c0076081540b0420000740301c48154011004406036a001075400540188005491904480186a071a10a03502c170142080b0035801550491001d503 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 164212383 1250 164211133 164211139
    0x303090206192705040203040303060806010315110307081303031b0e031006120303090203030708031e0c0408030904020903010605060a080702010b030616030506030a02041a04050609090a03080c1c060806090c 91
    0xa80410050505ea0700071130b0414043d24001c12000d072501c400e00c2c6018020b074021030b002d0703a1140d03024510000c180b0488000c51803134030720b680c030311304004000610406028010130b450035001403007401054004e038010560703074640c44402240403070500c00241100040e080302c1e900902481409200c00c450751700c5101d050382d1002000b0301d4848110b031805c81c0249000301c2c080ba0503100070842d2801282044018500c12030305409030aa40c44501140d03a02c0d03050014202103c5180c041c403080c40320344004410b950b9201070940340162640b07200cdc4c0010303025000d10790042d034105030700040c108800c640c4802041d01c903d950783c00030301c04040340d00e00340740c1d8402c0b01300c1c0c6e600c0c50100482083c0172034501c80c0d00300c580c05c10780040c200c40c1d400000707800040860f02c040116000c5400f0350300306040642800d000b001c0d44103101302c1d105011031500b032001a0b112640440d000b820031100100040b80f0b005804151504104060041405002d450301082d00170300d407500403450719101d50307000903982200000c0c01c2c4488840203 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 164213633 1250 164212383 164212457
    0x60806010e0711070b0d1503050c12070f060302090a060903080f0325031d1203062e052a07090c0908031206040c080103120c030309020619 61
    0x4952040c80d00c10014080354100201c030b48909070310f1a4108000c001500050151507518400d0b400360303100b19000e800843c00da103442040d0810200340c0108842010000c15140d1008244030000064101101e54116219101c900400820002d0703069015156100d8280e440b044540d40b203810030748216015100c0200701751000c112903050443c1c0c1034055500a5584010303181d41204c854801000c00c0f42d110091000a540d6a4040500b42a8080c13410007645200001c2c140f40e0740075612016040c480180b180e030182014808d42c3c0e54954140c0c0c90540e080b002d0118010341459006801002075100c0300081480300184101d001c00110411005010918111300400038103203007160a4014020400084081c0b041c41030b800038614500b8001800e4080b9403112aa03214605080ac1004891141030404100840354006000083e01c500303160b002c803c000c0c1080c01d600c7c50240b500b00c0c041c00000d01c00a400c05008100700c00313841c50b0f04040710481c1c61146c50340d00282c0d80e00b0014a0b55201c3d503801e40c01c101c00c01 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 164214883 1250 164213633 164213639
    0x70605011d131a0403022a010207090902030f0a060515010e01020c090a06080a080304050d020109170f0409290105090f04050c1b210703120b210304170106080601 71
    0x2c0140301c03000c00e8459040003416002c40c8100180c0d400080b103059002d81c001081c1c88107010170428040c0c2c1502d03400030b0f420071400090750000f982c40340f40303016040311250b4a03a103100566804003e2046000c0c2d442d0100d86240740540b0b00300026100945601440d80c480385807c4a00f0742c01080c48065049040c1d000744584070500d0100440103d004d80704003141552401d001c9001c40c41403000301e50884c00317545840d07600c0c1000d26000b49081c00e1842120110b91500c4848400a2010b280f025042c1e101400101c0e00c903c8030b481d206085201d04d5204920061811403900101c185c02e100c24400b00101400b40080c4144100041d516881080e1109522280440c520f6006d440c207a401a6000140003d410b401c03e8041c10162031007003200780c00c0410035800440e501100c484945418a903060960304064241202d550b0007030101e00b030740a01491640e84a402e0409203484800c001110710880c020a84000e50706900c803d6100d921a0107070b22001c40611918092240b81401204125580c035002424181c0ca = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 164216133 1250 164214883 164214901
    0x50a090b0a0f0815060328050603120a030e0118260913090212031306050903060705031807090b0414040510090203030c010606090e0105090907061206090504050102070605011d 77
    0x1084c1c212060b491030000029501e544014604c0354000f0504200700c0d42e800061030081500d06400411503d040c402000344584010031100d129007501c0409944680184200760003402410500030b0280d0718242c107102d026150000d200340e589005959040d07805142062000c603d00300020301040901042000660070b007400d19244900300c07441040020702e011254001a14291200d603500c04592020509001c00320400060300010213231414054685a022400302c5e481d080020404000d210300800010076134441c03c1c070501c05031001007041c0ca1406440d026032400518214035054002e034031b020303814038410f494000c80310300075078002c001821941c0c0c02c1e8000304007500304503230b00703d800d0301040c4403100d0100024010040036003210348590203d80d06080040408081c142d02681c030640c2c8000a02981e81e1010a04800742c03074581c41e2075640c414001d4440006003c035070344800b40d520f103040300f00300511a065020307000ea170b4403030030082c07140340d0741c525804422104000100b840710200c3c3e004a25410 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 164217383 1250 164216133 164216147
    0xf0d080a14010b0a050f13150918022505010912050a17090313030b040b13030e010305060a0b0a020601080c0f01020624370602070509060a0b0406050a090b0a0f 70
    0x50500c0c601179183c040386981d05002ea4000200c00d0381054801001444034102c00412032401c0c0b80d040c9403850b1203d1800241901c0c1a0350729440f84d01c480e6000480350b00b016030044114902152a24105103002d4a61030000c0c001d2203683c0082e1549042da8243c40710b464858821546408020307510400b1168881e5000c9100d107001074031101e1648030400154018000c010404c600039402240c02c41c20700c1c50241002c81c69100000c2c503500c52080011364a000290300301c8001100d402003032900280c10303684c140115031086200d03040b41c1c902440c0450805c40c2a6070010b030041c142d6940d441500c0c141c1d1032102c00e100b11b9501c11200ca038096001030b0009000c84a1801031346124000c0c8103018001e548180307000c640b00740300000d00314107440d108070f00340d001001c2c5001c0100301d01f400740d80c2051440d5103402d00003074a500082c00f034644210070141c04907206580d070302441005080034014180c0c0d140d42d00d80000d021030b030101c250340010401d04000001c518040e08140c07080e00205469180346400c4101084800c4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 164218633 1250 164217383 164217397
    0x6031803081915060908012307031e0c090803040501092907032606090109091103030d0b0a080a08040509090102160c060905061303060504050a050f0d080a14010b 71
    0x6544181c0d880b41c00c418803402007501080030110541c2d052803c201c0010034800441c2c00c8003400381c5c103080386410f0301000305a80c602c8040200e20800200c0e01d4030308084000e03003030407810581300d841a0b00320740e040030425501605040c0c4a50312460501a6688185603ca000364402c080c045a040003082141600340c4011a44100496010032040603881c0844409500610815030016142c50a0382400900e5035822201068070849146500c1c60543d000aa030300d4414001c4420158031039041404110006090424400000b03040e69100c0408850840c01850a440018403030058405c0000c1d028001085c003414940e0170814180c07400307040c0020f000011202916003c0780c3d6508000c05000c50702c0b0a2206584a44944042c00d1154070b4120000c100e0303005900042e100780070400c03104010f403150000c075100700d941c4507c001c1042d1b900c50404c00d040c022084005400340c0500610300c0301c444004520502c1c0d0038810740b110681d80c3c4032152450115a9501d03140741c40464018010710108000c40301030085 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 164219883 1250 164218633 164218651
    0x6040509070b070b1006020118110310091a13051c050904020a030e0f0708190c050a0e0f0f0103020306180327040b0301140a1802060a020d0206010603180308 69
    0x4650311070b180e0195601400003542c8103207202c414003001304001e0100b8802171603240700070703c01034410641524404461160081401c0d00f41001c00c40192010301c43d07404422020103042200000a050078100032101140e00305e4200384441c005121110000d1603680041c2e0450010544107001503484000d08004507202001d00100b807021070140e0340c60303000600c00d502d51036a0120300c403034807420824034140003641d42c100c0c0d0340c0204406100c00100020b014059803617008858040f060a401c00c040782c1e22058004507040040104007040c00031501403214020301040445c400b80d903030744401641c3e01c0380080c080290b250300560042118042402040304080304d0356001d991500069a40100c41400e1813802c009814641180e982007528003440392006107076041d0004d02142c02c500034002d40b4081d000f02003c1c2c20507507807807111760700707024a07400100300650150410365140c081c410041c1d034520070141068018480c400010603101c0c07203801140017180a100310404104082d990507140ea480040800070 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 164221133 1250 164219883 164219893
    0x2010201020d02070f0302070b163203040e060405010b0a030b130507020f0f012c030f1323012003130f05011101050601050a0e01030b0301050c090a0f030b06040509 72
    0x180351000c43c8028015180301e00081c42d098545450040e061145c44c2d400300b12a08408d01c0244080d6180d070807104c5615a101a4000707560020031903800e80404507900c0d0f8008004d201d00d40c0c049a1500000030000d886040404000c9030395444100801d8030000d01800102200078402811080c0c0640c010b0301c06420000c0841d0b100285d0f01e0340301070071902e048440400680c0801d40ba01c1171a501413085010503404c0304024031195040c00c0d681c2e805000340b2002082e001740107418440c040041401913071604482c452540b03030350310108103146860b08102c0c06001c0e142d800e120078030314840c040c49251b204038003c1038444000d04801140300c0c0114480d8640540004e000c100800c0c82c000010034a00805045c40800405580c2d00f800300042c00d585440c64403443c66890f100c103100882c1c5c1c2080070707078840246d180b030300c00403100304040101e026010941341c0070b82541c248010312440303002c404044c01c2440401d54007440c2e2555519000301e009101440040d001d0a0281c1c0400e025042030342013290b0090240003121 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 164222383 1250 164221133 164221147
    0x3050c1c060f021c050f070c150c0503010e0a0912050f090a0b1801170f06120607020a030e01140f0c0109020303120910060305030d051005040c050702030601060f12090201020102 78
    0x3000d80d1a40b81c00010700603800030300d152800e52400d40d000d000d090501400c04c203524001c40c20700341c40c803006800c000c20700604460b11010452002d00044114402d124103110300d4001500240c140d400c203000d40400d02948800048415615104d50300546d900000004190700031b80405a440b0303406201c1c03031649500e0800140c0050f0b2108044103009054600d00c060791403101500103103c82c9901581c071810050001c45440b01c004000c18010340000b244411000c0544170312001590458103189045018080c03141001040f580101d810302e07200d802034580e448059900801100c480250840054001609002c43d80202d2061005414222600c40002603410035540000b0f2440e000011030750019044841000381460341404100d100706680d80c0700b40201e40c115996503449000b824014560542c0d500006801418699403403c01410098410000b090840c1401005540151b0040e0300078813461000141503845110401ea015a256540d4802000c003010880c01421030703104140c5c119134080c0545 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 164223633 1250 164222383 164222393
    0x60f0d0b0a0b031606090503060c070b0c09030a0c0914010608011d091e0a060b06040302090412122415080106050a03060302030601180e07080309010e010c0803011509090603050c1c 79
    0x39005e8440354032032410061602080620706030780144404903540c814000032000541c44100307590800103203540591200701031004603181142800c2c01512030307800c0d00c000041c0403c0d1039225501001d0b09104203d10740c4e0301c0e8841070318001030a03c00e031482244071070f90305030101d440900e9464205810000fa140300b0396210b121555050480c08440142d40c02c070250350010082d5a01c560303000c1c8034050b5080e0f41450300c0c44d0000790440100078006068504c000a80106d203078800c46040390801c0c04070b070080100d9003410f110040c20582010070188100248034000c0b500c0c41500c1c01c0032048a40c6030390f03841081d070308086080b540ba400c4a00e40034141a1602030200041c3d60500401c0c1c0604801010031041403064400c0c101a04d0440e002d84c28603400c081d0003803080358004021500f2028003070801805200300840100e44942d00c144000d051010084000b0039886c1c0f070b090502e09040013030f54031224103c2c0c9414a840c201e5031540310091855101c0e40044d007280c2006c9039881652072400350050200000c1d620350b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 164224883 1250 164223633 164223673
    0x4080105090303010510210b060909070207060e09062103071a0411061e130801090f0515131506090c02100501060c020121020c0f06060f0d0b0a0b03 65
    0x105001ca80022005001c14245203010490125443c50b00300c4040c0d803803010101d102000402034025031a04c500100c202c58a071001110107510021b482600701d440e1801009458104901550740000d260111804103450402102400386900a010a440d8000140c0394403460344400c0300c00880340803d0003458003184040301015050405010052514034081c5030800352290301243d42c622840c030911410000120b041d040b800000180d07036032240d503008405060b0300d189840e90700c031006d150300b032280110401200800820b440d5100c0c3d421030f4a421010900c0c0c00c0c1203502103c0301004051403000090200d20380d04400c60380900440c0c40000e0032516001c10200380d4041d600f5110140c0e100780d00150405141e40f26607030040c121883c092407081c2250780004c02c2c900030903074001c1340c01311003818143c65141c0541c106d50008001c9012079000303082141180d5102c2504a80080c4200004007800c0b0040c108080e5820b000e9610200c18001030342c0e0321302e5400040c403c14458a03014413412158183ca1121122 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 164226133 1250 164224883 164224891
    0x90d020d05060f06100f120902061e0d0f0b0d030309060f0e0c0a06090b0409020c010e1911010212030f100b0d3e0a0c0c030606031101020d051801020304080105 70
    0x15050711519208090190705c200880c501010041540b1031b00c040b0950104044044521305c0e41e01240c0700e00d0a00014016004481400c981c00043c400c0e010400c215030402048400d030b0101040c4044800d402030102203e03848100607420522520601d00000e1283d800300084d00e2041100140100541c00340700120b4030b622400c21070b01d6021b62401583ea2410041c2c140050003249050301d60903050080c030b282d4a0143c0d114000d000da4000c10702c001030300000e41040d500281400b00700c968025400c5618084403404000580340c00032100381d909030310351000c500001c1014694000c0ca00e151562003c2c01400c000040c00445070002a6001180500c0c0f203400502e205103c1c3c040214014403070322204080d1540048002c0882e400400410060500380d0701d0f05c0003900f01440e10ba82d101c080500c0c00390707640c800400b00240b0b00e942c011400300c108030382e59200360140c030700494100c011002c082c001660794038003100042020800500c40000c504800b03520700d4800140600c15241407a996204486c207440c0f040d5 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 164227383 1250 164226133 164226151
    0x20312182e02040603050f18190309081501051c0f021210060e060319020d0b04150204060f03050f060d060c030e060a09030f020a03120c0318031d010c08090d020d0506 73
    0x41c02591f110755104141c001c403124080009401500d90741c190f440c0702514620120119114076501403602680110008024410603660394012480c038104408809024152182168092040500f12940c0c1d002050313950100e41455140180c5d020452541141d5811088900c2003074082c44681c592405160020004d6940028441c2000f01c02c0500301160040d400c4141d14100f2010780c003590f2508801440941c014100300c58a0320ac2e03003440e6a40000303920070b400005000090009030103038441000b001c99241d6907010851510740312954a0017510580300360760301c01055040080444d1255018200c1040c16007000246e15180510a6040c04000c8a248117425030b00c03410300d020302d500030307015140750a4140f002e0072801e64155030182242c03070048402c0301c6060b6180c43c0715407040c1c080da020440b0041e0295508100320028540104404070f42140b4004c0c010900b0301086583d405103060765174403a84088114100b00c038220900920382d800640507607010070302041110120b8018040540200700b01 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 164228633 1250 164227383 164227391
    0xf0d080d05070e0f060906030406020c0609060403021608100b0f040603080403051002030105011403070903080d09050705040c020a02011b0c2903040c03020f0d020a06020312182e02040603 82
    0x441c0002d042083c4404005014010120840246540b4002140c0e8004401c4a00780e8803070b1520b0600394002e018143c0f005466108541c1030291010b000100c913481548650308448803030070554100c020400d418820100254004041c0c0140205103070403070303204c9200250a2888400d4143d0008054801951040c1c2e82c03490001000e10030f110088c0103810b03031100b040c4010f52443d40b402000805100d81000c0544800c0400700110340c985100c0d010072001960442c070f400303440312504050302c0300074480c40f18101c03098402c010300040c4034100350207403581880d11074000e454042030980041d00c40a00c910945494a0004c00580e000175220625103006428a0384000d2403495080700713041c822120004804402d003209004100005070461002410342ea0b040ea50b07000180c42c50004504091103103103000354080e04501011440c01e0740000a480c2c050032103c02510141c076140841c2d820301d841c001090030140c02140c50b5913100c01405030a044508100c072103441625050300800000c03030300030b9000040080c2e29 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 164229883 1250 164228633 164228641
    0x114031902180310050603060402090c0706020304060c030b0d03080601050c031902070807060e13090807060507030b01021e0d05031b0a0c0b07030e06040311010b09040605010f06050703020304050f0d080d05 90
    0x42113640001c0d02d070640100143e007885e50019a8170800100000c0c031400440c1300045850361128162482c5503070161007552642005d00d41203029004011040d40080c4c0b401c010940d1600d40b0000c01e21450707400da01d52040b180c8880004544503030003040541c90611082260010342548110a03918182466028103d00b40c1809041e608080e4198000001c0107490fa100300007503a240115504400d6030350000207103886540c80c0000702d600130b5610181005103080c04200310250190446da10880c1e00b642650a41c8142840070100079004c00c0300b41c0070941c07081d030440f9403050049004641050054408140210720038625075100c3e07005c1020f0400080c5421080d80401c1092891181c01003914102400341c0040546050f1b41e0b108000c101a040010b80d0b00d80004210080d40025035040f0094001002c0d4945414410040c2c0028804c12410449007000090064410b00503034003041d030716a01941c900342c0b4100c2040309002c1010390071b0341c0c0100082030000c0021000b0b801446850b0828030080707030503d4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 164231133 1250 164229883 164229889
    0x70f1b0c1712040e06040b01110312041101020a030507121b061e050403020d2a0602120a02070803070c020f0901061106060f0d0f1506240201020702011403190218 71
    0x149114080542c0c06200c01d10588060b2074085501150075a000220198800012540c940d490201d50003103000c00111180c980440102d5644118007038060003011542002c01203960314000d100c040d002480074414800003c9501d1042810f81149240091040d0280310040c02c10311014001250742958801143c14036000c140180b10b41d2150381403013048146400e44020b5100c550544410742000b8100d4440c04184030a001c182c9554180110899140c0000d1701d00782e002036108001100030340d0707000da00107080d0004030f00843e4a10340e4031005c1c05095807030f00701041d03481141c031a00480e40035991910100141d11189000e50003008242c1c0e0b4034110400300e14170641400000b42100b802050003298440d0301d03071503000e82c0d100142c1c0d0007103142d07044c0c00c0395007407450008100d180c03048940c90610b0030005402c468041c0d00540d42c801c0072640d03c1d1040c00f001042e8201d20070020000e01203003403803c40700300c12880c10018540c0100280c00128a48070b210134003104076880520a914910402c8a5001d0030b42 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 164232383 1250 164231133 164231143
    0x417060a05091501060c030207090f020a0e03071409040c05040203190513020a18021605030702090c04120209070201020910020f0d020a17130e0717060306070f1b0c17 73
    0x41001003e4210b1890034400814045014003130b100034804034000f98010580700300152070041201041c200002002e9a14810107548424842d90000360050346480c080c1c500404c2c09812074a08100039400c505081050007490341c1c00520640e124030301034800003403507280c41c00114420f54040a04041c080030000446080310f401800c0180ba0004ea540014010f8131840700c00800d850380141d019403c10407481e0580e02901c60f0020b01c410300b000e8581d6000c1040b5000007e400311a00c200c413801c60300e940300d0700300003143d0040340301e000000c13079541c0003600260901400352600503031148005454000c8910100e070044002c1c2c8038000043e400000d4081c01c00c0c41c1030012800003d00303407015003118040c903190403104100f0041e40401c2410000740c240e102c2e05031503180d14010704e012507000700d6624103c10050f0080018070700c402c1e0401c04140004415140c0070070746034031501d40c07510340e40070100740400b0441d1320f003144008001040c03248030000300c040707268001250020044850b409080c5415405294145 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 164233633 1250 164232383 164232391
    0x1030803060a06030902011710030f05030307020708120d02091318030e010c150c09150203030a0c0924050c010e100b04151401030204030803010909022e0c0501020417060a05 76
    0x2605d04034100c2c0c0181e82c0488480b00c0c002c01c00d88610030310746070300f0301a0807001d10a034001040c03140d000ca1000e04005001c800745106a4403074080d1840207a80c2d4503a60b4582012081e0405094810810301101203850741c0034100f04074014080c6984070000346c10000840c0c101f8400640b5a1005034080c00400d640214030300c8032000c0030300e00300140c110703151b4500c00c4090307916a150602944610845a160344500c0302c1c0802425281c81445540c3c540380c2007c2c1d00d9034010342e1850019810480c00840301801780b00d100c021680c10010890a8002c2c0032070905046a070700e00702d04200031040000c00d40d6100c00340648810507030103e0181084d480000c01c640c017140c90040c07240b80240e042083c2d000c0016224580b460484080500b0300315202e01c0d00004800034800c90304001c040b0413000c8004100c1c00b03c1d5034003120710301d80300342d86461104950000c0d40039401da101c10f400781609000420340865174810f10000800b241300303000250501b915074144142407051194044600c3e800a02008828100d5001c4c80e80c00c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 164234883 1250 164233633 164233637
    0x2070203010e010c0903170f03070809010c0c03090b03060a180608060a1104180207060606030902030c220207020105070206040305061e04050d08041b06022103101202150301030803060a06 82
    0x3620418500c0a44034244d241b101510100e110746414140c21952812150003600710712001d0b0f502d1508075809070501c4000c0d18403800079841c100f5110304a0340103201074824181c040d03d8058a003460b0000800c41035000800c2a03810040c4010005004018514454810b030100d40d4045215403d050300185081c2000f4140d106040c20096851000e4070500c0440b0161220b00c1b004021700700701004204041c1c422810b0040109103400000520380d54180e0020f290148202d040c0d906d049202e008105540c2c52420405a011180b201030b00015030469008100441c410306155050103030073340002d0380d9600b26a20584954201c50204480c3c40254108e440c00d40d400302c2890042d41c1810703198a0ba03150315004c0c001d0140305100011078144040380800d01c1030320309510313184100c96807a000c1c02900d4820550440610025a100d0b100c03d685a180a8902c90048406500c0200e460300b0b81e081c1a01590b0003013031341c01910104207180350058080065011358011400c10f9a242855818001e40840507404101 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 164236133 1250 164234883 164234891
    0x2010216060207020d0b1501030605040e0d2105010f090b030a0c0b0304150f2004080c091308040f0f0506070b151f020a05011803050409020f1b0102070203010e01 71
    0x844551008040d1541c1001d801600c8082e079101190404c1843d1001600c1c640c244402c02083e41e41040d10700030700c0c14084c3d80c1417041964810610042d2002419204c03c40e400c0003840d184802e10944621504030340780744c45841d80341095541d01040365002e8100c0c0780c0d80b051f580300600510040b40581c1007001380c182c004009505113500c03041028140781c000e1400c5000008045400e105003158040d600a01a101c204055202050403000900310310303511101441107202c00c0c0090a60742015602280e020402070400400e2545c02c005888800502c0e0001d0130009040c07078030110340c2d04805031014003142135214032550f05100c0c2c2c0100d05900c42c2d20651040d0400c000486c000f40018114a412018502c5155000d03003a00c000140c00414401b6465241000c119000682a9001071700c12450303405940200105910021105c0c1d4150a00c000076010550070001000045401c5e4002c00c05440740c1114039007000c5c48240b522040306c030720000c006210b81d008640039065107000c1c0300c0d988010f042c0e540200 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 164237383 1250 164236133 164236147
    0x501080105130c09030c090f06061d0d0f2306061f110a0203030c010204050909030403030f050a09080106060f020d030b09060103090206040e1e2d0604090203060405010606020d020102 80
    0x3400742c12036440301411943c030341c0080c125140c026030024001c0d6074070550b500529070300d80d1900c900500c4028003800941d4201400000d004d0701440e08001c80300802e4610301800c011031001d10412211189044400c0350190b40c608000c03960700000c0070b00c41d46058211000761000c0c5141c1c1481e209002d00801e202e12400d00509183e9104e540c1d40b480c10480d80c0c10801014a50302505500300710341942c0103034260100060704907106c070040d4010020b8030000c03641c884d00381d15000b0800d960b9005900004020910007940444414007903c00b030021441140f80015900d5254204282034030341941c03000000c10300300c000281440c2d4040c04002e9401400b403900b0040e0701c1d000070000d0f54014000c0c5c01541490341d00c0c1c8003034040d92104021030740a4421200291494100381c2801c182002d0841c4520b40941081404640d102c5d0b4828001103082003070700110a0b5980507050000c134070f2040680980c1d44203950381103407030051b141800a54480d500800000803642d2804030081e040012010004045910410010f = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 164238633 1250 164237383 164237389
    0x709080f060604111204080309100e10091e030507020108090a2612010803130f0b030114220b0301150e160203090a15090905011d10120602030a060501080105 69
    0x107911036000c480c08251246021040300c036034400c601e01000602c05c090100400c0c030158400545c0200c8909045070701d840c2e0010310107022540b2403606500140c100c0c02202003c03890320f0b041010114001c98040528070b010310749104000c800003400318007194002c42d8401c107641e000000b00f0b902405c1e96024004038900e80d6540c51b40b007d0104070700070b0074502d00b0102d4082802c00030290b40c4290700c16403452005507140c0305410740d2500207440602c09041101004100910034086030022550301941141c00d590a020310311a441c198a4070304d41e0040c2c41030700b6000c01a28010316010030800c208600140344603071502498203440030106201c00c2c0302250a42001002d040340c00705540803d064540e01d06403140d404049007075100380741038191302441d441c101080c007a8820000101d248130903160f1500c02035440d0000d1003904d0091048005620105002c0302804480305946980b081f0f100c00e03a44400d68a40c40c0c010100200c410059070601d90200402c9030000c26445603501500c000d0030010200e40c500f07000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 164239883 1250 164238633 164238643
    0xc050702060d050901110703270b040e07030207080729090a06020c0304090603030513061b08070317130b1003050c010f02010b1305150409020609062a060709080f 71
    0x181c140120f554800080c030010082d8018400c0c24041c10620359075a00714100201001418104034200035007403200004a64045203108003103480106050381000c1c41c0000c0401c5900d0024421818145c08005100008041c00020f1103940c2c820301c0b20f0101c0200401c0703401c10603e501c050b403045011003201440280341000641c1007810740c1c030010160b036403101c0e0003110f400c5004c2d6a000c1402c01c3d040035408010150403501078041e14a10107a05200c0d07607aa0442143c0e0203103214848c01c010b095246400001c14105070080030035a000c0d060220001ca4042900421800e0071035075482003c0c91000b0400030000000991500154804641c0b08480c1c21350302c0381619401540c070402d0501098103002b1a11078000c0d00049070b2060010410707005e04000c402c0013009024101c54000203015036110380d90140c50144581c80c00039070050a101e00300016103040c0b05480d403100e080e09101c0382034900419800080c003e0480c0c9048004005442942400100540034400c584c01807030054010000d018805600015 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 164241133 1250 164239883 164239897
    0xc020306060f040f0606020f12281701140a09051b2503080411091501111005040609171e0706020c0f06090c011418151306030c05070206 60
    0x58166107000d00d00d80010f0081ca45003a80045190410300009072203a004070f0703d840c0c9a60994103443e01c600e02464080303030038424406c800d403020328614640c00043c289510700d01050011810311114888011080b00c0c0b80030700036400202c006045038100d00e503a08211032214000e200d0403209000c0ca040c40c02c00040010000c1d11102c0c441d520224040d030754030240300b0901070300f40380c4038500940380c81003410001c01c05a0101c9003070301d508003030000c90800e60038510540da10481d0350031156000d5440410045980402203080b00c20071f8403078010044221001c610a560140d071050b0b00c005002e001c9460310088410000701c895511583c180030b9001040380e100186e11200c808104090343e9200c0c03d1405d080207000b015014080c510840c42400740c46000010402d000d07405003021100c0c2103000b040110f0304030003070401c0c05020080034450055036006c850400b0203107400080c00020064140c42c0b006449800c4500e04a0120540f240200700b040d405105518081030140391041c50f00c801a004500c60344a618 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 164242383 1250 164241133 164241139
    0x1b030111030f040302010b1e01031b0c0b0601020309040c050301150305060114090315130606080c01020c1212030705071509080912010605060315032b14090a06080a0c0c02030606 78
    0x2000a080503c00e510150880e4001065a44501e0408680055205e041034840380442e24007000454050403c14101c0110340bc595a0001c0384c03299507564aa81400103400c6505622041c083c181e090b43d6a0302840301c88402540e1542d4480d03260614890950039081c1803803060519200c01c0c05000e903072103e00085851580d0103a00d0366003450501192901501c030b82842030000600c018443c0101c000c0c240103000038001c01090099549500701a915007481c500518003580c0b1552a440c01810142800350310900301100b0390b040d02c1d40e8800000140c0c0c0c802c86507680010000100c1c407041006c8404500220600007804000d61072203a6500c0d0400d101d41201c0c68403c0f2441c0084130104002504014040e0101519403916409e1508007a10603e0300d602d0f4803071107801203003510320b548560345900002d00082c0e280c240c15150440340c02a941c942c421151441141010400580d032a101c411102000b003030705a44080342e524001c0b07116030448401038003c8040211002d00003000d640c000503e55000741c1d00b1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 164243633 1250 164242383 164242411
    0xd030b09061c0510020a0e101812060609050a02090306010e0906040803090c03100b0114030c030c0903193009090c18090605182202040e030c1b03011103 67
    0x16040c01d031300d4545841d040e802103030300010340039030030503440b0341050414001030303130701200c543c4002d80b040d40c0c4540004c10748140400c03152070421403180340c0b910f10303448036000d907000003115a100c041a90a541c07040717400980032a000520007105090402109004012001a6641c00d041c9050960384403c400b420103003401c840400842e0704814140100103245800a0880b008200108540d5002c1c041480180d400b2a0211400704107034840e0a0451b44540ca003140514615951880012695042883d580b40c0600c40e4060341c442c0910001300c20401d42d40124082000c1420b602d004e114168120481120000309a10382500d03160b030003019400989900d03070000f0888505120044503d005046545400d445000744000b036042c401da41702c04243c0301c0680b040c11282e41e51940c1d03038220b003c0c160750403402440443d40260505c8a03052001c81001c0c030050000c0f804040441141d8619004689600e030f00d40c0084581c20340303180d141e84030407000035801d03402030200e6600e58030403c62a01004019291202d11 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 164244883 1250 164243633 164243689
    0x403020112020405030a150c030e120a020a0b0403080a0c030e101a030706090f0503030403170309121b010f050c18120a0b100b0f0f07150e0d030b0906 66
    0x198040e1000340c5005402c60f145108107042ca11281d011f0151821026460141030380702c03031486070017007940001d0141c005050100728141d01d042540e0090b81400114002c0009010001d03034400e070107038019400382d99507c046042c41c06400045945035003804003450b10b0b091b00301124440c0828002e0000745011070001e500032a9031a1748017001402c12070b1a0b40350169640100b40d840c3c102c5a030030140c0d001120038180c0c0c5603d64080c15900d01c904d0202920f07010741c4500060300d400d228001540c3c00107081c1c00f07696040c600ca242000d030070382003016001170326007140a40c482e000200f4820940301d8441400300b885241440340050802c3c0c4620000c03d040e40d540302410783c00e651507050b515850001c0c0b5101f201c0d40700c003403400c0445024600340d030940d50b869040700d400a8851005030546075400d109080d29842d20301224240580703070f4803410007206d40403000c2070490000c2d04544103060070403408201034402409414001812194542c1078544140c45030703418400f1585401c030681c00310080340b00d418100941 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 164246133 1250 164244883 164244917
    0x904081810020a0c080c09040206070804080106150807020601140f01050702120604021c02091801150602030d0b01090f050f0d0506010f060909140610030b0409050325050304030201 79
    0x24000340c000d810506500d2070010700c40d40002c040341d10034011600c0009840e212070751a0b840341c001070400c0358014150f001003005490540c008004152040c5089480e11740c0e100900c1342500c19a0384002c81e444001003100b00c1c2e803508101e04941c03150701440584010360402c1041200021221402400b4001e0130290b00c03c5032340507400702c0d443c0300e40051412848031400c10030320744c0e00c1b14102c0301240103440313403c6141c4284003281582c0000b181e00900008403940c40724807001a0492141a402c040d64882001000941c5189400d0000d000551b02942d81c56400f20f614409448040f1180b82c10804a4901042a09013403441c0740d041d25403c80d540034081105c5c00004588005080010b4140c0c0a080d000184003502914007008545030358445030541c0760b403141300c9230803940da65212528075401200010038a1600c41149050a41c0c2402c0000320010343c3c00105086032903000741100c0079840002d500860320001036186608584150400b07075104580e6547c00d44a001d00d2000906111102001c180c0d80c034 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 164247383 1250 164246133 164246167
    0x150302031002072d0615030b07020f010e030906090f03160902040905010b1c3209070801110a0309030c0f0b070315050f0904082a0106050f090408 64
    0x150010100c4481080008081d8000d500950301240c5180c1240751021400d11080580310840300303844c61510044003191252800341441d07585101d00c07510b0422003c00046c3c8584004d07805084558002c111400d80d001c90a03084402210820845500910410b042d5544580c12130700200310540d503d40214014402003807510401303400740d843d00c2c0c45101c4040b42c101f070703207501074012107464010611060340c3c0c6101c0d0003150702c64600010992081d0840400d02081c654000d182c1810074000c90f10409212444070300c000c1d0103ca8000c0d5608007684052080c01c0707200304540d01c080c000740c0c0000c0241c0ca822041800e9030b8880c0c0d6240c8024507885c0d426020a05001e01c00d04030f030b0707030360080304001602007685003155803104201c81c0080130a190042e0800c2c4121641715400903a03001030061854884071104102802c14020802c40c3c18039404c2200070760b08024407034500c001d04111141400180f9410740d0543c00c0d83c2140e0049401520441c411030441c0e0341c0d2114254110380c0100d03440750f4070020841125610 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 164248633 1250 164247383 164247389
    0x7031d07080d14040f061d1009090504021809030408060c040b0703230a0309150e03030a0207150c0806131112190510050a09020306090414030714060a0501080f0a0615 73
    0x345c071071500000c55540101e01049010820040c0c80f100851034000c00c80f08113038a81c0703644000f40f2084028460300000d41d11250300240004d11107007038070175a0b601d0044c0d1580c003250244038075040881e04100c1008104000e64114210222036030610b1b003056404c2c80c0364060080058204410b080305481d86050566401403080700419031159900400d26000e4054602c041c0100d5842c22038070714040e0031140c24032900740b075100d05402440c610748410607130001a402400d41610150b01c000c018514084051165410700746164458100901e4a40c0800440300d44040c8010101130406c56000941c1503180100c92901d420700440c000c558540c011034820300341c5da10140a504510b01000c4c844904075000e8044119241125004030141d22058203a080c0c0c0000d4034856040314900780032800054a910049114090042c00c917030500210b500e41444045442010700c195401100500512a41500445000d8602080182400101e000e40190b0741c404000002d8145560b070768142c180010710709090380c01 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 164249883 1250 164248633 164248649
    0xa02010509121002120f04030f03240305010603030905060708090d0311030d0e100e030405060304080903150405010f0905060402090a020f04091a01021606110106030b07031d07080d1404 81
    0x8641151000340020f40c002c940080605c43e18800090502c0c0c907940340941f107030360305540e42144900045000d5001c2d2610b5850802d1404683d01103c801005000e1044000e60044d0000304d4054034504019000900d241c02841c000c460070000d04000c60015000c40e0585d076010390301003000c01e5050804981d40265032003e490140800100e0f02d20000441e00320072030f0000c1c100251000030310100307024001c82d0048456000e850300280401c0007180351080142da401405201001d19121646000030b0815807144a03040081125100f40424400240f1034443c000c10014000c110034807075622070603036a1000402c0240700381c1c03040000640b104040d80690b640e60b00b1308403440b40c4564076186280c0180a40e18500702c0000f1441d00c10141941c80001c2151601102c0010f05078494113210701207620541d041191503056484e03c0b000000034102100b91840b0f11210b07500011401092030071182d6103002c614003581160f00c00c441c240440c0c80c0c00701e0f0001003d2014140341040c0140182c0384015070140780d100d420 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 164251133 1250 164249883 164249893
    0x6060307080f09070504090510060b19031125150209060d0b0f0603070f020f0307110d0c050a0b0a08100501050a03020702010e030f0a0302060f0f040201052206110c01020f0a0201050912 81
    0x410500082e50810315444035003d100e8ac40d02c0707403070307040950007000e001107402c0e900c03132000440340b0303020760300c0030759110100c411552500380e0358011a01d41982c0301010030000506800103a00388126000d02c00707a140d5421000354908048140060414020000300031110340d518a08948c0d5542d0f60482e142c00c40c038000c0c140035181c1c034190401420f03200d10640c040c00035000ba4200e61410314400710444000b240d00902040d800304c50a0107102c40b031000b04a0486000000030808a10b55545511550040200c070281558500000000410300640909040c03240f5411101c01d02c150782c1c00c501036822005207850b005848100c00c0c00107da6510f0b0500d20b15030140100e03400c03608032840209a00411b107019800b01c400c2916200c81080e80c00d1002c132803066101440320041001584201c006114070160340300c40e4111040c40400d40340a480455000d400410480100c80031058001e00c00700c468004240043e104003400c1c8018030b9151103821a00904110001603180450750310701203a80d1640e005c0314104c0e8 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 164252383 1250 164251133 164251151
    0x2160c09021306110601090c020304080304030506060a0506090d03030b210c03010513030e0108180d020c040c03020f040306020d0e0304090507120603020f04090c12080d0506060307080f09070504 85
    0x10000b54014445104000b01c04180800c02c1406a040111102d40c0703940100700d075a01c0c004040e0000c15608940c0e101f180400c002c0054a104208050800f0394003c001038429402e00004019003105550f104c00d001c3d1009024580d826030710040c4445c1e43c641c15047c081010300c01100092170ba03501e8500142c506120030750340964440000030384802808025402041503441c0d030041c804001040190007000a8200c0d500305003254810340c4410341103681d9040c00203d10031000c83c55406e00d000c0300031100c0142d0020394408824506402000c0d40c640207400c0031482c0c03020820340c40c1c0c450b100e03034040500410740018250b440d083c020b5008001e08010a815603455644480d261000350100341c480c3c2c00003d05c0107501180180c058440e06d01100d038010301a1403841c3e0f05030309000142c11070314020781d024040a01c00190300e040b194400320502d441384071021b550700c4491a03610200e50015100301d029030404d10403c4160b0750010185904001250245003865032040750342468810150030a80d0002d041010b44 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 164253633 1250 164252383 164252399
    0x6220f0f050a1a0a060f1701060e15040807210203061608010e07080f15150a02070f06020a022101091112010c050d0209030a020904051c03090503040902160c 69
    0x180940400e50051100303d1070100040030325542a034589900244000082100d40d006001603035a017481c5040000f07040d60701503580b08410710241d10400200e0b0364506014802c0c6819902154040d0a107001c0c281058102070420b540c5003030034010582d6070800c1f005025410320718101500c000c0c50f4000c049981d40e250515a0300381400d038071510302c0046a244000132a200c0359844132580301c1c1500c0da40e0704000344c4c2d405440141c40003025040c0382c804040b0411102c115140d14040000c0382d0014400c0a690701d0007050300916004450303100454104a000b01841025800319020780040d07011220382c0802c440c9000300520305c0c1400c500a04640d0b00c0c0c42003520810202d00b51008044c0007c27281c9240d801219a4150300742c8000826500025104000d65460b28505034003030010305101504907038900750355502040c901c0b5816070301070b9590f510000c09034405121042c10b000072100d851605000c0240c882d071700c26544e4040d034000c2d541c04940114ae41c0f0150124800031183c0c050b04841c81c0c503c140d54603515 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 164254883 1250 164253633 164253641
    0xc03070f0f06030b010e01030903050c0f010b130b03060106050703111c0e040903121805011d070f0b0703080403030209030a030c0506072a021c03020d0801060806220f0f 74
    0x280e030074080038003400022454041e129404480300c040e15118141541c180045004003a030103022400d201060114490b0524100180071402c0c1e1820000a805100101000390820002c1081e0b007645042c0b91411850b510040b4070981102d000e4100192510b40340c0c50282d81ca9842c14003441d0340c85c810713191040700103007074200c0c0c943e03483c04c4540751180d54881010520041c6d0340440c0c80a000300e0202603200c903000710036902c1601c04c50074405803085840407030355070035007941d550079801000c40c10800c8551801040a004020085c540008900241490540c0251042c014a031000e0240101c1c440040c0a041c0680c048070007000006081d100b803991507160140681e0501c40c4141ea891007000001448140144081044090444100c0705095020900380c40201c0b205441241c00a2880c00031034084480da00c04408001e20a030040d1109409031140203220b04416407002003040007500074017201d0f4841000c105960000700d85141c010001e400c03107074000b41090aa45984407458110f01a2100b100c0e684 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 164256133 1250 164254883 164254889
    0x1721091902130e120a090312140909060a0b0c07030c0504060501020a0b060a0e1906060503130f0c26010507082514030c0a030513020a2d140112090c12050c03070f 71
    0x10303c8008c8084001d1040310b26101c00c080ca414105001c1005421515001c419103a0000c40142a03100c0740c2c2d00e48a4564064001c440c43c03041d664010b840a0081241344071109002d01740c04c0d903082106500c2c2c640002c0d51400640c0c8080d048a5820340030416540f50b00b0108406000c00050040d4541405000800b40c000c50340c24079a0407038a4508041841880b49c2c0403070340200c42c1d2110b6405c00300349680310344940d036100690889504100e2240010b1341154901b500e10b6495900c40100d0700120108070007400e44000912940070000c5006c02c12501045000b180e030480391140180000b44080c41000303443c00d12040105442c200306c04010000c03010301d418010030480308c25a50912698945040b030805c3c40c098060700a5201001503418401c1000da8600701070b070b0001c41224401c1c3c50300d00724020458503803242c1160b2010e80884940d0881940c101d5038080b100c494080003044044101d4940000841c01d07401250f6625900d0b5041c3c40a10408000c03840c4100002000d83e0074042d90b86011280d1504148 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 164257383 1250 164256133 164256143
    0x31306030b0103050411010e010c1203150608061e03010f05010306020307030e06011d040317190605030d170c0d0212060f0118031721091902130e120a0903 68
    0x1c9022035100c2c0c09418001c981c041901801c0b01104001914205c042c411500d04000401d2103990110322800c048542d080d81c241c03800910000000000c0305040200c0e04104c0c280541d00d0180582d580b26007105400000d0b038101c0c0e00080d403904800290241031030380075582030306040c03000100601005900440c016502c83d1000c02501189511482e12000c4c00d1013a248220014050840c2840d401c14009522038806d24141c0c2d2000d900e4610401103800a682d00c000c10310f942e95800e046468580f003240c001d800300714010549500542c4004204400010000380d00c030300680c021901c840c1e440000d035035403a10010010f6490359044008100501300440300c1d0b40c82218007002403101940191141c4140300d0a000344c051501c0d0458507468180d105401e55a1200070040000711050b603c440701410741280060403100d0f8070b003081070100d031a01e54108100700d0810074114450005a81d0207500381b4080a1a00c5c3c04070720000000c0350320341404001000010706a0001130b0900d5265803100f14030046d24420 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 164258633 1250 164257383 164257391
    0x105060118050a0512070302180403020d2a02040e0a0803060414060607060e07030c0e041401020a020c090604111b06070228150e030d0608010e0601030f0303020c03130603 75
    0x440310064041c03040c0c464160030000215061003035082100c2051002c90101040300e0303180f0b503240d02254010310b60809002062070900c00744010164140071030ba1003081c1501d440c149a200c1d441c007041814480794102c01485086054400071034980d60045000544242c080c1c440c404524200804243e108581c030300c4c8074900c2d10310039403c10611940400d0050700003402090130507400c0ea64510060003041c155201c14825007100000140170700090002903d02c44240740e0366424989001c41c080001c454110300c569005201080303101b0390001e02e03440c10f40000c44031210942c40d060042001002262005010514005006d040d801e02030303441124014450000c075541540c0700c500c100e8807602100e950f0412090700a00b18641d02000803c840281401105883e90812964080c1421a8800740c00c4040e079400c0400e4100001407603203c0d90340100a40c82c000d001109101c41400e0720750321705010050541d512046107400b854882c2d0b054a011821a804803551680740302406403885005100f56070000e030070 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 164259883 1250 164258633 164258657
    0x90703020f151608040f260c03032a010207080c07060c02010c020409031101052a0f031602070f090f0609020c06060609030f0307111005211504020c01050601 69
    0x20019100a005002c950028180f80701c0d0a02080b0711068240240c890250520005c00c2c641c140d00310910003448105e403002c41c00c080c004128561010000f511605942007003089200c107460210840e9842080709442600605106c01c010700300402c04d042846041d880805d1400410401d00000c081115418044988207a600c490840b0390600c640c40c020700255483c60444010308041c0c101c0340d2214070908100043c3d43e0f04d6001c07142140c40403182404034429840318031101c0003d441e500b600080e49000900d1410848100c01c525910011b480c44078258400d100000300c1e1403003888928040d29044030000300080c0e95000140c054000c91902074001494a080000d007140300f07208690010b41c508002d007840356102000c010f4603800c18440ca076054080c45817a0482043e00340000c0180a01c110751035102405030341c003440f100f817250300c01100c05c3c0401003000c68810114208861000d02c4d520400e0350407a6220f4504076120146401415006400454443e00c20f020640140c5c3c4240401e070f90303450503940 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 164261133 1250 164259883 164259889
    0xc020109060e0307061b050a030903030b090406061802070308060d020d080f0705060a06081506040f020d14060f0a030f110916140f0a030504020a12030f030b1813020315090703020f 79
    0x406c01c110004500c08000c1c10a0340c9000e60031814805000e802d00040c03002d040c0c40422840e00c6c04450440d40c16582c0c4000340f150705108260740d110300c020f048003141008d07510790f4050302d170b180d010340a64800e0090241d031504541c0c0700c0040b4404154840010743c2ca0700628034171100e00b40c2000740204d84602403440003c20340c091510481e02140c4103a0010301420300d40e01e42c61501e00c03c0c0a819070303030041d4480144000c5020b0b01e00003003c1c03020500400146c040b450802d0302c4c0300a40c0150030184074600c011084003481c1c1d03813070000405994004098880f02c43e010301d03221055001c01038031030750054001400c208601030030a90302c40c86055280c03102d041310003032060341c2452841140c036101003c030703c14450003040074409d500c4241d0103440a80007803001c54959241600c01c515010701100000c6d01c510050071182e03450702801c026810305545450030004c4905c605104034a0003014140f41981c013442c2c102c10b55604001d050019800c2803c11480c6080110009440b05c0d41801305a01400381c07010640b078141 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 164262383 1250 164261133 164261171
    0xd02010903051218010606020313050f010806060c030403050a0804140102070e220206180a0e06030d11102a0203040e070f0207030b13170306030d030c020109060e030706 74
    0x10740c0c0359a60710701d0002c116a2000821202030504499180625840304c0707400024403451000d405a13070021a291200303010714070113101d510740000b0701907003070640b910300143d8001c51000c0d00000102c03a91611034040c207002c03c4c074502840d130000c2e10610400c080c0781c06000103c0f00800550f109020050b0403261048016a650728540c401d070700016034140e00091140705845144a0141300d811603440010070550005403954003c091340d200a480c5005202080b80340c00c2290000409600c0c02c820b0562420500194079980040d824009022001c42c0750496020113001d00800501001802c100c0040f04031a503100b2a00f00b01400c2108009201c40950001e0001059a0880b040c0301004401c03651506012140b400e0b01c0003501041d44994800171000600341841d80e40314a8a04552050703c0f0400e040043c104950395421001c4206c0820510502c0c2e10302140b05120662907040c0414201411107007240103040345030003d00100d00c3c05002410441c1c1c041700a22090740500d1041c024004001c100b2550720b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 164263633 1250 164262383 164262401
    0xd200f1c09050a060209011803210801030f0f4b020d060b0303270901050a03020102030724020a110c060c0a11130f0516050301211509140d0201 63
    0xb65012403000b10010f1100d400910450b2018508801c2c2060b4100700410507031b1041c3c108942107101c036032544030700e0b05091000e4014110302e4903200c03c8030b51550310f03030b0341c050f081c040c41c003400c500c150300002018003480307004a49424002041d64010a41c45528030100300402804001104800c0180c03c4841c81c100e90191300c0054000341094501c8226544110061000c8410540c150009001c40108581980941581c0c0300200440c080010092030800540220503040700c1c6c8500020003040c0003503640081500c0c0305562146040e4008107100d11049010300b44500012442d50002801d0141191720051a1120004040884003610314210800196010b003940c812810380c0b0070070031800807aa0004c8400d15401c800762131070070300c4040350000405484040c07040010329500c41051065040011022148481152405070305650410441555620702d040a0f90034240447c0d5071074003408100c1c003c100b00d070184000108110501c614290140032092190201e0301d0003080003800681d8010b00806c01c038 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 164264883 1250 164263633 164263643
    0x30903030b010815060903010908070309090e0616030507020705060c0705041a032d190b0f0403020705041d0303010905040c0f0612091103060702030309100209060d200f1c09 76
    0x5824071131030500407039421140d0300981c95902c4611080125407260000e11426010355a201841820608004e050714003079202103809038010410003509000583c2040780308250382c54007040ea600c07440800c9281040d0340c0c0006510690004501c0e80c001c0000030503004072007054506201c50f0284045a181c201d03614084c10350945c001c1c656422040c1c03d00003001360791482c062400d03001240c07000035651401019070742c6a4148030040740c03400240081c000c9a141e00c842103000c0341c0510326090b80e009440342040d20034035000310380303401e4210126104000516417426030402240d49941c1e4400a81d4090101620b05607000b1441940c08110304d0401c00c1c0c604282d0b00140c0f81e0407150954589004014203115400703454401e500240d110309a5010700c5900d029485990007035071070f070400100782400d00000341d40500e40c892040040c07500782c0c0c07540c40031b0300d017414480d030b05c00a03880c00f02803504640c000b400401c000c1d40300000030340c250b2481c090354042e14104a6500c2040749020303003011080201c0350300d0080604 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 164266133 1250 164264883 164264911
    0x804020a050d020d2a050939070c0f06020a1208070509030a0b0609160c0b040302030408060109020a0f03020c1b060d0f050a0e0a02010c170f0703030903030b0108 71
    0xc81410200c68510030075101034031000f0501129201c08117042000d0346248103500c08400b030f1904031114104a84054241101e201819041881c0b0300c2c8072800e00c00d12211603048041c140200c00c5802c02e042810b07a564404802076072002e071490508009a80c900401221040f403817004207a86100103041c0080701d0b40040c034400682d41d25502680c000b10001c01401c00c01004000041c40c40d20180301892610748034415010150800740100041e4040040c81d84a015440f003018554443c0d11004a1541c642c000da072402c172a84a904089065108a4001026602c598400022000340f158010141700342c65548511403091041c900b103082c1e00c030f02030001025501800010514040c1f0414030200300030000c101e24640381002072040255500150744041c0306a4131010001480c0b03440c02100e241206240107040c0d0090a640040d0843c04180310140c248201300c400c501042961004454640d8800070851740c0318246460024081c1ca407180c41200001d0800300b0a8215502a003102402104c407504410 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 164267383 1250 164266133 164266139
    0x50c070e07090308090607060c0309050706081b1803010510080609030a09051e040501080102070204050105040b0d2301050c030108100507020c06090411070c050307060f2123070f0804020a 82
    0x2551310340004600307550000c0100b02400c00180c061080d80c55074446501c0103e00307541d10b03040c01420f0141551100c810700507900304205241980c0080e0b4260b410b610920a45c50340842005c0910283daa182c0041d019840d010600445080c100e9130102154000c0d8110341d00c3d9514440100e40703d0150300d80e150003041d009407003807040345449001864800210100d088031410b1480006090750b1007a8420440d603580011313101e007941806c0c052240504016242803000180c0c19011944040c000c140162242c0c840102c240040c140b800c5aa11240340010000e10460030103d42c1401150310071303c2a41800d208002d41c910041c4014019a8801c10740c58001d071581c00c40000130b115040e482840d5540c1d11030340e588204081c000e0110041e0030b4190181401080d07440c1003105042c03401d40140c10170004d0040c1c645c91941801d074440202501c0e1041ca4503500e400c0410001014081c0c881c240c0c508158458081500444a01600409120350110356810034140d051007019140b4040c191000380d00103184003014 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 164268633 1250 164267383 164267393
    0x30c0b070221030903010f06051003020c06070806181e16083607030203070506030c090402071401020307030b0301060f08070b0a090e100816060c060911030d050c070e070903 76
    0x862a40b2a80d090300e240880190009007100d9140c0c135070140096880305d00384614103001a0424100d9400c0c10110f141150503a5500c0d61501d000304604100104400041c0294881103086451424401190b007154203049600303880c040d42c0101c40740788d600801000224501c80121411011100360788035240e4986440444660f0712910042d2020340c0298224103019400c1e9405c4041c5c07012009101410742981544109401c240340c542c045403181005100f803010100d545412030303041d2032080317500603981c001c145410f0000c41050003c4003010351012007040f0440e90143c20401d02e0140407002000042d85400000c000784805005204e103e60107a0320a11640711003200802210102e810040c130a540d41d80c1414582110031502041c0035652a01d0810003038004001c0261248030402a0004290415038018009403c100c1c0280c001a113400c5800d080c404010159925a80c0c054280c0d004924800d0015007140d0201520524a08c510140020096116910b10b0b004510550300c0590306c40c596110 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 164269883 1250 164268633 164268679
    0xc03040b06010e030118030201060e090d170702012a0e0411040905131209030c0e0105060340110405010509060d030e0604030c0e0a0911011412010f030c0b0702 70
    0x50740d019946d400307103802999400f12101c0300c510b01c21390000c104203003010146468183c1c01303006d8040300d6102d45940e0048a03000080c40000507030099440c0440c0e5203950040f4090b104c010300a00c03113240251b001d01c1c54500210925000345c80a503c0710980e0390190420b00c42100d00c42104004180001e11003400100f6160f04041c1e00000306c624a01041c0485071109184400324940c0100411900d40b8100100800d1a022100810007114078106941c500310115401c1d120080015007044e85038640800540c2100c094040021045d170b0300e440725a410042c1c4240c170040b0719002a281080d1903144032107146841c3c01118180d400281c40c030902900c51409124460510540880038806040314003900c5803504409032000314060501030800a107800d04000c40b8010292030928050309001740100401c60189000c200c0703e0080c40d02c0710204409066017a014010750f0101840e241071200009001d41b407e50380c1e103056a005840d003499640d07440c0340ca00740b54407070400002e40140320b08014806c2100681c030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 164271133 1250 164269883 164269907
    0x250e090610090923090606030f0312130204021e0408010e0f0a02060313140102120718050111190602040e060102070e06060d02040e1819150b01020102040f0303050702090c03040b0601 80
    0x40c00c00440c0350b00350811340e6000c100d0700b034192684030b54100b1003a49403c000c02088114218051450202c500c80055581c4400902c0550300851401c2c0c108119103955040781e0101004180001ca03500081603241941d9000d449204199800c04a510803d4180420401c3c41c080300f039001016909019400c0c40100e0304024000702960300c12144034400301c0d1b01401c0003d20000c0c00d400050303841c80c0031000002d8040000d04240704102c140d0341c007880100710f40d0260400340c071400d0900b1654682400000e80c9820b08505c48002264081d1005104111540e0050400d0740e103400c0c0340810076a180c3d0012070ba40c00042c1700345a1742c24140d40202d500340c1000d00041c9034480b079800001d441c05490b0020020380709401e440e082c810501c400391a80b0018400c0c80070301d100001d0f031041d400c800070150715640003c009030a550044240d0702c40094205a000754100c0f001080b03415200141280d6034100909a5008043c01b6405220303283c00040c5080c142c05c048038411980714401604a8443d18011510021260 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 164272383 1250 164271133 164271161
    0x1180f050d060b0a150305010f0602030306120102090d0302100c080c07061e0c0507060605060f0a0503090f1e010c050a0504090b030c04060f06021902010215250e0906100909 76
    0x8a40e18003d030300c40400c2e29000d0111407250614014188100408542c4140c0c0070f0b01c1440010305080c1f007541d5011048a401035000c690b480712a4000801460091007540c0030640d000c00ba01c05034000305500450880f1109004002c00c02800220400075124610b08039070000400104000f640000b50540d0302c01c03056640c5101d84483c81c0341d400e0510508036400c60616071301050b00424204100080c60081c0400352100fa200182041c01c00c10300113003640913804050080c0b003070100014910341020001c09a9007802a811504000310400b841c0c014104140c2c0f181540d1350928100940d0749000d00e049541d50080c42c0e407141e00d02845c0c0302100d0010500114401d5040c0100065040165240d00888000d0111200e50704681d130302c0c0250103480c0221291031200c0b40d022001c0346001503a0045600014022040712507070340365481401c3d0800303480c2e01d03401020720341c2000d60300f10310202d81c00540c2641d00102a2184840b90316017400300700d42c04114010700300000300040410b100c0c03007915410001c0c90035000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 164273633 1250 164272383 164272391
    0x604020d03031b051804090206040504020f0702061827010303110c10030e0d0c080702060715090302031b030c2802060c061e0408070b0705160b0601180f050d06 70
    0x183d189020788828610081d00050002c0740c40420311040c943d8030b0b2641c603021103080160310401e5002c28064042c3c2c1c41203620540c2d02080c0c490488111100312040703581e0007000c096448c2d0b1400504d4076001a10060780340514000710860820b010044040d00120b0041c4070300e003171541c0c44c6560440e0101d8403100d440106009100062005459900c0701c2d01d5840c0c40b035180841d900140100752803411102c2020311080011480c8904003141140045442c2e0580580303401780c0c0d4059504001c0ba4108080040940c002d1401501c50141035000c0090500c18002400f03d449000b207501d401540c034003d5148511064111107098444201ea803140d55131440701411030300004d42c8030350700040c00700e030072522125042d500454100070070780e020783e0444044030780e8200d41c05025040a4407803101754060000001c0855071000c000c20205d9015000380d0b000b40d4000b80c203c0d40200c03803030301c1c0c4108501c0702603c00c0c90101d428552603c240d0300300c00f00b890044d907103490203180c21702e0700c2d10702000401c0380f640f807045e1242507076 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 164274883 1250 164273633 164273651
    0xf0608060f040311190f080f030c0301030c1a0904090c0503030c03031006090b0a0e010504091109010e060a05121906080d0e0a03080a0305190204091e0504050604020d0303 75
    0x2050002500c124103180d80d100e0a49080d05001e45002071a04031850981c020700341c41e14603c41d80383e10007603030103810036921010b103c49854462502d2046005540e448440030080240c1920a44002d6040e20f00c0340201c80690703545c0e902c806e02c0700072200084000c000d1080c046542c07142015840302d654103029840c120780043d03540307002c80e045510203c01c00500790000070400c461000c034510300314014a003920b844409949800401c12483c01500320340c4082241075503071a08a43c1c0b080d4280d901501d640319080088900036110150141e00c201d4255020a0341c081c010900c0e86000400d584a14a840d19034034900202c810030980c00c240010040204207411541c14040c00205200300c0d000360000400400246c03004c04805065940007140152003451030b1038040c0f0003e4100d100b92183c00e849400c0100385d984500c0301942c07495001c100e5a030749652021500040c0f0107581d1700000c1413080c41120340c80c0b900121601d000f040e69002c484c0600305500c00000305005003000401240c009000745400107078000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 164276133 1250 164274883 164274899
    0x1b030103110d060902040513020a140319060f0f0e0d08040c1503020c01020a05130f0f03060c0e030109051b01090e2205030703080403110616050309070b031e090708070302040f06 78
    0x81c11381d21484064140d048c84021420101c2860002d0124404000c604d415030b03200003503031030f4503d0400308a0300390f400c90001c04108040d04095004c400600307050002d10420001c03c401002240615951803003150340304c011150085650500803078000075128015820002046a24000341c5080c4040543c200f000c20340c164020b1010309240046a508d407540d880040b11041e88448140c1c00c032001d41c500400f030402c19195120540c60407283d109a0101c0e60140e45035007510744213000e600003a0035508200e8400700700f1030046156405502248004060f40e2020401180c10f0369082c010184000c05601c08941240260b0310302c0c0c1c2c0f807000c00446209009020b1b5031154110780040c18110f001c44c5030380d010300c002c054028104406175060031004040918003008410a07600003200101c092001c00000b09400394030521008000d088144c4000d607580c280811404030035001c0415410401d464807012841c0c8078004641d400864122600404045007076800300401031216500c0c9003409c955485001441c54 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 164277383 1250 164276133 164276141
    0xe0a080301032001020615130905190501050a06080c040902061b010204081203241903081201080a0503040e070507020904030c02041401050321041d1b030103110d06090204 75
    0x140300e103080c1c0701582050842032101d091a0f84259041d904110304204100c480300c007500c0888502254402c50300c0200b100b41000425440750041d00c0c40c00b80050361400002a0b1100000c1244120020406603684400d210b086038000d0007403007034640021207003600515094100d40040c0d0300041040b03140551240c903242508000240f407143c1d41c3d4011500704050f00741407107100d07104441040010b00d0340c98582880070300c0030b01d00c084c4198420150102c2da1078507111241ca404c40e02d01207005914500317403603041c4040550010f140708000041888000f040740b1802050080160380d01500440c00c25090610304d01d10500010901c100f0010300b40b00d0000581d07a00004207006900a0f254014008914014030066441c0510b101c50640302810040001e03441c0060044003022912000580e00361072276088189600c91a800b1041c18040641c8407010300d2180000b0707a020f400c000d41000d0000070250701d115050b001c2480701501840c120020013800342041000301306a1807103490002a074241c0d50340011304031 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 164278633 1250 164277383 164277389
    0x4050403120c0903020a0308070c1809020405010b09090c0c010906060909110f06041a0f0c0c030f0a0305030703021b07060f12060e070318140604030f051801030e0a080301 75
    0xa040c0e82545a40c0240300c0c03084864402c22454040300b214115004210f00d5101d620008200ca00000b03650001d101d405910075020741390214096980c1c0d260b812032140078040712082a403082d072a00300001520054001201d058440242141415580d81010000181c200b00f0311301e6019500c810072503001600910030613004d41a8401d00042c0380d8450f08042c80c403501d181680e980118201d44044005690300e0f400d590880d501034801151241002d448401c083c0580d41214081c00004202d50318102d101081030545030300b0035022603420307208148156136a0356042c2c0015005c200c00300017240718584660000c1c0001d6024030360080380703030ba4050402880c040b1554010740002c0d1254441842c125130090801c21083c0302c48001f44140c5003403400061902c2b074082d10301e07000c2c59503402c202c3c0031920912a6a100e800c0d00496841001954010707003944540c8211011030000705810140003440e40268251159501c0d40d181007020030017003030015001060000150b07400ea1180c0040040000c0d800801103003e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 164279883 1250 164278633 164278637
    0x31b0307051801030203090a0b13140703030806010206070c0f02220e0105150a05090604060806070e030114090a110a090c0302070c14010f0c1704080c010207080d0e0103051504050403 80
    0x6602401c10034030301c0340b6080380042410180100180401c40e2000507204070420b81219510f840741e1030b00754142c44900d150308030003004890041020500410301240d100c0c11a80207495050160b40d94000480e1202d0081302c0c0f12001c15500071640c00804c6500200b210740510203400000c0c142d060703848140710f0b081320340c1a01d01c0880d2907104142c80c8500c00e004060304454007404002030380c1d468200241c1d000d0741d1401150f000d10301c010700150540d55141c00180c024003821040e241a41840b01004060102d006807050003582007101c500d691400c4c1d01031042c410340c50813001d410040401e0382d852800c99580c07800e00e076010400c24000b080d1600741d4420030314101080e0304c00695500c0b080c90310000180700b0380d1003040000d02104020035140d0700044090b11f100007600d04485501e0482c44d281c400c0c0c543d1580340c030b00387c40790120300440c0960b000101444068026000ca8900706e44e20201d499a800035015618000784e00a42400c0855019400c445d4204c10700104851650440308040f1301280d80403202900 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 164281133 1250 164279883 164279887
    0xf0d0903020f0f0d030e010f060f030c0501080c030402060702010c08180a0e0103030509012109030f170c09130b04110a090f060504180b100801050a0503070e070302031b030705 77
    0x10160100201d014402d4802c000e0140382161224198036107000c0300f060000e241e00e507140e2880b811030a6018401070303a01c46d401002182c5e101c0710040e40c2046680030480d40030310140d801142d1980281400e600c240052800d240c616503540d42400802d0300300002c22414803640d040814001000e5101400395181810340300e0100152490030000c40c40d255501400d500f0482c0c00051000c80d504c80201d0369924400c0c04c0c2402010188542c1a8002105001000348039103008000400c02d54818071b04a515405030fa285940c4441d4198500d407129000c0c3c0f1800e4120030100082106400d082035580510704074a00b0000780816440c0108003a1140c44a80051582c00080e100401070380010b41e0b01c0c00b526a10f54400001030030600060410701ca0341c02203041c040e0b1600e01c01c2c01445013940088109002c060f10f0f402c00707e2042030000c1d10128082c068580308002242d80421319040000ba10003c8800303640300c02c4895258960203030003d500241c90354007002068600c201d00300314220000c40c000c5860f0b41d1034603 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 164282383 1250 164281133 164281151
    0xb0a0b01020106051206010e090f0a06020a031b0f1d030102130510020a0309053d020118020105070609050f03120f0109050903031803041205010608010e03040e0a0e030f0d 75
    0x80c01c482160b0803503417003096140c8410040c4440016079038103561300541e150413141c9401143c50b00e0529074a0f0803480600c180340842040040903000f6001c1d030204c5032000d0205040342c1003491940358800d1518000604440144e2105501c602015032600382c42c4d406080c824100c2201003801d81c0d01a0b0350f016440720707811008100a00b4806800d98038503000384042c11059100350340c000e15900c41d07407255502c40c1d810301c100361000c11410911000d50300a07100b00c5040045035132941940c0b1545e52030200004d54a000d0070b40000a01c6000c41a20080c0d05a4a423498001d00342e98000c02031840eaa025030f541d22800090034800c03001040102004815000031605a282010280c0c00030748050b0041281c442c240401c0c0099903c00105603900030035204050078800025600d02460360040c1c2e4042000181064840020f02c2010b40c89a020b6074801002444181c80a8540395903034440ea204074440d40c0801c0e00069100135155201d0f084210305801900d04d08500e03448001c06035003051542015480e6508814 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 164283633 1250 164282383 164282387
    0x12090a0906030503030a020304110409030818010618091a0c0301030b100e010306180b070908011409070302011125050423070507060e06090d08010603050108030703050c01090b0a0b01 80
    0x2000e2040d8140001400c640e00c03030f81c0701e01002d4506189030f41c0110205003084900b04c00c0c0c0400880107002045030580301d06004026900c02d5804009028106120400e07c02040c01740ca401e5507000c1c50005120841064001c000709652601981e610342d402d4900382c502c1441c0d403155400381c212450b0b942d480c1e50460800c41c2c3e000c14041c26029503d0401a0f04201c3c40002d00201c41c116500480001905c03000d1000410f00c03010f00b5140141000d01400401c04095081981032068800e040c2c003c100718500260340d0381d890081a40c520200350b001c140c0030030056100711039013404403e40509032420516580d0300d09540303d692520240050340c1d56070082c00039040900c5803090744a1124000044081200c000d01504400a0081010810009101018080d468001c9001c45004c6000c861080c54159111501c9200d4211b1741c0000920690001982d030f0310900a26042e107054074041e41c80d2101540d0140d46962010b01e0300c65265480c1c0540c400411611008103111704060b080120f0340120540c00 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 164284883 1250 164283633 164283649
    0x4080a08070c050a02130207020907020714040e070e0603030d0e0105060f0f010f0521040503031f0b0a12060e150301151212090e0403030b01030b0d0b041b081209 71
    0x10160030021078042d001c001c2400001e942056607019070f0051410361101040300083d01c50074202039049645c550501406035030014071071048030740c90298240134203003060400059480c80b03070320100c00342d001003070034051444031021940d00104020f084074581140010300c00c080d01e010385280390300740c3d550303030700704011410241407400b001381c02220180901070892001230f10740d8000d500300f1002c0003404120620800340100e00d02e045900d448a4a02c418601803401642d2503201300c8844040e00040c3d81001c0c0c41c000c04141010548052244090420040d0b100443d0741e102c2c0030b41c1030590380d51200c1000448641c032140c40340c010550000e1600101940300107042c00c1d105115101c0305814081c0c0010000c0c4c0d08601c141154462340b21030401c1d019503a4038800c46000d101034108418420700341051101701030b090340c0301912507030003a2411700107034031450100491208090000b4054100c0400010f000460b00c007d45030080b9001c600d0740e003001d03489141c903a2030321540440180740c0c8400000c0c6044a03207801c540f = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 164286133 1250 164284883 164284891
    0x1109310902101418121902180f0f130c060c030305090309010906140d06120c060503130201050706150b0d0b0306060d12270e09060420010207090504080a08 68
    0x410f40308924041d00d50045601c549402d00c40d00e02858080c0035195a10034407000d103846100022a41c00c0007044103c03001049851104903c112000845041070020008000b0b02c151001d030302c808400e9440603189080c5800c01001c00c145410721600b03c0000601213080c4c0070180a00e5501d1203440d4590380b4024044800c0601180301c958814801e1181503a4010000019a2000d1910b464400c05580440f03100740103c102c040da51604181021a06559105400c4a07841c0038551010901d1341c1c604040c2c2312071000303590344108006814501c8000d94040d00c004c0c5150352040d080014226031402e0203805060060b00452112003000505804890003801065000360084001d400103040c4400041d41c0001c2c200c03c02814401080d030751107c43c41c01410f000c0518450076240120380c0079021070b60f5030210780d14040e401141e80c0803400300d440304900103003c030710640e8003009042d0390403144d484412010418446150441c03103040d4000c5818125400b48901aa114085844d00e41e4030400000d041084010 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 164287383 1250 164286133 164286137
    0x60f0306010e190f0c1e080108070e0411030f0c0f031f1e0603050102040509070c1113060506120106090b030405060a0b06070204090f0506060103110931090210 70
    0x300184250350041c009143c01c052960300c090319500d035194044014082c40d1482c0741c903092914524000311500b051003981040701210ba5880121000401651703800028058100e20f6400700c107042c00b559060340304d4550482e00400e22514030b02c0e07020300001d141c22010501c40210760000070324900b25003040300f444000e400e07088010308980070502d0b44820940d88620380c0c0b1030520b03840780340d502c010042001c4540c1006017003110074004075880f410424041e6000d8030665008291000000340102e00ca03c000042701540900d1184220b00400d04110142454020b4000c3c0580d542d040001e10340c0c0c0e0b010090001001d202c0400c15a9850b1010141c449440c42d8025402e2001c10401c100004e100031500c0e591081a03280c0008042e1150f40201d41c00c0d0207405002504507140c0b0391100c040c494528002c421035031040342110328540c0ea03100110107485c5005c16940c244103060004030100d161200c190f2011b00303045000a100301103010052881483c01c1c80130700c4a120303900ca0b070a9056007000c002d00180c0704154 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 164288633 1250 164287383 164287393
    0x207050a0b041a0306060909040b040b15030c010c0c0f0303080a0c140f0a020106030c090e1c0906050c010b041112150901031410020a020d090f08030720030a0b060f03 73
    0xd000ca0342d0094002c40411008034000000f40103580e4040c10780b07207d00c1c400b41001c00d4514091030718000e40d907001c0e10305540580c00c6074002400e1031100010141101c0e405006881c91408500040d90120300c9244100c821007280c0c080420900f4659440000450083c0d845501c1410480f0041d01200c4d40fa008041c200013085001c1700c03a14420750110f91028904000040e5110260b6104178010701743c03a0401003000b0300240300003031103c10580142020441c0310017170300c6103583c600784141180f04c43d40d40000003140d4280f504009850183d006001e50305108000424040114000a03040701c800e007441643c20400840c503c81c2003040300240c26840900d002d03a000c880d00c40c0390002032414805103c02860050340441411030300800380102c1e11040441c10040d0f495090596010b034458800c0c42c5a1000169002070000304c1480500c1c9840031540301501a51802e20581c495a00d41d011903121502d01a201c0c02140c42e035038408001503620f182c0a12280d0301d10b82040000c00c5a43c010680010b403180c1d00c1 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 164289883 1250 164288633 164288639
    0xf0303130612140106110609010b030706140f04060306150c02090406090501020c10050915100306050c0c03040909111e09070224040209010f061e110a030207050a0b04 73
    0xd1840040107650380d070304000105801002c00c5001400f084840c2589401d454800060301580025452400003501c00544500b03640c0c10780c01a0885100c100003607410b522a00e0108141401800d414070581c015551301c51400c5e400044840007940542c0c881d0700001c0e40c68504020038115201a849100480e00e420032546005400282c1c07130401c050405800d26176542180380800000350b04071a060a03d040989084030018941c0000805040340c0c8901c65010f19851f00c1621062280c0c80c130300c500d18110400c2c008600355101c1c5d90007089c004010000c100b004000d101c2500d10200058030051540003c04110240c581c07401c1d200c030348588484c03540107442c0c0c2640c007440080c3d01034004200d2042a50301030100d65401400700e141951800030440501d1008a480e40080d00c0c05c40194482c2e8000e641e40e00c442c2e42c1e90b00c6070703000412480c8682000034500d01040e0041c050081203400f001e0b103103494803a5012103080902420141c0140f001c0f00540d211040800140c240798603200c006080b03440c0c8090416107 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 164291133 1250 164289883 164289907
    0x30111040602070b0a11010f0b1207050d110109080313060f0c110904080d020705100c020a0201200c09010b0307091e06031e050702030c1614010e030f0303090c0f0303 73
    0x2050303010310980404049005454580700f03104141010286c81c000307000603000354807107000078504503070003c0c0a50285208904113820000c0c031b06c02194005825082854a02c0c0ca40990a10b0840d59980c1000354506000410300001c1018081d01c0d080701103182e114901e00000036001d00030310315005041c0701c02034624601250329002c669403400c00c00e803040d01907a6102d192907411072240c5400300100310f101141c000c0c10701c00005400040002d0a4408101460003181d099903500c00140303000307000a08005000d03805011811030030125000703003022107001d003103190000341d080e500036005500104030102c00c02110b01d170b00c40f003404020401c10380d14401500300107043d0080b0221318041d40c02807580711114a81c1c5901c440349041c05445034000100014200100b00a49981c40960403a8192098000984940407611201c030121049000380c04050580640199003030200000315a0341405a81540c000d00f6100f40000c0d03104501030809059040044010001418250000d560080e4420700141c40842 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 164292383 1250 164291133 164291143
    0x1e010506040b0a12060b0406080f010e030721051e0d1b0203180d080a03090506010f05130b0d06050103050d121109060309030d09030305010f0509041212150e06030111040602 76
    0x1404c4400321000d40d00350342801c40150840c440d8103a002880d09900041e5130300c011800d910035044500081c0446400042c0c031a680c0d004e080d102404c4007207940c04468011066000803500d80c5a2070810a044c4001d00507880481d600b5001c00007070660001503d52a081918844c84415500e07a400a4240c0104204004d40d2400307551019610b10580310260140f540d24110005050ba51100d020b0f59201051140107001c3c0c110300c00120352a204032000032840e4442c040010b41564030240010411b0846007132130401509000900d21b0304010409041000b00d4494090140030303502800003461303045401d2a00412040d072066860031658902046001d0004106085600c080f40c21100d103520394585913000d50a41c0300e0404c02007080e9103031008a400b010742540280b41203880384801c0041c103031b03510f01c02d025034520200c0f0f00402190980080302003c602034140304c901c00c0740c40040054004004502c000d0344016541202068201c1c00d02004103500d824098980d01e411000b40c43d81c10075107009400381da90 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 164293633 1250 164292383 164292389
    0x307020a06050717040510050601050705100f06051906020606060f03040b0601020c060a112a090c04050406031103010e0d1d01120c0509030106050a050d0b090307051e010506040b0a 79
    0x5140c03600301044821303104102500d81c001d08408095080d041601e4169039401d01505e03401541c07030401e4002002580681309540c640358119000e04581541c0d044600000c210010040059940d20300300810a42c4805903c581c0a121040b0070840d46400d0442c040d01c0c01c0b43c001e1409210720342c200940300002c00e202040c1c3e900258001445641c9454980c0140c2c24501d000502a810038008980040c40f070343e2004144109444100035202c07400750100082d80e4007122031002c86012a8006a42ea1007402c20b02c2890354800c81d03400c55203060940319000201550702c60347c0261029405550112220718082c840c505040d01881d004011903028640301401c0541e03107864400071100009402c8120b40d01443c03030078859024902c2c040118080081c0068080d41116110380c1c00396103002800302d101c1c108580140244c0710300804010000c021a0b0302c1c1031b60420018125500e40c001809444005103040014010300c5225005100c00355040b070808030300b10b420041006200e81d042c0551000c860312864a04019 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 164294883 1250 164293633 164293643
    0x109031401020408032206050304030f0503061504060203120f0f13060902031509100e0c150405100c02150a0e0402091207141003050c03012112090e0106050307020a 72
    0x6540180c0c00068024011a4840034050000150010807a1304505d040d0441d114040c40c19600507031a8241121a40000c56000b008502a00030041d034040c00343e8040e56004a004100e208070010a000340c1035150081d44c0406c0c0581e0011604a0360345111201583e0301080a410003003480c944510200b455600280c02101c1c81c2c00ca400701c550904c0b960f82c02c0954102e4000d4101c40c2da00b061103000c0e8070042d0049034942540e005045101c404100140a81201541910028808151288100001550f4030341140f0700c1c280307013000002026101c070a0400703205d06031500c46005c10354090050003030503048082001c050007400c01c15900550303004020340305041c0e02660010f1701e070084030011407525290308400d50300c2d134400c000380064948043c0c080060a0103056846010000c074a040a90035a6000d440e440315242040c401480750440c0366a1042860614252806019910340c9884220121100c501800103040c00000d2081c01000314019006021506d0414039500e0708402c001c2d00d0310214407004007 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 164296133 1250 164294883 164294903
    0xf0d0503040219030b040309210b0907050315010501020d090b030c0304080c1902100215040b1f08030301090b1215060a0f060e03060601030501050109030f1b08030d0f0506010903 78
    0x82d900e41c000c50804180b040d41c40d6995050b00d82c01c0425490400315001c07000580c1070400403901d41e01e00e18920561a80d52100d0302074588941d542d03507054280007015000d25200d00c500000d0140c1d410055040e0f07540b0000d0744022294101800281400201c404030424024583c1081040040340c50440703910081280e0705070f4032038440d440c00503141d115036140100d042c03060745800452200305031070f440f1003030380300f20350141c04110000c0313050342c568a8111040d080e00e40c241c0001008a06410300340c560086c1160003040441c2c0070203803e00075540e2640c10180041d1b00110041c049242c00d4818560a0581196411071903401032408a5940c98541d083c4240c000810b03011602c85c0c1c4850000001a00002c10340d0740c0242d4440100030640f0301c04240152080c800c1001017159175002e0b00c240c1b130507a28107030746003000e40307085407140020700001d000101c5442a03680c204803401052003400d034025140b401301869543c030b00782c5131301810303a204020001011490310b01840040e07038002d041da900303c82c1e0107981c02d0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 164297383 1250 164296133 164296141
    0xe1305180d05040303180308121905010b042102190806130819030603080a0201020a031d1905030c0a0f02100e030d0e04090f0c0503060906011505030a0b0a060513080f0d0503 76
    0x40301d5103160700c0103003a00000b046088105141800c0140302b88144ac003003042d05403ca407030b46010343d034080c810f0041080040009000f0407021941c0460604695220540d500100754013045072508100c034208100c0b00b0346501800301c5002400758641280002650200c0c5c14038644820210b40305024218804a1440030500410b0b8065003100d0010764000051030384401804c40040e020f54001c6100c000007910306054001c020380c04c1a005541400040010007142c801c10b506062101a5072506440901c03045c442580d0b5601c040000140e540d1061258103840c0c2500c3c03050204041c1050144014003210040c0c1a41c140c40000c2c00e205425000c0c80c0c0402102400408a0f000307010054000e041c030032442d42c1080c10320905980e4481214010390494a0703641e40c0c020f40702c4d10352400303000f0400044000c9405140c4540304401031a08255032400c001010500700300000da402d0301c6a80407401145011801400303c019000c000802488500301030304426041300000c64841614103461414004044003003 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 164298633 1250 164297383 164297417
    0xa05010309020d050703060e0d090b0409020304150e010b0103110702030c13091a10080601030b060603040606090c0315050103090803060904170c0c0f060a0503040b070e1305180d05040303 82
    0x1202c415085001c0d1410700c1e4036800c218015040c8c82c180c03006284611000301000d40c0c4101d5081e01111542c180300703801c09050204c0e4034060741c0090000d1b501803400b0035000019406500c00d03070f00584401c0c0000104103510000240a580038900c02c1200c6850501c11300c000341e20040382c80d101614040f240807030701219140055009090000c0c0c003501e1a089002c105804450540d00c2d14012540b003040302c5035050741c40c800f050b074501c02408000d04064980c00440c20f1824400080d6070000c1c403541001c1a071030384071802030b400c607030301d85200b1070000e82c9500786400c4c0b014107680c641014001c00e00c0d00344502c0d001074980c400144005031495004400f5807000506001c010a00c2005244070706842c80c0d035640520f841c0c1542e07801c0600740144941d1031010b10b9900b51601004a900c030465948409003180c0c7c0e1901d80c000c680000034145ca081c8002d91001c0d0791555910300c0d40c030f110030126010005060803c0e03090b200c409a542c00d502a0b035a40718440044140f03401c44107403021070350306140c5086001c00c1030030f02c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 164299883 1250 164298633 164298649
    0xb0a0309021201020a0c0b06090108150603150906040b010e01061d040e0a21020d0e041e0c030915020307050735040e0907051f090e0130020a0501030902 67
    0x1d030310b4880d4404102c10686650240117082c0070b60046201110325150340d02000b140354002c0c40365114652251401100f80315203440c10071750101c4000c0035554420504449070390801801c469000301600410701b00400c11500c1420b40d4050705040d54071150a60402c00060603454403000d13204070070001c002c903034812503643e5044290400746000903074040b8a034038030b0031622410082d903403d50b5401d502414003024910001d0088600401070b035070802c4411455003030100400c10940c46005c2c80c00540d003000900201070041c3c0e41140e010b0b6038001418209803d0480142c08514007070801240104180b010b0340ea80319040d03d002c5500b224042054a001c01403001d0803254404081c0110a00748280c540c801c01c012001e40121000c2c1d02d11480070790b0f102c044131500d5520f03900545e0b40c44104058a005c002d24020400306440c9842d003051490103886400090f0b040b84241d00100744200301c860003803607561000032804003480541c038110740640d000e68002056005140180360400d0b90701e2000005640c1e607081 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 164301133 1250 164299883 164299909
    0x12040819111504170106060f0e09040f0503070b0723040b0a08090304181d010b1f0e0909010606030c18090c0507080c010c020601060509150309030408150109060905010b0a030902 78
    0x180c030004495104940034086c14442c483d48000c508042e100008080c0505448941060b00a00e00e0b44075588580e030b034850403015043c1c256a2488140306920010300703061203003801405240c0300d00c40c00035034641221141c440080c0c0380703410030f100078017042180000316400d030f5568281509002084c0e41e5804c501c949140103a80c0110754a10b41c10380000107081c0f00340e00802501c0c18001300b200000195112040c2603c0700540d105030450080080d0802e942c10078034441c080c2690500e84140c0000c0d0050000f0620741c000c0e02e1004490b5914002002086e40610030301c485290281000c0250340a803c00c80c00d00460315115038650251a0041c6c1040701d03204404442011354460320f296103c0081c4600e503030082900300d035050050300c00c4500205030396000314140e5003c190014403203400000010020b01c0c043d00050481081e40c841408085455001400203180c41e0845007213401c042e41c5000e07100c0044d2006070344000042071038000140300204c4000c048814245140c1408144400e586c400300c2c0c0c080c41c0c088 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 164302383 1250 164301133 164301149
    0x9020d090506010902030403081e0610020709060b0c101b05091306062705060a0c0224250c14010c0c12021f0801121412040819111504 59
    0x800003181308070b40da80c040c502842c0642e0f02e00c801c0741d5074000d510000d8030980c83c0e08160300d00d15000040350307440c28407070030f07148100c0307074070668030502c1c2d032003e5075415124140c0040e206020080340794443c0c00020000686130236030041c3c2c1070020324030100004000c0340c0418240010406d001031a0141c80d207900c08100040a410311003000529aa01c1b00100041551841011107840c0d1001c13640c082c548480c034070340c180c4000810080c54a500c0090969084800c40d4040760820008078a00c09030020b055590a4a20703400365619a03106a0305403a070079280d420500d142c403900d40c841c0a8001044111a188042c0d07000c600044402a80c040d005a540400b20710004107040410000440c10307044030300700d54040301d20036102d6200140c1644d09005446000c02d522000040007080104408100341000c14921801040c0a0680e2024200c04e9030500940c0440100400d0340007c040003401070030000c0c607412145070950805040750301e95407020320305410346019216441c22100c981e4400220011203006040700 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 164303633 1250 164302383 164302393
    0x6070f0c0f0501031d031c0b100201020306090f04030f050c0102090a060f1b020d080901050714030306011e081b13030c080120040b07060f090b0615040b030109020d0905 74
    0x2070207210351148070354003440b07001a0030140c07050701c05000813006080405501020f14200588050049402c03206684040004c40e26a28030f82550703111030015a4665100394009a66442d146090100310300000c1c028411103803464080001107540718085a0481d0598a0095590242444801d02a00425130165807202001200203202c0d60410803000107649503031514514a81f08440c503000304660050040d4200c0041d10700500054610b10050012540c141030060030103206446122450707000d108040380703950001047c800386680180000a400d0700320141c034444910503640042c00d40c60041e00030868001c400154004001c0d403681179038010702c5100d00341f004659890600394511051440742d0241d42d46803410f01c501e110082e604a5140c2c80500109520301031600500e25110350201c1d4054030515556409401c030010030b4001c091100740908050740140c02c0138402c000c07441100140104168400f084100000980c020030341703044510b60000140c5036102541c204000d0203450400511600031 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 164304883 1250 164303633 164303639
    0x2f030c091008010e0a0c0c080f040b04030b0604050f04050a230f010501090506010212120702030409140f0105031b01030e0a020402040b190905301e0c060306010e06070f0c 75
    0xb0003502c1c141281d03480c803140b0540d17846000c0744008a42c0180b54034000a20004201400300305c12000409562170040709052030903a45542041e115003198004139a29420b8000340038540c5058000c070b9400803200b40302060241065914540d8410b41164014054109400e8880d49000076122841d11840c13900f00360f8801940440c45030b802040240518850a4508000704409502c0010300d15550400710b559540b4081c88040701c2c10f40448024186411071004000205041c5440d02955040c498021115000d5007404082c40803031b00c105811850281d8489160540d80c02c12024401c03030f00e03e4080c01e00140d80e155158246042817030b42940607400c140001030001380102036000611912100b90800f8012509904040300e1902c0c16105040d070100a60b1601d038030f9a08100440e0312180440900d4a41501c81e801c041070034201c1c04100307282c40890000846441450a10804500d01c4003211700c0c601c0c51400c200003074504030800300014007079900401d00d001046030705400da0b86840c1d00421560f4843d96 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 164306133 1250 164304883 164304887
    0xa06081504051f090c080714040801020409021b0619020d0603020301050405030c150402010206041119061e080903032d01120c2705150604080304092f030c0910 70
    0xf046160030020030310002c03400130741d840c030320703c00c48080400b103a4924465803284201194040c04191117152608410800051350000900c014001007a10401c00740e200c021140c10380447c1e018407001d10905030404405c2002c560749600c0c0ba901840c0c091040140c44d41d206841040041c112034000941642c40c14040c4006c1c8440007011f40340120781c80c4215231401011910001c3d1185068400a000d0b0303000c07801080000b0110903c2c244c5c01a8040c01c0f1800c04480c51880001018031903002c0f00202d4032040101c100701802c503001a00a500c5420298001c1c1440304000ea9248002085051003d00c40c0010f03d00c03100c203402c03e80014240c03000d043d520300c0d40c41d9200102c40404603542150501700c0138500003040082000b840d05030803458039000c0550003038521030078080c0c03000420035000c185004c00d08410079501c65020b080030b098510300440c0c4850800d005d030401c4607200380406180c80c4401d1419040c402d01603603401901403da00e1059160348a0050032200c40c050b0303600d410342c40400154805c3ca01c40d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 164307383 1250 164306133 164306161
    0x30f060506031207030e010c110904030305010e010602070612050411060c0d0813110d0213020a020f0c1f050901090918030305070f020a0201050702120f071e050a0608150405 76
    0x4104400f40c0c2c0c0350300004800e40740e01d80319000c80240440c0c406803d580941d0b0081c07091190030340c06885010b094806040c005085a6400c560843c086581c0700c0050000c4282010028090a1640014030394241040400b8140070f26400003900740310723100d0b80000c1c02c001128804540c2c11101401c000d0f00c40d407a1044035a00d4540c0c0012a074005150f400000b145000d0030800c8017a0582c011440315400d80c10501032000b4a01143c9050383c0041f5030b004144075503c4203100500c2051601c0d80078094001ca25602c85047c440700e44c003054800c02d0444041c954a00844c01c02d00742407001410040e82d903150b4000180d03505c0349a91b22400c02e051030709030301318400386034000500d44441c82544e0070019507841000540d9085100e0025000680c0301040a40055001d0b02c010f000075030000340180140d01c00ba01c0b0107844c01d682c0500925454003e44c41c00c115690743c9486403a941611010000e80c0135050001188110300c1c1761050500b00314540700030500d507480190b100c0301a0714000e0300912552925440040340c04c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 164308633 1250 164307383 164307391
    0x3080711030309060409020d090203030a0e0f030a02031e0f03041d060d0b010909080c01060f03030f030e031603110a120905040b06030a020306031005090a21020a1704030f0605 77
    0x4015010800c50914012080b1529010000d00c1941000d0400852600a4000e41014a140d0b0342e5420000d0140c0e81c03c002904a4a0550f0b480c12803080c9440144129001c02441e40c50013544112425001698085100c1504003184680c030a407aa2082c191285000c0c0e1010415400e8000000d020904550b502d030641c508001c0903803902d000d030b01c0b818180800341000d201d001d13201031270400040c0300032950758214402a0707004550007418070b00044050303400c507009580302291804642600704105900015000c84100311800e0801410000315101a141e114a04292640701e411899000402d401000d00c0c0d201284a58102ca688503400d240080c490300c5210540f00114001d02000203036407510b070140c40307030303440002c0d204a045468010070742009e500050012030781409880c3d22150034506070f2180700d101d60308900c010418540703942410a82e0301c50005080401c0030900034080c030000d80004040e546130303a00c5070900300601c0910045140314041c0b0740000703080f1819201c2c0076003403002d41d410285c09 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 164309883 1250 164308633 164308643
    0x33c010603021206030c0d03030b040204091802010f050a080f07050d0c0806191a03040602040e07120c17060d080c10020306120d1d0a03020409030f020105010501030c02070b0d0b040501030807 84
    0x2241c80d44410146c1d00d8058050269000800c1e141140000f0b00c0380e00301804520b000740c805410140c84e0130818060303d00c64030303003514880207240d810000e41d80c1c04404030084221504110385041d0a45500410402d0020300e010034000340d400100380402c5c81601181c60410001c0e500f00030742000007100071b04040050300e01d2441505c0c01f0261404d03030841c000603542203664401351940d041520048800d8a504000d105440b080d60038040002d15102d0801c00d144103a0381540c42a078540794400d0b040d000c440804000d9010013213001c20501105110742210354000c00c08a400f40203180c3e491801c60003c0c899080700d0b550601880b55031110030405a0013440c01104c0c00c9580040f4007032010744503030303452540042000004128040025000d40d0244458050100c090404094142c40ba0042402c2d030301c100303408400042d80307402c0304082d00340d081c0305040c0500800d18051081c00b0307040500a541d5942409165941000000e02215a42080d401005480009081032010b980d403030130300340465004190103440d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 164311133 1250 164309883 164309917
    0x306091b0f0f0905060613030308010612020702151e04090c0e103006031203051302030d0e01021e15010b0406140c0a0204110d060902033c01060302 65
    0x24009180d0601034160b81c0803084181d1654501600d000151101a00c40c1c0d80002040042d4008404241107010203180a81c4851030b09501d07206004016038449002041d0b0b20348180035101c0182c1d10082c134101d4040c0030340d42480e00e5040302700345035038525a0345208400421000400081c210159040002108556200c1c20f01d85109281880320000d0064140c07400600e84480078150b102e0540400b0b0081140d4101d01c81c03104092803035500c201c400740d41050300ca507409040550807035a4580115035000d00c56805500f6000751560200f691078094510000034003003038481010136a442007201c5d00544d074071009130303132030030720460400985500240840301c640403104030001c15608416411101250f60603034511402440c040ca01521682001c6082d941d1400340d4000440903a89a029122101880c0014141d41d40c401e04800c108880c01c1d603004007000c0d8014070400c594195402b0146a01001c00e4208403c0d00200310f480c0540c003080e442c1032051082c82040042005585130340a44507484107000380700 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 164312383 1250 164311133 164311139
    0x703020c310b1c050a06150803031906060f0f0f0302071a0412050408060c030a0e010e070510030603030507230303090609010b150d0911130e0607080105090a0b0303040306091b 77
    0x85040200c1e403602500c540c1c08903e0603000640746d90f0000342c846051034a000010b83d1070320fa030941507a00555001d500f05804407001d01c4805003070710505004160034203084d070034412420703405801c1d03140450b142c0f000e02c10000012001035020340c0455100c0d6034040701d103660440b025041001c0048040d1000d440c0c0c3c4915108074401c2c14000d0088070165402d080060400b603030790342c0b0007003210340c401044901003503240e420306844807409000d000f0f500c2d2072010141051608003400d01210b0380c1c2d01000340080500b403a80400220750040b04a6541580210302244132103d62402c0501c12130b0010329050442c40000204184038402051160084100400a200822003c000c012285802548540c0c3c01c14040202d000301c1d40d2203601010744584101910010b000c1880c00044075001990602c0b08d42a8175640f042030250b03802d100c1203601c0031980c2810b0724554105004100708010080001c10025903446682031031ba9070400a40300110351001050007410418a01245108200c09444207014040c20001c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 164313633 1250 164312383 164312419
    0x60601050310030b0718120209060312040501030e010b090702060a15030b0117010e07080c0111150402060d02040504050a020d0b040515010c020111030a0302031b0703020c310b 77
    0x482c000e0840100002e82c440c115140c080300e200c2c1c040c015005110b40c600b24141c2c1c070300d81d48842200814500d19007418039100c600601502410060501d88aa0004511156803a8150b02590191282843c1c00510f108088880e903004011480074254045440c41c1000b08040e03000800da8880c4c0c040007002d0208202c5014100e072051540c0c00020400c0302c0c9000184002910306071030084864010001080040d4010616410203006400104440c1c0140800e1032095803c0b0401c110624900d0b0020120344c0d61068100d20781c0744c40900000d01ca8180003450380180102d540580b0050307c0002c20402003810240030201c000d5000a0441540f0b50800d0f04800340c0b0718151161f503100d0415880178813406008940112207050414104078103000855407140548070003003000d00850300b45038a00581d0703410f2980149000c00d00820480c0b002c40001c21542e00026808150078010100c16542c0150480c40c401084030302622494101241c210006c401c00d00d01e0301aa04800388400d0241c0e07201c820142c08410fa = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 164314883 1250 164313633 164313637
    0x90801060305070303050d1404080904270f0c150801060f020609071406040f0e0a06080703110402033d05010504120f0302030715050603061e0414030d0f0e06060105 72
    0xe03000b0341003500c3c10004a80680b00901407502c0741900003442818a00301c20080410030384040c0c82110000c252070301e25042074410055034412804803040c0c013000900c64504540700070100280941030000928040000082c0e1030406070840842d04005803a07049401440c418092154500083c00b8a42c0d070300c50107002061311800760a2030300141401504040c051940e400300c0b5000306800401c1000001140c011001904c030152032700c50001049400c060900405030b400c0c9411183c60368000d010100300051401c512140700f04d6056030301503107903540c0880d4134000e0a02c000d00682801c0040d0320907041e160415a05043c0d640340d0703c590260302c940300c2b001100e2038040c50180c80303003141000a000c80400c0400c3e020420091080c0f04036450803003075540d102c011400082030380c94025120400d10080e49400c0c0a16944040c403080e40a0450308480c5841207000406800580040c10b5800590800304060049814400080c00207100340314010500d10020300c10000c04e4a05800782c040415210361103041 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 164316133 1250 164314883 164314889
    0x506160f0f020c010e0f061c1113120204060302090f040c0605030c040b07060e011508060114150c011d0d0e030105011410030605041b020c0118120312150609080106 72
    0x1c002c02d00d61003c100191100700d01480e4241c2e100551551003c0700d80d640b80c1c002c02c9506001c01d65a40080741c0c20700080e0030340c1e010844080a101f41480038284544a00c40e000b012100780b200581e560078141e00100d0000e048a81002e50070805010800521014070b40746603000e00d10500103818010790303980b022551804143c40f00c0032100d200700701c20041341a00b5409000c41c40c1c02902d00203200c41d1401840b508483c56142c0d06a9024900d0004110b501801e1044a0040260380300070726000b4135080001b0003c00d85100c00ca58441030120340031400348800d6115845030b0300603400d8155450b2425010715940c10030b80b625000005e94245613214281018001c25040305c1040020713202006c402010800b01242202c02d410405980b2a0005042c4d6294010040400010103503413103050784500000341002d0780e400410707040c00784510180c112001c0710761340384080f5031141a4070301c913412451404032190f44d00d0f40d10b8510b60302e017402c44018003121905009003c0340c00c1c9850b00450382e5034544050f801d0700c0c2548 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 164317383 1250 164316133 164316137
    0x806120d0f27080109030210050103080301030605041506061e02070e04020d0516030804090e03070f12020a051002130f060f0e010309020d0c0305010506060403050606040b0d0506160f0f 81
    0x4004800041c0502d04030280c02150401600d914140d03002c200c40410700c1503101c025281e4503407075040e040c180c051141a00100d0001014019907066894031041c620041c480280341d140d89000040c240072484507140c52941c0501d40910200313545d5003004000d075022056200d00c104400017685403a900010301042181c580b8a14601c05541e1a001c0061018203040300b82c40300d00642c1e030004600a03550b4141d030f01451042030b00985580c01c01090ac01256120030303090019900070458032010584e5400341c80395945d03100c800b94546558100040b03040815402c80180f143c42244802c00010020303802034030301c0d038a070100e0010a0030707520341e040c03d201c403c03600c01c074004513070342c0d01c1040100f51290035000401201810301241a003407a84c041411801e100d2026210450300050600803c80b081c06005d401c944111112420141182c0b641034a400340035007014400c660740c038080e0955842c5c01601400d01a048429903143e86401d0080189004418181000148154501d501542e00440040c502c41e0126 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 164318633 1250 164317383 164317397
    0x170c0d060c05041203050d0501060801050d0f020105090d0f0203060a02091807021e0609060603010507050d02180a030c14010c0f03180503010c020d1107080a0b070c05010c0806120d 79
    0x3515000d0040c00d001c070800d010072208100c04508200010075000d1160301c00e42d203c9540ba039502c0305050131100c040c4c004070100440d48004100340c0ea01c40c04648000c9412044403c0210210b02c0140c80a00c14480056000305002461200348500c0030160030405000340c003540c00a50314060360000b05d201d54200f1036440392401200c85203084200341c0941e44109103004844000901c03407464224451030824102050303020108003c00b070b40050009542140040d00203201a0801550140c858000e686805064a034041a010083c095035040d95000e001d001d0683c040345a101d0401c8014440c00d4010701704102804442c07002a5403050307099500c0650008590341010003d035174120f030503020b8110040d41d00e00c1020004540e0756002c0c800c0c41c01d00b9103150010000b2609841004e4103070703604080341107004d03000034904210310030001c10300143c01a0b00034601c5805a6138200d0561b250a040390b0042c040307600e031071074402d41a034100e101d4600070380b4100c0788503482d0080c0188107641d4200540c0040d000600d5 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 164319883 1250 164318633 164318659
    0x405010509040807050109061407030c14030c07030210020a0c1403030103080d0b060714011a120601150504080a241b050318030304060c20060c0d020f030702010501170c 74
    0x403024100c13982c42400041074188507601d0b41000d0b45c0c400024683d02c00080030900c000306401d8412403040c08658102503504d1a0000002c0174980001003c1e000080b00019158040500c207001000350074002070011511001c00280c020050380381040c04071a08100302d900e01489600000640c1c0c100c80d171001040b45011501d041d400003802402c000303503030090428483e901c00500310b40200f5030000381c1d460000500e081a80c11b801461480740204038042c85008611805020740032070960306580ac1881e4928500b0085d0750215080c7c891350b400b45030b190246c54505d00800040b810400800d0921a041c1e813501c00e04040380b130086a81e403000701c5003114010081141e1480c00f880c09941c1c002101c03d032945686072110101c0e8215030080720222030321070b80d03841050800c03034100b10f42c042e6102030039003240c280c1c0e001270402da5520a0f0103001900304d60404544a24110f00d80d40464040080c0360410a86a003003088019003e00300c00c0c000c51314109041480280c003a00c00240780b411201000b0300014102038 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 164321133 1250 164319883 164319893
    0x605120a0902010c02210c0d0206070206070c12050a0c0b03011214190605041406060607031d040f0506041109060702062206050a02060f010609030201181e0f05040501050904 76
    0x21481c4401c030b0500c1400b0744c0800240c0d440c07104103011451002c2d5001000d00c4090151070416902c09412403085094260150168841500f602d1402c0e80c1641c40d148d0b200c2090401080101880e40039040135031529038940d041010119420040510420300c0340f2280e901e0312003401107400240140c201d900004044000403c15001c4544410790100382030312928000c2c410390a032201e40d000380945489440c0d0040c4800c1001400d0b50890031460340c0e01622290800c4000500079100b624409030401000c1503101e485214040c40d59151901c00a00c06c00042d031004d88400040c0000300c43d068865858074080c01c1000c0f45040807541700c0203009262918140d940d031b0801c0400d40201040006400d0343d0180440800c1264032104050234281d102c4907160002d0410007031078050010101c0c09a6000c5100404c400340e003051520041c0c90342400c0c040e400c69010001d11903159601c0d404041030044200449009a9805010905903061000410b41c816100d0081c042a98800c1c42825000b00d05c51002501183c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 164322383 1250 164321133 164321141
    0x10c050a120f1d0c040b0a12060f050711010e0a02060406030c02010605030706210e030a0e0d050607200f07060c0f0c0e01140301050601121a0306040503040603060605120a 75
    0xc0c40c292000680200e84190b20007150b8402420012002141100385141e07103082055885503082100c0602c00d0810290100c0d0101d12103100381504413031000802010403c0b0785d0015800508492400c018034600304000400c060440c0900e010300d035103002002c1c1f0380f4100104103e1100c03900504840d150a00e8090100d0007480006040c0c81155038406010860303a40611840c0000d1174665940d170802c181441d100510788100c81500c18090345485000000130501200b030341d80d80032889c01e082c0460140c09010851020b14580014040d0040780701f088581508650b01780020301c100480085c940300006456603440e010682600c48580c40300404010703c1307100d90500c0030140d20420310840705044959501c070030b4100e1a00248a104402c00041c00500c1e900004081c544400324024002402e0000010300071400e0303004500a5251108112005003580419020318000d0140894800740303071508200c0d27101d420901622001074101400015074500c1441580c2400f52f0368900410240ca42058000040c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 164323633 1250 164322383 164322407
    0x1050f031f060f081b01050403150504020f1807020607020a0203151b03011403060604060e040f08090d05010204090b0916050a090b0408030316020f1f020c0604080714010c050a 77
    0x307035140c038008980c0e9042c407107020005080100042100c807410004030322002c00002d01d4541042000c3c0020004030b1403614010200003201031000582d40c5407800407070780074144000390903005121550381801e81c0c041807110038840e040540c256105071300c1e200e02c00c90f107404000101031341c5a070001c40803c038a0407919540507040401d00b000711050710300f050001c0c0e816420903402030038441c03100060b4903098101401580d5100600b00c0d07017003008130308046110f0343e01400500050a100c410340201c90800071a003007100d806010042180c01540300340e1a01e00d02035400750150310015402d040c2c2ca15824103000600c54012140d01e4110300c842008008101c516030080000315041055040c40011400344e214014000742c03504070f0140d56680b400c541c2803016503449014160856001070401c4280800210304004035610b0030300b407510400340c1142c0d000082d00800c000309405000d0103007032008001c8100020015544281b484a0032590901140c80c2200c48c4084100042003081100e462101d06c2240c1c81400 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 164324883 1250 164323633 164323693
    0x12060f340507060f06181a09270a0c06120e16050411130510030f0c09080c010c0506010603110409060b030106080f0c030a020c150705040603380d0b0a090b01050f03 72
    0x200c00880d200241c05640c0c107072041c0310030104000045030030f28440340f111242805100010700d504a2b450b42d9410760003143c1d200d43c00030494603400fa030140e08181c0d080000c0e2800c15004aa0300f0001d602c0145102e0000341c8030b0a0310452922a5961501701850280c4107851249004100a40d10304400d012030303426054041410181d030781d0b42d403e00b02e1000f4896505105265510a07a5050502c2c080e0b52400074006100e40c144120a00c800c0009240064024196860351602150304001100d50310740d0381c05160000306c6241c0c10b003000030400b042180055070480e2016941d140698440340c110058100069641d11f8000c54200b0004000700116001041c00e100014215071212002d948241035500064800c0030010302d000170100405030f450300800e964251240f401124103000c2c042c803000b034202c4401e0340c012001c100c0c040e1031030341e40d4070b40e00c204540304d4021044004030318140003410002c107441c1d1030440d280007140d0000301d4103041060040100031000390007802c01c800000c0e18036810082608a13442 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 164326133 1250 164324883 164324921
    0x9070f180b03210307030b04090c05041107080d0203100b0408060f060d080d0902011d0a0311060708030a0605041a0112050c0405100c0212060f340507060f0618 70
    0x1d401080d1103c40099022410782054503410000d0004040e41c146220062003a8240904000414030351050300e011030300308031000110280ca4001c086250301601d007010780401c00105140e45060000d40095205520064a40030290340b1541c20100c103000d00d00540780c6a81c081400034000c0a81c1c6071042d904110000d00f400c071501000e94404589522410840300c80da40c4443d484001c55070441203a1840303100741d140d4155165000720200e680d8031090310016000c2844403002d5841034503070302c0841b5403140d08440060341d2031805004070f10190105101c2c5a0150f480d01c01242d00c120702e01c40c044001240d0507074075110018680300c1104003600001c0d216010151081000066030380d00da940e00380400341c01d5141d0301c04150660040005800d0040702001da560803000c10018240c1d001d401c203541c040000300d1481164216003220841007003d000c1c03a400c001c14030901011015070400040c4c0740f518070412003400103e00c04900402501c00610642002645001d00402540c0307580d00801006000350310300300 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 164327383 1250 164326133 164326153
    0x6030706140c0307080712120b030a03031d01240506031b1e0a02010b01030515031c0207050a030305070210140921070909140f030a0c11090f09070f180b03 68
    0x22100746d0088104861410b558010302e5405038125807800c44001015400300004141040401c0d110000f03404002c0c1010740d01c651821410380000c4441c00c440c1801c00003048844405080e8500e1414030741822840d040e0502000550303803415804980c0301d02c4041020b1002c80c1840f000142d625045114011482c140c0e000d510f150741e4018402414102e0b01350342c001704056000390005001c0320805082c0040d01040b00d0724983d0035440c0058244010507003442550b664441494040b800c1c01219000107038003401c07082000044c10340c01000741c85081e00850308800d8201d010301041c2c07030005030101804410b200a00807141c4601d042c5070108101e82c20000740a24070022000e102e400d003513150304048a5541e84412160038040007210700c0740c171a11040001c0464440d50018195030b8000d404580c2c0822408413000030400140b54206e0203c40d0780a03005490380c0c18414a03407a0b94039001c4030301050510540e40000b94000341094854200d80c1c0d24041c498203400c0c503001020180c1100550369805102d14680b072 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 164328633 1250 164327383 164327393
    0x80705070b070801050f030304080a0b0712060f150206060a170a080c160803120606070212010c030912140403080703090e07020703050115060818071205100506030706140c0307 77
    0x307449840107640310f83e15036040c002007001d01441c01c40200d000b640144001c0c048902c00240c10040543c2095000b00c007079603060030440e68804140d096541300c45c24001c00055030120f0394048019281108418180724841d41012655000100c90081d0f02000c4004100040d01c40c0f99001c00001c180364041d1401c504c074944503504694000404541250302088500c0c0301c07010411145000303080c0d18009581f400802502058400a01070f04281c0b103001d0010780311b011980c92800f40802200040300a00114031120343c06001030140250030344206036080380300850180b044069101c001d40d0000c1160600d800c0d900e0361019034102d003008800b88600e601c000328034522000d8215100d2500d5038002c1020314118980139003074401141075280d8a0031300250a006003034004405980c405045186190b460400c4401203180015039070158010b46178580d440c44c00c2c40310115100018008106050110340c8966051580e00e8400b44500e82c0012040c200e4101c2e0464007000500f404442c0b44100c2e410701c010fa40320 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 164329883 1250 164328633 164328653
    0x110f030a081005060307080f0a0612050c0906030d1b020f0909030301031203020406120f060b030a14010b0c0a0b040f050706030207060e1f0f0603080301030606081504050d08070507 79
    0x2480c0c0410305010070000c086001c1ca074842c001e0b150641c0d0a600b9420840c0c005400c1400c0541007008085071200000d012040d554000070040101c040b404a01c0e00c81d5050180c0c0792a103204039940154003810020320503040c0025280e801544076030780c81c1c03611800f074125084000c9098000301d138002c1c07082d0840400707075440f061014000c40c06c1030b01858ad20751542c5410000b688042c5541014540184010008a500862408060305486202003030856450344850000d0030329412a1254850210500c25910b0065001d80c0d41c1d1820301d25242e0172a600c076000b4444900856610241940c40401c0590004541d10040e907085803080c0b009041401082d5200c1c0c0c144072494025100099001c00e02c04240980343c080d1000c0c0d4a08000685840c0c0c0745a007142000c108601c000450482c0c9030040900c40082039070011009640147c9000d4076541c680c50410041d201c03d1107145144d100b02c03003240d9444041d05060502845d4020018000f881c2d4015060f100301d200100400d0074883e040c41140081542000c2d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 164331133 1250 164329883 164329897
    0xb09010603140a0902010906050307020307060e0706020c09040f031115010905040605070305040302070504020a050c012a0518090a0605090406090c1502030f03180a0323070b0601110f03 81
    0x140854200c10069080700e540c000280f00384600d07804c1510000150741c11841c0c030000e44640c0c0c0f0b801542c1c1c0d6542c0348103900c0c5208003030005003460b00c0c004848000c1032700810f20b101940e02035806e80325600552801c204080000781c901901100d03c86a4080010f40541d01445a0b1003540b020748203c0c81404001e80d19580090348204105a260420401005050f10a082c1d01c40000d0401b00244d050585000350703100d604d80a0103000f03c0e0f0001e010130b0964080c4095a505100b80070081c0324103001440d1061403010a01c1b61011320025400c15480410302920548580121560108114401c81d00401c29280005081c00c4141da54950010495469407680503118901031500440d2814003440c0014014a4680c030124050120189803050181e0100c1102e410f154041e681a850703465014824104400c11440000c5030320400c0d11600c10190407261941d203490708242e40301c11100645a089045200d06400100308032010310001c3c2c6203601910103e00c5051541027114030003008000d13114a554000380c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 164332383 1250 164331133 164331137
    0xd0e0f070303230909070909241401020a0f030504090603140c010509010c03050d0b090f0108060609040218190204080a0b180c090403051303230a0506070e040b090106 73
    0x2190030300c02d06400051411540001651074902d40141c01480c4000b4080d80e1041c52003000300310081001d4a206070203650203070103010030801285840c035540056951a4003210030002c100604001841d06a4015580b199841030300940b9202c85140e4490304295049403003103040c000c0511021412002c1481003d0240d4803c0f008200c0b0b035590308000900e0482d50441c424100301040049c4600381c0d038000f5284d1072259050802d06c0e19120003403542d10141214403903031500039007980304004055620001c0d441c101c4104134181d8559403501c20901c0190801114040d40040d280c18280300144603105046501031000e011802d0b0003030803810803806903442a80040340c0e40d031101c0740c50001d0221509459800c2108020490b1a00000e5801c1d59250b04500c3c02c0d42e84603120300e40c0000c0526002d00700f19020100f185121105041c0c50b03103400041010f6200c01d003040c3c5e02081130b2084001c2c100003078001e2000d8015004001e296902102103600407000844250416181c01c8400c41c41e49400c1e0046000c1e003407c0e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 164333633 1250 164332383 164332393
    0x120d0f02030a0b030c030105010602030a1209050607050306190503151e150a08010612020607021f020a1a040203060a0f021c050703110315010c02010e0909010b030f0d0203040b0d0e0f 80
    0x318209450100540c45c200c0c800c2c1d140000400607160008101c2da078030401d42c01d03c43c944480000e80341c80208007100000d0b20b580580340c104202b9551050081d4840c802c111451100c42d01d031785495501202c481d025150f0503600000942c440c081c411010b181d40701904a080e0021101640c01c40310440005481001d0480008203602e82c05161210b0210040c005180c000c11407580f40100a81d5022030003400a80510000134482c1c06540303c1d020440c0f000071400625800a182d0311100035551080244183d4600000c1c0700f2800c01c40c2d681031401c1c7d00841e0000e00824003030322900d55560042c900013a0102c00360750700b048481c0704a440002140360b03281203244000750503c0c00b200c1c09016510700303203042c41c440103080040190010741a40c00b100003840c20310302100403040620060b00d001c0c52010441b98000100780400400101c150404002081d0907000d40720040700036007843ea40da0340b0705034a86026800500c03080c080c101c03d00c4040d00000b4007141c4045502d0906011080c100303d4007007412403454105d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 164334883 1250 164333633 164333651
    0xc0206071e02030301090b0616030e130911131b092102010c29090c030c100f030905030714030d0c0e0904080703170109090314040602120d0f02030a 65
    0xd030001c469020050410649403200400080d180e200501035102d030955201300140305912281c0a4034920034012003009140740c442e041c007030500e2050024082c4200711071281c07804a9011405000300c050791140e40b054251459400704440c101318140c10529940e916900140364041e11100b540c6060b090b074403500407003420001030781c500c0300100000143d03e103503d250280060741e10030b21520f0b5207500900d40c00c444941420090443c0e0802c0040710480080b00002d0082448000c90380303041c217243c110111214202ea00c01400300f020a0510003c001c990070150348100907000390400380c602480b4105507071500006944075104400d803407546010540c40410481081031040c0301d4a070055a45040210700c04450000041004000800040c1406404038134038080601071030b50103d08a008541204c103070743e19160040020400c0082c16000170b20040030824450100300104d405a4220785d0241c00540c150380a0040340350f0204c110403000036941c001c50310a0612078800346d409898940740214420b04 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 164336133 1250 164334883 164334887
    0x1090509160b0a020f0609060c03090f16090b03010c081909060203040c05010f0c0c03060c260601090605030f0c09060d0204030605010f05030105150f010c05011103060103051308030c1c0c020607 85
    0x1004c0182c002c05c43e030021090110100d000982154401c0d40104031958a0f618010700384c0c00d000500380b041c040c501c1086a0155402c030624040d00599081c1c1b4010400e02c000841014240c55211020344003068060001c240c030850b02c052101800da50b0b10101080d02516581c4031003c0f03a000700c80035203c1c10120b007002d226030340e8040103421440c0242e240181c1d00c403000c0e85421641c40344921004010603954410401064050318040702d00c1c0342c12042412204c404443e0003100e1240803507450b400900120800b0a4403030262041c3c1b8001c1c0861300a0100d156150f404a4500303900000f98164000020300c01d13104070b8016030005001440c4150300129203949442c00100c10000141c000038481d904080400899403500c1e1940780030002c0860300040c00c5c0c4005401a0791030345d00c140d409090381d400e180c81c58540c00341d52801076004c1c8600b0307078080143d80e99804a1034042c642d40c25006101a00800105a6407482e22004d4140d0742220361981150500c04450601101d5044d08510b01580103003042001d025 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 164337383 1250 164336133 164336143
    0x17120414040b060a0e040f09050607020f070b0408190305090901122904061e0e07050901060318080702210f16050a030213110c071406070b01090509160b0a02 69
    0x5040ea03a503420859000d00241905c220040c5060046940f4621281130031016040380003501c3e0000d00b0707a1401d0074440402501c0380304610031410300340b10f101c00c0003c01c121500211412103042e00040c02048c01d0410440c202d00b03120307010603010050706102000459644264a1703000746841c680c20300e180c3c9080e1070200d5151204180000d6a551044102d400031000b4030740607a4490390208002840404c43c210b084900030b1445e40c0340b020146880c15540300c3e950005a00700035101e045600c00c1090f03984140480a84903655089454dc038080c0b140700f00050044800f50200610003003200e00c1051100c41e0565421040001607007070340d0701029054043c00350500040c00c081c0864140801918106004100004080d22001307009850425894404003d203922022400c086143c0d02c3d6514481810104e170b1ba0f109900581712201643c2c04501c109141210807a44103c3c0d02c401c0f080902e80c0383c26501d10060030014050420713801071000107001c000000c40d12034047e200b40d917051070f111076541d80c00910384 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 164338633 1250 164337383 164337401
    0x12020904060b1803030f03060d0f05010e0a06051614030c07080f03070305060a0803040b09030109150b190e0a020f160b1e0411120304090507020304090c030c091712041404 75
    0x4e40c204100a0701c542d17200c101100d622240503a01e41c0344071010343c6400304507400081ea026046500c1d14965404070540403400c0b01c03219000351003d000c00e4640b680c07046103003901d6034003800108004819081007403c210b40610740c0540b9000101d0b0805060f0740300c04000350301039258548140400401c100c091600b46c850303960420019901111030a0a28031a150f0300c0c8902d0141c8500036502103600382031039609420a94002d6031150ba00381e007003c0310501c0c5c0340c0174154480040344643d084202070f5006503000110107086031145a5124025129440e4a6000354404902c41095290030810000e5103034041c131092030824400c43c09800c0303078030f4904200900034682e0302c00d08080006040901002c1090720020060032403045500d080ca0642200105280d4812540540040e03400c05041007641134020000c2c20869030141024880c13848007143c200c045407100c18010f0f0110303e00e4042489030075055865100e880001c002100c0413090801c3c2c00945c2c1d40c01c1340d03104a8440b141101d1050060425000d24021 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 164339883 1250 164338633 164338639
    0x80a05010603172115040905070806060117041101140a0e040c0203070b0c0d0b1e03010b04020309250f0f03050705010503040b040b0c0f0c0102090123040612020904060b18 75
    0x13445401d41002c024103200c2100010035800c10380125412040180181030221001801000031011a1800c2e90301e407295449440310b2401514005845c95024201d03015103042e0741095118a50344907558424081456081d090400008441d4100000c1e40c0d41c005040012480d100c41030b0bc0302d1000c0800c010340d407a50039401c04642080c050f4000003404a0a03082e0452141d403005500d8462520707090005080700550340e58040792400e00384007031110381d20410300099816402407001503060320600c4264441a030360390005501034540054544002555200e00c2c40d20404c984039620381c2c2c4c00300a80301007103030b8202541d9503d40710310800400c0020081d031002004e00b801c00c03c0c20b61606844e0a52141402070001e40500c41c1d041c0040e0ba0900d000d070407280c10048803400c55880b6400181018001e400004515002c02c0201441110640b940f01c003c1d51010020103c192809080c044200c502c410103500e40c2000b290240301d071900d01d50300c901a400242581c0703a00300d51507004995541e81541ca034040d075580 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 164341133 1250 164339883 164339887
    0x90c1008160509060403031209120c05010b0d080d020a0e040614030f07030804060804080d0212061201050c0901051b07030f1b05060307030e0a0b010e010f060203120402010f09080a0501060317 84
    0x43c0c207482c0c80094030101c9030107043c14801c01400c40f0000e00a0254140014480c6ca041820b8a0310030345c0043c408094540100c000304405c81126050154203005038070040d024010074420f5500500d0517400034880400e0500c1c0083c109070f40c00380444e0507124203800400102c145021011000d0504000781310b03540400200504405207562107229080c4102e00600c03041208240000307041c02032100880b40001c55804046540300381031012454091016900c4510805640700305403100d450500586000c3c040602a4a00d003007117040c01507410b079009115240c152a0000d55010f203140c814080d1100840c002d4142c5e4001018a01d8800c0380f101100c4a1031601d5103513444244895124401629440314460500062541d0408000703403405040701c8004150081c40310010503011111000c03107040320400e44681d01d50645904080e07841b0f001d0050718800d15400e4200040166110b09850981c5501ca400d2030000f0a40310300c60541410344220041d60903a440d4281007080211907900c5644119005400b24 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 164342383 1250 164341133 164341147
    0x602041701090c0311150706020a09060c15050709030b010b0c0111070308010e041716050d0903020906045006031e010f060603090606050a0e010b03090c10081605 71
    0x3c1c407500c4242c0005011810100180541900e400605401000c904072070310703440d01c0d518600100030b580000c0300203002403074080c80003d01e80d002c4c20a1000d9a41c0c051220200074400398020380090000500c0e40c03041103e161310001c041000b03000041c0c0600382c20f20109a90b114100c00c2c207400d580300044141900c8604000c01004641c2c0b200c42d01d0305444440303461000035261030030072a404e046008010000a08005940c085a0030b1948030480c0b0284258151016004e00a1040d90700f01f03002e10000e90040c06200003e0041d29260788118000f021481c140c0c080f01506010241841c81e41309047d9845d00c0b6600e086d20003071070341c403001e41280b100720160004147c9800030100b51910190546045103000703003102c00c1c4680f20207400c0f001041e40c182504111541c2c2d50440200075110307061013a2913543ca0004089907604008000c1e038151040902d8030744070359282000d19030065000820004040c0243d154403040c60307490a4021076403110a42d84c81095080c403445501c50a1001c403559028488108200 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 164343633 1250 164342383 164342393
    0x1202030307060902010314090c0a0e01080c0d05070b0c0d030f020a0909020304050705031914010e0601060c0c08010f050609060a08120703111c021e070b0304020616060204170109 78
    0x1c0d9000ca5001c1c0c00410510034a20068014218290910148002280c108640242d0008030864940f804a4803803d0980d500c5400e4130480e0303402e019201c1190032107280454582010741e0450304c1c06104400311a40540e44800c0ba03509071300300d0240c0c01c6182d0001400c1c16030559050251002400030245c08501c0c10f0804903011f8500f080764411080602d4010000a0078040c0901070507000341405001d41e81030241c01100050705008100c000c0b01c0d0361403881c1a6200d00e0b6414410460400e0a00d0b00400300c4d642000801d03103c40f40004c2c82101c01081c164030208190b40203001c0c03c8052582c9010201d6142415070402c030381c040c801040f003801103400c042c04021071800015000d015801d00c58030a69200302e80e00341100d03c0101d00c0e40440183c450341c010f0445080304092203081e4843c2c642d00380c03441800680c5d140940e8100307482010403a648090360a000d141554002184c00601c0284990719000d0081089000340140c101c096074015404a4100b0401088031034130380c19050400001c000302e55041c0e41e0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 164344883 1250 164343633 164343637
    0x50408010e0136021012050405010203071119081308030f090f030d090902091305010312020d0c0804051003020d09030f02061021050102160605060f060a0507030e0102120a0c0c12020303 81
    0x201a100d0784c8483c1d000b600c5d981c02010302d40c00c400003075802801680f0b09410682d010303601c29200140007a82c80c0000340011700000c01c1180b03499500c0b28100940c0e41e8242c440020581160119080c40304402c0d60015400c10100010101c1c072814504a0f40c903102000c0811000120581c1040c0c0607400070380c078001400f07611041203015a05c1100700140c481d02403c01007546607150400e5582142e16140010041c031442a52001e441d080b00d40c21a26980c28144007150030004100c0c0040c080202440f0a00c8289012003a25821103001d180c01401c02880d4001034094404c0075106030017140c01c12000c0c1c5943c41e41800f05550208540c480646540d01e03118501c07145e4101c20a20344100584100e10804000c004e4040f1910000c0c4900c0b1149410018200f042c01810255419803046040503070290392420298152140e440c42034503070904143c0c158030251192040c0010b0302d030450061000c03501210302c038900609148200c81c0c2d596101d150b204d15040210030020b40046648c0340088122000603600081 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 164346133 1250 164344883 164344991
    0xb12160f0e0a05042904020f030a020607111311030610031104030219081624320301080d03060902130b130b04031419050303070f050408010e01 63
    0x1e000541d0340e99a092240184c040348800d10b0171100340004845182409084c0320740664000c0350809a10303850902010342e03501e440100250800d1081c0b0041021400d03000d10101b180d80d0240c80c0031360760045889503c00f1203400b0005080f092001005006441c180710012007a4280e41e414104200921aa18035210340203910000303104403001051100e11805c50b00042006004040c2140c202d01b00d103101a58041300c0c0c90090f89131001440c075510b904031650807224400b4601c030b511926403080110742103a1000708402c0780e814175031f41c4428a61124010a000440c02440f0010280c441d80e4010000107041e0340a907401002614010300aa04c54502c04000441c101c0b105100d0f15623503083d0020b08600e80b06240d620003034452401150010a0080c03401005101c00c01d2030065480e4090742440d00b24501001d00b4000d003140c0d20600c00140ba4a0050b160940340d49098108141015500e4020f0307400c3d5640311248180d680d45030061828407441840440c8a040d10f8042d076400030f00300d0300d90940d9050300c1c440 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 164347383 1250 164346133 164346151
    0x60909061302010302040b191e0903020918060a0b03071202100c1506030516050306131b05030609010b010207050303030f0a02030601031b18090605030a0209040203010b12160f0e 78
    0x290a5604684c0613904680080c400983c080703469014500000041103042032038000458113000c004082c071000f0740043c40501c0300a8441402c0fa604607024440c0c601c200500c20b15101d481d003412201d0540007040380d107209064010380031410766806c0d014542418040d51055103034907591968000143c1d20419851001403140c980a480d114007410150070040038517860041e0103107020b4000c02800780218401407001140c0320040700c901c0d6a00180340d910f1000b1940d072856100030320341c4c0400183c045433448085050640c030300d04441c0c1d152000a81005400c3d200121169540e01c0c0301892940c051000c0001000214055402c600e400361298003a003c00401da042d1040d40007002802c070fa07000740d2080e5041480d03902c08800c42000c0000151800c01d200d911840b8141c0303011000582074405000c0c07007081d52400780c040c0c070304210107600740220118050001c9a065407100c480e071342c9030345920204600b6048004014020000f40d000c0d1984518560b0300b110724a402000e80600900300b0000c451a0000088 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 164348633 1250 164347383 164347411
    0xf030906251b06060e09100c0e0f01030c0504090617010c030504020934050c0f0705010e0d02180408031603021201060f0905120d030f0603031e2303010e06090906 71
    0x2c0d14104009100c650000d01100c0d042e1010300c11a0b040000304c900e0b2030305510204102d021011a816500710300c081062680c80921031440340140d500c25003041d000504107082090400380c4503c8030740c0a0340e80c15004001c0980b00c0a803038020f800d009004e01140d4560b00d060030441030401e900410b901e218008d00e42c20040340d004502c50000c685048504080c0310740040341080d500d010060040c61540010b8007442d0314811410450000c41b80440c600b01111416141c0500c0244102d0034444011403280d0207981c814103c9151307004a09a001103d0b22480c03103290210354034a400c410300310344221203800a108041c4103004014495590311111030544100d0309000414417540002209d024109420954000400c03003801842800c00061100c091b91954a09100d007501e4402107a044848074400940042c81003045084510049181031000b1116403600c50703842c07104032241c181607400c0c0c1c1c1e0040c051580300000412901d20b401490700c0c1c1018084402c40058140340001d0390382d03940e02030600200b00d01d035 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 164349883 1250 164348633 164348687
    0xd0209091006090c020606030d021911030d0201060e0a05070903060b03460c0603020a02030403050a0c2303100f02091801050a0f0305150a020f03090625 67
    0x810844110300c1c01802109019154440c02454060041034998030054801d000c08030b84c041c640403513603040c0b0310105d500500702103a80b04041200c98200400680304c295000c2111b00c0c80c0e031007d0140c00e290190540002c40d01920340510030340060802480600326502c0c00c02803140b846d40c42800d40302103940011f000720f150011540001d042c0f01c4803080741c044007040502407034840d0200c9240742c2c41e12a03503000d164107000220141e95040c00c2544000804500c440582400b1241c0290f002d04131044540c412641443c0c1c50740d5130b0600d0320030915401e9880e41803020701041862241ca41d0080d4503110070151100c0c4a00c1500400c0d5a1100c40203100601526602d20b000c800c01d466060b51601000149140680090081c2c4800c0c0c6d01404c0c050a8054041000040ba03503032032030040d20040304ea001004200b0703620518100c96a0030710143c02c131226240c0810500300003e0713030a400b0b14001d075040c0c0050402410020600c4089082106401066034115107032402c09540101c0c1c501d0100b103038911070b403800c3c1030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 164351133 1250 164349883 164349901
    0x1120f031101050f01051009061209111005030406050a09030c02010c0323090901080309100c080d060306020c010e010b01090b031b03040b0f0c280c0b010605091e0d0209 74
    0x40d040d5411070107600e0a001c100900243c60072190484106035142d044101545070100ca845c0e00c1c43c0110000b20780c005166040c10881d43c0d0146500c580207140c0404040310010001d040000000401d10002e80c000c000d100921905205054005c51496020495100180d5001d0000100024007a061000418103201458002c00b032004c07290303003602d40c3c7c4515190183c454003210b4116441190050031303418008620204000300300e42e00310704000c0609a0b1410300040444649842080c2140c008405100390222440355008801c0038522528003d80c540c80c0010410f0f08403142d1480c8108268101030440c503145c4d070049030300e1b01a83c0320310482c9a545e0b514001540c01d00c809444601d08811000002c20050007601820349024103000005c0400540700c4541c4243c250145044000d42c01c40854419446002c40181032030940e099820f041d65001030584810f0034480c002d91244000c2000052000362500c1d200126030b1103894400c4840c0c401c14107200c040344013010f9030900240121401030203e12810f03 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 164352383 1250 164351133 164351147
    0x60f0302060c011e0606080603070b070813050402122a0a030b0a0314010c0909020415080901090204050702010c120e0705100921021c11060d1d0303010f080601120f03 73
    0x210444c140f003e4028110b20f500c000c086500c0340d600040c0c0d00c040031900518000c02c0318400c555600c1440c3c1e0524546e40c40e03041c0554000840e00200303044051000a0300c0e143c900107002840005c0c500821680b40c42e001110481244099124100d00c15580d01200d0b150070000380c2c0e81c1c40c81540b8001500c60581d0000c81c880751510f0b0006040c0110010b8001801001504100d50022030340d40c4047d4075607501d200701c13401c0e4050783c040c51582c821046000c2e440c851184103800d51044c4548004900f0440d9034010804840b030036200d40c40140d440da40d9220f5000e400400c5190084003200b401c2154407203402001e511003070319014142c07040c90042030311705410344610418000f91800f20100250b041c1802e04c074143c1e40042500403402540f103004000240070000510009054000d502c609082011404000c0d05502400a15144031794814100003d40e188001d1615400500401141e403941807600e003e2135144aa0700c507203100e034080c000500003250401c4030400d45640c4a5540c031100e010901d030a840e00 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 164353633 1250 164352383 164352401
    0x304140f0a0b0f090d17090c060d0e010605090c040303080a0209120610050303091309140601060f03060515070201030b01090f0806060f0306011a07030c140c0f03031e16020d2103060f0302060c01 85
    0x54002c41d03000c50f42d0110341e00064bc4094441d0007040b01554034800d00000c000100c1d00c2d039410031414001040882c0c01000f50960200c0070501c01480d04400000082203900c400c0d000c05003650007a0200026840c14164044c0580402c400650402c050a4001400c20b400d21008280c129140d001d290100f04000203508803842a10341550525a10341200408101e8284030890001c2c0c1440e00001d40c600b8241c811030140c050909400d0303e404001d40041d405040a00c100604009426900180e0305102201101c040d000d00b0025100c603080038020460b1521007021240c1c40398000c03100412140948660384000c10000e8051940c5501403400d0036201a40d02a0024003a418080500780d00c0b07040210b5880d0f5840c400301c071003041248844060680d240a000703a68050b16840d010319550303000205001e4280c8462164146940d040164081201800d00b4641210003c10f004840b04415070082c1c0000d2104a1916081200d0b514003500c400310860640700181c016107002510032459902900242e1003 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 164354883 1250 164353633 164353639
    0x9020f090904140105060a05060304061d1f3c0209030712050607210f02270a0b07050615040209330405060304140f0a0b0f090d17090c 59
    0xa0349007a007441d4043d80ca580841000c0c65180000180f12454194604c4013615005010103045540c3c1d0307a01c10b00104500a42c00d00c492040c40842ca8031490200b14400011400044002c2005040c0e10300005860701e58030000061501e14100e0315044804c980a202c44242d2a89803960031200f0148610013881000c00990b054014803038041800d0400c02000751006205e8000c454059035008021a600f0350040c0c2c0c0c4201844203c07643d030110b007007242c004400803a11303140010706d80b04424904142c08011082200051040300d094490725140c600f030840b0041a400907514038205055841b90741b9000c00400801e2640700306402040103890f01d0703040d141c440700041c100d504d108107e42441c0981d0808032200c2035549003420201c0600e403668100790b404458000d0001d60071030700c4e0f990394600e00c044900d21003100c511030ba0402c5902c001d0200100955603014280c1110307642059100800d2058004143c03020030741c4400c441120440d8001a070106813116010385450a44440c8603d03810400d68410160b4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 164356133 1250 164354883 164354899
    0x1505030408130e22030f08060315091b011106071b080d0b1e090c07021215071209020306190605040e0f010605010c021f170411030708031309020f09 65
    0xc400c0d01501c079082c000c29040076200403041c110700104c564480032400003000281c40e020362940d00341c0103002c0c50760064001000e440c648800074110350600681150100500d078011107080e4440350030b41c02c0200415101380f03082c80c84000d0802881d60ba40034085c184104212466100c9120030303206e10611426540c2c03200c50103941d20702165614026004143c1d03001d04ca09085031001c448504100c00c11072480001402052666803483e06a9555802c014416070b0407060450031496103020911000b01682000c440301c1e240c41c10001c00c010a2000ea201c41c030444180790070020130141c0d5001a03020762103118840009100d000b00c441c0000070b00101d5004c560081d042c041c07030381d40700c0750041041440b0b580c14030000c107c05680d030030046034641e4100c04040d400500c1410b4121210407011100c0040a4090502c070031301200403001182568411a429030340403503403022000c894582400160002c2c407400d00114100803038048016240c0b00d543c410754881c940d00260706540742d65028241c88001e400240008 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 164357383 1250 164356133 164356139
    0x1d060a080a0506091501080c070f1a090102041a031503010c0302070605060a030308070f02030910090302010215010e1609030512040e01060305040510020a020a0c06091707150503040813 81
    0x40c242140c140e440035686410900090300506100c0a081d2046048490031480758a90000569181030058001d4010040404c031000120700015421207205104922547c0040c22460304486d01200c041d14101069004000c10131114003400c80001100750032501c00c5603a503da00158040600c00c408203940c040d401c114462408580550141055a0145409010f265142c00400042d41c0c410300009002c80c50503004641164490740c0740301d0310045940102c0c1d1801841c80d00080b1500d25451425000030691038040c0110350b410b004a5285103158440321589505040d4030740d084020080200000c1c0040d0003460641c1ca2240078420000d58202083e2058188495000195580319004850000d5458000010458480d20452340b080303400c00040c00341c0380720408005000e90710000c0c8001c00c5108610344103000c02c800004034402000f5030703240c00c00080d103800c000340c40e500c180e113542044540080c20100103145c01086a1054210700703242a6580303980314600020b107801902d00240c3c129200240c08 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 164358633 1250 164357383 164357387
    0x180303030204060f11060a11120f040303140609040209060a09050f0402040e0a080f0906190f030c030c050d0e070b16030207050d2a0b0a0c0c0602060709061d060a 71
    0x802c251442a51403040c240054402501c451101c102c01604550081e400901d01c0344056011a9203030708150591807a00da21646400402041516903442d00c1c0f030003c0a2004154141c410081c146056002503643c618001c000164590300043c0041c0c0a0ac40c81e0001a140f035803012051000f400300c007030082100c0e042101c800c0c0c60280e03003160120301a51418603002203200d00041c5400c15154002d034001c0c07400244041d1500e05412140810360454000d0044030401b180311007507a01c42a20740d03941c0f03008000040303a000341a0b500c1d008100b010306143c4443c42901b00d901c10300700c0d0b0703210300041c0c0041081d0343e12400d0507107007c2060303021103038080300410425400c2d005c01c1c4008140d98082da0840f296a522401009001c020341d05000b8450b805214070b0b0840068403d98280b11421000880b0130b032280d079080d00d80c46a91100348200001185c0c010030404201c1c485070100042e1145200409241c544100090720342075a9001d0039041c090b41c003e01c44240049800d002085580c0500126200c0300305500c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 164359883 1250 164358633 164358637
    0xd031209051e0f0d0c050106050411090901050604060909020f070c030822060806040903030609020a091a090312130308040e01081507090b09030a02060c160803120105101803030302 79
    0xc4102401c0c03600c06000b98400004483c4207842c00003018100c4440c114005492024800e40202c50b25503c0d034200045540da41d10a01c0700c14074011040c541d4541201c801c2104004050300204d12070351062200744a0107511040c078006460551100607550300c95500f842c04180240000146a000390400100410500300050000b606030401c03100030160080b040150090f0450141000003554080041c80a152903000100e5a0b8041c0c14001081901d40c1d00c0203090368000c005503404240aa801007001346414135040011541402100b81403055030b20029444194085440e00c4c0704902260442c00d0080720304022004580c00181942c1c1d42d03035500d0410513194030901c1088400e0092061240c3c0800180c06501d200b0b0100e9512a00014208050b00d03000380c202d21a0a0342520810300c0c1140140c54940003801205039040040450380a0303100f421040210540007004650414484802540240310380281580d0040302c04010700c1c03210007030440350308501300c1301c441680c03d0382c103400814950942c0c0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 164361133 1250 164359883 164359903
    0xf020108071b0b060415060824031203061f08040c1707061125051924030b04020304060605190b031602030403020607050f0d0804110d03120905 63
    0x220188541d8581ea01540e01010301220304684408140721440000c0350b5016203940a8001400058509102e8a2090300c0d95010740203407010800c410140805450515a240c3c106000c80b40c1c0000d066491002080d180c595003844180900004000f00360b2030b07074440756104c04589080c9007540d82d052501400130141941540c0540307895114080104185002200510038164054000e100f61032500c01c00301c1e0000e15607074001e40740d80950741483e13903000c8407414401100b84058070606803803800d0500300904031594103d50000314120348401c102000c4500d08605800d5003102490b2040c40c1c83c144213802030b0245070101580103100004000801c0800d078014001e541c1e0603900986081c0d5404040703001502d0b14003038010344003070610004d4043c001e407040c074401c1501e40b84156030501c7d0703072603000c220f190b0014030048816800c040c04041c202441004038180288551400f0302c0c1500740760300d07210f05c0c502e40070040704e001c0c06016406000781405800388060000801004005e10025410001d0301d50719000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 164362383 1250 164361133 164361137
    0x807030305071701080c0922050703120e0109060302070807120503040615120b06030a050601081b10050f1303020a090c1d0303090d0f06050a050a0e010e060106050a03090803040f0201 80
    0x100c12200841200968161004200281440c010100400024107402441614501080c0941c0314024209404892508d40320300000d0180360b0951a107101c402141c842110100101d0008007010f680e030250038841141c100b400c0040ea0b911070ba0414003c00c1c840e42c6005860b051804800d889807991000046106501030704003000212041c0b100c5104030f1200384648242c000a0001c02408181628030b01a046800241221802e41c00b682d1114248142607111711400d8111032901c2004081d2411181ea040c00112072450380f05210540c00792060080c44200e105902010510b9903000da92000b010014507001446c84182d260b42e0f030155405440c441c0740040016028406820394032410f004000ca0b9501c0c001c020314180702840d000d01c40c081c4240642980c841104682503008135500d80708103030041004420109051034181410000d07a1481d4041d8403d50385460802030011201284070790558a6618010f030756190301090840190035020f00282180c90000240001c102130048400142c910030307 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 164363633 1250 164362383 164362397
    0x115031401230105130e280b07050a02060901050103170f130b0d0f02090f04050601022a011d0306150a03020402121b0304050309101b030f1b0804050913080703030507 73
    0x20b01140f0341030b20290f54400c0d1043d44019083c07000d4180481e81691080684c07c9915046842034031009a0a40203460410204d030300000c0c00002d01c2c1e0b0600985501001b814001d120350352550340c2e400301c6a14000ca00070070320740012544241600d281d008903142000184143d4148945403008486550302402c20718503201d16000b0242160802402640d0380c0c040c0040200304042100800d20000d003400030011f5046000b801002684568a800c1020000045802851070080d010f4000b40892441c100045d00c0b04031098411842e50b640000e003207031b01a0842c0c810301e0381e444002c0c010800c080a55040250320a0021030407110070030300b40e004e440c411804102d440c2c2031441c01582160940c80283ca002d080b58004000c20032460a2a651203001050a450110b54942601300030605440c1d001c0802c030f000603103002c02142d40759070043c0440d10203986030082405c00040d40d070354901584900d1250501500c006000141c9429031302c3c10010505401c280d185d41c0d10b80781464000d0040034210348000c081000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 164364883 1250 164363633 164363659
    0xe06070201060911162a090b0603090303180f0f0f0c0402030412031808160b0a050702070905190213090501060c11040207020d0210020d020c030115031401230105 71
    0xc40d008001101c440d4944d06440e10409080f56440421154025140c050400c00d0042e080000300000048190012101001150070240e2041c1030310301d2003801c7c520400c400c0c418050380100200480f50020343c6880605c92410a600e103c60511320b4140b1110110300038a141d0080c14000070900c4841400740744241c80b10040c1501c1044100d00050310040e00c12002c0144940203a4040c0c2d001c0c00140217140c0c135000001c11160340b414020f41c891b2007403e0707400200e0200c0c4010020750007805a085141d000051100c3e00c0e00d0b0384000e41e9000d00f840340364515074484004c919152105440848103403c0b041c020755690040031500c1840031010303c100e1444a01d80000050120b10602c0c65a0b005940421682d66440c1600d08001c0030713400990059a118080740c2902006a58035100d8103c50301c0745070082e04981144d544c019007045948801c03540a83d06040124012611004c111405e81e075014013850f41c0c5d0360b0111607072801080210002034110007051200d0700b802c2c0000b00c0300d90407298100c45a01c200300c0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 164366133 1250 164364883 164364899
    0x30c0c21161b08250e130501060e16021519020906090d0f03020d020601050112020d0b031f0c090806070f0c060207050114090f0601150509130518030f09220e0607020106 74
    0x285074402d2a05c41003a500c0420f14224000218545041c0680004555180c480c003011548110070348030491018812101c01c2e019680511a5504101c4a601c1c06256840d01210316540060096510035041da0b0020f250f000070f0741c6242c140c80b240c100c0075000f5690020350f40f4203440049070180b4150b01520881280e43c00240c400136406040e00e206a4582c01c0000d071071480c0b0f0300030703401803503540f001c10341c0701e040a10b00c50700c1c10061034846039a0402e841a42800740444078088991552171035003048601c080c1440083c50000b51150051440d19105900e41d01c1041c007100c0c4020100c0000748080c2c000550300082c090150013030200311003808042004c81d1145040715940d100840c140a0f903070340288004101000e0b120000081c000b00c45d0070024078058441c8005100140028450b010f020382e50403c3c0070f8131501100c005c10030004110001e5143c4042c1e4100e0007103e002d800b6030a44a940c045807102a4207402c03200c0e0031000b2526a0080c400c0041c0b645400387c5800c421200b120040d8640351000a640c1 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 164367383 1250 164366133 164366203
    0x20d0515090609070e040903140705010f0c021b12250303030b0402030402030d0e0609060d1d0706050304080a050d0501080a02030c04051b070606030503030c0c21161b08 74
    0x15070140c840142c58545c040c10300c4003401c004041601441104489018402079980003071810a00c11800000d0070ba00c101303a50b00440d0030641d1030004661001c400711040c102c3c8410351030045a004c40396030010b00305075a850b0b840e10741c4004400310700c6481140c6001d00f8040c806404400e4a11a86050180c8030300039003400100d0204a9006e540366200c117080c000d105025509400c16180d026001e107181070324450200b04540c0c0102c0010b0219640c621442e00e00030700d40340203681400b0741d48001c0c0c8102d40c03522000030018000604094030a0000088020700b403406401125600071507600280510b41c3d40358640340d11101044811313402401000900c1d201803a10f481083d01c501c4981401d142002411b02d80c0501d6a0030136802110702598602010001c1070041026500c00c2020003c5559100038224000342803a05440c013040c0155501d00c645002401003a0540d001d10303d44171101864a1050b0510083ca8000744069001c003444040c404200d0032000300c4e41149040881c1020240d044124006581d49 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 164368633 1250 164367383 164367391
    0x4110405210606011b15091b14090610050f220503010518030f07060207020303040806040519030504051003020909191a0d03082d160509030606040b0103020d0515090609 74
    0x2103e40810300c3c03400241c54481140c521b5600c0039001680c26200d903114810801a080d0154460308810303030410002e5039480c06550398501c02d803404c29244c103210020030300710341c000b0007103005122003c54185203d6245905403508041c210110801920300242c143e83c1044850085ca0b00075402d0074000ba10206803680916044000c000c021485c01240180406440c4c100d2001111b03816000c118020142e50300f00003410103041c402c40034040c14185443d100340f8000307000b540084c0d20380d5946052404a0381010540f8103c9405507409881041c60750401c8000b80b18440d00a070b884110003007407141111300010b0861001d591040708012400c0715041e000aa01252020144e1154442c01e032940001c1c401c240240e0010821f000841244400312020320300c2c1c074501695011681158001c2107092032920b030030020644054202070f4034000714a8042600d914004201502454607a0403001123a44258101c030324252000307204000b181402c5801e81d001c20f41e1004c0151044900b040414180d10f058030003d801303 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 164369883 1250 164368633 164368667
    0x1c2109031d03070e01090e0706111b0d06050426040524070b0901050403030c0903020108060d1b0b03191806090204020d0204090203060108091b0411040521060601 71
    0x620440c80e9180400031080081c0503054000c4200019603411a0000c61340030740758035400443d072107120f000c80d64600500759100f401001562080a4600200803550350042072070040d00d00d01c4030100d0f2000c1005109801c0c0010b000c1c6140c401008184104280040c41c034080e0503082c15160030701806500c8450285008456105810200e25040301e103a0b400c84150340700d034030f072411420101117480b00b20959800f01e40f4000103075117034000c120406a01d440340c002001a181002402c003410350f000200101c1005181d10700a0100f04038050500820000718041220214040e80015031210902845500300b40e81140a9014507041e00018076054042c03518144014200781c002421a5210200540385c2a68240d070060342c208080041e2903114001840034100112025a40b414248001010200c0c014100c0800390800d1140101508408a40c452101e408940100b0303c101440c0031504203101e560300c601c0d404015280c0c5c95154001d10303030143c82c0032400d0b0402d4600f655500001903404030400c4885640d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 164371133 1250 164369883 164369897
    0x819110706020610060818010c11011808030a020a0c050d0c0b1003030503070c0309080a060218041a06090f04150806010b09030a060c020f06040615080f0d0c051c210903 74
    0x4a503100340350351b030f9006020342d40da6507150b8554440c9600b111483c01000c00011414200c0180e1040709002d8295a094a0a086401042c1030740301c0810501002c1e01e41d98036690001b92011f80a031040803850159030704001a107030b101d030003020050070080d15400c04841c5580140005a001101041c0d01c0084a80544510b0f00d9562807100899840469401c00c5090040d140c030040340440c030400410034014801c0d0401680c5581a0b29480c01c0c0040c240c907140e21483c2030181618013010441d011200c42d41066540c0c9448908003800110110000c0c616141c100d460299196007080080382c0c860308603020b08096a4080c2d0700c9558803001d500c58800000d805512507044000012440d47c00018081c106206880400c4031420b50f082c100f442c15030b000e135101c544481d48402606d002e604507030002c00e070b807000134402c2004100340702d6241d1f10b00e030030403406000d0b0418103007040c0401070140c244000386100c164a4510350744074025020310320541c02054a08d160039100c0d4081441e5115502c1c509400da2101d003 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 164372383 1250 164371133 164371139
    0x213020d06053003070b010f0608220209060409060e0105040605090312150406090c021b060a080109050414030c0610060807050714010e1603051204030206070f0819110706020610 78
    0x40d010320306155401e83d05200030010900401d44c0200014042e000c01c2010100b000c0c9400c80c020a1031402130b004410040c01c2c440d00b1b0034070102c0c0340301c25040144e05403641d1650b6514440090b00030b10b81001c006c3c20550400007104401241035000074440c5201e05410425030710b821306d90070742d00d00444000a00000c02c0ea4003260010350b00110344500340b074008001041042d21160700c4425508020003180141e0b1041c10017040110a01c250f0744a01e803403c1d40d2141c140803c03034000030a00c100600c2010b2005513981c0229040c856070600c42c0c080382d0f00b22401c403540d03170710705104040e170b603007811642120366121025020a00728844d84249014101d65940d10342091615101c030800500901e07200151590390303c013161070341042448850a000c00c0b000259000c0381c51400c1440c201701d0107206c0d03070800c208104000d000580d0340a06490b44240c004009000b604000d14106506114044040b0101d4210854000e64580d0040f581d0380040021001d40da0308960310310060365269026116841c20300e001c10710034 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 164373633 1250 164372383 164372449
    0x2a03041403011b0c1a091902040209060a020312100f050105031f0605070203060114060301120c0b030f04110a030809040e0c0d0309240e0d0f0213020d0605 68
    0x4a04030020040c00010300d020b10502e440c0901150f0044040400c41c056103040c2485030358100002a007a00007000030041c54010015a01c59070000c070b5882c507200e6903420b450255251581910040076000d030045683e812031000107944e80d004245002c040c550214000b40d000089410b40348110340d148000c60b00c949041c00019992508004c200e0010f8000045072016442c20340500200205803507220180c0e1101c1c81d005160400d00c050300440d182d0441070810050f680c950fa002c4904482c40842340c6101c1c50441d240c0041d003c5969880004c00740c10100c180410580c004900501031446800d001d03407420210f209120740210300740700183c41c07207030300f403001100741c2c00d0541104403419402ca00f92100c0e143c13480006041e29484c10b04c2a000904200018030440d01040e004604444080000d10341010400200800740c0d411100814080c01054041608119441c00b001c540d05500904c14051a2403840500b0020b41040d8204400a410180d0010302030410510307038000d40c41c8200c036180c0505103501c01 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 164374883 1250 164373633 164373659
    0x80304030e04060603020301061d09150102100204230301140604050a06050607060f0518030d1505031c030b0d020f0603060a05090c0909070f0c03081b0f2a0304 70
    0x360203104161200400c0c40e0703624800c0401811003504d0041c1c695060940081401da00028003060074180000c0628550741c400704041e078000202075004210701d0111004030b0802c0c20006001c21420300105003c00c406908055000c010707030089030102c1000c40c20104141c241ca034144101e401706444180420310504254101580c84001d44030046819035584012991982c082c140c243c80e61070b6145004507024100d4003c80c1c0d0004120f01000221020141c0e40a45a1060309103a00c18141d54400c184c00d44507020400c08010170300182030320100d64840301d000014080343c03942100060b14004104007541780103c202108681c0107007412107103042d04000d00076164400b070003196015480c038500242c1d5541e144001072051000c0c1402980703843c0e41c0010300466100c09010070060100028403180c1d0940d0216180e40c096403d45044074250701c0d0f4109a0a001c0f5142c0150200080005007826150054500603d501c0114052089031028a0107a11884400304090290035402c03c00041112080c410b078 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 164376133 1250 164374883 164374891
    0x1005042001050f07080417060105010f35070906050f0405011809020a092102090c0d06150f09080606030a1502040f03200f0109060c0309050901030602040e07020d0c0803 74
    0x10018544031110460440c0303504094011100310900240600c00c0c02445004d04240900c400010402035042c83d0023307208500001d580c000b000040180e213611500410000c070b4115104100600341000d40118219405400310b8402c00420358600c40000d6691040c0100c0700c207140e8442d00740307040c10b084c10011a204451007000e030b00d4180c030300140480e143c0100e2004100d101000d0301c3e001c0700300d4078015001d2740700000d100c120501d1001d502c0f8083d000d07846003004140c0c420400300d041d0703540340b04d01c50b440b400401c45030700b021401141d02003030440c030107800c024208030b04069516051001a55003101903034900342160035980642110521000154031400d00c06882108284090b0405448401820316103010764001d941c13a410320b030b50511706006084220b030441141550312110443c4d21074000382c80650144680010420200350000c141886500b22301c0180400414103641d55130b403400d2450182d0014042e14500b1801000030a40041c0000b480d501c4e00481c0d519000c0d50564152102c0e01c079904014 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 164377383 1250 164376133 164376137
    0x3150906180c2108030f04020a06090e0703020d0221060a12020303040e041718120a0b041e0f0f060b010906020703110f2206050d05030d0f11070c081005042001 70
    0x800103000204c03124040c510424942030901c10034a81401003080a8038541c0c0604180007a460003807011002e4250301c3c0d94440014100942d4402602401c48020f2003100e055020290980098182a500d880b17151801540100d480c9411107448900d1020790600341c0b1402541a8404c110030860f840003001b656070700c58028a09000700700043d804c42600c80c0c1c0720290307103d240c01004100c901c1d0f51a2811064070349000c680f00070700c0112000d07900d240340014040d101503e248029030841000900a40c540280d80c0da01c410174118015592078003c03403a00740d200007120038500b4809078030803e5102d021035500f118a56402818454510703155110700b1100403a04540040d2203480340581d907203403018401c1d44804041000300425007083d0000c4202c43d03413604004d00c61000c040c928404514000b059840130703007240e1b07800192007041c28501c4004011400f811002200c000c2030750000e00c48428401021a206503064419280d03e09002c48221841124014211810007481c190004525400d0192085041c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 164378633 1250 164377383 164377439
    0x4032316031803260306030a02011202160b0103050601080606011409030c0d051f110901050c01020904091a0105101d030f1605010e03030703020c011803150906180c 72
    0x10b20055010070640040c1d07049100307806a03c0c0300303180204c1441e00c1800e40d441198258100348001036190910020040d040113103032003034a0070030030341ca80c125040c1c09060b43d5010003c6226240100301d80600748003daa45d4010000005503c4002240844c07042105030344015407180101070300c5041d41c120205154162060b042c41c000591120f0ba0a40e1240703010328000c0c1100310049001a0181c0500b02e0030600780d030300f0100c040c0c42028000c0c040e914207680908205840309500e00c06180203015140009600c203081005000c10720052403400709140c2c3c418081990a42e0720b46042c000c2e01c40801e8004030014a0712000c2d00140300311840d03010020304008090f41c00070451000e400c0e161011044042c0002d01d0300c414200119a0840260b01071000d0650107941005590b0703e000c1d40310340a01d40a6414012040b544d00f002145151405010b16444a6a82020468015000014084503004031899450403d0303240007180303102c1001e191943d01000d03d007400c3d400c141141c00904404c8107035201e601c80d0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 164379883 1250 164378633 164378657
    0x901020405032d0715030e1009080406080a05060913060f0e06070e0a0e0a0507050705030703120c0e090402061b1014060909060c090a0509070201050403231603 70
    0x14020110705150f220018030300c808000103814203810882404003140da10103d4200440030b01c01d50104880307142c500b4005544000040141e040960000201d5040c80c81c126002040154140290040d5219540e580d04260b0701c1c1481c02045a20aa42c400c1e4803c81380300010b50084c41d00d03d20010154811680410420070341d6048005985404a101401ea045a810803ca01d03a10003032240202000301e81a0b89101d107404032a40d280140602000040d58851002445103801182121091a4442c048942c2e82d4098200203040c140103484070099607040c229150344080c171880c0c1e0b05e035800301c00412040280c1ca99508102c0160b01c07000200c0f0301e1100b5030200c4000203405000f1003d00c06441d000c00f080214040500d00c05a5000809080c03140480d4014086550b40004000d41d02000a28041c0c0d51600f001d40099480182603100951142c0b2400c1005202c80e41900701a0180d8030a4990a11000c0c03200300301e4140758448148600c00d03c07401e102d003002c0803030b80700c1c81140114001d060001e41c10407 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 164381133 1250 164379883 164379889
    0x60c070606052d0103090209060906030f0303070f080f0618040309120c0302090105060a0801030b041a070e09090d0c02090a1104080a050d0f08130201090f0603091406010803120901020405 82
    0x4020a0003d00300903d610050742c1c04480c0a10144600c9001d107001c02c030900485d070010b828039134007501841c01912401c1c00601c25840800103040c0d01074030360084035101e10301500010010300544140d2400501d0f210b0109200c00d030250700c003600812000301007424420340100d02040701e0800610036410031180140004481c107501d9031985419004a801020040c00c0d801031011403081a070002c2d0040d81d0030005510741540c000909419a07500c68601c00c480d4a072420b103a0525061006011045034911003406045030b009001d1824811003514500559a03903121940c1c1c40d90248102a40071070240b021690041c40c2c40d10316198440c21100e40082c500ca560f82201030740760001e030028100b03907019907600001e00c6400c000d0403007025850314103082c00680d0081e00901c0880080c2112002800321300d404e0045a000302d0101003d002100b00452400350303030b80310060150203551003d40752540c0d5100d542510705d1010030047c0c140e9981400441c030745005100b814010b040002d1120605560901001c146a5 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 164382383 1250 164381133 164381149
    0x60b1008010b13051f03060e0f0f0702010e01021303050c030718020c010f0c0339080702031b010515030109120c050703050304060f1b0b0a0c05090a030503030a05090f060c07060605 79
    0x1005070380d0b0007842e008030107101174111443d070f401110b15007008c641000280c1500c00d80e0b907980110f1907444402e240e1503d080a90140102070f03162502c5500125020703014420b01b04201088901400484801003075080a143e164000c0340100d8404441c010361928284540f500102040180c103000060703900700282a4030112600a03507581c001039114109e0a40e400700425044548024a602c03481c0c80c945040411548105402c510f1024400d4820005081c0f43c020701c103031078081e4807101100710a062451402c6001303280440e85410106100340602c182d50030144101044a41d01c01420b1100d009291425a00b03001800c03021100d911131807001100245041c00904014100d0341c0325042442c0c6504000341207211000d07040c410328900d884445010401e080c06a980042122900040039400c1c039038216003510819201c2c0c1e03007007001a0000810408000001d51103142c00103010851a103441701c095440700580d00d1034030000c1d4020400300d00078a40f5000109040361082c440021188d82e94804200320b8 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 164383633 1250 164382383 164382409
    0x62304050102030405010b090702150a0908070b042303031305070512010c080114010e04090201030f06060504080c0108070206070e011707020a020411130306020f09030316060b1008010b1305 83
    0x580d401005020170000240100e0001a4007150070b0300c0703d8130b4903a4001b980c600360031020760707010b800e5000424110105503214115144e044048180e5900a90404596441c07083d03600310380c9160360701c0481466550b401441c400551401c2c01841c076544484006c021001e02400d81921a40034034040054151b80f20945512104550800450148034880001c0c0c21960160b001c1c5010401c2407440251580c2d000c0d9121a440d0f60440c4d001a41c80020700048000740786240324848180c0c540000800c42c2600100503104071001001101c0480219000440300c69000b074500001590010f0301003070005000c1d0501c200306550600d449103817403048008516031944190f50050140e04a41040c50541c2803c3c000d02042800c0758940e58a03100d040c2d07030051178001e2148000f4204650119460044140301021208261401002c590b1114429000110180042081210b01e06d2419140b0a5a420728051090203603070903403112100b0381c3c40d16040000e0366000b0f001882c00111200c0b00801c1c0f07560385840304000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 164384883 1250 164383633 164383643
    0x403061a0405241f0302030a0f020f18060f040e091002030f0115030c09140a0e10180504020306010303080727060f05120103081b0118020f010813062304 67
    0x825640307541c8110108403036540300c1c1c01580890a00d0201e100b80c0382a04c000e0300010314005070b0300c0c0e407881704070001440301401c07411159000068001640c20200b004c0e06254142e1340410001c14510801c200c0c607031050741c1140b5002c5c00217202c00c200000121814035801045030050b0b50101556001610481c1c0c0300722030203084451107a0041c0003400005201a18082c814101009016050720010700006c0c1c0e00d04c0740841c0401000c4000003151502d058a80040c64074442e440742e0b90512200c0c80c0b103110264021800d42122404003651008402d00a990240d90098064032640e401c546044030780c0d00c00184418180424409098a131400c040b100c1c03480032400100710380d94541001c00003012010200c905404005003480304101ea1008145800c2c1100d911541503540c03041d24075848400010303101300e040129481c0441e19041003499101d0505401e1080f0703044002501c40c1001925076560960701c40c2810341861b030710000090060f512021400c071003c004101c44c60b0000303004100c059811075086030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 164386133 1250 164384883 164384911
    0x3050f0708030c0a08090f06010905060d020d05010c23030a0209010306150c0b070f090b1b030307111203010806340e1306030305030f1005060a03091502040b0403061a0405 75
    0x1280c4ca034044011a00050060007518154490003107150703603a0418040c000440c2d541e035011510903980e1100714100181d0103001d0288840007400d126000b0701d00318809002250380701c011400d808000c1c201140000001c2800d0504541304c01c10100003d400480d04181810355400010820340c8810381507040710641981c501008826610309411000740207000361003031040d00c03641d000e1507c0c9c005030301c481900c00f00c00b0110380340e0818050340c60580480319012410f50000200b406415540100300301882d45420080f50b1003404024606600740c403003441014900e41010002c0340c17416091350441502c07960840f02d11b80191410500c0341d0140014000c2c0c510100e800d54503880b01604000a01c407455403117820080000606c1d5440240c181d02c401003125042a2811001035000708061001c1801740601800541c2c480d9078400c8081e004103070351201a80e00480c40200b502c1c8a2142c3c3c0200d405584c410003903d42418a165980d1001c0c24a5400f90b400c030060344c0010101c5610389100f00e034440d4160781c41030a = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 164387383 1250 164386133 164386147
    0xc080403050318040204050d02090a020702210d09030b0c160b0705091306050607170c010504110915060a050d021c060e0703050702190303090b0a0e070f1203050f0708030c 75
    0x4101c219141c2c2c18000d07401404104015915900c10a2304550196a000e40c581d4074240709030000d00c1500c100070745c004c3e41407080031440490b110441e001e0458030f508903450003800e10026580e010b1684402000c4541040000350007c0084020780085043d0041e01c41003030346903546408184e042103909900107840802c03038000750300c0e000d69942e0305810580c0d010443c280c00c0c0300203d01c1502c20014050159444142c8000c2801400d104079001520703030b00000c01240c1000c1c0303400032042d00c0034032940744105c80510100d00d500302c248984c8800c030f600090025260100c960029503c40e0081c610b951800d03542400903c00c0d080c3c1102c80d1410450701717003800058150400224244000c0c002e8031a40815141004101c005a00042d01884469550b0038071000020b103483c044001d48200c08004013070210030030a00011440c1c641069035103180550a0b62145034462101c0120900e00d485000c4110588842e800c000c46d010b00010000c030314206030500e280ca8031948400c0417130b60003510b480c510b1170800210b131 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 164388489 1106 164387383 164387407
    0x305120708070606060e040c05031e091e0706030c020a05250b0a030e0d0e010801290c0309030106060306050d1b090f02090307060c030801150c0804030503 68
    0xe104c010b80b203100080049a61840300341c00f550800c0b184107091400381d0260303889200e09415010805000300c00f03e0303020100c09410b41c840e9014001350000a00c20002c0901d041c032090100900905203401401021591411001001c5405c640703048800690045088040c800306004501008028000c00c9941880c860340b01c4040c144000650300e0001f0340541103a18040a60302c2501c1c40d0980c0b100b4103443c00c900c04a460b40c00207111000500071508407143c20b00300c000f2480018488101d140e805106580e1015021001540c4080307400205031809004640182c4821310301031000a00d407901150f11201204001030610700c1041d0383d101d241290b00c658100400a04006104501e00c103080311000f5809080c4050081c0520200400d155004428080f11140e00d50b941900c26860690082540300c4404015007c001506014001084400c00504003942c0030b00c02a5940c3d1500b2008 = true := by decide +kernel

theorem cover : BRFrame.Cov 164208633 164388489 := by
  have h0 := BRFrame.cov_init 164208633
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164208633 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 164208633 ≤ n) (h2 : n < 164388489) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
