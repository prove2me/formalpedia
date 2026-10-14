-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0736
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T21:29:25.454848+00:00
-- url     : https://prove2.me/submissions/a1e8ba2f-6303-4eae-b474-9c5b3b24ff44

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 132194244 ≤ n < 132374100 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 132195494 1250 132194244 132194263
    0x614130b130e030409062405090303040f06030c090509060a0b0f07051c0809011e020304061e0b010815030c010c110907200c09180a05070902040f08070312050705 71
    0x28018002c071828541c08540701d0b80684110340322103282140003d004009110f4a00a000319842d01c030040b60099803042d0f5066100190150b03160100704008100007420078500400b610b015580002c00507655a03007d01140504d81000d40b08440c49000c1024036aa1000c10030107880c0300740440c0e07854180135a414000d40c01380010081a0340107018914540381d04148500000840b603980c3e014581d11490002d50072500c5104a9144030440202a030b076110303142da0001c58000d0702c02c60340014100010f0606042807a080700c0240410354480e08600455a4030041c100c0e00f05070422524155101404000ba03960a03a880da000c0c14000120b004100303011080713480e0030314035402600c0003040707140c400300051840b10740c032040d41d041180390741c904e0101d550b00054403450038102400080f01c85c0c4408a9030740c080c000410482c0d0040c071459411000140741440703c50003c01c01240c02680b100d050030f80360940003015400a104650040c0d90800200e907500c055041e181c40d013400d1a90307880700a828a0741c02e180652 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 132196744 1250 132195494 132195529
    0xc0308070b161706040504080909090607030f02040e01120f06050910050a02030601020a0201180b0c0303070f050c0601030213112106010e0102060109050a1e0f0614130b 74
    0x1040c000240701c008400c00b4800c1c0c1c051600c1c1c20b28030420941c2a20032401100e0a4140c0c1983d0800262490415601181d04140100d072041e0415041c40000b1f50031507030840302c04140b900044180414141c15016036407003440311000035400c29043c40c20340081d400c1c0c141310b000c488860782c20b010418440700c2e4072100402d50700407c0510a5242a885140e590f0f03200202c2e801b181c0d46480d00056445c00c06200390390180c04140d020707119007096a001150010b1b14284034a8014000880004016420034020070150b002c810156460b4900840c02034140a02c04010f401405000c0006006159000c00c17128152076040743c002c014015507510314001040350490900b0000300001d48680d600d001c2c0415800c0003210101d100d040c0f9640e14004440e0f03e0404114180960f008000621052141d40c002c2680040440c2000540140003683c28290744400c8611001480c1e0300c2d03003060f41c0c45407170303008250141c40000166a65058000040742d07260410a400c40e0a9036520302c00542c481d540c502e12601d004071407 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 132197994 1250 132196744 132196747
    0x5121f0308040f0e041505040305160609021c080a03020309010b090108030304060501050418021c06090309030b0a0c0e060a020f072d03030e06030a06030c15020f0609030f070c0308 79
    0x140c1c60400419400350180141881c1030f074400150841c0440c51561185512481070b8407207000c401ca049000d0320001d00110144441030004450049030100007030034040c000d034000300705021240140704140a0846840100800e8564440c1c0420104800c4495144544c900103a07030b50754003802d0a0040c0030342380000c1e41c8030401100010780303600000080c500907402075000708a03d0b60303a0030811085448001c402d80382210003d103030300094500031307403800347c0e8240d190908103019901c2d07643c0c1c00c1212030480c0100d0100d050184240140007540c500940e1182c45003004100f036500c04500030340703019840001d991007102e000503c81455031080c048036080d868014101e51103507869040001c0c00544509404200844d00307522500d03e004a49106401c0701d4040c0c80747c0510124081c240451684000e04585185869a00000c00202100c10520081030306440c507803541c0c0340d080002424912411a8401d10b039100405200c415580882125a4001c0c1040f02c01d56900c41c600e081ca17003440c020750001d0a803e50 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 132199244 1250 132197994 132197999
    0x1407050402180f031c0e0a0308040b0c0d1107030f0201051b0714010e0f0904050a0507180c08041212060b0408030417060403080604020d020c0a150e070605121f 70
    0x440d100400710100d518202401c0b2032018140e603071146500c0070869a4521284511702400741d40420001507020b070405c0c40041c4c0300c2d15141030540c0264001c0243e4030000a501e8107285060040c600650b10301d281807841c10416900f400d9035030101c1d0002400582d00c8841e08401c41e8021801c40e034120450315003400124071500d404030b4451015200b8540346140d009448052584100480314580c00c0042ca4512440d062030b041c01268040280200c400c1e01c100000e050206a0402c0050010700c02407182c0d015170f1603030202003016112038260101c1480b00c88014031000039140000000d50101398a04143d00714242c0c1007940c00303403840f5400110344072070010b0007081943c0b000c4010015110450781100c000c0c4401c15074a42d4859040390003600145a000100b01c06181a400400580e00c0d01c1c1c0700541481029524141440a0580222a0090317030102e600382e527032243c1c0519554810500080c1c1001450032102600b203104407150079242501060004141d59031044403255141d080d00003081c90542c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 132200494 1250 132199244 132199267
    0x4050601061409090a1d0708060c070c0506030405010203040c0b0a0203120a02040f0608010302031b01050409020a090906060e0909010c020a03050304050708060115120203040f0f050a02060c030403060b0303030907031407050402 99
    0x40e818409488006c08a00320400e444c800156400c00c90300f10400401b42c40e96241e61100130ba4000040845410a140d000002c140d503956000d94050381c000c400059580c145441e02c20044150341c0d011520b003000c02c0c400301440c190044161012540304c03044641042e0354418142009110b16004500e4000c410000459402d9100543c203042e61310a408030781c0c1c3c04049419090403000308007040390000710200700a01901c1d038283c0107401c0010650400c1d1640a0f1901c0600c2d064030030540080f000a156003070b100d1958540a01000d40294500008112022905c0320007521100c44c41800740a01000202242c208901000784400030804541a01e0302ca584031000e0040d540c440400d03d5000a00341601f001c101c005038401c40740503030f81c401d50211000149584802942061810507600ca000303980000025880d980001d00d10b101d014005140e50354210b00c1c02a003141c0e8140c2d0010700941c4203204001c0b00507000640d8800ba02e400017500849025141205444c0441d80e4104903040f90000c580c0f0005803 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 132201744 1250 132200494 132200501
    0x60a0e0408070f0210170c07210507060609050403030b0409050c010e0d0f0303020702120f0a020909010212010603060503070b041802280206010608060d121103090d0b0406060e04050601061409090a 86
    0x20401d02411007512a1611f400c076500681501801c140210000d80e04840c01c0400d022688840904000742498440d440f8001155070a50102c105d030794a0b4000c020405615208000c072921045a00304090700c449c0c1c03900b03a9180844841281884800c040c3e9030001c0d540c40c1c1401c440c01d0b601a4488000840f2803070020081c0d00840d0049006030010310b0561020b40303012840c5030070510300d5401422403c07459020480103640c0580741a015540c2000640091015040e82c0c03406014103840101705545090107041c6084225030000b26061010700041c000801001d0084810302c0102e040580c036048164113000c80d000114908030400d203007051701e031908560081034843c1200c202d52075103139196484109110080786030b610002c00c5180303140c61800030103020316541d5480384040c404803800c004d41d0344003080605c4e01500041d980a00400d0402003000024002d42c006444101d03404640d40c00c285d40c0b000d40d1b5403410301400090007541402039012240120607640d00c00c500400c084468182826054000d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 132202994 1250 132201744 132201767
    0x22020d020a031b0f080a020702030a0b0f0c1c0b040e0a031805090609190e031216020c0d030e0d0c09020c0601050108060307170c040608030d05060a0e0408070f0210 72
    0x443c0c20242001807204000c40c5100d10020f4a403a140d81100b2003603030803601d00f980100601c10882d400c1c000600135807010000042070074855101d04002d81061010358450030700003080c60f29490800c02c0310045a201c116103d0426003042c0b078001c9a8401011300080241440e9020140d40780f048641207402c3c1603021942880d440207080c1140b1203103444105000107070200f116050b400000e000c000c1071810203500c5c4c1031925511a1180001c6404411341c2c100d085503c030000782009059844140224034000800d81c400015280c0000c05c10316080c40003145501400315405418448001400b410548800f22403030301266108040c800119103500d01600290050042c0d40300500c07500380049042d50080c90418028070004000303050b41d52078860f29001101240040b44043d0056410741c484036100c50013081c0180103001d0145866400708049841243c0d0000c001920851220a0811800106224454000c0c0c1c20880066503288182031554010b1582280250070142d40361400805640c801090700c00c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 132204244 1250 132202994 132202997
    0xb101e140103020304080406200d1710060c0803100f090212070801060e13060914160503060901151107030c090b060705030307030c20010504020f0103140622020d020a 73
    0x900c091030011400c80c002120003c008070305c1000140511802040d5911070004000c010a128100c4c0143c034038185003082d078160012498884104103062024a1a0b0b640401754030150010140717008001013510042110241601400001040341e00c421080804060000a03000b4000e0542d10782a000c02584843c242403400ca009002003240140301d0300f0354604031398082c1d0359902d040003564208900222859009000d0036581c0c003000030414100d0241150302c0425030905021440d040900c0c806c94006600c94004006082003003044a503950148a0b05507414101d0b410140e90a980c0c054031125500900740107280b0401000008100d0003401040135600410400e0204a202d5014820300e4010004002c2140e0000d200080070b1600c84da01c41d00001249107050741c0040c00755080d1856280703546e40609100e9442c5d0040105600300145523070000c030401c0ca4200f22045110400407118440903100300e200d0700300c04034900451b03c01c0c0ba049110812245400f15551b0b9001e88581d0020b40c030841e01c440 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 132205494 1250 132204244 132204269
    0x21908010e0601150f0806010e0102010209091503060907120308150d06150602031303021c0b091c0f0507020409080d0608010e01060803090607060b04020d090b04110f0109030b101e 79
    0x1810144a840505c04406940d159418035403901d20055440c0c20075900d02c0ca04641d03092050700300710b03902c4000c124020420310610781c0300960300b1000d1504100703001308039620690005d0810400d001b0956410400d540d0140381c55021034075003000305041280e01241c05039000504a00b12420f11025a1010b28115442c2d80000c442554640d03003a6220700a001e6061140030341c050381000035003009114045030781c015111411103900301d555503100d80f02050725510195400032002445c00c00c1c2d481d078407540d0f51a580c2840443c1860f2070100611510806600038026a2203900d0502003102c0d030b00c03c1d21503540c2c613108188001070721a41004d000303101c0841965055802e1200018a41c140032003140e80c0d121000c0c000d180307060803079220340340540261484a60441d500f0015007284490314401c0314212445007410141504080c00c1c0542d10301c3d060850342e88a0480c0b2407607110540c0c1c003d0b2880048a9120030113600c0c0d542c8041030304200800d6035102c1815600f914100402184400315140c042d02d0700ba40044 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 132206744 1250 132205494 132205529
    0x3050106020708070501140c0d020a03032d0b0a05060c0f07050a03050303070503131e0308062e0201090b04050a02102102070623011a03090307021908010e0601 70
    0x403a550b519a00c034260f0250004035003440f42d544510354003030421603034051140c03500d001e00c4402c502c1c0c000c81000000c016001400400201036040c0103080d212036150603524180c600850004001510145000c42d103a03131758a41054403615502c05031401020f008000c0c98840079445920f0380c45020380000207035240901030000c1594134084007040e060700c6d0000000c609669034060300317885517071014049500c44101c0c468014009590b508019202205561000c881d41c446d914020b0084800074103c6480345c079090805181041d03500884180c10b140c5400c0b0341c0c0d0181c1c00543c00364010490f41d400901038007801006c000030f005000a060410510a6a207403540c010044400c40d204180045002c403a80200980034144140c990003500185005220009855070203c40b00705034210701310fa460001801c9500100001d000456084007041d0300c0c01380080c0355242042480c0d86a1280400007403268120000510254554a01c8000075140c2c2900811203e078240134440e544d800d09106052812107000c1c100b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 132207994 1250 132206744 132206747
    0x1140c03090c011d040203091c051903020703021209041e0b01110f06040f03120504121103040513092102010b1f080601082a0409180203032706070503090103050106 72
    0x3070ba40040704104544048154020017000e9800603028524601c1a1002401006001080d009200c141500ca1542d20b00400c2143d030b007114a101c16000c14140306216403c04241c0101c3c0b03400040324030381e03a15a40c8104801c00280200262400c11040302c161005114117082550f209100015090300c0ba541c0c0382e84000d071807945d80c4504010a004da03402c1031021500207100748140c2d1140e03038424101480c0502d12410300c001180c00c120ba00751048000180f65190480d00000410380001c0040b000d103280074100700104800c17402d604400002c903959941d94600384420000d10381d00c076503c444008017040241c45002400381c018082e2030742c03144402c0c07030781ca4056408010070241c110302d15489600013075a80e44015907072040000d01c0401e1402d40880135241158460400420320650000c07010b80380c4d0b04183d00607049440d0250f1003002d00480b11a41e40240c1c1c0c0000964848a0303401e000e08401c4400303406c910740c00034882020181c00c4080031440c82c041210100c007030000507000380c0e02005582e0341c8580 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 132209244 1250 132207994 132208007
    0x18060f0f1208031e0a0b0901210803130203010c020f061003200310020c0106030507120804050907050702030610030311010b0604050111011404080a09142101140c03090c01 75
    0x40d424856540742031072030001c2e40000c00345a2000110808040056600d00726110f842000c454079484555666500c1806180001c1d02d940505a0200180c0c548040c00708494542089104040d111f1034001c00010b2680c8400c9603054031580c1e01500910800c491100b0180d501d4000c03609911140c06040001108070341d01500c8a0101e9811480251604d0301c080c6410181c4600101300355054055001b101900c1410b81c0010940c6406400001403000d2860422504040c03403900b1014a4448414175135000c200783c9000d440644100301c3c0d8610864960318010f44540c465480000e4240c09800100034000e240b003440c003421a8066121502d0a100120742c1b54200c4a450074000d5010000b0311040c400c952049400408407060003000081100a05100844004084600301d80710b40d0300054a42c441c86e400000c103802424581c50b00652043c0c0b03c00018020390031100e0316680584040c810b488182c6094100c2c0c1442003862100b58514140b0109a0035154400c80ba420f00324492600c4406c07080d4440c40 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 132210494 1250 132209244 132209249
    0x6180e0408091e041109010912050304032901060f110f0a060c1704061a030f06060d0303021b0d140c070b030901020702060a02010e100c050901140418060f0f 69
    0x11019440e0480c2e400401c692219500d41e00c2020f40061442c8684948813486045141401c05034040c1e01c610040e17000500c03000c943c0d00304405880050100800080000041d07500780c0c4c0d0b12200e1403000c6494000c400d144001c0d10312098003d900b0343d40c000035516030800314040340c00c2c6a0f95906841c004090500e580e0b100c05c0d40d6428284d0b90b01c4061614041101a480010030041610340555040e18500400030560740c10381d025a6516603428074403030034420000c0d000000000960107422110a841815a102c8500501c101d010b80c444503854400c052180d4100c0d503480403d02c050401c08208a120507549010030801c1034045040d92801000c00704800b400c2e20080380050307004141031803c1c0712420843c2d41010b02803422941d020700c22000103070748020180c117803070015a0001030206401001c2c98a08091113516201c003074540006072003070550281c200d8581910a00708414410705e00c400035051031217583c1c000c0f401c0020302a150388400e0400c1d00b1050849034000e084c4010603460b1842d80504001c44e1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 132211744 1250 132210494 132210503
    0xb0703050606070203100f181407060c050616020a0204090b06090f0108030a0e031011120a1a09060a030b07050a080a141b0d1a0316270b030706180e04 66
    0x2c00480d502595a0707001070130309020400012620134880705d40b1a854403006d0204483c01c503c0004024800c49c1c2c00c001c0a0000c203000d2510102080325500c0d02e544400d00034014041d8501039805d01410213001b0071841b80520303400341c41004964800e05000704a50802d4a000e4801d04401020a01d41e0f22110364541c10781e0710070b02c061464141854801e65100c618000d0884c1c050203030110000c02e41c81c241c4500c0003018070040c0e081b550f80141c210241e640103002044101e0b22072608821855903980c400c1c00e2001203505645044c1c142d15114000f810b1203505601c02460744000c3d5003004446907010001d044540030742e4644020315181c0002103010b44450a488401c030200d6000020020400d0641d507450040140300410710f0940204403141c10360300c00601d82c0700402c8007081862681e040070841e042c01d81c180e440c849488241047c14004885d03544004084c42200e404218a444080540c014200c102c0010212001c10f603480c3d401622101c218400245107902c2c4a200090080007a040c46105a610 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 132212994 1250 132211744 132211753
    0x2301140c0d0b0102190b072a02090711070f090e0f1207140313050f0612070305060f03031603020c09041e0804080f0703110d2402160b0703050606070203 67
    0x121007004008000c0b003031103181148515011005569002d450000c0054014508007820380f40602014041c030f0090249490710410701103004200120b41c0c40e900c1c205540c12100e0340c1c9683c4520380d0845d804030041040030218010000300054000f0040f0200c021200d8140003444000504185207032035680c1c0c0c2038014869040b095010b8a8460511300074800d0511803c44500380d50301000b4050b145400155103048900f054010602c107901c1c00b440810700a840c2159000c1c60582d11443d00c0e40c008401a24413800d0603207075000724103a995841403680c6032200240840391141554044074110710134100d429405405110000e0402d42820b6410b03c1c480c0350000f0036a901034004c00556410310704248030546034480140000306010100384a0560b000c4100d00040c0520350071810030100404410610138411404164080c1c00203031014149001114210804c0700313040c400d40c009030040e10418851403290b401d6108103104218110340c04600889403950f00300500c4d6030744410f10045100c3c0c1440603516910 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 132214244 1250 132212994 132213007
    0x240e0c0714030a0c02030705040204080d030504060e030c01091b050904030f1e110f01062d0b0a09081005010b0313030306030b18060a061d090102072301140c 69
    0x11404010580d061180034600c030001d0111411030306541082c1034440002d0480100705096280400a44001e890200c40840c900f41c81c1910740740d40d9800da0071a22007819290b00000b0700348040f0358410316075281d6030780c145d9a9840a102c6400d0007005403d80c111401c0d03840004016003201c0201005042c0d840240c501c2210362941d440a680344070780941c29004005220300f040a144000c100d5120320740c021070301c400004011100000342004444014607496070302d8034004214641c200018180c01c15a40c08003d9219240140e403410001415000301d034282d0400500c02083d1b0703500152401c11101050240e42030000c2440d40041030305d03000e01c221124448144081444216458a0b1072035440c4203040008080756a030742d40d1b0b1081041110f40401c90621031000d05500c14007400010350000c49135504100b000c0c10211240c11008030361019045140c079032800907000500135070444503416007200c054507002001103a502d02030465203490b10703c00d500b8503151581e85405140120b000743c00301c4414605000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 132215494 1250 132214244 132214261
    0x3011805060f130c06050a030b03010b010906140c030406050a0909050702060a0f0f0c03020c010f140c0a051611150a0815040902270903120c030606070204020a03240e 73
    0x3440984150a20201e5201c05000124051403c800903c5c054860b00c0d211180094050304032001e402c07641e8040d0f410302c580b144071603a0003415001600d030070b0f00b031444400d0704044e8410064021404412070600c00000c2c089003082c2c01c030b0003400385c180c00d55075040030315601c03982c03214151842030b10740001503805803001c95921b08164000580701181c2c1c00d000180c585904030b005081e154004036681c0420b50001d01103503002d0080c0544605210708000c14480000d40407200780b07103004010322841e4107400c0406c40c0c0030300030b07c240b04031001810340d00300c82e901c41c26485c2010500e07083c00d00788051080c0d03884200c03004000110800c0d640c0090301c5440d042d015070b480a65040007144060b684c0c1d80e000750b6401e00e1100681e10000606400700d00c0d18417039800824078003c80c5201d0000541007016581c4140b00c0e50f00c05801e480c06103540620307022200c607241c0d21a4400304016029041c0000d61044c0041030050b01503074598024100c03c88013000310320a00003d4005861005140c0c016000e41c16003082c0041d8406 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 132216744 1250 132215494 132215521
    0xe0d2307031b0c06030605060901090506221e060905100c02010905060d05040203060f0402091321050d060b03131713080d0f031505040c0e100e0301180506 68
    0x16030080c20244a502406860100360008449040f00c40b0f4400d0301e400e0000660522407200078000944040d841d04c0030141c0040c041b50841d11420748139540000f00c101040b0b2540c804005401c1031600d40d00c14a540f00e00c4061141d00c000802085c41751041c540001d02c1c1440f4256480807207801610070341858020f004110382c02240080d00b079050184401340020b0580740c8900512121003e0302c0b000965040c144101400c2c8007000c0c048140c46101042400050b994010602e42c21802e0cc0e030001407181c00c80c0c507085080200920307a8004040050580d6802c4540020003000c030181080400c00c107541d19014541482e020075201035101824594022000400001100c00d0b00700e0744160190520314400c41d1105161082d070410b45543e00000a0401a20780044079643d10104a04082c0304a4a0703030200708003500c4091103164481c030f4540300e440134607500660120740b02d80f20142150724000803681000c0d1181c2186140b031806986070203040d1501400c0341c5c034142d99441e4003c01404481d1a11700401440 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 132217994 1250 132216744 132216757
    0x209060d0506070c060f050405060112050f121207080f0604020a140313020108010e0c070f030c150509120403082d0c060609060105070c06120f0e010e0d23 68
    0x119000c840c4008900700300b00140c46040c40b60364600403c1403074980300081d2944448a84440e504100074400001c101103038030341c11364000e26411940a58503041c030314500101d6600a100c540128541d100301a61302000900c0380c03000b8a00c0302622503d55500c2100c0c228801c41d100b40d10b56903040081407451070550014a01844240b505c100c044100700460540c9034003e991424000c0c80508080d421541c02c0b00f00c15004052120a0001903d42129090803901c20924010010b581c240380003800c26000c1c2010b44490f5030480c06d1001801d0700b0b10051b4000744000d61f0411054030401404c4c250742c00d1010f04a0f000e8170350011900341040081c20b862059040780300b42c801c150b0780414419110340001c0d50003600b00c0c40311803401001182000c600340041c44002506a6042010030803003a808281c0d140c582c0022220903140c00c003200041c241c0303080024001810101e840c05d042150300c1128083c150080000100c0754401d0310005085000c054440b070840602600008030000c0d07100051119940c0500792 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 132219244 1250 132217994 132217999
    0x903080a0512090d020a35030a201c0f02030a050604150501020c13060e0903030718060516020604050a031a010b072f0405010605130902270a03020a1d06030c0904020906 74
    0x444648008909500300c54100d1f42403480740c0044100500703d140303801450902000d0207124000c0c0361112400107514030550a10200540490041c0c42111850f03a02680e50707111120300440d12410720b070038040007900d0150f130303040d01c69418612842d0003070a10120308006c64405800a082076120102440800145540310381c030040d9a46c2c0b400603503032041100c01441103070b031800031f507640380f500c0d01c17002d010f0540d80c0d00c21007940c03c43d850086c09010341040c07c030f602c13002c0381a42150f8404882d03c0081e03042c0c860307078210340e8109805130000803c008003400b0343c2c032040d1001e080c0055181c0c0c070b0740e000c0b00c0503001b01140540000741190401411052051840c018075081003125504a40d01e10041000d448081c2c0c400c0000440c00155030108500040f0f055001d0020b200e4194501120400520088403c264000c1040307400404c4240d0f0395552000248015540a402043da180e96291003050a08010003c080b003282c0c00e200145203441c003c652076030050f03070080c001c402d03a85a81c1c0030302c0040c2d50002c00558 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 132220494 1250 132219244 132219293
    0x1018020f030112050f0118030503091e0106030b010e040201141b010504032007030201050d0b0109080f03120f130605090a060528090803010e06010903080a0512090d020a 74
    0x22503000090000d501070180341a40160340768151601c00e140c50070f0f1480c458141d03490240412980c80352041121602601890300940ba501c0c7d03401203600b80780e0400103010750030f082011100d0760801d040d0410001c50380504501d41040e030380c603251080e1060f011603000303001941ca00301070124400c40401400e44030030302c0d02c940b1600703480c94034011b402c441c4142e50aa0110b0a5008940c48100c054ad580d4400d0b00341041c050503240c1d25560000c1c01c24001c15801c001020344030142184164030030028140180b0f0140c00b2950002581c0000c292130380d010b40b05803041400342c10001005085911601c5015507029411248450300d40d44460000303042c00b40100c1d005000d14241c1c2404142e00d40151070188041c580b082c40d0341c16400c0c14038a00f44082002e150342d9142001a0040450140e4007900d044810610a00c50143c0d10f1000482c0d11490329080101020408609610060b41c014040e200900e4005000c084941760104402d81c3c0341c2c5251280310059111001260000341d0301001026545288480700 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 132221744 1250 132220494 132220507
    0xb0a110706050d0e150f06040e060f0405010b010914060a0c0819030e0d050313020105042c01090603020f0114041805040611030708010608070903060f0504110108101802 74
    0x140d08044095000c100041e10208903511070300314a11980c03d594580c440107000c0400684040b0384211001031101d00b0004c411400250962100d80080c0030100c400d03070544000340307000f9942c1c480408050f0b078190b9696103442027801c41540150780c06019103200812000b03006c1c194030100007955100500c150208881840c031080090b031603c000d0003d6442030040d504000388154002011941200c1c0d007041c05a000c40381510601d41c01c1400c5a8000011303600c00e0229000360b000507556440b89502c10600101c2455280b50440301460b0301142000082e52001c000341d0343e0780d1035032041d04c40764007020798850611044407070158000d07440600c0404000745070f141810790f607048030b1240032003d46050311066100c9040101b004000c4c852040d500b0030401c03001d4198242500000c0101d8014000c8100b800f103400f021900d0075000d401e4950045502034000d0280206018400d4060311080d40d003121001ca8180c40301c54598014205903110b90f80c0c40d48800d04462401c01d141d030200000b0520b5000c460743c200300c00d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 132222994 1250 132221744 132221777
    0xc030605040f0e0f070b040e0405030412052a0612090a021302090103060b040b07080a030f1503050609070b0306060d0905070305210301060f0309020102010b0a060206061002070f0b0a 80
    0x44840452806100040068000c0c0403d414041070741c00c51038440e04903490500c40900c60380255402d4070703c0e0000104850303856160640c034520441d0420700c08444902030220401000040c5041d660605070018a0f218006541042e0611030031000310340c2c4581c0a00c82030592140020030164071005410441c0c198401d0b82c0c0210305501240d10040340c00d02d80015002d075503941c0502803032005128845500341b0705868070000c294640104400140390800014005400c640319800451114003803003810000c0301e8800205250000241c801118180140d100091600c20081440d104a0340c405940514643c0d40d24200038040c0d000a100e4900903545484e1040441c4003000501e000d54441c0307000340030705c7e101c0904040c96070300403030780d906118003042006012003036110303100000b020100d04011410043c9480141d0240205414840d0042120300001400355030000b00f640c090041501c1782c00e40c3d88018041282c4415103070144d2041300440c0a8208030017a200c0b801040110441c1c94a501c2c440ba183c0e58 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 132224244 1250 132222994 132223001
    0x21f1b030204090c09030c030204050615031006120c08011401020a140d080c070507050103110d020d050a05070905010c0803180d03020c28060902030c0402040308031009090b0a0c03060504 82
    0x10a00009a0100b02486642034500c00c0512408040c00d0490500c1d24640e6510422803c9002c001d010f41d80341c2c00851060749a080070f0b010700340307102c04800c0d4507450401d41d10066410f10b071007100b001440c40000e01c040410070f445003c0d820400c0c3d81d64280310380e00703080350726480c081e04072455411446602c880d000801c001604100c004814040500102c0da03905000a18a450180805200c0d4004101400020b600015041c5c1210400c0c01c1c081001040c070000070a0301d01682e2850700c110390000a6490301c15225a01039481807200e42010400c81c0c40c0d1310001c0f40c100051b40035590215201d0403031680401c050390007456005010080a04610b0307907001d000d03030501807104001c0700030039004600c90702c44500c240284d82060076245864985e949012541404010b1284005044141d03150010780c2903460a100d10000700074041d00039582c450f40c0c2e2800c5a819802240c908200040001012076644424010000c042d0f403c5800885c2d170742c445603030300c07c01003040c2d40401c014141da400c00007407140c84902 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 132225494 1250 132224244 132224291
    0x308030414210405040e06160f030b060403150c030e07050603150607051b010f050f03070306030210020d0e0607020d0b0a0e1603060518031b0c03060c0316050901021f 73
    0x48901d40307851130b050510059514030410f50308a81c1120b4100800e00c8960b0382c014000c99070b1403070084c400559216040d0021300006001070303000640043c0100911041c80b101d0306e075184008000b00407005049404400300c841c24500002c42c7d0f0041303601004286070402c06190088440c0c0030461700000440c0000e48654800107007100e01d0b82207501c007d90001400040422400c00a0a180501d03600c6801d00901d20301c034072021030381011300200c00300d10128480d6021102555024221682214a000001c0e40e16901c480076140001d40415800c0f800b07042100c1a10310712980a03003940741240b00781e9242e41e20303490300400400c00c17199941030800d100ca804100181c6e040700901101100c0d01e06605012050354070062a1414188120032a416140c2000040703c51a15403c030b0242d4a05403410101820b0207480101daa078140708000c148201c240c0420002e50066290140d203c209090380241520b550040865050158014008030350800c141c2c01b03842c0a400120440005101d140030980d01441c03807509 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 132226744 1250 132225494 132225553
    0x290309070303120903090e1914060f06120a0507110703080403030f05090f1c170a0207270f02070b070f1101060e06041a030304030614100308030414 65
    0x303404005140d004155a11004245582402200f0154401400b41d8950344582841506030f00d0010b813110300d100382c441850052341394007480b103a12244110506128140c503098860400c241c0c603108146806001c40c1c03803c0032011141481c81e62901001e50041100600c000107000300e101814244401c00d00411001d144202d107410349850441c01c0090030440d10410070301c14000200b00b0031910740e4809101c102c0c4410201c4140c51703010b01c058001420294203800081c01c14001500300071046031600c01500000007c1d9007200c2e07416503100e00c0c100d0030090020b916035140302c1641031501410381c0c503000254812404034000d4502955503450304034510080707684034001405031101d030350050b40c040d02c4800c0c80450300009101c001c5c24421503d030500c3e4090144c0e0b00c141e5850b4151302031203103030400301c0044000c007d0a49440d5581c90400c04064010540f80c4200c1644480005140300341a091180035070b45c001010ba400c555a44d940c103071100403484204469407042b4404112840c0040c5100d20060019 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 132227994 1250 132226744 132226753
    0x9011107060203040801050c030103151a03101d0303040c18021201061706090105100e0d05070e04050f03030712020a11060109020903010614330307050301150207050a290309 76
    0x18048151b0844001503c101282c4c075041004001103481d080303150000465000000503014086101081020344210050f9014040c0380c0b00281e6000d041e9000c4845c00003961141d215515500d0b83c01602e901c01110014045240c007038080c00300c3c11001215041a101c0d8400052800380301d20150b50308407070243c1c40080040e900c80c02e0302d40103444211816810440a82d0f07154495410040000e00c1d40000c00e0412040104030f0845003ca41c0c0c2c0d0003c3c4c52045604031040d01d036403e8541c0c00c07031a032928007142c058419100300020145114800000c13640b14822541c2c44104844464849070b02035405410203004000402c0d070ba08085510078449107001302822003005a41c3c06620083c1829260a0390001044511112400308580c03641d08650443c105800b104403892074880041030720a002c000c0c103403480c985020042081c880d8010000714182c800100104a07030054203a012a5a42d0060007126004400301c0340400c0400750720354003682021a00d40d41c03000e030112441c41c000201d070006c80300c10390345500 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 132229244 1250 132227994 132227999
    0x5060d0203090c01090b0f09010c0b04080c0f0a02030703020120070905090d03110426030406120b030a02100503100905090d0306060207120b0403030b030f01330b0901110706020304 79
    0x20402244103803c400f0308216100c2482e00c4d442e0300b00c0c0c1c003980b0154800c1000002e101c4226038400c00d10000b81d00e0740500810204c3c101810f1240712600007400c207052130700c503050946200110005070945007a80c004c00034926141594011180c1c00c0981400d507080528031000100d402d20140000b1000d4204010002003a10340a4500780c9050007041e400c3c01403514088055079461990b808880a4480402100b000c40d4020140f1f10318a004134001c0000b140004900411004c0e0301100d40070307a1040600c401c3c4280c4245804250301e45400000080d40011141180400d16005c1d5018581c03094040d045803105079510a41074003901e4084464120302c0d0825546100390303035014410384001c0c01c074520003020b40718100709c004064002d10381030140040340f0032400141058480c1d0403031080000040d00740ca01c50f65542c8030450107030415802030704001401d600c400030900d035020b00c60070b0203186100c44603d81c41e190203111307483c41e03200c0840a4100104100c07803229512041090000501d00c61b030041d9076031403 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 132230494 1250 132229244 132229261
    0x909060b09090d020d18050d050a02060408070509150f040504020319110a0e07080a0b0d020406030b0a050c0901020309040203100b0408060f0a090f033b011d100f0905060d0203 77
    0x1410414640d0502186c03c00c140ca00e00d6030b02c0700d035000740e4400303852001200c006070030003a10380002420000d5004500060116100f1000305440302160020b842086054803400c500300192150801c034660400c0c074980000c0da071031410790000e80c2c000b80003600340c07959040b000c0c10100c1030080f0280d06481c0182e02c61715070391490805045245c000d20000c0010b0440f414004001411240c1c05800080950345681d13481340f5960343c821700d990002e5402007007003140a541e4609000c8031803007222005c4034203151038006982d00c0d108208552a05005034059840c060380102000029003000d0b00c4200d5180041c0b0001c51100070140c014400b40c003554000b08007a1900b8001d41032100c00041545000500304050728000500100c02128034036458100803888640301d0311414898140359280070810203d41a81281d104546160002c1071602a6184a60828104000b124010507045640e4100d640480408003040c407036414554071884030b117070804585940303000080054110300c200c001007546c000103111441 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 132231744 1250 132230494 132230503
    0x11010c050f03152d040507020606122b02010b0a05091b0702120109141b120316122a060203040311061f24030203060303040f0f03050c190909060b09090d02 68
    0x144c0440c2e00740100d20309504c000352a180090080c500901803204003682280c800c0c0485900104d10150202650f081032040d1050644031541000c05946081c00d11485810500105000d440018100740b100381c6440f405950307143d0b540300d00d2110180c41031040000690b100130000358a0403141d03001040100e043c1c01c101d0b0038080100c1001300d95601c140c0581c45080c0d5a8000108603450440d4440c0409103500500750a45c41006003409005001681500800c01d50b076000c0003010045544040c00260f22100844145030404c0765066540a2100d001c00002c4954005552280c40b0345030400c1d110300d01a841030b160040c241c840030405111000000c928441c0301991200a048032104411480102c2c040001c08140c007104140400d600003001541a4401304111401002080c04100405541c0c1c2010020a8480d0008403500d010740044400c5500d030158400300900080080c54441c1c610307001203a0021701c00600210358103504c80084030300c2940c884464912803417174840a04118408154007d051 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 132232994 1250 132231744 132231829
    0xf010207140a0f0b060a030501090f050607050901020a080c010204030803040c230d020108091c0203130e10090c09030204020d0207170c07050111030f0304080a11010c050f0315 77
    0x1584002c441c840800c1c0a050080282a005019000561102008500c0715039964001501960138041c144040040840b11000024026000d6074541d489040d0110f8071031090755050390050b80040c0c0c188000c10f8555008000f2501c1c413000040c5415681d94600700e144c3c004840076900700410580401207021904070031130907410320800b991211032062002070342041c501e0300040c0c1040355a03800180400010005540ca0769800400c0c89080041c000000f135880d0710102c43d190000401c01400120b1903a11200070340a220f2400d040d0b9400350805404034010482800d0134010400c00860000150b1500d100030f007a00820b5080260351440c040c00d010191540f105807030111860f04000303102c107000020850b901030b83c000b440d03c080c2d480744000304240740d402000e1b40000c01801c0003003403004011004000b403503480207a491f03040190f011091203600300d0b0001170440c40425401c1156000ba040088011540811554110000741c034607030010948130590300c800f1450824001900101045801a0b6441d8 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 132234244 1250 132232994 132233033
    0x90c0d140108070506031003060218030708031b160e04150f090201030506090712020c01091202070e010e010315050c0d0e061e130f0822050108180607080601020f0f010207 75
    0x2547c20301c041d034a020500a0320001c3d12103035000c076810107a0030b151907a520110390024122615a501c400d5599103e40c025800e5600803014068041452500403840d0711510a144030300ea0010341c5400d9114542c00001071084900c50181404104080c0e4248206207940d0a501400249040c10788009802c8a00241ca624401c84103181040301155101200c002c1a266004000d41c40d03010900f04980913080341040102440c1c0204103681c02c0c05c1d4009030340003c586204c1401100d0340d98410a4030745089003804090b11002500c5c04114032075886400060f001031410954510307102040303111200302d038104800c0b14003d030041002c1c41035000e2240c0c0c05100010030704850000c1420329584082c81800300e100d004088003030b00012403040c00741040580e0300801d10b800643c1d5070403a4a00d108021844e403406601d02250704800400c0b0005030000034104000c0c1c1d01401480b55890303040c0d06450350140200201d045200d00b1603c80c0000105014405034040020005601c4040501e000c0c82880e914a94049 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 132235494 1250 132234244 132234247
    0x102030603060412090308040b1806070b060103021b061003051b0a05090a0b0d0b060102010621030c110a03080409050702150c03070c0c03030807020105060915090c0d140108070506 79
    0x10281e40c0420101e0f00603621102600c40c2c4400014181c801004590019150007004140003410502e500000c103142c0b104041e45032581c2004000f0041030740185c1c01d014040d0623002c40002c005502035402403461400324540b60401010780c0d100c10340380c08400c40d90881c0031134860404200300641002441ca00d2103003041107500c000d0030b900204060940e24820b00e0300c50320700c1d00081500398030701c0c0d403040107081409460501d01d00050300f8440303000d000541e04540150318005000401c400d05d074456071000340002056094900e41618211030000e00310a00b40d40806004501440aa444054220003503201d08180394545190065041c00c03520b004050f5419900044103120284000300c0c05154000b1001074410f483c0d4655000c2200d00d41482440180b83c06070301c0d2408002d060308651054842d45c0707107500a02217a0756074406c1c000306e05010b40d400c0004040c0e01d140c214032444d1080100d075000c41403640c620b04001900b0004400d030380047d51561b0461070303040018842070b10b0034402040540010384506 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 132236744 1250 132235494 132235501
    0x50c0405160210050a200a09050d0c090b150d0902041b2007090c05030109050703060b250506041407060309050304090c030b03010c0806011205010305060a09030203120f0105010908010203 82
    0x6510b4052a6129080143ea6074002035003207170803940251902a010321001e18031040c03445407800664000f40c400c0007c140040d0380000c903803400407042402541d0150340240320328034000480001e0000007a04540c01401e040142901c040d160009d400180e501040124a1400b03a0060008541c03210880f56031301442c3c4624a507400f60800f185004400c02558044849000c01441604024284c0c00445041c3e04005882444c154080055416640c500d4402c011035100c000041d400c07120584a001c1c02c0030802e0000c1c5c21420b0350110040501d1005810307803201c44026a41c0c0c0390400c00116412148150b14a110542c0e6003010001000038101078102080400030541b00c0740d54034002c1c1d20031a02074686620914540c0b0b446600681030041e405030003440028582c00000d45800c2d0100c42043c0051800781001a4081032400347c54101c3e5005401381c00d141e00c0301d0300450090a18005c065040d8402005051108030303952614070f11440c4001d40c503090329414038000508060a65024a0f4103038014801e0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 132237994 1250 132236744 132236747
    0x30d12180b0f06180109020d0e0309030703120924030506032404140f070806090c011403040303060b07050102030609061008070e01180608040210020109030c1704050904050c040516 79
    0x5160802210070018078690f507000c000540c0700c0030b9084c4102440215600010307020105402404010312098010301603401003094250b81d81c014800d0041c0d141c1c0c0586000c0020400080700e1002d804a2894640c50003610f400d200d0010320381e14000d0098030035200c9220000f25616205540c0c10002c201c02a0100200010321f02c2012000003120091344006140403400b0010458800d0512902080a0b10001d841503449a0b0300c407041c83c411031805004000c00640d84040200c0c0240315024161501402d20609108041403900001c1086082c5681d1781008103041c902e5401a140c0d01e441070001580e00e2421000f032180e41e00f0080c040034090a824001c01912541003180f682c5d1101080c42d00c40c88400301100101e61007400040d400d41c1c0600442004502254803aa070030340305500a80740358100100c44a030032030803100c20030400f500040c000b1108030002004403407510990350014080d2401c141e00e8000252400070266001c82d400e502c01040c10b041410b10f8005c03e9400300308540c0705103080c14072030300 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 132239244 1250 132237994 132238013
    0xc060405060301090c050421060e1f020f0d0204030b04031701030b0c0a1202030a0e0601050a030c05010c0503040513050f09060103021f090e09030705120f0706020702030309030d1218 80
    0x240070001911030580541261140e1b00740c0e00109100a0110742800100c1c0300c000500390008000d0b030340a401c012000d90400000103035014005104490b41410000c2c0341140002074100758202c160f50030041008101d0026940045c2c8007860060b42070340c006040c2440c0103811103461100d048024001000100041601d007400286d002d1a000f14050f5250080ea0048545c0010708210120b40c0344040280300c0c4201760b0303900c4086a40c0c42d480c00c940c202e90301d030306c104075803032401e4440248400d0613203009206c107510401c2080c81031407107441100e003842e4941c0300040e04542941d82c5a03280e1517455041080d92402101301d1074111041c80050302d103079411500072071610b00b04102c4100d0f40c1805036104030785440c802c806040c01032003070342c96800c42814114811922a07110440580e0f051040e02071501e4001d03169000c80c3e2681e50082640d600c0c00000f551203030040c1d0000e00080c0d80c9400180000340c401e0b1003e210807658107003207030740b03503803c180c80c00c0018001c03502144201070385150f61001030b1000452a44 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 132240494 1250 132239244 132239249
    0x1504020105040504050a1401081c02011109010e0a090e0115050118030803062805030616090312110d030f0e010b1c02041b030525170c091002030c0c060405060301 71
    0x12401700322503840003440701c0a481d01003170f44030440c0ca0400000403400408107252840b0780b4140c4011941503000e090403400d072410a83d0081c0040c00421003205503600a880c400748101002d032043e01ca07a035855190404813903482d6814100c594441c1040da20410491240902070542401c0c402070024959291614005503400010001100007010030140da0310496040810411650184004a540309420343c004045200b107070f001e8030500010a16058601c038070325071000d4a6980d404039040c95910b54128416940422009100d281091619190402d02c080c01e100e6026840100c0c1d8100e5030507175003040f00c10149c040404c40c0d14040041d00c080e81e40b020605141c00a03001d5011300c05081d400001c0083c52940904c40c00840008805e86056030180c2185200e1094075540700008038003211587c0c1a9908459a00000368000c200302c0380807202030075280d030004204d002280c203041c0311030041030400c03019400b4440580d1022a402070309400c104500c0c21000e4060711407030304252802012400341d00060 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 132241744 1250 132240494 132240499
    0xc0c0f220f06050a0303030605040609051e15040c0c0302211617031303090b0406080c0c0c03060709030b0a020f09060f0c07090e010b01110309100e030d05040815040201050405 77
    0x80307030450803454040d008400034100003000c1d0340700c3c0360f078a14001e8010700181c8901e074001d03802d01800040c812003601c41e46100c2e5240c200000c0c4081b849070044140094010403084014400e030103e0501c944440c444c000020344981c951032881081400e02910700001501848580542d02d104e0000c03503200c01058403d01107100544030003540365890002d10809040103a49000c000c00710411101240d02c4004050310350194131003803c5662141a00183e510a9006110108903400f011800c03c01001c001005aa82082d09a900c0f9074456030020b4200001a5501e0000070f0451100740140b02e140760109800840301c6c076045141000a0340700c03400c503005070008207100d1400856013004a805010032280c000e88501d068481700c58030391010800810071019a4400e941c6441031412041d4090250800081c80340c000460a00c041c0101304901c0b80362000800c810001409182080340c6c5041000e050000029191a0788450030002d10528200e00c401c0c4c0380e94682e07030020038000981d030824103d0301500d009 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 132242994 1250 132241744 132241751
    0x615040b0a0504020a0206060a060c030e15160b0a0f021206010e0a030501141006030b0d060b0a091407080610050706091e03030f0506030102070b0610030905030c0c0f22 74
    0x300300000d808039a0551100382c00c940002000c111a5502088a034818035048030404244d585400c030840304042d0b02400103000c5400c240840030103181c41115403910b1010700100614200b5000141109c11204940440e1050360a8080c08481c81540c003c1880d000d41002c000c508203c000e2252800c640e42c054001410f0180d402030100007921500842409160400003e00c840c101c060040c00759408111402a170b46200b01c0c20100310b99201c0d010f500095403005080e00c0040229842d0140100b03035101c03031f04da0300c1036410301e002800c404c0c02d0041c909602074651780c02e1005c2c80d20311000b910700d5400609080c442c0c001d42c1c5c144500160040c05841d00c01e60440c0300010415158a0680d00c0380007006142603424007903039a010b0806500d50072426440300d40760002d00c0780391031346000d2500340d02402200401000581002481606002e10714841c503030300d503280101c1c064000e916480d0640d4011130310b100490300000d9490b011400c0a518840c0485030a603544001c0524503d1340002103281c400302e68211546 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 132244244 1250 132242994 132243011
    0x601170a021c0203121218100c1205010f0509010b0c0a0f0506091005090a02040f090606060822080d09140d020106081005040503090d0620070b09061504 67
    0x10010502201d9000d841e00c02c107110705125500c888464980120310034030072181d000710042100380035148501d218214588150b00c0b2401d001c40d1034007880c081e606a620403008000820800307405080c0d541055900c60740e03454810040c40c00e007903600507042074903402c0c0e884504200507114110b441d41120030580003191034600e4107200b141403a24200c806030081d100351030840140040841d07500d01941807041180e07880200b0135040c500b80c0350101d901c052a50050a071540c054200340c0c2002071803001103040011908210740e1103078221038042e08048000f801e418100700e0001d0700e8551608500746c6030151001c10f4000c40e60382c0e4182d84036aa069034403840c0c40f08010002c200a142012403011070342000d60703000c031010010090003403025100c0d025031880345c3d04644006948510402e4043c0c0e4008010f5403030300841d00244a903800811000301c50456881a0800300041140d0405080300428138072039640c0c0e412030a000a100350054908402d5030059002d02041c801c1c0e40460100034101030310b004c02c42c0762 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 132245494 1250 132244244 132244289
    0x30301030b0a061e170c0306070c020a15021c1e05070203150411040f06030203030708030702100f0f0c0810030b0a110c010501030605010e0c07110d0618030e040e0601 73
    0x983c56020350001c90580809010200080c0c12010a84000c038030b40c0f400c5041e07003c02040c0e5404600c004680c1541001c4080341400d4411007a03400e00900241540c03c0859603100c0703103030000081003104030060b0400840028600034441c6c4819407143e25280122100054464000100803d40005818054009024001c64400b40240030b44c150541a00b0134103480e103800d2114298943c071210303501c00c503c0c0140001e1020305c03034807680040d00d80260007503041844990b20080103074130103403189007580300e5851440d00481d8140070340b0030400340c41d40c00442e0112511440d001031b42c44100410060040d4401000381c10000740c03518200b120340203400042c03242c8807055075100030058002e024207281c034001040c00700d8010540041d412207105c0e03181008503a90b030380e042d00300c050801c5d90440c00541c1c00300486408240c030304144488030100100804801c424980d0b9031341c22540303c030042441d80b41c0c0703000422040c0f542100c60a1010802034405102c0c08070b4240e10b06031207140c140100128400141841034925 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 132246744 1250 132245494 132245501
    0x6050706090501050901090b0603030a080c0a0c02030a05030c07061d100509030d0804020a170a0b0619121109090c010c2307090e010b010e010305251d06040503030301030b0a 76
    0x45411200030132560a00c1c2e00c50501074002a034003036640d040340802049080c14000100c8550b00020385d030f100050f4803503000c0e1150070380c406a8103000700424112800007503541802584102403081d401196550b0500080500307140d0703598070030800d00400050396001029040650b1040c6041252901c103000d0325a042a1628050a0142c1e6054403c404110391856007140132203000d44d0007182d03900780f015503a82070005111011000000d281e04027022460016045816090300028003c1c940010f1030351107490460b00129540c00032008148100b412814804226921000300c08141d401200b9403a0104c211640c07400400e5180341080545541c0038140103034034100380045400318082d1840002518122a0340314181d0007203100f40c900e440504c8950742c905104207007143c14181c4440f60510b03500c400540003000e00404d078255100e4500c41034030300c040c40c130440080c204050b0b45400001502611031021038a06000034a4000c82c020003041c44140d07400025641100c3c2d2003c00b41c800d03652501d0310701014 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 132247994 1250 132246744 132246761
    0x311070305070f03050c03010204060c140319030c03050907050a2d0306060609060e0a09020c030c120a091e270f06090506060306090c0901050f0705060603060c07050706050706 77
    0x140d00a6150210b4003d01450a0300103c1c1d01450480e00000b203840c00b010f080b8410f5120b483c010455100464000400311385505903c9620042540c1c108010004000d0200c4c1d0825107440000e5929060700e08616010b11400760444c0740200101001800d000c00f140d800d9080d8080d0040d02d10304840b540186001c00010b40300a542002c0401d0032039503487c645400a40207900601b0085400e446010400d00d00c6000b4031300d20114020500b44c9441d1070080444025030011800d44981d0204210740a0704c28030030040140c01200400106988101103c402014509a80c10000c07014111042000c0c4100203103110b0b00035030710990140f40c9a0030405545d018103003904c04a01e41c50601f0f10030305602c00405588101f0881d2107070041802640c1d100d03010006284001c80b0000d038040c0340c510200315100400c00151141c1c5006040079460300c1101a0100f074240c000ca4001c03140c2c0d0f4403440c2042030302d040c140600b43c0c008032114807843c2061116901c107030729840079020f140104000411072400f40040c40d00b01502 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 132249244 1250 132247994 132248003
    0xb060a05150d050108030c03070f020f03011503060e210a030603020a09050720190203010b0a03080309120c07030311030f03090c01090b0a120b0d050f060403080c0403020d03110703 79
    0x4a080d2141200340c500c0e0409240001c1c0b0354a800c000048030840031007164000d130980c03800b841c80c2c001b00d41d171022110307040c003903099810031668040740d986074030244101c540e003800c400841d6850030700d1440c01c0004d0f6842002c002955810800c080141204800007442c02e11080b03000040d01c4007034900e4118020b2045900103540022840b00000710810203501240c000d003071a80d41c40c02410702840c814410004045080340315540402d0304803103003403264060b100340313548001c001055007120300c0c0001c0ea03c1e07101a04240c4a010000061280c0b0910402203144400c0385c10101a00740b00c51034010503182d02032880701409002e5144021580742406004480300084040080b0381c9034104644c60340ea0312005444410b0214203900804102c4441140645090780150355500c207a10308581d6107400949001c14009030010480040c034800948140484144918004c0080c41949400d0070010b003400d0b0064034020f5900d10800c002d01c0507813210446102c4050705414080105400710351400c1c0b84c500c043c2e10240 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 132250494 1250 132249244 132249259
    0x513090b042309010f090201050a0c06060801060602010e07050d0c030215040b0316030b010924020f0f0307030f03200a05070b011401140315010311040b0f040603050a050402030a0b060a05 82
    0x802c000041c00d0a4064180c2c04001c11000100c0100102140e000640103404240d0911103c4604c510500c800c1d488540b042d00c0200d2100d6654054a003590400d82041025035103071010301d08038180c1048044010b001c1251103c03850b81d000e403118003858143d40806401082e4400c4944466103680b01160b000b48800031510323542c3d10b0070508052442c0100c000741c4001038107010040c18198820003421095502015280000d00107070360340002c492501a202906500070840d032450b881a0a11030020b2080054005c0c550300e102c1071038010710300d403205002c043c103140c60040c065403954504103d0346548a01c40c4811503448100d032006807000c2c018103c0040c00402150004600c0313058003004c40324402320a8a50500050150b6189041c0d40000c0303071048000d154111010b41c0315842034100c640300348141d8421038507064491682c0351480d07005030071071101403400140810841c0d60620419a0010600c4c100300f0a505190f40081d407540043c16001d800c281c1e040c03021032444d59600b8400c9006001c010700d5070 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 132251744 1250 132250494 132250541
    0x5062206050405090112020112181b060207080d0c030e1c060903030e010207150b060405060403050d02060c0a05090f0105040b0a030e060a060f060c0804030602040b0c07060513090b04 80
    0x40c002d9025009050203820010f0000034508285030503076072041d0381610b840340b8a0400c042080003c02c250040801d0441d004ea00b42008201e0f651420074400418034441d00342c40b030034204c019140c8900307a0b00080850340302410004c0907941c4080356201040d4076151030504d00904100154201e80007910130701d4400c509015400800006500c01040548640c40c24004850004c417068200e00891001910300c080055946840413195031024550800050415040c00c1c2c68402080c900c0c0c00a4008680036486841e01c3c46440b5010003919600c10103a07005c0c9403801010364002401e50198282441c0201038401030a10b09a0080059402030511f440640da20b80030030ba107000b000340255034a03120722400381c070000c1410340c482c6000340340655044980140200785024001c81c2c050440381015a5404400e000100008be0b190000304014450f078244a92101803c0b0203241c01c18103035501000034000104030464601801041d01c0c012a00c4901000a449035601c0124018115200510b284100c003a0188c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 132252994 1250 132251744 132251747
    0x3030426041707050a14040e0f0a030903060b0a12030503100512030d1d0a0b090f0706090302101701060f0e040c170f010f03021302160803011a0301050a05062206 71
    0x454040c01ca102c4111000503070f59009011100000b40103407912542c00c01c0d040843e6052036040000350035900d400702c3e5525844002035a0400ca50024102e0010315401e00400c14441c8601803440c900303c0443d1031619441c506240408640e014a400400303100e000b00c0041c40107000c03040088001e142c0a4031107203901d00010011906c95101018246a95290001526158030202c07600014450b20000031701d51103034561280c0540003070040182c0d413548520547c5070307203d0400303000e0480203101e15211949002e0541c41045012078110034010208155200020901c0a400c800c1c6411603000d405c140b4168508100700b00c44080c03070905401d400504100d810744030707164070041c04183c1c2d1202c031007500050303101d400000b00049420320903698601003504c0c00340054036148011500e40035000300c0041c685818100c2e030f4540b12011308001d581d050404801001510302a0080f41c524000c44c40201d0f15545c10503002a0100015000d00d502174580440d02607c050a6105814040701d0a07190a0035150383d41c010 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 132254244 1250 132252994 132253019
    0x50a0b0103050105011806050f301509010b032a040203010b1801090305030405040c090510080106110c09010b0d022109071a030402040905030409020c150106020706020303042604 78
    0x12440302c19201d0302c41d400f911b0140d100e41c80a50b03400410320800980302c00200150080b0310320000340e02c00a6292000d0700145030f154040c495805000251144681c02400002c2409004000e1042641000c0002081d40d60114140a203c0603a4442c050001819140e841481c1840d091058010b4400400400c0f09000c0030701038400d004000b00c4c20b43c00b54070088011590340d0044c1c800200f42e070380244014007051a20342c0184000c501d2510b000c02c03c190361000042d411009043c4d000020540c090f006003c4a41e01c100f02050740440007000303021440c0e098001c14102c050500c15040c0040703001c151103980e40d407550100c64070000011614400440102404251a038003960b07080003e11507540000340440c2c901d07004642c01c0e940e4680280c03c40e503603034081c04064044064200c841740000c00000c50b824107680701400c1006500c2c1c005003080368507040c0e241420401130308690159400800e04020040d80082203d500c15840b12201c6503100643ea0100ca900000c02d111500703042011501145000e940304 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 132255494 1250 132254244 132254249
    0x170403090909140601050a050d0305031b0d0b01030f02160807060b060a091508040b01050d11090a020702130203060603010b0d06030b010308090301050a0e07151101060605120a0b0d030c050a0b010305010501 90
    0x9a82c040d9a0746c5041100d250042c0c8600d90700904441c54000c0840d014030043e40c0d020f600816802c000d441e1580c103100550b80031240101039555115a14405564940b088844404504408524141003d100840d51b4448044018191140025038000700104d07908002c4400310007424150f221403660394041d000240902510141c4883d29800103180741c482e010140c01690424035107c0c443c2d00b1b000900895040480080d1841241c20340050015154001c01c070340b08030480c01c401a03c07403103e40704024030712442c0741c84e590500d401403007070004590700c680880f41145c0b0b102c5101075840390f541a007a40a40034070750000d040200408000000c0c48a070300f000700709010301100208480c0e07644440e900b0841e0782c541e10400146d402150140813044c00042140c40803105428005420b17100845040d023540c495070401d00002c0d4022801c0c000180801c0c0c9002d41000c5010030074041143c0311030215481d0604940081c0c10000da032101a4140541440100b003c41d0300305414001c0703503031242481e40c0609000e1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 132256744 1250 132255494 132255533
    0x20409051b030f04030e1206070206070f020f06010915080604060c030f02031021060216030f09060c0803060a0308030f190e030304141603030306140105030403170403090909 76
    0x20304100c2a841280700440c0d02c249040c82d051000da450b551811220184143c0c0515041602e15000e02c00c030440c1084140e21500c81035000300141e00d00884010090b0041e090720209540c042c40d13840c4155480468000c0c15504200000640e0425500140c034040e451580b004001d400340105000a02910750400c25002000f6141803003114090b040c10f200700c0c80111001c1c050983e501d8828030860f10401c00e03c41045c05010306041141c01030307032181c400303d03030020003441c420a00ba0a0401b0070180c00c10000c407a5040c082c01c2004400f032428402900900706202c00800b0300b0800000180356554181d502c02c0555000500c0c1034403841c0c080184c40304a40141c0301110904a0305103900050100d9001c0d1540d804411740c00785003507890307581e41c49034102c00c80040a41d20307000d580b03030303426405410f181080001d502a80d0086503080c50044140314061540c40ea150400c4402c104010103e5003044108001c6002814840003d0ba2141022140210540c00004030399080c02c03038041c2880a442d41e2100d8174103c0b07 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 132257994 1250 132256744 132256771
    0x216062702090f0a020d02040f140d1a040501090c030302010b0a090b03070b03060d12080403031b0e0d060f02040f030c05030102031b0a090b030c040305010e06060303091002030d02040905 82
    0x6800c040311040505800a5100600e540060710204003d50f0050b00981d2a9a000d8100030f00f00340000266041074202c1e200e209e0b0444410031002d10203266a9903545000c1d2541000312840741c6810403501e034000d00b84200c0481c038002090401c442540305016503078101c251441c5850312071034000e010f840d40e0f2101500c0f40c40c0c2d05030f01003082c44070741c030a001980344014000c0c8000351510b02c4030713401a00000c083d103074002c40d170074280300c0425150380c01010000640c0e80c41110900d804d01d406012101d02d94881c022040e00c103800740354030a40003030300034141c0310040f181308607408842d150600261507a03102d100725039400400c1c0000d00c40f802500c04030031350707202c1c0c0d0044001d56217440a040c200c0c08121000c649101d0350200180b81c0c05001001081c807a021842c0c5020749036198a299086540183e425002040b4001410418003c01384511400070640801612450130a1000a582c0c2d010755003502e8482c000d12441c0050b80350003001100c080c1c1c40c00030340075034440740c0da2003240c03006010858511410305038 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 132259244 1250 132257994 132258041
    0x608060301060602030a0e04020903030706020c0d02030307022e0f0f062102010809030f16020a080a11010815090c070201080c030403051204020f060c0a11010207080a060f021606 78
    0x80c180100001d0360410b600035410607072004400c13109450203100064009600700b100e40200c0e28280018010b0501419001d031741c964030710651a00e415102001d0310300310b42051003401441680032840c5001d003015400f24005034521150160b680b045c5400c4110300303462501e1000c0d00d043c603480c1c016058082c143c150030840180e48001020303400308140a4180c2021414550000641c082c580581e04884404d00f01c0342012400c06019410350300c2a0070103455000c402690004626000745100302814100000d020001055600c40c0c10801d6030807180c03030501100d0800500041c10f4483d800c500d42c04002d01d4039006003400c070b02004860f8441e05050f400900e440000a0300c00071102c048a00940e8903584003403070104441038a040b80e400282c800c903032203c40b8003210b500079500c1201400d2507040b450043c0a100301d191030320b03000d00d12508030214190740103c1e5081100e000080744581d082c83d0802c0021680b408507821910082c0b103003101034500d480c04c02c041c020171b0010552240e58003a80101341251100d1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 132260494 1250 132259244 132259249
    0x100501090e0c030903040308030408040f0f05030307060e010e1e07091103070c06140f100608011409060d08130f090204050d0f050a150c1403070813030e030d030501060806 75
    0x180240201c00c030400d107020114002140c00d40055500c9007100080d00d041946070354415465074800c0d00c003503e43da02d0208007404402460040603006005403017083c04010319000200307031203002d0500042c000c207544044081c3c00c07038000e407c5104c0d0701d1210000c1e9502000f00c116600d412608c0740187d04c440d40700720710340400c603090f4500c55500081250202281150341391401240c03040032401c01154440e40360b0250840c80c1c0d072807038032550042090303081c01548c0d0720b0f001c8183c0c420f4408a9100340c0400400da03004116442440928040a4a0a840c0c000c0b0b20360b102408140001c1408200500507100041d140c882520814103010568542c030412102a65031840ca2109900a5005580c0d1010714980c0d800e0028620002c03103d0143c3c80340041e00c2d6405806d440380707100f5000c0383c520685901e444040300d48000c0d0348441181c61041d4100313065400d508208400078900c07580100f60408410f020a4130f4418140607400d0305160f85c2000b000c86411304486500100500428800c0e43d0101e80c04001041e903e2 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 132261744 1250 132260494 132260507
    0x703120204081c020a0b0106030209180c090103021602120303041b060e010309050114101703041d040c080d200d0c120e1c1106030103050601050d080c0a0b100501 71
    0xc2e40410000c20b42c038a0f04000030a100501032030514154828a501c50b00003031441112240204201e440c01130b211000b0205000d02141103006401c00072042d0300400a60030154815220400c00070303c8c00584483d420114241c800b9000c500c043d500c0041080101100400080103501c1980f04040c40c0700c800e00000a456440015401f03482c000c210141c04051107540729503c4000c0c1c250061001062561803035136502500c1030140c1e0202c8641c44800c0c024804164038901c680007801c2c030700004501c0c05d0310b080b060041c0c07030100c100c141c9412403a20b0041030501c5800381200000d4107280040d120171840c0030750003070140400c40400105540e810002e140b05a100410442c008108a0b00c6456041c016640c8561032550b80c40c001e1010b00c0740c00da120802546849030500301d00c2c48403203c0c84592500134185907610300000041544603420400040c4001007011681a0440300152140d0080c2c00035860561806e004144242d8014800d1503112014408004c202d5401109222010f078112500c7e4401113581 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 132262994 1250 132261744 132261749
    0x4060e060c0a0c0c03120e10020c0a0909080f0f0304020910080d3509060c030402060f0a0207090f150902030903040e040c03060603050708010b19052e050703120204 72
    0x10100103102c007600c1103006400200401d8418006080c0498030396580503501c81031011090000346c50344c2401c20607400c0c520540c0c00205103500051602e4035081c000100391a04034003400b0b0750030303854480d801d0800003814103a0340015591010075869860244803488583c0080701c0c07c1c0d05c03d88100c004110007c0c60241c2c01ea0a5407500b001030507403d05600015142269030030990a0300300d140008841041d00c0f20608400301c12400300c0c03034005906004820b2407038081c01508440d08050208184001641d0383c60444410300e20288c03c15032a032012040581c281407455003d140c5040c10644007074001c0000f40c1c0034074418148145032261650f01d0b20341d1031049002c100d0300103d041d8420001804800c0c610072056038424070900010f40a10380b41d9032080c013a40c0317a9900c2190150301c0a82c040c050840b00b80141140d12005031640941348084544c00c01d8507440c0e40c0b182c83d001e03c00080c3c10801940901209040036400c2540c6805040481030006001c0d03803044205500040d03e101c41e00401c40054001c5504 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 132264244 1250 132262994 132263011
    0xa03020c1e01081905090a110f060313060f02030c0d0f0b130f020910021614010804061a0315091005010b19020a060f2a0f1805090f04060e06 62
    0x240319401d07400540300c03a900030b00300d100202c02550040111100a0040074400c500c504003400c0210441e10b008078011346540340c1640300388600350200010b0388884058a600c11401d60201603800040c0c2080c00092101c810980402c0d1f0001081241160089000b814001c1c02802c0411500080c424000100c0e0300000100b070340302c0490f03900c080400340c10b9003051a820319002001403601c3e1111002855104400200402503084880c40c0c0c5100079204601d04018070014044140d03001501c00000c00f01e0000030001011713140d80da64000308400c1e0400e800844000080c04070740780c440e140f642484044004450051803032003040011682c0301032a0140b00e040300c1440c2c08442c01e0010880c86041c4902800300c404c400c610851440304089160b070f00520007041142900041c50b1030200c00c0001080c800c0c5c400d1402c1100581160b86a03840e442121600042458580034000208514011184650380d6100f02e0740706400c0001c1c17201603110601d030b842c000c2c4e100d618200410a00008a11348900342183d07401d8 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 132265494 1250 132264244 132264289
    0x11010b150f09040f0906050702120d0f18050a110a0305190317010306020c0606060f0a080601020c040204090b040e121603030603020603181513080f0f030106020a03020c 74
    0x5031032440c0038010344042010803000703505250714507010500b02d43e10301c403c070140c0c103450303e1103071040c0503540c42000d4101c078043c4040c00e12340c200b01082c09424400d0035514200c40da5503201c010700c1c6117030380d50044c02c0c0d111500759a1042d0550509250750b98800480b4143e41410b100c0d035081c200d07860500c0d6450120b0761b1241c0a0840e0a400140f004080b1107401b0058007401040c3c0c03090980b01141c1d070280350195200b4900181c8a51030160103511301840104682d0041c04104052108210b000c0295881c1c01141d1a121075035a032000c0040b4101007544000580103800401c0200b5506019045070304400400d84080220010180146650301070080034540c605a04024145114400190b5150583d000e81004a0955540d50216a441d4400c0761010030126000000a0074424140040110003041c0d0b4201110f0b81446c114101400c50380d90030040030004000303030000412451200341e86080c100b162004d80c50b90f940d1400a9118070104008074014020440c071304040f07140031501309640c0425050b090 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 132266744 1250 132265494 132265519
    0x90f0709020c0c030f0a0302010609020f030a150503010f0c0e0f060403030f11070e0103050631060b0402072306070503060f1c05010614090c0a081008070308070311010b 74
    0x40025800b5051140c041c2c02007001c840c241c2d0314108901804110200c00500303850842d8100242192510b40022462500400000625a4400003503c0e0003940c06100001ca801c4420781100c600c07100381c0c3c0896055428500f04010039550b070350006009207460f13280c29003401a0300d810810301b590301c0300310646e00c0003003800180301013803280071844010b070f5444c01d18182c003111800f00e00c0d19054080d03112841020401e40148200401403121940004880d0f0f41d003c0315081404a40301d400c590310b058141c80706402040107040c4002c0d40c1004403e110083c10855540d461418081e540940b905000b82d0f001520b50001821000002000341c4100300715070b141c5043d6120801027160410f0001c0704198030072810004610f005404003501c0c003103c2e1140000040d142c2c6404501c0340710000103100d00784180a043d00700000140f0340c100b1209809d02a1900c01c51030754450b00c80c1c2d060710350142c00c4404984600d0001204204c114401044018040e03142c03658041c48480b402c1d03090714101d24281c2d8100c401c00121 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 132267994 1250 132266744 132266759
    0x30501050d120c0c03260a12050a02040b040f06080601021504030806060c150f07030204030302032217010e0c040c0e0d0302010f0c050d0b0303030402030a0305070615060c0308090f07 80
    0x14010b1240d61800390410b01503516402c200e0f4060b90000d4492041070800c1041421002c482d00b6190101003481c0b5040035610540649500403900c2c244404c0d9403030703100180604086504480140583c039150030b884989030081d00f0320f8840b4034010000410115004100380d58000030b068800358018070400303551995195030807248285c0103017a072508070405000c5d00b0861740081c07060385640480c001c003190340ea01e46038865042c2c010010300031000380741c030420040c40466404812910b95041d6480300580c010168912421300388110340c080e40924044100c01c0d903000c80190002c4010400b0101102c000080b400108003c0752000300c0803070041100d208060340642440240fa02006010340000100c4545041422059541d440c0d1035400181380059140d074804014841c02403600b005070000e500750300c0d2960110b40c0e100d4074000044c052000c0400d500d02000050781103280c1010700c40c0805400c10b580c0d0742000e081103141030300440114040d0070020340d00342c2000509050310138a0000030509146800322 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 132269244 1250 132267994 132268013
    0x2040536060609045001110c030406050c0a06020a02030408010c0e0a14030f010203070f111203060108040507050301140a1a030616020f070e061203040501050f0d1b0e10030501050d 79
    0x199500c019800045c11150020014002013204e10b944034001e407084c98902d002400c480d0b6054866003a2081406410a25000003040d5403d5030f0090801d15030310f0305101201d52404255003801891940000f5004039a10b60100180044403000c100a0298004400064a00f8458400b9603074104802040400900001c0d0301a500c405101500340c4424104022040307080e0f91007201d6580200c1c1b00c41c0112108035520001501040100e2000b415518500c0c1d040b24942d0722015094504020700000440d0602c18107000300d20003410020000c2000c1c04e212031820021060403941469507a15004a6101d00d081c0d403803403405213120040290280765500090100d000550309000402c40c802d08003049110701040001002130309800099000300e1500d6400c100d0000c0665140c500740c2e03041030008000d2660403205031340c0ca41076041441034030791045041c840000e01204027010302251218004069840d0031803c901702da20000d8074942111401507206609460080c0b190b26004110507900502044a802c2d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 132270494 1250 132269244 132269303
    0x110d050d09150c23040603090203031201090c080702030c0604080f070203100b0405060a08070e0406112802160302090a09080c06060f0a030206070204053606060904 72
    0x14002405803560702c2d10000350006000d942c00a82e03440c103100710310b6500152014030091402040014906503107552106501aa206920500d511181c400003150340601c180d50301001c10700b144025940e907501d9944040d020580004010800c142c0c0440c440d60b1000c000c036405511003400519040d280e0b07030750740700180d030140c0c0340e1310300c4031405000600041e6410700c50390590500400b408981c0b000a0300400c021113102900c0e03d0700c203c1c0307503402c1042030005c00300d13481c000c9600040c0100c180d81c1d544c0c107080000c0d100062a4105d031120000f88000540341c2d071080101d000c42d50341070340c1d2a18080350f08280c0e03032103e5000011010b292400410001403400c403820741d90001c26400003140740203007540c070300b091508025603103d040d8003c5020001181041a032900c1902c0c41160f034105207503c0c43d000307c0d01c103108219010340a079480707200140380c0c0300d019620500000301549410b40e000d40181d8034200c1c020346c61040c1c00810f0040b140400d00b00e1502d011020700aa420807412000c080c8240e181080800035170 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 132271744 1250 132270494 132270517
    0x150102010612060b04060906030506010b07021804030804140102041a03040f0203030a050406080603010c0e040c02250e091c050706060b12040b0906010b1b0703051e0607110d05 77
    0x4900106204002c0a54250214460304020407003e4440c03040000356000e6800181c0070307510707040080010940018a241c115541303908410340d540503600204107002008404001024403030420b200425600c0403116101d58022152050503008800666081c0c1c4a039105204191070403500c0f4104182c2c01c0c80085800c41c3c0b0030319403000e04400580c0400e0a503007011001d90080b1b80302240c1041440d81100d54240c0c031103021002081031007000103018140722000140f182c01075960340103640b02c4500070412070a40c2d0344016a5040012042c10408040701f54501a515903880c0c4803021917075105001940342e4602840410140b90f103220711714119680c0d0031004082c2c900c0380e140c6100083d04403045008040034844120440424503203401e01070006213002e44551850b034441801084141ca217034003558003a01d000c41c9085118900b01d40150315240b8160030150880c0544459103803079007440b00110001007404004d5544076500e17900b041d280e08005540207002070f00407200b480d84c0548a80010030140192 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 132272994 1250 132271744 132271751
    0x307110c04090501020c0d021f050c120115121506081003080a0f030b0105090f01110307080309030309150702060c0a1b03090810230c0705032101060f0815010201 71
    0x30004007540c04050381603e0b03907507000030f444084a1080c4012042c0c11710a00040261460f005003030181c44202c441c0c40f40b004c95031900840d906c4464102241c8850384d10210722419543c4400310910a5000325030182c000c102e105029400902c0c40d40258281381800321780600501740b03003c9082d942e83c000100041c084500c026000720000f000d000181c00c100180d5641e2100f0760396a014007600b200d00301541e680c1442414001e80800d940c07444da59030240c040030b2810030031a07040c5510f494a180280d503c018043e10000c0304010b01302c00004040c0d407141031224112106003009020360b00060100361092001a04400e000900042c0000010500710f080762034403500400c44213400ea103090707a150700110000340c007000341003003903040800c82848548420b240070480048854208401501803160781041340080c8000a040c072041c802c251001343c4e400c0000d89aa0384603400604181c40d40848030940300109002c0041003140c0b15030018060180c940c0c03102c0003107403240c50000c10b940e20400b1480b41150340b03 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 132274244 1250 132272994 132273013
    0x150b06070b07020105010302090a1a010315051203070209060616060b0f1012050a0b030d110111030408071502310b0f0d05011502150c1312030e040908030711 69
    0x280709a68030888160340001901d504610402610340c5c40541030000c103a040c50811254003503403003440101810309090002d1440f01d00040c400024095900c607551094010781007007900b001c040000d000d210710854080d6400e6540204001060007007031040b1543c9040c440c4cc000006001e540401c18940d4002c00c40c11070f82440c030700007070441405010303884005140c9140c01c50300502c680c041c1c03640041203c10140480607030782010944c0c8801d0040c094040150046c020000d9600c00e6000c4800318101490315683c178503041c140390444e54000d41d811142255591007d10000380f280c030070f0303d00621411760702005868000d03d140e50641c0c0809a407045140510b0000181e118550740100204060065103540b41c0c066180b11004490050340080380581c0070510080d005d65000c2840403010690504240b03c1e501d51703a22620850080b04c10642143e52101800305425042c401c4102c5030612a58070403855491240c2444240c0700c100300000c2c0407940c280b010418060048481c411400016003c07101981c4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 132275494 1250 132274244 132274253
    0x31503030a11010c0206010303021b010c080c010507110a020d08070809040524011e031e020c0a02040c030c12020306220b011b0506071803051c030b0d150b0607 70
    0x41c007009120001c604100300c03456881e1070030f00402681c0c00c5203001500c40b562450720040d49507000e0131503460021004030075080c0303180c0c014403c90074841e4000f00c42d5503c0700500c0e40c81a00a01055502e1008a880844c81c85050301001910503025540600402c41b100d4196844403003582184000322140c0c8414003244e081601c992180034865401c180ba4440c2c41c403c401c0200000a103401030207410081d0103805e210060040402d801040c10981c07400044071841603440c058a4440e0800c03c8004600019030040c4800d80050380400050084a04102c885032400c000c1d0126410200140e0200e410180101c056800c954040c0d075000300d01a0114501d02400d10210003110400030418140c0c0d90354040c129025644100091008401070901502d5141c664139959954000140782c0010000101007205044000301c00c6031000b540e01200300d52243c000150b4550410850040e0000000e19107071001c046440c08070b5400ca14507070042480c90a8264040d650303030103410f0320015981c00c40000c00882c0e0025 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 132276744 1250 132275494 132275497
    0x6010e060310030b06040c14030402040905071502010c090e0402040902120d03021b0705011b0c0302100c03080c040506070303050a021e19021605040c020a060c030204051504080705010503150303 85
    0x105504100b10400c1070541c80c00100c14075028081501403480c0129402503036800c1107180607403030001d400c0641c070385e0340c0c920020b4050502440010000e004010300052088509000d40682c04007070b4000344208031000c4030448403030702c040c403803a80c058005002040c050f00789a80030244071400a801d000072075150000c220f18090007110410000ba9000070101c19031102d65010b41c0000d02203401902003185484c00081642c43d8402410070b08030421901d0000300070300f08504c00001d650140c9040c20000043e04c0c06081c01250360810f070003041725000005c2c035101d030384022142510740080032903007015403a0b20200c000b81002008142c40036401c004102c0300c000c8100e02d50445c0c403080d540311307a42c5940100030304007049454600c00c420341d807005000a58990841242c0d105548043d20001884d01c00000c040345014041e40d0050050b42c5040d090320300301035050300140103039035066070380040450580002e4285407040b44210121a00a154103110303640c880e01c029a0858080c111340140d2005040019095 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 132277994 1250 132276744 132276751
    0x312070c26040303090506030606072003060c09040f06240207050d1b091e0207030e131a150a051e0415030b06031501081f0f082e0506010e0603 63
    0x418800b250070020540e014004030702610058448904504100010501c00d000e036200044c8000b1208001e00010002c00d202c01c001d11a00900f02c440c40e0400d841c00014951110010301d0040d400e101e60501140d015010b40012034070210822541103078080c05044080f00515031440450280d090000740e80e544500c04144424098800060f000e40d410450481180c40c950101c8d22075400d20819040184046243c450803161000300035030f4904041c80d0440c1c8803021450060b0380417509011711140560070354003801260201d594011020404082040304940c6da0031041000c04104000382d4040038403d0b000341568064030f0304918412421090a914260040e0300580141405154880501c80c0d150044128009058913403a02e9810090b0159070700b296031a0460341400408804a4015544240701d2141d020306603000464654440e90840c80c105090310800c6150f01c240e844464140f1044a4500b44c0c003544000d29580000081e24424040d04000700500c1c1804445040c200807900e490000390311 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 132279244 1250 132277994 132278063
    0x309040509101d03070807080f0a0e030f03180f18010b0712030501030f0f03180b0c120a0f11071d06030706050a0e040504060e0102070812090312070c 66
    0x1912002c04819080710098402c00001442241c0724401c8a00301000303c0f961203401008036a514061814254501d100d08003403070280b107070300107840c000090b40903000b9a181c0c3d41c118142c0d1500400710034034503624090f140c810000c0201d4040501c1302442e100c28443d882510141004640c0407070449003943c2d25900b64400345031514000360540030442c50b04846901c2414905040250354110b403201d001c242d01a501c02002c0b60891503184007818090303070a2150910002c80000081c03034030f900143d83c4076002415484080d1144c503508944c03901c20b0b402a03410035031007542c901c04a104900e10494051008994248490040f41c2001c154588900103443c1c0d4180c0c508401906400c003d0145172408600340c0c010b804009081c003c025003a507100c1d817100d4821608480c0807419450ba030802c27900a01c42c2c2c9003003100075840000c4050402c032181020b41007200a8051100d01c603a10010300945900c20066840d007404c90040006082d513000d1201551064020750828480c1c3c40801d00005034911407084804 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 132280494 1250 132279244 132279253
    0x405070f0e042d080309010e160303021002090f130902060a030203040308060109030c09151d0601080f0402030c060d02090d0b060a050102030c0c0603061215070801050d030915020309040509 83
    0x50001800d01080d50f60b41103248108020381c900c0114540040f0060000c050203400004214000c800750042031001045a080c0c4031800201040e034800c07a44107210031009030044542c0120382e41c02d01d1080d034181200280036070b000c4085000c2041401c41d40140401c0000f0740d1f4009070409a00d0340380291200d0441c0c1d440069030303420705080152480030001c00080c10444a40750902c005031254805070b0881c0c491010101e1460021800c0c0c80c00f00000c1d0300031078003005864908078031850f42030350464080c3c2c80a0325400819240c1404040240500701c4020350182c2c80010b8441031403c00c8401040710f1500c5070320042c01c090340400002c52080b13002d130050310905102d00600016150150303180c0000c1c02d0900045141c00400c11605490340c902c01d840c68402c44001c0300107541a01c44548000603a243c1c0702c2a21180400760101c2080e5002c207580100002c0ca02200104945c00c155415030b4031543c041d01c404981c94a88404803040f09030742078120045003c01e00042c541a01c890041c5800b480d40d140160 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 132281744 1250 132280494 132280501
    0x6050f0114040203090c0613030b09060a05070c1a040f150516030e060406050408040e010305010c0906260a020417060415090c0b0d060b0d090203010c08010f0e0405070f0e 75
    0x1240e10702600140d031440360f44100b0500c201d4240002d0380d2650520191417a9454180c040025032104045520140c6403c092000300002030300c0103d01d0074410900003104000302d441d2103a0486601c0c01540c00206008040203c0030040c500030146690301c039105d1003264039401100c0d0340e950021006221000840d5484900303020400400c585051200f03401c501c0d0400940e43e40350203042c0e40d800b02070000b40600b550380c00403606006014084030090314050b4440082c0e940c1d80d01c2c0071402070641c2c83c001c10000b09848004510640300e000802c00c8030101ca9201d43c0f21140c10440c0d0058040050701e8917110f10703400c020000302080c1c60003076030401448008c01b809091a06040610f5070304a5049174132401032034840024000744900200c03034240c400100c0d0036601d54042ca29150010215608480c0c203090011442090703d80c1c0a801005541d4801d4000b844510540c0d4000c1d14042028000c15400d0103648034113001c1003598200032540305010f2022107000a54803201d0505c07205460b000002d14203801001c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 132282994 1250 132281744 132281759
    0xb04060507020a05090c04090209270405010c0807090605030a09020411040e101d07020c0409060902011704031d010509060c0d09080303010501081801140106120606030608100c050706050f01 83
    0xf090003802e040e10304207400d180c6440000043d00c564081d83c54030543c0400e06011a0722110140040078840c141030104102d00d40034030103110501110f08a03076640c20404140e10703c5110703010807401a4010349500b082c16050010a86841d04001d00ca075007180d5403100d8100140c0e9540c0680d42c015807610105030740d140d040030302c40c0000610082581e12030340400c0908010136081043c1c1d000400103582d00d03003403d544030740744120b003400310406595900038141030074030090000d1544a000d07003074400d807500c03402d182c051102d100c0c1e001001c9501030041000301c405e0548018080d02d00300f01e480d10501d06a0301c0e10040000180c469007018403500441c0d4003039610100020f0b00b00e8070901c0584407140003542550f2400000804c1c2d404020300e4003030100051003407508455000d400074281c216090704c04280d00c0da1146401490080d141c01401c0740d06040540001d1818003c0c8220810340c1c40b13500c00340851004c103040c040e0292005460b804100201002030402266052181c240035a1880c4000f000d41e5151601 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 132284244 1250 132282994 132283009
    0x412030f020301050a1712030906151008010501210501140910030b040f11030d0206220c030b10030c0b0405040c03020c15040519030302090a08120a03020f040b0406050702 75
    0x10303140c401610400c01844140e0343c4140c2e50040758001c007940c0303224240c1c007141141881009503100d0480c5001000780f007060140402c206200302c1c036408140c00d40c490280308101710242c041e44680c0101c1c45a100507c0194030400700b00c0d0b0a00b201840d0007041c0c0889850385801c55409030b1002c074000c501203040042c5494240d08064003c6012103648134500d042d511141c104c298094401040540c01e044294200054030b0018844608001e00343e070f40d810143c07200a900d44070120350b000d4010302d94010b0b61807007071100b040c0314110301d4110854107200781c11a5500b4403030b110007130480c407003e82c000140000010400031546000d4000141aaa103891601041c04140c0c1c00da0311000040c18014001c050180000203800300c22507180800340c0e5982d8646003492030511924003c242e1510020100240074150503800030f0441c0361003596400000e80e56449401e8642d1aa009143c01c651001c000c200f081a04c2030300600031400190a00c03d180c240d4600c076a8040b58401c0e40010089100410644150f1410700d0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 132285494 1250 132284244 132284261
    0x10b0105070210030209012c100318060b0d0210020d0f02030a0e010e010c0209091b041a010503090c0415081c05190302070b040606030c0b07080a0c060b09041203 71
    0xe1a5040480560000701d50150300d003070207800c0582c0400c484d803d0742c2c450030420310400f110710118580c1c8840c229a00c0214000c0948d040d004411410411110138840c0c4118407100003a42d205000765101d81d51410040d200390310582ea0300c21846490b0502680e40c1071b1602007451a42d40040403901d540301c0c4043c20f4040c020040c0001e540080c02018109500500410280b070024a0000300044426005903843c034460788001e504002d000e401c001b40ca120003e02c242030081514081100301d507101082205842108400044642d0340da207001d0a294046c1d0082c0d90040c5060060303c4103204400701241c1140c00c10b01c51142c501642c80810040c1403400c0c0300000850200e0310b0000c07040003400101405a00c1140c00940101c0c801c901c0303480001b4800e0307050320600d40c4c2c0852480ad5909050500300c01a00c4a40020b860100100c4d07000a4184454802c698407668403c02d514244520000b09603030a50140784165207442c2c07a550300031015502c0c2c400140c441d80c031580213282e840700502e9009080740d8452 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 132286744 1250 132285494 132285497
    0x910030c090e0d03390207080f100507111002070b06010e0d02150417010203010611070f0605180907020a03020d02010603020f130e0f010228050d051b13030203010b01 73
    0xa0314404484102150b20f00c8040820305000c6052103a00855409440c0c001c04804a200001c407140c3d10000c61702840950000d0b810343c200e4850701d4840d40401e45a5010300380c50800382e44403000b852400202900303c240e1000013400d0900d1420344000d4668140441001d4021341154000f440340c1c108690030200d04d81002082c6010812946a0310218801407504400a40f2902c01426080d0030902558103c2d0f001e4159001d00941c4405a101c131540030350001c2c01094080303030900b20240a003000000d2081c0c04c5441c10b1000c042020301e0044d0a844a912044034140011b0918174103001d6502e0b089811400340d4104c0e80200140085428002e041c01108180c42d011641080d90400c05640c418213400d108540490f442c000078050b1100d408000c202d520284c6140d4010030f03d00e0b01d071044042d03000c0e0103813082490038550105a0342d001030110102545091011801c140700d5499404041e902480e800405c0c200c65400d4100041d016801c0c5070001a82e60740107041e084000e0046040a00900540b03000a = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 132287994 1250 132286744 132286751
    0xc03040206070609080d090309180e0319090f03051006080601140603190908030414150727090b1f080606220909031d0307090216020910030c09 63
    0x2540041c50034411501e0241503540c54926920034041d03113004a405081c203540042081c4c8141d850040c00d958131910a9100c581500b51158050340814001c0044007042c55018628203544840109a007038550400102041036220000c6041a210f000c80c0d006140120010400e00e03205000640564040d03800103a45900300c040100b0808442c9080c84010b0f81044541c40d40703965580d280310f9845110b9103c0740c4c0c906800e002c003803428000c03104001c50081e80200034102606038080c80595450559141d000e00854541e0300040c1d001b4820030012841c50b011034041c900001014080801c92184c0d0f8116050f01507480110345400d00d0440c1c00340c0100461040c00840340902c0403070182a011000340501d014800028013084c03e05000c6109800f0400f00e440d540d81501d07150901c60004042c449411400310306205407800003030000ca51800c0784440001d008146490511200d580a90002804c00d8208100d0b0820350300142e980d040c48912071658861417601c201d01d58105030401c0301843e880394100524 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 132289244 1250 132287994 132288001
    0x16020a02091902070803040308011a03070e090406020c0708030d06050103060b0d02160c080d110a0c05150405030f0a05190b010b031306050412030b19090c020f030d0c080c03 76
    0x89501103581c0c498065107400e14040000c4059074044d109042c0d008105034000000c02c010190429902c44c1038410010880f10404001004600d051106840d501c010407401c1c1d15241c0a890084007070fa90281c0700b00000b40c100302e1440540351400d0303510b800404482d000824104c29604591043c0001400c1c00d185c00d2060920301003a402c803610a60801c80f40c0e1503000607160316003101c1c3c0045480e80740d9214018002c8030b641c0e40042c5480710350b075050000000310300c2d444450a010b000100b030050035800001080c40180b0b454104115100110341520846105010004456805200413503c201c403040141c1000012807820f10b050418000da050044e41c0300c0c1c1c11020100c2e12112040341503441904604c0d07500d441d981c0004000d408800030040c243c9081c070f0204030030030031070304032000c0452000e81301802009045400c0000811440071b00ea106500c0001b020450318045401c40d80c1424000d0060714000b05010315032505503802031000015003515205504c6021b640b026010b64840780110040c1c0c21400c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 132290494 1250 132289244 132289249
    0x41401061404020f13030305120109110901110f0111220f060c0602090405150a0f080c090a0e07060203190e0a1707051c0213020903031911030307030516020a02 70
    0x32050a485400b40307030301081072800816941d003200c0010421461101d130450352450001c10b90f80c404042951950265000014606030318015030b4801c0d40d4507042603060400b054011220034403901100c0c5001e110350940c2425a01080c4075040b00b465444d208669110600da41d1404c400320544802820006000700410950010384412400d0341c00519200420072402c0c10a480640110300e82d09500c640f500d81803006481204440301000301c02030391801d80440c1d480401440b812090300c84c2400a4200e14003107a071500c0c0c44140c80e540203800302c0c4009541e4121250b01490003105410040145e800000d61008010300c1200e001c001990514054a41d8503401000c900ca012440c1b113072500e46140b2021012802d03005100260190501030240890b0350540340d40c42040416004003030340910742c14400482c0c0800540219400c909016000310301d0300f000400380128005084503004d040007030105400308950001d00007140104540c0c0e0b808100d0342090003010052104480e550390540d880416402d0058 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 132291744 1250 132290494 132290519
    0x2180601090b0705070b0415031a010815040219050306120607020304090e0f0d020304090e060103021507020102031612080f061f0306030807060903020111040803181c0b04140106 78
    0xe4400c00300080e02c50f140340c030f0030f640303041c02d160410138a0a0004ca800b10345403c1c2d0070319039424480240e4080c480968030303611818125414090b85030004104100051064029001d03014141030003600041c944051601c4142c0c040362442056000a4000010301c20a45041801d2038112000e4002030542810880f8001e552403095100e4079030181d403915603840c0035083c1030040072003146007a803d0740d1669090407002901d80d8054061070380e42c50301e0a24941a809000900d080c10f9a9016001c070400c1d103011002c01c2999001a0004c03030441c8820401040203000e2544008c115521900343c0a00d010b2407020054900c00008000e02c0d0316261060030003510b6a5548203901022014000351101e105170310724100c0161110750009044240b00080a10070050340780d01a5001c02e0190b802040010742258841c0e43c05d101305e124990248d4024024a01c210065205212200320002c01468007411440d40440f640803510105484441d8074504201c203011328030480180c26a0014020081d03281072001e0500348 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 132292994 1250 132291744 132291749
    0x304080a12030e0a11032509151509090507050a0509090703060f030503070b09030301060207090e010906050f04050f03030c07110a0902070c090b0109050f01052d070218060109 77
    0x5101024030195401d0b4040d902120301086508180c0c3c1c0321407081e007801c6843c01c021001082c082e02c2122140400540c18111400302803142604820481c1c2c0381c01c04c4880030b01940c0d02c8061190040400004109441e8518001c0510290300c1c0c0c1d0f1a600c0c5001041000c41e01d0091401050103c1040040f84040e80003080300d01d00c44d0200c072400c00130345a40d04110003c090541082101000466011081c498004080c00040e8454110508503a5401513080d4a90000703115000169111040178401d000075608088900c4010000029200c5c015813219820b445003610724580d010956802e000900000740599000304100750010746c9581850f0145060f14420440060443d08403840303064520303903400001000809100c84155240c001c0350515180a00e080c0c81750740401031601e03404007030387d50140f001c0d203080710340040200c5810f0f40040c0c010b51f86584030380d0030340901d55030100080c141d1509403080f09025456014071140c4580c0c152042c091003260904000c04440001c2040004507a07122a11209 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 132294244 1250 132292994 132293003
    0x1806070c0b100503010501090e0c030a0203060103170f07081c0603080301090f0e0d020d08010f0501021c21150b09060a0302220e10120b061c02060309031b0304080a 72
    0x70030b0754a10b0007211650040d50840780d859400c0000004001d03903190051030462064406441150a0501c1016590702451400a4050704524010004141d40c4026541700c03500c03034004180f0300603100c1b00e00b00e6036501c580c10441c0e044c070001c0761503041010a80342d8a02071104801c401c005050031030321182003d00051180840241d00d90070070007900a540d40045052486180440e101e1142d140e5004e500c810070302c807182001036404400040c12811200c41c8000711401a00074006040d2780c0d07690542480c0d1000041024003000d06d0350910320080b484040880c0c1020554009070300c0d90348410f2030f0000c00312580900884401071000c405642e903800201e8041040b40e080042e80d49984050302e0310f41c05006c3c504522103c0c40030200251300306640180c644240607040c400081d0544914241040410204001d0220310f004400105c407400c0030800401c802d12000407090225501d5800a5110f500440740c504860b00040744010081c2146020382e454032101d40d0245080c9400c00c0c1880344d40c0e560b02c51000c1c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 132295494 1250 132294244 132294263
    0x1020c070915030602040902070b06090c0a08060f090901090b061002031b010b06030c09010909020c0c04111303050c0907020705090403030222080105061f170414010606081806070c 79
    0x1211030b4800001c620045511041c290345481c1e0303900d0004000c4d04208002c0e039a9129040019803036140070002a13204021005545041010241d001c5038004402007800f03401c0791801c170402046903156406948501d42c024004036460304a4a04400782d840040c0219000d1521500061021500072050703c41c2d84134200c4034650328103a000c0c03005025040100c50f694100c040003060120294106004005960342a00c428200503900e2a2030003c80c810744514031002e0b0080035011034545081d80262540ea0b420742c40f45410041038010f0b0040d0780125600464181d4841c0703410403c10b041a420745603004c0e000380080e003500e52038403001c03601c801c07001800141056400a10b860046e1410b0161852680507401e420000c00c0e124ac1206000300800d44005215000b01c0c2e0b4621006908031482d01c565607082d5a0301c2803003450746408102d0303c0c64003510071074060130002041d0010319024840d12000b801c0595030100141400e81030442d03241d082c0d25819040b50400420000c1c2160841102440168424181c0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 132296744 1250 132295494 132295511
    0x51609080a02130f020403050a03080f01030b06090406140a060801060b030603061f0b04063f02090d060906060509011208090f040f0618060b0313020906010504030501140106030e01020c0709 83
    0x750010030340c0b0f40004c800d00b40b0204001c41488400204449024801d4507100f0441e00c0b94030740700c0a8103d003488010071003090b00e40060501d08240049070b82044c07240b140070481c0b84003034001190103d01110081c240795075440302081000801d025082c02000003d190b2451400c1c2040483c3d22250001d105959114a0103401d01e100b0001c5c000034001403c24040300d544854440000030a0300c0ba48903041c0701e04d14080c039a0844804100d99170702c0001c0b43d8540298403803100b140e8210010750020300078a6448070781d412a06020aa090140b404078038440c80e00050581d04100400c600036406800c50404440105070700000504110201c840e804e90854400242103524000240076040c1302401209035030410030b0000b48100b00901460072012150414450b25031201c87c01c1442e070004444995840f0301e0000f1510250a025004c190841010314046240c1521394403110300791001403c1c40300b10000050010080c413a890321a00c40414a007900a528040c000607a09079140028050603c000f039030b5100c80c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 132297994 1250 132296744 132296779
    0x307060f02032410031512050307030f03150e090a06050c04050423071803140607080601051204020f0103060b0f0a0e010306050f1327060b0411030103081804020d051609080a02 77
    0x404000c100342c241000104a02d231403e036440340c000d01c200b200461341c00c00750a04810300a001d100e200d00c540450611405d0310706220326420850107042c0f181c25020b10f42c81d220100d5000d02400340301e040c42e1514559940d24210502041394070711443c6d01c894000e807610a5582c1d00104c0d2a8941156081c9481ca5843d413201405516045095000600982c0d00c0c3d0f4017070302c3c4201e000c1280e601c5800103484442a540c2c60341e00643d6548580c3d42c061041000c220b00140041c9013401c1480c400207010325000032403980300c103243c0e001c503070140c1c81007000c602c004514010010360000c1400b0f400300d0207103400e2086500d01070105284950000406100307454481070038104421690104a0794041e80c1c901c0c00d840d07949000c000d6215401a00240e4100d0305000343c656013030400d4020b11403000c19640b403140c551380c619115891a6003081040701c0040c41a07044008090380d542c0040e01c841c0f035100c00006614241407801c1981c0402644148041c0180c1110030050840007103510551640c040d04e203200c2e5074540406 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 132299244 1250 132297994 132298031
    0x507060c1b05010c030e070b0d0e0f0f0f01110f030403050313020a0f06020f0d14031306152d06030b13050f04030215010f170307060f0203241003 64
    0xd0989a010700c04542061160541140742845030f643ca04000c610300448500391103d11902070b407100b003041006800c8030754500d0360101c01104010340a448503c0405801c03903051a00700e6445014a0b40111441c0c22140020300c20018004d00c0f65008510f05100c411061491b4000100003038107000c004000101c0389240c46c8801c015195004000c0c101040d21812040000b0300c95009407401407041000d04006840005034042c0c00c0e03c060f0300c1b0750000c0c41c0b08072013410441d0700050001c1490004281079400240c140d001d800e0034202e0070030b60140380d141412a12810b4028a007a0a80800002e0480680f11211b007050388050360901d00d000306901e101d2502051080c82140312103c4164a000104420700b0000d0031070034044d9110354240e600e510b0100c06010742d280800c0c000c051608080c1c4a0800ca00b82c0f1240b540e0540c08a0002901e00348020780d100d05045500c000036082149400004028a42610341c9280285400350340d80f0441d116124800316000560380c0343c412041c556600000c0010100052 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 132300494 1250 132299244 132299267
    0x13050c01081504090b1803032205071a0a0e0f090a020a091206020702040c090f053a0201030e0d051204050102071401020d0506010903020f10050903010f150501020d0507060c 76
    0x1c1044c0031422903882e090006030701c21196280e0003889000c82c005129400b0040701e000e40105c0d12090422450100060015424132004a42d588074007040051821350034031100e00c02c9001320007000d45401384000c0103015501c41c51140c62080700788945402072aa120041c13240c10503a40031006032103c0c4050070560300301071544c0203280303807107030b0400c2800c204840f030380043c00c034588240c1e000d02039854012001d9a0f030b800709011b100f2044408581c1445642402c1564200810407040405040000c045403030422481c1c0e80c2c802c101460900c031050003903580602034040842c001d24028a10100c645500406034003860010400c2e04641c4000305050102c250142d40d14240c00141c200d0b4442d0300414218001e604c429094942507080c000020107640c0100d426500f1a0b8000d03003070000c4c4114820400c40d40041d80312500342031000c14003031103940761402d01c80d03c1c4610303c01d040c000607030003980c403100c9551806c29804541154410741201c05c1850f48801520003e65212402044801d060401a5111240748 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 132301744 1250 132300494 132300499
    0x503070c060b041503050703060f110a0503090a0f0303090c080304180908091801030b1b03060d0615080a0605010b0408030406050c0a1712060108040203030f0a02010b090702070e13050c010815 84
    0x8030310100c02c0c000081502403c6034070a5404210070a480728580c07085e112f0507078100200714418021154002d0040c001990302007100015100c1c2d001041c0e0700c1101d50300c807210301940025503948419041101c116260009080000000c40c102490410014101d0044410a4014646030000c5204103c8494261081c2c003900074010384010700058110000100240b105694025069002c1070030f1801c1c201a030055441c0e542c801c90b01c9e40c2c0c1c0c2c16051103a00d00d6211012903504d540c03032135000d65034218040403002800084018044005890801d1001e43d00d042e0406000400c0800081040220000881c0e049441034284982c55804000d040c0341000001d0101902411000013410440d42c000700007071041b042d10f000c10360800d80700e03c0c00440710100d089400a4250303204200c0041110000c0c0c024018403d064400841d2235501280800c000000c251612000b5030b00c035003010704c02080b24407031082e4080c0700000300c0149049141c86499031400310780000c605000d140f00220349141c0c200a822228641c02 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 132302994 1250 132301744 132301781
    0x19020c060a02031c0b060306010f0c153204030809030f0412030908030901080a0f150e04020a05100e0108040c090218090a0207020d020f03010e0f070305010b010503070c060b04 77
    0x2681c029480e60b000001c4001191100c01e004000691a40303d41c40c01d00001401c9035041d030b5155001500d0301d0861480e10018014040e45040002d2001c50b9041c0f26401a090301041401e482030b54111f07060020f0001200c15481581400110b0341d81c45580c0b94002d13003501c2c040c0029205ca40d485c0c2e04602ca0015042c100010010307010401da04601b981c0c130900c600c0303655210b103155a02e80540e038580c010130a4003400180f00320f020402d04003564000071610707550000005604a00d000c200f082c200015071141c1450074002013000f081d413a045014900804081c0c80c550000700e00114010f00c000411402d0030f040c8884240414240280c590a402c00390029400440d40d40408296a0ba0004c4003d030105108018040004609003064002e0b01c48165000d403c2c0d0014803034079802c200030108581090350f013665030782c8841c1141d000e04201c242d50484000c03000d01042030450504600703580d45c4284c000c0c1804810018001c50301d90110164400c590001000155903072980c0014000e80750300c0a048081c1c010 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 132304244 1250 132302994 132303007
    0x203060117070515030a0e0c181e0f0403181505070501060602120d091103010c051306020a11010302180901170118050a03051c140f13020619020c06 65
    0xc4001000110300c0c60400c5440d01a40c030400c10035081004440303208024403d001113184801e01d50020103100600ca8240c8d40007120080201d503035280200340c611480d003040803d1108424401d96404c5c03504d41d0104100010b8646030004290110010380024100800c04010320040d800b00000b60014100707030844002404c010710740081c4250056801239526500e441c00c0007440500018801103200d0050214508102181510100030078400109880e028014500d60750199020300c5250b07071213421511050348854aa05103450404525081203040d580078200d1000812015410b0114620b001d10b0302607500c0c20104c081145140722138002e2a0061313180c100114030106160030501078141d041c0000c006100800c10f284040c014981c4000d00181c2110500b100400d100360f004040c00c440c0799a4001c2d08024803200041240c01075125202081c1494003404542c1c59595103072500710702131081030618030a040d000182148600c0420811401c0c146916000680c001d004c1c0340300d0101300420140d210030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 132305494 1250 132304244 132304259
    0xc0509010905270a0e03040b0c01050906250c0b0901020c0f0d08150d0609050309010215010b070206070816031707031a1306030b040b041214030a0b0d080a0306031b0b07060203070c02030601 83
    0x100452702d201e440f542040c0000310b40c1e900024800784116451420306c01c0e02151000302070b1005920054400400030480b64000219140a402c00c2c0525141d6000694444110503414104004280d1038900e81d0010904094103a9005400c260407010310f001c41d440952070040003900c000201407004102d18180401c5000703000000c8081c1c07481c1035080c1c00769040b5480f010218001e94400340140c5007201802d00000000d8106107002e4414a40714110807490158500a80800b5038500c410813000101200030407108140b0350301403141c0285250400303000040d5015040861034441da1403150255050400401c1002415003180000b580c01c0003540e1182d0401c0c0c20400d01c4123000b207030150b8824103043c4204051501c240c840d07c0a00c401c5c1007038281140c0342c506001c2c010300042c0d146507a001004110340404611640c005002c0110075031000910541b9602c1d141c0c07012025802090062100c04504201c008030307120448601c0da900c09001642eaa551440030b845407510032030080c0d0184100c070004100e0b0b4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 132306744 1250 132305494 132305497
    0x1813020903060406060e0c07051009022403092407030b03010f0c0806040509150c0702030c1003020a0207050a0b04060503040501271a04030504031101020c040c0509010905270a0e03040b 81
    0x202c08241b0b40031130941d2458440049807041903001810355120301e130b0742c1d01c103000d6645c0640710480c402401c10313110316162045820a0018150361001c08900003050181c40c0900b003004024510103002004201d040102ca0510041d01c002d007240145515445468040e84e800e5001409102d60000e040050340c5450000a00d030381c004940060080307103040082101054005400d4800202c8858076501c0f5036a0b004a0f1301d05034001c100c08a0b0075124241c1c8004490350740f0303881070342e08081565005807074800582c030013480e0001550000e8000c0f810840148140298a800c40c2c05440071410b185a0300e03101c0e0301d082401807103c4647c07611010025881c094140d150910352241050084114250003644000c00e2a101c034006d44000b40070600c208801c000160808130800404d00050060780d11810380702d4041416250b0001c942000100006401da91540e0000f4284c00078000645446480c007001451050800c107403403408540303800d0300f4070020754500d886801c2070301c09141c40800d49441d80c2c0da5841002d1607 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 132307994 1250 132306744 132306749
    0x81008100b011706060906131203050913050105060d15050307061115011d13061d0d050f0d1d0d030c09050d0203060c1b060414070b181302090306040606 67
    0x580200c0b0f05080302d01504840600130a030003010f061804445e9020402d03254486041200901c5c4030400010f5440d0603100266a15402a29840c3e501c026180c01c02645c414a81e000500140c541401441542c5410043e42c0f10b10b0301d40e440004403490400c1c00d0783e414641903031000350306201d00350b404900150310004541401c48038900325003200704d40c00c03130241c0064800d02644003031030845d500b00e0ba003982d00d440d0003d40000740d407041c2080180c6941c4950301a00d4110325400402001c0e107804000078ac8041110341d80807081d07440c0c603500f0005c142500c54028403c102d84000341c02e488008034400000740d0030949000c0369440c0c04071070380303403001c02d1010700a0013400502c90081040d00c80b00040c1ca00b08a01c00e00b11482d80180036296035954402d00e041c80c0e400c42401000d00c5e076107241118244407420090300c1d00030750044680007946401404158030b0404030303810102e0f0300c201c00d100c074000a40029507118002042210b84621900302c44940030028014001c40c00c1d1b0610524042c0003d120700c03540850203 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 132309244 1250 132307994 132307997
    0x10e0105130c15050a051e13080708033f070306080c04060311040507140c0f0d030e0d260109020a021b010c06091502030c1c0c0807081008100b01 64
    0x805030f40d001c1c84507a1103080c1c8000c90102d5010490118041d1180c0014000c08001460703100d510450084c441c0b806400002c0b05481d034136103d20303044c0101c9004000b004000d1085600552a0041003091412204007101c0881910404104845c01445a004100d55485038104607262240741004c0000c014001520400310b80340124203141c2e010f03003814050703c01070fa41c00c401d040c400d19800f9010b1000522009009504100c01011001c89114584000300075002c1c40070014052000c140360158140701c1d03c6641d4009043c80d2a400c0403141e580800c1c00e04404815081c084c00d44450302160406010b44014201420380021001007030441d85c0354040c2003090400c1c3c2c201c0e000905600780074801c0540f1003007402d000c0b910640c00040040c26541069912901c034412484401c080d0800a0060760416100c0101c0d410011920105426401c4031455642c00c1c914818413000000e40d0002d032001c100034103007200300911130740002c001512007900c000003407220100321451031812030801340c02402000f00090 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 132310494 1250 132309244 132309263
    0x30f060a03020619110f010b010801090b010e1903050312040b130506011404020d020703020a12030207120c02061b01061503050f072a0c03110319080a02010e010513 72
    0x41260030550282415290301610803450010001c06034031071401c1d00340d840e07001c00c1090400603201d03003c1031002040103a400000480c1c03500c5804000344c4000016004241814a04414148030b6a03101030302c40c42a000548488861416442140c00c0a490540018115100c00030365010350700030340b024048c801d50041041c0a040e440d0440380900c5000c0c42d00c030207451540408010712005816407015025014002d000500d0401c41d10445000c4e070b08082020f4015801012048042c080d800040803101d81c81440c0031881d0050607aa401d03500d082e4410054204040d0000460454990390201c84d000c14000404240d1109409402800391806016450209c03d00011400000340240140780c083c02207a004506d0303641d24410111149011031305064214100490124160306140c1060301c01d20780030b100034905950960401c1c0b04505d50fa015290701a90100034401d031007018813050500020340c0b205071039a44510b10101280034284044950307115501c1d11701404444400c103074402481d24861000380 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 132311744 1250 132310494 132310501
    0x510050f012102030702071d011518030303050c070f110a09090819020c060c28030503070c0309051e1e01170408041d0901060906050102030a080903040e0c030f 70
    0x45900b500c14120a050103081503402400d021140d8001c0c6074404000e1040f1a40c1c5641c410001c20160005002e2480f210941401801440040703a40403c034600182444944800042410040302c800e07844080c0c01c0694410110751400800c45c102c451040d04444404000101402c0021414001d121564400c1c101030038001a40b2456015045d0101d4005c0c01d15401c0020502c17a140303c0190364800c0900b10b000d0302002c58142e94400014041d000c0180004100c0201d68910600502040e5406400016801c002200000e0790013011203034410018541000c2440e402d1400341c44a00e180d801160b4880200906031207161a0491503180280049030341f80188003003481c03001708c002e1003130060314000b540d10b004070700d1400d2400051075005031181c1c011903d46555580320364041e112861410b0400c01254041c0312003281c007402030310081c00500034200151445e190000c1d599100f01d09004080c0410140090006402030003502d000349003520005e5000d00d40043d0b1469907500c2121107100240179000032 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 132312994 1250 132311744 132311747
    0xe071a04030f0809180108010b031c030b0f0a080f0606060403050a140c030a03270608070f121a120d05090103180f03020d12020c0607051c0510050f01 66
    0x10004149221901624240c219118104290070b1214141c03030030030082006041c01d80300d240d9021080d00d07520002030350b5541002c68143c03d441d86a440948681e0011948600358110485054007542d403600300091b10740c10307007008254500304c55140c19030702c000741e42c0740022003a07070109282112404080c140d908641e52901040b01600550101500d03c0e8040141800080c0e40c60502d500c0b0900c40700112029031f5070040002e40b40034264042140080c003654180c0f1f038a00c201c18800b522122240700c0070201706080140013485035900629180400a0000340821060b0084604428802649105020500782260340c03031a07001c4614040d502440048000c05008074020400c801c43c83c10955450307142c2000f1000440c00303441b1103c0e200050b1401581080005072403e055801701c40d209402400c50f5044021001e41505189030020001c4c80c010040031149404c0403900a0703004010341400f40d120002c011040c441301807102501100340c0c1c904024882807044e0f040c5440100c5000325440f01001546000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 132314244 1250 132312994 132313019
    0x2c06010e150d0608010614010809070e040507050a060f0e01030506061314010e0d030f030f0b040203090d030510060c0b071106090106030c060302070f111909020903010b01020105010612090503120702010e07 90
    0x50403403015014070031f03030181d988626000707500a00c00354100e40001d516049611900d42d02500c1c01c075010ba00c130040802042c1040c0039628002c00882c18144046660010b000d0710141e1150740e028109581c58001910036a1503809585000c0704a055205540d0740b92640103504500400b269400b160402d4007020013071400c5045c60b1100c5c1d525645481103100d0400060740a8141c0081041c00903440c2e0200045989503840514812000f031340040985101d02c420143c110381c4050b25030b4640c0f083e00d2505010703e07504000c520480b02d5000e00c15090319540e648007124103000024071080c1d0b034001c20701884040c8005402c070009480c021540043d40030760b1020260105d2250b441d00a120b0b180b048514808104883c840e604140030140000040c10514410008080e840d600a00b09190b804240301a01381024420750907144001c0c0000c12040d410288068034001d00c1c21104000d00741c54030941800c0000c00e10035246007581070424a481c80c10842c078040d0280070464034045103441404800242a900c012 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 132315494 1250 132314244 132314249
    0x3051603081b0301031709031903180501030209060723010204060906021005010e06040b030c03060106120b093102041b0201140708060f040908040902132c06010e150d06080106 77
    0x1389030440c21003046c41201660803041015034103004080c00200c915942152800c0000d10a60352400094814008001400c0c601e400980c105403040c0b2641003c1c1e121881110615070700405244540c288541114000709941d40804d81ca0b5400403d00142954101000750155440c640a640601c90800b202d002120024400d503421003110402103405820198000140b0100140541d104011040e0101c1d150507002c1e40900d00040400c079900d02907240794840e030802041e040b507010107a828220714800030000d454090041000f442815031810b069000075814105601034002d1114034054403500d4a16840c84061001650a20a080310507952001103944101c0540e181c0428940340e80d0180202510f640d225190015594403031040071452800c06400104101c91000d81d841c030190f40f0080c00d01045521030b4200c01e40f840100c0c440360401c080c007c180d003e000d2008201070f5882a0040361100c401d0b20351f294000300146081005180c0800061403841d0000800b0f05c18180d658002038201c54071407 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 132316744 1250 132315494 132315503
    0x17010507020a061109101d01030e0c0f01110a0821040c0b0912030c0706140307020604021c021003050403180302090606030a020f0a0e04050109141303051603081b030103 74
    0x60540000074045034011203180b0f50070120f050070b1501030004200000c4c1c102c80c200b4089841e40b00c0f0361f041412a58440001c0d25800c1c41c0c00e21034401c41c00c0c840703940d0714000c0c42024466080d55100150300d03441403006003807000721242101d5680100b0705195096034441510119615840c0c811030340b080c000c82000350701450b84030202c4c6001c64502684401c554100a1003564003641121000b0075100b0108060070a40b1101005051454603110001c2c1003240340100160f008030052007049603143d00410501d510540540340c90301102c040c09040f102c4020240c000a5121a05640189015506511061003a8402e0701e50070100020490000c0136201c4a1000940c004881d00002c0c0740d0342080c501450304410381c1c6c40090700748201480300c000c05412107100c10000500b01040e0508501c1c05005e841c1c018482140204640c007004a50301a4400c070003403901c800e0041e00e410328001c051244080711801c007801c50004680d041c46203001469200150751182e805150b50000424030500c5c141202e04a1394030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 132317994 1250 132316744 132316753
    0x2010e1503040b0619060306080f060f011710060b0d0b0406050d03050706020c0f0d26060d030e03030319141e15060a0801031a0c0f0c070306020f041701050702 70
    0x941c3c0d6109034111008140c560050012810003805500890540c006455103450204020307040206152608040d001030b165140c1c0600c0c280600c0c02900010a410340b200040000e0640d8440c0c040c1d545083c2c111482c11b004146440340000d40c815a9801402c28042252014082e1044420421058074240c0c081c0d950302225204194000130b009a005103003203071003240d026041c0307218019918241202001150950340014112451642d8401621704114018448c2d442c01155041c042e171910710001001c48d805184150f0b20030b0141030003607149008807000102107940e00e00c1c080b0b00d04000300601100790250036061007400d007546a90040301c0d6100e440d100c030742e40e50344a03219141c10b2003121004e0044a00ca10f0034400e0001e940e00c40c0801020f15400036200e89516516502c0c00642c90344100180d6900c108210007440100b807489421510442c1105035015100c1c400381e880c0e2428050a07500080c134907031001403e030480400300e5000d8400c9460591504102542032100d4030300b0785000f152118014bc20 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 132319244 1250 132317994 132318001
    0x40b120714180d050703051f02130b0d0f0f0608010b030c03060402010503060a0905010308070201120b01091509080f0f010c0906090e070e0306070210060605040f0314010902130902010e1503 83
    0x150040181a502d1000700040001203054884609104c1142c006076607540040501c0d2034041801c41180d91040024101145068800e031400e440c020114029080651070004100c00425455001054440308400c020400103c2e05070600d0010708507485898141d5003084210748961030f010404003e400000350292030030b980c40d94011100e070742c4010205a40720106c40300108440660f4032406000c1c5100d03540160303841e400e500000d40401030441304034090904103000e14000d41da0200c0ca500845000700e1501c04d02d506032910070364404095810442c1c10388034004990504540024000784920581d4000308a42e8140c4803007100c021030a4041c2c040401c2031403030b040043c0032020f00e100c0e030701c4001840d00001c2c0b0f07142c080001e81400803d0728030350016400740d403114502c007405108103801000a82030051410389403501c0311400c8141440054902d140300b8032100300400007900264021b51b4010701148100a080c1c0d030344001444a5401640002e075960685000c0d0b0420b40340c0c0c00c114403511520a820340d034 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 132320494 1250 132319244 132319267
    0x11030114010309050f0a03200316050705030a0507051302030601050412051009060504051209010c0813080a08040e10180c0309020406180b19030201180506040b120714 73
    0x81040d000c2604040c1e03200858000704506000300007110001501400500d2a0340c100100302c0c14903c1e1a1074035804840010807800c480c00800c80b5800458042c149001110b94100281004200c1d44816010b0081e9481c0301d00700070300800c00c80b05440f0100c44050950044800c25001c901080358143d01007001000140003052280e511401c903103102d01c003100c1041103840c0d0300304183c1d000c05a08840f0107444c0c0c818002041018403030300700e802d0703000c030780050038001582d0000703054596071100649407150014030f90b0b610545028110000c1c050000032a0b601d0100c074689091180c0c001e1181c20b83c0e550394070300840c03054200c5400030340407100070b040303100b000070100380050009124040640c024903a6a00300640162290b00500c8014031810043d01c850100420742d0800352840d90602c02e1264909035810800d44c0f00b840700c01d4003540d4080c64180b0710580d003c001d1080484107a0030541c0c0c0000b000c50006034082c9a08001c0c00745400c918540d40440c0c48941c3e083e103450300258400034002c4024072040a13400c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 132321744 1250 132320494 132320519
    0x5040209070c0f1a15040b09060d17180a09060f06030f020c0f1e07050d0602090102030d1515023009040e061b0c030403030f03091415070201110301 65
    0x154003440c0c5094401043e5618848a107612011003040741072007500700f00c2e82c0161010210719000007524284100a40c0e00b000903040c4500400007440307040341015241c10b2207105c0410500d2101505012940c031050807202400c1d041402144030310070220071402181c014001d0190904980e110101d4045242c182041a406003000d200c008a904c1c2d400d002e01d19a261042215030408041e40025161001c840030140c500b9007900b440c4104658040c0404010139207035a405800c0301608240d0058039080c41d5030040b41148103051640308410f00302401948203400e040440b50451b40c556012411074100030340180e8441c0c480b00242081d0418440301e4002100b4141d41c4054403201840c01c1510313045203100010300b01c0d24007000041c000c0e88a1001c02c03a1610a24101d0703850300e0840310480741496808405d0517074034440c1d404001d08202421400300c9003d4041e03000300b1402c87e88144494400c00c1c03002e0394103036681707000d09032034000c00031038408955a540103200b0706c02c030b81039140c480038075580c240300303480359070 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 132322994 1250 132321744 132321767
    0x40b03011208160c050301060815061504051302030a1802061b0106050a090e0709060302060d0b0315010b0901080f0c120405030706020a0203031006030c0e01030f090501060603140a0504020907 84
    0x44a810806541001a00f00100059910480c5940f141c0c9007400c0034103007180c1c240d400180d45a130094010400d07642c020300d0519031044044038807040000d00200e007001c1d680225442141c0104144403031410280082d0080d40c07007501c04d90700c00c1003020340050100c000d82c004e11308060340102042050540501540040c400e001c40700da000807540179514400700758540351540c0040541541c80a400c00400e400740404070060228090a0003a80d08680000703a09115a1107140f09066403480c00c0000c94030140440256a110342c07064407144e603901e56010b401540000207003800a83c11100107840480b41c0351545024482c2c18010300e06100c8100351a40780c0020280c0196501d110604c01c43d40000c0e0729000600c501c00c460f43c06180c9904160404226805558001d18189030070a160641096404110303900c2c4d10400b4030300803da011408807100010140000007620550811401040c42030709a00265180902e612550015590f07141490040702d1054a00950100c078034030100388140c4c414141f5002 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 132324244 1250 132322994 132323003
    0x905060a0b1b16081c1b0809100305010f1703190e011b0203030f160609060c1b020f0609130c0c0b07080f0c0a0e061206040b06040b030112 61
    0x10025203070600c515031a0804044007882040d0742c402464600030078403c820a0a111041c8140c50604004415450b0b0b03414540c001c02c0010040c6109105901c81e186082c04100008042021040c0c141420281948071400c554000d1042001c1012500d02ca8070802d41260b040005121540d41810326909000d41c40901d03d07192484180200480c910a040c902e040c060301c561100d80c8600520400901840e10000903c0b101c000010704040240e203012085807003903503200404903551a116030ba000e90b600f10300b60005c3c0c401441c2c4425001040090340c080500f16880b9103441c25103c0c010600c1c2c1400008600c030003508200f0350400d000e070b81e0402c44040d101c85400140071010fa4540300418001b254800302044000804400044051003080c240081d0001040c0c40c0c030003e54907001000c0300356250050000401004000390100d40548a10f1164065603401000b455803602000d00c0055298010342e003280c0329516210040c4603626042080340c0c11101000703003075400e60786800e500312450203452406a8 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 132325494 1250 132324244 132324259
    0x3160f020307170316050301140d020111100c09090b130f1d060403031b020c0d0c1d100902040312030b0609060418050601180519170a03180302060301090506 69
    0xf503146641118007406542d0558807891720100500030844007000450a0280410051044003076100314035001007005c0d9a18854139007039100407610500304001c0c01b110b07806000301d041d80da44c1c00e60b0030282c3e441c1c080395200c1084546450f410000c80b468503600d5a84001801d03805c3c909808560032a0321104140400020807100c00030300d500b00c0c000100071105054000344104020140c06120b2289041c0c0c50b00c054085114402d1400781d95400910041427180c405c2d026001c013049025003840c00500103d43d00c86036111500c10040044140959003040341c060456404a072031001071081d41c003203a81050320701000c60322440d01980104200c044460b0031881c100031102c3c1d144c071504002c10050500c20f070b1072241d02c000c070040502107800142c5428104211403025036020005d050000e0242e410407525030321405000c40c40b0000760003c0c0e50085500c4000c41ca03410b00861000b1400000140c000d888100d803e13149000c03080c9007960f05010003507101c80c0a00041c450180d540d407019512000207400b41 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 132326744 1250 132325494 132325507
    0x30303050a02120412020601080303070507060203090705031c081608010608090313032009240f10030905190309090b0d0f1b080f061302060d110706060b03160f0203 72
    0x265800c400c01c54050343c04100311a861400701b03070f040000600401540010310f08605280350010158443c030a800761540d42c021020402181d400c0c0a00b0300288001821078038000104412808510050f03001140400c80000001d86810014070200400200941e600840b580c02e00d9415504030a001c0e222041510003440038010701c466007140301c2c0241d40a08000b05040078000701c01400030405105040c041c2c0000014080101c400c1c2c11621040640880006444214031000c101a0415024959400f54605c4c00c41c0d0340954040e40403001890054096905803240a090300c4d40c16001c40d440100010f01250f010000203003164400303030a41e04000d2241d10a001c030750f1211018074510200603114182507061030709642d40d01101d01c40040c4400805008410002604c80392288002071143ca20300d10180700300411035a40400316000d42c03800004c2084800c036004c1078510707180c1080008844483c03500780e0100304100303542e041c0c80c4108103010400424074408034003200c0341c4218075080400c0d8407052042 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 132327994 1250 132326744 132326767
    0xc0c08060c12070c12030b03030d090b0402030606010c0515070c020d051006171f020f070c090b0609030a231f0f09080d20040303030c020c03060907030303050a02 71
    0x1034038040c018914099458000c0707621007200c4500b02400c1c000034008550a900001040c0c24648900020b00381400074034800c500010a0661041d00d80070544285001030a60030004004c0c19036005d103009404540c42075886000540721080742035006001036002005411990030101920b40d840800d510301040c0d0140340d6404503807a500c0da60802c0398160480c3c10001c0940e0504d1141000a080f210540740c90410303103105650704e03241e0000200070b82345c042c026510b000a00d940c048812100e008906a40da6214605049401100601403441264103080341c200040c03a11005441e145040180501030120055645491103400220300700030180ca04480c414500c40f0600004a82c030070b86030060310441194005020403200182a429061490f14417800e01103650003068845003201030000286821143c0c4501401001150305e880200c0c40019011080541c59085928030100680860301400f01c02c204054448004846c1c1082c40e03445090b0030401301c7c0c41f1f50082504504514001442c228070803e5 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 132329244 1250 132327994 132328003
    0x5010f031e020411071b050d080d021605060702010c08010b030c0306031c020c03150702250504020301090c031404020f1005130308070b010e01060f03020f0c01060311040b0a050f010c0c08 82
    0x4544451300c0f00424030350244100503117020408001c0030040c0300807500707040000e100000c903094050309580010429107a83e0351160f040320001c1c05d0040c00c503001502d4520f0901e0740e07a8000c941d01c5005500748031860603100d0040703000e075050701e00213001c403411681d91030441d1540303801c0107207416494030030f009100004040d114070000c1c45240c56805400d0a03072a2000303142c90700d41860b620300d100c0380c1c046c010008040da01048070240100429060003003154208046c01e011030403508070700d91161000000242c50038140e401070300c0c0000542c80a00140c00100c2688064003000c540281d04002c0300030b401801840c21589248003640d55003032083c2000702c400b40c0407000203000d81046a612800150080a01010052240c0100701c0032080300780c0e9605201c2c00070983ca07a00c41401080c59000f00c1d400c6001c0c0403140a5450300d0041e4002041035035a80e09005820300394520301c2d02e001d28074000003c0d040381002402c03c400e170b4001038401029503030040011100c88803c0c02c0143c4100a45040c0440e25000910 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 132330494 1250 132329244 132329261
    0xc03050c011e0c030c11060a0e0307050d030b0f0d020901030b06040f060803030708130c0e2e03140d020a2d030302070b01140906042c070807060305010f031e0204 71
    0x450001c1c140701e0503c0c0c050115440c01c603c020611211401c6142040300020342613a214201d9603010030000007141e2154518003a00900810b00c0c0194424030218580c10740c0b1421400c001180c98403400070804080c08240488688041d4000c1c0750f5000500c040781d044c901e83d80e0441c0010340001880b9004a02d803004031640c50b00303c804690000824000c41039409111a500320401402e140303030040551f918a121011148180107909110800140c5146411a1003d6000001d51603900004403000d1002c05003c00c580811035400c05000041516014000784d100b46800c2c10303800a0041c1492501d4840303c1c1c01e0701400c9014a4661209444115000350700402489842500c015850300c00f2443d20706107800058101d000b0035044030103200354a54800e40425040003054900042e030f6a044038a2148180c0c1400e0b41c60417442002d843c03c414000c00003440f4044580c25410f880303a090b102d00d821004d80711f083c0300e5000c03d41c8041c0024804141790900c106980e40c01c8020101402d009540850240e82032603 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 132331744 1250 132330494 132330551
    0xa0801090807020901090216150b100f1215090504110402130f0504020f0a0e12010507200309010903080a090f060c0605090d120902150d050907060e010c03050c01 71
    0x42480c02c118284501c401e405002c14130000d40c2007000ea101c0c1c102990103540005440410a031140009960759075100744c0170440090603081c02150203010140880c00c15004810001d1402d0039095111003452196151440003003030760180c4130b0300d0070881c007000e00380142040c3c400300091030500d48144c1e25031000300f42d84d159018250000d1803511030b9400712071040e81d01c55401a03004100b48149a400c501c102c903900b8005003440c41c540d240310404182c82c62405500c1e618558139100a01239155000400140400d603100c001d50f1918015564040d01ca002d60701150f03001c2100728200380001030002000d4826001c442c03802c00c0400d55100c0300600205899408200418002041001441418001c5980c414060401804240a040300c02803101d43c5c4d40c0f403901102a516038002085550302c00d14226440100a2030350740f00c2034200385100c0145015581c04006129801000415502466900c0d240c00016124401f000146403003d60b0b080d07015004010583d503842c40b011080c00c1e2103180941605510 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 132332994 1250 132331744 132331747
    0xd0203010e06130608060708130c03050303060f0103021306080c0706141602010c020703020f0f040e0f0d08090709050408090607060618060509010506071403030c031005010813030e0a08010908 84
    0x1410034810000050500f04440c141030141c24001c220000418640200a82c58010140ea840c001c01d80c0c6010034074413005001190751003000041c05000005180120411905c4072485626040194220f1150010b030125000d00c4e43e90070024540a400f00940c000440d080c85440d110066039454102c54041603103242e17000c16101803060020b1368900c8078200d90054002000083c9021801035a181c0c51480002d105104010501ca5292500c80a45420020103072003800740d02c000040007500d902c00000d1240d12392060700d941c80a0103220703c0041d40184840030140010500f4043c01d613000e450024001c0d03031000010444c04d2410b4a4644c010b001c0c8900030a000a07a45013040380301d2180c004090a03030100d890625400380503580d24028605c0c11214216003003580c5a640e0305c1c00040060b40465008001d01011081013192500301e001107209000078568100c80c02e4035000196450341c810b0b5a128540324140419100080c0108405e40312094003c000c2e50685a030740e007405094804809088503c0d000 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 132334244 1250 132332994 132333001
    0xb030d0c030906031e0e19050a140c0d290405100f0203010f180906060303081f0605030c0c0f0f010603030809430905090606030f0c1002030d0203010e 66
    0x510000b501c1c00b51040c1c0c54240602051103051800c5802484030980b1660380c1d415501002c0c1d4003c108107800b0301c0d8610580351700300005080958030b80030010f1094500424400c0c1c0a0800e00010800c0d004241000b0305880001c0101d0321984080d50440041d052200c00d0002c1c00f15141030007050081c46184244001c040c004900b013025401d6403044104003660b6070060005000005c4840002001e5030324000343d03c400650004100c030040c02403200050329940c9002d50110904da44020694420b00003000d2000c01a502c404982c00220014491103000502c28000304242022030b10090041e2904501101c00d40707202050074606028500c0c0482105a55900c020020150040c3c0f401d0740c0880d03900090308880010b241d405407031804502010320348203000c0c0140d800e203c2204c03100802461a01c0e00c0046000c0e298100e84000b00b0040d0b40c184440d11a5000180d800c2c60f000406060000d010300c060480403400400707020b0f071540542c038500150301082c040c04404010500c05917000703100302126210383c0e06 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 132335494 1250 132334244 132334247
    0x602040f0e060f0102070608070e0102031312140c060d090510060b03150a14150d0c05071a19050c07020d0c030b0106020f03030f0c0405030307050607030501140f0402070203010b030d0c03 82
    0x40001c3c0c01c605541060204010301c0d6000143c031580a0981d0600480100d10040101c1c110711615580a054000c852000300d90215601c1e010300301c140c824400360341507601d0781641566481c1d4004819901040402c4002c26060658106600300c0b44120200d800341800001c400c001d0365216001090703008804820002103a183c2061092860f0040c1e070034480c2c0d24249520f0000004e00390600d60301805c1e082c0c0c42d079124070a0b8101259000c007104041004001140080148550320801090f1907118110002008012685803254000c2001c082d81350282e024054030071010700401040d000003018244500009030700e540350300d040300c00c1c840c0814170075060940c0340224880406070002011036004c0345502001134000811260060b5124400d4a884d6176220b40b049100c0c480c03078200580500001c5203510030071000042c01c6000710090b440030320040e80c0b03c040740d40280d548071003d00d600c00d10002c00b1001500301030340200411400600041451422800824642540803050200148581600c1402c0c035 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 132336744 1250 132335494 132335509
    0x80d05040302060a112106010c14060105010f0f020d21150305070f03021e030a020d0311010e01020c250e0f070e060703080f13050708100b0406031e0602040f0e06 71
    0x1503482d4401ea041194000050161046c1411590703a00700c200c102240c2c90742e0013581d41e03191690740022807444c10000e09242507125030082c85210301051041800200540c059405400000c0c416402444a41e20400b01203900942a041c400d4840d446110118a100c03035034041c0500325540420000c0517545545841c0c3e242804681c40b9003c0d03422000c00c1400140d0b90050500360004c000d02101c501c01001400082c140306005100075407012030208a50100f541000360700c0440160a0020054002102442400c0c0d21a01c0c4001e10540c1090030400802c100360150000d04030720900007503004948950180502c0103042c0d0b6180c0f9440e0b80001008280c3d03070310030403038000010300761086820250155400780400030054440c2c05400b41c1c20b07000482c807810316584484601c1c1c0040c1103030191962580389540f10880a814000440c0c1040072440160900d8003c01049070b13440341c026802c011802408181511900c00c045a200e17400304000034855948800b40c102900e82c24075155090300f0030004004c4038 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 132337994 1250 132336744 132336761
    0x109090507150203040317040e07030e0f06010b0d2003070c1b0302010c020405090c030a06061403070b040b0307122a0c0b0402090601051201090e0c060f0a0c080d05040302060a 77
    0x2902c40c40c0111a48594044150760880354812500350700059031141c1075115006a81004140243da00100488140d160b004815070320312003001c0e201307600c03070b01d5102540340c26090080f0341c0302c00c6003045440d003258410790004051351610500c1d03e02095040420268591080c0c81c03071000580003109010034090040800e40c680c807240c5481d1145586158000380030044803500182c4070741d036a540082c903204010f10694050440040c1943c010f03014510302100205000d001b00080484081c0502901d820001268410341d5005884030341010b1400c52038920a51006061004002030515500c401c40807a00805007000d5004000394440da8141e030341c0204054040d4071200400240802c480e01085c0c0064400b6000794040c2c6480180d03542e0f0a0050740c45104104191282140490000482c0106075102c004061103050030b59074036250010804c0414000c226560300f020354200303c2068080c1c02501c2000d90076204445140c00e291620041c0d10480f42c04031815000340e0001000c01c0f0301e050380c1c0d104400c0b9 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 132339244 1250 132337994 132338009
    0x40317070201112b110a0b100f0302032a030f01090b06040911040f061e080d0302120f0403090e0411030705060f0405060904060302040c02100b03030a0c0803070c08030109090507 78
    0x4000d8494400301c0e034401904e502c442442c00b030004c05003101d501c45c21000c141d03400d00400300d425401207442c0c9150b0542c000c541464513006003450120b10944000659070441703400a00401c480304480c003521110703501b500000d2085c00203903070070580070b61014083c040c141900c0a00024540104c2e003007203051100011301c520b104925000c03007500000c001c4150100c3ca0242580c00066044c4601041002424a500030014546644c10026000c0040b814224240d8040009032541d40c4100001681680110342e01d02805145110001c1c00341a08d0409141d070050180c0741141141c1c1d503c0310000610101510255441c8290300d004642c1810f007004040002d000c25680185082c40f514a8010140214000e85102d69070000b400c0c41195030742d40144000d10b80040c01084000311400000c0c3d552041c180804030401d0801c100c00b281454080309541074a40c071500e40352400c0181d643c906100b580014091310078021442c0f02c80740400c05a9001c0c50290080032400644940d0600700645805c805600494 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 132340494 1250 132339244 132339253
    0x3130b01120b070906080c0304060b060324030d050418090609060926030a0c0207050301020a02031c1505040b03100501031103070b04081c1214220b190204031707020111 74
    0x3589034041b481a40c400e00c012242d40d2079880300c0c50310a01600c40000100e90100010003881808100c02e00c0310b1030070f40a14040045440311020130300d030310b9003404518400416414042000000e40b001d507940c0b0800b10b901c40011301c400f5192b45801c00c880a50905442c610340c1d0303041e01010084059813022a0300711483d0340e6060700340c20908500340c0d48401003d00c190300d03440e0a1a55070b200c0c000c11401004d804010020b5440e61140d802c001d40c2c1ea0001102c01c0d42c2d01c1804844111613084620a04a440744000d01218030242401c0c00c1c00041c3c1180b0311910382603c103404407540c1c42c210b1882828017030341c4240d684003e69840c0720101440c0402c2500301485640040008101d10300d400115a40b4205814807002c6c08003c8500056178007121898500750b0303181c05c1101e06d951000c42412a02e128070418a8400600f00c4035141002e4400d0030322600410318201d0f24080790418450600500d071980013088058075003034990350380c017045030301c1199405100a40454903030110368200c0016510014207030b0042 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 132341744 1250 132340494 132340499
    0x12102031f0605092b05060a050403140a14030c070b13060f020913090812010605031f150c02041104060201060305010b0d120509060f0a051b07060509010503130b01120b0709 76
    0x900c0a40201c4d0740301020043c0d50301d8515803801c80320341c92170302c1d950410140c1e40c0030b1400c4600017010346800c5400b00c00044036181030843d21800d81e0161080441d80795110000819110740003185507001504000e0b1158040c0134070360008201c042c91511a01d003180b210070016400d4504030040d03a442c00780c032004050044c8010711454982c03407800385041c1001c24000c43d980c00107013840d948501c40d80d500c1070840c614030400803840c1c0b50040d00641c02894070502c1902c3d4643e00e0f25040285503100d00074513840c00c8154071503140c03007881842c060401034001080000c1e0f5601c000c44040240c0d1060713001c180981d44455040080c45003e100740d01c54420203450392015022596907429450f50440100400d00c400492070742c2d910f480759800d0310034030418988403e61714800c9600250030380d081200e0310345104040c003030f0711100c1c41000f14040c02100e01c03d0300d0b203d04003050000191802d0308001c0c8880e220b88508a00c11000c2113100c10402e000300f60710103042c0091001400c0c540c0441200400344404d1101c1c0e21303400c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 132342994 1250 132341744 132341749
    0xd050a0507140105070f14160f050d02090106120605030102130911030903030601080703180c0302130e0601050f04020706061203090f0e0105090a0e010510050a090605030c012102031f060509 83
    0x5c07940402e40c4800111404291454480d6042405074020301062144205d00d00c0003000c40301c005400d858070035100381300c0c0325501c804010094980090094005540800411841c0e010320000100c5108110011a421361504042401c84c0c001d140c0c2d041c03404004520030061401c452286480c0246041080e034518603102070303010b650344000f41155040180c6080050b00f224400d6000c005400c1e000d090340c9400361244d042080c0080c200c2d020a80c03240c0c000c58034071031615019106120031540351401500c441e03846c0008221030b84003116001380d045902000000c00085040c03082c0005400c83e000c113540000180e080090000c00301c2e401040000011240502500c4960610141112000c55144215a5850003030038080c2806502458044d0b00348003c0c444040c081c2d0302200c00ba54000d4403024021070b504c20b00d40003074910600c603064043c1c1000e01110001d5120b0300c019601e204040070145010320b14083d05d101241d0048465008034206240210005500086603030000c200d6480c0540c1002d482800 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 132344244 1250 132342994 132342997
    0x24060503190b06010c0606090f0b010518011b020d080301090c0c050307021c06020324040911090702010e030d0609060b0c061302030f070b0c060a090308130c050d050a0507140105 78
    0x80d16030b140e020000740c680d03807088880c0400581d100d00c0c01d00c203880d0b03078942d060041c09010b40c84c4920f45090200512070380d4440d00990344101e4400c2c01c2030790403542190055039585a52060042c400071034000d600050385031400c03048203640c1314088442e5a585042d03440c0c400c0b1343c54041750404120071440d2100224030008250f60440747c045802c00c04d44d2a000040006520740444000c0c03001d0300120801035800d040c59001030848144a40342c40c038a82c0340804000c00c86864010003030140c03c500c07541054a0601104050b4040218000010001c289050192440d00440f0349000c00c503480d4a02402500345038040da02c01407407a0134402c1e041016185c4560307110040100a07803202d80b0b80e44001130642d0350030084200c3c00c00c001d4007035580a9880c3c0100d11041e030301603441420f06100d003102103000885148540440710b900743c0e843c0d440541726140001280c410b8036030b003650341600f96003000c80e05548a04d60340c80708920400061103143d07014904281010080d500000c03194240454400d0166000380 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 132345494 1250 132344244 132344293
    0xd0903082a070b0c040f030f03080109050c0a0e060f1b0d021f09050718090c0b0f0724050117010e0c01020c120f01090f0b0f010303050a0c0f24060503 66
    0x240c01c050315510080b04c1e10a90017141d012000480403101c1c00414001e0500000d030105008c2e60b1f448416a0b00d0700c07100c4007501c006035030280c84024100b0007000c06d030b44207202640c01c9800c01010103140400001c070f1605150040c2c8a1080800e49a0b0104200040c04000803400f00440c1c0c0080c000c600181000c111007030341903004c2c001411b620f031460382d000c1000a12105025188624074001c00080c1a40380b00c000b000030b050308880524410101103403c14030302060b00c5000b40d04491840c50209035a0720804480b242010a001c03854179814080900b6101e401002d0182110100001c450ba60042080c0e0940390002036902464014558181590341d0100b04403501030340903100c00441ca070141c18854941090a403041c00c1a5103000e00f41c2c820003445440d1110702d0350107600940020f443d02c01d28014510800e01c0000c1c0852010031103910042c1c040c0988000d9a40a00c00d040280d082d6529008000000300a500034000e6a40580b030b8481442c61203508090034040e0010980c1e0209040034a007a41a00d0b03 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 132346744 1250 132345494 132345503
    0x10806060d030f170a050a06060903020d0f0f1e12050a02060105010503070504080f06090d050315011808010504110a1202030c13060503031603020709020304030813020103020d0903082a07 82
    0x81060f495070354043c1452440084120700040458a80711102d0002420262468510182482c0c400244544a40da1010a0b80d4004011003ca1a42e9070360351078400c201076400300c803902a0304a901000c10b070b0512900200c1c06042102224848031450620900c56000c0032410520609011900e40c0f035600081c4581510028200142e403911910f4003503900d030040c1c0c5e220400e1031060210104011314041003450007103404004640e00304240d52415035890000b105c2c1744983c8005045c1404481d803081c01400200018803510400058840400c03d0a40d0b80498080d03a20410f0400341c91483d04195445800030322200c0101e5a203044942d0020361549200000c1c6845192102d802546086580e4801c5004100040840f07942c0d80000d8031021150010240c20340c094015500002a0000303a40226481964150b0324556143d0b24641d42003038280002000341e0400d5070900c0242c4400c4020311803022814080d840700c444ea07282684814204480c5454000c145c10100d5040444005c411016201010b900 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 132347994 1250 132346744 132346757
    0x906180915090f0b010504061d04030c06140f06030303090703111c0c150e01090b220b040806060301060e180c10081e010605091207090e0105010608010806060d03 71
    0x128100500c40740c100000006109181100480800c01c4040303032040d550303125501110319030381c0c0c0b43c0c200011620507200ea0b0210344519510340e40c0d10a4454950703540f061280c1000041286644c60f14001c40b28030180d0442124103800c180b03c0c03050075061500d580500e00f10011480c500d46141082c0d00c804443c0300c01422905503800e0b04041e540d960408031000b090312200a04002414101030110508a1040c5000000a034500c0e1110910030031158400d804181c580c800150b10700044210300780e01c00b030a040407082240441c2684001802c03000307802031102e8422251110b003849652418801c1c0507081c3ea119a2418408100724501d9035010780d80320310540c0d018030059020080340c1d800c0101c03000020340c0c00310725114140c601079000303140305024120079404821030303215504601c000804203002744004a50140800816842c040f455160100462816991580c0c4d85c2c40c010b106490390007007020700c965101c0340180051070740b080400b40113000103001401a404c115000c00d6000b5050b44000e41008075 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 132349244 1250 132347994 132348011
    0x90f04020403080d02090111010e0d140d0e0c04060602060f04140f0a03080411090601020c120106080318030d2a020a12030c030305010b09090c0d090f03020a0507090618 74
    0x1140d905407001160029601035070360154820f204001d6200e40c0c00305011886444014050038070511907102210100001444070200303400c4150b8440310752a00001075007000300301c2c03000c242000307025803803140c0300000c01004656141420001603460540100c000c6600c0300c800c000e44001415116500150000041848200b0080c0d00d1420b01c500d100306812113102e41140142056445401c03d4441c0740513501c41d6240403a120304122103000281c0c1ca25006900040200089180c01020f07000028031000000480c99502c42031a410b40c0c010010341e6070382d16864104060141400e100d505441682d501c1c205c10170810f0200c864034408400103042c50000c420800800441d200c0c015640042c11442c000c3c040f5a145918000301441e019002c1140020708210000501819080594a400030010079203042607984841c122100e0f040503004014190300d5071013000c04101c0c6000700354072480c00396001c3d227100301907814034074508441030340306040c0303d4a4898204481c1d0711441c490998407090f40c030042071110 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 132350494 1250 132349244 132349249
    0x405030403050313094a071e140904060f02041206091a1501230a11150c1c29010e030f0304061b12080108010b0f06090f 53
    0xa640c0005000c3e100008075040207884840041c1d0440d01a18010b0003e400503401485404800140940141c01d005040a42034442071004080c601308811b020030300b0103102d00030a4a404c04561000790060a00d4400d17000740044104520043c0000d00080c5001301d800d0000301d10740c104004c0014010941d00d41000f075100e201d540480d80240500c00719000300d0b40b0181084c00090036001c07400c6400c600c0f40d00003920900e500e801c840b881040092924410b8800328001500c841c52003000c152400c0d90014075000008298501800c803200680d1b40c2c01303802c1502d000c0141e1511158080d61013211004000300320082001e0740456212061504030220183c1c10840040e0141c1285007005903c40c042c81d0f030641e0400100b810400380c16800341d0b58102c1c00450314092503104d480d0000c60300c000d5003040109000c10342c0501e01070081004244031030307409060b043c1c4440d401409002c414100040b240c000410001109010703400000401700d41c04640302c041c01c0d001409904c01d00d98100d000c0c203904e0282d180d096 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 132351744 1250 132350494 132350497
    0x1020d05160c0b0c10060b0d0b0d05070e0709060207030b04060221040321090b0a09050a080304050105151c03030c0203040f0e06100c0804180e030d05040b010b070308010509040503 79
    0x141d0004618285903252114241240c001421070076891085c448041c5860402e40142400c40b07c00c040d1441ca490941c5000801414420324000d0300400f82070b5040d00040c4c0200310110003009041c248410320b00388581c0c003d01c2000740394051b000f15800300350306001007002100b12940091b40301c41c00585c0d40d840000c0d81d90048108400e0b20301c20381959010041456003160307088900000380d0780131201c040303600120700c01190018500500105090400110140fa00354811052103002c0d4007120fa20780c13460340e81e1822990088800f100d030307a51243c00340040642c940c02c81c9260982c08854900403110980100c5444020400000d0100340c1c03031301c1070041c03118000d1003200c014007a15106071407950f8594109038031910040c1d604a0056490700024045240703d1140400280c0d8000c62040c41c0500d031032220000c118101c2c0d41c0310225590b031031407846900c0d01040184402408490702040914050805441e2520141d003e054814400c2002d0400290b11011440c1960001c554000c0503855a0418038a035 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 132352994 1250 132351744 132351787
    0x6090c10030605040e060103050105071106160e060310140108040807150b060403050106080c090c121b0301090509010c020f21040506070c1a090a060c140319080f010501020d05 77
    0xc1341c580b01003050403034404070340203050380d008600a00954a4084080700c1106003080c214004d030f002000856031810080c4219560504c0502c2c00c10104800080001c03019032050ba6403110496080c00108850791414220240754642400c1c900140c1c03400e030325106036900c617203040180401060804100d5501031540160801c0c80c001c1d0040ba01c85403a864140d000705510702450780c03288a940481d0394a45001400319105000540c1d041d81000c000c03448182c0f14400c007605090031302003031600f901320b0000c00c10042c0d802050008404181410140034090031100900e02400c1150001079015205480004081c0e6034045003a6640000d0904901d8052090244e500310951092001902c1030074840051140d9095947d1107040798044c83d001d2003032a100d485458074140e00158203040412900d1700030034502d44814003404060021040c042c24180c19503114290100c0048080d400c440400783c0c2c060040b6501c0036040001c0c00041d414000041c5d600c48079030004404001000450918101c9000c00c108c60 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 132354244 1250 132352994 132352999
    0x5090a0f0912180f0f1203030605090720010b0604051c020603040303020a0f09051f0c02040903050a0f0c050606040c140304030f171603020a0203040b0412020f0306090c10030605 78
    0x18901c000340700401c3d082000d0001040d94942c81404503401d104071004e4012201d03000c8803120000d1600e07092004103141d6017000d03004e240c2d40c1c40c80042c1a840d01d00940e031203911a9030b910b455000143c3c0341d64840300191072001290b607142c943e050ba401d8844a088400756007080314501810703084a0070f0546c180383c8222000390803003004001c2c0001c054041c0c010700a2031806488248018064072070031179000189200d03060340b08044001c8407010b0000044c000101c8000c2e4074110184c001550041801c1c0c50b0100c00442c00a02e00080800347c07150701110010a0041c40e1920f17840700e00d81c03a02d5240d036909010b0700252060b599400d012840501a5042800401c402503ca5440749450304015140c14100c00951021030320741c03c18210400101402203100c0c490708030540303120b210501d004400941181403400103620003004003042d401684000744c4000c050010410b09090740c0d40c4188881600d411412902035030042081c400094030200741c080346014180e80e5031402c441d20b80422806040345522254 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 132355494 1250 132354244 132354263
    0x1090b13230405061206040305070609050604150b040c0c0b0601051b0309030c0402030c16020109051e040c020c0a122306040212030a02151b0c0615010905090a0f09 72
    0x84030700480d04400611070121001c201d01c3c0e0f100003e001940c0307608010801190000700005000900030406440803034024500005c1c141c02c2540e580e46080810f4a007036601c0e02610490740101d1050303018440c407540040d1000c0c04501e0817841c000e048040700f18001010305014400181c001c2c0d1150003652103041c0701000d03015000280400e01d44e02e03a8822071089000b0b008490b0f520600e802c1600849000d202e40440302864000d0312868a050211091400c0741000b041c0240051103942e2a075001000307460340d400000190454404200440348512556015500031640c040b40554407540d83c0d030200c601d014414180c140c4540b9080340383d50f0085140c400441404090b010b841103000691a1041e80701f5582c44450046000d00307642d8074004c0c1400d400040c0d02c5075074040100410380d4900390f0031014280c1120015051001041c0280e040700c4640000d41e0b101100704880c01e1201604000304100070309180b54450300b0800426905072009000c070824944825804001c01c01c41d503c8406a1a04000f01c3c5 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 132356744 1250 132355494 132355529
    0x309100513060b0303161e230105090601050102070e1008030d0501030b0609010f090c030b0907020a150507021c17160306090b030703060b060c060c040302100201050601090b13 77
    0xa250720501d5401900d0b5a86001c410007041d0a00000711041c41c00302d40300030185c2041d42d039549451141c0020b804d40500d20301d5000c9400080141c612800f03020b854030400281c0000e5520042c0c05c42d0001840c1c043c0e207921290040185980106421060b103509903d9401d681da0382c0041102c004120b075024814920000a00da003900e002a80070a050324801e44441e07140d610381108201200c1420b004220415500c14410030811180b503001103a00f03c032a0401158110de001d0006e90458800c442180160b04401c101004001e6695100c2031401100c3e8410006800d03d078000a42c1c6400f00782540c03200c0480e903442e20b0040c50103123102d40096544ac060b480940d103440e8a060400c19500c0d00941c0c04241424404242007070340c0d006899000742d02900034200d061440c1c85520103030420303082e02500711008201c9011095400d0109511581c20350907010f903540c1c9107105001c00004184101400c41e4500030034041d050f0383c000229011903030030142007070310340e008048c0a0010010311344c000e0000000064a0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 132357994 1250 132356744 132356761
    0x203060d050706090609061805060c070504050408190804030504030201030507050702040507020c040609060317071a0c0903061003020d15061806080d03050c0f070c0902070b0604050121020603091005 87
    0xf41c030145e5885556281d0650703034580040d548801c091f9100456501203c1040c003880c108140a40018102d1004954065648401007011200d080e2400c4c3c9850740006501000c05a1011618850403150300e0007070300c0d51806440c0140180034500000b4101600d82011681140c42081a160341c260010020042e5090200c3c0282d070b915403900c1c8503030040d410300c0c20010302d0007854481d84040b2500050503104200440c0b00c3d001880e484400c0c112240d064611840c907400a0304403209101da1042443d2942c0e0300303a400c01705841c140c002042c001506000240610041e2940b4140d422080e85c4500704062000c02400101c01409464004280c3d040120344c611860840729000310f81125012415203452480480084068400481e61084119410040652107020307020041c11034501448494017840e440d4501c01e404e83c0c0c00a00250399484035502400040c0c5007501c034540c01003d000d1000035a464402100104001810b600a8030907100400020790300c00040c00300700380341c1c244494200501d1400404 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 132359244 1250 132357994 132358007
    0x907030b0f0a0609090e0f070806040b060d0f03050a020f030a09050f060a0801060c060b0301090b0415061401110703020315040b07020f07230907051b0102120402040203060d050706 79
    0x3451032046184442640060070690b074444252a51036803103410050078441c0d40d401600031282c164030944240c0c1d111442c40304003070050300050810070000d009036084c641080d0102513405480c9612070042134500000003490980314150103130745420042c1d2501c4100c40181e042c4024282031403082d00000450f50700039036105100b00b00f0b4841c03c80c3c80030b0302050302e6014811107005404001e00882c3c0c1c0301c001409180d01031418074054a22a0101180c00d43c14000883d01b581c9072904202e944c020803c05000400814643c10401520102410020349180100c0b5070480c0c94008919130510000b000e81011684082c0401009160007030100e034000c136081c48101000c8402102e09441e00e58014021410341c52012840940585040e0001c2640074103116040c1c0d00380500b00d01058a8443c0986c3c090810f4035581c0d003240c801d581a460b5180c07500703550001c1890403442160b1070311603641704020a001c8204501049900140c05a0700142c90303a03107003004250240400200503020f485041400100c1960104 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 132360494 1250 132359244 132359261
    0x70806161b06060f291617040306060e0705070201020703060c03021209060a150e0f070c1a010504110903061807080304120318051809190c14091e06060405090703 71
    0x3070f541540c2801d50740d901140c1d4400800b0001980400202e40b90085182e01d0313491769400781d01d005000740c08619240e00b40762310541c0f0481d18692180404c00c42c1d01c800c002c1c7c00342d002c229828160b1600c2051f50000391502c2c42800001c000598800e84484018400e90503181825103958152a0310700703107001c00d160303034003001c4502c0700000e03040500c00903010310360300840c00c12120010034116060326105503450071024001d040d9410044c4c40c000310004034120542c80b064501941c0c1070340d1125410b100500054480480041580210401c10190aa2000520310394401c64445207081000160303a0380d1410110180c0c4000414800454041000c032030000c1407420052180e2130b56002102d841c2c0700341c0c00418441c410503910000c003226001d01d4030b01965441d0b83c029824810340303548450b41144180c00d0403140c4000da818010f241801c0c012101940c04481c0000301c222400740003403406101a00828107800340c0341190704854004103c050700c519080d00c010703203801000680e05240c0403000800612050703 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 132361744 1250 132360494 132360509
    0xa0303090312050405060a0e0102010213030f0b0702060c090405041707081804050613020c070e010602030408010e010e030901120f050f190c022805160305070806161b06060f 76
    0x7105200e4403a001d64104c03000c0307900181419042641c001010380300680103a40c00c44c1555002c000c40d21940e0140300c211800303035204901c2415400e01d24101080301e120001c0c05542594054420b100303a07001b0203c140c9514200803207000c5003c0c1c0d5030345080d507803000d480c56052206c5100400c600c070070404850007601403030003101c010000314a500f60401041d10000d403000ca42080d00c100d00030030010180d40003880301640b01030071564126078030341c042082c4c08005d90050300145c001240522005100f806a8841c1c2480100203108025411440540b02d202d42046641072112003070051525010940200c0a8a140048100014034040034140c031580b204688501c0c51030b426107034450b00d18903644241e00310300300302ea40284600120b4031005410302107001c82114014030700d08100400200100141044010301c00040c440b51861850102c0c0781003c0e0350001d55040c3c00c034108000d200d000c580000c040840c95858030307c3c1d580c0820f08608a00280028000c0c01450808a01040d091f0b81c6003503580480d50503 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 132362994 1250 132361744 132361763
    0x152a050c0d060c080a1b0e061204030f110102031b03040215040803040302120604032c030a060f0501081f021b010f0b09060301090308010306020c030408100902010f050a020303071202090a03030903 86
    0x1800030381d4040328045a04d0351920f540300007101031500d107c3d84040703210711b2000d0662440d00b00800c004000740c0e40c0459080300007645c014041102079034080d111501c0581d0b040001d41c1181030041001a185031050903550b407540010000070b0666036881c1c2d0f01140c014030742009565554441d294a86c4035441070105030f00400f400310300c12485080004d1400e03c180d13015900c8040da00401c001c00480c018019040030004010146050060382d0203110211000744106000180204100010b000b80c0320142e00184403608481d083c202901c800160b10104c06848010042c1d8500c00f40d0503440a072030810000c1d03450380d0300e0040000f50200305c0341e000d0006504122842040350380e80700c0801d400d84580440c010000341d224401080002c5c9660080c104208030a000e4a007400e4850812901d01900641b80641013604c880d440c50965030041500d4669440d180b91031071520301c4944000e50340740300140c0030a04000300f44035460901d5016a0550701084001000c1419069481c00c00030003116030390005940344404d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 132364244 1250 132362994 132363001
    0x70512160c12051603050607030507020309060f07020a0506030702030f070c270f0209060406050c0a060c120c02010908031302030f0319021006050f0d06020409020301030c152a050c0d060c08 83
    0x1e603c1ca241301183d80c403100400040d17843e40805c0300074000141401d015032009110000f15650b900002d0101c510f06c1d404038580380c00c002d004001c110100765000394000c074810801d11401c0b43c2d020048926400e8000300c0305130b44501a1804d2070b00c1401c00d85c400000b02c0d2083d11011380381810f2508442100c0c4411809100c03195000d44200708922408005580c0f09104000400c60345002e00301034906015901c0c00d1b03c0e55081d0b00d85950341521285410f000000f540c0d2103c1c161000040e204503034402c08244001c00620450b603807801500e21029101c00c0042d1002e000e82411580e0401002444400c0390702aa62035040d110000303503c4150012406016004403c0c04e480004118400ca40c2150fa00402060b40c04040c0418803c4546c45003000b41c4425800700001b00701d18000340000c0d4002c602c100c2d2480555441c21188485950b0600510300070440c0310710310091048503584075012079241c0640e500c4a001104d25005150009400015420004482c40340c0d0a028080c0d2040b1000500b544071511150b4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 132365494 1250 132364244 132364273
    0x20301230102071a07080c010504050d020c030706030209120706031e09080a050304170708040515360909150106020f071e0b0d0903020c06070512160c1205 68
    0x2036a200316005070300c00700c400c011101511015a40d028118400f20f4a00017154945010320f62020787d52200f00da45030420300c004c0010130044041a00305502c06440f40341444800030b81c07142c50511820301059000f14440340c0d079540d4050150020000e01c0204c9001c82da4403000500a0700013152040410004410010042245801034540c000e510140091800c90304400030740e200d8202510540301c081c40000c1003010520071400800700e690065120540b070340d1611042054001103c440707449902c200780310512410240d045059461079214840e100da40c1c4201c01c01ea00c50100c06041182d0005109007800000d900c0850b6030054100c1c189103d07000c6e030b80c0700c1c1c0040e80d0f2400310740f424180580c03090108110940300061240d41c0004101d0b05000c446a503049000384540041c1610403215036255803040425804020580501d0b40a6610b541020741a07103c03191505000e11204e401050002044000c80d8590446180915404440300006075110401c01c00b030221070f40c0d81103800c4e202d0640c9004250 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 132366744 1250 132365494 132365549
    0x904020f0913200f040e0a02040e04050c130b06030612030d090b0f01060905060a080901060e0a0f0b030c01090e1504020f0a020f01090b0105010e03070504110a0801050604080c09041401050406020301 87
    0x14031013002034600707031030507071034407548100144680c668a600f030002203a172400425901d8010f90040b00108201c180b910300700101d040022072411445842d006203000e09413204025a40d0040c07003105c9000c101003101c90401e080d88505009100490300c2c2c02000310410883c480602c0c0150384140010100b40c1e03d802c010b50b5029220301407d0741c000c5003408548411442081010344c40329201d4000301c2c2c010b0b528101d00142820170380f40202450f486200c8605800803611540701e000808034001c04144240c0720001c1e0020a00c0e0081d0341a60301000c0008059007801d004560103d2000340c011982c40300e0791301c1050559001480050b00500075907070070014404050040209030754108ad9641c444d80d10b1f01d0011f40d00b820031003c1c0140c0500801c9400520355071140302c0c1101c0441c003c030100783d070b400081100909120050700468462103090109011314000000c3c480f086020a07607200c03016480d0713401c000d08480460035850707a1640c01c0008000c10000d0903000303541298050340354503280489001691404 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 132367994 1250 132366744 132366757
    0x301020a020a02090a0e010c05070302010c0c030504090e3d020403080904050402012106051809060a021c1e06060e1f0e03011803020c0a0b0904020f091320 68
    0x41e4002c04601001d8500044a1500300c050160001003100741e5080850030740e58000030a8000c10004908a02410703028014000c1008003480d0141030941660360141140c007d6000d800402030f82d4440030603a41c0d0382008100340c1e181d146100c85a40c20f0710340d5120a520040b015100d804881440c102c0c0341c102102e0700031703101500e60049440741041e072808240001801b00401c140d040202c1e03501401c21905001004030300d004a400000b081d014140b40c180305445400030403090308110244100b001c40e8101243c202d411450307503400541e031140e1080b0440d481c00146030704a10524900100c0d0220176036544509010301800a50030700940e6a12101650009030803070380c00e5004a0304852172146600c1c03c2c6111a42c58242d800c1c4039900040c510003003402c440e1402c103508c0e81c0b4900f02c9000070500d03404200a1b449000b0403240054560309200c03044900b400381c10720b100d00035030300408c035507015000103816141d803400c01410800c062a00e400304140a045041041049001760300300c66460b030600703003048484 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 132369244 1250 132367994 132367997
    0x8031b03011202010e06071e02030f1504060509070b04060206010801060f080a030f0207120807110d020109031209120515100b04050f0604090929070e09040f06060b070309050301020a 80
    0x410300142e001920a4190348448503801300c2c04010203030008448074212000c403954250300c1401510b227841071610f8030603244905016540a402404064004140703890350265012602040d540c0787c60060600e881c1503a08007801c0c00b031000c10041400c0740c0c001400341c100c1d0b0107840244070540d52007502c07040c002c190340103c0400360004c04085011900641f441703130300d0302120300c1103441580ea2080380740115104410100d5a1810000383d0f0710a00181200f02600da42c0100c07000c1c61041c90581c00039080e20200c0c40003c0082c038800c00107428190045100000070003900709004040b480c83c1c80c02c0e5403100740070b00d020301d50380051801180164040c030351103401b6502006111440c0c0360820702081008a2140320fa190300c4070081202245070b07140c600501800d14807609180070a00f803540b00310b1080004440c03420b1103202c202002c01c040660300840b400941c42c2d0984a548854a40d8100400c64090100001d02218200040040c581c213001004105642c069907070030303101030303150700c101802d0b032040e040703081b0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 132370494 1250 132369244 132369269
    0x1407060e0d08071d0103150902040b0702040b0406060813031b11030123011e260d0e030c0103020d0b1f020d0203120a0c020f010603050102040303030509030a0909180f08031b0301 78
    0xc0550007130b40099458501f1041d0307034842d2030b5101a000141c0e0b00070340041d8128a8003040241c11030a003401072002c0b403003003150207020b51801c1c5200281007950080076400354214004a0f4004e050080c800c2c4c59940004800c2040c55442790b0030f0100d900141d440c6220301035071070710b441d080c0002c52070b401000c10b800d42601c40010a03482e050300d441b98510241034007601165002030004030440900301011014080141c00014400c0750668103090000d0072581c0e02c14410194050441540c0104400782030380402d00740180c8851000800d0ba004003410500140c006441100901c4070705044d5520b01d0400241d60f086aa1003415400126100d019810326100a001d001000c990904000e4011080d0a4003d00c103d410103080311030303020b0a6840740d60082da181d03507002900744141a4580940c56214040c10011850300d1071030200201040d80034440c1c4000a82d455000c112000d018078017070107485802c0100410354101c28101203085c1c2e48166182580c81c40c0030301c12130841d40188800d9174101e92460b880807 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 132371744 1250 132370494 132370547
    0xa050316030c02151f0e0a060602070807030206130b0c010615020d230f040e01060306050f060d110c1b09130b0c090a0906090f0606030b03030405011407060e0d0807 72
    0x1355110030001d0101c100815800e2004a1244620740b948001402c028003401400e00b0040d6440f0b0803a01d460b0012000c41d0001d4509000050340016000e0890b541940c3c00c2d44da42c000140500700d0a01d43e42c0240501c1c0c10001134200300690f05401050958041e01c140f081c1451035814166501c981c410881c1000c194103401181641c0c55054942c0fa0440083c100c1628000f904100002e256020360450901c0c5014680140107003507051080303030013a04081e12250f40c44421f92001071014025042c81b0b0b110603464440000350f00582c482135500000740c02007119045000d0304c034100461500d0649180c06506900300080100c17541c0444003100329040010309819840c1d507840000d070b42c2e0000c000310341c009a580d8000110b0907890f2144400410b000a000141b20890100b03480554075603030700090406062468160080d5400b200b203030100d88007400c104a80c10030008a00b80a40180315016000074541003100e424208080342d07660241e800d542c1c48501700e540c0c010f0255040c8109660700341c000108095070 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 132372994 1250 132371744 132371773
    0x516030608240a0b220b01080f0f130c060905030c0a15080c0f0a17070c05060c09031e151003030801030206160b1009060b040e0a0c140a050316030c02 66
    0x1141e4000d4070000c00403850303413600c1d808503101a03503410440e202e003400c024003050b000f4014401c8030940072003403812446600703096000d4040301001914403000a450721002c50109030340c100d600c0d1032079944506800d51065039903101030044400307881220b00034051448983e81302d181c900904426581001244000c90845800894034814004d00900d43d05000304106548408060064004201d0a58600809071785804241d103030940080d00007002d11021590110003d807011a42c03a900507003006209031117801404c000b03413802c0000d00c140030300d4000e190400a4040e4020031304a80c00b112104a07070381c6945821090000388003ca2002a0008802c0c50041c401407402d40000c043c0715010401b0000180c2ca41c0d00c5010140d0320580705004001401c103000c01c480341003409110002c0a1081000d0b040c1460000e0841c1c0401d0001d0120303681e20360b5504804181800380c10b5412640040d021225191000c0c070401038a0380d030040e0b92000d03400064130144942c140c840e004190544100d94090720304e18260303401 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 132374100 1106 132372994 132373063
    0x20a0803032401020307060203041119061202130e1006020c06070c0e1e070c02130b0d150209030a03080a180c0b0a0e040516030608 58
    0x20040007598520040034101c0301c0030030030b6000d800da40d40100e00710f00c035140000740928404010702043c00070409000f0000c0d041075542c0c1603034107804418000d6800c824811880000d5150078280035280c4260090803242741c201c800041d02c552151100030400b1411642d9048141c1d0000301000317040d504000c294110141a9051781ca0b120850311280030303601050080008501c00100030400c01c0b00444206908040e20b41002c0d003d44c10601002004a0754105060b0310442402103401e09801b0b5501c50038200c0c1c840105802c242c14415500c10715100313844010340d120305509110030b030b4054130140541d50410b44241d13551030552402042c904200c4845028014085a5000c10303240000d49012090003035518141120303455000820080710006500181d098005041c00c003848031007040c5d1a91646050700b0b42d00c0c10302c012500d52850581e0391111104041031003e85001c00c9561002400 = true := by decide +kernel

theorem cover : BRFrame.Cov 132194244 132374100 := by
  have h0 := BRFrame.cov_init 132194244
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132194244 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 132194244 ≤ n) (h2 : n < 132374100) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
