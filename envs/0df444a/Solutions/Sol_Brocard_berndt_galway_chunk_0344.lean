-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0344
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:19:45.82118+00:00
-- url     : https://prove2.me/submissions/1b6068df-7af9-4232-a897-f0bee8175099

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 61690650 ≤ n < 61870506 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 61691900 1250 61690650 61690661
    0x15040c0e04030c0605070c0204090b04030828050c04030611120106020102120c0a0c2001020f0604020a1e030803070f1d010504052418030613020f12010e01150603 71
    0x103600c00039003540e140c9500d000c0c10b5110241005042c080d1a03000183d01c0511440a10225690042c410403000c0c1c03660503e002140000c8600310040b8041001103240c010700d25070b03c0040381c01120b44e41412154070302c1e0f080340942009880e00d134151006200c08800640c840c0515036000706c4450000380c4074800e03010b00000300c00040e8041025644104014800040600c6103207500001c4c003803d20356070f06641e00c4202e0b5405480d4030f0241c00254810785e02d2900c0720790150b0100310070001341c1c00c07140802840c40501d6121401a1402940140c4a2600700010746104044442c1c4640340c0c4500d83c0c6aa0384c940726203c090384110784d001d001600301440342e88055040004900d41d5042c02c03849182d8018040c4c006400c034816070107018400c14950411000000c06d42c0c1550728140c000c040c48646802c1ca801070400c1e500100410180310b402030000084186034202c4141118940060a24210f21f112030103000150a4040000140b5501d40f038030401c01e19024060000302804103a0030303298562600f00300404644 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 61693150 1250 61691900 61691909
    0xe070f0501050f160515010f0906080a0b07020a080703020610060201050f0c030a0204090f0605040e0a0308010501050307091203080105030d0203040605250b010f0e0f09031b070815040c 81
    0x9001000902240e40d00100341d030795040501c1050799440049a203c10072034200030600074010703c202903075910480d040b03c40980c121191444d00e00d4080b5181c80c0c000b01520b40303600a4000951108040801149034640110340101490041d00c4000c9110349411046500c000400c0d00903a00c8007080c01003070000c1440d5500145030b684003c020074103240c042140c1c4030a018100000c01c040200c0412034682055048400030544107a0400c17000c001d41c44008094500c0384286445189032805040c800180460803558540c2e0580c0c40c9041c1c0c2e800c22006496076000070344000c04010350b1040c0420403080c00b0500c01d811501070f80700c64025624000c201450402c40742548000c40d0024001080000d070000280d03203104540d02089200702c810554401c400d2092841c000e0b0102080c200002a14403e07000a201a01c81044035810b803071361050444140402c0649035107810740c0c000c0000a00e0040c0210764501c0c658070800a440000340c1d280d5081d440c00041c1062106851b801905000c20040b0f2124020000c2 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 61694400 1250 61693150 61693169
    0x3031506030910050603031902011e060e04030302030a090204110306040e1908090d06050709090e0d050711031c0f081303020703031116062c15070201020703050a03030e07 75
    0x42c5003441d405078035003001100392040e1580b41c2c0c0218540c0c1d6018019100c946440c1c402c50b01441e0003620000707001c1c009041980100c1c8114410784100d045660258206446000380031884985565500310001d602c01000300c032010380d58402e12001681d0f21f00503050074840c1c0059a075181e0405404100859101d551844400c0e4424550391843d8204c01041e400e40a420005a075200d01c241c0c03010411240d489080108058984130400250319080345902050310358100d810000c00c0f11518400790349158281e02903010400034040c14001941744a00a005044083c0c00e49604c0c0c07800c05151983c0c48841e21086001c1551050141880d682c88005190b00461a5000c0c02c0c10780600d0b20b0194890030a4040942002607017400a10101004c0280d02c0d42881a520200310403507803058020b00c1080301080308004000000414000000e0540d410b40c1c22900041012103468050021000780341c1c4203c1040f415800350340c0c00000410414030a03025294065180170400c204503960746402e00f1215088100c08 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 61695650 1250 61694400 61694407
    0x2d1a040201080a06140d03030905060907030506070212190c0b09031803061b0a110f030a091502070612060308030123030607050d0b120a12110304080309040f06120503031506 76
    0xe45c080d2069486029045c0d4403101020307072508003140548400107028000d80300f000240250443c00160880489010f90261a1180c6038030f036040782c4442d400600c40c442d001c4180580c0003440144080e5509159090804610200240e42c030b03001c181c003044a41900c5031300003144a1030089130303260910001031000c8020301034515024249039007210b21303407064034540d07080803405401160180c01006482d101d504100e8a2991891110541e20340c0480000800500e140e000044d04070080c1410042d000070300d4001d041d80078180b07501194003070f400f50901c5915076200c0d00c001000c6080b107801140608951405024042c40720000286c0c04109401a02c1c020741c4050304000c4000d51017000d0720000028490041003c001040c001505503440403a0031115010f002544c1c0108400044844040011500c3c0d20700b0030b090300d41c0001e0f1280114401c0c21090742040103c1000e610b029070000d14041d008000003e02603803100e0105509000c4008203c8a990002040c4a0241b21900040801600840f00caa14 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 61696900 1250 61695650 61695659
    0xa11030d030605240f07050a060b040504030215040602040f060816090807060e04060306020a03050402040605040c09120c080d050a270b0d0f050c07060501122d1a040201080a06 77
    0x303054034039039840941250944d05240745030005504071200142d05800d807580b100d01d81d08295880d04500401100c81901d0032001e0407190929003d40e0b4130507a050780190050880104c0b8400e2820300052048071400e034204404540407450608003006031180b03503140c0d6150311780030031503600740350300101c03200103000d0848410000c400e0300203031001c1652400c0c0b0f03002c000095410042006000b0ce504014800e5001191103140d051b450b6002601c0341b4001c82d0280a083d03911400e020484030300c011010002201c480c01440148445030540401510625000c100308ea599840c6070b0412910905040002e1000034402c40d403030b44d222010001e450401d40c0d01d148600c1017024500811070107403080c076040e004d011402c1d00c840b40c2503a10038805c89107040340510035460326412030000c5522030741084465624100c0003084201c1c02d8051080c035607a1006a90b200c0482901d110300c0e0340110250f03040750940c41c0c62150070004070b819020122102d5024005001424a4800502100e200074491245c02d841d00e5010803 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 61698150 1250 61696900 61696909
    0x908010615050a0215040602031f0303020c0d0f020405180f03090109061b0516080f070b0315120a0605070806012606060f03040c0501020d0212030a050709080a11030d030605 76
    0x2122001c1c0e030400303e6a030992941c050341014180102c65003002c55090400040c810b0540040d2701c42c02d48001c40e00303054074400100034010455400058016071000700c4400d0300d410000c6e03038941958012b400030031080c1825400102600c81c12101100c00e07400780400c500302c1c3c02042000c0800300345d420001d9401c1c414650002041e04125128600c02c2007400500c03411804620300c01b1100154204064446034040c0711091003040c1618030580d42d8a20800342e400296200c00308180d8192800e0f00d01881c599203e540384182c09215442031a648840c801c3d0800040c20303010000714148520580c0b000c10340f40b8210744060821100104690306011101c5020120240c86a40d080450072001c1742d20110307920350a010940600488020f4803950b0400000d000038415504190001c50b00241e085420030200b401013244c82d0803e000742c1404460f414008100e41040366001564003c0072454125005a07035682014034182c2138150035500911030800310341c582d007400e0110801c0c042c4c85040c280241440c14000c00c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 61699400 1250 61698150 61698179
    0x10509030d05100305060615040305060f060a0f030f1104060b0307020d0806040b03030a0c060b03010e010b0f03011422020907030207060606020705130e12040315060608060f0d020d06061509080106 86
    0x80e100ea0b04000021030156022300a0714080e503003110440c0d01d98a0500d007500754110080c0da40c03e1003a10044400910070703450710621400d60790300524080007801c15a550540810001494a40c0281c40f041c002c1036424102c4051407003501141c5c020b0a03400320303070300c4060401d01000c2d140e140164104007003060651070020880340710380000d1401030b00f031502c907041081c010302c100c10500e0750550030440c02500001d41500502d000b5441101c182c60700208003001c1508803001c3d01144010803240400240003d403500b45c426070b40040c00d09001e0341c4040554000f400c6030741c040343c4c94801700c1c3c0e022a800c01403104038403c02d4098901c50008154560401c0b0000d00c00c04101140101c1e500d071584030f040c0d80c41205010700c85102c4900001a81ca6588034a00f200343e500d08502c0074002a031a24000003006445100f10174041c14020304003031115035108051002d10302c1804810380c0c01050110201d400a0f5a510607007005000380c03a0b051030f80d10704001c0014400340e0315502c0200c690381414018086896181c184 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 61700650 1250 61699400 61699411
    0x2010507080901030615050909090d02060c0c010905010c051801080402010206150d020306040b0106080f2502160b09030d051315090803030106030f0c030c020601060f050c010509030d0510030506 85
    0x607140c4034820300004902404c519046a4140d0b00c000318103010040c4c000011340803006040700e80c050143c0d12040b003282d44043c071120000050f8401c0d40441c401c884d0820062a00c0a140000400d80040d9602e406003914108943c6400051001a8460101c2500450307154664800d20b045641820b040d00001e50300d602c003901101600741201002e1845540e4049a81201d41d400fa040c0d401520b05070900038110070b024030414000c5a590030002e8215048050642d02c81d020541d440c500340681c040203640d054200c406c500c000e511509200a61404c00c89201c40b00030111928642c4d5164822424035040440c81040300051202c144021041d6881034152081600c00e00d03103c81000801200040341c124209034800503942c000040041986545a0800c0034040d0350502d0501100c10050021403c031140b0b824001c005030803e200600070749100c3c250342680000c2c180b8100d400d00c1e08d49480320f07007100d40175656000103900001301070030348182d2806440e60064200103a461603625540b00c00b80c441c1c03030003000c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 61701900 1250 61700650 61700663
    0x70b060909010605030a080702030d0c05030409020a090e090714060414090a021902010207050105100b07060c03060f0e10051807111e011e0507050d0209030a0f0506010612060302010507 81
    0x70000c02095102c000100002000c49038400c017107003401d610690001d907041c2d010380502c8044541d068080c0000041c0c0c2c070380c40b000844c078040c5084080c7d4001d401c1000c00604100d60b400b4000b035072380c00b410b0000d0300642c6400040e0010900d458a550400307c840504180034440900c02008103881c4421301035a054000e4414850b5a580c140a020003441004088600b009005517000201c990540c040c0850301d03c100002c20082d2180d00946810a4030b40c07082c03403141d08040004d0000904d540d040b000c081c030300c1800d002c03807600c2e10f5070b0030302c440744046402c20030002c0001d400300301e0590b1081c1c02c810b00800342556912144000304030008440d0400900e00001d00c0054854a20003e0081209500040b0450810452030a1940000303010301041244a81d150b80b520085a072072082030720130700d40500c0c0c0035120240b070031302e140e144580a50401110343d681030007112040c030081440c080c02100e10501c0b41018000541c144203020744150181c5d540320742401d19000c070600050341c014048509071a080314 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 61703150 1250 61701900 61701919
    0x2010e010506151806120405150408070206130b030112060f050919052b030c0201050f01090911060d0b0108011205070506030c1e09010e0f0d0314040b0a080a0b06070b06 74
    0x10141303140c00d4880000c203070b001400028411440129070340f44500032485038040d204240600166074041d16025100030b411244100103420040c5030101c02403082d100d07444120100990745035210103440c2c10076401000d0503048810038201704840352141544907a0f00c00300c1040700782404040b0580d82d02a10380d8102440c2c0c500310380501408410480c0c1441380340310341801d400c41c0b4400603000a10004070125a000b01703041046e9910450300600500d8401c1c0510500e80f5440da1a00248101034410160256098503542c5041d95964844400400781005803034008100d1001071000140180b405038040301074141c024806100244001c15288121002140c00c00e0f12602d82c03080e080c00c0707031140f110728404030200440d404041c007203100d002d4601130400341c0742e404075104204180984002c0c80340616501001078203008002900030552040c94200c0c01c134503a8206078850a0240d4583e1280303482c0c001040f954020840105514003c201610798250b40841c01d10659648080300e540001d026140302e0700d04d07a07 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 61704400 1250 61703150 61703167
    0x303050f0d0f0c0905010c02091f09020c01020c0705031912090909051c11100f021c24030816050c03070b03100b090102100b01230a02010e01050615 65
    0x501680e40145015004204482c038050b403020083c40c500e8a10b1021500940c400603296000f40301c0f1107a0035401629481c46692000719041200c0b03610054400c0c05800c2440c00301e43e0035441d102030042081031100059072044020318031850b20000d60302903886523100c03912500506401183d010300b8627600c000c1d2450040c14810041d644000070350400d030340441c5042010002e00000150f00d03541d801c002c6840f2007292051000490354010980501101d680c48550142c541500aa0080005034001c07440107081ca040c008441002140c0d241605065549800407041d184460218800303070708d04044c80445c101c6182d070b500c028403409201000502d82c00103074651002d03c03909001d40354814400030144c811030385e21188040e0300c03900300b41c0c1e00d2100500e0315140410001c4020084640c0500d058006143c203a60004c4003401030000101c425041119004810800000002c049038841540c0e8914a899020a0b54020308407020a0304115150381070405000c0643c444014004196407031120481e41e6281d030 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 61705650 1250 61704400 61704427
    0x712060209010e0d0f0312021303020603040804030b040c03060e0c1e01090b030709094a0604060203090115050114070201020106081207020a080a0b01051c020a0303081501090f030305 80
    0xf02c40d050354128000d469114208810070340302e400d039a8402c2d00e400e09400741140c5158228040e207844001a2150b00c4024000761030034070041e5610520660181d03152540301d42c0c3d6041c081c0c005445c01c40d030f50481024103000b0082c1d14098a400c0700030002c010f000c044009800035001424044071070103901900314000e0300503442022514042c007000c2e4902a641c0c100441c2c020030070380300c40c0308204400d494400e5200c2183c40c1e00c1403580040c038902840300e04000820060796850407a041a40484c041c801c040d039020402e05010380781c4142c0c040c000058403890000b02c2182965030342d6003810410a0312040a100d281c2c0c020042e2100402c20a50081d210045440181d0040c1499001494944611100340c0046d000800c01014510700c00da500d080c0d15903959800303031707500c5051081c028664802c0c58010300c513900300340d0790f04141c0d00c1040100003c48a060707000300e0951070654200b940022091030400103800140302c1d907046540400e00c0c0c00402185080307250107400060b40401020000009044480c50b000c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 61706900 1250 61705650 61705667
    0x20402030a020d110a03060e010b030a050c0c07081005010b070b070503090102090628020304150309020103090b0708070305090c06071403070b0c040305010c17070c02150409020702040509071206020901 88
    0x2903803000304101c0301c2040c21361301d031500040349000000f400e03c0c10101d105041440d038030b0b040f44e140c00d2000c0e080d074034ad0440880203494020314800d900c2c0428082008411010002903006050010280c42180b1003400c1540130f40304141c014580c603440070048500025558250b00e68888450b1916548070744039a0100c50192180c040031720350004002c105403101c04124031280c20000e407484490550022440800d9031280a14840c031101c0c09292003a48900b0f40c0030360040d466552051400042c02c4105581e95208030704160741010000d000c8400b040a031581621449801c0342c1003000800d041c642e1880000c20728403039800004d090340b104440c030710070040c010421303260102da100b000601203180010325a0090b8100f44003e440c00c0d801d0250008081c0e0141e84105034260404a0400113642c1d4100f00741c454104842c0700b2600401103202c1505100f0304600a440500030a9002581e244560300400c002d0b81c2c0043c00c200100e0b00030b043d0400c2a46000600300300750aa0000000d41c881c0f03002801a200b0381c8 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 61708150 1250 61706900 61706917
    0x507270e071703030a0b1002070611070905071d011b031b0b01030b040516050a03020f030a050303090f010b04110a12090c030b060108100308040501200d0e010801060e060403020402030a02 82
    0x900300802c00103100100265100e49642203041110348100340c2084240320035407602e9805600201e90900ca0300d1710a109004d5481785c105c00706c800c00c2c0e56911141044580469481c5e00040d0420032001104560740c00200490009103002400560040c10072001016910f80c000c05101841c00e084058412400016003241e0b0041046e0b049580d407810505a102c104039421550360080c26944400214800c440c1c4c41900e50240080d8075450a40e828003001c0c0028085440c0c0c1031251650200001e2820001103115420f540d000d00400701c141d035181800c2d60031080702988190309001000b1010010305095940781041d0f807401d400c0000b1050401c0006005c680400b078030a0810000100034410514207280c060303071081e600c0b04925690440001b4a102c0c0c0d03404001c01c00d21013040100320700e44c0304510113000300d1010f142038000c54443c614814a408a141038100119408142f241c2d61703513030440602d40c0101614105814a44e040c840003441c50700c29404020f00c19680440810344a0307940754181c640c81c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 61709400 1250 61708150 61708169
    0xc020a060608010c080f160c020f030a03111002190f09080303040809130516050904021605071e06020a230a030801051c02010815040e03040b070507270e07 68
    0x1c0d40c56050060281902c4034048000c90f003400041b40b02c014518441a00c5551841102040c51074004401c40e0114021002640e01c001d600416017915070b4103100040c4158440d441340d4044400101e062400d2112480d50f0580d002d1040c0a44510082884401ea90606051030440311555481d503094800540c1900848101c0c8804410401044240c2004151001e400c031100c0303a08900c0c5070304a10540d0f030708071303442d045108084113102100c0e8040c20103040070060080c80581000c11503010309580d074403a19002da030140d000e240100700440f000612441c4112103010421121070800b80081d554440f00c040051400050000740c20480f00c10038503c1c4d032400300b881d0968a1444440c20014440002070207414841c000020f072182c03407071129030a40030703099906031a21000e030364a00380d400e80c800342900310040d00603840f0100c1940204081c001000a8800781030900e44564050a11a10b40303c030030340103080512500c02c407610900071090159080d0511900c4041110800e420460781403640c1d0343c0c0500f0a2 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 61710650 1250 61709400 61709411
    0xf170304050c0a0f060c0b100b0c0c1806150f042318071b08041d0708100f030f17040602100506030106050105091002030909040605061002070305030d0c020a06 70
    0x1c00101140202941c08216141408541c540304d0099440c21131307106200106005d55211400a25140025a84807446400140e410380d0707100918015a4080c8886290340d412000e110750040c034061512051070503200100c05034926000c80410080305c000000c4103113420010905855a2111038102c501800c504005002c40c42d084103a01d0744d41e0003482d100548180c04070720041d156280f400c816035102c3d0b0160342e42c01d00c03070407450021401ca80300032013010340b01914100b001107940c3c0c0366841c011100c401801c402c00c40a1404c0305009260407809030040007071801d8a102004441680021032040e40d4100c0103403449940c282c070700344850031001c401807040500f0200d400104140c0104802c021541111010f10039030b0350703402c101822580e0f58043d45020641c1408500843c4c10a9202e048110196004817032815845800107413901c042240c0886140781c0310000c000d414144590b2560740f41407a40001e0100e14110faa50320f4503400f82c030a19000003540c812080104e0380c03081201c410020b07080b2004000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 61711900 1250 61710650 61710653
    0x20903100902120622020d0f050d1101020405030604060f020d140106020d09180b0105040e0a02090f030105060d060e01200c1e0c040207020f040e010605030120070f170304 75
    0x34000c144070907803154a03901c0c0c0f08920200302040f21882010080768000694036014002d806011340003000b41d80040407410081c0000e049a8400c2c4800b501030002021603102da203a004101181e15668411a64010300c030810060700d0000722580c009078084400304107003141e040701034020700610200100701c81c14104481020f1149402040c141c0d41154240d9001500f046801c0d194030300c5d03d20412403500051080441c41d0b203880d42c0b02010f0079605140c5146020b13640d411100c0a00c4054880750041035001500c5c00191800915100350600c003900240080d1038101f00095541074154005030540d612040e07203501c400740a42c8001ca0070805030030040ca020700880108005500491088005c500c6411442000d1950690341c00c404204101c0091440b8070700501444007a40000300103d0700035040d2012541d10340d440340030340c1040402d40f40002400502e003404050039030301d080e012417045070540c514404021080408a4130440d411400e000100c04c000e192160b03105650281804801501005000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 61713150 1250 61711900 61711933
    0xa0509011b020301410103080304030309080c0132041b12050c040509010e1903020102040513020d0506040b0d0f020307051008010e1005010f0e010212040602150c0f1606020903 77
    0x9492041d07445c19000d584516062241484110030354807005203102d1401080054401402103074030900c05e04c0e000c219181280e80751a03e603000000400021b9450f41540200d8500c0700e84100341c0c900e800c002c0000300e842e5541a54200201c0a0070241c8400110f01c03004001d4640c0d0f0b103800005210480c00c0d0044c2e000d05090407034440324201c500b240324a0400c0081164040140a000e01510201025003050a02c1c0d00c1d002d0716a1051110031000d5540a220000302a60341801d4a922452802c00150707842d0120811042241c000409442c032540c9801319825540e219003600b5240d00364440307030304008100c0c10b00000f880c0c12005c1c0d016962002c62600b00540d895805500c0c68101c50240010020315110360340808103600c403d0052900181400c18241171040c131402d01d00c2c580c2d003010b0040e14a10f0300b103000658020f600030740013480581e000380c0518000045290001d5480b8040d1110541814041280c030b40303840c4a0750071406401c1950000074001c0c050507504485152100804844110480c4c82854 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 61714400 1250 61713150 61713191
    0x160807051207030e0303071701080102070803011503150611060703050f06100903080f070c12031e0e1203030108100504150b0a090f09021c030c06150509010902030a060503030a0509011b020301 84
    0x8d1840008036000080d09030b414000e5070f111aa10180f41c070305503820012136411800b2040d41150405464545c0740c201440303091984000740c481c5985000c0c0381ca0700784814625200c406000d6400f00340c0340000b08220076980d8003500360031000894485210461082042742c401055401c094011480068002d071301030700c840010181c80d4860700302c03401e0351a030320280203241c3c5483d050080c0100c0e000360400d0010a160003d07814001c8038500344420503803000404210403007000c82a00403d54000001031201c01010070882c10703122a0341405204034a001d0b95a0401c80303542840c0090601c0d00c2e40c001400356030313940c2c0c07010002e002d4021080040480c3e1880d40c0f00513159252040c1d006640c44a44801ca0307609100e07503221a075400d0b1711910040105030796644000e220140c842d1000741c00b10703800421699103024100b4000c0c1506900541c4030304003102948211805607111601c01c0c0d008000380c5000c5070b000301c2640d4200000b42002d480310008040118540c0000110013540b40d480c04400001d051551001c4c0b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 61715650 1250 61714400 61714427
    0xa03231c02130b03040b0408030604020c0a1406010801151e051302070b07030c0c1103010609020c01090c060f081503073b0907050d02030a0203030c06160807051207030e030307 77
    0xb050345403507881045101500c02170f81c01810103010300b4000340100380120003c42d00403202810051600481e030303034030707034100f01014004940001c0701d041c0a81a4a600304000ca0240c200c50000700b0030b0301d0441c2c400b844118528441c0c402c821031815189001424106002c50041001801c4e003013003820308005e410000d602c80e44044803220a00008290b01e80d119124034040308955031100c01110b44d054881070b024100c2034540320790541d02c4480204084910780080e2038420f68040000c10040c2407444c0c1560302c0d1649410407010040317255103040c8220b0b4801381d455000780151451032002039000b40840e00b8566150441300030f10800300680306001060719020360a1440034640c0070070201c0e00ca8819044958152402401a030280e081030003185814030502d42651320081c1250030405042e80800e045401c80e0f4401e54940d041102000306000e0b0341a560008064185042c04003442d040b42d02504500034284c0910201c5070700400200d0782c1d4003035444096044549000c494581c58040310050170404440c00 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 61716900 1250 61715650 61715677
    0x20706030605060702010e130c0c060f02030603120a1413090b04050124020106050a0f0303081e040303050402012d0207090e0c061c020f070201080601020a03231c02 72
    0x10480d100c0e11a8006481c0010890313442c119007a001143c0301071808030305541c800e56064000b5058445031044108690560302c0312000411681401e004543d04208403081d140d00410400c04a0b07039010030714000240143c042c05440302c0c0c220b0310807205001c104098140b0590001103d281e4800d40303800100844030b01d1401440502c1c504020b0200f940c1d003e1043d940101c190603d01c0041d441041280400410f483c0b000259140c3c1e9000024403000c22507200e2140005d0010003442030503481501c039940803c90080c11001381c9205802c054103040b00501c0902010f0303860010030110380c4961340900c0c03002000c2c03403094550500041e185000850080c044005031048490015400c0842d018803042502d101024000d40322005041c44895482040e410048080c503101c0f4030502c00451000d403007020003c2c0c0303060380c580304148000341080c41c003e0109810b550248c0743e46d500007580a07900816405035041512814100c2820529250040c0ca00000c041101040c2c0c101e04440b1507230140085d88241c04 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 61718150 1250 61716900 61716913
    0x5070825060c0b0703020a03150902040f06050403080301030f020409020d050c030c0109062a020d06090317010806060103091104180506161409030c040905010b150a0c0201032a020d02 80
    0x150b8165003490801000120f07a50001005070b03010b40c0c003800300d01605e07007004110703050113010800c0c2c10348454002d004a0741c0d0100d018010303044100704082c09411113040035480e00b030031912022802e0005201c002c0c80608a01141021512141c01980040d075010b4201c4046e8003051038080c1c0c43c0d1280480ea640070b4891078100a03019071095105204581c01912525089100300030000c0f19504142c00e8084da02d08840d14881c0142c40d6a44041c1050b8040c680004400e41e161800a1142c0301d0460420b61501c40500140801c02c0c010079220340010090a00042906682c50030503417001c0d00c8e00540f64001d1411501690042c9604542c411452140c0b00340d0b00d05941d0f2030b024200703504101850700d0015100c07144240b59200c0d550f0081220b010700404540c020f040c0388000501f5904001d10842e0390b6511034821444a040c1080351007040c40380c400c2050700300002051b004000b00700c484030203810180c81c0c0f03051041503072007a120b2000031003a000b0b820020003142c8201a6949940080c00c40041c8a100d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 61719400 1250 61718150 61718159
    0x1e070b07091503050405010e0a0b0f060d0804150201060b1305010813050a03110f1f150509060f210606011206050102120d1b03050601090f14010c05070825 68
    0x181c80780d1094552141064140c2031182d003084008140051089130a50360310001001c0ea00000c03c4800e400c40d100703040722219031500c0d10400c1100b4070080c0c5424044e903217842c0c810001601c604284d500b0703a140046005804014014100e014090560088900f0350001541891241101d00c0040548001380c0307907403505884045911480074013000c80580603800c80c01d40310002921500441e0784856030704003100c0d4140d151416850612826004d5541d02c0300d4400d060020100950255100c42c00300b92a20500316071802d00420b030075030b02c01008032f8481c4210f0841300303032150f507001805030b08140e109070500a405100c5040913551a03003a01c4281c0031401c034403403d0407520081d01a000680b070781079000c5d146602c3d00c0c9054428680090039642e01d01500c0c2c414040c0c01c8000d1001d05043c080c0117547c0407400b42402400034204841170b400c21403102c001c000b01408039095945154a03c510203181128000c2c1c4541003490402110741c103e151540940061840c0301014840c1061044480070f494130580d40e070310b = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 61720650 1250 61719400 61719407
    0x51605030303041e02031c0503150d03020d0e0324010602011103090d0503060d0b101e0e1303020106050904031d0f030a02040f020903010c09081018060c02031e070b07 73
    0x211401804901c41c544ca6007a90045000e5612001d4030140840b500004c540d000207030030740c1c0b072a541e44c40003a00c003008201d030012540b2480000c40c03d080d124141980c1d0591002901d50400410120a2028480a0000c10b440400031400303640d0000303071420000910030343c4c4500400800c0c0f01d04001903081081014002c5105401c0b28042c0e02c1020017030a01d0035a400742900e1540005202a07400095104044041940c084501d0710807507070b101d000716805080200c0300c88004c4900d003900c9503101105000713108802c07642c50002c3d005880078600078041d501c6440c0407405090035402c840d0700100c2c410280300030107410040303d5620b07402030a0512003001c0705d901445065464100681e0703050748028000e8004d03041c20b070b001e034482c18860003002d490718510902203400e481d02025098005500300008103d01c0c1001d0201c446000e20b01401406207480c035200030310300c10b209c0c500090002a568118115018020022a1040c074240e440008681c00c81160304002604002001e8441c9218080090340c071522 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 61721900 1250 61720650 61720657
    0x7080d020105070f14040f030b0613020f09120a140708100216020603040f02040e0a05011802010215100306060609031a060102030a050c0703080c0a0c09050105181906030516050303 79
    0x4a6940700c0090340f007035610443d82c5026040d061004d01804000104010f68100c44160207980a60310381ea040f4100312b000d0103880110b8000b01c0c5c0c8032a1040c40004e011451803001c4800c104421598201046030242806003402c41c2180300500300614410304000012010039079900310384920064400c0c21000c0981c0d81700740c3c8a1060105aa00e0705031403158014039000b009182c00c280188411204030708682c0c0428101c0340c52950201d1140d0002c0c50038030800074240101c030403034245040c90008009655001070341e04c00040440d844c04100d250009881050003101c0d80d0015500081c0034010640d45081c007905119044c08141e42144070f249e00d00703e4251144c44158001d07941a030040d0b180071400c44084505400c01c005001d40c5003c0c00e88000080f0b19068080e0641303580d0000600380680d01d6241510000400394032080081e030030040100404d642cdd89a90300382c9a0860303480c040740c9aa56140d0ba56100642d010f566140034a40b88000c8184440003503808094a042c10002e6001c40d12502015901e00 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 61723150 1250 61721900 61721911
    0xc100e120d0f050a030f09030e0f060918040f0f030306140301090c0509060112020f180a08030901030216020315060102010f0213030602090420070204051501020c090714040807080d020105 82
    0x4060304070712982148140010080703450b8170f20340040c0d40780e030842182050b50700c8000254001203080441c0760940c0303405104070410240440d0280c1c0790404260204581018510b020708000804200050034000c03070108211400d0b80c08540005c0e0050701d440d0240040080b4000e2002090142240000a003030501c606060260000f09100504d8541801c0080880c030081c0007604002e407480c0304003001001780c00540101152080315a45491100b00c80e905100380c1032614602c154600d00c420805007030f0100071145495002e00e400b682d070724068007080000c01045c1e200250580300d907020b00e05030307080a42c01e11070003032800b40d00a0180764150354401c001c1c2d00034030a0b11403035400c48040401c0000c020703030b000304140702007e40b0200b105542000013100c4000d0362099041c420800141344402c61030300b071188550042000160951910603400005d54480c0c0b103500c014010064240131548050141700c843c500c064111404582d1140c8900050780c50f40300500c207040451007a0341c04020040e006009041c0b059 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 61724400 1250 61723150 61723157
    0x12030806041509060906140303070b01030807020d12020d02011a0109050112141f0e0408030114040603050105010b09120c01050f0f0c0313291603020c100e120d 70
    0x25124002000010840b90101140c0e50129510024814049004842c010507101c02d00061461918820071210420300301100d110760010410712001950a00445065070340007045c00382c030380e541440452860400c5c3c0c80041e2030f50040340d403251b0701c042d80050f5080d10700394076a000340424107500d10b030300040c8189064160701048070304106111551003080c501c640c181d1084030124000740340e00750401600100b900e00030401e141d0000002d450700ca88205400c000e00c0b01010103101032800b44c542140364003060041d103204100b420b02400840d80d564210f007015603000340c000c00c41541d4078015204294845100e25018a9041d20a041402000306556a0001c01a15031926080d104101080c180c0d02802c2c0c204080f0b8024020580202002c07c060980c0380102d5804450003414460061007980c0000394600035400f0001c0404140f4500b50252115030f0b03040c1904044000f540d10b001d9050407034440e130040c0c00070151230580d2078a80d4040c2a000f80740344251454071420300003509158031643d0b007801c1300d4080b = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 61725650 1250 61724400 61724417
    0x1080c01030b130f02070602040305010914060106020309010e0102030903070806100b070c0b0c07030f0503090406090c09060f0908010203040b0a05010501080c0313020d1b06020705010507050c060703020a1a101203 93
    0xf0f40c445900f1091110f80d07030b46801450241036a440c14201e0b007007a001600c003030703548082200811407030700e5001c810606036100801880d8074040e802980c0e8410102c0080c10000134421640080c0d00030003d0f10f054600003429500c0458941c4481c66070b80f50201d416034041c815484000560781802c40440380010f030029819400203050084c0c02903070341d00c170f51986000346c4241e04002010603c14094240041c0c425400fa40d66099404104010342e0001d810040b031441c6801441075141d0707000310104049a80742d08203822011340500061710900159441250254000020041042900480c02d03100d8003d1440821141e40c885004648059080303134003480300041000801c41d0304032407940006101f440140300b08103843e429550040c007030540f1a6404040c0394290703401e11206030180540d40251400b03103000c0c2c0c00c00d85180c40700341c0e9030021099603d01504000845400b410300c05d0080b10b014980005140e10700070300034418642100422140c5081a5080b0240807a81050b48007000c4015038040c6c2c2d94820 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 61726900 1250 61725650 61725679
    0x50610210b120d030903020111030106021506012c1c0506011a07020a08031b0610090e032206020705040501030f080a0c02040f0204061b08070b0a06030c030b01080c01030b 75
    0x10310420032842d0780411048000201400c1c00c01001900740b41541d8080b80f070503883c0c60080c1c299030400510031960b407000d00052098950000c0c0c4c0242c0799003540b0400c017540c0c40c5d400050780c40348410382d451249901c802d010307038140d424165107625075008145c1d14640003103c0505052001001100002d0081e00500d004100c142d480d10081d80d032840a203003210745001c1940c1d0001d079402100380d1005059800104044481007071241711411160321980c0600641d1030081b2207d031040800c0d0044502445d0340b088000c461140030403c2d00c5030600b4030400c0b041c034841103052920040f402071040700d005100b070303800c00704041c2003500405040340d611140b10403160700e4943c0c4240203504901005001c1041b1080c403080507036698024482070b14400400165191b0504a00070117800a55140300003045050316040006010502265001a0420f08040894481d03501500203845503a202070f0680401d240080140b141703012020341201c00043c1101c1280118100540a03952001b211a40c00f02d84480c00c1d02 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 61728150 1250 61726900 61726967
    0x1140a05190203040803041805060406050609060705030408070b0403120f02030301050409030302071b090606050f0706050417120a0507030905071802090a03050331060f050c10050610 80
    0x1103180c0114019a803c203500c9454240c59504a43d21600740c144480140404500b0308c0c4c4600c940007802590144072141c108408076081e8800e5070200f40c040c0d100020100f040c48418010341e0040d024800a80b02481d50b81c4484c1c0000e42c1040c0400d0b10b6140080c000c4900950050007152007803100382e0091030860703190108000080002c50700039418940c080104400095107002d000c41c0700102040c03400003e50038205010b0031190746410030814013030200010807544250b2400d988002d030340208042080d42da5458803d0020750390380a5031100d9803010071a2003001c0c400403242841174030000e2082001740d4401404a0595000900140142d0040c00302484500c03001c4c0110700c0d0582d8194809481c0c8003440300031a5180130075600641c3d01e50004281d480c0c00102c02e07420f4100304210300300d8980100e03401000039203c280301445200c003800b100c404035417950f40c000c909490303285a4080aa4030f0b032040000c2c010703024142c101c0c0c18074421244005880225030103990101204252100c440300151f028040340c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 61729400 1250 61728150 61728187
    0x506120601031502070b070201050709051009030204150b030c03240904030f030615030f0b0411030c0904200903010507050301081213050a06110c0a030b0c1810030b01140a05 76
    0x490300f8a0b000c1004001180030f0141280c024002c035400001d940c50711001c0140700000caa0425481142d070199000440ca0303000c0c0c1e241040c2d0360100c0e00001c5481030b00d00c1d040c00c204002d5004c5a50294044100410f51030000d001e14031400c154007042120360007a50110204402400502d64010105030104011a115000392610426035050000303185440740c0c1c51a4a20740702e04841c0c000203803202c0108180f1999401a04030722801130b0b500303202c1d0301d4194100003154003008007040b0001e030000c600300d202d075500c80d0444c9135401c40000524440c018030140003186031307004d07440041c000d600300f001250b5154800c40480c0c0c1220803440103840f000f040c4820881c0c49a0009a03e414407011480020a80d5590309031204020909038a5600f801c4600700703562801c0c900030700b500d80d214405070041000442c1164002e03550104000d081a981c2d080d40e09044a582a404404c072500080b180d0040a10540c0650101d51f040000343c0380e11400341e41107a00c031030080c4900320342d03000020b40c1400343c81e0303d0316081c2400c0c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 61730650 1250 61729400 61729433
    0x40501060912050a0506011202040e03120412020102040b04060504090b03070305030d0207030e030d080906070804030f1407060905030d0b19120302030c0109060605040606020d02120a09090e0105010306050612060103 94
    0x1500c03010107036905c92070324280007a0400384049182a00c0c1a0031840d261080e050601010406981030501d01c0015213100500108050a0301400c5503c400c030307842c402e50494000c0c01800301c1543d00e483e00e407040207040f504107000e01200345180c000d482005140010700101100d40c17000045140140300c00d003a401035004400c2c101d051006001c074806040da4280a12000608070b83e4828080e40f40c140f170350514104010380b02000380600c100500001c25070101c0c00780d0034a1640e082402c9100c0b0701024180c0203202c5c001028184a1912550000f08080400103207058101042d09000740d000002c10020200e0f9018141940c0c05107486082040549131011101d2050203401a03909005c1000314aa0954190030b074126501c954460052025240510540000e000d103440241540e00c0b10ba04065603a80100e030b450700d80c003100400c0c0000034512800048000e04540744003445179044004100d4080d110030300044665038146000140740c1e04201c0e100c9040960003c0040880340d20710b0f00c0d8104883c660303880 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 61731900 1250 61730650 61730653
    0x121e0c03060b041401030501020304020a0e070e010c1509050c03010c090e0a18050a060506100e01050315030304090e0102030f010902090d030f050d02160b010509150f040b0d0302031804050106091205 87
    0x1140c1c04d000e80340042580c025801000003580e039140510400c80d40341441c0d004005000410303001d0002d40b550082440c504403a0070f0070861624000d500340105050003c20491080e070341000003030030403c2404140c68426020641c000e00040e070b500e000a440500c050300070001003045080000380402542e4100f030b0341500500700100c0c503d0000b40c0329142810300048080d03400b1707a2200c09011043c01c3c4103903a200c5a0020f0300c0e14440342002d800008219200c00342001961200140749100c2d107580501c215002042c004000304408010154018080d4100b11428806065000700024100c3c105008036050388000410003258081c03e81e905079190680840311004010040c0060143c007455803000b0140c0d02000b011442018044c0d2030505070285058004901400005050015100702075141107489072040700d092140300003100102c1d00904164502d143c1c0540ba402156081c50780201c000c1100461604000041348285020700041d610f0a2081000085020030104644e01e060004954070038401c10 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 61733150 1250 61731900 61731911
    0x30e0d0c200a0e0421050306121213030b060a03030203040b0d060b030f041103010e070528060905031605010c02010302030406020c0106030308070314010515030718121e0c03060b04 79
    0x2c280b1503641d580040a400340300340300348814040c141c044480c15580300113146a0440c2c019030010b0060101800060040405240c01000ea032818000ba040b19001e1000c0244c4800c00d80d54400b400020700d01c000e803111801c880111b4954204401d16005607501a00118030b44ad1601e68404c1059000b007221854144da10300c00410340301208001180164604003207100c65007800c1c2081d5083c0c54100083c148203030b141844860a80034042400382c12100101d6144034011041c2d00b0407415a0154040ba9a03510341c0c00c40c001c038980c1d03041411002554420b42c11959900e80a4424250080e528040d02d8086580d03821001c1c010741c403035001164807502c074050141c20104030903181400c0d01d800c0c1d001100420114030401000b150305100e02e03240c6241000400495516010100340d041e0300d81c0400c9401000700100007101e040c082c0321b030b00544180510200801e240e4480340d000c10b150040e40c04441c40c1c003002e96601e20801000e002540d00c81e402c803011500840c0355590300e90042c07410704485500300381c0b00c1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 61734400 1250 61733150 61733213
    0xd080403091205011b030b130e0f100c02060f0408030a020a0516030305041b0f0b09040e060f16050414100e040c080117160605090402070f050d030e0d0c 67
    0x1000b8002c595201e00d0003c1003410424050b1079034a12040800b4041600d090560343da030307a40318071698001d200c0840f000140f441c4860754560070a660030031605414807881942400c4d0007820b03404000c03402c070703154291460b945520349600d00788070050301c000d0b1000781c0500c04644418010f5008010f440002d0070700504d00322803108916242d139140c01064000c01d607940e040005105a91010101c000f10410b80c0c8042c0b2402d002c04040300844500440f42d070044003042503e00c540303c5512403d61103046100300c6000e440c191071205843c40c000c803031560040b030308103404920080c0141c05507401d0710341e0314034401c10101480c024400c4224024403145e080000c6007095034002e8442e44101e04581c0d141e560303034103c80d606002c81140d005400442ca565543d114042c10395409490310083d40a440315454015920744800b4005000390043c803002415018280201c0710410600141441030b007419a1020711010200d20355013a1603080640500300890080d11611000414800304103038024002c07150802c040c14074 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 61735650 1250 61734400 61734419
    0x5030a0605100201090b0f010b070602030a140f01061202070201050901211a030c3708100b0f0102010e07120602040902030106030c020709050c0a14120406020a0f020703050d08040309 80
    0x1d286442e40540d40d80e911101c18040c4010300240c0c03042004901a030350b549050084011813042c4000603040c1740e80403002c41e41c511040e4028215802c1c2c2d5050000c103900700107d5002c0c0d551400e12400c00480c0344403c076804000014000d9518080c2c05866550520a504006698000c0360b0f51140d02421100102d40210f20b0072403084c3c2c0c035184140940584825504801d1520746010351000d944a0920310104101d40f206800003400c1c20410701c41c000541182c0018001142161600006254081d06640400080140e406034600d10011640c0134a082100c1c4c1c0160300325960101c1c0f4002035000b511050240031407a01d10960007a02c1241d00610b00f0390740710418002c9800a130442d5002035114007489002550400034103000c1c0810030410040c40c03e0800303500034148a40701003c4c050083c03000d201c0124504650540f401c4000450412200f4902403030701c980298003c07113404001c20180900d20504502c00039000081c0ea501c44020090300c4070700032050b180400c00400442c1000703a02030000c14400031 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 61736900 1250 61735650 61735669
    0x60108040b062103040f05061303060b030a0c0608040303050606070209220807050f073807080a090f0f05011209080c07030503040302150a0e0f0112091a01080309090705030a0605 78
    0x41e803015507112400e20b001200c06c82c000f648000e1281009012040070081c045800000701d9521a13000141da89540d0042401c01000202c098156111070000143c0c0302e801802882c0300300d1103036404000c0303a41c918003080002d00420300c0294109406034002000050002810345412642d80d10882443ca410b507550705540d40021030884594000300c090482100c000c00c8044060607080c5507442c200c031138503000c5402a41c00d2817142c901c9644003132480c81d403a04107031003240d107526044030f00603039210041034010b00340200303510840a0b601c1c151741000501c008858901d40035280142e6980403a080401d1802c405042c0c0048181c9030000100b00d101c2c1040820480d1800862140340036644680c50350040000092500c016585114001c1200074400c9a01414541c0c104808980f00c1862264850040f2407480d6401660400b440c80c00c108034091001ca0782da0fa294001c1e0901c1c09000e240e0303c410130b042d100c3c000c0040041e003003d546000324503102d00a9000e981e000d4200000055400c0c2d440000915819 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 61738150 1250 61736900 61736959
    0xa0b04060b1302070506011d1506070b04110306010b0408030a0c02040b0a1d060d0f03180b040f050f030705060f0c010e06010e0906070807020d0c03120f0b011205060108040b06 77
    0xf40e00040070030801c40f05011340c40c018500d00364808499600142c0060310505d0040503814070141d9100140c1c0581d44040c261200e044d0003c185e2842c130700d05450b00c4008045129001480b03803040000005586280c0720855050311211409981054003404041d1003441c0c110320120703805512903110b03420548070350340032400405500c406e03103074200d1003041012041e1101800c0980108400380c1301e200880c030300c00000f507034690341450314561304240750076850f018105c242c11140081c14002000100008090b0407881a140f0440d48048225914810196100d041c2d12405401131810b01981198401c21005030181039443e80002c86e14211004110782041c000360065019250b40101303104441d8020072a5a074000d006060681050410003800303540c0c0e501c0c40740d001081118a0500d0001c15101e28080080c0044038181405442c4900c1b403030501034401b428410b400905c0d0b035600444814454000c42c0d0085c0342c183c5511010b522152140f964000004040c0c2e41c00100c1c0e00c101101b030320140e0729804000c9 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 61739400 1250 61738150 61738189
    0x130504020f0a080a0e0c120114070f090e011404020f04080a0c0627050603090a02030f0706030507050a1b08071505010905070f021c090302090f010f090203090a0b04060b 74
    0x10b10042501524000010b050300403c1440c04d404c1c090850700c00110684a003a085998120158104092034054010b514244607118500401e025a0705d401a5482443c4041074503090340c203580b907084403e21301e482445a004500700c0503c003200380e400c10f60b0060480240501c025480c143d11007000600d41b070682c130030032a00300140020030494140c1c06981c80c140310403107456140c0940b10400100c642c0d014a4005e0500c10702000001c0b45084000b000440045907000c1e042c2d13488500e000606c1c68488140e803007034101090030000000c0400c0d200d04200c1e8014031498450f0007110010f480070301189107a14504581740c0608006040101306080060129030304100e90102c0c481d0b0420100b14140d40000d450b034000d000e1000084d5040a4002c01c400c10400005004c1500f281319984045501c00c0382e80e48007070740140d01c507002d12007000d180304145416248100c1e41c4c0e10041c0d580d0f81c1c2c01c0040340300844401050350449840b480c006030f0344030741190300240208400315520150342c0024032501034203840821030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 61740650 1250 61739400 61739407
    0x30c08040e010504110405090a05060109121109061008010308030408070b0c03040203010b01020d2304030b0c07061b050702041e05070201060810050c030402060d0917040801150602070902130504020f 87
    0x142d04c0c06001d0386000040503035605040a15090100e4025072001d8203070307400240c48500051741c603441207039030100812134a0024400000541001305407008010300300e40c00b4031420030005e281400c0040d185912201d555452100c580c4c6144c0340c0034015000070300101e5003420104900c00106103107031502400b07103512070704856807401c0520401d03003129096038865040d074000d00b400d08840e540290603511400850030343c41e00181c0c1d8a20382c40400344a6034000801c243c40c15428802c40d030344000d02804885104a20800241142c048241c1c4c4402862281c02c0018400300000801410f06800070000911044420040c5140100303480c420740d0070481711880140c0d0740301c001300480030341009035003014105e1090402c841e040061041041c2c2c032005001138000c002c002032960000c0c50f02d50000e034130036030000d1800003d0300d108030942d1500c2e4094850302d0020340c20070b81c60b203021540c481008421583d20b40c00800030140703004801c0c0081d4006c1162105044101310000540b512640003e000441c03035280d48503613 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 61741900 1250 61740650 61740659
    0xb04060e010e070809061909080f1e0301030c06200a030e01020111042318040303060f170a140a0b13061407020a0f0c1707060206010506070f020d030c08040e01 70
    0x80b940c0000c015a08120b0341600340a41a00c001c24210381100c3c2d02c41e4446402400c0c00030788005001140c0c0d0003401c143c0005051600720401c0b0020b00403400181d5940504028050000340c00c0e07001c00c0c08050080302030f0007020000507004120b0200441240c1d4030140041c00d05018541c14a52882001c0d0301252100707000300b0701507a0a00c07500c03105039856500b5500f000d06101101000c20619004160000c1c0c0350300300c600b52903030b50314061400090442c800403114541490001c0c0a4282e603c58240403040050307000c1602400200e411070141c1c5070b00028552403509071a241c0c0c00962802c00103096000e1084810040b0780064006441004074804041c1126040d24140c1d0890340300d160550308140300c110030300c14500d5002c0341c401c5046821203109941d0706a00c1c01c1c958201405c1da070084c050383c203940b00101c0032800017040c442c0031543c2c640c0940340a60380c5c58007801040c2c0302d0008024042c101c00300c441c00051809490a0742e4040c0240b90152400b05d060340c0701006503000c0e4000354100e00d01c0100421 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 61743150 1250 61741900 61741919
    0x903020c0f01030c0e0d08040f2c01140f040b10200c0306040b0408090402030a1d01050c040504150503030a0903050c0a0e04080a0e060d0209090105040905030702130b04060e01 77
    0x14001c010a1804000d0026400c10041c0100c0000082d18810b5005400f8403050018130410303100038058110100303103925034481c000c042d0013030b2091000d1059021140c00d10385c0050741200080c12500c43c09981c01505103042e08211048a555054980c03241d0b890b94800510303251940d004600090715100d140803a4500a035803003481007108101c00c40c0354001c05422859480c0030908903045603003e2616582070300d46190003400b034003421030266005840801040401945500070448403500d0303a01c00325070400060180c0b800e03201c00710b8540400e020100300800040c2843c0d482140c00a0010800c0f00708036403a80e0009003590302c000810750000312421020302c284102400020f4036184100c0341036184520300b40c0e4424540d04003c0014280c000c02107031210720240200c0c103007110314500030600ca54848103042628000d40003e200540103500310340c004071711402d1611803c920740b50014015410101e041d070800c5203c109982c4614500c9441d020b4401054039540120b201a155211100900358140494507 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 61744400 1250 61743150 61743169
    0x603100614040b1e101101090f06050a05010e0c0c07050a06080108070b070f020d02180406020a0e09060612060d060501080309011115011505040b040902040806100b0d020a0e040903020c 81
    0x61084c4000d16005240700c0c0e140098181c010f00035200c403c21100b20f020156030480350024404615400d00c540b1104001070007900e41c0040f840341d5002c101507101c0118501c11030706c09000f070704001400807002c9514041d4410250403482c003e00200c1d0841034444002c10410562580709002003941c4030014000c0c2c40303081c0203640103410343c2d403902d505060294803a1100c405005202a011710078000c448415034445054401e07229080b01c0c0c4c3d0040600b401c2c6001c0000394051041d070400144e07000e00300c0140d85407811409001c4c040007041c00e41402001605050820400361049078051701020100d000580c550088600070000f0030003950704c900c41d0340009402d14000883c608840d40000f180303903560615640040d4155212013070310a00100c4114001c1e130f018032550f000441c004101140000f0600e00c1a0010302c150f1300003030305440880e114851708000500d400c1c00b82082c8080c05211000748002c90b507001d0140e07050103152882c8041c0401c0c000c00d048941190301600103801440030744803a800e004808 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 61745650 1250 61744400 61744421
    0x6040b09070308160618030203090402090f0319050105061002030301090e0f060705040e0c04030b0a051008030c070311010504050a09052203020c0306010501080910020f07050102040e0103030e0105040f050405060310061404 97
    0x860700c40303587c0003074a910030444030510aa50200c0c60030000c0c0c99801b004088001c0103801c81e00e003511030031f41d00381c0343d02d100c42d000721019801c0100203411418010103600d0a21070940055085908100007900a002411045c00040c0b2846d9212003004c5000c0042038046c0d040303a200c20340c2d41d80c200550010281c000a241e4032400100700006c0002400550800da44400008030000e101d0300e9083d10390a407a640e43c0d02541d610312004c0340c4250b101c88041124000c0742e00c107414490081c03071844010358482c0504c0c414942d002c000c0c0a03080003401d1040e00f00c41c3c1c1c090180044404840c2c42944040303d10b140703565041d030040e409000001c0c0641810042140901001d0a001c28180341c00c036905541c4128001c01c0c000d9a5401143e112112041c901c16240655031000080d5242c544030200164009030074402540010038002210b01d4035409141220140c2d00c500400c070422504050a0201500014006a0300b6210700e5030030901400341441004041c10b640c5103000b81c11615041000140d907440820b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 61746900 1250 61745650 61745681
    0x114040c0e100e0106051305041d06060a0501081303020a0b0c0319200c011d010b03070e040c1401051306110706031e0c1206080d080c0a0206040b090703081606 70
    0x609025010500f0300341411680c0358580f642d03949070000510054130403c3d501941c3c01078144110000c9541403082e40d4010040c4001c1103e456035152002c200e44c40c0308900c219404990014003180700410031007140e41c0c0181c001d0040315141401580c940c43d009004403042c02482201000380301c070040140d80308070410748400405020040b5100f090244203480300240c0d4480350340c000b813481c503540c5003034012800b010120103940032008000c50102d40a85440c14400380b00f401130041c0460550185884940184e41007038005061380d0400106505040d95a41401e06004045c03061806055480d40b5a4000d440b6540d52180c1100c1401500d62030300710907821041c141424580c04004899180c0c1c240051561b034a0004100307c0001001070b01d20031900100c0046003800c1c84c001107015140040e481c220402255108101940c954141c2e6050303000781201c0c040160001c4c80070501081804030129041019042034a024650301d81e521055580061058500c031012204030505000b054407941e03494440401 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 61748150 1250 61746900 61746931
    0x604030e040b101707120501030503070606080613081e0c0114010b0a081b09060408070513060e0604050402010e03010f0615140406180504230a111206030114040c0e 72
    0xc0d00030f81105000c90203250130501c9900001e501c184500000400b482e81007008000359610780c107003140c0b02d174810103040d034100c2d044c80786c001038001780042c0240c441d4035101e480000d034884503540d0880b9540003042420110500010752103450001c3d000030000707021010000281c000000900c240200d805038414440a10213220301180640c1012849501c0135091300040d00240034010740505a0242e030078160781040e00424081441040000c240003540c80c1201c80075150140300c48640300703640c154011418204c1c240c0012540c50306241e00b0450304030b8414140201f818100307502103030840d00404201e968041e00c074481000403100ba014180515030007031411100000b000d0000e034603648210301c80c2d5070401c005101050001e801d0707090f0ba1405090014801d00507200d841161003003040401060401000d84400442c001c13a1440c40b48103040403111403a607080610f00b800354200c00100424650b0075540300d901c003c501501145400b84a0f600c1211858003080c2031510812028500900d1001001c1c5050f = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 61749400 1250 61748150 61748179
    0x2061c0c03110f071b0e01090b0d0f12030b040f0207031211030708040c050402030c0901081807051302040b04030c0e0c0406140901200708010b1e040b030f0604030e040b 74
    0x180469409514411089513900c1091401d12800d1a000d00301c50503055282c4408609a10f03c0245281250241c00301400402d1401c0c040113070758202914000e051106040c4580001003403411803440090440c1400614140c0b61000304065070030001c407421100764001400020580c000b54440f0460103c428100b003c11107078401c0b81a90312004c0e0a04081c000803900080401c02940401030140002500554903401c141aa00c41c1607004104200e0101e101e401c00a4074103444490581a0900102c004019032403412091081851106c504022180e80800010586401442c000e2004600c80c040740983c851404e420f1009021020b404034007040e1081108000d03841c2d101e650248500d48200e00d80343c0d00d52429006852808800402c1a400c83e90308c05d10494031395000c0b4540c4101c902800c001c0c4000300c011420040908480b084c1104980400703010380c801c43c103159008400105020341100c0d10030004010781450b000d8101c5040700010b00040550400e0300313107800b40c403d2014003980c102050110340c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 61750650 1250 61749400 61749431
    0x408010c0c0b0a0b120d080105090f09060106050a0905031e01150305030307030c03020702030d02010506011101110f09040b120607030b041103130303060512070f08030306060d0c050702061c0c03 85
    0x9409070308100c3e1280402d81242d0f5424010100e05c041d102d0803168450480440501800000d201e1b0a10a140d8400090301202040c2c2813140329940000180045a0800c04141c4190b00100000d4080005038140894103413020400c4000550b81200082910460080e000c0e0035211a0003060b030305507030700c114200005040041500d800600c58103020484c9001807000714004d000700c02002c0d5152107403142c410441c03501940300d01d008850030b9a55508410359135565500b82c403080b401010468200f007012032000c1a0078400b0b041034120090000c07500780385440c00a0300c0002f1400401c200c42e000f0030b0511507850f825100c0c038628088142c1d0140305402c8902400003060100400194807003848a01d04000c00d403181e070000b0050440204001a41d5441c0c8040701c1d902d8226015140c030800d80b000c40030407100800000e0761b20880c0d00401d110300d00341601c20740802030001114800207200d401e01c8050016074803140031f0321440750f0301491213601808010114051302c41282646007410b280402c031158482a = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 61751900 1250 61750650 61750673
    0x50f0c030d0309020103020909190c0203090310090804050a0305030a020706020d090510031103100504050c1e0c0a051005060f18010504090507050901030b061014030106030906200408010c0c 83
    0xc85050000303c40c086400103030081e103d40c5502d240e102d89008200700e110310b040b44190100f00f50240c010400c0c0002d6038002c1e0b0f41d034416400c0d580d52640c0b224101c030021901581040c91320500c6038244605050b91400800c1e034214154100721784542000c203090112660400c2010002d00c0c46200034101c3ca03606041c0980392000c81c1c00384901030b050000309028103900a0700b2005001c10002842d594a01c0c00d040c0c0242251031a001e90740c4582d0030034000c07441500e0040c05445070042c0e800001d00c10941c076240d1080c2960f1201d0150140b50040d552040d0104005020003104007580742c0700407070149804d5040100840748030740414032902039200c94001203442d50003858199081990300040c10f103400d007080f9140c074066611031903010410350004401c000c0340c03090041c09103006407010381c3d4103054808103a4000300b01d0700c07007002e0015050004000c0030b17209400c40144d01d805444000b0340d104062201980c160310110310380a003018006030412505d03800b440707001d4000d00716241c6040c02505d030b0b40e548210060f = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 61753150 1250 61751900 61751923
    0xf020d180e070309020d03020708070506030115031d100603021807090b0c031b030d11040305030306100504050d051c020c090103020f030c030303070c0506060603060904060c1b050a050f0c03 83
    0x201ca600000c2440703000e60300221100ea0014814600802580b40096a440c501d0148003202d00840303600140301c0c00c5c00300941707040e600362000601d00d0358588541100106240c58603403064500f43c4889908c40c42d414844211450300540d07000c03c055055005000b00610341030001c2041c000b0745001c104c61203510801501c00d481026501ca9911840803403040e20310b0103401003680003400301c43c01d03560040d400040188250320740b81e8428044807035400d601b43d605005a101c00342c800c0d0402c0002072824038298901080f420342078103040c0d061a40740c1c40413805004080d40100c031240e01c1041f0350f00c130b02104100000080003041c401001c91903507840101d11016010301c8028040e9580004200c00342e5028031641c100b1010140072aa203e180130940105040d0820314155038501801000c90500d090180403a0700c101400f420713801ca0350f1030383d5a42d0300c020071404d4021420840104070040c2d5002352546405801d901070f0005100071401d50401606120b01d010304031b0f01680c0302d01c03030b110829200419002e4001 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 61754400 1250 61753150 61753169
    0x30601030e030f0a0e03010b011407031209060614030609060105030d05090a0b030c04090b06120112060603060507050c06011211061c0c110c031204120303020d05070f020d18 76
    0x14104000318030b076005100d0202e5103180b0100c2d0802c20350764040031141d4020400c03002070203050040e0006485281c1c0f0308441c02240b03070007041550086800345800d2100307420101c1001402d81c206403121030844038280c000080d240c20115441142c2e2608000041e007200c0254017400b03141d450000000d98840c1114600401c0c01008600401d1941d2524104c4004103284103420780e6924244244001c50351060040440143c070f0720100760002d09100c07065450341c486010a0b019140d00303200390500c0f204200e50080303c0c0662182004230005103240651405460140c480035110212031b040b0300e0600505801c0244060102e00381d440110f80c0c403000442c0750b80c07c1911210b40e1100b07000030420481804405003038805017004000100b035548910050f8000b0015800c0d142a01034080402d900c03890b04600c11620000244410b225844c01c0c205100c0003188070b800e00510706011802050185c0c0c6003241c5010220310440d4a07038500700d405105411300e115003480c040b00604451200e40034080c2290142800b003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 61755650 1250 61754400 61754411
    0x9010e1f1209020a120201110f0c01030e03161b080c030c040905101406090f070e04020c0a05011107020f090408070809040b03101b03020c1c170f04031403070503060103 74
    0x400c601603100c151401d4010313020032984c9440d03810200103d41c00c410203c0c000f451000c5440c4001c1c001282a0f41d590301b150004e007020031040300044018201e84171081d0f186000c100328003080d440008000c1c0700400c0c451408140d0b94402146290340c1000c0030780c0401883c4d002280040000d5501140820340e0a01c1280c00190350403035410100d1412460560342d82d00c1b1442c02400700313000d03000301c4404c40c4200c80c200d4440340d850b6a00e4201d1a40c2c00c10680b840c402082c1d0020202c085841c1580280c880982c2080449000715940d845040c00d48030700c4000301140f181c2c00600d0f5025820007030b181c04041c400035200345280f4101603980c018944164000941109004141e00001d41d949422040c0200304c01000c9503244a6600b2541000300103450101c400034034800780520f02140030b4001e0300c100c011510041c0c5284c1d40c1580407494902c078480400003c0042d1043c031000d640c1120800b9a00440911027007a4003845c15150142140d1240b2294146042c8140208042503600c503040342c0d4000004e28002c0351 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 61756900 1250 61755650 61755677
    0xe1f020c10021218090a09050c0a03031b0501020d11180a03020904060905010b04020c0d030b040513150605030105010b040303030b0102060103150e0a1202012408030a0f02030c07060509010e1f 84
    0x7944030780c4036280b070b800004103050025406191f00024540c1d80124180c03802d01c80070300d0030446455002d200060110380100418515651110450410340d4001e10002d442d010540c141d800403102c1400d401ea52550000c0741c0c0d03140c6e1608448620030329200543d201d844040c03c43c0c00040c141000100000c0c0101d84580490080110a4000018100e00a081552204241481652a1100211207000092912000304441c0c0360a0290a00480813120074078102041500c2d10b000c200444401800003503211800002d4070f840c2441050b0003454540c1d0782036150313820752900a00303440440001a0440d440480180b0108a50a189801c481001c080000d0a6048000211f06095108102402d0445a404140e5802e034043d0403c5190750320310f203501000b1011011040408621b0340c09081820340c414011071600307a004810010106901c1d004403420010306c040786034a001c85542110000441c0801d400510756005884001e400c64104d4100f19408480302c00c0300d00c02114654440d00300581002a40c4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 61758150 1250 61756900 61756927
    0x50d05030418060608160e06091906050306011116180f05180c120a02060a02070b0c070905060405070210050a0603020607050102040e0f0903120402010e1f020c100212 73
    0x20000d00b00b0710b808501010744245414000c3c038581c802c1002180c0399400040d4180c07003141c01d03564200840e441e88030600700b2036020302c980c540244c0e60f141c1e0403589a48a96011600074810700c40104056070702d06a0301d140040005206141c00140386151b0b52201560300501d40c01d0305001c101f95148460081c0d180900c10b0440c1000c0c05200c0c607900d2902e464803081c4440740c1d140c41c00b100407520f803810444845089500901c24001c6969603040304036008216400014074240c1c0c010614a00c4a104681189403100c6501000c2d0f03110162404035640140000c001a8540317005d00303a03001008690421181c0780c07400b8040e41f1240c11218440401da80d50b00003a00c1c0e240b40c1c0d4010405176401400e0151180f03c280b41207030003544907000e1107500c030900c0d000048000c641c10550610641c14040a90b0500d0b04280c41c11243e00e2010b00120705000041007800095214418054604403072012800394410799118040d06200002070814000c0403480242e04a031500000c04612000b001084555107025006000c0d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 61759400 1250 61758150 61758157
    0x60702060d1d010c05040e010e25020609060a0b0607020d06060902070c0302130506060409020315040c030f0b01050406020714120118110d1707052b080907030b01050d0503 75
    0x115560345003040c0580300c00080d0010b4000b00e0308140080201002034036040e80d00307000d01e114442d01141da100c01800105459031410360007103410708003100701d800b628199440d1500441080c1005174000010081c04001c00c11150781c114040f040d04001c1c8500c1000401c1082c450307082d010340030b2101c5d1200c1c04204080c9920010060050100443d11818a8601003103a0215880240e114580640e0054500702c02441480d0082000405d02031402d441c100c108400707500000d102c0c2d809804070040d01e051381c0d101c901405941c251940c3d00000c903a065844044220b0704049040c1e81040001e01c0306102254000800b070040c3c1e100702440c004150200c0340054071450520390766290725424481d490041103491080a210039104210482e1170107141424080501c7d44042c004d00b802960203c04851070501300d0007400303028000c04c00c3d1030347c402950051341c0d131841c54240c80303c0714a0302c801411140c0c1d0364440c5030305410454580151514a14503210003c3c0302c070060080d00d02c221800e4000c1003c00c241003045 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 61760650 1250 61759400 61759417
    0x30403050414130c02030703080a0b09060d08070203101d0c03060a0218030703030c03110a02030a1119140a0e090703061d060c0a1103070f1209030609050d0f020703050c06070206 78
    0x140504e4014400c002d48075041120210046200030000c140780c0c440b5805600101c16010304001c650b81d44e0740c0104041c00200540640e0100d000b0064000980c83c1440401804401050b01044810040c3c80324084184c045141c82c8451700b00090f544000d03a0081511504800700000158803041c60007480c0b081d00156a130890340c14030031008004101900800e05440c45800703a110202280c0b840501152541d0661400a5140d00301040b0785000030325102c0394201b0007a024240c100c010519502c0302c1c1d16050650020044081c240700c003041035240c40c3c03c42001614000014448071b040c613030031003075890340d070b9000040126480e01c42281041002210780c0d128401e0f14030454009091441240ea980e80c8000c82c8480086c103d02044111000f001080b942440d0703000e4610314442d070b019191400459a0061031008000394404c00101090302c43c003134061010700a13800382c045444106005816000030403802c0e01550081c04003080403403808511822560815510680e8620b80d510000f14582b144004 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 61761900 1250 61760650 61760689
    0x1092705091f1d061006050f09040e011b03020a0c020909010b090708010509070504030f030f02071208180909030a05071e06050912040f090b0f040903180b030403050414 74
    0x1c0c0b180407000e140c2000007a030702c0c620452500f45209050107a100c9204690212540e8004407003007180b14400e10092000c540820300d40d5042187c08000182980d0b4810020400d90391205c0c2d05200304000414280455680e5080440c60b007161070101900702107130b0701c0003e80310b1484c000000e0a4500300f074220422000c1d0042068100c0d160945c4003401c8404280100c80c0181c4801d40040c032422301032411202969080410081e0840c1c07255070031989910b41c4010001180142c4100041d40301038202c1b001d16443c2700714100350300d13041c2842881d10301c1c484c5a2004d41c481d1182c8002c0c080031840210407134800003840d2901ca0f503580c026080074003400004800484d20340c406008000c0501100b54807603400b54091750241c40100d201080812032a00490061510071000850304019004807640b000014801c00340c40c2c6101000a100010100c0748601010703808110641c100703240f91a44440c1140c0a0407c50a056055040036100202140158002c0041001c90603690040c5650f0742001390512070f0b01c0d4035 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 61763150 1250 61761900 61761943
    0xe03150c031006030506060f0903070509010f18181401020909040c080114040b070e030a02060307030204060f21050705160c140102070e0402010c020d0c060305060109270509 76
    0x50524040341c0c822141280040380185020421520900419004040c010005400c11640e1403104500342d05c00701035650b06205000300000d0750f40f540c550a500034444000c0c0000c02c00e20b04640c24244040161100a0142c17801030149040a0310032596425681c20910f1000301c3d91000144500a01c40c00004903484500c440c200020010481e40781c00130b40d060f00f8000c1c4030308114202c0c00e1010200c16540180b50090103000035400911072240c4020404e40142101c140c0c25103a004144103a005640382030010740c000400744205034000e0911071365004a440d0415141c802841e8014a18001d84913515040c0c0d241c0b00803030070003842502a00e15070300c590412460a80070700d1070300d000025942d11500380d1100314413224500c150700106180003122094a4031444a079126401180c003016909812a40403124203200030110b0f01031880b010207407589490001d2113003403080c0050720507031a41d48000345032606c043c200180c010301c041060760131103507908001c11701c2d072554404181440583c800c00800c201144 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 61764400 1250 61763150 61763161
    0x4050316060209011101140424020d05070905060f0f03060d050d0305060f0a0503030f0a02010e060f01080606041b0c03051c062103050301030f0f020a0e04150605030d0e0315 76
    0x1076000301840f0b4000d8854860180d0113041640c26a8011205c054002201e40c000401080822202c131040114901c0400844d00801b4401000c981103603240e0350002d5610010032010640100300c00c0050002240d4481c100b00c0b21401d8440c1c2840341c0100b4802d00303040403020602540700c142d404003085034040140e13582107645881c001c0040c44100ca040b07100d0b80740600220380d6801e040b00000c00b900c001801070b601e003000c926981441c0e41d00c046802400c641d40c642444440f984107000041c000d81c450001000e103075150040c83c0b4a04140036121078801e40c0780c520103045451441d052070b1040040c43c14504c50360300d0542400c1d01c0f14040d0103240849882120310300b102c0e036541e40d80242d0548450310111010015401d0f900c640404810a009001c41d104100600200301c01c3c130605080c5030322800c44002500c0c81c60b80802c02c0c400306a0700003a41083d40c1d006100800888403140300100c0b0b40568200001c43c0741c5070020381d03a40d1040d416001409000b01c5860307200c0d1414458030781240c0c41e00288043e00e0130070 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 61765650 1250 61764400 61764413
    0x9010c0221010f0b0d0204020309100e060f060603100501110a0c1d1302090105011803020a06051c0c090b0a09080f0609190203070501030e1e0f07050406050604030b04050316 76
    0x7403224030340c8a5480d140340010012254459a00440d4015082c142c0f0840c8503400c0c41300a40c00900518040d05c81c420b200030703100c00c1d0f42c0200e40100318011f0142c9580d0614001014802c40040c103150f2280c3d4040c07042101245511403072404651091070005600c3d4440801d1a080404240d0f0240100141000205a00c942c4d071208c80418441c0d81541500b80d59840c120030090881c0103c000c0d40161210010001984550080720720000c0003500100701c00d58071350015000c20b00342c2d408000410300c0414040300444501c04010902d1a80d6041031100b02c0b5a150000c0800c8154050705075500c01c04902e0507034161107070f50310001030101310302114000403800301101d03941c1d1022115810288500c01d2020702113140d864500d51116070140051424a061030010760190500c2d600d000e641e841030800b040b100085021900c2100c1c00c086019200d0442884405414030910350030103401039081101c1003003640c803074000300c07401c594008900c250301d902e6914104e815482210043c0c0c0040c504100340c0402d0046 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 61766900 1250 61765650 61765699
    0x90723010e2806020604080403110307090c09050405060d02090714070c03060603170f0d0f2702040b04021204060f021207050903011d1b0303090d03052a1209010c02 72
    0x14540c0400740b42da28101281d03154170488004004901c240b10400000c0c1d42e80c28040c0d02d01d0401400c0d6584152510b221030304850007003400400140005030108600d04043c0b007015000603044e1802c9030443c3c1c0c0358003c100d0029002d8110700400864044103005281450160340c1500d500802040c50f06603281448009030100340415200c01c480d03c14501c141c1d424000c2140c0541001020b4981000c0412a0200081c070901d4148206e6a4556030100f095141d00801c2030a24010b001400c804220940180030860300c1c00348400c1d001d94410000110001220700d60141d010b03503c21004a034844882c18600e019010750350090440800c00000c0c07225407904800034058241c0b081e00204002c018103807a0640312203400c103912904e90058641d0100b040101180c01d440d546018049a1030321103004013148a0003e404801d4000a10100704484400016820140c07000b4402ca8903480c1e1142c400b4449884030346e064543d00340304800140804440e400350054880040d00104044000c3c500703a80b10044942 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 61768150 1250 61766900 61766959
    0xf03050c0907020c1507020a0b0a09030609050a0b18060c180f041404150c0201020a0c02100306150201060315020f1204050c1807030506011706010507050106080111070b090723010e 79
    0x107542c020049161403227582aa20790301002e071740352480c80c0d04d1925850000d00454000b0b035031500454140b240480c05204032207016400e11844512803500c20800c0c10b00f0b149002d483e625501d1820042c24603140500c40000c44041c03421200e074122140c1180022b8002c180f8100e0740c6a0320210a0204414011a00801104030405074000d21680940003c103d00700d214a4100d200071420303070030184c40941026802c069441005040000d0960389841c03051603040950010703c1c0060f03440300c4090080060300c505000000c42400015030510140100b0502d0794010b9143d40380200d40c0c0300c0005030034000b0421840325100320141c580710101d038032540b2003052124103d0b40c0030080f070300f4007001c54000d500c03e000d00d0071545402034928001d030700d600c0700440f01c55001e50001e9420350b40b190404500400c0c20b03c601c5030301208541140d0358504132032900400d000c10050044403c0d07042100c1c01c100300c01486800b0f011124008242d4040501c20100595180c3e05408889420246e04002c001d04016000315016000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 61769400 1250 61768150 61768159
    0x150201060602160302031b01050d06290f04050409020109030c030813210209060a170303070314010b0a14040e0709030c05030304050f0609030f15100f03050c0907020c150702 76
    0x16480d950b0b8260943c0510000b500355004400305d21602c1d0039138501d13030301402051400524203a41480002c0a1300c1241c0c101081c8244036511020845086040c5c8142200c4e040c01042e00340446419110040d005500c995801942c4800c06031045a00c1204100050760b4082012454280c4a040c41e00007a044203461808a0713038a200080b8007540340d00c80c1200440c00b90380e2903041c03001c1c5560078840c0c0a040504003641003100c055002c100104904440c500364240c0780004c40d2070386040e140007030640d003081c10840c0030456440014040f143d04001240c440e507a190801034130103803100480c3c1c041445541c1c8082500360400c014070281585c07004242040364050b40081d200e40b030702d45081680301d20547c811030354070101c140c0c161750503801e1072006081c020200078140d8403001010700c4010b00708407140c40d000d80100c026000704032441d0380101c0d415020300729040034552001d0a5580b01941d0f901c0c0000f1040c03041c00b0f0301c0e000445041c402c1041152302d54018001d43c0f010282444143c807150015003040b80714 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 61770650 1250 61769400 61769413
    0xc010b100e0609011d151207030c08011e0b120702010608010209060a0305040c03050303070c140715360503070503060403170417030c19020c0105040b09040204150201060602 76
    0x4140c420030101c84100700041101c0c3c50840c5401c010360300c141000768500b000c035104440f01d100d540da9204250b464240e452404541e16811030f4458040c5000c018480d01c107040c5003a0410300304642c0004002d05441500e81e0084945002c902c1021034424650311040d09a5400503d0200412960030503078042c4680d60000d0018030f4903408280e00f13074003c036807003240c21150501548400d01d01c00e40010790800d000700030303c00c007445d1a501c5950859100315844004500803d8040c400c1003540c40c811200030040d64080c12225003400c096100e201110b502c0042044160b04003400c0c0e44212140090090008500000c0144001000c20482c091288101403081c0146003000030142008203580b84102e0313040c3c0d40c840404c01c003486885503114002d0002e60b45016540c0400315001409401980982e1032100760f1911214140004100600b000101500310341101c2c0001e0002c1c2d8200c0240d4050340c11b1942400c3e104d0983c0d0020030020b000d41e82c040705003d007400749803c080d19010b501c0001500d105034242c1c1c82 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 61771900 1250 61770650 61770679
    0x14010e040c020d0f030608010c03050402130203100504020f090307060801080d02010b10050c0a0f08120a021c050711060a0903180303050f031003140615030c010e12030f0c010b 77
    0x4a0300d40d10341280140c2c01c082401c3d0350041c45000c520543da80d40d41000220640c44e6841c860071a01a1140c0001007565135041c403007903240010619801e0520b00c0b100394030754988a0a0019a5651481003500807900452084000c80304101070b2440c5c0314000d1b040f2600303943d482d540140650400e1080e40b100303010ba650203007056413040c001c0401d00c19000e00781b01c500ca00e1109084400d90303c04035140c85d141c0030340461500083d01e018186519503000b0224240c071040010600c0302d21120181c080301c0720b9403040006601b000c84005130807202450704038001625030359900040c0c55041c001c0d1640c040a0244504100014160758010304a40d4044d03030b0b071080040d480c04502248007403180030182c04224180004002100503c005560080f25120060700b05541c2c0c2d901c142c94600010300f002c0c056001070040000f640340d040808000c441d021070007003a0390516140041c0121134807600907405609141c4910450780c4041080300d140000e19044e5564a60b030f40c5c60654001c00d40d20020500c6052003044070300 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 61773150 1250 61771900 61771909
    0x19030b06040609050607061d010b0406052b170f03040b01120b0a091509120206070306140904021c0804060e01020a020a060e150d020c100603170c10020414010e 70
    0x4007920b1071030703c071520010700b0031041000d903810540f0b04440c0c1a8480d22846a040080f0800c1710040b081d103400420b030607101c041080165200c03504080c1c010031650b0b00c05200c540d620429000e01c00300d812404a01105641445081403c4c51031440d0f940000c0011208c106041c641b0003188102e0141c103080c0d4890b42c0b0b41c3e0a03412601703c1018041c14500c205030110b41c0d9441c5540c84910360a2007003c402105000031403041065540700d50059455610900003c0b8210390144001984020b00303150800c0703000c1c2416100a0058012602035014a994000103400c42d00c0c0d95188541050a605100c1c0c100c21040c030b054500341c0d000d80070340000108801400f41e150350000a03039061040e401841441d5550400c0b008844020100d1101a413286202d808540601c206200401e6003000d030203005640e4a00e07a0104a00c2d00d1004004a0300035450103404001003000200c50303500c40518010120740e0351001202041c548600805200e008030b1002400140c1213107200301420181c142a2245088d0b84919170400 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 61774400 1250 61773150 61773157
    0x20d090e0105030604021c0f08070308070314011707080303010b03041e0b0f06030109020919060b030411060703050f030a090b0702010506030a03032004090f0b030a050705060306040605030319030b06 87
    0xb1a003590000c40450014600b05440020301c0c104032032204455082600e03401c5100e50b9041080e01c0340e010005000d801d25510a1120794054440c0c2010701c00a20455131110100405118007a032010710b45218220307484050041100401552007101e0300c95861741003c0c04540d005850484400718004000c016142d03130b5071791084110740c115200040c25a25100c24403211000241441c0d811f5590312007841c0140d807000c07145400303a0b4068480500d00e004c010040012a450741d00aa07c0e00e0006204100000310b192880380200702042c3c80154803005140b40c1a80d9500a4404107200301c03401108000e0010b402d584080301c114020b05480d469074071210740c181c2c220b6200f43c440700c0d0550000b86491020034003030f402080c00007204116201c04c50a803410a800c40ea042034000a000b03640701c1d03814034040c20781401104228076045014002c40025951680e9480c00300c0e101d0180251f2011001a1060345c441e40002c00074900501640d540e0b96880102c00c506104904105010901c0d01c0342c100c5181c02c080096 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 61775650 1250 61774400 61774409
    0x10f05100504060806270603190b0a0f0213030f020418020f040e07080a0b180c011d030703060c02060601091413050c1b070807060f052d0a020d090e01 66
    0x400e441d1505140045501304401400550400340c0c41c4c0c0d99078000310f941071019031102903c0c2d0300b0a1290424400701070500640700380c107506080255140c0e00206020213612500101a40400500c010780d050034403010b80a0f03403803845105000150004240b0038482d000c446040d00c2100c0400020704400c0000c0051040b0400207504150781003040d0300700d800d040d40a00d0701c4020703540441d030029680b404060302d090b003944000c988403032402c409d2212411010f254a000c0c151018003a110010b03078900000c0032000074000b880d1034460019000d24030b54905200d640c02860f0842402d2181b041f801001940ea50001d44c0c1d0180002c06c1d4031000030f406424040c1d03120060100030040300540274021a004041c00028001d002c9524080061341200074800002d20040c4401102030105103151800c054101039a6610400a2100d00360307114400541c00382c121145d0441c00441c100f41c040d030324810700d4140301c00b40714040641100020007240c21a00052038400c1c825056664440646d1290080480140d0a02c10b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 61776900 1250 61775650 61775657
    0x30c08100e0312220b1008070b03010b0702090403090b0f030f06010c051b0402160c0509010902090901050d0302100603080c01200a05070318060804020103050f040c1a0f0c06010f0510 80
    0x4120604e070404000c0508004840303520b030841e842510b800c1d4495506862070b0301c071000b01103000c101081c01480000c2c01003072a84262404c5600d44002d0002034030802200a22075105000044d04160145015030003a00c14003449544801000780508144c0d4400c1d00c0407040512100005a559032041598061450b801005003400400101a10180b11048054964003940a00c0021103200c0c1c004510302c0520f020b924008045d40c0340c241485482141a000701c80004e004100284042d21a800c01c2e03030446800b80c0f00403100b0803060030200d00b000c8124100300303c290f0900900000703005140e00a403512444560007004042c41911841c64607000000d40e500082d0001d00004804a0080015001d12802401c0013407982e40e43d50b203401e499150541003100420b000030244410740d689881380e41d41c040c008004224460903c9c1c0c8588010003001c0c070581c0108118003c1c0301590b14002c80035200310085611030b89032550300092056407110024024001083c2e1035038000545490515450700081c2070300d46 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 61778150 1250 61776900 61776937
    0xf0a0c050f031e030903030c030a0e0306070c1b0302120615060406081902070203100501090b0904021f021905010e0d0207030b01091104050a09020a03110a050a08040c030c08100e03 79
    0x70341c07030b42e03d40314142c242c16450000b0b210584a640b014001410f20f001c0071009103039240a6030b08080c0000119480c00c1d802540100104007000740c20111042d4680c0e003003000c042240700214841c0c00f007040107800094110030003208001c010700000a406e4003901002041c40700441140302440b48600842c03080c000018028000304a400c18030403010904042c08200262038654103802081c0345c003015449081c1d88690311001008076450787e1007101c400b440c2c2141d040e01c071402e20760009180c81d41080070b12284c440b0aa070001010394001c01401d1441d003440c0f880c0c80b03142051402c01d18003e14450002c0c40482c080d03524407990242c40800d006003642c0c0d10806482182e400c069842008184017030300b40344c0d0442c00300000b05003a0343d202c51140c02070109620159a40d81c0144004050303c11005060440c20014004100368903008820384440c885245064010340e6164140496858a00c0e800900140e00300c000100e200c28001c00d0b108811581d0600a019150324044116500e10410480b410742c3d03940744 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 61779400 1250 61778150 61778173
    0xa020a0f030f090803010f0801051f0509100e1806011a04030308070509041104151706010e0f0604090c020d080402011e120f1b050c12030c0403050f0a0c050f03 70
    0x207501c1100e410070811000160f21400741c0d42d0414550003a00111110b401c036140c2009000c809004503640000d0010704107112081d08210a41c0c0c00c2040c0c029107100f0010a000250008200e0b0b005d00014807030082110558241b01142c540c850214500140e580e005d10400421210b040048200050140d9000700c0c1c0fa2900c0c42e1030450301c451024042000b000b00803c48911155107900412640003251222150350303030700c0c2601082d2010300c05482c08003030011003e4000c1c8448488401c0310791042081c20802c40e2200700c00005051140c040c400c02d584030a0114010803207155540c0000421038264084400611079094103459841080350000c2c0080c400100c50400401c01500c00f800c0e0388118185028640e0704d801c406403ea400e20b40c90441129656071050b088003c0c060b0703255003070403c1800c1480c0362400c0718070055142c0943c007a0030b910b1400000082401041c5480403a0000d54006098030009901502c501c1d48984620501b039600b00d805080c04945847c1001c1b81c0148404002c0050440c038051 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 61780650 1250 61779400 61779407
    0xf020c15060a0b0f1b070e0f0906040605060d05010f06050406050a030c05010f030f051602061608010b0c031201030501020a0311030c03040f0201020304051009090e0f030403060213030c090209090a020a0f 89
    0x71307001c014030a54180401c2042c004000c0c852204454984060a0628200340005040c58401881c0f0040c00d541070060082004002c00d2607500300c3c1d0000b10115a607642c036400310707101221040004200e58a401b00d110710103061030b0b0200742591070450301802000c3e61201080f5001c0d819002c00f9043c010038800800c019030007280305e11f4041d8007030b050100c0e001c517080410000b12042114100c000604549484005a83c148030566004d200503890a040c0e60003c80010861401401460001d010000b00242c59140400035540b0f60340600c070225000d0b40c1c42e0300e03109000c5c0d000082d50300003081c1000b40280e072a00285054a1042422030f094a0a641c1c80303450ba10016001c94500360705500040002251503254400c01010810ba16280c102d1158500a60007040300d40015030385000340c0100c4400121500e000c0100c40460790002030260302c804140000c10203021283d800100000d00031840002d10240380c1e006480703419400c503540b0010b0313075403002003000340e22407811100002801c200742c00d83c440c0e00 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 61781900 1250 61780650 61780657
    0x111212070c05090f040c0501021c08090307060207030504090b01030b1305070e0a0807030209090d0206070f020312070c0318030201020c0d0c0302030307141612060905010f0f020c15060a0b 82
    0x6840030001155465000c282d103500161004600e080b1300404000500801d001000000c100a00c003c08000303013052010500800d056000760b04100302100411300c0b1140400541c1c040c150844801c65440c11540f0300a00141d00a201d200400b40c2081e940524641c0640300d510840c1c00d000c2c140d00000c0c0241e102e00c2000b000300408500522041c103400f01003e445192105018144110052880714118010004009001000401c89604c08084258819404940c0d90740002140c2030140d03000c0701450060317085001c6e05010314205d0b0503080812a030203920180e02c0790040d002c5d840e0740601d2044448503402030085400041d0150307102d40254042c038140a140810315a009196540d100d584070f030300003401c5910111003039583c4501c0d510300382504007051140c5c0c9141c41c0c0054400c418185080010032a600084c60007030089030341c1d5080102030040a40100d00b003c1c6021108200807080310541100035004559150b07520708c11100d001c68120051003566001c0c860040903055100d24041c0343c00e00c0741e031 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 61783150 1250 61781900 61781903
    0x60c0c14010507050d0e03013e07120315060c0b0106181809030801050a0602060f0711010c02150c04060804330f18083901050411121207 60
    0xc08103c3c95010803070500400c0c0d8407001582e80d034407102009070105401e4a404078044861590b40c0403902c400c41030342100b6202070030700c1140d807404018450800c4400501034510f024006069405840300100d90540c0410314090601d41e1908245443e0001204d0340c00400c0f4004109032030700001800558040c00f602034182d0410f01c00703841450385944910901c4011045201c4260b83c40e11840010580c104240c02c1c09880169403002c00c0c6490035078001d594000281403154a0b500c107802244c0d09900c81c02014200c1c0705100003d000c00c40c40f40800035500c1c03040207200010700000c2c002144511101000726000c40703c0c40c3e610380e0303400c0d21981c40f104c2140c40d01d240240d03514031201c48a0911a414000a460104000140003401c810300210300ca055030303204030108209105154041d0b001500f42c03415901003070003113030380030303401c150070610841400364641c9003240405d0b0828214810254150007a520031380c400d0103a900c100c0b181c07205002c500405820207030100c0d0841c5a4800d26012282e0140c10841d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 61784400 1250 61783150 61783157
    0x910020c0309090c0d0603080c01050108010c0c0605041b030b0603060a05061005090a0e070807020c0301020304030f11010e0f011a0f09070804030509060a050d0e0610090c03270b01060c0c1401 84
    0xd00560740301c41100c80f281d0040701c10023000b050001d4442401c1c032816004011802c02840340581c0742e100100b810040c4000180384690b1040820b0502800d4040703400c0c0400c403071034282c000301e840b0f0070f0420101c174084400038031900c1054001000140b460150500410024201d5204041102c07801d88403504010307041508140ca800c00010326040180e007241c011101600d510300d490402c090024109440821070034020707030040043c48002688105401581515442c0050709000c120310460b0261000c4081d80c20a841442509055010194056802c0c1c451400c034110390040311200b80051500c00c0302415138448401e1000407015801101400d070b02610030302d07003140f4107130760440016529002204800002030b400b0602c00b0500d401f610030b5407059505000240410b15005c02c01c5819034209004440600d62036200c15184203010360060403829003400c178040141c1f200724006240b00014218281d689403d880000130340b841c00342d116000d065402040c0700c64118205042c00100c2d080050006040 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 61785650 1250 61784400 61784407
    0x6070f0e0301060e040b010803070c0b03060103090b0405060105040e0715050a050408010c050301030c081f020c01020c0102031f060819181203140606040b040510091d0910020c0309090c 81
    0x303035803c0c812800940000c0324200020b0805050104c0c86000c140c21441d141e41c400c011036400325000074050340480c0e41c801000d80d070342e56500004801400d1568002011580ea600a0104005021841c03d050380d06c20340d010003014165a05051751546035100302a5100307401d001c500380d421701c143e0041910785540d040031032070260380d00c1000f0b0031a16104002ca0014030040014410041c038104c001740200210001060807403042c40401d4036481500c20000912680007808031400482074041d1102140c0c1407000b152685043d10300c0501a96513060303645506034084d4008500640141c103314000da90115041c214148211113540040c025900c05000703428205c81d6500001c5e5440b0780d101050300302d5503030104051030131018001265a0141c90f6500c80e41c8180014002601c5990a40b82103803011103561990b070780112020b4526068540242c002400800c00380502c10156498150040c12100102c801c0125040510030403030003005050380e11034008100b07030340c06c03441c2c1180c009800014901d0300519 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 61786900 1250 61785650 61785677
    0x1202040b04030b280c0e18070806132901110a29011202010306090c0203120c0408030f070308090601030807060b030106080105150405011202090c031009110c16030506070f 75
    0x14618401c0607400104e5031101c510800d810350240c5040c440d6002502c1c0903403004c26a00311078448440c01040141000207100000d001960750720981d081e04448d011003000181031203172811840c00000002100d8181032800d6140583d40b15524400c144240c00c4050151000306039100c81c1c00c4046a1005c240d2065070202075242581c018a02c05d001744081e000007800048544005400e4406030340c0a00d101600c0d0011110105401004503030702c646480000c420b01d41c0e1901148142400760b41c00680d9180b102003000d00e0110000401031218074029100c682c440d550f1418610b50310b600900005280a105100c2000096000e401c27404415100a0001c5031170303902c4441c400c1c00c50301c080326101c040300308200c81030881e800c3c1407140c075002d0711003040b580304807541c02d2700490740d90507002e014191206400400560782200490704e100107803440404c00d01181d030141c81440000d0b08010400c00c01401142d0741f40340f285c82444281000c4980c08000b426180d5a8a64240c4011032290004001d22100420a10 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 61788150 1250 61786900 61786951
    0x110703021305060906030111030a090206040e10030b15030304060521040b1806060303030705030601090b04090203010608010b071101050903120d0c0201060b0a020c0d29071202040b04030b 82
    0x50041c020010008582c9408810400344102c0500b006010780d01d080101c6410000d500200c0e98410726800010030000980d1005c0741c55031146501100c80000c10005109031240c80c40c0c4e05000700c86c02091000459100d17440852041110750454607407640c420802000840c1c025070161503241c01d0641312011100780c100844e07405110896003124080640d40800a45200c61b0500c07104040c001e400038074141c504013003c6681c0307220180c10901400004000280740d84c1c480c0e41e1240140140707940305903c039076642100601a400a001c0c16001c0b40020340080b408541071016a0f41a58010803450200001071b4010758165010082c565058003070025554040b0320050000c04403100c42500c001601080e084000307007110110f40120b8800501003040c829201d50000b102d1b0440c000031110070a58800f24540106550700301070310360a0301c044d21110420a0720074164200d00c1005603895450503030300403500b41001c921aa009013502424244002e00105104a80441c0d000d010f6000c00c8040104c3c2d2640e21 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 61789400 1250 61788150 61788169
    0x5090a050a0b1c031404170c0111030403020a170c0d03030e0c0111030306041d0d0c0203100b0a09020a0e1804031d010c1e0807050a060f06050f12010b0a080706020c0a080d11070302 79
    0x1187c2c2a40b104009621550f07110080314200400e00c40a14140b0303040d80e00094090010340b1a56148201c03909100c105042d05100070401200014840c40000803140b401134050617407101954050300070740c0035074107041d401044040c141300e412001452669546200b044000c1101e1080c0d46001611100d03404003070081040300000984150f22414102c1b602881014a40014020328030000790070604904480c0e1940604101560031611003d40c03a4210010115165070301c42c001c1d66406a109102400105880a1090b004074082d558040c00c645c01c0c4007403405001c503407500460001d000b01e500030000c68903108030410114608008206a1071813501c038a0410b410401c02512650812003070001004400e10a007100440194424042e00d0b00e8040012200711205e0a91030007006958040024035400794010310b4007190041c0f056800f40d40301e6000950f11456030050202500c135003a11582d2501d41400c2240c212004a4002e0101d03048110003103580aa418114400510034102c000c00141c0d52072022 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 61790650 1250 61789400 61789439
    0x20d141e0706091b08070803040e04031407021806040b040c0813050a0b0405030307080709080a1707150b0406140f011421150103090c0311060405090a050a0b1c031404 73
    0x8810708035040100086c180b2040d5031016145a004001c108400300f910b01200b94403e4043c24410418046160307041e00a02c0782040096000b126403400b1100140c602c1c6a00740201750a5030100107074004403043c40126042284d154010134120400030700900303a221108203195229000b95450720543e0369811101540c00c0e6003c4400f03800c08000c1224580d8010700042d404080c3d8074042504620700302005450300011080070704514070008a10341c5002c120700403943c40d00d43c000c0039500d11040c460307144001018118903c510641c14080000380d000d0601c441c1ca4081d050080500304424500b100544030080c1c0d40f202e1710400ca60a002c00d444088000b426840c140f180c03480c2803002454059004100119841e0803a07043c035244c07081c02008111043d50984c1526440044241c1d0b0454100000b0100d01407544029030200001c010041c4401164020354000c0c0f5400c01d007800401c0404040100d995000b4008034412b44850441001180c0711750003940050214a00705d030710f450741398154260011009072a = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 61791900 1250 61790650 61790693
    0x601080a05012301031506080307030c0203010c14030109050403090314010f0c080906070f03060503030c0a0507060c150203071e0309020f010327170a020d141e070609 73
    0x3480320a00c6400c0c09580c0b070041c6a80001003550100745003c8031001c1c0b06000180c00c002404400a4816245600c0340c7c004e000c100c0c0442e034662169180c018540746c0300c080b080b03000703500349260039060038010a0b18031111403a080f020740c190380c02c00c540701d401840c0c02172094040214040c1b0004c042100104a4220b03c0d150000105000f401c001c00d010031740b1072041c1c4150402407880104401d200c0d0124403143c0000e118500201003025101c0c0880190501380c0155501d40000600315520900c0010340c031120900c41c0b4265403607142c0e202c9066403001c04444003e4205188215a0301e5007443d981d009551150440c100700078052504c00740100c035841014503810100f641c030322007031066180c842c940c200411024a0b090001d240c49000907032290440e400c07240aa01c429444800400c00c00e40d0740580c240b19802c034485e8541210721002907a8015480144010034410918182c01d9030220049640e40c24444a0503407030020007005030507103079000c000d0a44500c0d95070800c040c0050540b5100d81140e003001c04 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 61793150 1250 61791900 61791913
    0xd08150d0f0206120a14070f03150b0f280c14070b0d0e060f06031b060706050705091504031e03030b040c110d020a021c0201050d060905070906020105070903060e0f060108 75
    0x1002d00d02207620046c00d2000325501d000c00c06c50f140780d00c50001c0d0164901031401261242150400d10519041d9401800700000e000c18000182e854038005446401c0244003244655051301c03401ca0303001c1d0150130b2048000f580201050020505e03d045540d101391101c1304458460307a45091200c0c69420030609d00c0d140580b110202c10020030200821034000740c1d1046250031608090000a41d2082801031008900041d00d004221503542c06c2d0075941a00d40000303041c016403901c0c80000303005520410840703101d901c0500495554880013415a020b0f250700003802c8a160b404500000c0800c428014112b08154071080901490388482c0584001e603643d130f481780d41303403a2460007581d8240480a2039240031940701c1103128001da9244000c0458010728100303040c14003219400121080c1c0b1416480300d03146814820001000d000c50b5002900c5621a40d849200b00e036106c0d40102e00383d49040c0c071110000b403d07440061010a050b5442055030410b400300710760749007030b004130741c9810310341c091703201c19400d80028 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 61794400 1250 61793150 61793161
    0x30702010c110d200c1207030201090f0f03151b09090c03090b04111f0e030d03050103200402040504060b180607050706051c0504050d020d08150d0f020612 68
    0x1c100c01c07540c420307081d014012954202d40f00801c80e041502c00c89400c0d0a00e81406042d0007402d20521034000d6016004984114040c072229980304a244402c9000544a01000441840c0c2d40c10134800d0b58454520a100f280ca99118401c100d80504586400150394980882004280c59401c5208911039200c0c4041c0c18509807510f0126002c6c000c100303003494140007807100041c800a10060b409a4800713480e040c6040a50301084045420020b100c0c030303904658111b0005140c0100c007000c4004000c500704c45c1ea56100101c00c4007560020300c00201401c11813548603008200b455030b11100c40340c4c00340005003455510000282503940c1540300c0a01400001100ba4090b14040f200542444d801d886051420910341c0d1a0366642d20b00d40328100400c0b0001c904000c81609074958a0b4064004900c14801814242407560711741803100c400304090f10074a07800185941c055a046031003104006d22180c0550485c0d014808000c000c10710480c0d00e030110b03808030001650743d8000b4040c100200c2e07000b0364103494072 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 61795650 1250 61794400 61794407
    0xe0603010e0417130501350103050616051206010c021509010806030102040317030c16110102060a151e0308030a0603120201110d020f07060f0b010906032a02030c03030702010c 77
    0x5000c1d1010b000e803820441046040100001134046800038601600c821074128518801c2079038070440303403260b074200d0200c651031081d800c0b103180c1c103980c060800d8607000d80305c0001000c410507030340600e5000700e80d00b40400e48a031a52010385c0f03039001c041030411102c1e0000543c001f4a54032078210031101d00d6030000c0344904283d603000340da10740d22a40075002146050300311745420010406031ba0500a41c40c1000001521b1640340c04181c40d0740d444038104030384203d4458500352440c9046010514010300c101d42c0042c004104038003569030710500701c20015003040d0030900c2504d5101c000a01040c5542d02c00c1100000144500700214821010b42c8000518141107203000002044280d4148046a0412500000b0381088008031000d0011082c0010f90300d65500c15130102500815001411451400504031001c5009402c0700d000e0132000d0380c840c1c0900d030300c804050701264000c0d400c103145401600001d901016080b0401401c001171401107070b00303180d020000d25195500464043e00107075164000702805940 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 61796900 1250 61795650 61795673
    0x21207050414012102130315050a0b01170609070c0b040b0106020601080d0206130303060302060c100501091404060908120c04030203120f1912090b0f090303061e010e0603010e04 78
    0x34241303480c880b509001000c600746802c0d04401000d1140c0c2c00203000381c2c030828500f46078005540c00100420182c202a20190041004942d40400e240c180840b6040740d6124615213401c900c0d8101240149480d0102404428400148004240316500800c01c000c900d440092521a80c032038910107020398103000c002410b04c8010782c4006102d074059404031031640e402056195100072030659040402c105c1c5e080440103030000b0350020b50450300c00134141045000100340310002c0002c074102441180d9075560814100c03100c1d15228110288403c010800088413a00140c00980c0030305401030503d00d00c911610914441542c00c1004100000f40800850a0900903541002c410409060406494035140d803841c1c401d20b94a048c05146032000140014083c1c03c114600484400007003248a00c14600040044010342e440da0294510b0700000b03000020000480c0c0c49a40040e1064503005080c052041c04031400b40c0000341400903403180a500c40d00d4a202440c002c7c80d281c4002d581d20705081c2004149900c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 61798150 1250 61796900 61796939
    0xe061201020304052a0a06030b010306050a060f1202070819020c0a0f03020105030402010c0501020a020106240507030810050306070305061215010b07060b040204090c0801080304050a090c030212070504 88
    0x740180108008120003007040030420710840340c25420b070000e0021400c0f041e21029055a4020210000403441542c0345d400103428602c2a00c00f000029192410403403032800500c20305000415003440f44804510820070401211004030000d41013101c1942d490380306401555005100011100c4441e80942d81080005214031050b50000c0520f41480e83c20034100c3e000d0b0002905100b0000301040c2103910504045442e183c001c0000c548074602020001e020780b04910944c1e11050f030043c01124440c2c43d0450040c20b01c6659212035203400119036054460150040142e070514050000c00030b800d0700e0501c0b13854810a607541e030000741860701c0400c01c04445022442c3c00441d600c140c417420b0041c801d4082240c10344501f5103105071180c03444d2a10030058070181c0b000c40e4005001013000110714415400c0b03001c01d41826200c5a0741c5d680c0f10028190740c0e0141c0e20502e54440309202e000c029000e80c0394004152580c541c0f8002d85000e6480722054001c0c1801e90301c500014500050802c0700c0c00d40081c5511000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 61799400 1250 61798150 61798153
    0x1020d03140402040902010c0b15010f0311040909150501060201020d060b070c0519030614010501090611030307030f020f0a120b03010b031b01030e060a090b070807120e12040e0612 79
    0x7441600316000c14100140024015540e0b0480c0c0b034150381c056904824003a501004003607180c6400300d00901c2c800c0310300140134007040804405004d10fa000380680202c40041e5902039041518158444c0e0140c120000183e4a00c003003402c0706002d0a11a0140901070f04c45500090790701c2d16420100400c507a941d5100201618041c041000040d8120b8415404c68000710f90070505240c40d00305c40100b03440d095100400d0103140c4007615074100301400e2039904035003091321200c0e04d8a0ba205402d031340049941d40740e41e500da081040011a61802540840b9110342a984018180303004491001103070740c842c25405e40070801000f403031b0004d0701c0e05000308580d4050070340080c0900f00f103460100c0d030780316111015404000c02910000c1c1060f4481e50000d00f02c9001202102d8141c1407180301000200042c0070103495038400d0700c0028540c14050507095000d09020f0350391451100b81410410010928514904a2405840803081c550343e02c600240024108042540c5401d083c1901000a101d80003001980303035 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 61800650 1250 61799400 61799411
    0x10906050a05031f0902040f1403060702071206021b03031603060f090b06090607030f080f0408040b130b18030115050a150e03010504060207060c080402090a1d0a050c01020d03 77
    0x500b98004250b942021680a441c07850032184142200103450359040381d503110307201050004005442c425010116000440305030501c0c0c028034103041d2600c9003201c103800583c7c021101040142703038844071518540e000720030040c180107500007140c17241a100c9010186603440031081c0824410b5040316144100a54202080b007980b42000340c0790080e0042c0718001c5c00c03c0d680c1c196420541c40d900115100664002c00480e910310b602d14003e011301d10301c0060a00044d80c0d4000140c03540d41c030300494030300490b048090541068940380d081090741d409490300c403111009d40c080c0010801c1640f006400f80e41035034001e024400c91610241030850341c016806241d25001503508000e26150b441c0040705456a8450201c100c480c00403090b0b80b8010000011a059868282000f0a2080582c050101a4440c2e481806204001c28088840740300941c1c01940c00610000490080d614990090603400c810566100ca4a1810550141403144542c010349982d040928071103031382c1da41405680302c2c006003800c08025 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 61801900 1250 61800650 61800667
    0x191a0a061d040b130501060504020f1c05150904050312010b040518060a06050a020f0a0308180a120807021f0501170303010b04060318060f09020f040e0a0f0c0b030a02040501090605 79
    0x2040f10000e030283d010400c0316040c590038081d0030341003c405014060401e55640d2000c2d0042c540c540d104d078000c91154584012036100e10400f9009450141c854820511034850444c0108440c0a402030400c8580703200c100a10348949104494081c002c060310440c064807186000f040c0071550807403110dc03010894095040140d690f072015105004c0c0e802d140340107901d500d4803a0050b0301d004403001c01640b040c483c41039080c040507840195148500000d032210001500d4001d104c0c0d0360740c44001001040d44d143c610107500340c2407140e1151580404948120384154a05200d0741c1c00441d84c11040800d21521040144040418414181d02641100c0c1c01107146625246001d5180c0c040d038010782c0308042d102c842d1001d000c400c1c10541100113800034401c02910745101030081c000c0c0031909040340076401d6504e4502084c40c0070320a03480040b040c1806040200c4040d9540840b51503840e0049401d01400040841d50600001c05580f03c1d41c0444401039a8a0400c00050700940c2a03910140401c9007c010a95 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 61803150 1250 61801900 61801913
    0x614010303020c040905120d0213170c040504020105161104090819020601030c09021305040507170903040b040306050a090b040818310b03100903090512191a0a061d04 73
    0x2c1f02c02000300211911007081108501c06031040c62003440e03200f08049400300d072411608400c9548402004110f0301243d001c082440190b40003154040d02198061040f00042400c503500c40f512503100304008004601c159000500305ca8140805031201000416030103e25a1020b00034200c5220500080c100c0358950341c1c0b10380450945004000d4140e07004900c0886140e840b44411000e40390080081c4107a1a1084005103c214104110003c500400c0e02140100350040201c0c2d0569510321001807520b0300b141c0f140c4010f40740c06800b1b80c141030342e2a03112a001c50443e8810b0b9014521640c290b550702c0398003443c20340750000b040b100184503540c400c1480403d8000044100b45443c02e0129456107028072042c2d210003010022403150b0980102c89940b0b04500c41030780206007181c800d4951004c00b5484001384606140d0b14008400aa4000402884031b0103141510403865441750303c0c10624a00201040c070601e5800b511009080da4070f403074080c0040081c0c800481008a105112007031300740f40945916 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 61804400 1250 61803150 61803163
    0x311070e04080f040504090b060429011103040902070605040b070201061d04031116080709020c0304030f0c0b0408030409050c0307082a0304050303060a120b060906010c0614010303020c040905 84
    0x100b507410000748001c0a540090b0030b44005140081c42005402c020781482418a942210034a110740c0c40d000c9540304507200e142404101030701031040502552082001511a603c0314a40740042d44014000041c4c141803900003004041d1090001082e103060626010b050083c0c06002c49080d0f9050110a01889514414140c0e00785501034881101da00c803810240da041107040161000d034016400042d1807240c001d1004021180000c0441e07130760b265140150000c90040820810280d0030400040000c0b1752900300d00000300b070042142580103036582d80d83e02616441030f4010351f02900042010040c42c08184992540400e100320b290b031841c03501c1c0400904120000306121502d14600c03483c0c0d40b90544840c54440880d0f2041d0145030340381014200203540b03070001c640d0148a4094008081100100e001042108543c17043e5400b5041e120f00c1c0c100201c001f401060030303040050b09540d04001c102d003402510206005044046d140b5411030400a080c60404a0818012410813003010001480081c21 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 61805650 1250 61804400 61804403
    0x9050d0f0203180402040806090604020a090b010e090a060509040c0305060709060c020d0606050613030605060102030a020a1202010f06060c03020c0618060c1002071208010f06200a1e0311070e04 85
    0x508020f4040000c0c00074011900101d9141c45130804000003958000b03042801107001303e60200300305640354070141c15990310641c4c660000d80003900c010444d061180c00150050540d0602141080d00d440105c0c0d400007003140c0c20b440701071301294100309028080c480250806403078580109010b042a102070f28041032036400a000d0b441e0408846c0a201456000b00003a00c0028092580d07079001843d031854117005400107031070321890540450302039070001040364140009500a8410b003041ca0b11584200d00c486c000401c00d6540b607000031341101c41c2c24401c030006030141d501c90301111000c0c0d0070000d151080c4030032510b020342c0080007013907140e40c080c04c1072083c041c0080701c4031075881e024006101c1c200048081004117250003c96442c08120b55840550030241d00b0fa650800a684c1e0344664015020b420303c0340344081540c0100b0030760492003c540c0025264a04001c8a01803c025610180c040140e00f01e030b001d406110070148400c1540c401c3c0f180015854460040000c6401c1600c200c00b241400b410 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 61806900 1250 61805650 61805677
    0x403020607020103061802090f060a1b0606080a150b10200109060608010204061209020607030f0c0515071107030803060d0c08060c0a030b030615060c1e0109050d0f0203 74
    0xc0c400704680c880d4116001038004107010320034548041301070101942116801d54030444840307010100506003041960741681e401e50300c50000c0080f900d4507140d100386002d02517400b03503164580400c4011007000200200e51141d00ca41034101c079290000001ca803648009144100c0d121003051011381c1c0d000440c410380e46920010000c0400c1c101c9642801003049440081c4001c1c01c003500040e0240040d0b0141c0121805503c500c10125a0340a188086450600000b98004814400000424402c045c8808035498608210000005503200c4074600220300094540340c060b44c0c010409083d42c800803c418000780c0e41c00030600340f411a42d40c0819404028400c2e8020443c000c4220b041c400403003640d2000386010010780390181400d0a03204120f40c0051060400b06c0d061092000180c20001203c502c038480c80220051090388031010050f4a80c040200118688509000b80f42000c4040507070b40c023586070341c42c000142266589031160410400c03c12000911000505800704550007100b21440201e8504 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 61808150 1250 61806900 61806907
    0xa0b0d320105130203060906010e0c070206070605091b0a050904080f16030c0b07110a03080703020f0c010b03060c041a0307030908030f100b0a02031210090c0c14010605010504030206 80
    0x4032400e190311414040206507600380000d0080107000441858240340c002e8055a42982d00c1c1c0b4140ca540746030038824982d6411400e00001e103c100c540f070142078000d02c02400f0b546007101946078281641c03c140e40600b029040301da01103000055081450523422815281c01d1805403a2100240d2100c100401c0588148400601000505070000807100d0307006c5281c0b4102515145401d0090461b51001c500b200c904d0b0781100852650b40c0a0707810980c815088000500c58103401e0750301285c0440015210205040d020300a031406040c2d144044c00c08041c05d0300000580802e000105807504c140604040203491040100384143c61811001400d985910400542e803519240300480007022900c0c8081d0000d0008001d200c01c1d07502170524503018080c6031150700303801500c0316000b035018070132920b40c40c0c0503130701c10098040e641c490030344055400041c5100c0b00540075900d9422031705482880c1c030308000185000f01c0d41810030680c50781000255903d10000c014890410001030080d104034000030380300340800b0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 61809400 1250 61808150 61808213
    0x6092301061d13120c03080a110406050903010b09130605130b041b0906030305030601121104091a060a080405120316210e060702010b150d0b030703050111030a0b0d 72
    0x4800040c002503225180d880e00c0561381c80d005001c508004d804a00041a07000418084a01c5004149842101e07034400e510703003880c3c020f00743d0b5036a0147c5581c44c0c045d501d44440c1800c0766603020280c0d126502001e400e084c00151442d05004071240100048080504c07031590002140d840e00c94035501543c00014600182103454808080301000c5d4042c80b0b85604180c4040101580040550701521081c3c0314000d44800090000301a9000000c040f02c2c4540240401c1094220941201c00801100c1d43c3c1c404404d8240c101140003503114100318000301d25900188400c014042140040d028540d81c5083d081d17041c408251a00034102c40c4044080045400200ca8507640d2500e0188402c03442c102c08000001c420044903888000880b04103025503c0d11842100d40e040c62340f00c4e03801d20b0b009486454a0402c0503442c07400100659440031b90180710320080880012000d1095052000304818100c2d00c07880c0a0042c042640e40c1c4008807400f07100740c20740c41d4001440300d04040c41580600040f80c000b91245 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 61810650 1250 61809400 61809421
    0x307080313050a0f060b15030f0a0c03020d0204091b05030c030106030f02091c03090611030d05090c031212010f03020d0f05011506080a0e03280c06092301061d 70
    0xf11001608804035104032104100c100c0d07003c442d07560b105a0342c00851401d4020300c4009030100b180d0b00203802045400081c80d00132070342c1c45082125102d081c010b0511020790803810803078000e600a13162443e9211144c5c0480c81c08800c01580345c51161818900d54a03020301618024001071140f42c0c281a02d030748004001c0c0b002a0141e448070040130780304040e80c0307195100c0080210310545041c0d0114103c914042045440f6081c10500d03280408002d514068400031010000c0c08014041c4481c2e0180a015036070a0f42e003804030306042d4204000c2c0300c2e25002c4c5110600c074207010691140611004c8200d0420050b00c4100c000080560450105103640c1c0e41030406038050180000c190740c4d061500c480100f90710b500400c50601070494410100a150403081180d03642e489450312441d030890041d40e1a1101000ca038480aa9012251410002400c025900d0000f0780d000752004a81c0c0d80c1d01e0241d48201001d0041d00005000c20f16030081c40042d142c071030071041c059100b04001c55103401d81d030005aa290311 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 61811900 1250 61810650 61810663
    0x60f18010c200405090d09030201110312010320030d0905012105010602030c010f0204080a080a0504031b1e0303080604020f090d050c090a0516030507030b0307090b0111030708031305 80
    0xc120155440d40604904101215600c07441c0b000e2003945048041022202d0000700110021040d442d000d201c14115001507031000755131288880c05e0f100400190301101d1a125040780214402c01c000040c1030040c00401044440d1500aa07020394450381c01c1400e00c550007051078003102d00a0078000c043c156002d941c0d039a8900500304400049050000020720780741d00100501d9021200d07402084041000d4150000b613102d40c0c8903600050307001203141800324903810003c2000d8150303810028649030360307991110404890703800700602d24400100d04010f540c941003a10b4620f640e103013a210300102e007159400f500e008400350150340619030100324180c140c06200d00326024400d0080c608070307420805190a0703980d00c2580900718000e141c02004911207101c07a00849006810404d00b07040403550494049008060041001c0101916110202010b490600814000d00326821003c40c01e840000005481e6460580d1719040302e50040059a0201d0414000c0d2500321074481e2182034251380b82e040240c94101e = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 61813150 1250 61811900 61811903
    0x604060e0319031101060605070503030406050c1209071805160e030106050d0b061c030207030f0c09051006110c010507120207050604090f050606040602060402010c021c080409050105060f18010c 85
    0x2142000810034981c1140104e016000d4400003071100c1903d4100459050003400c0000303003554410300100380010055000f15a000b80c000490034100040c1140d5584140801c0d202402c10b0741043c5c00601c00c40d8016081c41004a0f82d141c41440a810b002c036143d1100b91b029103a076000c000504c21210034036682900f00000400f80100082c0011903181041c0c5144082a1401441151424000c40c0f0700260010940140c0f41c054014104446c5142c8400650383d5001c1401c482e8649040c0000c95184110b11402e40150f580d41074411a0300c4c1007030b03400303420000d410030013a6069000904e0705185a034441c0884110b00c1d4410040031194103415401c0c0d14080715a0815548a00080341c08118403a142d80081e80b0390840f104240090341302c0320144010761040380580c1d80141c004500003000f41d4000c40340c076489a4400f0300960009080c1c80f42e200301c400700320038045407a00390004080014070084c6c014a405001d0490780640750a090360000c00452241070351880740e4070b0098080740c0035a805045c4101145 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 61814400 1250 61813150 61813183
    0x321090909031c060f0909020102060f070306030b0a09060e190f0206070803090303041104060b030a0203040c0e07020c090f1e040312051e0a0c0509060903070504020c060906070e0604060e03 83
    0xc441c1c43e9010030180031a0301914040b920f035040300107042c4456019200c00581c041c1c0207403900e0b031036a24107032052140040c0020107240c0c4680000002640400640d8426000001d0000c3c040d011854241e0580d0300c0d60b0b550301c0715075001f840e2054010107a0750031195840e41c48912610790790030520105016005400c005480c0a05c0402040240c1c071000c001944128403451590708084604c4040000701c1307045014415900005000040004c3e809070300a5822a004020803c0115a00d0961024114048800a0044c0c009a40340301680c14800081500880d0350700c2104030034230304001e001d100c090b0a120444800ca45000115044c14012818400e109001550500681c68060009062940c494000c510f013100c1c03640004403280203500c564144090280e59031442e03c40000b007007042a410034440c69138140200e101c0060540d4a034030003041c401c956a80070740051300e0861082c600302080213200105004250707a03581410350340e050480d000e640042c2400717101405030001107882c00714800c000e080384 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 61815650 1250 61814400 61814437
    0x102010f0c111504030503060402090402090307080c18150402090607050727021206060c150f04020301050606070f0305130e07090e01050301090c0902160c090b032109090903 76
    0x7040e070003006400420120303070894411011110107441425000c07074000c1e0000e00c040c404240c0a00d00b5400822180c000280f015052030b103424000382c200545603015031143c2c0d20a076098501410f12610000b406500c035200a0110f18109040703442400003001d455105a90002c4d83d500150780d140c059802958104007101d081e59110442e15020080282c40d000f085a9049800c0102482038002c648070700f0b01c02030070400b568444406106507904011264074a81c002c00010780b00c150f01d500400c038800c2d40c0c8065829040d0070540103040c01c460024008c10f004000401c1084046000e1070b01ca20255070741442c0050381d49041e0848081003011540003280e40084820500c4804c9034080c5040301500c060b840d95400c0e0780d23039131030030903007211000c2d03074020010302541c1c4040100000586c09044a035101038090030b030000f000c0c0d590001420f02034004280e82580c400c102e05640c04c04002030102481c4480b8403815520b8030415441103409000c040314840c005410009071040401d00a80c2c0181c1d801340c07032401030b = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 61816900 1250 61815650 61815671
    0x10309050304080d030b0405070c030809070801020d02130605030c1c110304080a0207080c0312030a06081e060c250302010603050d030608060906070f1808031c14040c0902090102010f 80
    0x4860845101c4480017906001c090a1107180c60320444d4005d8400c1c0d1500e074000c90316613406803440200102101500d0050301c00010742c00e1003c0c002030550401c0325000507aa202005140000b840460300b1050030030a0500404c01c0e4a6060740c125139041401c400011009401c0c441030801404121802050300b45000c8103010030041c202001d014120301e01e800b034468080d02e800440e6511280a10f080303074141e1243c1c0e0000311102200c002103801041c400804035003035448071911460440c0203a841820b8000c41c0c101c03d100c0d0501408295001407004603800d2a0810943c06a003810407e00c00201d00c80d01d80074024002c05000b50b00c03480095902c1010381e0720b401c01d1800041d0003819070344903003400360084200044901c040844c1513072041249403501840000910000c850010440350b002c0d1411000706400b00c1c1c219010800341c00700d20f0308070501646400300ca11009003079030000302484528400c4803090200103000d44117148142e45c0714010043c2c84441100c0101c0c00342500f885c1100d01a80345c400941c2 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 61818150 1250 61816900 61816903
    0xa020702100c0b060415180207020901080601060206010608060609010f030b040f050615041d18120301030c0506070201120c090308070b07020114070f140702030102190e0f091501030905030408 84
    0x440b5401800490040c0d922541440151060b4042d01c65560b505000180803406202c5803680d0f46580c000001410010103a000c40c031b204a00b0b8100c050381c5c0d8005001080740301d5040160301d01402003842c1104550034280c01140003805010b001034180182440304001107071090781b02c0108c20000a100b03100c4940200f840500400b41036410303a009003050200c0010a29140c01120101c0e0745007840201e18100c900107081d0b041d0005000303000c21800c06841d01030050001c115103100e0360700540c0c60301c0d41da5245140141c0d00d107a03036601ca54000c07101403011030b0148c0c1c1c01550025114000c0c840100d042c507043d1404035800005a00700801088000c1007100c240700c103a448803441108160004c004007103803081800c440c16812194038001540d0b007144050703440d00c1a080c003054081c2c440d420a0406043c0c4c0d0003c1d003603030480749482da0811004951200800e500c5000b21403440411f8541e0403100f5401008111522001802e81804401d00454410b81d64070a61160b49100e400006807901d842e110b0748482d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 61819400 1250 61818150 61818167
    0xd020c030a03050402010f0e0a05270103080c0115060e1207150c020f0402031b07020a030b09010905060601050901050d02032a0d0f061401080a15120201081e07080a02070210 76
    0x99000410a414001400723009046030300c00042c00034100e40f40c051403e01000000e07462024021641d12a503d4042d0389070181c0ca252a0203144181c1400b41c0318000c541c1c01a0859140c1080018075121418042002c40d8102c45819083c8d1001d5502d051191140f83d501480c0c04240d0b407044070418078070f0751845120340e0b0206076200100c0c402c413081ca26510280c010481a80002c0d140e031903030701040b500702c00d2140d4200d200a002041c405800b1110321566612190701000f82150121100d9440382200001c100341440415882002400c09504103c482c5c40020305500401825120056000010071002500c140c414009030780d0040c100703400381404404011803030704a04600010141418030324002c0d103925000c1d01058814404c95211003c1c0d00d4001100c4451020340070400c1c41d552492140e89080349162038501820403070402034071040707091000421060000700081075060f0241050350f01000d52444664104e0713031b14070705100d0540b5541c251000a2040c10b8000b98800c055614441c0c5403500103440 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 61820650 1250 61819400 61819403
    0xb0907050a0906080309010c0501060305060c04031b030308060f0102011814060f010302031b010e0a09020415140a030c110303070e090105040903080103061e09060509010b030a030e060d020c030a030504 88
    0x101e8504558400d0710a05458481c00b4903001c0c0e8105100580440d441040d400704254010000810704654a03219107081205c15580520140310000d41402441200030898200d1010b0322071041c000c42c6103480040c11184040c01c49c2c0d2082d0b890108400d41c0c1e030b100350069581080c0100c040c03054583c00d4a044148194030383c95100160092030001007282d2043c41c0801d04880c0c025026114003001031b84003013250821011158144007448107000c1d0191120840304001d00009d40d00103a60f80d0030708015185080c0c241207640d0030003030004406010440440203550208036036040200b0f40640c1a01c1c191081541c8060100d00c520010041084442d8031440c00d090313481c820b582100950b41c0764070030b100a4581e48000034010070491001080001d1580d408414000c0c81c481d07181c0d4400b04504410002e8806c24441924565107a00503c10081801c0c8036070780a107a400c07001012031242c942d03000b82c201c0a2031400f59205000204000e040001c50360101c404c0542c100741030b0303655000700740e00140c0245802d507030 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 61821900 1250 61820650 61820659
    0x915091101080f0402010819020304030c05010b0402070f0f03030b06030a0f1107200f0a031a06040207262503092702180301020309060a110405060a030504020d0b090705 74
    0x10240e14950007801501c0c054002a50315400590391a00199400c3e00040c0c0f800701070340042c01c03030702e19814458405540a01e1181d55100d124540c0d44c117100782540c1a4144d07c1740f141d441007000030005002d12402c5070400c0c4e440f038900341070012030342003c0d4000c281c04080c0d10780080b000130401510320aa540002078aa450100c200404036002c49215041e020300c00c801000001040201850092102c10842c20840020000c840d003022000106040c802d40d640200c4101c00b10958010114030780c0c1040340d038480340030780d41103040c00c2154841c0d0724505090b0554a07485618180fa2002c204904021501c00c11079407048481010342403810f000700c40b8486401540090203101000c01e252415454060b50401d00714148924000c1380c5070b0303401c003e503c007001c40070170710103030309030980c00c5890a0010318841d00a20014190394a05184400103541c900d104000000501708424049507448009a442c02c03203041ca40014180c2e542e00c04203181d4007540d40d02522402e4200300304071011000007003410a4980984 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 61823150 1250 61821900 61821923
    0xf0405010608010b010f0507020f1002011a030604020d031b06141801090305030106031a0409050c030d05040e0a0b0f030106030804090e070302100507170a0804020111032b091509 78
    0x502c41c600301c0300000745090000d0341d0007003004045481a030207040600e000074103000c0088454000200e00c101c8121104001d40d46500c4504641544007151200c0038100750040c100ca40b4059001480e07140c003400d00201888000d1140501e42c030751030b20114a000e41d00900400070400440e070070000b07042d012275100f40e8220410316076000d03090060148001d0594141c80d09410359080850030340103055141e078080749c8615450314103400c07036949002c1d035001d1602500c0540003031013000007818101b41d0f82004d0300c002d00a00300010000e403070401c601590310160742c0c000080c602201c88000351030160210002c950560900401200f801460300040040b100c13410010001c6622074140c6649989180c84040c0d4403070103c95625208074000da000781400d9200706c6040c1c841c0105070310382d050160016000b80002903c0807003003004658200a800030700e490804001d50501c1414500071410001660241c546001501d01c000d1107201e65411a88550b0b5103c079200c4204003e60020000030248540c040d1609820719 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 61824400 1250 61823150 61823159
    0x10090606050909060609040b030a0b2509140402040302040c030f18020616210206040b0a0608060a090201090906180b12070614040e1e01090209030705040f06030204050f04050106 78
    0x5208a0b400950702618403045903960804104054014001e0150403d032104c3c1c0000f001d035020b00902204c10300c2881d1041281c00c10341c50604c0143c6403020b403800c2c203400940c11450210340018060040f1a030012068044a62210200c0d020b80190340c8000c3d001410001c0500c80d241d0584c202d2100166504001c2003007038404c1d03101c0c848840410b20043e401000800c031503520722580080e4410041d00400700b40142c0c0c2c201a980c000441d0303812005000580010050004200c03860101d0781d0011082401440380900381000c15845002c040e000c3c4201903070300c449141c11039014000b124014090f0076410841103640d54a07410b45204a030701c41c0d55041d0b162a102509600e8000320103a401420303080203007601403c0c010305451264030100d94a0340d0300c0003403000003250146191030700d1081c071104046070030207036032140d035a1080641030700000039450060054182c56100040d040c0111102105c0114148620703d841c0e0001300069000070390001e0408041026064058007454080d9105000800603c1d030f5070b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 61825650 1250 61824400 61824407
    0x1020a12110405010e030a30020c1e0112020a0e0f0406080604080a03060b0301030c080f070806130c030b151806010914040b030109060c0e0409080f0f0f0310090606 72
    0x1100042001d040d00b0701040c030855109520913080c410002d42103481900542e210140e0031090f184e0b04d922903000d070529024180501c85030742c00c00c2220900040120640307681c0002c01d42900c04a80c0341024450750b1200a0603031041c030201083c042d007291302715524911460020441d10034440464007030300515002252500b481c0c4a910101d5100704e0203003201703840c5d60340c038640342e03910880c5610304040e1241c001050b50042c0400450003113215124580d0303028540403056080071301180da041420341041d8400c01240070702203043d6602650b0440355000d5072107245003062102d0303107680020786090644000c102170440c01035032680360203004803080c513980060401c1c80d0b807140d001240c5642c0000c041900402928205010b1401220802030000c14403c60b00c801203421941d00002c203a03400c03602c0741a402056500040c031601444001d48091010302000c3d19503644c1e074401c00c074207140d00110010b0700301c90280c24401610924034040c2d031082da490038030010880d44801075000d01e0001c10319022002401070b01 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 61826900 1250 61825650 61825661
    0x6050303070206030103080f0717040e06040506030a0201031e1803021c0e01030c05070f0b040605010506070b1305010605150c070b16030c151503150605011403040512030901020a12 79
    0x10700038000741c03451b82995203002058225143e0040394600500141c400240c006042c002e040141c4400325403654a0000f808005c6140034218501a034604001d10046031004079100050319020308001c140c42c080314440001c102d643c1000150302914003006000c503600440804002c140c080e0342141c22460143c2030042e42c805036850305d90085603141440040f1540207410020880c2844e040032810240d4580702e40c02c00e0b01480008440c01d2090700104802c0100383c0c0f0505024010a03164a420b2811650300c01c450b009010700b003103002000040050301009825000f403405030802906039070036100d024502d80341030f4100d103541e10b1190103414401300b0185c1c1a43c1c25600c1c2ca090580c013409810341c440c1c03400e8490341100d40059501088041162404400d103000b8008520011803148c12224514100050540c440c0b2200880207800c0030001c200aa901104480e07045481d54071a030380e07a440b94588945400c040441c0201002030100c1006603800e81036004e030204400b070341c407541c0240440300001e03001c544 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 61828150 1250 61826900 61826903
    0x9030e040617070501020c093903060a060f020a06090f080720042007050f1614030105070f120e0a080903011401030b070c030207080f01020702011404061b11090403030b040605030307 80
    0xb0700000b002013406560020320114808286c1203612031121a4013100c2c0f2700307201180e001200010034020345082c40750194000301041e18004001c2d844007500213444084620006d0440764451402e54140103103407103200c03031156200b40400d5481030149440c58000d100d241201001c408225040b000d00c0c00c1c80c1c007501e0081c407030051404e050701034034481629150f0000303407040e26148118800c152060070100601c020540c2988845d00340940742214480340202c060403014000d034103000c1171045143e0045004841c1a40c02c1c02d288120200002e0300b02c1c001d1140145051080c4030ba023103910705100c007035401040c510350254001c1c04150440440c41812034021310000300042c02440c00a03611510494030f44110300e200e4030586030365a50f5102105d2600b191004080d01696002030344408540e0000c0000c4244034665084c281032900d0480f001d0140d86040094562032030651440a040200c009045983c00c0c10003082c0303483c28181400c0050040910b01032490046242c8138021601346000030a0312a5907 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 61829400 1250 61828150 61828159
    0x190504050c01080c0909040506150102070b030606030705070c03030c0c1706011806050a24090b03010302060703030b030114010e010f080c0d05070f06050c010501050402070503070609030e040617070501020c 90
    0x281c00e0400110388076140213044201c441810702585540e966041201070183d400f5900402c907500b0003590030900c0480d0010003034107540c46074408001c2d0100b83c02c1543d9010b00116005500c0c1d686a020a0f030b080e2169031070090100f51030b003502108054110805001081c041c0c0956802030703032100003a04641740002c0c08081140d0200c001000204540501c02c0a251080c0c040891400d40da100802e8034107456800a000140720810010684240c1d80c13010350b00042c503840d02d403040c180b03841c903800c441e4801808040c1c003130140042c1000c185802030308140c07211803000e00200000507814074550f80d800002c0c0918403403a0000c0c00005102041e0403c5101500c3c0170340003410300d0007410741c00c001c0701c1c0004001c00c480b00c0c00b50f100c00103641050b1040d00802004140c496580d104c952002170790844030146c004074404e62050041201003400001555802d540c000c800052804c100c0c102580d104e07a00000e400da000741030003000b08d4180502403071107064090010860b4282d075150360059803104c03096070400c1d801 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 61830650 1250 61829400 61829413
    0x70503031b0d0f050d05060a170106140301090308072615010306170d050705010e0f340504090302011e060807090b1813020607140c0a0305030a0f090f06020619050405 73
    0x2e810f46c48107030000d03c0204204070040d95144440c095840390b801700036040c0d55508041044010020312607244040403802040b00d020559030140c00607501134100e1040010403e80c081440c881000c0640070605000030a901e1031500480f008004032100c1c0600d80001d0400b040020f50a520181d00c9000007400303000b8280b007030044002140c454000120030b641c151341381c103141003150f4402c0c00344441c400040000740854802400d03046030185500c9012074185100d409035086d00d405003a003010b0a07500100c60100311010b440c01d08074054030032600f412180155030080c45410390382030350100e402c40f01c0c06425512600c1e90b40003084116400140c1c000d8200c0411034412800214038406aa03000c8949240e002000002d40c021411a0308000c80071942d05200d025004902c1104022034000c1d81c00c21039003041d0150440d91010f88900038502c071070080c00a411030390340d41c0501a1000c5009048a11024900141e0784e0100a5803043c0070303a442001c200000c450b080a001407402024415034004005040d03 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 61831900 1250 61830650 61830667
    0x90b12060c042d090b120304050102060106120e1b1002010b060a0e0105040803040b040f0803070203100e010e120301030b0903130e041e060e060606070f1202070503031b0d0f05 77
    0x1070346441d079105143d030000380070700041000d00e03e00c001024010442c2d0001d075070401c2c8403d00110000131414191160700c02e00081026a07030000304941581c256140402e0b240e00c0c43c01c50342e40500b02d0b0144000040c0500c02d03000500101100c041042c017a000c07100c070080300452a4041e42201e0301005956007054040040d130040c10701955141c2050041890030500c0d143d620400300e030441d00143c000d8003100c600060104100c9031a000e80c0c501a140d854044c501d400d0742c940c0041d07a210000c03c50f000303074103845080c0603207420740079423040001c408001c0c241d881070341c1c0c00592010b0301d0f40300f4007045401e480342002003900a1000000d540390042080f070345070119810b0000185482000410440741031084850b41d100814075007103913500003440b03580b001c104030040704020b03420030380c00030140c9005003400e000c140041030705840100e29003034001c00070801400d04208104e041c13801580060303401d1b100c000703044221491400f10030502400e101083c3d80d1442030803603046802e0400c04280d880092130038000008c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 61833150 1250 61831900 61831919
    0x60f06010906080f130c0b0307031401060c0f05010f0207060516020708100519091110031514040e06040302070f0509010e0115020c1201020a02060a020301030f030516050106090b12060c04 82
    0x5805c0000f4034000001030006030758081e08903c954010807446400802844501a01030040c00c4c400c8000b8250300e0780703640c1010802014200004009400340c2c40a5400d0014403400307602001c120300200400350740c3c0c0c1c0218201600500802e0b21804080c400c0b40041316801e500c046460b40030354256801030101c82c00c1c03c58001c40030301000b4001c034103414060105c3c86401d080d80d2042c9466076208030900b0704180c0e5240c00300004030010030522000e041c01c0842813110303603c02c40040c90507240c1010000d040c214445001c41c00402c43e40c0c20b0b14100d0f1040c1000d10060540021703105003207400c0034204140d1242c5410502c011441d0030721403200160885d030010b0100160440d085501001184103c031030710743c480b000052009a90f02c20303103200c99500290b400c015a50600c14180d000b5a010340542c03955141d80e03281e00300403400c0800036040003c0400d11051882030030409071100c0d50000024003000703440f0341c12200100f2203865141d104400d54014600484008509144241103800c461810300e840d00651030b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 61834400 1250 61833150 61833181
    0x309030412050c0d11090a0506090703021803030706090b01170604020d030e0a0e090706030608030a140d05010e07082d060102030d02040815010f030c03080a0c0f05060f0601090608 79
    0x116440d0145821154444e200c110b948440703e4007980001054010710014030052090281c13100340320074141001c1208a0f16407420054201c00b42d0301e001651110750004040044011545003030380340c040099540c052100681119400c00d0140c291800d5690380d44911172240720001d02d0458283c0c210500150152900c4c1e00b034402004c0c0a801c0001481c00132000251050381a608404507468196040c0300751002c00300400c401900d02070404103c05410085019520b0140c600a042003003230741c0051203042060003060303604010742c440c001d00031541c6880c02011404c1007180c1d4040003904d40030000b401c0f541c41e1042c0c147c402021b120008510107141c0d07000007003101c0007003c030360641c07108000b6a06400c043d8401000104954000303404070201c442e40d240001941a84004003844250a062003c0b9200900800481e40c0c08890300d90348901c40e400c140c4100d604000f003d0300b03141052148006000001c1759080c86240c00750410200d40d07451000549080d0302038001c00d00080c821200060440c811400304 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 61835650 1250 61834400 61834403
    0x3020d0212060405150a090803010b030c04080a1202010c0503010b1b010b030a140105090726010b040905010911060f040b09040b0303030916080d0f0305060f0405091609020309030412 80
    0x404103044407100109141c8241a90112a07035400f04003032004281c098001190088030061080c012040305849404860006000b040d074452000804100c075541410115001000350605942c0c0d4440715081c00c203003817a50040e1240c01f65081c40220382c501e602c1101203038141d80c54055400d04005800141c801815074425450b0050b44d6258600000390f981040350b050614490002d54000750003000303105003540d401810a417419480040103115034541d0389214000c010000c035810b0b85950040e401c903070140c5605021250000d10f440103920038410103410840c00305020340000c495400d401810300540e4440da010030085040103100034000491004000c21008900400228072240782c40c00180c02c1d54000d48101c1e50b16484510130300b41e001009420840100311110181c0f034040c5182d013000e02101003265030070703007010f54890006070540c1c2e503181010300201c4054001c1001d841e1042441d9541c005440a402c2103602c400070004104801d8000c42e84900d03e0b2401440c1814944600010503641e507080 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 61836900 1250 61835650 61835659
    0x902010c020a090b0a1703090603040507150f0f08040302030d021309060f0602120703020303180f0109080318160308160b130204050a05060d0b06060c030309030306270103020d02 78
    0x100312001d80d94070306055028164900c8000741d038800b04030411003451500ea2004c04803410390094400345250100a4598290007a41c4c01c990f00d40c0c4915005040c8440c0e038002220ba29822226005201e61050060a224296840e20307402c21070600420341b0308450864000340160710810000084510640181850304d01d13041c04000e04a45030000c44003a00d0b00c0745c001c04005a02d01800b0446a681005141808241e41503560715007111610025281e00c0004c164541c02981c141071081c00010401c19448a0360010000300b160412600c4d08042603401500c01440110501c40c5015211a01184061001c1d480f03007540c0340980d2455441802503040451440c0054540c210b0840110b82045000e6101e1100702420800c0d002c6244100012524003509811000d8a49810001c07682c940030351003c403a68200400609a07a0b640c00029824450041648001c1c080072090090f000c10000155000e44401c66003000320406103c100c03a038034000820b2481c803980601004002600700981c1c0b50300003900290 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 61838150 1250 61836900 61836917
    0x10305040c171e010e0c01090b04030602211504050601020c0607140a021309020907030504050c09060310060314060105030102030c18010504091b1403101403100501030f140718090201 80
    0x103c2a40510001640903c0070b0b51900b02010746001d09101020a070303442428007c00040c10103600010314001d034000105425030000d54160f6140381490040c6188040e10301c41a128a0702034064186101070510841c003850078800820041c0d030012450b03200010000d0080c07070400741c2c40d4a9458404070400b225116501030b008070300d40580c4130081091141518145e02042840a61040c8041c541d4010144402c06282000707100000308046045500e0110490701406235450700380000c0e08220111400e002c0796494000c002080000c2007800c002e140003034a058402070303aa980281030a0744002c485800078070004024225100080340701d0019208010301d005818540c8400418080b1180400c1c0134402c0c900c08450302114542c095003044140502901803420f5081c1000e407030905814034059030000500d0200402d940d51820001402d08100e440c4043c40256502c0c1400301e070300411403030160f40c0c444540091a1a17210300050040071a140000c03003203185410129003030010f2070404001c0b4104032064 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 61839400 1250 61838150 61838173
    0xf07060e0d02060f010803030c040e1005060d090c05040e06011e03051f1a0906010f030b0402070b041a01030b070e2d040c080606070f05120406030c0905010305040c17 73
    0x1c00ca41280c01880360000d008904014844e802d4003081644002c1700ca0740104200040913480c0400e48080b07584480240d20f0b203440e240207134021518039801035600408042080300310181181c00c890003a900402560411540b550140400d44403260002003555000c42c0040011030038501d8041c520340203010510304a2074495a41d6410000c100384100070512803009180311004051003031114031200076000020480307100e8003294070340381f0080c8440d05110400900488076030081c5c0041c3c0202078020021590780000b03162210b600c030010350b41034500208104498841c9e21500b504107041e2600003c00e105595150312080f103036100c0701440c45130032a5400445400605180d001c0020b1200205003801c20100c1b07200a01c022507004805c0c0c0d00802104500b07102c01a10741c1d038120350f203490700206040551449407d1652825050010080a100380018002902949035201c0c5480d010350f079071511a0a5540e038011170940c1d800740c3d0041e001c000014401c0003c2a0201c1040080390341601c252030381e046d201c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 61840650 1250 61839400 61839403
    0x501270506031b2101140a030b0c04090213080c0108040503090405070e030a050c0f0a23060910030f05060a15030e1c09030506010e07020d0c02010201110a030b03070b030c0f07060e 79
    0x1000030314002c0e4441c0c48004001c1303411000307094054440702c001b0014042c00752001407503507400b900c40a07005400c51400b140040303500408840c00f0b000e921900b99600c0d014222803004146081c0300780d800c240903d41d81048258810f000b140e029a400800850403e00820300700401408094045010f000c00441840401e407000d101d400801c9008102424540300d141041c0b0000000d0400c5445c441c07001500c0c2440b20120310b40085114841a0951a00207200b040c0890301600c10000d1007544020080001c2c4005903040e044410741e00442d090034466500e0700c10a0104002e20740c052404602c9640c03070f40c44a098071907802280c5464850049030a640c50700c05031038101c10720000c2c0c1040014500394041c000d02104001e15401082c420355a10040c0c03030040c4000b5103e040c0103407039408101c2c0e2600e171801960b100b5004001c030f010790780003199510492004003034014a00104651b0090080302000241400d5a1040d24071615074011403a15040011400c070103103900c50407040b240566500c0640d2045c40c0d0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 61841900 1250 61840650 61840657
    0x108010f1401090314030a20030a0e0a0e040804090c1407030f121e27080a03060b030a0f0c020c0f040e0a05070605071e0201050f0309100e070501270506031b 69
    0x15805e001d550b980000010041442c0e500d00c41c440c611041d0302c2010a04840300100701c2d00700e0012807420241404101c00021001070940e4001e2079021403200600080c405144024401c403070500703c3c20000c00d82c8030b080940d0541c41c04502041e962606100c21004a03020300081d81d0420414a480c241d0382902540000455481031441c000c091805151055104568401c201500042600c010040c0e03441c0c24091140c848030382c5004000c58170209441a415011360012006041a890304540700d2a240344036038000c01d6401d10b07018101381801d00d0b030400c076030021904c3c0014071009043d08008106020034400a05508070344402948100949180420401c0c00090060600303503860503990f803018100301d1030b45a41e00d84000c0909a0006243d070041c1c0c0c100c0122201003140020603512a6a14281d9a050003602c1c03110700351050400b810041c0c5501c021070fa080546400740c944180528600c040c19010910840c2004010f00d4400341c01c0c4480d10b081409541c0c048190425265226240a841e41e201d80 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 61843150 1250 61841900 61841933
    0x6080a05060d021504140604050604060e0d0501090b061003050403080705031008060108010203040311032b09021f11070e130501020f040605092103072d080d0b0108010f14010903 78
    0x802d003484495034074803c4400c506007ca031024206410000040e4041c49240304020610402003648415922202081e50059800070000c0000121f641061044200201c0d4880c1c442c00c001b88070100c0d0701c2d019100d81c030700694041e55501680d54a4100540b4941d002030850107407440d03110000102c9030020403505020781004000541c49007814075018000684118040c01c0540062016900c140100061174051004d0084c0b007000d2002d140f1030807401072035105c1000c2d4006414100c03034820701e201481710341c85000c4280c0d01c0c0d02c44a110a10699251111400390300c0c50140c403500442c1d511b8160003c0d0301c4440d40200e00062400c40c03041429620355000394030140101c6c1000c10812035a01c2c2405103c1e006c1d10702e0350383c111007040440b11020344911441800a004145005c0c1c010683c554103802040270700510381074401c0d111198244640c0c550400b003e07100b0f41d01d0400901042d103501c1040318504070b808450b0b881c0151030412105112030410382252604012942c42e000000c02c410704e2545040a = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 61844400 1250 61843150 61843189
    0xc0f0320070f12020d0611091201020a0206090c1509040f0c0c110103060e18070504050901021b0f0a290703020703030c020c060306040c0c120305010e09060106080a05060d02 76
    0x86181246149031080b8503404180d11420040d005800760319041181c0004036800000001c40e0000310317a208043e8001d120718242c100740004612880424150300030300203c01660203c50b0300ea9100520940c2d148a200d0302c0c00d400c01030401400140c2069140588a2080001d1000c43c0e03011410014408441c0222000000100c1c60400328092140f11020304803400d00c2842c0a01c4114140a0146d0209902038680c1d40390300c001100011b903a035420300c40803002d410010400e01032070508aa0050107904440032303503000a00e40e4911401070a0300000e042c140031008030301900c070458031602c03050301d490b103075081c40d90140c5020346400c5c404242c42d000382442454903071401601ca403242d040041c1115a070a50650a65010001118050744c035070040d2580000c0c01c0309c010039107126001702281e40740c9640c2c600038482580d8100f4010346981503007000d4160740307035220513082d80d90301c51640c40da44c2c403020b20523000464100e030041794561095420090784443c01900c0d181180d80942e01140414411720f400c1c0d00350 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 61845650 1250 61844400 61844413
    0x20711090702030a0219020d1a011d04020f1c0b1e0903121602010905030304061406150a05090409050f010c0e0102031305090603070b0313050c0607030c0f0320 70
    0x1498121140d5801c19860b100650603e8007440000c4e41e212070455100c9039100b83c0d9801801150358421310000d2550340540250800311800901281180080c081c200998081212036902141c0314000c461203950010f0202105845030428000d0020044142c250019000d150482c045412101e2041c021a01d11a00d1000f1046155407a85411005821f100c21a0810000400b0b40d8444001541d00034280112840c3d59036006841a401010080c0e4024505c0c0004001c010900c0b10681c840074014a402280e10301a5036414100900b480c041e00f042040c081041c44541c0225100317402901c800c040207030001038420340c41d4580390b1a0480d00e920303c460b540e45070341a0140180c1e0194594036524000c3c001541043c01102d6001e038a2845402507030b00841101c80010305030341d001c1090f20000c21340142d80b546d0f80d042402541e4981140c1c0c0c1c00a484078881ca03070307240016040030380445075460b806681d00851100d0750341d122043c036044600241c007001090103040a2035604801740d0400c170600d0400500700c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 61846900 1250 61845650 61845683
    0x80a05100501051e06040807170c01030606021f090c0306020901030f060b09010809011b020318090705030103062a0201020903010e060907060f090819050610030816080d0207 76
    0x281800303115040e58003a0070030004102588501000c0c482c2c1c40d4400d0b0100440c640d0b0000071400c00d0040354403820b02e40c4540f100001d880c0c90030b0311501c1a254400000d50317011040304001582901d003e032040c20010703845083c9000352005104c02c11341c01201c91010100f00c5140315194440b5404040d00142c0d201a80011800e09035a0184148010384e5106103040c49803514000c1c42c4d03902400342841131410301401800080900e0000c0d13001010700301e007082d5503410340712400f90020b40e41d070041d80c40b0090b0000d80000301030302464403101c030714030070300041c0d235a41e24503829980c0e5000600604204241442c40b0f424070051815003144903100050b10a9000503183c5101c1c804250946072002500702c180e03000714017032140c150004030b8070000b42c400900302816618100c003411920000161b00400b002d010b29115800c42030226100598407a0040d03045507010340302c16007c071584d40068440100080020406c2c1f4410100f040110b40c4098003d0101c181080700110300007060344c4c8400070449400110005480 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 61848150 1250 61846900 61846903
    0x2010b0307030c0e060a08120a02030d09030806010f0504080d0c080d09030305150402030c0702240a020601060305160c03080c0d06080c03010e0d0c0b0402060403061b0801140916031401080a05 84
    0x150300050460340b000240d40b92030700548c4c032041000081d000b51440007803a00c466a00810499030301201041d0200034821032401c0050421501342c500900099007d10044885482002600d0960342c0c00805000d908451010507a441e40d000c4204659407841807060200a15a07031181c44502c074040c0d10040307001c0c60b150300400c2a60301050705841c410707441030040c416a10210015108501d03030541d007240051030303050140300107035400c1001c2d1210b03080700040e05200c0980c003060603412141c0c2518103103c691100818081480700e130303030b809500060031420f04a011920a1208503002a84030b0f01461500707082d5040320382a101c082d040f00c01b481d4003440544d0281d08003440f882c1e400c8020b00c00501a400074480c1c006003c020303d140c01401c2c0400660228082d96203000464004503846141044003001c018041070840e01c4d4091407070701003903d100001074121700c600402d1a1034607001b04018600d0fa12021f900754081c844560b40c4e0200b580c0c0340040c55028200c0301c0124060300c0d8041c0207000180b002c0c60700b035 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 61849400 1250 61848150 61848179
    0x81201090c0504120204020f070b0103050c040b0f0f1003060503070f08060105010806010c06050403050f03090604020109061b1e020301110c10060b030f04050a0804060c0506010b03040c050d0302010b0307030c 91
    0x103400b001401c03c020054031a210038055002d070750448025984400f101c08520307040c0504400a06001500d10000081200016941403000005e841c01d0100303008100810180c2e80103004116000129084243c2443c0f41c000c2e0030905080c51400d00183d884d80350741c080ae2401220b9002010700145150081c03045607420044030340145824030b4440d0542c6400400240005a0820700503c3c240c2c403840032a0401d070144080d41d22202ea00040c142d12071a121100a9903660207543c2a408600e0b407900c0483c116105408511350440d1041c00341c07498102c180e13105036411102c24423a0b10620b0410882000598080c050244034074a2000c801d81c9991030313500c01a081c440c48201030104149440c0082003040d604d081502d52280b240c5500c8401c039074860412030300b40758910701c009104040c0010081801c9410a015031001805081117401c00da881c3d076004c0420b84010364010b44002424801003041e441c00451840c00310707200384004100000f5250200b03280c515075420031241c407c5036007410b000c01c00b48009403 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 61850650 1250 61849400 61849421
    0x103180c0f0f15020705060c0319030207021c24090507030501050f07050313060f020702090a05070f0c0812040201090b0309010b040507022a01050403021305010501020115030302070b130308120109 86
    0x1000f0f24100d003040c041e6031440310307119480c01084045000d00c0d43c80000c3c0300b07446050500400510700c0020f2110000c00952045008034850402021880f8035951400d2206c000d80d0341c802c121300445940607408481c101102c414000300980c6032108a00004c4050000b0030055106800206086c101003030503241c3c4410003001c10b030070810140200300d416000503250584c45038008900140005112400001a100d5544040e421001100901c19402e080b0380c4124400c942943d81c0c910080c03504101154000709400c0080d000b08024404c500403031746410001a0450300c14180f182d1102c1e40e55510482c1034108984084060359500e1220040341458010103601000d40e2019010b9181c5400104c03800c0031301c5085110607101d07022280c0c0050b034018001c46010f507030003c14004e40541d1400d80780b4041d01c403d006040c019403e00291042c02c00c80c3c0c0c000300c02030f45d0b8990040d02c40c01c1e05103280e101e10754100d0900e880c1c2000001c0000008078200100809103070400c04040707020366040c0101c0c58242c40040ba01d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 61851900 1250 61850650 61850669
    0xd0e0715090605180409030906020106081b0609030c1c06060b07020102060a0f0e0703080c01060b04030c0e0403051c05060a050102030f0a0507080c0607020d030e03070c050103180c0f0f 81
    0x1140480e05511480440541e00282441d5031142e500720401c1005030040945030740c0162809400c001815001040340c021110703941d0080c450706032901e2005494031207060482d4042511240250541e140440c081c0c071015001400705e4209031400740019500f00900028039031941c44034011071040c04840d005030703005400d4414003640703005420760000703540f00c81c010021a45d0715601e070b1000c001454913070480c000609440c012204021703100d0500c0c07011a0301030700070b80c0829880c0c04000500360404105440031030340c21008004201e850100c03100c008150003841242080020401850045207a120890304c0ca807402400140520300035040c0801000740d900998107540c8140401a01d902c03c41c412103120010624209031100503501e0710070824050480d014400e070003010f080041c0168001404610000c00340e13014080d1880010042c2e440c0d205109000e002180e641740c3c184115406600000085c003203503511407415045079210b40c102c0d00303130b00d810648801b580700c1c504011001c0328840c044007030402003c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 61853150 1250 61851900 61851929
    0x503070f0515070516030216080304091a060901110c13020304030e18061002100f0c120603110103091a090303090f0601050d0f0201140c03040f060503091509010b060d0e07 75
    0x440c040e04a0017403c0c41c0d5080406560282c0c010036209108010324013201c40d03500b18000741c0360220281c486c1c00a001d00291a03107403612401051060703100f940c5802c0300c05040c07107141070b600d48011145024404c100b441c0e541f00e213100315101600e403100380004012030000016164180780c54010310081950605900c02d0100c0403903d00c40d8000d20180c0d0b03400c140c1c100c5010580c0311020340240d04211000803221032840c584007500c0247c0146e40c0114442e9101580e4003102c0c402c81040520403508240030240c8804080c0581805650282c6e1050200d28082c1ca800684115070801c80d03410110201da0802e01600003105110b2a50801c0100104001031203000c0e0482d5130602012400d6034081750030142103089903c40c00c03c15a4014154185421041c80e0340a5070742003143e01d440d07070f42e41c03062082c0e40c030407485860700184080c419000c0da400307145030b4409081d0104003420402840030001d80000c02d070355600c01c1851156520a40140512a518180458007070344042407942011001c1d0b00c10040c40d0080c5 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 61854400 1250 61853150 61853161
    0xa0506010806040b0d081204021c030210050a0914070f05040608060c090414011d01061e0815040606120e061b030405070f030f020a060504050d06180503070f0515 71
    0x8609181c2c0507005540c0068910700c1140060560b044d120000350201a001a9400c50403000b00500f9115030b000b6038042b00900401d542c2c0f100ba141010201400503001b2640035001008a50032450308492081404034114880e03885001c0c048100641c5c0d0480307603120702d904014904080d00204003c06003107400b085803500d0015160f80f10140102070070340700b11000419400c02c1d6195404016000d1503400403012644c1c6852210381240560743c003080c405140e2000005005104007100c1035560b4541103416000310500b40c0903500c070003003d408190040c6941640c0861600c60303105200c0180b081d5901c2c144500b02d880c1041c02140d601d107041c1c0e070041d0005010842031480352160404131026808500e9600d9a0301c1c101141400c0540d00440c086184440001050104c0300106020361402200c00103249607a800082d101885180703e00c070381084551141d507002c600b45900c508040f5500301c4030b4103038500c4541e07079850855101c140202e903107803111580e500911008014191801140360b458a6290811 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 61855650 1250 61854400 61854407
    0x1050d0809031203010314100513030f12020f040e131101080406020c030f220e150d1202060414070e04060528020c0c01080c040501030509072102090a050601 69
    0x1009005010410002110221628100060400000403621107a22075031240b03005046180302480e4035910b4401c00c540e100b50020544500b42c011000c0181007003440c005a64140e070700040382c500c031f02c007400391603d4801402c00e11400104545058411141d903114100030300190b120308003508640c0aa5509045600050350703040c15113580d4282402c088038207039a86d140c41c41c003900c21444800300500021a00300790030640d01016049100c1c030004103401d00301d01c01c0d00442210003188141c0e10903800c16400b084081c4040341141d00001009081a80d00050a4952001c1c40312521803000069001c40c0c20801404113040b141101c21405802030070138a446c1c070300320100c14000548003801496075100420b4a10b40d10301c80c0d096003101c00790100b240565070020010001d40007804000e00c02e00803008000d07079035885021040e1051020781d071901d007000d06143c011402000000d02104541c450a80b000c81d03041035014180703085102c1c008440e0703030300d43e02c0f441800645a40a40404402c4d401d140c1031107a50f0781c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 61856900 1250 61855650 61855669
    0x408060109050c04030602120103061d06010b18061201260c04020d022205041503030207090c26090d0302042105120d060504060503070302060703080702070302090a0c030b0301050105 80
    0xe1a40803031103403540c61807424613101d0b07640b0091440340300082c100c03201091500300300d0403a030003120100a100e80c45888201c90f181042c01008050b080040188070406926020b420044407481c260758964503002c0108025038404500750b00e460146400400640100ea410b000ca00840441d41c1413510ba8009100c56035440007100a81c452a0007040001d031440c2940e06032008500c00c10b100c2440d01d43c41009040e0004209d016803070080d0308003060a0350100078442078104983d49070b802040e5051911380c6400c020070b02c184440c401c01c0100c0c02180060b00c4144001f01d44064409035500150404601a5103441074200f054000d050050004001e09010154200031130350900d01004c07900b100602c0d009040c041d01201185190a000c240b5031000c48a03944100e042c2c0d80159800c00029880d002003503651300309880000d41c000420006040024840c1003a150042030750300480b5125911b940c00180411000ca175101981c540d28218640e54a074140034144a408081d03000300103d50500d80410400e01 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 61858150 1250 61856900 61856909
    0xb040905160203070b04110a0603020c060702010209030c04050406090b0c04080c1008061210050c210f04080d0f020a082e150504080304060e011d06070f030c02030607030e1204080601 80
    0x4405d0700007030a016100d07189140e044401015110200c0d1600c001030000e41110341e0401c0d981c8a04000640c0103401442110806d40c8001c0003801449903000801c8094280148104c0d003c0d620703180c8020005104008480c0200d00c0e190b50f1546070390402d9140c502d03100c1c0c04125584289061030003019516081806e8903000300c8252610780c0c510300301c081c6861030513800344286059149884108a0b00108900c0a0b04e0310b525085a8100283c00316074007210844020f80e4103c0c2c14000c1c250200b000103044000501d03580e410041c02162a0810200d11002c0380c210104c0040458800070403c800c12100b080f80b0b9400c1404000c41d41031030b2207400185490b42000e80900e00c030304541d48406840d201d002e1400e0350018540142100e548a450700d40080100c440303000720a010821005040c1c0c1040e014084101c0010000341c0300d20f04090b00b503102e0310406418040c007a030a100d55000d00ca40942c40034401284540388a40f004144121004802032420381d44c4039515064003414001808042400724105d070450307 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 61859400 1250 61858150 61858163
    0xf0204050403030209090103111003060e0c0a1103070605040308090319030c03020405030a0f020108010602030315010302090103060803161b180e010e030c0706080c0301060e2202040b04090516020307 87
    0x265507a241c168001e1140c03480c55903100a07848000010040c445861007540441590005801003202d101038084d03035440c2c05084012030b10b20001484c90b80e4010050030035a145880c0008890b0021501542594400710f801d40b06a038135901000280740d0040d076203540100c086c030025490015184130000711800d254140c1c0c1d00305511b5000035032026201e034050b81d014060090683d0fa0014403480e180d8104400310104a0101e4004000010540d0021041d02e1250348905c0d100c0045065620044009502018240c5e060643c0c030500421221801c201504a00c020912404c008040314109104000b00714041207491120a4005200c080d0500c207050600001c224008203802030388008650142604050304486440301280100f00c140c40040c40c4412285642c69002d003035118a90b00c44082c1c4401d0081d80007155008155184909041906082e02da1540784400021f11302840c3c40b01c2079a129034401d4607110320100d800e12211074180310300e1f5000701c1c158440c0b02103000411000703520ac0c0103c5402410b179 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 61860650 1250 61859400 61859411
    0xf0d090e0621010c02060f060904020d11011205070c05010e0105010f1205070306090b100501080105090f091513030306050d031e0509040f020403060515061c110a050a080c070f0204 79
    0x10b09401e140040826041a0300900800c0350b000c070001d50711030046400c0020800020b010480a003084102d5900568025144402100d1140c82d00300302d0502e911006810810120341d4a8981c40448c49018010a03999a4005642c1c1080c00c0c81e5003543c800700742e80502d90349000d004000070039000489030212000301031080400303070542c1412824144281e01c05040300e820300c40c00b81c04000f02210b11a00c03131f010900d40c84c9030103030b01d41d0011200380d4400d0081c03a800403821390210704626201030f60300317500405500c1250600342500c0d80b030340c0300100c0c00c0c1c840000d0f0039002ca940004041d014081d10025040c2074400048070380342510028400303440c03015413101c90602e0a190300e02e07135031254086562800f0094000e2154200e000340120080d40319200540c0e02c02d2400000c12115030f103c5007681c2110710010300c42418045060310400e00c800018941d40d28059075592a9072038291a0030103080544e220341c407a6500d442c20361401030800d901c010044000c203601080b14800041e118040e00300b1564040c1d030006031 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 61861900 1250 61860650 61860679
    0x2160e1b0403080d140a06030302060c0c031e0301050102010c11030f070c030f0305040312020102070f0b0601020f060a06080c100c0b0a0204030f06050a0c17130507050607050f0d090e06 81
    0x615110340d401c003528280c0002040f80000c81e02d0740101714040c079071400582e880d40d2100e10342c03c2118550302000780140c00c884003084020841e10003601400c0c0c0a2400e03a071400c50b80200a601e0080035191880c0541004401003281c2d40e0280b14140800d405030510000b01d05031240c0f42030f124441c04904c00f0043c007006ca4a94148014032207850055540610440d41410050402a110380c00c9131208a44a145020750034074014818001e49103c294400c0070320b040311304281d5801c031440b04000d03c414118851180404000318003041101d005d40c506010015040c0d041000366130500071061a42406003540d44518540b150340810610000368224030054034988690300c49002034426035001406c0b0703031a04203160080c80440e0340007502032041050204612001418141c580111058001d55080345090000d1880204d0446441103036120f20b0a4940c9661158000340c3c80c0e4000c11030694103584240c066a0b114802085110411041030514620039450840712203601c14000380143d02910070501d8004 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 61863150 1250 61861900 61861951
    0xc020316020d0311030d05061306150309110d0f0c06031401030312060f080c010e010e060702042310061b020a03060c030b0402041203091403070e0705070507030f020102160e 76
    0x86803400410a803691b420702043c24101800701500e0161194100ca028050906014407a140444003076404090716854000c40980c02042084000d1340c501007410694855a554058207012079032007411004801417980c1040e03100c402c40341c2c0154052525010502103044c080f066414110303641403a04078540d04100f25014081d002e20380c001081460b45d00d00101c2d0244d00441d101035260740030390303031400b0303840004004560503100c0d000800d0700054100300032005810250807140258105026900f0311020035044111580002c48000c80d0034494031409011203a444000c44065016100030501900d04940001c0c22201051000030410790361056501d8206000780c1054003a0f00f8018400c54441d581d4244008107501c00c44422000240001030101e42d220341c030b00d028030340320801500901040381001600c0080d11805003208081c40130500840000070030802c4054099407040030041003400f840e1001920700055841a1513480c0a100b50911810313000d940801c3c0c2c41070400d100d11000004a11602c2c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 61864400 1250 61863150 61863167
    0x601031203090c03150c0906080c1e0a05130e0708160309020a0303090f06020115350d08061c030f0e0d05010606080c070302071401050f031006030c020316020d03 71
    0x200124a4004000140001c0300c0ba42d41e4a4005c0c00f0701071001d0703c200d9204446602040c0501d001246001c008650b80b807030141c0203005083c11a000107501c064280805001c160800f1840c10002400065585a02e24032058001c000340260049a5120b00300508081d01061005105a201107a0844a0043c00b44250030401c2cdc119006000034085030303205e060051650302d041c0540c02951150f00f0340001c02c40c1c414400e40c06030b010300c42645210a800c2003c1c0516200d2500105682e00c00c1c40321803404170803403076a0885400c1428000034076910781c0c00c4001400c248402401a44110105580854070b078640d41d18041c6a19490300d414441103101c0c000540d131520b0550300c41e40e00503084210f944100a015480030043d5403860b212194141e98800740d9448a106648000f00181c0080350204880d40741c1d95062600b840c014100340b0704040300c4805030082c0b070b0002c64a51300c3c075503003d01c1e00f044080d4061142c480b408800b80b01561030a010b080441e20070b50f40042d0000e015030b400f070030070781d060500c00c8064 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 61865650 1250 61864400 61864403
    0x60a0218060309010b030c0a0308160303020f0a17060904030c060c09090e0105010801050f0c0703120209060a0f031a100503060303160b15040c0f0e01020c03030a0306090b0d0203060103120309 84
    0x115103d052041c3e5682c000c003140300c04d09002c0d20452403030030550702d4410f0002d0101c0f980180710328984a121401c0c0790211240e080c08500781502400a440024403110103003104807180d43c0c82004d141c80c003940c03052901c80e0280005010724000406d000200368001120038400b50001000304800e04002030403510040c59030301c001ca41a140c04c88598403208103401079412140c005000744243c0d00d40a40e12415524103480710301c001902001a074001034000c154002c1d646c0c941303180c0103040c0a170f10000307d42d4990000d030b103030070000b003940030038800881d054800ca80a034202d42d201b880a12020102003500a00e00c80391040034440003000040d46c41d5401c00403a900c01c009440d4010b82c0025616058804010544000e2110701c02d8000c091840c4c02d0078814010160789542d1101c045005003502600d0303c0c1882070105046000345407130300c0306a40f400c200900000c00c0e1030750001665407408031400300f01c0c2c0030a0b1007a442841c4840324103000d65000224141525000040400030314040031081d0000c1641320320 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 61866900 1250 61865650 61865659
    0x12020c1c11010f02030f06010c0c030b0412020f0604020307060c1e0c03050706020607120e03120115090501050903030403060c0c0506101409040c1512050c2a060a0218 73
    0x3100c1845030300454407201d03140301c00024004207001c00c203c0c20507408105ea1000c0d0010304000014240d40c4640c3d4030841140c000d0b81ca603080d15880780c0750407000840445080d2511014a90198070481d070422501c101050301d10301501c900d0802d03600103030f11120a4495030003040083e041c03020038800210b10344285400030500000c11040c407032421040c1c0c90b095200544035801151800106039001241d0980304400599408046002040040000301b40b00300c0324200320f12040c02801100c0304588039690207491b4200d4642022109418000c084034100d4100c50304004090061498984000080d181500d42c8810f0118046080701c00c11110301242e800068806e109400c00c1c00580f00d01c410951007034540102080d8402d82c01003041c007510002c295001041e614081c00108400100e0200e0840c1084240c41c00640416980d034040095072016034280550740000661003c0c500300c041c108211000c20050380c14508440322826a4581e04000d00006e6015000195607e003280c12034070709102075070000d1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 61868150 1250 61866900 61866943
    0xe040c030b040e01060806060604030b0a02070305040306020a090807080705031b1203040b0304020103050117211605010615140d0908070f0b040317011a0702060903070e0a0f020a12020c 81
    0x4003c1e000e444a0311540d080c900500e00828000d0506074200d609407500b014259125031604001100254010301c2c040d0b08101c01400f01000041d01c030300080c0400c034199920600c1241c01c0404c6103003000781c2903112442d40c3e80990020499038501182c445a01907540c130410000843c8c64000c00e5500d450342d841d01009020000d4080750120b4036401850055000b81d9007001389a884245204a10a110201c405103074400880c400c41c04480c06600c156900e0f0724000030307081807100604008182c01d191001c44035a51102418804100c0300c0c1d41c03d541c0030206141c0150b86001c400700380400352082c104030750410f80c0c0701c2c0c03555800d00c10641d0071104c01950000d005056031000307046c07406a002050b10308500050104921040005000d9084c0e41070f642d460200c40411100060035201c00d500011049811031014012481580d800344160001803080000c040c00740d140c8054060122900001c000c11000e20510050100b03641c4a10600c0300201c10000c0183c0c7c4007400301c02c0c3c82c40d01441034000031a00c0c6200 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 61869400 1250 61868150 61868171
    0x301081504050727050123040b131a0f03030901200f100c0305071701050607030c02190501120e0a0b0a090b070201020c010c0306050306150604030803090d0806030d0e040c030b04 78
    0x580403213900110048100041d980b03c1d000080f038485107003d64030514a00d0081c0114138580703944120f034036000040003104022850a070900945960b00707050241d0800b07401e40d040182c10100741082c0d544030210040d62420b8000340018001d065242e6914042104608810f44e001d101040f034100100d0000c821100d27244d03148008040134240059240b0000707030514010440f0b241c0500804000305140810600c4540c0c04c000138092310741c22801c400d908018401f40c9010141e1103000d044400b05100420b001c400c80e092200141400301446030001010385800311550940e40c0100300c0c2e0310749580c425070442045d06c80450b110003030a020880540311825820900007145d0301540100f200b1540d6400920041060002c02d40465080d8451140c05801c00380019403000c00c002040200f90304001d00f03050402e502d94403080c56941007212084105c2c0d01012444009640095003030f60302040c110000c0020198010b0700401303000070110014080d5860321a40380c00c0b503009400a16001c0c50180c8200000e8015 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 61870506 1106 61869400 61869449
    0x6010902090a0f080f1504050c010f030e030a0804030908030c070513020c06010602070303091418180d080412080c0315060702040216020a080303010815040507 70
    0x85410100704040b8002e02c3d0406040404001e2001c2941c07042142d19100901c0013025102c0c0000e410080054000507410703002032401e183c00c40d8001c12041054025240c000002410380c000440c032070305919409142030f80300794040d540c2d9448080e5241c00b0280c40f072045001321a07407030b002480180258101a4549050b1084e00031006241c410b80d03081940c00c0c0242030b008140141c0040004106042c1e0140c104c07000750040407254141c860000c4001800c003081ca82c1100c070881942000104480c0c0c2c00c03490145060140300a441c1c00441284005110150440702200c0814008000002062003005a14811900d2090303c41c0f03580c6071a11240b064100580d405507000303004005802c0162694006041c0440716880126840780e40c81c410011010342d15003202455500c103000402c085400014100f03032205c200c0c00044455151820014103109a6402590355020101c2240b01440711 = true := by decide +kernel

theorem cover : BRFrame.Cov 61690650 61870506 := by
  have h0 := BRFrame.cov_init 61690650
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61690650 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 61690650 ≤ n) (h2 : n < 61870506) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
