-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5169
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:58:30.861979+00:00
-- url     : https://prove2.me/submissions/8f0f3406-afa5-4b8c-a22f-00bfb645cacc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 929496402 ≤ n < 929676258 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 929497652 1250 929496402 929496431
    0xf060e0d030e010b0402160b09070308131706160f140705060a050c03040b0103020f041107050a050c0409030905151c020d0f0c02101a032d1f0e01 64
    0x56095a100000d588400320007280070b00340141030007400c058500b1072804c49800d54050720341c9030119018080c00d00b0840440c50034202040500f00443c1c120004644815042c506011586024445c0740505103e51105044c080301c0800e0380c50043c442042c2002e0f802c9503068003034032402c000345441d81c1031010300c1d50080c40fa880202d0042010b20b00c12400303400c035460f00c40d51010446101078440500f04c0c409000b004009042c818946056035011030344983c10038108400034002c0d080707000300320300382400100b406d000700000003070108200ca204200317540c0110508020302084030a0514042d000443c0000100203a0400d011008100c0015080341403074100003000c0c821580c00303000580e402d010703400140c0300c640c1d81c0301784108441d502c0940c02c240308448131248003d40d10307a240314440140715a2449a80c00011002c070800851310000350070345200000f40c0c180350300555401c0c400c8001800c00c1c410403080c11000070880d840c5920031002e4070315401c40260f500100910000e05113034015966180110038940 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 929498902 1250 929497652 929497663
    0x5030903122523040302060f0f041d1605160b04050304051210060f06050901180509070c03021606080f07020709021209010b010e060405060c070b0f120708060a030f060e 74
    0x344a031a0400401207854035149440d030350f020a0100e2000600007800140e4400c1c0441d001c1d9142000040d0726900c0710f60501c1f05510556000c000c2d840705184400c4141081e03000782c1486030035081c62045818104480c10394842c8510301c4407075000200307800ba46002031540007140d900709004004881c1055220008101124034552031145c82d40c0c410401385d007407030340540980009001103175040c0765a030345000c4014220380501038265052083d203040381e03100109450200d000a003001401c0b0300040c01c01040140c040440c010003640180600e119031090200c40407012000c0320700c9c90b542c815007036650300008042c02e5000741880086000b0b03a0800294691540050070308400d04008400050038078091041c21140f040b51554107000f600006030507155034180a80d4120340f41940d22581c2c44110609842c01d04006410910300c02c10042074420300b126401024040d0841c107050b101c609900c406d2419101075508441095005c50111010310002d6100d42c40310341c0980c4203801c04204411510031041c01c11 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 929500152 1250 929498902 929498971
    0x3070209070c0b07020304060534030306060f0c080307230307020105100510080a11040314100b15030402010c060204080d11010f1109100903020d0f020a060503090312 73
    0x501d400e4405010b00c02c507105100e400c001c007030000310b242529080024102e8094601d400c22b42c1c1280350314980ca180c22010040030b1001c03040054020800040c80c000c0c0050001e0300941000494a00f006854540102114944c441e04018883c0c20740ea24400c04030784d5003005a13601c0b691007002d404010341980d030183c090350141c41103030004611440d000344441e4104149912081c41541e802550341080c54115041a13080f0a035602c01185541855186403664400d0b80d00c028851103000c0141002c0c02400714010102c998400020301a08600c50100029141030300c0d2000540c00c0104081401036000d480a103006078401d18005d4141030382c407200365040400c01c0404501245411111903600d034801e2056440c100d1001c03008200c02c24048000c6540c45c041c0300640750245907149032403891580900a81c400440c3d0060902d1640d1405181c0b00392100100401240190442d50f404200e050207003044d2842881800011810f103031104241d20b00c0d0001c0904600d01c013403480ba104079a413041e988540040d2 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 929501402 1250 929500152 929500157
    0xe010b07022101021c140f061e0a080d210e060114010320121621150807080d0813020108130c0b0721050426011a040506010201110301090e0307020907 66
    0x1b000c904200c0454103a60003402c250700c0e061182d04004059903041d4502c80c1e0501c0780f01421703d8100f11600412a103a4080e04644101d1250090030b000807540b0850080d10302d030042c1c650b14882c80302d19040e0030607203901c2e074401c98854105030014818441c6600140741c000e8014507010400418002e14880040d4120b4910704100e00c2c001075020402602030009600030550042d1a5201c520501c001000d2080d001e0703e08403460000420041054055001501c0e03110001d114907103000c0c0c1c1c0e440b1455071400548070b44107081c021000c10282032400740c00450f01c944400c0ba81c0385602c00050b0300440301040000c0c400045d88241203000001724001c0c0714840058003614400c84e81e66503050424058500b00e2901c0c01d0006141ca6400c0084603900c0b000756800c90305100b00c2d413804802c10300080c42205603032226948c07941d0704c0e100095410940180c45c07208c00780c03810344081000d611800c1c012400c0c1c4402d4103482018490820041100000301d5102214008000301a00c0c18403040b070f030005010140c141e512100 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 929502652 1250 929501402 929501411
    0xa020c0d060504030f080103150b150a1e050301060f200d08180c0f04181403070c0905060d0212010222031b0806150f06070c0e010b07022101021c 64
    0x1059080305c40c900311035121703081c8003c05600d141c4d11046201691103045800541b610f4509002d03440c2d08000c1e41c2c1003030542000c00c0e11050050401071070300c000c25284c0b00c50042c00a02c40c0001c14040e42c1228140e0f142540c802600904410b42519440081030388030080c0312000c0c0c0100d200e107074244554502c09502d5900e83e105410040146001160b03c1d443c03580c446e801c201e50584041d903d4404d800c145900580e030105910355100444007541002620150403141150180d4102035000710003440081e00c14211202400c0c0c41c1c0000c0b60454a00725a480d4200030100c110b4030142c604040050341240400d40054a40746100180526084140d82c98100d8034030741e103400380200008800000307001c0c206202c882c41f10324a03020703d01e690741070041c2c0456403c91010b032480a541c0c80e960010440e2540c00b0300015615181881c100c40e140f8510710403501070000040010540c074945404844200d0f0700244900c98901188034030240c403145080100140f0740d42000603054005081c0010708101903080c00004 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 929503902 1250 929502652 929502661
    0xa0902150c150105030706020601030f022103030609070e0d0b04241a010c050706030b030102310503060c0702040e100c0903060609020f2208100f06080a020a06050a020c0d0605 77
    0xd20042c0107030040780c840d801c100c074107010040d40051400d0440c0c1d0441e01d0811804028008039002080c644014401000c2d02041d0ba085d0440000040d8010703070307084d11295000d5540d1041110029907030b031700d40d6900c0490758400d640441d581c18115030b0464095042c0c1c120032a2501c401d00d021410101409021540328440c042111a20007620181c80302c080c02c201410443c20b5984948030020390081d0070130315a4614030714180d600c003503054030001c0244580f4048910804801003e9060404241d1041c45180318070104050501146140c000c1c0740a002041c100f03071040e420072010b80244e10b9035203d103120b40382102410032014014940b56031120344440558a041d41000d60544000c0d41102c8806801040301c80d840404070303012240e6100c0d40d00c466070000c41c41c901e40040020315652140041d4417840c058812001484e030302040c62000803c5042080540d00c8080036200d181c044006035000c84800b004101e8507000e40000d107040c4c102031054441e10401c10002035541015020141e40c1e0b00c0c0c0d80d40c00c10 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 929505152 1250 929503902 929503933
    0x10206061f050f0909040804030b061203161b03030c021509010203040302060903010906050109020903010c0905030c091e0c0a03060509040c0308181302090a15080a0902150c 76
    0x55040082038881c0a50070071644200c01c1907003014500041081400604069000c607104152811100c00510030012402c107170a15040300c0d00b1038001070b5900036600e0085400c5182480d54201c140d040d5030302035401c01c2e2482013005015100d5000070345159900d400403490303101d220320740d80000e9440b9865003d011a198010321920710191030003015403410402007000719a80002c1a40c2c01c076a412075031541e49203101130100f4007411300808001c08107410b010001c0b038200010380182c40d9012080c5c2c020050021409022a150007031031248a4154002078440030840c18082240b84d03100190080c001120407203003400075000501144c46088200c008520f12007400c0e4507004030300c014081100c403803816081607102e16198079000d00c0000c06080000600c1007200d050854101c80d0450000c00d4608400302c0b48020f00040e501600f5220300c00c02e4040008100409040000b1100402a50324010303159200d06160000b8502000260381c40581207203003401070100340300188501f6400402030308100c060315404 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 929506402 1250 929505152 929505163
    0x60403060e0607170103050606060703171312020c09061c050a06090507050a0b121008030f0d060b07030804080a140d14180a03031a0402190e040203160e01120c0309020102 75
    0x40135501e031020010008a100000d4032600300000f00e500c45d5440e5414607041c1e964504500c80c2e290040340d80c00c2003203400d0132084038890721319001c2d801508050f156118200c0c1c46002c07100d951a0b109002c00c0208501d07050007616040b29a1000200075181a11910b5003407030504110000c4543d03075124448a0700700318081c40010000d090a48112003030a0820070f003e142409405004a007083c1701800141c080b8140da81d806000b0101c20741a695900c43c1e00035503452650180a501ca121410010001103100000301240d01d4070341c2650b00d074445601e07107546032250f035404607441800700002c01e5406240010381f070004144d0010240310011309024051110840440700a10804101d465000500000c82002c41d01e2103805a040c5400944141b4502a1201c8025800f01d881d030014400b0414080320704041442c604034080380d442d0480440c09030401c02c001d130300c001c0350f05c4818481124106500a8090101d110b084034050408001c191150280b90044032a02001100080e489601c00810b40d60180038 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 929507652 1250 929506402 929506427
    0x15100f050a05060d09050109170726030105190e0a020408010b01020a02060901030207020307120b1f0308570c0d030e06070c030b0a1107150b060403060e0607 69
    0x1201072103146000c000a4580c0500032800041544a02104040000a41c02100c05a501003644804180440d0841c0b42c0c0340c00c04c1100705c904001207280216481c0d690401000c0c102c0365140e400e443c0d0382c20f220a100d5020300000320105104410b62001c21020001015a803060901c410b0040c1c0390b5280c016074900f910600300403941503402c500c20100160b140c2c4021074021030401c0c2005a5a0091031001c83c1c64403070300b5400003080784072900c055001c104409041501404000c0080010203030241c10400d82007001d88002048003404121a070041104440020460080150300044441000d440064900259612145101e10030030031280840c00c54403611241c250b001008124000041001c588603c81c1d10b0300c086d00b485420a44402d190740c5030000c031480c00d0b51100c001c104182e0f4920700300c0f6030300c132095400c45003250510360f09100440d900c0003618041a0042c40380c1d60000d4084400c440208451001d007a040101004040081035050080b600d90100240050241b4a00301000410342c03401c904 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 929508902 1250 929507652 929507659
    0x4030e01050c0a060b060c0f010506090906090601031b0b03041101030c0e06180406080d0c030201060b121803090a0b22031a0903090a090902010807020304060219020315100f05 77
    0x10504088510003d1903010003580401c00088041c50200098aa130203100b003c4809486451415a0500c0c01900000c1c0245420394500000342c6408582ca900c0791401c4402d2420350340b0160040000ca41d43d405540840c0e054942c00110141d2245d450309811f5204036400c1e142000c6402020740a560b040c442d04492540302c1c41c2c120f0f00a4000000101d59118041d00940e501c031500110002c9a03440ba8030190090817244129181c1261000c8003802032071000c00e007640554038000001075230703c040008682060070030400c1c142d400e65a500040e04c40b07250007840d90880344801c0c0421175198440da42c6400150101c410311646525602140c540602080c0d0102d01428044143c10400940c3d40035428680b890350008107003da40d26945028610b010f03402000c3d50000703512000140423015680110aa58000c0e41c0f4807000350b81d01c403003c2e6a41e02c40c2d1304c1040016808051100d00403503000500d035010b140f0003003d031414855008101a01540305680603001402809400c01a40644689200c000c18054 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 929510152 1250 929508902 929508907
    0x110915090609130e01020a080901140705090108090f0613050606060a020c10032a021b030c1207050d11010906020f151305150a0b0936100504030e0105 66
    0x850224030107020b000381140c01a8440440c0c21801c4050b9000064090305100c000c540b00c60308000000e040d9441500c007880d6651030180c4042c00e0024042707566200301441d4954038a0200ca01004454080c0700a12465090042c0240d00903d03510a024281c0607100c03111002c200600142030140c2800c17809000f66101d1042007001c03041d5503401003407042c0c100c00304840e2100e10550b503c40c20b501a00311000e4540003135a40014038091008170030020b44480120f6801c58040f4044520080c0c0c82c0020003c0ca0799150b0304c00700d0f0340082440c00301c0d0b6003000550003500307840c2c20715680c0022805103584403504641004000b8030b48045035030b1026044000342041d00c02803a00c4049090f00c01e4807181310402004910140600144000416000d4810303c40da101040350a01c4400c81c0610742407001c25124818914100000042540f5002c006540541c400d1540c40801c14101d02401213201541758640119844a641100c8261000e11008000c042c80550105441c502880e008002c1102582041e041c480305 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 929511402 1250 929510152 929510167
    0x181e0403030c021501031505341706150904060302060d0b03060906011a0f04150c0b0c070512091504090e060604060b09040506040e0a0c0311120d0f090306110915 71
    0x1010041c0c42c00c482c03c2900060542c5903415404100303c00040340c042d49d0300c451040c09149445141c4003050301e601d580e0301c01200d0080b081c0c8424680e4800e03120359030b0000034103c8042c04980304000030040e080c8000c200140f11940d9030f020409980003414400d00e4684e03038020b0144a81428081c1c03c0d8001c0c5070b04060481507040c0140c2c2c08468400440e80081c1d9003001c141c50941804483c215030142c18104600101c90418110091000406420031034001400d00301041d00c60001d401903403010f40d23112014014240003000303446096040745006641c060000500c4c0110070f400100140090b126042c0c002c0341100c000840f9524001b0040e1046025038905202000700704d20b802c00f590074202d811100410a9203800000401910100c29455401c0c0a404020020003150b64a05030889205802c01d28040c40c00e0010000041081008041d107508000110100c09100b040c12010042250800102543d1240c86034400c507483c0c0c00d18103048480c002500d034445c0c6003000340114072001ca4188580781490 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 929512652 1250 929511402 929511413
    0x60406060504150507030903080408010905120405010509091521070b0702100309150f0b210a2a03030c0303050a0504120e0334060201020306181e0403030c02150103 72
    0x1e069115010000f0105074017041503c80c920200040d41c20040d4203803107548940303d4034002e000c0c1c4030782140c540c401c1015203007200da80041a00c1c1241d030141c40303140c28400e00a0510a4603000144081c00c80c1907111a0091b8595886403070540282154203000c50f03200a400b80d00f49010b8803500a0841e4010034048403006984240300301c5601480341c6004105000e01f071925040030030003030b21480200c80c2084040c031030454099000d2244158112035100b0000b064504120040518a04014403504242801408105046034030400407071620754018120340328001c0e29100c0a4103400413400900c40f06200001e15500d80601c54000500c4442001141420707a01d030000c040a0008100502c030040003190800c0c1e03000e0020b02140000405510079680302c0302001900300240020038101e041c986480860014414800c0c2d80c454440030301940d0040203c07041101c02da08005042e0003001040d2001090880031342040503025900c680c401040d421800c500113802c2c480445440d000344c0c1900c0d00104080390 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 929513902 1250 929512652 929512679
    0x14070608010b07020d03121d07050d02090103060e0709111201060824031501120201091703030a090206090d1209080a0b0c071a07080103020a1d07030b06041d060406060504 75
    0x40d4111303130b5107a161305d683c5000d07554010100c01c080085403809280c14070041c441c0c015208030121800940e151203440301e08020036880d480701d0203500011440010700004c6c5041d84001d024211b008100c1c1c5000d41d40e07803412000c0c0c507d00c0394104e80303010000c0385010710f02d00505c0c0c849001d40071604100d0343c90310304411415410040c10704040400d102e10f0b01450441d4505200e01d02501860400320100c030360b1601547c05840550500890001d04182d100260312034500540052480100010b0740c5151034010f41c5901404204600740d0b0b0041c000c102e06c44023903503140e030961420340c40b8049442d00721000342009445103d15074040d9403135800c1600040c000074501d00440d68890f441e00c0c0c00d25112652820200b052011034244001c0c1400c4060511000135001050181224421070300c04914a032140c0003a0043c4221140c103510b85034414004c00c4030140a6008008140400381c4a541032642c0c46607424602c80308400c0203103401c5800d605100c8503003064010040640640d0500c00d14251900203400c0024 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 929515152 1250 929513902 929513917
    0x807030506061905041a03090c03060421140c0606120102090a05060d090507030302060a1104060f0804051c091703030c0306120304030f080c010b03011a100207090914070608010b 78
    0xf20001024400c00340a1010342e4050110725203600e0b45200c028100041d0ba038425034042c0320b0383c070030800391400300e02d03000603094480e41c0d20a2124100c14148020880c449070140e011000b407003414901c4d80c00c009000c1c0302800b9004a900d004201c3c03420060144030100c904040703031160316401000401c446031140c1103a2001c94100740c45440c0c0e47d003d00c2d4424801000c6041c0002e106014a001c000141640000c142e4001c0401c6da004018142222144400510440c0f0540c008541800c015912642c0101005035109000d04203489403080c400c5034000501c00c80340f800c040480c024140c24024081c40210901401003110003c40c69810200800c0410b07000042c101d6200e4118142406541c000a00950b0300179a400f60110321548480e1504180940180205e001e49600e0120260030914050081c0c14000c060030700c9c01c82c400c03004802486200074100300d820003540701e0301c03034002032071040c900c01c1003c450b000382040040b804903011464203000e69544603404020b48000148030002a0f041200c914 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 929516402 1250 929515152 929515177
    0x90a0905010516112a061e12130c0b16060609050108071a04051c05120a0e04090f0b15091302190b220b1611010507051f060b04060f080703050606 64
    0x103c1c00440001c1d201e031042c1724250016030f1f4012488105134071094060304090b900508081556520140c01d000711010020028003030b9020103c0c04c00168061308000c16104003100e00c02d10302c4900c10f4680c0304c1605c0641e40801b5406540c0d070010030040030305000b0030300941040300c40c0500121141d210346d255401180202403040c03074800c8480c0c1c06c68085070102d03142154130206072000002d04840c405240d0b0403184441010840c40701c2080301e58503052081c00d08c00c6602458160b1a458036480d1002c1c1c2c230350010036110210041c4c04080c0c040741e0304c103051580b040d40340001c00041803500e031046c822002200c2d032a0302c160502c408420321505005205aa0399042401007648200c0501c050a0804076856404898840750024964603401c200c50038194a045c001d03848800d4001c07582c0c004403440c0c811110003604a820021020200441500140c81041c88894010500603100d001c004c20039405903000d20089810041120b0401e50461a52503200d100d9007070070031140c41c203000894650710a10280300b04 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 929517652 1250 929516402 929516473
    0xe01140f09090f150105130603020d03140c07030c050f0414010605130b1804140c0702060705160b1207020d12021c050702031e07080405090a090501051611 68
    0xd01e64108071900981c1c503c0c2e011980750181c0c82220109400c802c0c05194020701140003540c400104078010300c42142d50203410090300b0025610103c0380d40390000042041400c00b000350003241d00003008510080c50064004140081c034040420010500b410446030040e07040c00c0401201162240c4018110303991400e00941d514402d501c907440c20300d007a4200c0c0844642c08103034501e090042402ca41c40c28841503a0412280c002c100e00340e0081c01c4122000b901e21030042012500505006003d4101141b00d42c00701d804144060684407810021a08950700d4070201041560012001c0030302d8030b4003c2980d001501184036044002012042c01d82c01c0309420913000603502001c80d040c41c00c6420301c02e0b08030004011038180403200039140e5029200000901102c4414040d90300290b20031a40c4090b841000c03079260515107001c0c060312402c000c0c520204107a454420700040b030020f00480d8401c1c0b1440d40d502004070b401c020082c05000e0302d1088200c55902c40981d08901101c8150000c3d04800c04001609 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 929518902 1250 929517652 929517661
    0x50615190e0d1a0a1e0c090f060201090b0c0a020c01050313020d050706020f03030c0304030e12010f06030c0801020307080a1a120703030212031b0715150e01140f09 72
    0x40d07600c074000c203455030401003801801050043c005498a2402503000410b8516292003903e40306407105403456100c00043d8900d8210440c034241d22648110300c1905294603d90b81d20322a40041000700d40c46480981d44510180082003403140c100c2d81e100d402406801d0070b008040300025170710307070700703580b00c2818090000003295420030403400074840141e0003804d02c4a004180d25006454520511594016109203c250b90284c84084280ea204e508140c407030505540d00c03034604540c2c0803045a903068029a00403003009042c0710a0103241d040081e114804500701e491490a110740a907582d102041c282d00c1802808079083c0c1c00520706800c650002c0001c150900e5454030800781c001c01e40201a8404030003060714444040215040c1d0071070703000c1e4003620060001201070f0300052000b2542c40d206616880741c4580b0101c1427070040d2104034040d07005078080c1000c0e980b4201c1141c04410001074441c8600700e04010703552401079014090500405800300311403e21000c9000c601075511120311402e402c60004 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 929520152 1250 929518902 929518907
    0x2151302181b121f050301091101021b1e0402070503040b071101140d09060e01020d1d0a03090608070e090c090406050f2409150705010b1c110102011d010c020105061519 74
    0x40e009040002e000300440c490309d1901290002c0c00d60841c5000d40103d1b40019206030151415401c26140903040c0e62554000d1070440c00c1d04903e1010b4242d0082e4240002404a601000500050a11040301c503a464189051409240c1040c5600904000440007810f81010a1000351182c0c48810140800c1174440352070100080c188031381c0d40a00a6100ac00c3c0b0904c10b10041d0005400c45188007050322240c0090102161a1020118080c0216100e060200300e0280f2030b0070704903484030042c6008070301005c060000450089090300c00d8015003601244403c600d2409124100c0203103c110703030444030566100c010a0640c07603806501000d08821703140400441c800f007400c5a01c98180205a0b0200c06000341003551540c11401094503603600c0d100440712075060102051203210389803010b0300314040065542000c50000c50b01c2180c1195200c400087c5501c5c40750100058140c202400440c0c0b01005c404024215900104842d01c00c07810040301e40b5070641803501f252040f00740ea4015508404103080103 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 929521402 1250 929520152 929520211
    0x605031b030a02040e0105060703020706050c07090507090302031e0613080c0d08041208040312050718150f0309020a12050a0f08030f01060e0102151302181b12 70
    0x3050304080000104103181c0a2540140280c6821070100c21580c0d80751024001b0030b029282d00103025a2004030203010041c000c801500020598600715280103445000c0982038400645055012840403141030045103000d101c0c4401c40c3e66a4400824100001044199660b601420b480041070360403072000b0031f02c60104101c59030110660203e0b400c03440070b0f03800101051012901a281102302d100580100d030b00c201c3c43c0328011501542e91071101002d04074407500814016000c0020b01000720400c03922000344004e5403004205100c141140c420056101030031143c204000d0310105498441400010303991030390010140d52002c8600c0281045c240b521500d841c01d9038001030241ca4818048000f0059000019441001134644e8a000342c0d0743c800b4180c41d501d165082c080e001d40c2008007a001300d0112041c500740e1061504400d155481001d030007199400c0000781c2c1105107001c810b02044405001d20002c007030409108031646140c0402e1003110f1400310b401510100c00c56000504004041a010f81e9 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 929522652 1250 929521402 929521441
    0xc03120908031602011b0e0f060910080709170a0b09010213090902030115063e01021213020d0303050606070c06080610080c0706020c030721080c03040309060503 71
    0x800741e40e0f09000a0081070743e046141808015801c2c41d800451a12040329400c1070401d0b42d88404034100c0001007041000170304070b42520f81002d014000011103540310b211a1945540540751001a42040c0c0002420301d1040d4012228401e01d0041c4840b0007000040c2840b42d4a4101400c4116500c6601d80c0300d002e840f404c0c21101410728518400306101e820361780441031040c0b08034000c00c04080508505c03000d144042c8503c0022683c503c80007424034640841140d03080000700c45801003400c00740003100c2c000e00805421034181c0c0d804980110a02440761409400a491002038805414640d001889400440b00018105500e41010501a4540e007007038502c0d030b43c0c1c4040441861601c40310000c1c41c0300f6044421501c0341c044443c120007140d005011250040000c030310058a000216111103000e0344c44030003105290b01c01000b0090110740401014106550001181d40780182080f100520f0400080c05030620316004105010009821102c84001c444090038000d48a6482000d4204400205d91 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 929523902 1250 929522652 929522663
    0x604090b01080d0906020607080a180506190b040501050603040f051501090f0c0c0203120a0c17122212020309090702030d0c09030c14061b10050a0b010c031209 70
    0x4a1454070205040f80b0700c00a070f41d0f503c00c2550340e03803d04a0352694141c3c2e004011401940100d0b83d502c440d80c20000c8d102c8600c0341130042c0e2030404e40e80c00d460190200c4404402016103086846068071034003404c05640c1c012130701800294144070001d08907200250006003614800700d0b80104010080c0708240303901c0f2610300b840009603924003a1801506560012542891601e40030101060058446100094002d4020f104c0a4030210203000b4560007100c0b40380500814410402c0003c6601d0300c0c2d00080282d0a13400d544a4031a41c4010342a50b4000d4005829003425122070b86002e030b40240200d440541184c5c40c0e486000580000740d00f9071140d0311825400c10031030b104216080b40c0020060a484145c400e0801c0045c5a844013290045940d000c018001744030141e0420091500b12105658104000c12041c075000e401103881d01c1c150341100c0724001c1608142c01c00c2089002922500764040380c050000d021051910700000c11029040700011b00b400790106a449000300c0540c4402c00c880d5104 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 929525152 1250 929523902 929523923
    0x910050108011a09070c02220f060504060602030703050f0f040e09060402120a0f06020c16180b0103060b120414011a1302070c060e13090b04031d03070b03060409 71
    0x1d956207030180003e40b250101c00524100645200e0030f01d41c66083c070821403681e07a01803500d0940e003081200038460b4080000310342c00d56034020031103096120f02042c4464000c000208a840c12040c08117030b603203542c000400e41d0418059407002ca5084021641c0c111003040d55180ea54045410800ca40c0c0034580000c030000040404128440c0c2c800100b00740aa40211004400b480340e110200e45d94030101030300207254440c0009403e00144030381e0090054034140d0b5041d41d07a49110b010700c0c08010805030340f02d1064401015010910f041ca01c3c445d6051514007031a09100c42070030206c8400b114801d14011001d482c001d2070004040c02000c00c40e40c20410312490080c0000c2c0802c8040001009610494510421446211420481c128030854468a0703000c403400c2c000030f2130803000b43c5064080c0b80c0030726000008080e03460b015039014030401400503c125000780c09824141801802c0541900c500009a0405040b05442d40e6001800a045501125480c0d03566542d010101e000381208240050000b03058 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 929526402 1250 929525152 929525159
    0x1060b0d020c1209011407020d020d032006060d0f020a03020402030a0207020307140d030807021501181b140d0f020408010c171006050901021f0c110102071a09100501 73
    0x45070010807114014108550300c2074000220400c85104070402180400d00711a00c02c0085a541030192070854001040049204019001708102000d10306003100002d01229000591448554442c0003881e0020014074483c50f0040c04102545001c10001d0300d4800c00343c66076021503880903280d0002c0e5502401c20340d140d080125012002c0e401585e01248070f801200710118010b01611f841d00c68960005080744580525910706881d1039801034440811409150100c02c034480701d01e0200e6000344500c10300400b041c0485c2c0308110443e040c140441a4124100031100c02e0190b01060311782ca07070485a24810b40d9160007086501c0100003000d0203009040c004103000482c21810740c0000415042c0b07840f00800092043c003981c0701e107039003140e01210360000b490b41032010301e202e10040c00e40c403001070048603040c40e403501c0c417048105110300d941e000582c1c64041c0c0c11500c030350041c41281500c49000083d401c00c52541d5481000c0c5400550400c0302c0105c890020700214020410017400d18250181003001d540c4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 929527652 1250 929526402 929526427
    0x1f0305030904270b2a0a030e0309101808011103090705011106040305090d0206030f101d0112020301091410110c0a030f2f0f030c1c0201060b 62
    0x405030003940b050f4605030ba8003541e00c108070300c0e07091110354070792884600c0c001d2075844041d01d42c00a80358001e01c903a05000c1090450240004064a041400002d900d501c020203008081d24030014044041340c03c1803100a03099112401c0b410b203040780b80d0a0001b940d0410368040d080912165003c40d180b036090440c0c0015110701180190b02801d03850094510494580c4015548070010b111018031941c41200002c010900c0b58000d400d138000700131b01081c0d01c076405da000035040c1d810580700382072074a010609100c4d2140554051600804842a03043c00182c0b140c0b003510300540d0140300f25025a41c98944420455400394086640541d005040c440c11601c1c1519196a503441516080440c510703004140400d40c10020686800b0142c140080c2040e81682c0c2e000c51b00a00a0b20f40402480041844170702910b03035140c100070390030050022041d11080c1c1c4020442c940440749443d0780300b0350810000000d020101244c50078840900220403580c041c12a08101c0c010004c0d075100c1c140c407041c0031410000091 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 929528902 1250 929527652 929527657
    0x8010801231341033105041d0f06061014130b0a0e040b0f040c0c05010e030a02060a0605010906230301091b090b0405130b03030a0e0a121101081f030503 67
    0x11083c0d0a0a96058080000b65a8801d9410940c440407a40000300740009880b0100072440300001350001c8142c0d502ca020506840aa8481c2c418601d41a030b01604001400c11080c003101d8030800041000c2d0402001040f202c0711802c0000c401c020104510409010004c0c08884e8400d14048124814550b41c00100816400c28422036000850301103000da51071a050141c0807941c13600400300c01c00d061040f01040005e14803440207406020a070710000d00400c400717204104201041c6009180c2e40d4620b03000090601e10002c0404035054640072051210380d90107021081542c0307030780c14164909114001210901d201c000101c0c10103480000020440e5212908240c0310b8000c000160b03d00c0b04594103058070100424010000e481c40c0034801000680341c8808102a00320b00c110002480d50900000300f4190352103c000b51000c1216041c0034101400c01c9284c85009103141c0c0038051000d00d090f41c856070604401889503040010084c045006802c0400084503882240641000803960741d191407070326038 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 929530152 1250 929528902 929528993
    0x9030d1112030105090f1306240504060e01030f020d0b100311030609100b0a0302031c09050d030c15180c0504110405150a020c060406080108012313 65
    0x90007124030400036030124400307580c103803000200941e103241d0b1041958445d0400040c0119542d0100300001c8000c54403d01c00c0513420000701e180da150011106140031800181540000d001f20f1800d0810400280d5410005054a61045402941140c0350000031840f0303e02110140907818a2014050081e00a040345000c507480381c0011a8003810403010180c41d90012126101150008032112121130450b900034102000c000317050b1312250380c07a50040b0b441e00d00c1c00100e203450030092401e800300807900040c0d10401041c04480341c0c8903001c1e1960700140540d804840091205a8200c1c1071413103e0103070380080c81c0c50610700e12003c00b414460708242d00d40e030320603101d40307401540390150241d00200d402084806685d0b01600b902c0611803040010300b05c0e90700c840036140450058811041d2103a03a10701c000c1c8010507056450324105d5040810840c01c5541815401ca03580254034030822001b20840da0b025807110341c509100411084a09100c0e684040c41b070100120000c1400442c00c078909040740202c02c1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 929531402 1250 929530152 929530187
    0x304030c0212070821031302012f1c1704020114070501050a14010602210c12130501030902101b0b09010c3221190e0a0b1303030209030d 60
    0x40f224045d0301d0740f420218500c0b085452840030000603a0a416011103140f03054070604d8804581d01c0c01245011400004003540540e84000300407204041c001000041112401c00100600700b080030342c1c1c090400114441c5046680d170400c5c00080030342e80603a92511380002a01e240c247e07110036510f020ba009140403620f5060f242e147c520700c25981000ca020341c81c1602da150b0001c200701c4805101c4072840800d405c1400301c2103034080000d580264010f21039450002c80802c0140d440305020b0481c403c0c00745058101c5030406140024400251707070340c80440344054070941450040108441d20780070401102e010301515190a0000380041007105500c0740f101841a80e494080c10303405d4214800c1030034a642920900020150f060b082c02c405140c00800b0030001c0000c0da2401006640d40040007468100c80c001001d040401ca0181032420500074000840480d030302800d00149103580f08440801c01412201e07901e0b074000e070148205030103641102d206a0004045890340c500382c140080400d004213250502c03 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 929532652 1250 929531402 929531413
    0xc031204051005010f0603020c0f10060501091215090201020f0106150e04090209040b0c0412080307080705120718080717070f03030509101403040302060f0112170304030c02120708 79
    0x802a095204442c142c50103a00c81200701860420700311f01940000e800700c249801028480001014200008820511100c070086140307132400c0c1c005046007076203900041300074001541c20300000341d00c4980c007048107280003400198400c42d0f0004074a0721130401c100300c01541c0303801400300d105c44058903009018092544c3d4140103140b280c0900c81900c07540c3c00c2c020341011844c03020500141b00300c00c032170794085070701814581007961b070b5608441101000001034961050000502420540c00740c1180d030b000c007042c10014500110700c6944d80f821000241428104030400c000c0361540721040341900c0007401e0420440b0112510748902c403c03019031500516241d032084400001c0d5012001081d0301c122901901c4680c2014206414403818020b401202000c1229180c00380401c0050000958011800380d0f005140070318010030460146041038104007000134401c04030000041e00206c54000c140708000c552901e035113039868251600428844001e6010240d2614410308000000d100b10884d80e10104991 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 929533902 1250 929532652 929532673
    0xe011b0f0c05040f05160c02030712080f1615050f0417040f140f09010501080a0905010219030504030201051b0720040c05071506061b1403030702070602070b03070801031203020c03120405 82
    0x215156887c080003901604400002c100711000c41c03619101c0c00380250021443d20409159008540d84a200340c030001000150f010414409568144244600100c4003003100d400d0690360304010440c000e000a01401c08a00d40340215210719040c0c40c001c4c5501c0c50340d50344640d00c809100000c1015003921a008949a00d0742d842c0a241000545d0f04a403010707110440e05464002074000036150040c01998550340070400c80641c1d40c140418048200190780c1d0000340c0d410540750090a5034806091ba054400368600f00c449603136081811508000e601c841210b142da100e11880322000c07100400c1042d84145014100400300d908940146800d51003005c0b00d07000b80c0d18070388070700041360201d0040c0320000301008040d0080c08070a00740320320070714002d501520301c004d5075120750780c078550003201c0c45401600070350300401c00941c041203520050100c60602c0d9066240c81f01005000440520010340b04081082214426a000b0b504403240c0114001c2901d40d0f03a21200502440384c82c4c242c0b4112010b209184050 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 929535152 1250 929533902 929533907
    0x120a02010b1c120503040507050618040e0d02030414031c02030309070602030f09040216021306170c031c17040503031006021b0103020a051303120e011b0f0c05040f0516 74
    0x720526540408580c03d08002d04004503160307040103000b19142e214065000c912540c030301c006004100b05903071a502818010a0900095a8900b81c043d1050307402040340e105156008000d503400d40b5103a005203588041d85500003132408030a40c0301155024401c502c013040c410740c003000031031098140408591002c0c0c1c0d940703002c0b40c0e079100c0c0080c1e50111080921412419140030b4001f44000f06541c02c00101c07010b140c0c1c0004920402c1d581603034103002d0390307440b003042203900581100c0507010800010b00819080d000c0401d80350200c1c19204487c1c08104240b9480c9a4005c5600800f010207000040c041494039250a40e034a078000e58881600c40e03903250f000203941d4400915407440081080c0036180e40007180c00150080d4100d806640b050240503c444050990600502802180248002d0030500901ea6015060542d00007441d8104100420041e40c11b0310385119241059610001c00e00500700e075070414001c9241a50880c99005040103000303980584181c000c103008203108001c1c41901072844609 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 929536402 1250 929535152 929535199
    0x40605070c030f0f120e1f110d05060301060b31030f0222090606140603100e0606070807151d0a14030714070612140105040905120a02010b 61
    0x2400a03403401ca10f2807000d071150070240f02c0040300c0e0421202a48080304244240c610244000301c0c10783c8a202c86000004810380003102c00030401d01c081028407400c0d0f20800540c400c00700440c81040c2c884020828a4400b5804a07006200807145140ca92120207041491342c00300d5400b540e100110b40b9808004101d885005004580c0d100c00d078190010081e80c00e00c84aa542c4200d001242c04000000c1300e0203a602c0d00070400c00c14414000014802d0400c03484a001c900c0081e139450264100784100030110746d000704448150f0315903a881c180e031584e6160008010b442149401400c0764000b140e040d0811003034500c0000d0041d4145810704c5000c1c110501a0240c40c50040070301019400b40f41d481c00403a40180c0d40c41c00b0040e080c000d403454603a05440b40d9000215804500345030342c2c0020030800c10603602100c0c00b1901e0303030351840510096442101d41d0303107200018040c242c8903e03543d030540010440200844101d090440c18001c0d103821010707a01900034100e18040c0c902400c1c0399060800d548a81341d00 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 929537652 1250 929536402 929536427
    0x21c020f0318060c030402120f0726161707051c020418230f030f040f08030a02070b0a02010b130e0714060d050c0c07030606090c0c05070e06131404060507 68
    0x4255003103075070b20340070800d4501403801020001c9c02091510716543e80309103e0b0f040a00035140748290b07900d12181680340e80d92082005001c46070408a00e801001000a2011080b02c00007010640d20741c20707680d1120705101181e8001d940c000c110a0150252040400b0030f04040d030f00880c0c1c204040ca40c050b81e10b0040f1246404028441900c080d203991002c03405116180180c687c0302c00306ca0300c1d8a0303414900c070700c0c43e4030110308103080c0c0c1d2020030704109800410310101e01a14440002c1c500341400000c01139580c0031913015210350481c000c0765001c581403003540702c0d2800d10401001100c50b0316010b10f20b08024059480307440500d00400700080384260410202c401c80440141c07000d450010031580e80710081101510004072000e08115a0b00e001900b041510055809560b00081291600d4040f0341122a03032031352001480210a101c0f0085400407459200b2036440c3e0700c11031050794400c00014621015280a00c0c2002e140c901c040d41100401002244500e203d0001004140c4a194090b00e10400000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 929538902 1250 929537652 929537671
    0xf05010f1107030803130804030f05010b010906020a03050307210b090907052211030a020c070e0603061614040e041208060603220b1302180c0d021c020f031806 70
    0x802c1000040c0031040110b0f44641a5050040200d509580e01c6e0080c1e801a8000c1c0d55406000c40c00d003091000a2041c0030319000300342896a900c51070048040d44502c084139000d42408004000034103501c1c06281d4001951413800c9032032103035a00140c0c600000b0102ea40b1028010f41045002a400355000030b1550b060b0342004210f1000030101000c3c507070201e0020025908041e441c0e007200f0140c1012000910b001e100d6202740540c4030b54610080501d00340d010303480720300441100c00600c2550380700421041e4210004000d140c5689032001c5068030b1060100016100d00c00c00002c00190b40040158510301580c03050b03084c0020f1400e80082120000300696034503600440800103c1c44521000512a003031207400d44c0d4040030f5003029121401044002c0300c0e844c0c1d0345081034800d1011840c09044412000451761412002800c00410000e03450003032440322650301d5030001b000d400d40300702109040d5401a000030155950074400c079016019804c1520114200c500e0461803c4255030080343c114822446071 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 929540152 1250 929538902 929538913
    0x2c0d060e030906070819020703031b02030a0b07050406080f07051b010b0a0b0304020103050604110d1814070501020d0c05060c21070915020a02090708091002040f05010f11 75
    0x544411004215501403000540300c10486181140c032100e02a1074010f000d4030350907468481d851000c0c40702000c907150000454020382d1060000a4018441034258401c4156403141c1c4030252000c00e1601d0607140024054810120410030415408001023040d112259107c0201e510760f90b65002071041c0c2990310002041062043c1e4804102c00c000d240c0415001a001040b17a0341010b01161022400750404030f20064000708010940d41c041c0669038006005850400c54500e08940305100760148032840281552691410903e0400340c034125008240c0200010310b5022a0240890b6074450342d115090250088010400c00d003030041180c65440354106024010b2540c9030301904403203500101820403034160f10308180c80007205041010f8403805490320380003c07050810f0809000c403245200c81c2d808640c0042500070060b2610b02240c1d030042260309243e0100e4070342d000b0345414200e003401c030b030101d01c0d00c00324000034842381e07541025040f1142a215444950b44007681141c034011007054000d16a84035 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 929541402 1250 929540152 929540179
    0x9121b0f0f090c161208150108160203210906010f080319050c0d03050402010305011710110903030a0c03080117150903040b070c0311040e070605071b062c 68
    0x80180d40e00403c890689898030103442201128035414034030641d0301d1501d442001340c40a0304128915004034245504811800340080000e08481000302010300d8032a5000139070b04050b0003001641c0d0480301c0c0500b003500c0c44004014092910b01d08507003040d03d03403040100015840b4110030b03010050307a10100c0694500b04400d005032003030703c080e000510f040040400c0010000201030003a080c201c81a0b9402095604090000605a98041e00085031541d0103410303040492070300050203020b200e0a00d00200320507000d5100c16406008007140107405000004140403001d600a5400198520a80780c0d2040d40c0d03200e542d103a8041c0c444074841142c2ea4000c407101922070361400c08899100403088220307442c194407121b035684240c100e15801c03505429042014000c1081203800d404110201750303000c100b90310741c25081c0c50313030341c2074510464080c0400040d80c9810701491104440c84c05407603c408003030503035035400e004021501610b01006101d150729449500100c3d0301d404c600b003003a0020f012800c40400c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 929542652 1250 929541402 929541409
    0x5120708120601180801090b0901051005040b0d02090c03040611033102060d02043015141914060915010c0b090f070b09031f0209121b0f0f 61
    0x409408981400701100a850880c00703899204c0b00070b044113400210380758a44e4981142d8101c0080c144812a904000c100007152648424190407140304807404909480c4c0c40b80480d8014a000707102941202c03581c020003042a100000541c0100e00c1000c08003c1c2c07070040c0b082102d8500058840103a082c2e46245220018003444200607142d600c1007100080c01289903002500a6012400014080d0740125040042641421140d203035282026014400c6641c0e00707200300300c1d100010344018018075100c072142d48044907a6119148072452480c0e501f07032504001c281e0554481100c100500c2403801d00d0300c46100b00302c022041e5801440003034040511a02c0e540004100702d03420303554403810010b01120701030101e490300413071900809001028050155610407008c1c01c16a0300e400c0228101820011003015480000d880d6130441b40194440641d0900000300102a101e1340400a601001100d03111030703802c3d4041303a202e81011f02040c0710500c1c04401010b110415585404031035110583c15011400c03400e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 929543902 1250 929542652 929542687
    0x1005040f02090d0309060e0f0303070311100204030804030606051228020d0c0608130816020604030203031210090c050304080f3a0e0c01120b04020a0c05120708 70
    0x880d000000d824104040b002c200700190400c03082e00051140f04041000680020500d540d01c0030a442c001c1c88070350110042566481001d80090801c104090340c40200078007403002e00b5001f080c0c0e0700199695035036424862901d400c140400c2d00d4071480c0043c004ce441c900b04644040308800d081c082d00c4800a03200807000524482d00248041e010300c084500c005982ea44109240c091142254080f514180071008040001c010001880c926940c0c0d14030340424600015078001c6035204d0750070f003105415440422443d0146a00080d0580f0000c10161128200000c00d64400c44660011060346507895021400b902c4182240a0105a0030008540801c001c6c0c402081c480076650003441c40d0480641422900209a00704101c42e4020006181d5012540c4480d407050500b508500b8804410741c003403e80d80750020003100c81e06201910b0124480b4821940102e402c8400c020801c40d11040421800740c190202c0f008210303400d000760b0000d4004801503609480d840c0703400c11825824041e07003890140402 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 929545152 1250 929543902 929543921
    0x13050d1a07090f0e040c0e0601021e03040512060f061c111f090312020105040b07080702070803030c0405030f01060b041707030b0c0c10140c0d02090904210206100504 73
    0x10000b01408904400030f080410002e09110000b440c1c9441d190a140640e44880d8120411041c0080300b4041e16170303400141150390034007404824440e0080d00b40703050318520482d4095500500184110030b0540350118505120b1001140039074041d5803000100b10700e44401540c4103c40300400100903004c10802c0699641c01c400141c050840c4a4010003481901d91107031030b0a80018241010920412281da9009441440380b400240020700b000c0d0341d481c0400f18020000c804001c2014005014940300701710010041150000b96541c034102101940e029078028016203010703104400801d081e15105101d0081250111900a401c2a05100c0443ca00c1000901c104160340314000e404000f096034151214099003200401c142d40d0f009aa9246003015580084182c40710318080d80d08102c200340e803c0c00d030fa00000c0c4d45080741e41c80b10348182000c000e010b2005855004a42c00c0300b0442000b0410a0398141c804001420b5030700d8600c1807034126a61001250256003900b5003e008100c5401c1a030009883c4 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 929546402 1250 929545152 929545157
    0x15010206060907091a07060e060103051b06180102011d1606090b0406051e03070c061b0804110d0b040b060102011103220c0302042a030e120706060b07060213050d1a07 73
    0x3040c0746c684806040c0c03000c0c40031140d916001300004104005040200b4840703801034400c042e81002c0040c0026199000710031001c840100c040ea4030701d0340790b0300c02e500099800f810700d040402e01041280b0280d40d110607070f4150400c056052000419260f0060010204075410031541d2450309042c03030011103454100700c0d00034540311049221203c004c80e0f040040c6203c0c14856482c1c102c0440c103410f00c030081da0050b400c044011011591006c59041d40560304a40c4130350419180804181440301203403440004020280c000003004041c8030400040902d654000c00c800d9000b0311566041c0e940079041403000782c07845115000f00300111054800307008003125005d0300582c4006400c1e6900d40118060390000e803410f401041c1d503628401401108001c54482c801c61600d410000f501c01c0c0e1143c656540d407200b8042c2c4248402187c001e0800c0f07200d401101c003401e0130301c1d00c0a44840c0c40307142410203904807040e2107040594030740300411142000f0080d0f140c0349411000c265030f0f41d2040d4803241040c41014009908 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 929547652 1250 929546402 929546407
    0x130602271816020c18100b161205090315011d060a0e07120c020c01030e07080d140d020403030203030a0b09071704030e03160311030304030c270515010206060907091a 73
    0x1c0c5542e98410344d031540c164080c14040c240c80c000302500c01b040d001d600304100d00c10301441040580c0c8540d0001c135101c240d01c03446024900c1808641958140501c3e42c13500d1b0306200340965040981c5030042003504880e46010100200c03004404242c0b40c085040340e4040e0022a00c100400080310308018080c1c119619043c811a400c0d4402300080581d40103510001c056031284140c00495689480352912000a02014050075810000c500343c8070380b8030300031706020010601030f0950203403900c8045a030f9004401004540d90359032458040c0d00c0ea00226044154240f8211044910341070240d04180316895540c0d80522068215020f61094040500181c0420960314041340c1541c07010042c21170925520003c50440900d90704d0700c0c104256401e6032403406504280310400025113040c0c081030990b0441c1800070402c80122a42058200712001501032060604082c864840b901c4441d5100c1901c003a401d48003185d0f00c5000740180c6d15016140400003550b0090208640c100111040c0c04000307000c0790591 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 929548902 1250 929547652 929547673
    0x603021507032a140d020303160908010c09030c0e010302010212031e040b18010209060a2d23070f060b040e0a06020301060f080c0702010813060227181602 68
    0x458128158074091000304007110f03003c1402001d50314501c010708800005c0107500e9100e0f000030746070300028004115510622008010b40742c0602c0c50040a045000f000f005001c901550083c185042440141c9071000300200100d12030509031541416660180c008203600748015800021582c130080503541544900d429a58804821640c1c1601550240100400504011001c014806410500880c450303104000c0d40318035498030b10940d400040141480c208180681c0541c0705840031910030880e65224890307501c01a40e4000f4100a409150009000300e02109960042d0982c4180f0718054000d144084a1000240c070380d800503d45040f001d000071443c1846485903602c0c0008541c01281d110f82c0100040c009643d1100c0c03074017044021071408041500344002100850f202c3e0143c003030b0400c02042c000a03106840520300308026039110800310340c0c90546030000c01034244504800c0e40c0307000b18030440c6055071030404030645c01950a00d50f1032002d80ca4100d07001d409084102078500c01c2d40128071100 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 929550152 1250 929548902 929548937
    0x17070c0816060606031b08011202150c012007030c061e09050f06090105040b1f230312090a050402071103060f010f120f0b090c120a15060302150703 65
    0xc48401d4402c00000c40c0ba03d040c404040c0603903c0102101503200c01e921100d41030075601c0310540d0b0440e15080d031550807002c451f0021820454040040820203840069201c1255205612081905098034600030306040d0340e4400030600e204209002d4005403200d005000030551079400002d0b40c40740310a040c2203400c0903129150589542c4203080d00c0300d410000504080000500034680e025140c00b0003001907142039518201c1020007d4040240c0403a803400d400d080240b9611203002074100020007101c43c0650b08040766144149000550180c0100040841040d11200a80c0c00c1d0000c0240300d0000c031410203083c03000940182000765020300946030143d030740b610705000b6140141d19000d485035a035810200603928034201c95004400c0b4020504a0a01245404950280c050b500810035040c607210703076000b280340c10580520598020b035001068a1030075800112401a584210098002c1d00304e1191540e0803102c0510001e50041d080d2108507070b000107008002c000082c864184104c0703800140200 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 929551402 1250 929550152 929550187
    0xa020306090109020a0b09101b0b011202010f140a0c0609020a030b09070608090c01050a110d02010f0c0e0d02220f09060506031b0111030906070c0f050117070c08 71
    0x78600c6941d1941c00340c05605010001c03c0140c0b1103812080e2400c890f101c04100700103600005401005540c40038011020544081c00c0b640d07940042070351646503180e0560b05241c15445c1001c90100d41000c0e0301d188110b01403c0c104c5804880640c607a13003404400390064403651441d100890b101650741c2d280c4001640c40500d0900070310f026603a110450300d040707240f10303103058029004002484004002c00c0004440051050a840300c00c0c80e201e62a40708950090f6800240c02100c154640524184104220341c1507002800c9090503403400e021501210304150b5144002c071f01040d0308410341001c1840581007140b28850401c207048690a15034004418400483c0c4000180103a100c0e12060744405108030350040c40d80080003100035060051351040b00080b185070f07031049103044c0074100f0755000805105100b6036040980c06000d440d62422586412100c0305640d0141a42c0c2510100b00410750354864510800c28011034104560700f6110f401c405e841000d40828201d0b00c6000400c20400c941d85110030 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 929552652 1250 929551402 929551411
    0x1e0402061e0313050f120913060302060318100b01050f0703200d020106050109050603060f010908030c0a0b07090803031f0b0a0c170f1804020c1618020f04170a020306 73
    0x140f0180c5000146081c5040410010700900203030300801030a000c910032074007240d04040f011620001c9404214000c8405400540d2010354801c0303022081050320351000345200704488005060f00c07209040c800c2000101c54111a982d03000800901260207410302e01300051158030301a084c540c404076241d860b1043c100300c504120001d01c1d0007480c803056403a0740902461000d00024200b245101d03080c03201140e200c5c00020700070380c4a41c41e400c0300740c10b260b4010b01c5144080c01a0106480e0382d8020006503680ea01700b0754500700c902a08550000e462503201d50290400c2d580c03980060351954403281d007a400c20055104881c407409950103000180c86410700010106058980c0f2059290416814550410441d0142d40001c140d02044400c4262a400080350390304500c0e851a4801c0001c8030340441e00a004a4040196074802c0d080303a0040c0c405041a50b00407640c0c0d442049030096480383c804826030003040b2848540c500c2c1400140708083c0008802c0c47c1000c0d024040394003043c15600005d161150517039 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 929553902 1250 929552652 929552671
    0x30605131b0305060c04140607150501121511120a0b0a060f030b040b21070f0306021209011806050603030c010c03022502030d0309080d11121e0402061e03 68
    0x740c04008220b402d0085a80c0002400071244c100351070860640070740c0d00c001403128401c2000184480400000b50b0071401a000070304010021581c4030031000b100e0603140d26007602d26600d400c1042d01421081d01400d010215450462821b05003100d07040884580c2c058aa902e0003a15a4903006003503c81c0c641c4100281820380d0b41c019009044034018003250071604d02c0303e002e0b03410f2085118480d1102d5240c1c1101d8a8101c020500748510403c1550a01a142e0401801e400c41c4010000a07c0480e4003d406002070f034001c2864035840c0c0d04a098202c40442c2040c80c40154072003003100100d40280c4c4483d0b808100039040e2481c3c94208001d050071036450840650100c1e034041019913445428100c0c210201049208101c0d20811135000607a8031000700410208140e00c0e20610740410003680245e0320b0281d0303800d40c284100b4444a01c0800560441c0c0942c5007121140d600003001007000016206c000c8007510a404003a44039a024407016a01249990340e480015080802081e11814029031142079130341e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 929555152 1250 929553902 929553953
    0x504051e07020a06062306031902030103050309090705030717102105010506100c060b04020f1204020f0406210203030c0a0b0f071e0c051018031103040f03060513 71
    0x6182660803558503070405203c6d6204004181e40104402000000151007146c0c0c96441e581c80844101304106084c3d8509810341c0040300010400400001406a0281c01c8800c44131950b268107003103d147c0012603800c000a550500c110041c00451440c068102c0000400c82913255280c0c0460080d4001c0d00302044c0c5500b09500078101444002e1103003d41045c3d085031100420200170400070506a00e0b01c00c0a800140e4814208605a8680d41200d8200500c0040c01352940882e40c580d04030b491045806a01401d0030b000456010300d4503102d10700644491680618403d043d02c20b62444001101904036054407041115444643e0100000654030784550402180d0f843c00d52000c40d05401c02800040900158124100c19030340d401d41440443e0415141841030554581422841c06955400c031141d001e1070f105040f105100c400050b141090300a450312585100490101e641d20322a9120740080c0c03c5480b103080c40043c60325001241c00c014036181500c004c10954484442440020300311482540c000c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 929556402 1250 929555152 929555173
    0xf0403030c03022a030601081b0f0301151d0106050a050d0507030f050c04030c08010b0a120809040204060f0f0c020907031d0303010906230307030210031518061e0504051e0702 77
    0x40000707d0142801c2c501909100201c04584001c04510038a200d2080c00e022030f1001050710b00350700c8075240301c0d6880507454000399522030302c080f00140c241240120b01c12000010881c01d000340100d41102c078265a402e86007400f000032200040c5070141c0810201a01d40d8a440303198001800303030381d01850b06850225555451403501002900c2c4540c0080901c1c0d040c20f400b042140c3d9910140340454861190454100718a0b25181c80d161050f800d140b43e12a101050110b2400c1d03205100189480007a22140140749000b0302c1030b43d01103604403000b0351200041c030000700d00d10301c01d420a00c00500a5150020002e4440303010340d04540098120385840e6544117000c010610030200c20454060a4110700e21020301442c1c0480d03200c2825001c0a40281110200306900e00e1080e4401d503c11018500749203041a250300707a2100951200e44084030480c204240480c100c0c2a5107003013030034020400250340e031181c034145c184809040300800c619200d0703144007003104c0d40302a0009242d01c0303000303240c0c0036152100c4d0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 929557652 1250 929556402 929556409
    0x1f150f050f090c03040212120c0114070203030f01090b010903050a0b09010b09090303311202060a020c0304091122060813031704060204050a030c09110f0403030c03022a 74
    0x7900102244100046814001c0c01c3c504801129041034054940074030600040030a1031401050b0a8040d015203000a510440e0030410761001611503c144160407183e00d543c8401c030b0b0b0f20301094900c82d451103030341001003007541d0312036000c80048070041c148562203e41d20f840752400d02441d05015a17420085404001c00f2000030f202da00c100080884803040c442c14a50481d680d24003005110440c040c2050410300311044400d405021001c8a40510018032000303442c09504c01c003650070511016108031408901030844074006d031298441a02d00640c00c2514014502003d007a49061070920396000b0032542600d80c61030035025500302c8010a14030100d0307103000c90003003138204024007100c1e030303143d1807500000000e0380041c404108051500711500180c45c1c0703052170310080c4902c2d481070798011040c450010801600c008107a040312201c550420004503591150001485080414480558104006d20009003d860454003040c001c1c41250040b14250544032000c5c82e40050142c14031000f140e02480516 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 929558902 1250 929557652 929557669
    0x1801030b06030a0f0f08040e1306060902270f040504030f08090118060203060a08030c0a05010b030f0c010c05010905030a03020306210c040b0f1e030601120201021f150f05 75
    0x2070064000b8224008103032941490082c202200510b5030542c00701c030609000b4010b0945001e0400314051380c2c00c1d42002402c078049107038803d408443c2c3c1801c0110001d10308499109648085001142c4c160307156200c0000c280c0480e1500c61810b9014002ca280d020b50b41e01c4522555206502c1b07a1680d140c903081c69400a000040002c1015001ea8105813031904140c000000401140b41e01481c0985c417500c40e24001001c0035442d8008000d944400305072420000d000085c8000b46500600003081008140c805050301c5017100300c1d81004c01c2c0d006808519165108599824210b40100000a43d017039443d500c260840d0321681001c00020b0f000300620040c0c1c0350004102c140c0080000740704100d0541804030f691074944182d0380f281301d65a104107004098a4241021b075403058001c110301e03490040c6070000e1034810300d4445001d000b4460035002007030b1102c504484000c0190141c0050845003c0c80c000642d0440005904064103a22000c18441e03058060003030300c0c05042d0030080282811304010500c000c0340d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 929560152 1250 929558902 929558911
    0x604020a09152a020109061209140c011d090f1306020a0215090a050709240b0a030e0303090606090c09091302090a02090915010e06030a140709030308241801030b 71
    0x420f42400200180e030045890411500315080c50041c0c94079005500c80140460b0a0140c01075005280314186070350082019210f2240c05d0300c5401035a00e0840f919000d03800150b01e0203030020a20004511107101600c02d280d40204c184900b89501c0c80103079600f60130398108200300000740c4e00015181a900d00b01020981d846410980106524020b42c0c581c10b40c2c4642910032009941c0e0307100380781c503408100700c1c0541c20150b03520700a075403806503500711280e0945c0c040804140081d1403d07440034070524012048038000c854200c0100503039240c001c10082d0079040940145031148003040307881c040b51600c652241c821400e030300b0340e403c141e09140140034483c00001c280e000582e10401600390190b4801144030740107090340c8024244507018100585251082041d19503004034044108458005242c0005030003103c2008140d050341c86074541581e85110900009003c01c02e5800007030300c0c01c0c2c040142c080c3d0503034120f10b80e610040d112902254070400c2c542c00d01e2520f16122030052040c80700300111584c00 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 929561402 1250 929560152 929560217
    0x40b1504142d01140f04180501080109030503041e02040603050f0f0d0f054b03060f01050711130c1b02060403082101150f020d080604020a0915 63
    0x10b0011404142d030064204100e200e050181500c41e10001043c10000e803011007009031800303035865455131003840d9251000024540036034100000800c0c0e05006002d044041681500d820341152502c0e91203862220009510060385602d650354000580d41e1402040000e5005001400d060107050260a0034807560408660071a4014a410005250701c002c614991080720716100e41c5a0100e140401c1003c03034081c08010071a4102c3c0392048184048107844014013000b0030b030504044030240c1c3c0d001c10500003200c5155100801c400036461550062006100341841041581c1c00115584006076854421000c205045640c1d03002c010101c0f900544060b80512080000c4001c584a660000361a4411400010035003500400d40c0e40f542e1800045c6294061583c801d10314032903071900e201c1140540360300d0094002411004502d4161400411000a200d0242c3d450290075554207081c080a9400681c00404124070402e00040c0c042c02005841b03240c0d203460b44c07040c05c2c00b18900450400c440510305100302 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 929562652 1250 929561402 929561449
    0x140405010323030d05011d0703050f01050108060103020d09080d2a0f0203130303050a1d0109030339021807050a030c0306150801080d020a11040b150414 67
    0x2040841c01c40342c194021004100c0b0303101c0400c481c1c031030850160080310b15940b4200000860300034820000104600f03824001802d1540e0381220403030641d84140d0f0074000600110300140b08551042d002158800f1041c10050714058040304120100e03038540d2829200c8840120303100030640b107507004250342068611b050709103101e08030301302d2114858004403450070302c1000410411041d000307209903071102c1e501c1382e0352800d120b41c0c901b00071b40903a00c502c415000203880c1d078a0881410080b4041000c498406a5420410906540d02929202c0000e0140d40c815210442c1c0701407020340c8900420650600c002c440300702038107284140720b607054440b0040b00d02001c4140c20440d000e90300c4019104110150329001c2491a04c006041e0010b1015811017201610f0080494451580102d460b41c12900750b041140c05400207440d04a840b0354440c200203001342990302c00740d801d038501600000481a801002d408005400a2850bc1c0642c8035900c6090421400c001c040c0c180c1c070b000014081c4040c4d40001e03102 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 929563902 1250 929562652 929562659
    0xd1217070f12091109130203060c0c0d0c150e010b2106131a042015070f061b0f0207090902060316035004030f020a060f020414040501 59
    0xd041e0000b035200a0b1031141d0303034200d030824001c0076141010200c070007501810700ca00b0070108811002d03001c104143d000344144804547d07110500401c491180400c00003516545121601c1103030399044000045d10001e68079500c0041d0400d880c4581c050801d0007000004440e858407050002c84101110b03103d07502d4040f090204840d000100b01a43c1c040e00c40420528100e0380703458890aa400b40140110000c40c058003008104414403a500102210513a66044042c00300d801700403103c00c40b0440c21018620601c01e00e4009520390558900a5105541c049621603110140b00000c000c0881980001078051102c40305854061202030041d0400080510844640d5004510b841c400a45281580c0b280d0100c00da0716a4401e9118412642103c103a0b5001175480300381d003c05550903140c0c83e49240c4042110050220f00314540c17042d00514440660120381c0c0c0d9501e0646002003800d00b01d0b01540116000030000a40710b1203042201032800c480182c0b20307814100c0c0d04490210fa150207a005030701c0d010050 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 929565152 1250 929563902 929563907
    0x1090624050901031a100b0406030204060e03070f050f1f0e012d0f032306030d03022701020f070806010e06031f0b0a0e010803122202040b0d1217070f 66
    0x1e445c503c1005103100c0e2984880000b810409101d82c03001a2031100400c0215189900d50010001c4580d40d42d81d0303daa8402550815858851130320401400040160040089040c040400100c44100030b080654071010b14078a05003440c28400030f400080c4a502c01d0003020740c3c21200b02c609c4260340085085c042c820301c0c0341030500e0094503210340341440784a80c2005031076072181e081242c0c911281c181101c40301c101201343c003c90000c1170b18110701c03d0260804001203184030f4800c0d210140d811a0004003800c0d0f10400107c01080b240c42c001c0d045000b0041d901c40d50103402c2044500405040c00240601d40c50084002004800603102d00d210b60400e104207421200760801c0d80e884500741507000121840341d8000103014403107030b50010006c604400d0000400080100c00741402c0708400781d203907051369130341229001151840403485000c032001e404c1500140c1465440b20a035000050300405160445450314a0700071150410303200052110f603090881a0362a82c42c8682242d024201042000d2200501 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 929566402 1250 929565152 929565173
    0x3150a2307020d0c030f20011b030c05070c0b212e080a0201111906060918020d1419111918020c030405210123180109062405090103 58
    0x1ca4104400d5a22800d0904203807c0c50b00e6454149900811807401c44c0001c04c401280c5a01c81d01012914245015a00c6401072080750170050340076000d11400c50801e03c1740f03e4990888915107075403031401e802103119074540300303c0b13075004019a88401ea0700a800c110b1070101c0e6158900c40d000888800b07901045079980018480d80f05550900b428070b100b024441c1003038501088005803a45035480700600a06104481d4824410364650040601c8407aa00140f445041110444003c3d0842c4c018800031002c55455000c019040c901c01058580c86510102c0074868010f91540607a0321880b151808400362900e000300503500d0742d14903120444c482c074201d14008000d10003102c50303410030340006907006041424011940500401070041d035001c0409400300341110349841c4040c00307640c43c01e00c802841d0910002c80c00c4000907240107006441d6154460301138500c0c2c0f05814441325640366000c4034002801b0740903090780001e10303481e400c050650300c140c805542c000541c0502d0141c0c82160060012a01c031104 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 929567652 1250 929566402 929566427
    0x402040b030a12051b1207080703020708030d02040510030501030b060d050a0b0901020c0721110d020904110f06070b15010c05060f012303150a2307020d0c03 69
    0x400040040c880c801007402c150003564001c191041e001c0304155010340001c00741000084240ea81c44044034600810750b45e9a010300d4100c460404180421000900d50380c0040800f1486841903c2c02c1e15580e40c0e400703242d504a4051184000d402107070a01250901d00b00314a078009142c5407d0049503d95201d10500300c2004d00040c2c000c5d40044034840605c18200b12080320b850b07101c00724003180e1400b032000c24000d40220b280e05040e4003c0079800150720390300900c240b06030643d07840780c140302034626542c12203054500e0700040d401c04208000140941e840d003c0c070714071941c001d03441c0c840058502d07c10000c401e005401064494070b000d01001c0c0125400d20000d070f41c001702d108040c2c10305094410051356484442000105244200c42c10131003140d0140541504803030601c90451001c2c2d078481000031015400d1102c40e1f030581c1c00050301180c1c0c0d800051074180c00c1900e2a600181d81c40485642d100c0c1e90a006040d402d40c0007a19050081d544d0341001341c150498107900c0c1112400f401a60000d0203000c1d42c00 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 929568902 1250 929567652 929567659
    0x9100302090a2705010816120614090120130b07030509030a0c051903030f200d030e0607050f030a0902010513060314090d1202160206131e030b0402 65
    0x70407590946945000030090701c20041c500940b07040c544045a810800c44048003400d5040100001d040c1c04001040802c4403050700c0701280d5181059000c4861111b50001965071a03220008d684030400842200c40c040c85401c000451018102694036151000d03401c0341140308a81007084460f183d23030014029041d07901d2030b4007883e034801c200e0a0071101409400c01c12945805025000750070841040040c8044460542d54221a49840220b00c83c1c924000c0c40080c011500351108003103030714814865180c1308002206410118603800c2c600303e20705100601600d0100c0cad030711161404c03841d0342008070503401712251501c903180001000245120f40800b5240c50070311034072084040c08680c0100c0a03210302c44c4072034111503040b40d55104018007038444151a41c00e001d51702e8000ca101c070303100441c00103850801034580310400894090b1480084d8442e0015008000000d8410740050766218001c0c80703c06442101041c0f0300341012040050f0f06000c00380c0c40c1038201090000c000081c84e00d01c107154401d4044 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 929570152 1250 929568902 929568907
    0x412090b0d110f040b070606060906050901080618091506090702031b03041d011404090221100e150109020c06011a07050106061e03020309121612210209100302 70
    0x2540d000c00d40b8082c00c1d0200e0b40305440402c0102c5c0241115010f4910300e40038034400e010540d600c900940307400b03d003405040d000400420032045594040c0d51140d80291000c1c022111f00c4012403000c00301e01070252202151070b0410162130f1055202c4c4005260402d000310f516404c1d42c03e0046000c0d683c3d2040500d00030441c44200030007400ca48062043e1001040da0245002029660034255007084d982400317000c194401802d1091450300706803041c541401d41c040c00303044c01440302c0c0042101060801c1d0320781c10b10b44030b04a03080642900500a21950a0000c80280882a0401d400d441925416000840018414000c55407855000521ba81c11144191402d0041800c100d00814161040c0c000142856083c10f90000d01d140d4448444d0080094034030030fa030007013402c03a60102c06911041e5100b0019030b104090000c808a40400100fa90b603082041200301c00d4083e68520101c5032094801c00d02040c05141c110610064030700d040c0303910f280810000c43c5084030500000d411001078005260805502 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 929571402 1250 929570152 929570171
    0x907030908040b040602011506020309091f0902190f0f020a06020a0c06150e011d1506070209040311100e03190207350f03030a0902011e080412090b0d 66
    0x900741128041e00014104594594079100064040c004003485140e84401e0100b002641ca0710100a58004d2070b00101100c5468030b6883c40055a40c40014950b400d09805e4940014200c5641c80148121121031102230280b4041038000350410101b24256070034031064400e4900360960101c0d407260016804400180c072058010021078401000b107400a061615100a9600d5210748441002c101ca00060148140b0780c2c07102c1318045a040880080030001c500c00c000301d44d0307900110804442d0444041c143e1802e0500d650001880749106a5003600410550020308c400804144482c94240c1840c1805100c2400e01c2ca04e19552445803441d0a0101c240702424680e8051090001200820040c402100040351b070342c450b030110003428042c030070350b41c143d0020000e107290020885052034031486001c0d505664440c41d140300501110700c001c0381000210000c44182c940c003142d80e00301c0240c1c250740306d000614040c50442d414103421420b8609000660108111040340c0008590781540e90110104400c201c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 929572652 1250 929571402 929571413
    0x8030a0603022107080c060405040515042906070309052e1d030a1a0411090703050103020306060a0e13080d0606020c0a0e16030908091f031a09070309 66
    0x4031900000d6015410040c8044048801881d900b030002c00c490070345032156559444079075590040c40341c25030003460611042203280380c580e20403680520100314103501d210006000504894203007840812042e100c0094840305180940702c0f00001e142641c40d540703020200d403405014014a072041520070012a100ca00c00f5480ea907001c99481620900075007002401500042c01c2904003c2c041406003100011155817450300160413404990000c500c4c9101d8400c03441d6052403424000c0003600e5034982c0c1034040d0601d8480641103881402c095800140c20b50440c4105410100302400c094429680002c0500405070400480c039000280154003a450b44080c2c0341c41f88550064148800401e4a002000192150046503401181700d0231204502c1140e00c0e943c0c402030381e010070742d00c04022140c00480c03400c02c98080d0307018070348075405801424103260440001844044560700b0151400c1c52602401403102e8041c0582e02012045500103000e8405a402140c0e03ca40020810801c054841542405009 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 929573902 1250 929572652 929572661
    0x150501140603060111060a02090f1f20070f05041103090c1e061207260a020a03020c1c1107060507060c17090c011d03030d1d0109150b1c08030a 63
    0x45c1c013101528007525001990310001c0d04541c04050080c5442d60381003032140ba0010b0482c2114882700e8200303200005034170046031810b00f9401102d4541052460036000c0310000c001c41402000e100c1a544441418102030000344e9405c01c0901004503000c1c014081c2c07042001c107841000e00425100702000b610000e01040705181c00c0c8a11326004180010b012480003040111540b0600316a02e40c0312031010340c02201e5040303110b24602e580058403034002040da076442c950000c00380300806180250400f042100fa89080c01045030b9074407101e100195800c01041d0b00001d5050820000c1030140010310b1801d50701031f1282c42001c20040c0415524203440d5041c90007a400300740035020f003240c1c144503840c011000c1079461b0f0703204101e54003040103401c07260402500ba209545000380083c01841c10304070000101c101510040000014141140d101d0300caa850382486414843c0780078980f204130a4030009500d02c11100c0080381d0314080e102d855064040c8014a070211107400d9400301c40c407543c9645100c4090002c1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 929575152 1250 929573902 929573927
    0xe04050a2a08010209030f28020607060204060f030605011d010e0d050601030305041e060e10020f011a04150806040b18011e1508071215020403030c1505011406030601 73
    0x2401040841c04180560280038605403d074101c8101f09510401ea80c1d031000f42d040b58060004030a40300428490003061116400381c07000d41f125082080a40e40d0506036049500610300050526480c0c4d21407580c1030044500502d02800d01c04007160b49010b2000c624074002044134107010045869103182c1d10fa01403402e895a8001058926558603450001c00036400f03403040d40e034800c00a9620341040c039a900340a03001c07115291900e070b4116001006020306400d0340305ca014150701415240100090003801000b41c0e070800c032804607088502020800040b151031220800da04160300700284405000001c0640d08141c0281024100b40e42e2104241626054544915400c0d400c28100752480c0c2c02d0a1003000c50911f004400340208500051010450307e500c0c810f05100c3c2d403102070300f0405080f03041c0d1000440d40c0500c1c444c8484031040b0903010141d9010740e004400007402e46000c241444042a401030b010010314000380003951606908076a00102c0382c0c03e651180e84000007244082e8080c50059010 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 929576402 1250 929575152 929575223
    0x405060a020c031b0a020112060b120402060c0a0b10060212040603090212030403030f091502100e160b2802060406180f0c0905060a0302090a0c09051c06060e04050a 72
    0x12441c4c801d0743e2526030303299403401c0307011a021602092000d0021b0250606988100001c9814400783d0008003140320b002510503604070400304001400c1000c03d0011030110740c0601c488444504040301c1d42034150704980e000e03c0840d003001c021100304031051000c0314111380d8240b07000b089070b092034000282404040d1044907000e00c40050004200b5030803009101c13003107441d274440041c4a03035123200b408010ba40c080c80c4000180c001c008079285911075507024400c080d00510488030340d504540000e1707000c110960021240480d011840303d049104007944a20703d416030f07000b04070411101c42c42c080d680b0140544010b0030030381c0381c040e42841d0a06a25000d0660354001e031014404e22000d0403c0c10784182e43c0c0c0615074889081000055890034041c507010200c2e58082c10031005e69075982060300c02807061041c648204801381c0301c0004c06a651189031038075450403880a40345400d00e17187c2601154055440b81009140d640300300b002245001c12010358107900903004400f4100c20703104880152841d21078a0300b4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 929577652 1250 929576402 929576437
    0x90303161a011e051008040f0c0f091e0c08010608090a171c0c14030402131e15060f0309030905120d0e15090d030923090f0405060a020c03 61
    0x41c102000700f154244107680d85440107005444c0e405104c890401a034406001c00e0402d0080740000d60111528850240a1800e180c3e00b01e440b4500005d4080c85644814005500d5a0080c0d240388040c2e02455141d104802d41080080c03600c040c0980f81405c14401e0605010645000495607001400f80f40e809990041690b0039402c40c00c00c0c0c0e1459030f0410400b8070800c1c50311800301d991513592445100031002c5941c03200000f00c1c540c0e02540a0a904c0100200d801060b002c8880c4100c2140b4000c0380e1385418169100d524440d10055105c00302c841148841c038414039070210421409030403d201d900c40f001240740120390703e00c0905003580c1d0152075611264021310900165407a003130000c5401458813141e9a81c9140740b000070020071207041c20b44c0d078900f20304d19000c000441d4245810042d070b099592107824032880442d0756081243d000c000185500280150402c0d40c0c40c0f142c5441e1207da27601201d0941d40f0382480c10181c440f1035403124028500c9444540c0090320501c0000208180c07031a1500c1c2485000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 929578902 1250 929577652 929577659
    0x5090609040602071a1503070f0b0906040312081e1e0a022206180e0705130305100501031a16050a090e040804090b09011401031814010b1302090303161a01 68
    0xc0c0d054049900c6d250074601e01a40c5922440c0110b20002100c03e1004001001402c100723503405164018002c035076000c40d003004004009042e410406074070b40c0142e1603031400303440e207800152108a4070304402010785007044204001c10543c100c90298103828000b090300584e0311503403008001e1280c110390803e00345040781c0c0180440d800c03950366001d83c0c078a40d0b100c141240c1c420440700111510783c062000314011440005103918030400c09440400200c8102303402855507a16181d0802040d0000811b51607111001401031080910f22403aa0001c901c5035081140f4000010304c1e005d60307105654100700300000458148030b0388501ca91002400003000802c40504161601e8040740e8032a10813401c0140c2091002102450058a014126822203003144108101318004500030003900340d1090300d42c2c4006600b0380c003040748202c0c2040400c17002e000004040f00d410f030800404005d1081d010380c000303004129807800c0752000700070307030364111625007941c40c60b03071000d140442c040d5003507184241200d1818800007 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 929580152 1250 929578902 929578943
    0x5070213050702010c091d0a15060203043312110a03091e12032003190b030c010e04050406021e070317131202010b03070909060b0a0509060904060207 66
    0xc2c1c001c400c281c008010004039500151011640c0c2d2080d03d465982020b60030188540114140da400000c0c0d80c0700040e02180c060590303100c6c0340180c002100507480410284280004607801c6900000c000c3c507083c004008072200c5940041428400c0000c020302d4008131604d0f41e940d90040184001283c040b1a1200041e2030028010048505c06681d101842d41c19030b41424036400c40f2042091b0003492014500501d1001038000e4000a501c1c2c80344152200c604801c08000d02000e9800380ca80340124600103c40d0101c0710007616503941d0b0f5a07204e60090119840c503a030300004441c0c0d020005840100d445d070b03200e08040c8000d0290800202d001b600c11009100c3d080c00210041080503c40e4440c03104601e40807003003004644e411954500c4000c0301c4048100800d02c600390400e4501140d10012070140c184501203411310580e6803041c0c4040342c40b210130300304101050290304c80c4410b05840c102d03c000c0c540800101c125002414484c0562071800216080c45403d40498201b00d8024405135080c04241002 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 929581402 1250 929580152 929580161
    0x11a1606110a03141f05010807111203040b09060105092a03010e1008010204060e010c0501180b070e0108130609020d060218010f0c03090512031309020414060a09120305070213 77
    0x1150910381d030400003003144045c1071310b4501c80d070750440a200350310341420015607800d0f00c06071070700c002c0c40000444c00007401e400300029074500004441c1182c49042c82e2800006411018040d04410b400502c01407040b911102c1d92039900680503c00c22030741c009003000c0e4400107480b0100040102e100000045071541080789514013401148a41d0020b0560b9000d001b0b08034000e07030240070005022500c3d0384403a5072180e60301c0300e81300780160000600307681c1c4040380500c2e060001c2c038219a410842010400310036000307041080d140b9020b00340420ac03480c3c41400400000f0102800400860740c1d07414074800d545480e41f615180c00e502c003604554a801c5000c14250304401140440d0000d0030740484461f10511403020b080e10364dd4191200f41c0b440d41803000700309498030810700c3c444803480240a00008800d215000100406032138500590f5076013441e031103401c0c0840148001c2e0241208015004883d81d00422000031201e16094801e62043d55180441e800e10502c00041d62014050000d030b0400849940f1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 929582652 1250 929581402 929581421
    0x40e0103020a0e04081218190209130b01030f1a010308220e0a0509190f020a170d2d0503090628050a020c15040506011a1606110a03 58
    0xb50040d602d41d480802c032980c80e508031130003008484203001c0c54800d1310b81c45a0781c98111844000358400b1100c03680f44245000040041004080d503c1c032461402e504207204010703000501c125880114042e41d46610516100621008140143e031030142420b01004d07501c00600081d0307102d02e07904256500d041c0790409400c0440007059050155810092074440141600110703841d81092540710f55035210101d000b40b200514001003805402502c4008490000d540117080307124449645901245005104884139150001590103c1040d40b800316090001626541c4001524106a0000e0092003812070406400c989040c11701001a00c0141650043c0240d8030035030800040712070990740c0c02c0b038628441e00d049000041800307681001400b40f42d0140c008135032299002c00c000d498159000c03140c0e4036101012003000900210002032004011060045900620341d0078408501003080840341c020620a074444a0000000ca11115080049507044482d8101c2c0e18026581c0303030b00c0c0002c00900034014600303 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 929583902 1250 929582652 929582659
    0x11d03071509140f0f0d15021209030403080316020a0503031009050a1506050f070f0f12020102090609090711060a0615111902060d02030705040608070804260d02040e010302 76
    0x140d012680f0780c1e0001215505840c01010a000240c207502402202c00414500d82d03004150a01c004005c20408540b052803420203403c0169264195840b00b07a101c01e001d4580c186c40d4204000400100d500c01d0182d03a001901e8a040b5154104c40d03050503440c0801c9110000c0c507a000100030401211002241a41200c100c6441803240b070b81d41100030b8003201e920001c149a03c8540f02d000348081031041000e04044003a0f050741b07a01e0300340191030300309a2100d03800044540030040200c00c010081c03034044000c02404640000c0d4282819480020a18090380d042140952190000100c00c240301d011080c070102501000e0b20894144000482d0180c001402040d07801c988a8180048052003203580071b0010b20300901500a841000c032541426045a40045c5da01c85020b1085d140403070002e200031030282e05207480f4550364a05d0507402400035075009180c2018441400100404a0700c0c02503440524001c00303103058030143c104881013080d40500e00380d5031451403022401003568120004611b060b00d0088 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 929585152 1250 929583902 929583917
    0x12080f040e0a1b0c020108270615040608060408180a05060a1e02030901080a0515030f010203060a0906080c0409030201020f0423062704020d0f0507030e0606060405011d030715 77
    0x90004c3e0346075816104005d0000f030011000804105950001a12030700031800c100c118105054076482c0342c0401a208281c1202200b5426003e83c6001d220345401440c40e803024094600d069160506070307014152078621513200f0044003074026900c1d500000007a20000708543d0311604504070003440c8643e100048000c0020300c000d40f07071034580000150748094078141d445d0300c229035540072a000900f4000d000718801e421040f10000b0301380e50034031241c0301d010646000140c80c3d1408004209008001e944414402407800c04144140800480ca02d0740d0301400b514007158001861808a0091180c40c901c007043d040040303004264000480704208200b45e4450504111505100c1001800d11500070b40608100c000d03011002c240320340d61092044008014401030824a4040010041e80c4c40055000040d03681c6008002000b60907100e002d0f02c514084009003103514106c808950300344254043c0e18140030780d8600f0010620b11724100b0000c040f0740542500d500c650344082004003030060711041c1000c2401c1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 929586402 1250 929585152 929585201
    0x50d030e15190c020301090203120705071e030b060a0513020403020301060e0c03071b05150f0718090216080429070f1101020102070507060906020d03050112080f040e0a 74
    0x20301596103103201c9004980c1d000b9645202512284095a070898042d5204c002c13810150390180000001d0f0034803000c1c030360b640f51541c0c50191304240131500410720081d4504041c3e40e41410011920050326440404064140c4490f00004d003188055032040ea40110030040d1141103500540107072044038402e5009200781d545800c4090407c170422550700030441414000290b4881c07203211402c1030316075240303000c00c42039070591201800c180400c18840c840511140602051060420600350320100610300b2074207110782d0001c0070950640520400411980200e0214400100e24400e0541945d00008042e82d5950314040030248001509180c0f9190207490140b002c0007041500b20341ca020381c0079048040b450081c0c1e5036040004944182d6504540d800d101070710010b40f0400800f005080c99403500814a403514000034608a0743e0b841d290704041c02c21004004036940c0c4030a4040c01c0350700884050b16207040204441680c0640c1e4003000c4440c00703d006200b0045020b13440406103000802024862204 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 929587652 1250 929586402 929586439
    0x30a0c0504140c091011010c020304030308010803030f01150e1c0605101a030c0912070302120111120a02070206070b100b12040308071b0b0a1a01021e0304050d030e 72
    0x20403500f21044000400207000709140c20b208007200c030394285c02d0907000d00186130811130843d10307a03011751300150744001070610906410000e25801040404015442c0d4a0304641424600b1410300c03c4021280d0940111680e1500030502e0b4110003c0c080c12a112a0046c1d4a500125911904c2c081c1c8100c0d00e0517022820b801403aa41c89010b403240300311002c0620820444600c01540f009113841540300b01840254182d684507610640031440000003821402d05500401034a050200b01d5000035030b15240312440300341203000c180c400014050003d42c181e6039650448901910800a00031341c0180005408000c110210110300c2c00741c9200426070184588442810706584135000c0c180000012050010b400a445021400e900560b0351619400729a45015800c00406400c04101e400d800404200b0a11000921526280402c226014002c175038040740081d4968940603da0251460709092203910643d040040b00c00511010305455440c4034103040040018400c1c002e107500c14089101c22459228 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 929588902 1250 929587652 929587691
    0x1e031d0604030c030c050c060c0f1b0f04150e0408270105040308160804080d020f010603110d0602040f14180408090103090f020409050c031c0206060915030a0c0504 72
    0x1540341d25160f500c809140c40a841c80c1c0040641180d50b4482d13458031001985440000d000d201c00404010007120350b02110315801c00000012640020060340300b4443c0070390303070240c500d911108113440c00503c68295403c0315590038419000484c200404c06d040c00104400780000b400002001c0100d4142c000846101c030340303030300b550216240c00240300380018000b08802034001d240101803200d2880c485056a9a001129041580505440e40044298040302c6806101440d09214228020480c89040d551444641005850580e000d180e100f4900c00402c0010350441d00075080c40d082e1088080ea8440d1401072990f92440b225004544884e0640c0003903801c048554055940000d000d400d0403401c1c0011070050801c0142a90404000c00707809000d601d952003008600f500800181c00701d41038503814145041014042424060550302004c00b83c0c0d6808616a80c0146c000c583c407050031f8a42800e15685c0200b00140366502d40110355050003007119000c550401c542040e60140081c800100d60b4180300d0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 929590152 1250 929588902 929588911
    0x1030912050a092123010606020c03010b06120a0914062a1305010311160c03020a0e01060e04090c1d0609100f0b0903070f030308150406050d121e031d06 67
    0x368036248031000051700004218180e00d0341c0d0a00d1044540d4801c07845802d445140c5d000b0f10140e000300c0b52031503a0703040138096003500382815210540b80255910740c40440a40041503018000d5551203c2410030400168169043c54818120343c090300b001c0b02541001205110401101214802c1c01545201b03040255810f0544008003610310b2031034040103402400c00c442510040d80f01c2001329a441e4000c81d000d08020900440543c001541513106100981c1c00d03907001401c0d00c00c0501c00402466034040a4480422001d8170040b505040310300d085208201d042e004035034503640d00601100d46401081007d0700c520011200d01c0c2c480e0300d072008448112641c9018802e5503884401d414821848500004c10103943d02070102c800c1c841c0c0d140c00c0c4180240361504101c00155200c03003400171000760480083c03101d801c110f0701041014500030015400c0e401c6c8101c0207140d40c2050f0303403030500ca0b4007585201c034a40781d1324809404401070248008004243e081c04003104680801c040d60010f003c0051034900c503 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 929591402 1250 929590152 929590199
    0x60f0e030a0303050c161b080309100c03050d061203172202032407090501032c010b030d05070203012f0325030b0301050a0506090c0901030912050a09 66
    0xe507207280c5044014010081182190319420405a1800c0b28142000780141c1c1c056514511301003441c615225105040f5800307002180c3c020305c06003890380c2d140035068001d100c2c03a0420b403407c4080c13442c00b541d590042c000580394007490a4000034a05004142e041003542c86a662000d241c0182c0c9144108184240c40c080d0484c070a896014040b00074000180d090300d40014103c861155100e50300703854020105c1c1c182e40802003004107124401e0b801c0007000000d04024202406040d02c0380781031410f8408200d45c960600803909031086c2e40d400080d40000c90000000d03040d0344d80e10020440c06443e40d4081071382207000c0e6107820002005d040b00709118460700603458081b00022902e0040002d003a03003000c1c26110180c00045a0600b03101c001214443d610041510003080d00c0107030790300300360840e0b00007070041520a080004000480e40c0e902c118942c856801c09070396417a0b03400440104c1c000d00200da0f00a008041c095150341006802c88058a01a1f480b42c2d110719032103494900810aa603e10368090b41e0303 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 929592652 1250 929591402 929591413
    0x12061a0c2401181d0f06010f03170f1b01021e040b0a080403021005150405090c010e2101090b040209100b070b1305190302010b19050d080708040807060f0e03 69
    0xf0007000e0343c4240601444008011403981340c5400c0701c10fa101203030b090f004030a9205c4285104225010302802e0b004011a01c58901c0d00d40c0f079900c600078400400d12550040310303400a0380d00f4070018210280d4090704011300d01e40d814201c0c4034111701d00039400f9448044001c16200e0714401c254182ca8101c3e81540d078604440c40c00c000e000601641c002402034411001d42c00b4000c040c2c0c0508141d807084030b20900c0c840581c840c10080700c909210031504041c081c24074941100ca180861643c00058081c0ca0410a0720010240042489866035468440200403aa03509080071142401800045640158000c590411903911546204020712110b4800c10031501d1040c0400c0000ca452800d00e01e40c425040360003568054010f688190030125540d465a8143c18511000c2c0b0900d942442000e0030180705a440120760081d04070031418000051260512a803425580c60003007050b1075007900e0346264028012500c81d40c031140703c2a01c45003c0c3c01004006107e0310741d0782284901c100c0f048a1300c0700000d0013814 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 929593902 1250 929592652 929592659
    0x3010b0114130305030316080708041e0302070807170c01020303070801091e060608090601080726070f0b0a030c03060303080406050601021e0a030e030a02090712061a0c2401 76
    0x142641000301500d104080002e80003010030302c284011841403028039450000d0010411000d410814081d000380108110300d01000700180038850301e0440c1c10f45a01d8a050620f1103032034202c1c075001c45078010116501440d58001409058910055038400e00d0000781c4600440c40401280d40c0d02040b1440000038602d98010800e4a41c2903003c9041ca083c3c0a011110101a1054010948100d070740484002207143c0100140c40c0000c0c404107000d0b018250142030900d143c4040b01107110103c0c58040e001500c16844c001e8440010400140204000141c410741c0320340c2c620031140340380c0180c444100420708051643e01514030030310500b4141d0340e04d601d810f0b09507103c0c0d4451400600000b04800e056104801004410b1841c001f0001440b08185000b0211002d1780e140003843d04008074034680c0070790300c01c0d502c04006a803002c250940c802e1441c82c00034101c800c041400f03070140495910051001a00081529000440c0c40050510200d407030120303408841c1d540d1082545071803080e0b50040b11103080c0010f0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 929595152 1250 929593902 929593937
    0x913081605100e0607050a03020f04060903020f03060712270804180e0303040f1a010902030a1401030206070b091903030614091b09060f0c0d030e0f06011203090b0711040b03010b01 79
    0x213141f54016441c005003403110b1038004480582c8950400c4010401020b0f08004500c1d0014428210020a50180c052404c0c801e40140212540c0e0b00d10010b2280c41e295908820800010110080d20b040000ca0300d040301c0c981400e0b81300c4d07840b074040c1503a04d0364403285081000225003d06005210000c00442c0745503203135103c070030a469166004031000303407141840c2da140200c40c0000301e0103032507262070059403400d0800401c011a4400c0941c0d0340720260311001040941c0d143c80680d003205801c501e00201d250380d00081d16050028140000030902e45c0c6040c2d980c2811f1b410f80c0701d001030f82d011140d03040c006200442040750b44102259291201c0c040020003a41161940d00a89241c1d174010b003025050091100c803d05554201c0d41014006903c00030808aa6540c14010034865603104070152560341e52800780399490302c40c14011484021504182a8205403060700d07000700820030620b40c00e4884001d80780c450f07181c2907801c2031140f103035050100f131406d50724041c420103040b0881619070701008070658510 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 929596402 1250 929595152 929595157
    0x7081b04030602030a0608013c330501090b0a0c080904020c030c0601050105040e040f0c05060d0209040e0303130b060f04110a27050913081605100e060705 68
    0x1101860414040000028518000b550207121803510100311641040d000c01e0858014038050448032881011407801855081314480780b0369018256505014102c42c505030182c4480345080400220355540001d43c46041d2138004100100d4200b107140c0144c3c1c07040110b0304a0f0303082c0241c0074400030410038040700074018480804120b200313110700350522400b0300c00a4100c0e0018421940e10740c01c001181c401c440c1003841110b01612003402d280e4241401c010045134021001800100801c1c04402c107402030140a1015031f0040070003e0805a0303031540d6901110223504800f02e41c5015605043d105c55007441c0c0071013940d208442001c3e03003c82001040c0c907a010505005422541c100700b0541d48005075032100e000b52543c20151100f150360f11948030b0b40040c126003c0800f81d810840c0c14080c241e040f200c00180380c60864404840400041d254684901c102c024180310003007045800040e65440b4a01c1d1042c600c003114055029506507185a0020a0580c5e051100100441e0010740000e048280120007 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 929597652 1250 929596402 929596441
    0xa06091202032b031b2307020409061e05010303021903030608161d0907030f03020c1201061712070210050d020c0714010f0807031d060f04020103050702060708 70
    0x85414405810b480c030001080490900351840b03c5010907620000e400d80110340b1038041010b0b0084910001e040018480300720041c0d44800d03000c1c13161045541d40d440f80103440314143c00400820805030145070210007810398000c8850503103000031340d4400c01041846114100c2e0f070140c0140040c03103802c0b450281c00703055415003101450350360a0041a2008200409a00380000d0142d0004180c2800718001c41680c1c604880320503070280004000c0c958002080d1001207036803209500408001074079040e8105442c00307000700d0f002050740c0d060718080d00c0150081d0301181d038150941d800c40380320449005d44441c410105101201010080030005092203650501c0680b0180341803402c100521600b4000d030703488016540d400345c1c8141028402004c0e038510742c81c40720009081c80d040540c881040500003031401010082403503510203106043e070b00c82c9180300b000039080724103482c024600700c0030f0581c1d00d407404cfe03500b03074000382c58200020146800050185d005150741d4035141c49a95664146168070703410202c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 929598902 1250 929597652 929597659
    0x6240d060204091523010804060605220608071202100302041d0618010501021c0e06120f060105070c1203020c18040210082404091b030605060a06091202 67
    0x104200200e44188003400152021040206018110404649403500d6a030001800700e460308800f81620311442d1040514002d0a00f04410b40341d5403400c1500062466901a507041483c141505148840c804180d010316804c2e0301d07007080010780b43e83c40c207940c8a07014002d20783c2280c12100d6a0703000d8901001e640300d864200346009480c0a0720f440c0c0b490b13242d00650415103800c46e1101c040c002207182c400300d221220495106840d01ca9854100001d564071900aa450b0000b03000400701d0b61014403034034100100d140050042c2d541c40682a41c82e040c680011917031034901c40f203c8404200d0300e40c4a1801c07104404e410106142c251428100810401a81a04d00318158441c0c186030507070a4440b00c400700ca4456160425000900d4180181b1842e48207268140040024440c20000c0d2045101c403400d000c03440007868000c5001d03800b004100185502180a89010303000400c0c590010101d682c5138054030700c9800240151b0302e0707003800d02040700030070f024910224905002c144003425001004800103800107 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 929600152 1250 929598902 929598919
    0x341e05071e060315030629030a0f020609040b0a0803120a0c020c060309100906021207110607110a0506040803010f0f0608060105180901030c08120c0703020f030f0d18080624 76
    0x3952410120380c0a80c059041f004480b03c008907181411154400100d04240d02a04000340c0640d0f51050340a00000d0091040e0008612a4050f46580e40f16501c43d1402800304200c854a8a120719681c1c0c2054016206680180d40042d0b428150b82c082d440c42191240c0091880b10850020410300390001400f015a610074513044030248600f6008801d2940d018240050b603814507200c40c8a50b500c1c00510792414891103080725040001c001038040d500440b103141800301006010f044608200070321001030100d1184006200c14440b030403004604031a04500405c0c04999240c502c0c14082d10710f8030941001c10002c0c000a61994050300040541c031140c011240403144082000985800c400c4c1c000b580d042c80543c00501c0010010031030041d000c840c19806906158000c07866a59926031800028004c4040e12862421501d0402c880320001d0320301d400756100018142c0c0c00a01d20060700604003405900d19400080c60f03540400c4140c020002101c5480d544c010864a2440d40721410307410a0700180e04 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 929601402 1250 929600152 929600159
    0x90e07030f03050c010920010807091404020f210711030d02031503100915110403140f0a060c0f052d0d0c050d11341e05071e060315 58
    0xa1140381001b6101e4041d941e07540008041106210fa445035407217040c0900c810a0100080d0801503074800c485d40a00480c004040100c04503000e400303505510707070082a02054140101c0b400c4408150000803100b440d041340e07514520300701c0305511403620030803080c1c204024241c2500500c0c0c00440d4404001152a0303000b180c2d8101192800c0c0a042c0444480c40d0713034030fa42c00100420503c000902d05c105010500040e0b8500803580070901c00c502c001010f540d00500c44030300c918802e00003002900245020340301d0120b824100031028180e00703504580058841858070000303501480a03503100c8440803500314940d44203011075816a268070b0400b51400d800c00d00c0340a4580030b981c040c0c10440040d40d0b40e0315440341501c9480a054a2240c6094007194400703101451294810080c03620b10810b81c2c03850101028014242c5180c05031000c200038241004550b921004454825124031030207108100311030030140c0d5000c98100c0c28600107411001035000c0b6604218851294000c42c134004041488161403958 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 929602652 1250 929601402 929601427
    0x10311040602010f05060402030933160e0d1a09070312020d1407050a08073f0201140105010e03010608060a05091501030c0e1e041b090e07030f0305 65
    0x80e90003140184e45440c0032000d0442c0c14003900b40c10030000e031415404d40c00c040b200301ea190000701c24842c0c071100d05d182c45000d4a90b8901e10700420f000b91003180b4510b605285115084081c0d81c14071041c003003882003000e82050301b04048001e08603900804041c5150440c89070316110090050040c040d00d104041002c40407a059048003914010681c0040411031441000504040604c1c40d810440c44010f10001c804100b0105403080c40c00d41c0848071642d01c102d83d15041020812000e8809014180810201013001c4100e61101086004031501560200c41d0383c0100d00780c0d2641d200740341e0030104c150010800c40d402010f15582c003c10040000c00e40a0700e40d0030440c54500704480c004280303078692061281d4082c0600c1040300c041c48101c0708a01940c1162a21020354203140f14007112659000c1c00030703c204000c1c0c09440d12006050784001950b007031a0a2142403d0021200101ca88188500026070003d00c0d00c00d200030840700c00054400d052443e00c0e428600b1484070803e0f003d010080110141502 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 929603902 1250 929602652 929602657
    0x14070609140102220e0c090d060e07061205060307090b030a020d050d0806060406050316030221180a020a0306240e090634140d051803040e15010311 65
    0x75000503100c000d071442d003540c00c0030411425064141540070034050003191040496000c0840c0d41d4a9070b43d901c6a402182400e4074024005d021646006aa25000940410a402100c880303a4039042262280d004020885000350b40007039055101000c20132002ca40350b00164010f44e0014180e943d0700050350081f0b00101c00d414011101500080b41c1000619000700784076030004015070712241080e040ae64081d0182c407014014000236240c10350030405c041d200740c0440d80031850101c1204011500007105010601040d203088155082c40900204100d5000030709103042c6030000d04000700d02c0c1c0f468848000400705602d92146520010303150500070440d103485840181010b04031075419250141c491b5083c0140601341c1c0c40c5441802d4215100c0c40002d2035a0381004024054146601c1603415056a503055503848030f001024001caa42c520901207940010300c20700b149804001608160007038241c0f28865401490580c00e001400718060f8814117400d107121810606000408600520509903d034 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 929605152 1250 929603902 929603933
    0x50a020d15050a08060609010603111b01020c0f0d021b1206041a070302070c030206130816051201021306050706060f0b030a2a0c080d0903020a14060714070609 70
    0x420303110504120030700b000c80f82c2200030300142002e00080e003444000a403102c04c041c42440101602d9652007010ba5440c40120b0300e4400c00d5145441c001e85024101c0c43c0030350040c0401c07154502400f5131f1000ea400001c00c150b604a0003682c0a0101d1a82c070f039018002c41c4c0621112107810002d0708520f50100c55040201c540640d01403c410000d1075820104000304040c010507100416005020800c0007e000610700c4c030590b07504a8415450f22210b41d46c1c2004148681c2c400000b504c6003c64034031401112501590956100762070a020a01c0c203444014280c0c03082018038010311000700403c210700c82c4100040e0850b0392040b0000f04500740e8820040c03c104030940c000c00400038000040c0b2002964a20904844100c48031109201d503204c1c3e141150405103881030f01c410f210405000c001041201d004075144805e00d6a070400211026042c001c2d95a244064200c964001c881000c04a400001820912580035030b03480c0022008038146071144e540203280304858254907145003100241d1032260408be80d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 929606402 1250 929605152 929605181
    0x3030403031106130f020121060905070908070806011208070c2c06010e060a110a05150117060415270c0902041a090a08030d050a0b010504080a0204050a020d 69
    0x604251000b909001c4003801c2042da003404220100c00082d60070741403000c41502420820001c1510384140c440111040521140d03003031526001040b40412a030189018119a0380c2e42d480c120744868400340e882d48140903500e003070b074844c00040240089564405c1012482000032601b4101c441e0307120a000074813a0400d00500220803507820300303c1504c540d1040f04855010903414241450400a051074502c0b00185000c0c0b00d00007500841c25000d19a40c0c482e000840c41141c4950780e0038101680c03a882c0700c03151002d42c0c800440000502c00141301c02e040708904038101a24940d19141c0d00e41300b01ca0040082040343c541c44043d40504e00d0b40c1102c161401c01519821481e610004e8035112091144503003040041c60f1060006016502007103a500251900148511381d5400c041070014102000b282d118502510000400913045103250b00320500486040c5420f09c04d0f903400300d0054900e80540c0c01080745aa0003550010094039113504100c2d00508480e0740146000841d420b01e10035903a4500030b515030b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 929607652 1250 929606402 929606417
    0xc0117040f02090414010b0d08070b040201032304060f0e0d0f171512010203010f050d02030307020406150305070e01050703030c090f060306030c09140f0a0f18050c0d080d0e0106050303040303 84
    0x5522407e00441d00100800c49007401c1e42e100315515400140a40240036040d038501800050459000b64083c01e07500c021504d49044140294041d82c22240381103c00701d61072410094100c9001d0301c0340c040c50ba8250001c0014143d082243c0c1c0e02240ca2114408911003040111500b4003281c05041240c24043d021103000400c400d0b50003820703c05003010440c42d030300481c2e00c1003004101c1c0c0038007403000e8010745a040719200c040f0003050000a1660181305406503100703160900c0002c061280251035880341d41580c40a100c00d9542000c26104d4100c020a1507021540820984001a100e58448640c81c3d80d9810980798082e2520403c0c9905680381c4c11840120b5919041403041c040950500d20050100090a0041c2c00103505043d4051101034691007074840b5500209612581c1c82c1c010882181115504116200080d00e40b01c94140c0144010f807142d00075140b24114030f00300800c491000c2900080e0f0149032141c0c18003180001c0406c40c030381d882d041d540c0380701c045441e64003803006000460003a40d8405 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 929608902 1250 929607652 929607683
    0x3140121050a02040f0504211b0c1e170a080f030c0714030a140c07090905071d1008010207050d050c0106120b04120216030209060406090524030c0117040f020904 71
    0x1070710341c0c1c01c2318885950500340c0c000340482a03000174121036482007010a01515151450180d9484d600c94214103120440e030316140302c54009401c0002d0486080014401d51078000d000c0507500c5a030000b60141602900700304407420221444021500000d40f10069441c3c481e058036541c03000d11544140d0b641c81e410000d142d00286a0025420100321901c418040c80d100104c042d1070381e2102503119182c4401e0300c1d80305170702c2402014826007004011a503282340740e440d10400440f00c031100c22284501107074500b00010810700f0051098900e29a4401d00600c0f5440c400d0030295020b400500080704d096496a0b00450100d41c1c42d10780384609480340c4610300e003500741450038051002d6240c05000441d48400d070140c0031200d140b00c042d02140d8040d03802d00c1d006c0e00c480380810082d11a94001e04140c604000600c0388c90010300d101c1114980e00c10a000c1c0011f1009010035440d10901f00007c0e0020305507100704401781008014803500a440341d41442c031880c2041d40401c00340c003800c0703806641c00c244080141 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 929610152 1250 929608902 929608913
    0x203010524100804021014030106050301080106090c1d041b052502090f04150504030f02070f050f1306080d0f030522030509010905040f0204050103140121050a02040f0504 75
    0x1c1d4101001c6424540c906015440142082c07402800648a900d05120980020340030700703038205603814034240840c1e80350b03182c480190085c0d2007031140c0300c1c0b99840d04100203444540e0b0300c81d0404200340c0d640d0b0304c083d0000c010704804010000040184c3d126640b1000c160400300c86561500700c0c0d48464640e80d484201900800060b154113198110b2b40b01e88041040d00180d640f20340d1164040030b00d048a40142d1160b091040c0c86078004502c1e40c030402d1801c4140030034142c02c842d501c1400c2c10141c0c2107415103a11000e02a0314180180302e00fa4103c003030150f01a8507880c000e20040c030200c0d05140b0000342d01d566203181074176005421480b00c0108240c11508402a985406026032102d40c00e144089040a0242c83c2804100800d002604118010035940710a82c810311a0b0710040c040208244840301c00c030310a4500962061003414080323031030440035059200700004028100c8000841e0a000b031210340c00800030307802c10084c0494181c010007070040010395035845010750048846100240e6480d0920b4403 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 929611402 1250 929610152 929610211
    0x41505011404051c0602130303211e0b030c13240e04080c15010b0318071214160905010929010f020a0f3509040203060d02030105 57
    0x714141210100018005602c0d200c1545241c2001c0e005240351184942c14031038003d00400e40110130614400b400041499030045651505849603040780302d2004042c2074040407a14442e580e1614a10720749035180105030654800000b00c1800703010344860201d44000900c507100c84a03003001305039a03140c130103183c6560346882c810540440a8000d00b00681841022450702c00000c100900d01034001403200746c00da41c00d01086e034a01c0184030400b5211b5848200d4a051900115101d40c804403806481021402d400180034044680c11882603100400d16201d150543c8c0794010a42c1c1d2622900c0d00c0181d420f1380e86901c910080141201c00155075040000000c1950780a905119815042e000d05420241c0a0344c3c298040034000d080102d001200c3e030700247d04100081801034000d038081c2c02d504050180c80720031307240026914080d00c85441116441c05e81460141a6148e031004ca0520500c9041c0c20301e0ba00031900280300802400070b00d285c035800a42900c0381100c1c800880d2103024041325504105d03644 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 929612652 1250 929611402 929611427
    0x1b0105070c0201050f0f2d1c2309010c1b1e030201061e050f0406140409050709110c010b01140307030c030b1002010e0706050c1002030a0b042306031b010c02040b04150501 75
    0xb8614040d6a048c50302a0082c950703c84211165540340c0d058a40700350f11009044d5508019400045444c1082c400350082c0004411400402c0392050800000042c41d40a8009941d0050b403e0085102030400c858907003105100071400d566a0300c2d00410101c0c40100301e040025051040d0302046030401c42030221301c0d404050090b000c0da041c00c0c3c1c18460060300c1d440c41400d080060382c002640c0c0c1040d0900c5450f00040760b000300050b03450300c61a200c107000300000520605007650000d21508207410300444c0c1e200b44807048010010700c18070105090758070135003107202c0043c203503d004140040354800040045603121311410150b952006446800a003e22288000340181d0805a04003240b034000316444544031014083c56980c000009101755801d40d01c00080c02c1c030043c1007001000800310301c41c881540702c40c901c1060800d815000a08038a0009840da00c1c8820000105040030f10300c07030041d1010902048107c0e4450340ba920300b602c1e075444903c1100d40c080d1022006440035841c00c00050036000140700c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 929613902 1250 929612652 929612737
    0x9050105040b103201170c0706140609040209100e071707030c091205010915050628030b190908030105010e0406080d180e010b1b0105070c0201050f0f 66
    0x407001550f0b6507151058101c11324240c44405840c28190700103c40c0c00921000c02038010741c1500034001019402d10250120600c5400d0410455117112520050084103e03a0168000900c0e40050014100f580c82c05400c649901d01304190151611000324098104450f0700e00010f40006e10300ca05400d10540042d0420604d040401040201000c001c4c020342180c041c01505000c1e00380454100402548501d003000c1d00800280040070040c0303c6240034107010703220f851040d0b0043c180c81c9025007507890041c166540b81c020b028810351039036641145441006210510b1100003115082c041046401440046803003141d042d5541c1d81403500160052415100c0f03680101c1c9841414401901c00046407490780040e41401901d00b40e045500f0382a400e06904030540308680c02000080c400a0344001d003844498040114240048010241e4221a0210b070b49a00060011034520095405080104451070000e03801da89032084100b51245a1b0384449c480214545810b0026002e940f28810258034100b07146 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 929615152 1250 929613902 929613929
    0x1c020a030f05040507030803090f1c020d08070e090c2203050120030103080903010915060504060b0f1e0d0c0905240a030b04020d0c0503070306080d0507030503060409050105040b10 79
    0x7921415603817660b5000081c62408000040f41c008141006542c200440c120121071408a4240401d2802c00e0140c008a025109050f400d00055000d882800c0c844d081701d903601050302e8100020000030b01c60240030309008240801c400d00421664400c80170b059291a0464090075140d880c00e9401c4507002451000128102245c408611070030b0002ca81c1140d400000c515240c441d07080c006401800f561100505510b903040e011605000c0d60b8004c0c4044800c225803c01138244d50782d201031a203100303880c403e400c5800100482c200c11a0075440b6684c07580341210b90035003410400344900302142e1301420a4000300d84002003c000d58a040e001312018010401031080002000c0c2c9002d0006024608400381850b880e401038a40300c2d1500d5060320001411540144021140107401400c00d078802c1c0c03120310009081c420003240c4100e000556401145213a40c0d06e82c0760a01030f803000c60340d540024255981c0903490304080030100d4000d000349405140a241503c085060181d03209190403010740c4136004c0348010 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 929616402 1250 929615152 929615161
    0x3061814120f09041103131b03080901030c020703060f0207140d08071b080723010b0604051e040c0324082835070c0314031c020a030f05 60
    0x6100c2541c049010780142d40b40c503035105400060251295030045031500c0300200412905409a203544005140918010141a41c0c018010441c001640c0005070824030308210803d520751195214804084151054410f2203449030f84400a559501d80b80c15100c5401207a101c007480300c1881c0310004075800e803008080e006285135019000f503c3c0200503400340404942c5549a28240e0811000d2107980040c80d5551891580f902d44822904880701b6035800b940c014084005860510070540d00318001001241454a402d00308000c0c05c10f12804600ea28018040c0c4011940b6180282d48140303019803030110703480c1c4c0500301040003403a81c600c544100c10000d2004210000f008540842c0c490f4180014010701c05480b08500344008003030300e0080081d40c581d40e0380300380300a0351040300e880b40e8014403001c0034500783d1340f0b20001c2e540194000901607049803401000003800300c0750400010b403418030a0300e0420000c06030034203040c03170f40200b4010303c250001003503000907906105007a480200c00300108440d061 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 929617652 1250 929616402 929616433
    0x121824091115070b0a050603100c02030403030801060e030616090f030c05030c0913020f010e1e03070f08120a020c0312130905010315091b060509041b0f030207030903061814 76
    0x140a4400800a035443c0c001c68540e07101480f24804c0e00d503004200340011000c1c0b02c2b009640303900900c400e400040c00b1070b0000c03848521030f1072038010126004000f044942ca801c08542007140780c0030043c2d01409101100003070014400e110101c011405284091802d510307101c28181450301c86c42090b8400c00401c010080303100300b4620000451078040d2000f0545403030340350050307448140d4540007031760059200c0c0d020f48400c100c194508854100035800c3c0d5541d140c1e03444000d21590101e024281d417039008110020007100180000e40101801761049610b0748000301c000c0381c00c0c80802201450f03014000140e60a000c981140300000402050740d00b0042c40d0714644031500300d1401e442c20001200e884007400320500003080d9074115204034080700340e04190364643d03025115900418130280188e003044007040c0007125141c0d1410306074816480360000e003100440120001c0d0f210141c12021321140c002c010000c13802d2403054400b5400658180e911801b100c0c20000030140c1081c04106c010b501803510381c2841c2d02d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 929618902 1250 929617652 929617673
    0x2322050621060f18190219030f0c08010c021b0f09070503010801050c070c0501030c3b040204050a03020112020f19020c1906050c0304080d050a12182409111507 70
    0x17030642c20360301c0070300703031144005001d107c000301c07881c82d83d0060444044103106101342c016080c184584000e810242c0d8980070503099441003c8203401580083d003540524103c800710011035118000c2c0140440d040d44e20018404810642d41800010004001072080700024803960341c021000015280c1090354607600c10181c07070f074107009035410075489540740c8890a01901050f2070a055000c0c26000700d2030300102181e0b0f107a9401c64182201e8440d1189440141064402c4030103444014103504d4155055800548600d00708082c03101295500300a83c401f8450703e000540000c15901c1407140c04000400f100a15040701c0d00442445685610400488000b0801030398080b2111410259201c00042c00c0c1c0500354080c9a2089945000341d0110300200c0c2c1d07110f0300521614000d034440d000c1c1c0040e000d1100003141c00c0425403200c000c24982c540c05c04101a40741a440c00400d0790160840b0414108201080e900340510865400340d004620b10300502e01410702c1210801c50144881c00c2c0155916080d0b0501e = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 929620152 1250 929618902 929618923
    0x11407210201021b03180402070b0a09240603020f030f0c24040b1e0f090d290610020c0607021203070b012322050621060f18 55
    0x2603551100400001e000303405540031000504140810900c01c403010030707160b51000340c400c80b10a20340090350880789003520903206a140c22044001c2c02d6995031601c00010a0400015551402c4480b1414841c0030289000c981039a4000340200341e503880c610520005401405440b4400e41002c10302c152620000030b0001c148071000c58018a1070382d20b8060741f410004410fa030702c024025001901040401e8407000400b070078450005800983c1c5207003d00d03400f0300c4c01150100c03403230140c08100940441c030b4004c5031007000c01d0180e012030894800c9903140241c3d240c0c202c1410209210320a0030010680303028040c4017040d908a0018050700c104810014016200e01c64000f80314188100c7c1d03064041c802002611613407940490740e0441c0d540c40795071246e0340e84088503294070680c8000740d0b070001c1c60402100c508070352103620000141984042e0254000b40c1030043c00c05400036800c207000c0010000001c2800c0070314000d00040c1469060080c2c50310f040c240002c25070070b00701856214400129100140d11600e6 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 929621402 1250 929620152 929620193
    0x5060f070c0b040804180e070501110a0b072604140d440108010f1811040f051e090a32030424080609160306050909010209011407 57
    0x2aa501e41c98209202c0c05160000555114034510000c0c1c02c11b0300b58003503000142504211a426a501c400450f1034031003502c501d0141307400120000e0300161200c41c1030f5800c2641814019500800a02d07490801442d0301c1880c00c0307240d0300e20144000d101d007070041451480704900140c00c920000710006001d07022500b4500f04244020f00e6004515050350742200320342500401c200501c2f44017503203001c219807800c0c0914110784d4a8041c015a14110500c41c08102d038009075484e0052800d035403a0380d009041c84442143d0400d803124030160881865200b014460381003150a0194420f611100c4034007040300510340d000e80e0303102c1c070300b1000800ca800340078905140d100f9448030190580131010380020510701504001d2403002240c0800c4404d40590039070301c0710803008030310316203100380f030f401140c020400f0383e0000e41264030712011412407491640000d000d9002402c01240140d030710b001007500f44030122a40ca905950126101c10b41d9a40100c01d010304c2286100c07a14100b090741d441d40c80f0802e880803030090f02d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 929622652 1250 929621402 929621423
    0x4031514070e0d05070905010515030720150f1506030405070312050c07060c03260103060b22060f050604062109020d0b0109050a1e180b1305060f070c 66
    0x1c243c0e43c1c44910706201d95000054a480795902c4034214050282030284620904613000302200010701d410682e81702c2c04156840c61000c0c400202e88c5070007000c280011100c180946080c8400c03440e11a40c0740d40c0a0400700071540d00614080b28400202c40b072001c1044c0c807514041090101086e00040c117201540d8105140d0040c44d0b0a0081c161120b100b424085821401105000a52a5041000801000d009072200296004840b420540c94001d0251810380480c4140c014030104810b41c1c0314801c800005440810303080c01c0150202c0c180102c62107400c900c5504c030807060001040c0717000c02100500c001d481650400b418110003418001e00d1052031000101041c0d500d4401c91007070381001c2043da401078605450740e10a4102180e00741740c00d01072418141c1c00c00000c1003030050b01d446040300307241072802030405a42101c030107072000d811880341c10046000b44010385004507041c011700e0b90099080c4014007000b80807500d00203081402c01002c00c5e1860390708900b00110760b5000f2800c0c190040d0700165411 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 929623902 1250 929622652 929622677
    0xf010b1009030b060120010902030c0402032a0c1e100e0a03140f0f07020117011202150405060c0a0b09071d042604170f210910050403151407 62
    0x200e004c0a1b0300d03c00e0321a40088200c41039500410f40c44110b070b650080d001e0b1858110070100784010381c803080d101d04a003286610200801d114404020b0f040012035400740902d41119002924540415001070070301c05610800e0141c181d032710030045003007124070581c400d01c072011900c1e034455118480c102c40a0300340304031440262405401641111002c6100040c643d07101c290780039210320f0f140c10064040340030820600001c4031205507945458102d411074100340c0054103080d800d00c840c0b040e0f201c07107881b1003803414400401c0a56402c00130f00b001d0703005400200740049050420080c060009081c00d403c58000039030a1204015045065110041c0113101584036200c0749041c160001030007820302d22240e203032180c85c8162603205000340201d4040140c00d5198140c02420181c40c0c00d482050740d4829030002051080b80319041900d081c2d0402186071a40c200407080020a01d01d880e03d90030500016000201842004008850b07101c41c00c1864900700101d00d1000c03103115801201504120501c02c0d40103a20 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 929625152 1250 929623902 929623907
    0x1060e1b1606050f0907080d0e031e3307030c051306030b0328060c180b031909020a0501051303080f0d180305190e120f010b1009030b0601 61
    0x3120103581581d044030480300c03039040c90750090109442405001c4100000f20b070102c0300018100c02a900d00002800040062060549500c0900d600031609401090320000e505090441600d10040036500a420982c400a4134000c1103c40c03104014101d99105c403066091058528400e507200303201d82030004071000b4580b010b0341c1d54003854071020050a5500341c0030a03019032540000c14148000d03021200c07801d00d154041e20544103c0725540c504850b10340360103804070340305801a007001281418017401d42d004900d000000b40c1c20303079001002e0042c000018000c160441100d41815440f030000c08102043e1300c1d600240c2002442d10540b410440041020b0981d0496041c1010086078880003203a5546c00c41140b04030b0742e4000c84100303190310b403a05a41600410f000000f41200580c99a00ca80c5040c519500b101511070302134030340b40100124a0100c82658840208049024201400070320f00040c41c0e070a06804e40711a2050785000c0c6860710405519079810044040a40354800200d800c3c941d03418004 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 929626402 1250 929625152 929625157
    0xa0f12030f02161b06140306040905030d0e0c0f010503060d050f012406050901120203042d020f0a15050306030a0503040b0d1401050d0206070201030f061e0801060e1b 73
    0x41d8181440092080e8a00000712510784649104d07422071072103c03013054034000400300c0510030710020400700079518486107a500015503001c0001800098a0600703501c1d65480c0d41c00410b60302204540e90040c0e441d07008010000281c0c40901282d2041105c180200001d007240000f03800740c0d01071426207040000f0032400b0700800030791300c002100801010328401c031280741084481c0030924090b8844a400f103800c0b07104104981518106841c1da01c281080500060000d520040c001c1e20030040300821180c82a820041444001c0d64500415400c200c2600401c41d0141c0c245c2c0140b4890402c7d640d0400404441050b25032028045023407458590f603c91001c01d0405141440003002404005400f0071200f2029010b1300a11b0b410b000c0c1048265040c07600300910315801e0290545c802003400b2401c00600d0301e8001458094811315001ca0000e443c2c80780c0500b80c2301c00780c20036000c142c1017215800000c0d100030040001091107000a020321490710346003241c0808c015154400c03481090000c0341100408404 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 929627652 1250 929626402 929626421
    0x6010b0702221a180f04120309051b040b01030c020606040e07080a0c1a03040f021c02090108011a010c0809011107030c06020304211109101701050402120a0f1203 71
    0x14180100c55200c10005031030b800111280744140d04101320100318a9550b0b001c030380308860542c400c10a0f0b44541d21107083c50200c1d500510205070300c6400c2c0c2c0002640502581c07505117055a42040413081403001c20094800c050300d0641050301c0e2030310b401480e80d07001a41541002c415600000c2d1041d20940c0c460400d9070740e40000c5024450b16005100b003240c0b0340d100340704a502070580310703109185d203854540240c802603801410f8402c003a22114058601245103004807292040ea041280c0c14170f03408525101401d80c41151070380d5503401d100580003140100101400b200346480f0b0b0f2501e103c2c0c0d4a05a06025011015042000b40304403040717800ca0402c04103000d590421000761034182d84120003580c0394402c2c02001010344601c40740902c00c0e41440203055074aa48030342c0b0180300c00c840300c05200c0354910081240c8032000b40501c001581800d0014a008001090710001c240d03880c250040c007450348412038030b114050b40030801c2c540c04503d408588540b05503012200c68110703035000c50210080c101480 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 929628902 1250 929627652 929627719
    0x31104080f030c060603070e0601180504050907150f051804110d150b0406170c04090212240306160201020702121b0402130e0c0c06090d1106010b0702 66
    0x4008250300c1c000040e110005106080303600c950303160030a064441520b0b100300700001d0582004201158020003040c0e40f03807920458119600c0e980c1d81c00180c00c1d103100b03031014401138000440900c0184011450b160380501c40c0c1c1080c90842c0e0740d0741c10090051080711f191840c4801d58280f031151540d140d402401b200840324541d151100d1608203e00d0042809071922080c4d030905e84030000341c0200d00f10540e0121480364480c0d900c2420310325416401c90304002d1502c44152400c00001c1031003096440030b02440500800b02c0016450008000d408101e8445c2102c052080c0d091a40300c0e0540c2c00180c0c090780115070540000103010524026800381c000c0c0307400258020342500100180400000d400c0050012401e500300c6500d08160500040307104218001d00d040315003450900050940e07032051034100034480f4009207450303024120642048415646e00c411a0083e02c03c2120459001000582c0155508043e0045515080c901c0c841c0703215244009000d02c85c18114a12041300c0c51011800140d60754 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 929630152 1250 929628902 929628913
    0x3050607110105010806040206030403030f0b09010b0a02120c120a03060302180403170c0306040e1c080f100f05040902043e07020906010804050f03130504060e061003110408 76
    0x4620161841e400301c0103201c0c03150710b0000000342c00c040005400340990b801404651642d12544c9040340074040c0c2d5041a0700c3d150300c80c01c40d00c3c1141c4680300c49a00800100c206561540b0200310000c0c1080614100410706460a02011240810104081c02c0c06007101a9065a6a031003850541c060b0007194006940285480315040200d030a400103e84a1886566913545040286030038088652094401c08003000b4188009021f600701341d44a0300c0c202c070b114400c40d4001c0d048014114008000103002d400000c40780d01c1401000c0152021b1542c000d00c2c04a2001c1580e8109403041c0c07075411480c800d00b441580c883c500721041d500c07254490a401d8020a00c10b20f10850308031502c2001210030744070a21081128418220716185000503900705540c02080700100c1c0e120355004503603e450190041da000e004800600865010070002000c0385130190400208013450901000101c0d85c103035214401c00030707146007044100c4c0d9416a041e83d41120038100010081c0c1c18402c500440e016a0304070070040d2045 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 929631402 1250 929630152 929630161
    0x4062102130e01080a0c0e0a06080604061508030c10020d06090c0315060908030318031911060a0203070f0c06150f0e06040b0d11040207020a150f1b031107030506 71
    0x51034015050b030706426044169a40e85035401c4d650742c8034041d00507140c2d5005046c18058400e08496568201c5580c400100d945030302c4406290400e42c095900b00c80c5241e50b482007002c98112009084010220341014504044803140300984814281c002080016400101d4072484151940600c02402d02d20b001081040101c28014006088801c00c82264404080e40050210301c0f81456a00343d03024074001d141162120081c00c01200044140001c03d40402d224400e6094880c4a815602c0003079541d8020003034442d050414103040d00900040c60030350040042190f2107800811b101d90032074452400961003005030400b0001400b07402515241d02000000004484844c500030790243c40410110014584401040200312a0302d408050380001c040444800421052800140000805800549040499400508860b4560300010102400d82000c01c08441c4d0050344903c00703c60a0070100560883d540d01d012032403500340d4005003008410f5498452240c0140006070056500004480711070a0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 929632652 1250 929631402 929631427
    0x150a1b08030702010e1207020103180f0803070906020a08090108041b0f09050c09150304081e1b01151406070b0109090201111c110a0c062105010b04062102 68
    0x3610924015802c1c0b0b042c043ea445c3c40411281005407442040d03e103080a55401035000d050b0b90800c0b00c501c14840c09020020030440400d03c010548102401c1303a40e4680600701070819030035504214210f60091082100042c0c20404452103200c007424070406564581c07501d2041805074620134039040c86120780c00244216020101d0054a0b00b03080c0c00e102c956500d08150f222400b80c0052175600004a90f00c55070040420b00c01150424007850404d880c0070200310b00040c0c001c404010542202400080056100803044442c03652071070180d00070703c00790121488011110501c0d000c1c09240b107070103825041c0699560780880b11502d80c082c2808000f5a901d82c0352200508030801c00340d01003460000c01044203140401d038140c001000d007940032070300003445004868026003081095241d100e4208503001140780090170f50020009562a0040f60440c61111208001c060600740341d0305040000602245030760358155000c0d152a81307001c81803000200080c1c1d40640c0001005e00d441440003400300384540 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 929633902 1250 929632652 929632657
    0x1206020c1608121314270402040b040b0a0603020a020a060515090708010803180109031506090f140a02070809091302090f06011d030309040204060305100e0402150a1b08 74
    0x40019042d1600101001e4040c0604d00c00c84491040507039002006100c4140e0160240640b90000340c0280b0207000c0400600380c41029072012600c15003240800c00003149418011003110080640b410301050501c038002c03950f203041600a10040c1500410760b0041e0310300c00c002e0f10718440c0e0800350500082c1040045034010380008016036020f8200c40000909076400340840c94120703400b0800440c03a01581081840e8102c0b003206c1c2c41c40c1000100d1030008042030711960154200c1c001703020001680c030f1800d00074404503841c003082d07102e1090400c40800e010020000529078451b0f10301c4c40240e86c9100c0d45c0351008540c803480d03e2190b4001032a40c207102e0500c5581136609529072003642c0c191015201d20311132601e8040300702c2c0c043c0c0c00034080741c0641c02481c010b41c0c00c80f08101d001030101c0e81000c0c00c05000030300341e0304282c1020b40000e81e40e5081011280204551000405904141200c103080680104240c4c980c13042d50f01d540c1c0c0c08005100345000c2d100300403d803151907030f10302d80c00d0480c0d20600d007603000c80d03 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 929635152 1250 929633902 929633909
    0xb040509070813060510090c030c030c032d06050d0b040506070c0b060d0215040801021804050702030909090309042306031b040906180501060f0806040c1206020c16 72
    0xa0059600240c0c109000c1d485140c00383e6114442d0300c00c02c0c030700e41e51a034000d4517004094030300d00078241400041088141c000c0c1e2400c0e80d46030310081950580107100600300d035801c900480030981071112080102d42051004c503814660b06490314000300e00303041d000001d001942d01550704202040c0569041c003c0384031040c2c1c0590701c500c06603a03445e107d504040b0342c4841c4186024106c080c2100100d44286450b410b007803811807000d845280314013100e811842941d0082c0d4820411130350001070114410034480b0100c0e4a41c041100c3c00c02090a0000000b0342d207004800c042c0380134006240200309410402c00035522800c800030802c0c0b26010408401001901c000d0000744081c40300d45001c40e8485c640411510101d0641c0304030146201c07000c00401001d072284a40a81d002d0380d98800e0f6000803001914a654018052400840c0300c81c0f80ca1005002400b01c1e07403008000d40c0281061000192030640010201c2c0d02c43c40400c0c1551946041c0540244a08415540a44101c038054038035201e40c0644a001c9 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 929636402 1250 929635152 929635159
    0x209061926030406110d0c0b0f04060b090405010c0e1e040506121c0305160f1b02150c06180a03030f0f02031302032109040c030908070804031b06050a0804050102090a0b0405 76
    0x950481d1000347c43c8100d150340018032854490300010443c56400d03040c0395219000301804141401c4410100c2c00074401a2416a1281d4452840745040c6400c85030b10711a80e202038440307280d04c4900307403070019803201c041504500c01e60312140455040e540e208505c542840440049c0c2d00c0b0b80621507102280d1528036810040400c1c100300c0050740c41120320152100848084c0c84078403000554070001c039030840c11440c00102d5291800031600250300c64050101d102d2000610085e0366a8040d0041807030904010708402410540400c2000c1004000c06e0310502e8076494200852405000301105014262544003110070510210800c4440121705c124400c150b1700940c281c50351903680700c0c1044525801d48600310400c1c0b90800a80300181441c2d40f00c2c1c42c0a81b02031070002803158059036801110381c444a829900440c001c20140140008080995a110041d0803031043e6180760075000307032040c0214010315041c440304000050504c6420b404132001588001e0080070700c95120540b502c0d0036045030084600 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 929637652 1250 929636402 929636413
    0x170604020904262508160624030b3105011e0209040c0206062209230105061807052209061406071e0302030405030d0507020906192603040611 62
    0x213036049045441182d03c1d00140110f10301700900600580c010f881c03c2d0700315016981c401c0c1c410b90080200264000a10f901c1810000192540c00d0450610070302500400c1d12031050030710680c00820040c40000c248440080b03225060300241483e50041400858044400c01c00303521165640e0400da0080c02c00c070200711410440c841c44084101da031804216522074020f110981904030b4014400040c0703030b101086c004040340c050301c982d071981c108100d1001c425054118034100140b1309407080c0203040d8130600507201c02540142041c10080c4412010b04a02d00740180080c4d8000140d0341c2c805001801d481d1010060f590569941da000020f0041c2d108602800441015052171460f04c1c3c4100c0d4551500321243d428035900060380c4010007805450200e05500c01084009545c0e102442001543d0000740c5480d074860140c0c0c0148601030200516042c841d40f000001e502d030850012004609856016035003088801e41c0e80d08100900c08010b0020301d2610003c900080c036141d2228402100c07024940036030700f = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 929638902 1250 929637652 929637697
    0x14070e030d0c11010507080405060f091f020c0d03110706080901060b0c0703140a0b07120e0c010210020a090521010b0105041a071e150617060402090426 67
    0x11203010030b0001c000c0c0540400181d00c0102d600c100040c1c900c090107806e040d45400d543d04006203e07940300440f10006000c002c130310725000f454407038904580780d2071401040f034405c0d0403040001c0d211011900c402d4890040345180d1400e06100c0c1c0c82d0100b24030b03102d904880081d41c5460018054440468981e400e039800c1c0440030407407040203030941e91030902080080c10110705541d9081843c181c44184d02010f440b030910f117a40403a007031042d46030052a41d51075038100710580512000a07a13210000944040c2d119500000041e41e0000e0000f41c660f10307a080c0103031500940e5904075824944c583c40b00d0751080c510a010304008840c221851800103c1d003000b0440c0810b10300065496015510500c01c180b81c00b207410300207000401000348000e510480c81502e4513492501003442403941c080f07050307c0005001010440c04807480c4a204040c0c104c0c0d000f400c04900d003040e0040d82c1ea040080001b40540982004902008040d040c10801919030041240030440211151410b0750420313030982c2480e1082d030f031001 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 929640152 1250 929638902 929638907
    0x224161104020405240c0d0518010c020d0b15210601090501030b0a0213051e0a0602070b09041109040c020d03141920041203020111040b1c14070e030d 66
    0x543c121240a00740c04500031206110500064044e8030074022800c0411017142101c00c00c0c000036011607855218561104050b80882c800e03e002a2021b03414007650b1504074000da920f0080b9600c1031540300040616940c2c1da404107103000c00880a6160300315104009a0942025030900401c00d200b1000459075a60380c1c441c240d00580d4020301c0003a040000c9000412040385842e002801e40360700421006400b19a903401040003404504003494104099800c4102e0311300d4601c41000090a2520080c50102d040100d400003503c99201e01c54421591010103840d20400301055501c56034005100300903030503031aa0040c0d1104548028200003918140b8920708642c1d41807102ca02880218000e0b40d180f01080083c200146188034030075400f01c1c82d0305507982c000c1001d05c2c000d001030041c624200400c5002032a010742550799030080424034840a02c800e000c02a04c90064490100281c1110410a001c403900b4200501000801c0300001d500c5104001c08a80c100005c284140d100354200d4000d14a0314104 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 929641402 1250 929640152 929640157
    0xa110c0309011d150703030b0a0308030f0901050108063709050f0d081303020a050a05010c02070b0306130903050f03010801060f0e07020627031306140a080103022416110402 76
    0xa03070209a00d13030301d001040802409045030a21a05001400b481d031000020401a4240e004030b40b004000030801c62601c900d1003120380c200e03407078030300030300c01541003880703032030b11200000e041ca07100140440e0700410460880c001340c612600c000040c1618990514034401c0940580c240543d030b0780c4500c83d030840001c08002582e00e42284169140d14194840141c402080c055080083e030031440345040c10804224284611030210784100000103603200b1150001c0d08180060b4402c0c0101c8405100308185501c0e140340003490548680c5000801d0f42e02461700f507072280140e0481240c1c041c13002c800495104015444101682c500c03110414803503030f58141c41500820100c4003400160000b1021130f02100001700301ca441801e180d000b0b240380441c0d83c1107242c0385030002080c440710f182e41c0c0c038410130980d904a145280d98220b59400b492811520184c0900710800c10711000f4045d16214001030410044403211000b51501e2a928554440c03007044d00700d44a0326030740b409590280101386150981d00d414400c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 929642652 1250 929641402 929641457
    0x6010f0b130e06040207060203070804020306060d02031e070f03061a040504080702040b1c030324030308190f0e1b0406081f0f1409120a090b030a110c030901 69
    0x210780240c1c50500310803100030403020703003460340081d024040720700040c0b07080c0091031190039240d807080d88920b464010145410300c0640041c0c05400c10004a00258401044e161a8102f015200b68082d900840b40c9a241c4085603002e0581c400040401004014407604900300540710302c601070410600d003400704001c0710300c1524010406801040480014203040d0400c0185142c014100b07040c0c004110f03c0a140214241d20483c006555205880c08079842d61028411910320030b0b540301c04031429598041d190010180c0217802d10040c10b40211409481d90b040310702d80c48030008090081150316030103256112140459004880903056241c2090b0900d489607604452004004190740400030036200c456450540030382078241d4030b500881070721050901411000395104804500300380341c0800280c0c140f0a820b0100240c1e00020011001c070707650b20401c584140e4a043d01d50940d603444252100008000208241240d0b100c0441d01c200d1184021014007821002a02e47e40240c410f05014000310b80707440e14 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 929643902 1250 929642652 929642677
    0x150702060a06090b092d010909140c061b010b060d0204090e0f0d0e04021e031008120318031b06060f01091503020a0c1e1103010902030607120f02030906010f0b 70
    0x1000491961940000140076070840707080900f06c0100080030000b111090300410f0449885480101c00c0100070303007074490b40298003000b1f8001441c0610004000c0c1c45008851050840d40c0b99a40399015000c0d8000348042500511107956882e600b081a4045d41051107401c4100d850301c0d203045800d030740128101c4485195480503203a0194000c0b0240c40c981d41e41c410454015600703000404400200d6a40031800c0d040300300c1c880e5100d1405040400440025030031440c465000b41c40d10214400c28401a00c1d00320b070500c010403021300c000100091460240c240c90550700300c0404a50004a032011404c2c0c1d010f03403020f45001d142c3e641d0420064503401a54480c408040c1c0381c010b00c0d09902442a03007d8404c0803298589541410302d1519100d81240301c0142c3c5c801340c5900424400d0400110100400e007582059000b482112925000a910389100500f00c4050116800b1002000b40c01a400b80c0c0c162040004215224101440140e950308400d018000720855a100c010802d4400e40c0190b480e48041ca0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 929645152 1250 929643902 929643919
    0x1b0305011e090c170c060f13120b0f1308120a051e010b0c0309060f0a0801050f030d030b0f12011407031b0e180c090f2709150702060a06090b 62
    0x3e4880b000704c0c0107581d0620f41c2809000c1d403c0e07410780c1e580e00040541451500d04507403940c000b908411a8150390794072004109501410100000c3d01e14031241c1e50044903500e941060340e44d0722101002911510740010040400080c0540c180210420480c0c0101c94140c020051640d039261480c5031031602c4200034442c00e40500c01006200c09080c020409440e0700001ea904040195001c1041d6401c8804011b2104101044080340b299000e032040c0c1c01050700300c0342c070300790504000042900c501c0e40d044080f04060f290051081c05484504440e90280005419001c1c01080421194001c2480440d50038840e0502004522031318407900940c007022203d40b00d074184c41140844140d03803a0405910f007541184a000500c0841203420350200e11901402c000790b0354401e01c46c0200280094880c1c161481021401c0c1084ca0388036508034901030501c0301100001c419110380400030702e082ca034804080c1d4404020300402c45216408240203000e0115840280300c2540c842850070180d42e004240c079500081030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 929646402 1250 929645152 929645159
    0x142b14070203120a090803010f150311040e060316080d0908060705042601050403030b040b18130609060c05040602120a080c090117090d0f0918091b0305011e090c 71
    0x60b030f0b820701d030009143c900004850780186c1c2d0364100ca4100744d20200300b14101c100f0070040d41e0030b681040507510325646010440c0d11510400c4400c140035601410703400032043c40c000f541b10303107003044003110688103a20061021659a0304441e0b40d94494001440040d070410800621020f0020340b950180f800c81c1c031041e0074241883c01c0c0305c00e5100b00e5101151070340d898040e000e02c00b0b9001c0c46131034001e40c041d076070204512034840705000c107072400c011005001c1c20711041030800300d82801007803d03006a0400e90b05000c0d48079034100343c0d000c0d00b1005400740c1070764504170080c0080d942000007441225110340079941c40b0141420940d0484c001c1c5941100820307140b20010f40108a80402840c10980504089000c00380d4002410a030301c10841b50309280c0e80c800c0c1d009000490700041e05000b4440d40b0700d0710450303150604002c850304080710441610103680f240604420007220b552100c481d80c0d03484000c40005a6681001c0340601000fa00b50134450103a03003c90750212800e400f07100345050704421441001340c40c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 929647652 1250 929646402 929646427
    0x20d0e0a030b1b07390303080702010f060f060e0105030c070204050726151207090203040f050609100b0a03080909190e15070201020c0a03142b14070203 67
    0xb004100074a0600d50890607801c0341c6014018203545401403100d02520f40c910400101044002c4c0a06503c0b0020350742444103078442c659086003600e03814585401c4589a0340c0d8181d000d090070f2041c0d0b4220605094000c80d84540d4a01c50400301d554030f0b41e07a500c42c2d0190302d00646103440b0540c0c0c0054996010000c0d88007604040d0030a40d00501c092038104442e4152040d0703c100d035016101d01005038007603c0244032109608546600082d50110b8007056180c1c0b61101c290380c0c0e5240340c40307540185500400001c0c14040d54640050200780c0041c10b450035454200c0c3d042d5291440155522800d030700c1d10940e1001400e1281180b4256540034035618504120f074003c000c4828070040842e080c08109010b0072281ea0f07140d00407080e054840354028140904000c5600082c2c0c28000d20800440e803051100c04001800010107542c007503010304110645440c0d56210001503c00e507040b02300c16001c440151311529a400e0025001c6400002d402c00c520036a4046408450748151506e000592080c080d80148a0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 929648902 1250 929647652 929647673
    0x105060304080d0c200109050f010b0a091a060403080408011109060d151a120a050702060610050d060f0303020d030903120e0a1e030f0e062703070305010c020d0e0a03 73
    0x40c4e041c2400582c81e041d070445040f00700080b50701c01c40c2a9441b18482c4040200c1002000c0b00412044000e00180141c50080b80440d2542c0c400c90480035224440850701e40e0026001c20080d020251030255225200d082c0711640d54018810031031190700e46941d1100d003002210550303c034542d000f480c1c43d03c0c040c48403071403001502864407000d0206d088034a002410180c5800c121000d07000302c7d03020903210710342c00452606204004003101c084904250420903810b6020601c9903000704215003500780700d031400204842e24081c4040d9981006e1900b88046220301e01c0c624808100c034481c0d0308444641205090447c1541e810300e1001300440d880c1039000084610301e80000b028101060102e803c0e00b8043d881c0d45400560a85800c1c0800701c00e200d50009145e4000c100c03106100a90804805107880d00e008100f6520a02d0310012014004c82114400c2e02150040c400b5503540c001c007201c00c1a52079041440c000c000341070880c0e000d071007444016403800707010700c6d40700c9039400c8020403610300d0a00e0f50b280c1d446840e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 929650152 1250 929648902 929648921
    0x80304030b06061b060901110405100302070807060903080105121b100c0803041a0f04050606010e06040312020601052407060b12070905160305162709090b0105060304080d 75
    0xf00601c10710b503580c48038081210703021107584001c0c60f450030054041400c540f410305203840d01101c00c220922a84d100c450101c4a8001d56180c016518205410014124054017600411243c00c1400314802d05038040c45039410f81e4070483e00c501c0c0420501d090740323503140488644a4641007440380310302c4241c5807043c021000ca00441c02d2074909011f05036940b40f880c0e801118111070109802182003c06c2c004641c3c07559118242c00a04900c0c1e00341038913915a40c01e001014070341046a403800d180c01e00c1c2c17920819580150f90120fa42880140f81400c040d4032800c007402618058140b8a200343c005018146906106658440c07e40345001c0150b250701d40500001200c00c0c5d000b01c886810414844030400441c0e005245a42000405040c03410b242640080d03071805020070503003044144032400000d401d25800780c0316241000030070341b008041c1085a6070042c03807000f418411f89403000640614960414080a0710810000b000d070ba80798070801405020607075000d00220130501040001c90b51035030000720103 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 929651402 1250 929650152 929650159
    0x607080603191b0605040806040f030c0b04030215091b06160803011215050415020d0b1c0303060f030b06010f020c03060106050d05090c06091c051b19080304030b06 72
    0x201c48500400140211a0384412902d43d000050584146840c8007a000090003140c9404d910303143c507000d001969040e000d030010b4825040322034141e04041c003030320744001980c0c0c4c807004000c0180307040d060113501c0f803403642c80a40b640405000011240f036004501024420f6010f140e0b80c900c03030412004d101c0150044a50028050612240040403a10380070103035000740091400745600b55454a007039825240404940b1504a007810706000000fa02c5000032034001c0d1010000503102c1c00703102d00c84c0010b0802d1901d03054010030040b000700d003078030000c900303400f1900e000e61001d2244543c3c84800c08070019140c81701a00300503910020810640c41307105030501b1002c0c244129540c980b01940002d051a00a07804040400c03400200580c0c004800d001c3c05900803140405800c80c070b0905070128525104810a09220f04410302c80e4942c19019000410700043c0c024080382c0b48880302c050720f00b0410b20701140076403051180c40f0751810352102252461302a10301c45403313942003500d103582e10303d2016000340203c0d50 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 929652652 1250 929651402 929651413
    0x60506240316021002030a0504030908030310051018031203110309030a0c080408160303111f0213120624061b0c0302130515041a0d0602040e09070f050904050607080603 74
    0x50100d15170000c0d50152035203040024817400c3c2807a000c0c0c404c0020364491860307a00184204146141100b0060040b142c0c00d940000b141060003004940f030005000d42130346020603801000c02804003103242d0000c00c240f140c07400c12030f111500c410189980811940e60040b035004204d02d4034070620610100c906c06100e60003203802c1a07110702c66142050310703910506100c000145001c00c24543d004a00f40b200b2360100d0003800d2244140703914103548070041c2840c201a690000b58041a0403004101c41c40240281542c810b085107091600740b01a12000050381030b04d005250b0049503080620204804a440d90380ba07201c03581c0390600103018000141101511220020b000c0000961941105041003811154001901386041841030583c940d408608501452030801030020115400071007100b8440115051400510076240110192096030450b0445102c440c00380031100300001105c1d403d40d401489504070003a1500d01307000a8140844014203198805008078040c58000c030015600414054144d41 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 929653902 1250 929652652 929652673
    0x1809050a051f062322020403051213090b04060e0c0a081f18020d0c020d08090127020111031605010b12030403030f0c02040906050624031602 62
    0x1810004610015141508100035440c00a00d010710b410039a2103400e8800c0101500f422824a8500d94421089441c160540c50b1082565600c01078000b0319600395409041302581d600710300f03001e5042884112014810701110740680c06140e02590003814041c00c5100005107402c2451028043c500501500207580c3c45020800540e014920f40c80380c9010012a0303982d01014100030001003000304001c0700d5000f8842c40d0382d2a0038031f242001040f130344000d40c0e01e229142171090407070081c459082d00c0b04d2418074201301d031504580c010521030603000f0103440e0440b669540c031500c5800d0741c0e00b428440b10144e00784c0e0281882c1040744110760103610300601d131035517845501c1c0d84443e1555018600159009602400740010410240240029608242e80e010812a41d44407a81e65900039808010144030712880c90351152032080d12030640c281e40040c01440310b50038909144004040075202c2c01e001d10541c6290a1080c0c030400d5403503480051031011249551b40780d580f0480519440a10001180079489400 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 929655152 1250 929653902 929653913
    0x2b060b060a0509091b09120c1207030b070807020a480506070b0705160507030f06050a0207021f05040e01031a060319020904020d080a030e061b041809 66
    0x3440003800640301d42c0c0d541c00650041100451009011068004081305540c0d4485043c0082e2000c2a000342c8500540149101c901e81c1400c2a280c00c1940000f045400780c1030704500018044202c030702510101075662590b560803038400c4070403141d420250b8040c800440000301c41c8607c1951414103078003503440000c9002c41c45c0d100015050303142040758542d22001031001000d100200e008190445d40b45107001c0e83c0c1d03641d0800d4400014035900074800d0210311403e5100003804401162030b4044156102640c807403400c0c40a04003612003d454242c60540050321407842031017122a2150010000310088112005010800000d110414100300040c800002e07910000b0306010f01031403141140c0040e58184c4583d035400c010000340568420b6000d031107001041c4042c40304102c60315030152804121556240013140c41612540d000602a400003c1c0c003080c880e80c5030713000e00b0300c10140200750340e0035403901125001c00e001020000e000351401003108021340a1548518960591a810042207550305a141d0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 929656402 1250 929655152 929655157
    0x302101107031212020a03061a090918070b0c0303040c0617310302010e0d094a0601020606010e210c0303040b07170301151101090204060f03030801052b060b06 70
    0x4040102380c540c00148030060b01c09403407202c54070000030303c1030908203000e000641c0184050320091815011007441050110b092111402030b00320000095a00c030b40007040d90341e1325401101d05482203000c0303480100700107101d000c1c001900001d40e4810101d40d16660000b10060305a40100c24031000510300104095090503079411402d8001e400019071040340180807424501440b12003003c101c1d0310311040c0820b0805182c2d403003450100300c50104c00723401c400c501205030034148485c00c0c00c0c503070f460480700c1c40241e0700c2d0200d00c0c8030317a13420f0b401c0e80d4594540307200566040c1c0c140c1c100791b90300280c511403444102c0000c1101402001c18542110005400301011a06540c019004180c02c03450004298003800001083c0e011018000040c49246614084443d10348100c140d4490041280314200001d002400750450b41c142070300107008202c4039980c2e4050320b141c20b0961004174081048074000080901d400f210500312080f0072442640030090002d192510710303002c0c201c01c8615581d58048a03400c1c0c0c035403002 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 929657652 1250 929656402 929656417
    0x5090d1b061202030c03071404030812090d02060103081b07031a0f0c03060d39050102010b03010905060403030c09030c08010203070e1e011404050415030210110703121202 75
    0x142194606010000b04080d8548480c000064010400d01041d018044110b1381c1c0141d452a0600008c402d80e025500c80b4407a641c40079105400100b42c42c40008a40309901c1e0113405410b049032020391072140c0582e11010244800323081048240b00c00101d00140c0c20f510149414501c0660354101e40713a6459580c6040e0f6400030340c60144030581000069624048481c3d0000900c001460445c54804001003494942000003070000904440e5505a003035183c4100941000c01c600b001c0050011214180c264002845007034015800d01c1134000803030a0602c9442c0d401b9400c00040c3c4007a94403900d0a80280c100140d0000801440340000404034061031040780103020114009641c3c0d0600020003082107850581e1103116440b00306451840e05180340d64203134010402c1c200001c619202c05400c00960140b41e1205420070f0400c03052684400c0c030b64100d0b00a40c0d02c02c0b2052003803000c01403401c5030080b034041c4c3c0404041e40207031802d2001ca110004540005016880c04400ba901c403080a10240c2e04600c0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 929658902 1250 929657652 929657693
    0x3040509090109050d020a111924021603080910050c0a21050c0307030f1b050708060c03062d060a080405070503030a090608040804050603010b180f090705090d 70
    0x10441400c002c001d0042171040c1c4440d10003084103216944407051006044d546803881007030704913280c0480400700030300e010003800c1d1f4103811078a100891001502d03186041c1103180c0140942c1d03095105a000c19411360082d66005500182000e900c001480000b007a12050307041404000c0c8222010a030b001c1021104452042480309c0d80c02409030000100c034030310b081d030040030f000d07050055004a1302c0010507207000c56010301d00902c0700c1010580030341700e040801030740e8901595103140c0d00c0c042c0440080c81204461000c13044034910ba60701c841c03c4a8601040c1c23106603000140009056000f0408422024140600b03482140034482c140c000860b2030b1301113400300011840300e90400060240911404d00100020380145281c600150380050221815000360b006100108001c41c0500130080240e8010342005881c1c01d5503035849001028458110815000b074014011001d03860340d060034444042c01c803202811a5403251911101919590000031101d0f412020000902c0701058400b61039090200e4241d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 929660152 1250 929658902 929658911
    0xa08122508041d0c04060e010c020f0a060f02070f140111120d0c080f09030429030109020408070f03110915030a0804090c1b020d1b0b03012c0a020c030405090901 71
    0x81080b995901c0c0010411034411074240420044590401c1f0050080310003464403c0404d0a01e10004042c0c180c80403840f03400440740c0c800800c00d19000300f21050021040c4d0202d03612603541d152520500081ca006016000004080f464100d50140b10480400f85000d016143e00c207114481c0c41c413242e00281d00c180314031516802384009140d00170130442d80125038040e1032501031a022159075620b1041d40703e0003600300e03500740b030101a0800f503251940300c44455001c8260b8030750352411310101a401c5801650343c0c6000324240080c0d211442000142203a512980407a074009503002003000810000304501d1f10080e409044648940d014004460040c0c4a89601901da030700b414148021a900c80c81100e060000105034401008907140d01c0c81190396044800752541c407840d15080c220599100a1030b03420815081d8003040303840300000614169640d440ba8800c1004110b144203c03040c0051342201040001034010500d000d820303400810003c098401241d28041c3c0d200003280b80c0d148101c0c0c04905a9554 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 929661402 1250 929660152 929660189
    0x402060f1c1a1c170319110a021c090612020903030a0314100e0c030705070b01060801031704060f0e0f1c0c14060406030203060a0f080c0a0812250804 66
    0x29a044403001c2c1c40c0c20705603220058155071401300805040d01c404a05010110000b600b8200c610000d4046000201050200a1048001415a4121500c0d0201500901646800f0192001410342c1010800e503039800e0701d146002e5040e92141520340382c2c171058503020000350501c1d4034200700901e04d00c10f140c1c0d00000c00280a4202500701c60340035140d40340704501c04104115811690103039a801505d4034506a940392109242075403544900a001080040104000243c458010715114102e0f4002c58076140c03603e8200070f00c440c5a01c203d000e1980894002c800b00c40c0c1c1284161034685040e140505210103038122035001585c55481d8114800b5841280000b282c10800368001200003820140d0a501c000b103220400120280624024141056800b00000e9407076512400b0b43d00c02010825243d01d00f058030313420b949807034848401d000c500034a10b000c0b00052070100028005ca004240786500c0d810030801210300c2c2c5c440032144540c10910517025104102040600b00140002e00302035154044040c003 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 929662652 1250 929661402 929661409
    0xf0703030c0f020309060c10141503010b2b06021b1002090f13090204020706020c010b0a080d05090316240e010c06020304020d0f06050a0605090402060f1c1a 69
    0x1d414000d50810502d40c60303201040b07400005031500f02c81c1c219042034035480740382a818039000c58000d5101c2d95909089401080f440102c1006004200790449004d528400f4000e0509950f01c5c00045c40d00a42c00600c900075000c00c1d00c001100d001c0a1003002400e5007100e4558801707a0704400d2030700381c180c032850100c1c42c0740003010040456078182204c019424242154000b5010940141e0001e000300b202c1040300c5000080b56000c11000c1d03600034401c5494110300d0074140300035009400d4000440d1700c0c0410111141c07500c902041e00b110015401000100801141120281c110000c0302e500f5103d00d094040c24800340036240c2c0302406182c1c14180c503a004519000c85881e03489070501013800b886108894040e6801003101d0b5210b071b000403026035262900e201207140309506101c06031120a943c040902008080d402450107640e0058007800310039100c50400407552000d4500a5020400700640e08c403001c1c8260151a1099506158024803404494a01d00b44c8884600c81d922151000002c3e101918 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 929663902 1250 929662652 929662661
    0x305090c0109150e031c0518090906060411070c080f121305010c150203070c140115210506090304150905060d1d0d08090105060102120a0c170f070303 66
    0x900034a400c40220f03150040c841c1d40e211402c28044100084c0807040d03072840c5c40070080300c036414801c03044c4085012803155004006800040c0b0803140328500d02102307030040c5040499140506440c501170011620343d1410440103001d1120340c0054010248101400300300a44003850080c2800780103045001030006009050a01041400a59040510601503200d08030f1852100f550401e0810070140240d0f42401c0b44d041d0101040c1c0074806000000b0019002da0001601c00c040340f01d074400c1006038041c0c04030142078a1144405240f600085602048540c000808454006c800320b019058241c146443c0c90b03040c002e0840d61050310354000201000f007820b00c00d070440700c202003e152410310746051200180440c4181008026a20f44941007070856070004051410823050140854101002140021701200e0045440700304d03651801e400a1101c1d4004142c2510142e0158400c9103072a800741001e440780100c010b0140c88191840300c10740002204100104101c5100740d80c0720343c40d0f041c01e150081c143c9 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 929665152 1250 929663902 929663923
    0xe1905090609101406090603181e10020f0708040803040e06100815011107090f0b0402070314070807060603030e040c020109030210020715020f090109080a080414031c030509 76
    0x44900750204152140d0815107a0103451948145030384c80d031810000035440e8002c1040e445d40c010000020b0205480604640e129005481303400d490141701078440e00e54005c84031070540842900500d250f880059401e034001c0c5036280c4061800342c240655a01d0329555504160440c00e1603610004084c41700300b0000c0c8078180e0001c4116001d1250341180d500003171080c1d10140502d640a1003903002c00c0d22aa000380050b00d075444800003101d000f00d0355540301c034000e8880ba04820001324909003c3c10310b91f003810f0086409aa816841f8204880c030181e01940d4a94080d440503203800000b400740381c1c0010403902a20004501983d110382d04203005a0411003280d0b04a410740085d03a14284880000980209680208009144006840700401d00f890000d00c80c401144811103440042d00303130100f00392030025007009102a41c41c0c0d12a1034981c10403982d208140b600c003a00b03401c410321041003400315440c0b889041f50070250540c0c050b0844410740110150619580c100441d407150308001000741c0c2081045040c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 929666402 1250 929665152 929665159
    0x1060b0702190b09040c110a0c050f0301050c0426010608011406060a120b010201020c01050c0406091a070609061b03090b0c090d0602280c05060a0b031506010e19050906 74
    0x41a20f0001c100c0400d10442405500813034440200c00341050042c910030381004802d00c242c803006a210310344030ba1f00c44030700c0c000e040c4528442c0c43c09489078201441030034481c82112803001d260900b46102da5490701202007598444507000c501d0403000c25404c7c000d202c0144118000400c01c080b0031141402c9100000b419076005140c1402802640fa40c130050700750542c2c6181000240309050280100d0180c858550401d000e58200021f0010340403020000f03104444840e60703040c1c2400d440d09600315241e0000d0217030380349940003807004001203915176008102152040ea4000b5042c00d01d01c1c0c4141d1b0b0050003030511008255548461030510070004200381c0d001d000c2181491070324178104001018494101805000140e01145c0100034144080e000640c04000114608901c40e01d0f900c01041700328030300012699030203410041001503003503001d0501c07800d00c02009041e295440d81105401c2d80e01c000c1203141005a804600c8401e42c5680c0c0314008801031a107211560315061038240a1581c20140c5010302 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 929667652 1250 929666402 929666449
    0xb150c0c210307020114160c030b0604050f18011e0b0a05010816050c120325020c09010302010f030615020307020118061421240a0602120d0e01060b0702 67
    0x246503002c401c88007001c0e42402c189036103940c9460410500d0048198820704c0b240d80e003035050203116001c1000c034200c070301c2051840716507652a81400150340c01a29583c1c01005050081170792001c003503c800c80c1e00381300c4800018650b1100100f410b9103840d0042c002c01d0050351294445c3e0203050070004980600803c3c02c00000c141070400c0540c102e4100340e080042041000310b1001060075027444880d241c083d40000040d201e041c640406161401ca001071308003001400c044215900b800410200c0607040c00500f90340041c1e00c0c0d0340064402d401205650404c040d668900442c0d01e80c1819041a94004540d0013541c031600ea920025001d884003060240c403681031200100b00d6241e200781454101100d6003809030f00c0c0c10a5a0522865905200001c40b080880e0300070844000600a422003a001d80100340281c60103191040c0b0029690900a040c01a00583d002e0580880349400a000d240c040850004041c1d50004507a800c44025801c03980501c80300185440562609044c50440c1510f0350312541d0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 929668902 1250 929667652 929667709
    0x308091e1b01050702040606091e0b0405060a0215070503010617130f030507120302070215120c090a1805011a0f0910050702090a140a0c0c02040b150c0c 67
    0x280e07500d280d40300c03110507200024400d04640e4800c5040d03441c8035502a0040c00403544881c0003030220710041c040c04881014040e0031042e19101d015100003115032000142d0300c2e003800c060500400b940700c1d0012400b1340c81000c008603d68855070441612030100c50b607481c3d449504000700104010004007801c006140b040080c80980004070401c1d0b500590b10000c005c41101e400c0c5400e98a41c003429001400a01d089880010300c0c1e605034005000d214421214080c060390122a0b0101d03900808402060b02c0040c2000145448410340040143c0000109030390800d550b10400c1c52110300f001c0510404140d1140010005952a54501c1c40310a400361846410100300c61910f0050b4001e103103d641c41040d40403907140003140a08110303020b07680c001d01450003519003203030120040e10440304103500030f1440400154a1041c136119682030241103541d10518003e60b6020040500955120701e50300602c0101c9c078000c20034001005008d11040c1c1005000615004010003415071030807200c4481810345400c021 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 929670152 1250 929668902 929668963
    0x90f01170a0201090b070f23190b060405060a0b0c030712020f0a030f030f051303080106180e040503040909380f071124060f1012140103030809 63
    0x203400e94100030400e13034485d2511f0078080c071544038000001d087c60f1f00c4012030502c04455560003004140e168002c44080302084000081c60061082e8080c2c01c001c1c0e401c0114074645065007005e500144000d02c002c0d202601c41454041d00d0b402002d0180040e0700004412041020b10048500583c801d400a07190341500305c01940e03142c18100d0380050070080c821214031002070082d40249a018001c0b00c1c00c201919000d0000c104d441c42022081e00840c00b5078000040742403043c0940c0c1d0741e0703011106064030094900b0b6070b5580030000142045556001c14030001c03d40484620800c11814014480c00c040d00d1002c908030305001c1030861480044c1c03071480d920401c40601d003409281c0c1285000000c0c50859503442c8044400007183c01010503a0f019150020304020300c5a040131003c0b03102d500c03004209403504020020f186012020498010200e80c00d1000503600801400d01c1c03600c007044020900b65071108821802484c26002180480c541205204000208100c10658500c102004914210655104 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 929671402 1250 929670152 929670167
    0x17010503070e090a061b110d0504090f020c03070b010513050103050d05034c0312080912030a0f0516020618100f021e042d05090f01170a0201 62
    0x40d664020001400f04500b00c80410420820742c1d0444810445002c0c5414050395054804200e1400540d40b044040302c2e00f040484ea0f1660042c1d00d8890030b18040c81c004003440503102400421810a90074005060040400c0c001000501d10030340101c0f00b158105420099040459000e601030245850014400103100042007020701d4181c0c10850786941d40d8803480e40c02d48004004064038503c0f0065001821000040616030009242202c4945061100401c001c455130f5888054050700760b100011190a005480c00747e00514507805035000030000780c00d1403040d071380b00340c5074800416980d038098071007480e19108040d004020312030301310048046180000d545550141c607240b2001e0340800e00c0380b444d40040001a4110010000c2413180b01450020300d0020b402800c1050401c01d842e10000e03503000d6420084074152080c440303603143e420528500c84d1107020501101c03010001c5414901140b56581c41c0ca681e8403a0503402e54400c030960405c60140300003402d210070300d207403a40114031031070060303802446 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 929672652 1250 929671402 929671409
    0x51914030406320d090c090e0a0b0c04121203060608191104051203220e191806092607020609030309040c0801080c1009090b0a05100f1701050307 64
    0x11000301410060007181d030f4001e8504180c082075180003030494580980c03a0000b00c1d0071802482180440d80c1c0d03c500c207005940d00094005c200fa04900151000141031012207031f0490040100581815120030709802c0c900300070001511060304070744110031807030b034507028500180071030b45841d5029081c2800c52700f4000c0e6000348d4180325541c640d000380c5a50303114802503800a000060980008480040c149078482d40020202502c24110303030510200011008100ea0841d40358a00c0c800c01c0780c2d608c11070601e4520001c241d0b80d10301600d5180c24064101400442c1848034001c031800100c440c030501d440079200b100c201c0ca0b00d1440900e40030000107000481c00350340e081e503010742d86142e4604c0d021000a04512620150a91052820700340000c41984443c85605071070964044402c03410f0b95604010046002c191144001031002000707011494613500251204c45000e404111420b40300e40008034090310b1070a0600000b01e00041984000d40c0c00312480101007031001d035155455041101090300c6054500 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 929673902 1250 929672652 929672687
    0xb0906400503030703060512061605031b2803050405100e07120c0302150c0703060b01110d080a150e0f18010c0905090705090d1e051914030406 63
    0x81609104032090301100c000c9030351041c1030301d5407490701c04e40180042c010f40c040c1a000c4d1200441042003a080021014000c2d51081e010050700c2d44074480407540b5600040c01c1c188503080d0712607000c01c1e01061801030941085501109110101d03003040000110b403c4035246d100309420841032101084021605a20000d880c2c9004110311181d111190700c3c002c00ca1b0300c800098a084603907441480420318020043e40e2080b01d01052a026003650f0a106000f225030002a41e0044041000000d400794030400a400c4181408944510b505400d40c0c200300072644070802150002d0100451038009108a01c15583c900041075a034600b09a81c003c441600200b4045c4c1c000e80e03000114030300000e0124010300114036500240050915281d008007042c0c2c040c4902800741d80910080758150703000d00d0558566580142134103006144544a44812542416100e004101c2032000100400e00600500c182204800f145102001103803811a51b86c40307514070100202c4d0810b000501041c2d82c042c00406000340e658 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 929675152 1250 929673902 929673991
    0x6030b040c031b080c1b030901020f2a1503090604030f0207060815030a1b0f0e040506041104020c0f07030c1703041404020d0504150509010219180e01030b0906 70
    0x10f1038110410300c40c05a0100b801b52009000f5410100d001000b08480700b400c0c1d0075200900220211030341d4542d082180fa0801d410750300404141e202400e0900a0341c0c81d8000c04a00c00c44412100181c06030303205580c6601582c00c080b040009154000c13005001c0684148001d091503403030a0002007038103030060101c3d000441420720252190b0340400180c040c035900a04680c40c05404500400c80c10f040c03074402c468a5034030207140003036040c50015046100ba500080581808da80300d41e107030b50130f07520a070320015485a0b0900c01c0c40c3c10400108030346030401c84070400800e125070445c2000d9030301c50840d41c010f5803002000030b080d4458031400700540b4100c0f600c0ba8040300c0005d0400c00000c000c0e0007028000d43c1841c2c50202004240045e2150071055201205420015912600000c6090344985090007801416001840d10100c2c411000803200e801000750710025641c131f0340184155840203920a450244e40303041400403903c414010b45800443c1c0821412000040c14a0a2062107030450040c003c985203 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 929676258 1106 929675152 929675161
    0xf0c010e01060612020c011d0709060506071e0819120b03120415050d050703060518010e0c1614070f080c0d14030c0706030b040c031b08 60
    0x3d40d80d4210400002d43c150328080d620520b203024280d940d40390514a090300700b105440200582130081d040345032401070754906a4100c0d820242c4102d40070001c145c0056003000702d851020b412501c0c10074100300c02c5d00f8040010302402c0145000780c0c62020845e03103aa0743c0006500f9809030143e104008400700ba1044c0340e501c416005154140d00030030042801525081e2468130052801840c18600d010703005840441030350019181c0c6400329803102400e110138079060b04113520b00142c455150b0f003d580b602001c1d0100880c003804e11074421000180075181e1101413078045580c61303044505200c0041d44003046560300c04043c07241c2a03030a1040c0d01c1c04502070a02040c10411040d00500074540100c89445580c0300f032626200f040040d10040081041d225402c2c003021000703041c1e9840c0000c040c00508188030076284070500440402d0f1030721031815484030081c80d034144965450301e8200c56544d44c = true := by decide +kernel

theorem cover : BRFrame.Cov 929496402 929676258 := by
  have h0 := BRFrame.cov_init 929496402
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929496402 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 929496402 ≤ n) (h2 : n < 929676258) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
