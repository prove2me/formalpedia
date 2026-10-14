-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0425
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:44:56.212874+00:00
-- url     : https://prove2.me/submissions/2dd3b19b-1995-435b-b19f-ddbf0c0b5e01

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 76258994 ≤ n < 76438850 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 76260244 1250 76258994 76259003
    0xb0703030b0405190905010b030114010f06082206090204091214030f01090203040206070f030905040e030a080711030d050109020903151b130e1305010606020d02030702121f020304 79
    0x304100700301c100000d85604480d0324032142284c40249040c00c0c02e0b50030205400e03000f50000680c0307006c403034046403c0d14080c4c8000e45094950100400c00c1c03071501c4a05000a00c2e803890082c02c641000b0300309507074501c0d80090705e091212a000b01c50081c441591700c001c183c0c82d401801088543d056141041500d02c107000a180401c4071000b868422841d5003003124450580380c20b08942d0381e8207080d071010003900f0241060b42c0040341070060344009010b01d00076071291800307521505d1b10030380703802e0800c03007550301c03524886215400520410043d03a8200c1a49074100d0214105039803800382a2010a155000708100a10914209400000e41c403825074020400442c7c280c01752101d42580c10025461850300307480c496001030800c0b08207801c6541a030050513040030742d0408001c1c01c1d585d46c1807250306a8000c0d28100c5c882e00701d14005c0030801c6400d02c11000101000c1c00541304110700340e48040d40b0307070207883c5000c2d000301c002030421803503500d080c01030024003151030b42c68490b101c8000c00150f0085d0401c84040300c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 76261494 1250 76260244 76260251
    0x108040320060f0703060b0906031003081305040c050702010e12030d06060c05010b0303070c03060f0912050309011d03040308030411040e0d110303060603011401030b030d02010b01020705060702010f0f05040306060b070303 97
    0x301e60902c203001d49400d40e03900402d000d1400303901d52305000b0391350310042551030300b5210000c0210000d0a40f000402d01903d4246100800c2c0e82032204020440d0224000c200500c4020085c400050740c01c46207002d0070100445814801d52046411207081d446841c5050f04041d1070014042b4003075420241c1c4180d242d0050000700301c407100e6001855524450f0700805018440700010410020301680c001b00c20070051502c01040d0f0241070b660740030031502c941c00b4410200f4404001c119054a0074803c1a40c1125030340009030580000070301e0365840703100d54040500051400400101840a0503541c0c0c0b0719044050000c200101080c01559110200c7d84511400035101c0002000e100c80e00100b0b0703130f000e42ca00030f00321032031a403819a01000303220703601e40f0355414103446902a50141e90140b0a02c0091200da8000ac03800c0190600028145402608101e1282c04141700c0e5402507648190210302c014040d04006110145203482640c0c1401141d000420039401c0003c041410800c0c0d4010f00360391842500c091 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 76262744 1250 76261494 76261501
    0x127050609010218060c120a0e09090706050913090b04080c0706080919031106040c050a060305130305031b0301030501020a030e03070f0602092209031b030203090108040320060f 78
    0x240c0c240d210380343c0c1d0301c011000d210304084e0349850400c000b0143c114414080300c2081a1040d6503010b1600404441000300e032003903003089600c2c10881a8940e0040e400b202416074141400009803850042c10b1180d80542090080100c1c1001d850303001d01c0710250404210515071426240c0807055074072070510300c0d01c0da000f02c202c00203e6074000c140b55800785119002400700d0045c1c002654183c440c0d0720100780d080000c442d1b000a5241d2041c443c55000f1350190303100e0480c1c0c1e03081c20280100384546520080401d4036081c200400840c8128681d010b49504d071070301a030b49490f44c0c0398102c00200c0b4000e246010010000000082000550040c91442590346061100c001110100d68890091604c0904154020010a000910355138028403224000030b00c0c40888a175000311541d41c8254140210b01034903650030a043c14180c12a0703074140250700300107030b01030304003000d0394000d45900507030411074140032403400803034100340c02101c1c5a4520200741d0000e0041e590aa40496511081a904160300c4004103010 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 76263994 1250 76262744 76262761
    0x3051b0306090705010c06061d1006020a0f0b0612070626060108070f02010f020d02040302091f0b07020604030204091101030e06090d0e0a0f030b0f100510030e01270506 74
    0x10a110b081c0c0000078002440c40c000041d03550b80004c00d000c5030180d54840020510f031540003913090291040c403a20b5806480c009546458010041d0011030555010880c2c15000a104090b800010390f4010704204c901c1d01c0f103401203020540c508003075201e640240d940206088d40d2005d243c0c1e900004141c8100c0001c44441a08000b440003a03544a0000e005100015901802000d05003c42105403000107072001050045404980169244c0c441d002d80014007082549400728a90f500070041c0c0c101204000c42d4000c00244a4140c1c0c481d45804030404654582559a51010f50300296005081032003410064a808542d421a02d11681c0c08286400301c40d6080e5003000039000d1040540c440102005a41800c09851285071303100016070000c4881004200d80031134003580340040d4030400b11240203040810421540880090611b4410004044104040c0d1f507202070306890040d490800282d0000f010f021a80500402c1301ca050400002c00d80800c0190803080342000828082e000351071850b10786007213 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 76265244 1250 76263994 76264003
    0x50103051018031403100f1401031128050904020319140106020c040902031606090303120203061f031d0f0c0103051003060506010903050a050309090601052706070c03051b03 76
    0x3400113035a00c5810101d0302200c500450b08104c541c2c0301060200d0b50741d80418504500741d00b083da2041c030314262909040d40c06015201460102185440c20411480103010342c40e81d01c43e000e06d056a025503508201940a64205c4440180c050019907880c0307000c001a034000d000c000d000121040c500811540304c210b030924501c0c140d440c0c9030302501550482408000160814200580e854081c8550366141c5692a030741d598010315140d100c2c030044074a50700700a040035880790403480e07450b401002000855560030b115241c0c21f80302190190340701550204102d0041c990001c41d411500c5070040e5850f981c020009021501c0c0c01c4c41c0c4200c0d00f142d5455401101560b400b40c4404444060840003030001610681060390300041c18504009429604c0c0c071803c1c90420080025035054000041c10103885c00c190a0f030f203502442c00c0c00c1c094640b0100005a5001046444135038604d452544204030459550704222900d041d004681e00a0325602ca06003640c59102c550303860408840441d110b10510b040229 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 76266494 1250 76265244 76265291
    0xa0e090906040201030b150c0a020901081606030c0314100e13080702060a02120304030305040c060c0210030e0c0301060f180509030a0c02042c07060302031b0d0e010501030510 77
    0x203024040c182c44030380c01500a0038a141d0b006500c0251071105003c9100410054074408060744003c045910741d80c014486d041e9410303045940c541e04581000f0389050840b03540542280c90310314001900420180080f00144140000b0101c44d159180522500c298076581100503164900515805030b211160b00d608030b804461401460400140607120140c684000540900f00984c01511022103104852010a44c000c031400c5010958030000c0c04103100020b203440300a04481c4c10302601c0e00410b0340000721034403041e120200400d03417202c4c1c0408080e002846043d09026020380240407560303c0c1c056850041583e40207001c1c80a1528080d003290b0900c03801010300800000c4c024600d005685801240d024003480801c3c0c0c0c00c80e445d6040582d041c007a608141c008070301e5581c00342110a100e6000f9a0501d00709a010104050051085c0f00740800300c00e003c1d803c9603003041301481e500d040c2d050345240503003606d10780e41489500c1c110000040c404046128652002c415804011007100860600c00d80e44422 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 76267744 1250 76266494 76266511
    0x7020415050307060516020a12050105060f090402100e061c1404080702240f0301051f120b210c09090a0b0105011b020a0303020309040c020724180b0a0e09 68
    0x220f000c2200501400092120101c014105c011404003500803d400d2041a0f100c50395221074a0070550500c2400e20609e900303c1c80446090409040c028005031004d040600081c3c071540443c40c1d251030440c080c94550340c030580b001d004580c550402c0302c100784400c0e94485160341114101400c8034142600c04112520865104480c9828601035400b40b1140032200c2d45040c40a03040070b0500030f4404d1801014205c01401e0201c1e0390356940c180410f201c00100c40d2064224400301010b500810150882079002011000140000750790501c600010321810404105007489040301884461940700401c00001283c82661003050310703100c1c4070700300795140a099030103010044004014001584600d40b1541101c404d840806400d0368950001501e500143d4008c8015903c005424111800c090280501c0b0018600140c021785203050518840a0602e0300049080041c451010206034041d4640c00c0d0419070f14084018920380700c2d5003105281e800003801c81e020071a42e04a0202616128070745034402c0b00705 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 76268994 1250 76267744 76267753
    0x91b090103081e03091e0a02011709031209030304021f2c040f06050f1206041104150e010303121a0918150117070302090106110c0405010b070204150503 67
    0x1d603240c801080d0001580c0c0003000301814101e096040100020b1409160160003801045403001c0b003084020b440110040c00ea5000400348001503030308415103a45195800000f1511551b801c0c00e030724114800d021240b2950815003090021140c0004081d610403442500d410600240019108030314124004541340000d00403294041d0883c2e407951400b501d2110007140f40864000c0b00300040036541d220b4802401e481c1c0d212401c1001c0d01e0401283d07251010255191000803820103400c40c3c403408002d0014200b4080141c1000b040d0301c03980d0103103000038543c0061000c00398840c049000b0315502840300b5000209a1048920741c1c651a104820760b40300f58411040d5500c031058184540407a00410341403050794100c41000d1508014001095212020548402c0644c180808030003542c40817040002594884541400162120a0201d0566100b0704050000306c010744006480e00c0d2700e5600b101d07001070034400002110b00440024091561003120b080c0071211f68891400740000c403920809526600 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 76270244 1250 76268994 76268999
    0x402040909260a0c02030a0b09100b0108130303021608070813060e09060405130501020d020429030606070c0306060f05090a0c0206061002030c0d20010603030e011d100206091b0901 79
    0x2480c13091000c61014099845894940c0c48950800c0b0b811603242d02150800704030140f40361441e101c2c420b4091802d080081e91810905001070360726600445c010249030740003a180300309103080c003003211016501c220020391740c04d800e14068100350403180c0c007145204000f0b400407801500030181c141c0703001400b0709000710380c0e600d80302000060030000d00500c114080c2c010484011880070300080c0401600e8500c09030341d40e840d0240103841204901211041c1d16454886509800c5880007100c1d080a4121105a10794020b800d11604440c2c45500c01800381f41fa00308009800716407190f08804407001140d540c0b0711f030f5640f140414159440d9180074001600603c0010301c913440c0000300303410409040c0c4103c0b03041c554141040b518061207464030750042503900c401c21005542605400429071218802481894a9035601505804903006402d05211003000c250300786102d05d2200e05003007a0001e0000102000404020b5100c8206464500203805201607025607901910306013040c10700d002d01403240c11307031 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 76271494 1250 76270244 76270247
    0x406020601090b0f210109030e0a0e06090403080c0c030409090b01061803021c060213080c0303070c060309031b0605060405150108040b040201030e1606230703030e07050402040909260a 81
    0x310b6154601d001701e40008044114003401d2140716010341c403a03250754040400c5e00b010400ea01155600080034011958104801c544a010a05420a40c1802c15a4a54546941c030803918081c1c0f01c000003e43c4000f00b0001000d88503504000e11403405000c0401140c1d07250728003220190340429141032043c107084e000f00018145a441581390020100d10080b0911096480b0342c00c0c0d90080c1e01c00286118103103402c2c41201003c0c410b0410040c1d0450055190900598030607806070041d2060304c09166481000005041c000c0b03001c18448060313103240804000e194549030008150075503a03d4065854130307000540c070407950a6228121403050f1518180c541e2a0b40d9444022000244100e040644030030031204440010451145d0324112804c0c52101c05041c580b0050441c4a1080100c00c8035001c2c42e04440c01000050481d10f85640524001c95452114074905107000d44d10ba0140d90007d10010b40041d07499001d03803001450030300ca45040f00c0405a00c06074416090070420711004602810803082042a = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 76272744 1250 76271494 76271509
    0xa1e0807020a110a0f170705040b0913030e0603090318241b0d08090f030306090c07020d2015030105010906050706060506191e02190507051002030406020601090b0f 72
    0x10f010041080509a44030340e20001420344582c801d15040c284203400d8190020240008009883c0c240e404000342c0900d4000500140c1c4040c20441d4400f0901d01d003403042c14407038624240c0e91b000c06001190340e820302d000410740c4c0c0e41c8080400c0714080070702c0300c000b9040d1800c0702d0380d550a620700540c11090200150207000c1d9035408070482a241c840b01d150100700440003800b04c5075011940786c0f00c044c0e251074400e0804d030400c40d0f9031900b860160010020000c050b9100c0d001c2c150050ba0000c0c55603120f241030701c00304072001144000030f00000010319024000034540e88007020801d42c00c0c0c40c3ca4070508900c04079000540028010360340800e010110500c8094401c034007800d1140e0040c00013244080d0303660003040301684078007059020014090f10040480d500044c003401e131580005400700040180110081d1200c0c80e000c2040020034006c00c248040c0b000811400c000b505c03005080152181140c0d401a40c0d940c468070410f0051b02039a00002031100d83c52003203855021002e070411005070302040811209 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 76273994 1250 76272744 76272773
    0x906010b04061d031507080a0203010f090e030c1b1309050312190908030a0506060a0e09060a0305060c0304052a04110408010216021509030a0206070204110a1e0807020a 74
    0x2040040f68521181d41e000c01003844a02440e0021680d2410b00c0c42c07004103982c100420342ca03641c07801000100100d440c0e10501200311800c001c4006004111440c29034110b2043c49036481d4140302e04d160a001342000f448845c02e14a404548a1001d5070980301440151185414042d2054006002c045854054900c480c1d80c048103454100e02c26400080c103000458014080550b6218804400c102124109200304c80e01700404444540c144030603c800101403c00352004a8011360303000e0041106901c0c0d20060f00007540d40031050326418580740280110399001102d0070368441c41a076a403c46150103028402e003820404001c24040c1248410600002e0000d2640b0355105280c108030004040c042840640418807070180c0c0006840c0d060300400c1a104043d120301488003404000b0b41005980015a003060700e6415200591034140c2400010000c0c409000c1d880240d203400030740e100481c1d07444144000e13903281c007110000850300c1d460000c55442d5012554000540c2c0600c40c41e00100c0c0014801541 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 76275244 1250 76273994 76274027
    0x30902010e0d0f050307030e0a0603020c1f1805010e060c190807180603050403031b1205090309060703050a0f020610030201110709060902070302060c07030e121504080a080906010b0406 81
    0x300c45a2680c8003840c1d50310425007078001030196230042d1020300c1c1c000140320080513645425400d12011240c02903c4443e004240d040c0840602945224149242c0245040540032141b051402515050241c00781c0369103c03010a80d4050302d800161484a20001d8481d840511311002c0b5081b540034100392040e403000b810745400d001c11200c604182180414020024121503a40401d49041910b8054251550b9024026412001c00600000a5070003005500c040e5070724200450381d0b490301050300b800e61251028082d000780300040d45005040d00a0014041c40002d6aa208039082b007000b01280ca42c001a41c24a41c49010340300304001642c4228800052070070140c0980e41e42c10754074082502110080d5009122490700400c8440170300d030301032100680c00445484014a400741a5400034218460080306034401c106183c5607009649041110f00304c0d105a03070740ca8030342d241800d040c0014290881e4441308e00184451000a951442c0859198103d07200d04071214246800c04005546940d0020b20000 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 76276494 1250 76275244 76275263
    0xa0c02030d0f1206081c0309050303070503100909080f0a030b0d0309150206011401110a120504140d02010f03051f030803072c041a041d070501030902010e0d 69
    0x50140ea0240030708401c10036142c5440502c0c4501c5079014000c1000306030703c485503e01d803803002c00c0548000718405519101528007080e1104002c04160700402e0320110181140c84080304100d11550032500071801121100f0800d000c1d82d568400e100144c03908080000c10340c540900080610142000c003412020407982004166a10000042400251907a005600080c51356108000c40c01c1a2148140307181d000b8030280c0003560414480c5082c69014861507410040c40d90b84696104109201c880807041d88904021300039110b40350010642d4000d402a4041e402a9000c40c060600d00104410390095040e1207041c00c101466105600034080200780a03998280041c546614545c90485a400341d80300b607440c80d4480c140901c5c001c0c10186010840c44084484400078202c0c0341c030031440080c0c5100b00f21808034240c251400301d4416006003889040d0014248066600d4144684510703002083c00c00301260009aa183c0045007650395841020707002c90300d07556090700c85007409840010018056136018 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 76277744 1250 76276494 76276517
    0x10510080a0b07030f0f0b0132070606030c080304060201061d0417040f030b090d0e010210270f03020105070905130b180708040506060307051e010c050708010902040b09010b030c0a 79
    0x81080d20418800503111647d0b0360b004108542e04442028040c0003890b0f0744162032640380c851503026411a10b1959845200841c1c03070000c10185820041c080d41d4000f683c461060740d0341c0c503110382d01e0300580507803000741d400d000001c2040078180c20402110752480101500c41c0d210b6407200644075461112505010000308404a541079000c02c0800040d88940401000303407174400301e500c0c1000c4000890808103d22103182c01d1040c1c1c0d0010b000c03690f0000c40c0c03000080201c207103012a214050b0440c070a090000e141c440201c01d020f01e00d01e500203500d00a030000d01071556080700031108400a8000c1036407245c80c0103143e4525902130350101200040240c07079410008140d05d03854a00e840c00b120990001000c800400003000000e200450f0401c0081e80100b400b1401d020001c1e96190358619907d8200706d50f07880c41c0801d070303129460765010f003500700303058498850302c0740c0d0240d0190000000903030140d0708001d51104039080c82d41c4114101e589a03800d4034151340b81c021130081243d10a040c4a0100700120302030 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 76278994 1250 76277744 76277771
    0x501030222080304030c050604030503030105010f0c0b0403051209060f070f03200424080f091c020d0207080a050a02040e100f060614090a0302210601080609010510080a0b0703 77
    0x203074080c0c01c1d1100210340b0f40f491450440c01407021900410700640050208000080000050301e064aa003405c0500e08440c00300c3c021680260804000307400d0641882c240000d064000c00140041c41013010b0341c51455854000c1b49030b0718402074503810341007100040000c1c039444c03040e840300d0a441d540d864041950118038941c46100e000c2035130300c0003000f90002001c00548020b501e103c4010303000811303186410346c440d040213081500000e0a00207420f48140c00111092801c0c03104194042c05441c032640030b034100e400e009640b0124407040ba8054881d0f91800f1803100000103040c01d4041c0e001d40240360000c05507007804080c02c0d52803800701c1503201e03058100d001d6030f030385000b0f444000603000c00c002503032450500300910100b00b8440721000b4150801003003150f51a4400c0000940350151032500e058041c03020b2528002c403000c10252403031b0041c2d9001103000e070030101d0402d01841c1d21b0300007031041e40c64040d41e18100c002c40348070f0752640b58000303041000001c00c41c8841c80d91102c481e090000328005c00c0c400 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 76280244 1250 76278994 76279057
    0xa140109091409070f0305150a0204121203150509181207060c02010501090b0904060b0a0b0d06050a0f050102100c02071a030a050a0e0c0105160602040e220b0105010302 74
    0x1074042c1a152000c04002d0101c1e0200042c1c00100600800c0c10b02e9685036448540d100e01d1400d00803116002100000383c8d0000080e0100c0300180410b0320a1035200c049404c026407203401012186001034208001708200c0c540065001040e560024102c802c0c0d51200e041e141070a910001c0b041032240100807510071504030700000f52802d98011130000c101c010000b4002401c4a105070008880c003494545060129164503417044c0c1e109901c40400550072544000241125401c2d0340002c40b01c950004203030b2a041d4003500240102c2d00140c03240b141d916100c54a1000103103141c042d03140107174015813510345050b406410500c0f144030180140c840c8a6110b1032122400e00030705070541241000001800480c4509129032a881032441d0000c00c0410702d480403503902c41c1081c012090401201047d036846c1d0340c80040c1408246070703001000315a115511141c500c01c00f58111030754104c0319211541603c2059120700f83c000e190f50f01840c00d18440c0c3c21b107001500207400c071101c41c01100c14240c20f12911880f0441 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 76281494 1250 76280244 76280261
    0x3070f0806040b0723090102010b09010611010609020702060a1d100809060708040503040b0913050a05010317090906011d040f02090a090608030403061d030f0306011209020a14010909 80
    0x4000e4071980c600360074110b880d10009030804081007502400c0050317400c91903940c41c0c21024081c001a640d284040700403030140011904007036005400c0000024010b42040014199101010081c01240c1ea110120002c80c011554069002003041042207401e9120f1814400309034003049080c403040780d0100200c1c0300b56088030b1140300070452000602407000c008001031030744603165240248440c60940d80b21526400741e882005441c3c03e0103c0c0b200a5540e40501c400c0d80c01060301010011480d000040305c000d00310038030054030140b6941d500ca00030004484115000104042c052007d07686441d80111414260800ca08000c0d1480d06400511650b5a0042c070403200e100c0356016854171054401c2200400c040d600c080303020b5140060811a5140120580d011a078000700d0010344a0b20003182c0340d250ac50800910f41c0d281c000002e501034000d2609024500803607081e0307a4030401051061414088805641e006540841f6448080103084240c80c0050901c60040c50245217103540e82800c10250b42004 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 76282744 1250 76281494 76281509
    0x405070f0311090105040507140a050405121b0604031e0f0206070c03030807020c0d0b0c090a06031a01050c0a0b22050c0f150d090807020901090c0e040c0e0f03070f 72
    0x8000420b080c6000c048141c0506003c5130200f04030b04106001a003001400d451410501c0f5020903203102c01e50242c01958000c1002414641460818801498031842031000307074134594020f9484184142020707000d03030301629804000955118800781c42c00801c03080c1d40f001160541e0b100e601200043c2c03070741c0000d040824401c0c0303072565400341149006805158001e15010440d8410110721400b65100144414160b812454031007068460008400180c45a25800354001030050030015440f0761580c80914004028109640c140c015040119100e220710900d03203e0aa000d04846030104030b0700310704660000602c8801c48400482d140d50004a659481800e032480c2e003002d460544503041084010340000000c491021400c0c8a600b80b090050140914080d4120f035603901c81c00030020488200e8100360340042c0b80c0c024541c0c1da551b40002800c3c1c10451031000070540c000a4090707042c0341c0200b030782102071a01c407803055200e400140304101752002540da500d40b00344000012100302c0c440700c0c2006030802 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 76283994 1250 76282744 76282763
    0x90c121e090303150e1608060d0c0308070b0703050c040e1005040e07050102070801090201021c18030b07020d0f02071a070b1512060106081b1e0316030e060a050405070f03 75
    0x214944d4565000e1242e20014242d40000704001844280031190504d081007810710300c0340ca4840c0c0300442c6c0c0e10081302000514044070100080b041c000350001400559220303c030050490b81c0d61040490948400765100b01000c5c3d4207003c140480c11f0b1a1600c0f9a21819101c00c40c100c495950700040c054803200c6042d020940c100420a026035641401500c0162542d20002c0c00044031310740c0000d41e2a02010b1803143c81201401f4005c0143c0d10a540e000e0032401454520b415191300c9080c198031003001950340002512550207400d0342203005004950f000d414030340161508a183c40380d210039210340c805a0f0070100c1010420380380000e01910350240120720307074107003926000c5000e0107224012001da5052241030b80710750300400025500c024502d43c40b040c84041c607800940e60002090b103501503140c54404562645209100704d8a41c940a18403c9030707012410344902030405016002ca40c0e6a00e42911a40c22040000303035020000d4004d690010b00c075104550040ea990155440c60001c10b41048842464 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 76285244 1250 76283994 76284011
    0x3030b090c27060702060903030d020c0c040e0d020d080604020c0f01020c0106050d11061806070311070f06050f0304020102071a03061503070e0409081605070f090c121e090303 77
    0x5940e102d0540c00c0e070181e1001c00d4014611400580640a44c443c02441000005111802500c09000341d4428010001c4190346508125010035200c20b0f00819542c012458422040c100c2c0c240003a02e400e00c1002074026015079007480c001100c3c0c0100c000d04090700180c080140d0031480b00e00700040390f402c40d405000140c844815281207400c3d00d01d5540518454030100e00c0d0080030481d1805a220300b0715003221a5551503401e1980410040c652241d51a8000b10108040c0c1c181134110101c2000401060b0644038982d440755201e00d154401c80c098180050020300508560001c07500040d1b80050050044400d40b69650802c040810b6007070030900000380d408003d22645050076008030028200171034005040d45855080285200e0398010a5441249c41da0444414804000c041741c42e00060455900c050345c80c1c5042040d41d0300010700c210700c110f00c454540060101014407550750608659079600b440303103a0700040c4030b024140503640c4000303141c00000400d40390031081c4134002c0754a21a403000702c0e100780c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 76286494 1250 76285244 76285267
    0x3030801080c030102040317090a210c081f09110405010b0a1b0f0b13080c0a03020606030f070611010e0303070309141c030f020412030e0a06020a080306010c03030b090c 74
    0x2461080507010345e0040c4800d10026000440703800c0303200305030000a900d07030320482d0002d11011240d41c0088a201140c00340d8504080d100b505465500e0302500401003590b81e00c100080d941c069503044105850364104007004681190340010511502803060001030040b0100090103c1d5801c0e17000f441001c0f4001905203419400c080a4330346444120310025040d1800d8503680044580c4940060030300312454000703a24102540134061301c081e0040c802d5070320b4200c3d94181542e030326180c0c081680175100c1c04000880c58540091642d54400c41c00340503002c0e1a00c0c04030180c40c0400d00d4401e12080355292034510350403035001c0000e58840d143d03a50b40441e07009078900384080003440842003401c1903009185815024500786800032400300061034002030607080f411003c4001e0140d504201800700e0383c503507420281075001d6460010a00c0480d00018503035552036003039035030f14208000184000010b10001d404d640c0510050f06036240a0300f0007082841c2e001001404141d411614000c000034042282e04609 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 76287744 1250 76286494 76286503
    0xa1208010e0711030f0a1e0302031005042c0f0105040b04020f0904050d0f030b040504151803020c060d09020d12020d0207050105030a0b0402122a0a0f12060f0303080108 74
    0x101281440040f05120aa54688034440da941c90140e0090008003154000d128603044c12038458004003074044410002c400a000c0c2d4416501a48a41401c041c0842e403442d06124680300000e1801d402200409481d4804054502d00749828621b409600091900c2a80a0146512542c0f141a5288003480c1034410089042c0c0c01c511060b004074030100400001940014060b52a45220b062a16101032800c504401409401190f10f401501f03103001d01c4100a01c1c0301801c80c044200c074105000d940100d1000c0c00240e01100070160040c0d000104c0c601c010f080541c001c207a0600700213404200c0004540210340d01401c2c0c10303011100011341c0c501e4295066818008030b83d42107120300c060105640f400c00024418080900441d1085a0351500ca070303e030b651140d0494983c048542c01540301c514195000c0c5050060001420101d4045405201810f0121000b1180300881c5038503190700308054017404543c07100081402c0d4040e43e55036280490311510032880d60b401107100e50744a0104d0341c107006000f03080 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 76288994 1250 76287744 76287751
    0x10e0612090d111902060c0102040315050601050a050403080d0216032f07061241010f060e04110c0307060b10090b03040c120303020904050907050a170a1208010e 71
    0x10407aa4507a82208100049602e04000054611100707000c2c1e818000200b20380708107c0740c1e82e200d41c0b00140000401c4141501007000e080e9000302004250303a0340b0019200c52003201d05400c00103100300414030004512038054441e40e0394100700142840b8003a080802c0180403004c00750b010038404503241c145581c40061b40c00441101c007002c210b40c46255144256920858060402482501340080300b00001c2c2c0d6000b2076092030f038402c4000700e945180070042c0050344100130194805090000c41281d00d018084490f040b2160444030703a1046250100c11a42c5102c0258090f42c0940c80b5171002d404c0c1039540b0090811600c030754024569418061501300115050f409543d400b600c200c8204220f155082190709080350118420349a070b079556840c0840d84602150050410700106940c1172042c141e05502a2040880544c1e080286444003003003690340d01c0c058411903034000f513110006c3c0070300c45014668400030340946003100c0b0140099a9144486800700e08040000303002c010040100c0a05003400b540c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 76290244 1250 76288994 76288997
    0x609120905090a0903050c0105040b010329070c08090d0804060e0f060a03091a07090303110f0a11060f030a0516050c0a020f010905031603060e0304080318010e0612090d 74
    0x9240e10701404900300c1c02c001440907608682d00d00880c000d0501620880b1001d8038a4002040607240030301e0504081d44080c0003d99240c3c203040000461000c0a04004001210300540021503565031441210403031866001190010720600c0001039640340c94ad000b40d4120320501d03016840c1c03400c0007001815118406d800c184a031905c19944500d80d1240b6044a6111230f117132034045000c0205003071141c149084010401d4080b4448010440c046074407131013020982c1d11a54450100442e04944c140d5030310603001d03401c281500010034040008a81142e0007408100140c942d40c14032070301c80120790343c0303400441d03021320300c036440d0410071450b0303011500d90740c210500368240b041c18051201031643d070310603101c4402801044d0002400c401ca078000c1512400400c00203088400401c9400480660000d0500c41110140d0425100010808006c4160b90030b540040740118184544107070a4900120380d02c7d84641407140d86181c104181d1100c070001d00612a001c45020304034101040c0039440c10014109800 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 76291494 1250 76290244 76290257
    0x30609011409031206130b10030c020c041a01120f020c03041d011d0406060302040501080a0c0603060b0a05071407081f020306010813020a08030c0f1204050607150e0109060912 77
    0x130401c0c10000071041d0454019245200c1920580d48480024032524900c2c60348075503100d005a131182d1340f42e084040c1c614040e5003501c07040a680c000b4003050700e089000e02d503001403481d04505607651003240d050340c40010210012a801c50300c0041c40c41280d00014110b40c81d500b001a09001403c08610340c0494180c1c8541100c910350f00d03002c01e40f040606d8001c60b0064491000b40401e0a0041540000002e5600180b0800c41542e4031100e8590741e0500b0502110003400c00800000d100340a4400c8004441c0c0c6000400e1508641c40800c5585500c0204200c4255010300c400408c80380c0702308800406410a100180300480c51054030001800c6100644482d4500402c10480c03140d0f0700c000000c4d0810ba0401c00780c1e06900003440081c41040882d0004601880040303840f40d4043d800280a00c0203042681c00d40b203c074080c2403409403582c41640200c3d900180200480d000140c0810f40490102501e0a000035116803034085107401d44801c000280c403059203461240c0c1c03c1c40111459208282c1c100e05080303 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 76292744 1250 76291494 76291507
    0xc0916020708160e090a0203060f07170c09010302130812030103051006080a061e05040305090a120b0c090114070b010614030402130203150a03140705010203030705071b0503060901140903 82
    0x70a43c3c1c6000d0045642c50000340010842219082000c50400c0c2c1e07000302581c8640c0b6050f2480600c000007100d10300001031800f090880c0940105131801e008021619011b407a00e1b21640054010b0343c084904070320a4800480d00141401d0306200e00b14940c0010000d407956540b441c186985440500f041da10710041c1360401c2040088400100042c02a52204001c640003440d0280c040c4802d44000c800c02c3c2442c1464100010154030100920901604540310910705440f60b503c2070016880c020000c000d102d4100100380d00c0e004050151044803414904040c41c0700707280c46400b800313401c0000c046442201c41d000511070390342c00c80309407469101c1805e0b001d03045140035000a00c151413201c210a051320b0b40000441c4070450725500782c8081060140102103410354070b2034590b250007412000450107001d1850042083d41c40401100d00510103581c81c0c03800d129444d1101e6000e819006c254414146a108000900792818000d00340b01c1ca04000001034070001100500446a500034841152500200240d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 76293994 1250 76292744 76292773
    0x301140f0c0c06160309051009030f020c0a09020d0207050f0c01200a060c02010b0627060406090b0901030207020907081e010602030d0b0607051608010b0409080306040902030c0916020708 82
    0x2203e44c049101d480300070650707000c03081c20b4004281c3c0304405040e50048400c1010601255040603464038482d40c0c80203481080b40004a0325031484500b580c3d0301c1142030000b003061030364580260050000e2000010715003c03443c1d65980c5484444d15040e4040d4001428106140d0b80080c03c4808803400e00080d01032a14001c108103845034903c3c600203200d95920141c030070f201da01c05d6004110b403c0010341010b60f034030a0300c0c44034650a200c0015072022030302031013071060007410503c0541e0111119030316020b00a03400e045c11b284154111000301410180c4c288043d8015a45100c0040d004103d1070711102c1d194140798841540c2180b2031101e6a007502200401040020b030b0000440d140d0307002407480040c0c0011841d00080551091a0028000d88100094171204011180e035000c11244410001c00007030204000340b009a958601003d072000000313100054a609080e001110301c41d10090584000327800c0c503c00075200150680340201103c6a110150042c180c04101c00409400b00d14018400085074100 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 76295244 1250 76293994 76294003
    0x3050f0403050d18061508060a111b15100302120705060a03020c070806040b070807020601050a09020903011e0501080d0e0d03030b0a0f03050c13021201140d020301140f0c0c 76
    0x1c01e03101c41966940503902402540800e541c4060b4020000d0041501b2500340b001056228000c0c50614028000891f2801c3e50510450004120365007c1c1d41c1015841f010300400039078040c0000c0807900818140d0404072000341d2100d440342406c0060700d802e40e4118018060401c66048105116607c80f4205002c2d590790b08007600d00c11032507032070007507580c1c1c10b41300c190741c1004056841001d4520400041c0010440001103640c81000c0c2545c884800c1d40d2055030490350303100207214442e000428540240100d84d21a001404a0b0070003500114600c0c41f0030641e031700b841e00c2c0c1002a0422030364540052140701010300110045080c035107001216030003440000b4036504651403004043c15590801901c40b5152181e102c030092500e003030381b0001d1070365904101d07448000f0200d1046c40b88103040c0c840369a00c6030f50700c2030724400546100e80c240700380e00300800e10443e40301c91403520b039000280151420051341c0c24042c00300d0b4410803040f03003451410085400a500d55002c2c080b5005030000f8001c0303001c3c0200008 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 76296494 1250 76295244 76295257
    0x512070e13050109080a0216120b0a020f031626010510021c111207051c0e0409030507110a080616170a0509070f06051803010204120b0703050f040305 66
    0x800106194540c048000030300d00041e60010155401c10b91075006018440300942480b052071b8090750700040780381d000131000900a01880000d08810808000442d088070f055950080651030018503201d000e06140c2c2d01038204071519501c00e484662045a0142d004500f11104400c2c1c07901d000704404140e29000d2694014012a4014800d1814140155100b00a90041149842000c213240c41100c000140600000e2a08110500c03805440a4400d0a044101c1c0c4503243c002014202400d006400113000b01c0c00040410100010071424100d503640d2440380042c001e00c281c64041d0b88d80c0c80752800c000700c1081c02c01607610840c0b00180c1002425404102954800e400c0040042131070b15081b0f00741c41c0ca07440c1d0301d00e41924a03400020419152010750002c1d010b040d041003103616143e40c0d6001d4120030219800380000281d810f015000e00701a0f100e10300740014200a001606050303e4130030240b03050350b540c0010380d80e4000140500030159058407130150040380c071080c015002d1400d91006891b510400 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 76297744 1250 76296494 76296509
    0x2d010803041404060306051e0112031403100b0309010c020c0301060308040b16060603150e011b140705010e0c1906020303011206090605090102030915160e060705030310060306051207 80
    0x9405400c5541c3d01d51140000c3d60b4051002c2010307080c4200740d00e610304c0d0524014003c0c200c1840000c039804000c40c912060301030f81595500d1401341c000c2454001d682004d4a45821005000c60201c1da0441e100040d44c03240a61100014042500060091400c450784000502a9142c810f0a201144507802201c0903035a40030b10040c1d1758041041880d80601600c40e0140040d86000b00120801c003113520804184030400030305000410a900040e400c0b505182c8200c866141940c214140250040302c0344010130001d4000e0340e00300045070b1955800e460400c040341c42181c01500c400c0300c42c0e103400b2003600f18040c1901c1000c40c9542c2000d2000c0d50328801030150302d818036040c443c4102000081e41141c0b031a10b500581c00d01a60a020768498041d42085c0c81e64080d5000b00c4042c25a6642500141c0d032150184440032580700007111400e4424008001c00c003504040200200400303e0720800007540034045018082c0301c0145000350040884410790046445203001480714480d00d00001a00400d80d14030 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 76298994 1250 76297744 76297769
    0xe071803080f07030908030c0a032615060903060906180316080f0405060c010501210803010308031e04050a050d0305010e06121905031804050403080406020304060605092d01080304 79
    0x100c1c1000d0364179003c664000c81907480009000c0c152000c0100c1d0b180d941c0d41c40780d00d0b44003001060300c4044620441082d4111003c0b060500002e40e108007015814540d9000948890700e010071110201b8186441140e111055500002c280b159004c4111485030003600100d001e982050025038501d2600080c960703000d429003901280700d0108281c0c4d40c2c100c030010400105429034550030069058040c0c07000348506000400428103000040d030011000060341a8401413140c5181e0940ea1480c5903504040c20040c5051851400c0d4135903803218030b000b00d015a0203031005040030b801a00d00180341c1421030400c0f40401d401c0000401881100940058100e10100c1340d0012500e071400045150031019003440c031034645507507012814800040020090040d141d088001030100c40d400b80b005035601035400400103803140c5c0001e40071800d240d015540181c401c42c40460308983d00c0000582012050350101660303c60146550035400701202c85806e000a404500c0c500380d03242c40b60b180d0700e03801940309802081c0007 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 76300244 1250 76298994 76299007
    0xd03080a0509011407020604060507020102091804083a0c0807030b0f030610090506030a03140708040801020714101b0e1302030a020a170402030a060b040e06010e071803080f 76
    0xc0c00c4d005100c0d208840428070b0360a16002c20001d40c0d60f0001d480a88400c0e1400002c6030000d4410300031a240660b0280c20403c0c030302d0480c08000b003100c000800a6039800320038000304001104a101d800441020500c2c010704284904110010102ea541500e5a8151810303079650901038101564a502a0340760070001034451041010481c0c075030680c5003a44d0301d40207a0080141d03669240c413100081d00c0008108200350380c0d0769410b01d603441d201c45e100540400c0002c008100709021040041c0005c52160004508040c3d540c503010303007681c00441c4225850131001403040d0000004201000c000d07241c1210910070a00901c3c181c0c11301b040d8100001381003145400d0f69001c0c40d166050310003c10907408600f15644c3c2380110174240203421480a00340054011520318842c0e1385c0c0041514041c3d80c00074040c007010b911990b01d01c4000d10481c46e000b50440c1e00c1e945140d034901c00502c4024000c00403254809103502d801c000042041c00b07042c2071021089505841400412070340b8040e182c0d807410700510903a4415 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 76301494 1250 76300244 76300261
    0x703050d090b010801060602060f0408031f03080d0f05060a0504020a0c050703050109170a020303070c14030a080103060b0d03140304030203090d050703030906030501080a030e1f050403110d03080a05 87
    0x820081026451810101c1000801840c0c600d042c0c100c4034440d000300002e503200c440407600d8840a8555814041c0401d000c10042402c0100541e008a0840c0c8450301d210044800008120840d510694040c0004114480885e40d6030042e41c20714982d042d401c105910f801c0c0c0014007042480d010340c500503640880c1841100c0c4c002c0b13101800140d003010884260a94919016000e081400c0c03080b51030b41c2c080750042d0000400b10040c1e600281503074000e1030440d0f84141040303072501c500603800d40350005a080056100300060000741a110380316503410300301e503055051070f00c240d8100d02c1c13000d8044d080300084a00800d6118090210418807041566501c3d00e43d402d0491850046d0590541c0c440d00003200c060400074006600c00850348240c070380008036941c9900c2130301160ba0901c6141099085148220b0000e8170030030152584240062800003001980448803085e03d82a08074000820b10000e0140305004542c0101400d09204450342d504908060b80e00526210000d031032103007104e86990218010f02c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 76302744 1250 76301494 76301497
    0xd03110d06030b15040b10030b01020a150b030f030c0c190302030106081e19150f06060c02011b080702090901020c032a01050f06130b030105010602030c240a02070305 73
    0x2210800c003070000549a0074a400803030010707501102c2c080c8140c0c40b85442400c16000710184050000c0155268030084c03242580541140350f5018114001d1540c0c0300001442a0058400300800c4840000d07481c03201c005241c6414822103640c2c1a0340d2060120701e600c0400060740c06030300801035500d064880c0c491401e5130004002500002c1d499401d08d440401c1450002070b030f00084451940c621010a542031440d00c0d01c0b41c075004400705104800303c0000000c150814858140890301a03800207040c0f00301803400f0100c0f0100d40210002400d03400202c070642da0f0000c88120410a02801d4400240d8a5954140d05200300c48000380150203820000709811020f5055076008244202620744d40e400d03403101d50729001d202d170500d0340d2100600e4041d015105014407655110715449802900070341c4514041207000711240b0701c4108401e40380c000402c002e407028001c0500814603500255260000003010341d00384842c1e08a1814108030700c01d501d400da43c40c0101e08a41100140034010780c4c070324031400c007200d0a = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 76303994 1250 76302744 76302757
    0x80a0c15090f181509051b03090c040b0d0f030315051f0804021302040609030c090b090403050903011d0a140613200907080f01060e03100c03060e01030503041a0405030d0311 76
    0xb41513080001d0b602a280c0086214020030309070300d0300344e6450002c882c1d886d01043d1550001c50b4071203010440345007010b610070a20198020700c2066003d04c140d4400c01c1c0484a42800c800181d15100183d0405d011000607101800c42124015101d0a1144844034130710005081c2104008001e808a42075495107002d59108110815041d5580c1c0e0701c032100541801c0c6240320490f14110300400000b0b25240d42c0c864000c4a48006114000d0b94460307032011101d5400064041c2d40c10756a50703902080d2b00303091801004041503014043c10484c0401c1c14611000e202c0300d0ba1f0a0030f940c0010b003c1214248813508040303500b59002100134400084a240e859400d800342810980060b00041400030b20307034001990500c906c0c203600180d545a0b88903041141d41d4103040d22099050b40c00207804541421140c1c0295469440d985000030321180c1d14811240c0150003070b0700589d229003000038180300368002012401401003071724080038a041d10b400c0102c0e84c0c030080e80c491070080503503c03042540f0419581e0100c958 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 76305244 1250 76303994 76304021
    0x319050903030304030504261c03110c071d0f010e09070902030106051b03180409080702151306090b19090503010e07080c100c02060c0304080a0c15090f18 68
    0xf141d28080c540941940d10500510b51802200c00200c40300403070200425181c41e11a03400341c200c90a200c42c000d404820909550010300da1900d0140200c4002c0801801c000300362000103010310751807da459030940d504195085082c0782042c0c01c00000010b80d0b20018115022080050303415034038450030134105449a00035001c018000000024005e030b011018044041098000008030303c2c8034a40c0c1e944c1c1c0d1158049040c4003200f600e081d0b0740c070713881c0a41c81014218000d010301c6203000d140b9400603544040b0a80003441140c000b048070000c001c0b144003010041c00c098100403181c41d0a110444115004103050900746031072402d50740c03500f9442071413050004d0002a00038402c52002607040e644806c22401611180c1c891407128160600d841d056014030b43c00c2d03e03111640000303455002d0060690040070a102e80d44801c010000d480d03907040107050503d9004440d40e41c84941440050110360342100c1080741001803600c1c1c140002c82e00b0322200c00c1100c000c0d00056003040300c901d01c4980906140c0341c0069 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 76306494 1250 76305244 76305247
    0xc07030308060108061e0d020f15130e070801090b041506020c1002011506030e03120c0714060405060c030a09080c1c110d05030604061e0e07030e031905090303 70
    0x204041e04408481c1c0a0407090720f4001c0244c0c1c4040130321110300b15003105c0402d0102400403144d142c0c10884100c2421600191000304101c11460118481d8075521500307200042c00020302180c0b407214038170f64034090a4003030a500d0884c244154000c0c6141018090224030359640c1200b1130441d9125409000000014107844541d0341e99102c3c041e4560190604142c014900b4980030b040280c818414690301280c808031800b02e15040000441c010008640d40405610080021000030800102000c0c03040c00d03a4010650749114924010b018a03140300001c0300a40d00505c00e120001d0302c007190041d881003132201c56175100d80e208140380f4050400b42401501101c40099510146003000c10b00c2e0454562280c1d19944a660f8403000304d5540351078030810080741e0040c0c02c410105034440c100954208000410110f465621807407904c40f04218008119030b010f1088404118078a0381d0b000040d030000803070808010106030035043c0c0361a481001d2501d040d0241c00325039049200d00603015034040c000054203ea = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 76307744 1250 76306494 76306499
    0x504051806040b01050909040f020111071502010b040204030f030c05030f0f03060301180203120703120e010f0c02060105060403170c0312010602060c070c060807350f010308040e0c0c07 81
    0x310035010064865a00450030141c4500440d40900219052084040c101c01c0b010b54842d01c9469070168403c408034100300b64840f4100140104201c2580509400c0204680a150710080a0b003103490300d101d00c90045005010400100350340e4034081e0b800c00c3d0541003543d41040c041c0703041c0341113100d0706040f1440c034400807900308440d4400402861040500750003c000c41003e0020a1051071102d440c003d50640c003068198420b500e1803030241c00302901c41e00f03090000107440c1c980b0b501170769483c00744004140e54404414141540a00403410070b05d0701800034010550400340415198852400080d00c80301180c490350440300755040c1110a1185c44c00d00340c03030721642d9240300d0701c1d5003200a10550005104190108081a20345c40032a03151680c070945d840b120070b14205040d03541840c02000e5109000c500d80c4032030529130114448404600c190031441a807400400080700d441003010b8003010140c00810014000101d0744000c44080c0c03440b041083d00380d66030310366001c0304034031602e40510414021007800 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 76308994 1250 76307744 76307779
    0x9050105091e06010e0c0a0201020c0105010303120c08010e070e0307050603070305010f0801060806060f0418060c0f03050402030703020609060403060608030306040e060405060121020315150607030806040c050405 93
    0x20082c0c440341c0c004006010650700e81c0c41d999502003e01a0802c0c803608180811614111640144801c180c10b000150404004c0c0c05602c4c2100c03801d91003500881d52100352000340c040c1d035104011070710541d41000034042d41804514807a0010060505040c0844003020082c10b42d020801c4000402009000c00c0d80d91510030742c0100035207030a1044c03501408a4810108440300180a84400d540c1c1d4507000740300c903507102070410100d8a060035910380c0260391100d8207140b0188026200b950140149808212600c042c0c0004102c3c1c0d07003004d0100101032815083c400143d9010402d2002c680c3c044543e940c540f0164000a480340c8107c0e03200030f007041d2400030006540303a4080007641c802c000840e03007003142c10500b202c225145c00702250b00904607045507005100c02c920180156080a50a00048051000790381c0030a02d0802c5080c10076583e40740320820041e1400c264402000c19803029600941092019a0040d10441c4081c4c03202c2d100e0303a00c4100d040070392403040042e6002003c0041640082c0440481d0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 76310244 1250 76308994 76309003
    0x3090708120a030b030a081204060e0d0314011e0b070611041202092419080d08090f0a030206040b2203030e0606010503010807030b04050a0c24030614040c030905010509 74
    0x502c040030a04042220390700d0b00c0c0101d07640c14150b800004036841e02d468085c112214010003001151450303170322044110606020042c44ac10b20a494500240c0f122146d90136070701340b1405922030714805c0010848030407081d8101e582102114641d003011600d48002c6d05d89400503101071501d0645003003011400040700c1d00741c84246003100340291041059601c1e8410f00e45c1c03203200c060f07500f401500c0c5900b00c646050700308116891301240303400b0341091780f05444104107424407417105036150005020318280803841400380000d0190024000040c02004950780c1c2c0a501c60900500c003800d1200e40303c000440322408440000f0351449035504c0c1a20034081c0c0c2c40c000d0000c0800c492011554483e001c0054040d50041c8120390584d482d410082c0119840c42d510b0708400c0000500c100d80901a200c0400000b90300e241d0070b8000b5045808070609000b02d070044000504000642e030408040c1003041c104480a01c0c0216802c04041c280c42c003060302c61040405030090140b4140091047d0319200412100b00000304 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 76311494 1250 76310244 76310257
    0xd050c070314030a0809070e04080d0b030102030c0d0b04050f13030c05060705030a1404020a050f030c06030a020702030607050711040b300706090510200303010e0711010905060c0309070812 83
    0x486910172516210303601a40c41d81d2501501c403200f00140c01003004115040080c006448092201203440310003070001c2400d90704190350344040b656012840032a6124140a401c003010030590f03040120b071824480d50701c4442c101520b4000c1c0e00ca0460804c1d070606108003c1c070003406070801c0494200382840c450040c100d41c003c0b20140c8189141150421882808003401402540c00402000c0c0c085c0c10541045400e180c80ca04981c0d051158100821061300d81c80055441500d0054006883d4042c074010b05040c03643c0185030104002c810800c000000e4640000000040c5081c0c03400a2900e00b03000224600760400142d0024a00002540c403000315203450341c0009505510041e40c401c81e58515080c7d030b40740164050140d008814808048880f403040240400d00910307400c00618180c10b40d1242c1d421075000b81c00031b01c88200780104010003540c000403004444003d14008003c010701a03140c4e00c1d203445024100c0c211801001010a0305514104500d2002d000c1c0c1005440c412014001400d04d01e41c041c4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 76312744 1250 76311494 76311497
    0x3061107061b0804060c0504120804031415240d050c0f010e090c03090115030804090c0813020f190e06030601050a08060f0c040e011e0b0406020d050c070314030a 71
    0x850400908541400002007006040c3c54520044e12a9a6000c0c0601070300c2114500b0458184030006100c1c1c0150003580000e4042d030700c1141c3e6076007113040410201d05c0c403000800c2c0903400640c1021294201a0b08103074840c07900d0100c501901d8050480c011134420b4560f840d90301c804030400c40000c2c8840802c1100700c0c0407044031640c00010700e28006441001d0200045a031010f0044002002e00418100455010140c0d800000354510b1220300c502e0000e6458000b603842c1040444c0911115400d0310a1003560704440c185a840c520700011051030b4003407034190080c0941d0041c0450340c11901d8035020466481c0d8a1110107010644440d001c005510080f241d4038800d11500c000040c160600350a08820740f214071010341441c1c0d8841c00b0900109902400c00c03d030700300301040005084a40401c10710701030803c140748101d08048002504074180b2068101c021182e404000820403107400140c6200d070703642142840c5849224040303d913030a15030941d1000d4292680300e0301c1262582000700003009080c955 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 76313994 1250 76312744 76312751
    0x30308060a14031504060908040b0304031d1f0e1f08150f010c0503070204060f050f03070e0112030c0f08070b180703170705010c02010b150306060a08100306110706 72
    0x122000c9030801e042d610704a540640040c49060785850440000940c805d002c1c0350045001d4040782c0d181d0510f540f03d680f015500350700100c00c0c00304256103d61100750f240015002c0410340039180c800100b07030f2086081055821040d2048074404c03103020b0100024840d0008004244001303444405a2007240c0b00000703680010080c50000700410040f009800a00e54042c05144040c0f0b074001c015110040544001d64042c40f05102500040e50340e8001c2a0140010600c0c00814034900002d100c00340b4100c18441344283c01c503880134003082d0342010f03001c0d0440d0100c021b03102c4c03080903605081d54080100c540150001d4080e02c20300c020b1200040062a160380306085207400c5545055060329512070805c10818282c00030035040001c100d1350f8008036104004c1c0762103d0b180030b000d550b900b82141e07070302110480980d444810120311072400c01d00b1440d003101c2500750b180c86c6280c100f0019040d032103002d066805001514010035100c100364007010010390b5200d02c00300700521210315842c40c075400100089078038508 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 76315244 1250 76313994 76313999
    0x1401030606020604080d0c05040801050405071d04031710180219140301050d02060c010c110f0d0519030603020d052503110f240d0e01020903070312020313030308060a 73
    0xc0090f00e644983d030082e51060034000900075090240c201034010400b00712080c0004510f0078801e11803603000740d100d840104002d525100042c4103440c0c0403e5041c4601d45c04d841048046034000045107003900d02108a652035645451412040d00a00d40020502c1025480d03045200d1190382d0041440740581c41840000740e58250040f82c030351360702035924608440c00380010031003410000c0305c804d1100d02c000e020600b080800c004442c01c4660030b0389a0030002d40740010826086100b44401c40b41c12064001804e1149407c44002e40b0501c521501880444c850400040d481440703544040702450f0300822110a80c600c0d400c1c980e560314468401005030300342850304988144068038091040781c1c0d0000b0341c6a0103036216810010000596503071641c001403050a95a03450960000c900d0509040c014680d44800e682310340c0c6822039501d000d199603242c3c410080340889640001c0c80d06c0440e980803030122070907104403108a0641c0100c81c52004030f0b041c0d01c84007004050b00010030601c02c0e103040e104403000b0340c3e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 76316494 1250 76315244 76315247
    0x1e070804210507060e03040602030a0809010908070602030a1a06070209130804060f08090c0d020f01030e010606120f0e07330306081006030803010605090f0a0303030209030601120c05100e03071401030606 89
    0x8030768423410015a004018110072a401103034000e038041d0401c0000540d4031540d844841269000070001c40320150b00100704170309154281b041d508100c440c407880804404102d1b01003003080c840d0318130285c440c0c0c2c0443c00044802004070102c40c00b0590141c07111391102c0c0e8a0b00094503049182c22007401103101d107070012340c0c40c80c4001507104941900509a4000120313a03028800c000303200480c52410107481e2010003800030300c01d000703a02c010419a030321030042ca0003c450307084c129904511109030140c140706000c24510310014040e41541c900320491481410385040030014568114584a18448442d50b8490002c0c1c144d4000c20840740c41e03000760707200c8140180d0800e040f02c0c0305000c010923440d0244010b000092080b8084c2c402030070003400c0840300000c1800000c502400303035441240040d40004d0000201e003000d2044900500c00c10661921190700f83ea180048090b20740500d40c001d50800301802c40c103500c2040f0b85039a108000c0c0c10f40b02c6440d20b4052003c41550440425400b084c144031001520301e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 76317744 1250 76316494 76316497
    0x7080403020940240f0b0906060a0210060311010e0301020c0d08060301230114060307021f0912020601060810050105030105060703050f0d0f051e070804210507060e03 73
    0x55810014400c088285aa80f0200c2040260142510600050742c048001109504440052110601c40701200751180012006a070100400c0c442d03100d081083c0d04259407260b640490304004115400e98031251186e40803850310800d944070b50303031440c00d2807800420300a10510803c112082a40c40010100c500b4040c1801c2c0d104010340740d641c0790301588101c00b0003841070f8a148c1e00640c0040c008103904801903070103e5044107000000000e03501690040201e080d02d180b241e142c1d62001c1c2c0c0c030241546080741d17003c6c0d203c40500c1c0312480c0c0c600409030300c0301e078200c41ca81c0f000c52080c2d48545018502e06a076180250b5800c4240180004208070b2000b2440caa800c200d102c0c81100c0e0145c2d1480d296a0030402444540d80105000714107001c2c0078822080c4081c20320000e400d920040e6030000502500341d217000e00a54001801650364045c1403101e00c00d1090608104581c001c6d02030a084909072a2071400050103501ca05400741403a02d000100440e05a0090040c40418002d01302400a048140c85aa40782e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 76318994 1250 76317744 76317781
    0x24060f0d12031803050904091103070b0405100c05071e030f0302060403030b0609100507050a0b0f040c140907030e0703150c020601090e06070c061107080405010f17010b0c0703020303070804030209 86
    0x3141c5e062084460500d0150040a401ca2041c0800d8414040b0390b0003084c87d2546075081702159041c003040902880c2002034410400202e00e00e00707400500c1664980c5900c803ca80e02540c03802861100724030102100084440f0015584800140343c00380090400a48810003503604400083c1030896040c0b080c5410801c5d958100305c000c0030905d1810a000c1c2c10385107a44040740845030f03405411041c4001ca000000600c5c030030011200d80d4a50340c603181c07030f02100d02582c540025a110403401c07200328454440110055000c0080d040c00134651718100c1d03101d464220300e40d000a05403410480c2c920300c0c40e41c180d004180004a15022602c469884c0c0c00304405842d044079030350300d043e4003900010f101240309000d41441c070380c09528001040c806242a00c601c0783d000190640e0341c0b403000901007000d947e009001200d89119440c140044184042e17086c1281203040c0308144942c9001b09403010745500a0140c0e000555004044075654480c500e800ca40580207488180d100f805140d0000e010b448030105030108 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 76320244 1250 76318994 76318997
    0x3020108070c0c15110f0d02060a02030f0105060304150606030b1c1a070c1a0105100219060e031615060b03040807020409062c060924060f0d12031803 66
    0x3c415041050080500d905810710b4400c00910768800c3c1d80903003050207209440c4844801901250509880192800001a02003903c0758070400c200428588007900d5141591402c071400c56880d115070030420301c80105901c065501e00d2078400e0028030142c142e402040628410740380d04580d07000c8544034001039900c05002a020321207560101000781500031b0b0103540040f090409816a2400d0344a0b00020324415900307070f0400c0038110042c0403070728140032007c10701c07051440282401941d003100b0048010307500c1001001103844031b0b900c032092030090060711940c10030510071040340480c07400c0c0840102c02c509801c0341068540140440c0c0e07000000c0490b8070844c2c010010501c2d141840d0700344001041482002d555003644c0300e006000c03104190020702440001c0703480094001ca079400c0b590781800805003126219034010b4038014020761440142d541300405483c1192030940c0e40d02d011a00801c0401d00032503004112a03408800c102025992031004a0641c1e010444d0300340b018850b0b80300c1e07001410f0160 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 76321494 1250 76320244 76320263
    0xd080304020402070305040314030a02060609070c0b04170c010b040b0f01090e0c04051807030515030a020103050405120708040609050102060f010308070302101829010b0307020c15030103020108070c 87
    0x50250030560001c4c001203101e0314100340b0301035982d2100b03640c1100000075003c254100150358205281d0411031285c203c4070031110f8045a04009034041c2041030015001050740da00e4030005020f0000b2843c02c0526142154140c0741c0e01c901c142c01050007843ca1a9036148243c1c90001c0f903207001c0c01c124a444035030543c1030b11107000c034a091020794208000000c0c1507802140c000c01000c50203403201c062480c46201045004805424449030141c140e83e80145030100044c040e11140c580b60b900024070129a540a00f4000f0355900c80d81803681c1840d00c2d40200342841d4400142c0c60003002045030041c412100f91340d8400c0580e5850b03c00480c0c8a48090315801c0c846688a00188041000203004040141c443d00480e0310210704900086d041e6514101401c40b12102c1e410b07070381c045c000c070381071000c003003a01d188030181c035000e8000e20b503a40c9040c1c18060310091090110000ea4854020003205007240f20003004d040b07562622040800880e84240000c0b800207100700b01042050b0700503070200341c0c5981d0050055 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 76322744 1250 76321494 76321501
    0x40b03010b0d0e0109080a0e031b0f13110316020105010609051c06061403010c0e03060403030513050f0a060c050c1002130f0806010e060312032802030a06140d0803 72
    0x405a00420281e09400c0da69101c0c0030f020003000d100d5003060b01c1c400e91385540c9454a0000c00f074000d001c0d603000d4600a4008000329103500c0c2c40741c80410400e130320444d51010500240c2010074601d0301d80300c083c2e108940c50f107000e0704030444441024520400e02240b5200e00c009070460101d0995400b0f1040c40042241601c0500035850000b04000d50703680c1e40d1020414501050300e0380c1007560080e60000642020b0201000c00030b08003805944905000c50600c81d25080d2403038042a6512401000030342056138540c041042c0c009140e031028840d5401070101c48640c810462180d44074910010200c03070b01c901d41a85001c14074082c1058401020f00c2c20047c10300318074420200f0010b50b20907a00e0300740c00000d4013004121711450190f81c0d07001e001c006005101c41c1d810811800d10022000d0041846030740204c01600507109000c0880307034095058407090368514400080510a4902150b01c00003160022081107603200032940030320104c03140c0c11691840306a03100148284a8800303803002d4616101000003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 76323994 1250 76322744 76322759
    0x3190b060a0e130e011b02100c09050f0d0c030312051b071b120606050405010504060e15060415030b0901060e01121a12060f010b030613180c090b03070803040b0301 72
    0x410000c2e0f010303008500041d42d60206400c540402108442d030b15031041049901503410020040500c00307005082100c4d003030441c400b400e00f00003403244a101d041e1109014116494500180f100b4980c8510b05000480d00da01c1d01425051400511000d100d240c1000906000018201d801e10180740303410320b0f403410669446070318a41d0808080c2d6218241c0328000007030091751907000c040005004041c0000c8043c10002041b06440c8180d010620481c14980c051110300225481182c0101d071400f4002080030035180407982c58025030b4000c50760614059403064110350160084804408100da070402036a80340d18003503c41d11800707034100340081d00750040c0b40307030b42d5910f90301c0005101055500b04450403171940015602000e444089101c0350002018004500008035405000d0080000c01c02d08500d4400f0220341045101000f03400d1440e100e00d2304c070009180950094500c01d803c000141315450300c610800c400f4100d250700f0280203102d401ca000510701400310607902034840400f111851a40b90680c0d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 76325244 1250 76323994 76324009
    0x61801030b07090812041701061a0c0a0f210f051b0703050307050a1419080f0d09080405030705090903040501031d0607081005060702090a0f0e0303190b060a0e 70
    0x4600b0b00c04a000c3c04a030f0807100700030070481c81840e1383d1104c1e0f81c1c0d820592820360040407400740d80d5844c2c0c1401c4080c040300858801850b001e2005228540d15420420b100b00d00e04810b00038054240e181140741303103041c4803002055818105290110101c9505400d0301140c0f80e40c429508400010002c2c011039201740009002c0100e020f00369000c850760a500d81d25031b14110b5200c14004c65032503000070008001c01804000417090000850041c0400c072213a412043c480780c0300e40304000c080d18000031b00c1c4c4080074040401d40320300d04035400042281c0d0f100b0745009100ca03841406154804e205140c00043d440c54841542031007a141c81d4050340c00c203890640198040c20000d9070610b2901d090000410401004001d4540f01c0c100503a40e4041c1420000f00070411159180c0001d400751404104000240c4c90701ca2a140d00104010700016203503504841ca04001c1c5001a2508240d010020a00a04146ca001c16440204807a84200020880001080f8a0307200f00e08000e00824502c00e001a8a1f190111 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 76326494 1250 76325244 76325251
    0x816060503060d14070b030f1e01080c01122a09050307030206072904060207060c050a0503070f0201110c070e0105010905030d03020c03070b010909030807020d1b0503040b030c030f061801030b 84
    0x1d0495250035111286e05800f03400460b40c680400100004108103000346d41203078040c080340022504055410a25441d484a540d21140e90512480c00b003128051049544400d4035000610001545a12140074001c552140d140c034040c00603041c02c1d0041801d150200b800c0c021203600a06146ca0a1440e036114080711403449013500e19030501a01807444c00f200e841d4103d1049220741801603a40c00c17646045001c4512298603a801c0180c00c1c0500082241c20000f201d41141030b07810100254960464100e0244c180148462020100842e050003a500c000a03800c098070021200c40c5401d81c0c80d03000440d40030410344100f50b410340c454906191360300d020703034000c00c911030400382a20700e0030045403500c014102083c0d020710881640d07510501d00781036100440e950440c4462000d810030702031400d0001c1c120300c004030180070304549108400b407c0190400407a001001c05120094070f80c9401c000e0031a5a800841d41d12000148002c00103500f850070b21000d5800603080c8542c860180d003944c48140801074000c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 76327744 1250 76326494 76326533
    0x705010c05010209030a0311070e131b0807120b011703311401022e1a0a06020c010f0504060206010b0d020d0f0c0f0314010b030402030312010816060503060d 69
    0xb041804c2c0c0c5030f10103104010384503000383c40d0300c800040580781c0103140c110320754000504083d1000c2404800c400180c00007803081d800c50300f0300b080d6015106400d03c01152580c400640c80c070a020340043e170400582c4410074158003a881c45007050307070381d801741013403160001d48054482e402c00c21480c2c2100c28454005807070150034600816075400380c2d0050440415a0b504a1009640e036008017070400c0d1381c104101d03a040e0b0451480c100443c04042220700390008010151102c003a2039903404081c0030708840407240c002c180100030b0b0314940c5c1d86000c003035165003005061030b00140030030110754a00c80c0500125002c451443d40100310b1680380c40c01010042d00488280b51515400300b100c1c80c2c840e00940146400c01c03c100200146051010401400082500f1140c000341070802034510302c09011540c2c0d0904503000c083c2c02c29903d5413240b0009045129443d00741c40054001400407440120000314944094a08000340080540f140001c1c0c840f80000c940c490340c400700c2c125845001511071a142201003900 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 76328994 1250 76327744 76327747
    0x52a0d0228080a0b15180a110f03010303030605090f222003011d060f0402030109050a0515010b030f0a11040b0a0c020f0d08040e0c0d060602060703050c0301080705010c050102 77
    0x20071241c211075005562000449610100f903000611a00520494000801c03035004401d00203018086a03003004044600c0680303000590002d82c2003002500f201c401403e940c1c0f4510703921a150318078100150000c5c00140c0019181900104007400c0003484903004a1001605906a640c0e1400c80c20070710240390712098007000b5080da0800002e80303840c48070807900007890107460000c12000c24142198010921110b031442481c020f4280d4040203d07601e40c00c0090074910030041d6a590000c00d02500100c17a0050051045100210900030040b41408010722541403507100d5036680c284072030081c003007a1b81070049003a582000c1484c0d0b1095500039081502c0384160b2038103203581d440c500303d450307004954081702095002450204501c1c0818054140101c100c440236000c3c07489481d118414000ca00500050941d01004a400429118103940e0001d84d030940c02d1282c162216170081d100c4105803045000b203030520021500c071401d5542030360b040e81c007460000c0a0080ca03001c0116440e50a44000307850a550 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 76330244 1250 76328994 76329049
    0x190b040603080a050d0b01180501080a020f0c0601060f0305060f0d0c050a06030c08090a0804050907050403080a030b0f01020d02060601180e0114150a0c0b0402060c0a052a0d02 77
    0x450360060f0454000c183c40d00e549800c3c1c088041e00a0b9508070241c0f50400c001682c190a43c1921a04d800c001e5070000e01e000c11560342c402420000a20505014408500020866461902c0300160f0b071030584801e980d80881440380b03142c0540070350720245c2e90160300940c4003241302180c1c2800101d02e66064094801d40001c0390b0340381c1c045051181141c121200207902c1b0120503418941000c0c085402c003803502c00038404042281c4030b00609019034010f09124644510104025510401c245c1c0c01842c0c101518a42c0e403d00c10002130700902d42100e10341e01400c0700300807081e42d85d0b001050440441529030042c00c0f0595803030004507495001c07107400c0d40160311071000c00f045201101f09003074042c016036183e0310f0b42c0e080154104001c0300c010081a1034000c034100809800c240c4d0005ca0441c00031b90050f1000c41039201c502c0041c41900403400055280e01c520311264084c40700001304140414192100c001148181e1441c0038481c0d01c1e81c0d0f580075000151f6149a0340141030014005184503103c6201d24022007 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 76331494 1250 76330244 76330253
    0x90c17041a07050d0b03060f0103030e030f0d05030105040f15030303052806050a300f050610030201030510060e0609041b050c06011410120e0d0306030506010905190b040603 76
    0xd00b510410300043e400b2030441182207040c0b1905000c0e500840040000e0301e001d6005089100341400000d040001810700d040483d1010403412004800700016100c01200c0150300600540003445001e10542c1440c9117440051120f21030200a001084c0d00051101e046071015000313000f014080316451405000c9440b200b9541d511000800c880519020449500c0c101c100804044c2c503802c081c18a11000040c203d010f64094082415149040240e1800d0401400c01040f00419100058124080c0300c1c00c0250340c3c04003080c10001c0e42d2003620100510749901083c4120104a0300852001c1150303160b080e0000e01d021030103800f80e0f40c8020b2011610094905035001c00d42d8070a40d64001240011076241e022080a00c00c240c05030a002c2a0501c41e04003e41c0001c2d130b440d00c1200f6003020700400d8136092034064002d42002c60403491010880d0101d401d00c1030014010f25407440309480300d00800002044418060054034020b141d8412000201c0e600b0500c1c0c407004040b0110005c1e0702540d00c0e02d0000024 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 76332744 1250 76331494 76331543
    0x50405070504060801150806073204170111040807120c08030a0c03030c03140705090a030803070c0311240c130905060117091009050718060807090c1704 67
    0x80081340c001051a40102120030740908071030b040085c058120034108400c0540c8a81007005182810702c5005511110074900d1000f49051002c085c0084400500440c804c1e000d10084526081132070020880521403042a01690040e4000d200745900502c00804c60351200e00b80a94500380102085260b255440d1140c920350f92001ba110380c041000078514100b41501803080c0284032045e82800e00c550302c80701105d245d80c07110041000c000e004001c10010307956181c149401001c1c60744034030466503a0800f01006450103800c40000ca00107903a014155030034480109102c0f642c40400100802c2890781107161130000500107004090005051004000702058810030000814510400240c3c03410003034001001801c080070f500115110072403d110014400040300c001d003d8401000240c00340741c0d80b5059050050329030120503100302000700305541c0c2001780d11140c1140e10307050843d03078250340e60480c0038152803d4101540c041048184910710840e070703551402da4000e205480000741e4055003030ba0344507007 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 76333994 1250 76332744 76332749
    0xc051f02300106080408040506070f0209010305070f240806030a05070b030109050a0b01020c01050913090b0603061e15040b04021201090b0105091f0903050d0c0302011805030702010305040507050406 87
    0x20000e01c0e100c0c810120001c0031109000d00b15a01e004d40c9580707402d4a48079041c0c82a84542401040001851028005840002400c0c650700801d80c0300c176560742e414a9952003441d4090580d208003043c1e80040c40031103504403e40e404180c1c4805003420364283c0c00503180300000612039a0075000f00c03503281e80026018800c00c40a0504100c005440b5410324640c80f08550008210403042482c0c9039039040c1c00da800040d19042c50900b440c285503a1200c100201d42a02d198460070103010382001180001c00c4040304c0c0a504c070300402e50855046980d240d41c5200c2e020081610003618201c0840801c01c0301c1801210050b40a0b0080d20105030754850401160881c2e11100c41030300d10816500c0180100c5e1268040c02c44180400d1038030300d05141e500e200280d80d03404200d101c04d030303041d08045c1c43c0781d4100e0295030000000d641080c00e8441100c51000702600020403410102d00652030300d80640e0039507682c92030b68550306800100035420001c541e8015801448058419070745440742c0c01e00001c455455020710400b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 76335244 1250 76333994 76334047
    0xe0c0306010314070b0711040b04200c1603170f0f0d0203060a05031b010302031008150a0b04090305030a09051e0c270c0d06031b0509070c051f02 64
    0x1e60800d0011824108001394002081107003080000a000c0740c83d04804000c2e00004076000114404243c0020b8014200c1a0a0f46010f00f1264404100c480ca181e01800e21002040240c1e2064405540180c020b01d2490200811070048000030f4034004410760090520300180d80000b0346008004d6080c4080f54005001411226400200b04429030418480000c000c00013503004056011003800c0302c2017203545c070803100c07410540c0c0440010703055581c1030b0040e0024124102500c090007848000b441c0120030460700b08102c41d081650142c0141420306ca1001c0d220f40503504c25055072520303a007a002610102c48151454400d15205003c6400601e210b20280d01c0c0701c00090034414205014000101e44001e000d0300762450042c0742d441c05540f2403a62562041e044d01406550f0044641034900030620749e00090003280598802e141c003050440c0c0d843d001c0da10101d5084642d50b4498104030b0703901c545200300038001e03000740c1010701900922081d140c0a5900001d070150400094901c020342c4002400c21804 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 76336494 1250 76335244 76335263
    0x70309020316140907080a0207050a06020304050a0c0b0319090311070611010f1a0415080d120627020a0e060304080a0801080706230918090105010b0c100e0c03060103 73
    0x220442281e03504640803c0300342d031095020703d40800d001d000040002c04071401c242c0c000501000304078090164404941c0d11020464803400e141c100b2540d20307414404102c511001d4010003094110450b415280b060001e01840d808100502140c0009008030300003c600f4084c01c902c03c69840801030000c0009013070b13265104a1075908280300740c1d09450b00c99224648240c90002c1111a4542d00714190b00110400d48001c42c140c2d6507160180d0304600aa403250b200c3c0e003e00045401e641d81e001c02c40030360022290509100c0e141d00d0300401c000405030341c00080c403c850705100850494a2075009480008c0c44c60800390010390980c1c010428030f50003118101c034042800514071002d03070b401050180c05408910010701901e401d102d0041c0020345101510f09a0080179021004081c01e0107003100c4c91940e010b031180d40300b0310251410406c1c3c010142d5031401c542d400e00b000414501458016120301e407560b03000030101d05800100001c000d000000c4481c1040c020240c5815103510100300d4107008610651155 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 76337744 1250 76336494 76336499
    0x18050603160201050a020909040b061518030c040c1704060b0a030f0b10030c0b0d020d092f0f19050d050a0605090307030504180b040c030e0705060c060c03070309020316 74
    0x90849071300815401c140b03441840401c000b44c94600c859035005078000c030400b0417900c507040001d400c1d4001d410300d02c014031000241041a00280300003100c4e0200c040d02107842e06900b00741044251001000c0b0b0f0400509254104c0c07000341e8540c031800c0d4000b4029080068a0b07001039000c10545421504162904032110b4100b80c00c015400444c607500844504203605803030b0542d606c884100d01d203446100030605010450402c0340d034042d4112844071200c6041000100c025161080100c1c107100e000c0e00100954054024000b000603c1400741a10000d204443c03292006003048003e015000750401c0310070b044040420b0b2502d400b2465486c990090009002d000b5181c5810740546000900c0403109400034446c90002070707045001e82e01a28040e8800100c28003601150800030185003112544c010300300000c0103c0c030768056124103001514032003541d80c8036494005000c101d00c20300d1250042da40c003103800900012600000345030090f18500d400718a03022250002450191442241c84100034545000c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 76338994 1250 76337744 76337747
    0x60c0c12010504050d0c0c090614030105070906140c16090203220213020703020a0209070f11061009090804030c14040b010c03020c10020309030609010506010e0a080307031805060316 80
    0x1a0421400a1802484030f45099501c1d940c889241c0400301c0c080c031107089150820090f07503000c0c0001074100408100143e40d61118492080d022a8094070b000354642404150202e2050f00130130256443d68072880d071030a90740c021080c003660012203404d140e4080d0084d803544001c15000304100900b100b040250f22824040300b412900701380011600160848801c0440041c0c0f221462098081818180140c543c1c1450a003030707081000005000303501140d640d0400201c4d03900b0222a0780d51981c0c0d503549141414070504856a0783c8000d0707078050881c80f003001c2e00f0003808803590400c6c041184100b10131800c1590360b81d101c00700b40c00150408501c0391501d5541106070b0600f03100303a082800d024a40304914106685019444e4000c660344140207664841c0083c4250b4000c00c201d895503103000c0c0842d00c0610303103100d00070f00803e401e65045000540900602e1203500e820300e40e032019030b201100038514168603035030300b6241d040001a0076040902d10280004441c0c0e1071030043d500c41c10000300030644001c2812070 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 76340244 1250 76338994 76339009
    0xd0b0901050108070b0a0210020304080d050f0702070501030b06070602030c0f04090c030c0804210201020408120301082415130207030507051203090307030c061b1d0102010c080f0a060302060c0c 85
    0x21007900c5d80103011182d41c2c10303070000d03103008201410140181c0d20389460500e002a441a412990702c558144024001d10025168480344541c001c0d40c250f0301e1941d100c02c01101966084400b00e94000c0d014400c03500801c1c080d500650b004040ea1100c0f0b45010f10541545e007054006610444602d0341e07800c68404107036014042c070342c000005464501c01074034155035181d0499154115809030780030001c1140300c1041c005d41c11134000d04a80b508440040360b004d04c2c040c642e0340c0301740602c901a018000307440c1c81d5401100c1e504480210074962a0469075070385030490035086130601803030341e0001d007007035610b0701100040c40140076150081e0744070350740c5280605084c0d290000c01080e03050300001c104100040c0d0360022055444d901d50510f42000745280905108000c1e040d00a0714071310784007200e54040c1840341c0008039032000b81011601c81e084070a280006a00301c0d80c03081c0310318022480d020006240e008010300c1c1d0303550090010b007001443c152640c0100700290856401003260f0740c09000c1d0102c0601d4103e8 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 76341494 1250 76340244 76340249
    0x40e060403030c02070e0a0b0a09020f090a1505030426040905010e1003030f0332010302091620030c0d020d02011503020d080304140105090105070e0102060907030803060d0b090105010807 82
    0x6228103450005032000000c6c0007400480c4096858002e240c0960700d070706152005011040e003c2d500c3e1900c1074092051940464070403441681c00031070008243d50384841c20300005040d51a8941150380d140c03543c0580c40a0080070001c00541c2a0381210040b400c1c10103040941106180000e00b50f060403010060b081d0050500c0740d40c002c00c1002000081d03400f071100d0841c400309140225260202d0a6030f00584004e00c40304001801c0c0b13090b02200010705110700e45040300e0007260381c1c2c41c0640302d45008209001d40580c01a0006002c9041d1300f504c05601c0004100c000d02d540704681c50800341094850030040d0b1142d05d00d0040e00681134000d01503509029034a2580382c12a0391340310452a40d4001084c401c1070490040c08003c020001400b405070b600d0841b50760010001c000d200d6442d080002c0c500a110403105140800c018810b00c0030130b94800540746100c0c4504c46d00400c7c1071829a143c649240d00300400059110303201003802c40000d249020040d004900a4001107030a50421181d2801c2881a8 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 76342744 1250 76341494 76341497
    0x6030501020a1215090c030204050d0609020108010e130609080c010507030504110307050a091512030512010b0c0c0111100c1d030a170d15080309040e010e032205040e060403030c 78
    0x10050b89900124101000455505c040000303092004002e055001c1d0040383d0010750f1006511001c1400d002e40d940000c18228070036a50030140c1d80e2180003040803114241c6200840103664070b0044000740d4a6441402424064071a03a410310300303100b60150a4446c02c035507030030000341c59005000400005203a41004071800328050071580d03041c03002003811410f0f288280c144054403465589801d5598580490240441090460408829003000b4080303a0040540110603d40306000240e000c2c02350062310400b0070001d0240400004040044495a61502c141d0b0041d018860389591419914400d5968400300e030340b6101988244030a5141041003208650350180d0008650400011041844605001000d808e681c0e206d14038000c5540c0182622100d046180404040110b1b510f40d0002c06885540c0d012541400b40384014940d0900340c803101204481c3c2e43e40305000800c044000580c0040c9001d0101040340711a968a40028042d2a0300031821a4203400580500080c190305008032140240103 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 76343994 1250 76342744 76342751
    0x6020406180603020405062a0d080712061a070501110315030105010b0c1e071206020306043608130603060608130506070c020607120207050a1d06060f04030606030501020a12 76
    0xe2071b02040c0a8071070700c131f8000134a503031100070b001c00303442c10180710b806091400003100e029400d0103601a00a01c400c0c3d64803c0440c2c00314150241d02c50702d500600003038840540c10590341000e8032580004036004004211041e549807945540404d21090146101d038801c0c1c0c6403100f4a50082c2c0074903084480c10703080a0032100c8108484507220780d00094034248100042e682042d00007000041c0b50910032180c021510424000700c5407000e120f030a4004d0342c0512801c0350100305e882149603d00c0701d40c0a0b032041030002d04400f010700d0504000f160302898903c9004490051914500706141c1e100700701d00d030304042c011036030b40e80303050102540c426681640420700480780a1201070719102d5954501d4002c0c040d6040080c00c15240713045444507001e80c0d447d2903100301d01070344000c4000300c040c5d00c4482a00629004001f00b2900180407680000482e005610b481211105a12030105114059029210031030701034504100c008006800e6103c0c035002035010b000010384400000100811694501d07007130000032801c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 76345244 1250 76343994 76343999
    0x50103060b0403080306060705010504030201020706140709170a0c030b010303020105131a070c0f060603050c011d09041403071b0506030c030703050a0b10050903071502030316020703060204061806030204 89
    0x1840740803103058030f4000075101d1322a994880064054440d071180140f0030350806040c40304154054010b002103e00c070360418400b060b800e0345540c0d003800c1700310346500c005212404100314a0365804419140e031085076055a26524490b25510300d0520a5030040347e43c800c1c1c210042007416428800c05030000c154061400c0d505c0e1154540c85001c0101c080b4000036003600001160b881401185101c1c00c1d42e600c85c103038411342d05084c03d201006050510041c1c41602400c81c2c003510340d6100303405001800200304400b160700320b030780c1c0c003032101e049402001128500820404948000c0c000c1000c0c06006100d80007101c081c4180c5510540c0d110040d0348214002c3c2010700c1801343c2d8020003010380c2d40c05802840e00003a60790752403001070040c00f60f00c3d203510b40000041d00d05482283d8498000d0003a4002074049900c0b256842d03080585290f000003030031005030004e2000c56460404220422061440da104681941d503e94503800200ea2080c1d00000210304035000c40c100c035114181000000348070a040c01c42c140751 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 76346494 1250 76345244 76345259
    0xf041d3405060a0e03280203100e0d0305040203030702120d0e0d020d0b04020f0402040b040303110f0706260c04061b0b06010c02040e0601120506090d050715200d0605010306 76
    0x40c2040c0f1005011001c840e43d491504c0030030074064400044110320800e9101c011081c900000500c100364000e000d1145c0b04110000c00d030140c40406407500000f441801c52800040300100000f6001300e0b414003081107654003690b10300d650104034440030b4002d0000283c101d04007421100a05900798003543d152a40c030000360342d0b00303140e082c891504242d418600d541e40b480040c01c1801c04110703046d4040e00c0400e0128080b1341800c0070b0310aa0384607840713880c5038200e03140c070865640d03036040b8400c419036008020a01c047c0d0b21808810302c0a0703480842c02d000c0590b0007518078140f071104076803025400c0008101004a25880000c1850710004818488511003c03030700c6503c0c1d80c0c0c1000700250305000400d08044e0454986e07500c01203046025806550341541c54842d428868049000c0580b4076214803000b00e692400003190308a1070715015140d607860510182e680d8417104504801e122441c0b9964882d214800d50511444090b64500c0c5518650b10051300e48000101d07482600043c1c10075142110601000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 76347744 1250 76346494 76346497
    0x3110f12150907050306030a02030a061e020408100908070c03030309021503040c17030d1103010906081c0807030b0d110111010e0307021c0206131406090f041d340506 73
    0x5491450151380e20350702c51740800d00d0018401d10003034061249540f030b10184001ccd513001c0c488000000030000502c140301c074240c505038019800f0352810344d0840380e400c0380000300070362000040c0341c85082030605000991315000c0466801d0343c41940400d03210b003105000c40c500744001036680504c80d645a400c41c102500ca1010005032401120a01c401c0c038007000510791010016501c030810305130802e004089001030300170855082842103e401300c1c1030a0021440810200d049038004980342c5006209944807282110406806404038050590721460400541c85000994100e00c1c0642c150b52412640d1100040515025100042150b403605440703011041c4084125100c054045503545030203c49400c12071913022200a0017036021000203400140500c0c01400d6030111155101e032820740c0d08080c000e04c0f50314800d1003102944024a01500e403458901030380070b0716400c0c00b4174480722505501d0300200c81c9041d1142100411050b2a0f01d40b00034400f8004400300c0742940b402005942061600b008298903 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 76348994 1250 76347744 76347751
    0x2071112030c0106091a040c08070c1e03050a08150f0d020a150807110c010c03050d0e0d05070506010909020f060a0201020c061815010b03010b0a03110f121509 70
    0x204810400303a040c1660030000d49010180d004020488566520450001070640111b900c020000c1071106001c10314107482003046503c0a6201e0f010399035030359030313040703501e20844030003103a212141d903508c030054040c50b00461000c603210b034854595621400c1d001900e0608024140c0000315481407520f04a600d03101c031801200d643c01d0701d140108034800d01c0040c241031280d4000c02c03280c400b89020800400d50103a0903500070032807611034021008500b0f0400783c848280000041c080341a0161050000e813280000303000242d90a000054444010f928030340c2000e140c01d040200007a00420014103104050121038010895240d0401c4000040e40c040b4107100031403501140b142d800483d200500300d000f90120303028161030704113944607840c00080d08500e802800312180814899900701500c0d82c11407403051030503204802c50403421070380703000e101642d03030341c05441040101500c4003083d5011000410140c031190764034280d03240e02c0e0a03054500c40c11400005056210302108040f245115840e070400d031982 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 76350244 1250 76348994 76348999
    0xc100e0c150c01020304030309120503090303130206090a0b180603011a0c07080a030801030b07030506030a080a020309060d06051206070c030309170304030201150527090c0901090b04050a020711 85
    0x200c41c00310001d200c50056442403812035000104210800d40c1c1a444944844d103d6002e01d400a0010380c001c95403030008032880001b13a40200041407284a4040310701043c5440200b105142c501c00001151100565500c8241d0403003002c03840408200f801c2c0305220135a00e080d140340b811507140c441d02c100c0b0702010b400e000c118044001405205c40905200d484080d2190401700d82c4003842c03514008009950920060b203102d808080440e44a92203130040c03a00a48005000300030500da02e486071052640310f51120340941c07100b00300d40c540e1030301c0d4000a171240c5c605c480750014810f40b90509005100481c401d804503d40c10072400c204101d038020490a00d1250180b40000d0b0010042c40d2840c0d0300c240c105003010f05444c001c07007080105941500b080483d499081484141c00d40c0d2002400150402d1b08501044100f80c42d06190345c508101c681141e1005095040b00c1440c0c00c82400326000800a81201c108a40c130350b4014841d508007802140e40100c104040bc44c0b800c0e4154032000d6240c0075401c2c8092 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 76351494 1250 76350244 76350259
    0x40b0d1704030b0705090102061003110f01030621020a0504020901050f07020f0904150c03110a050304080904060312030524130603060516081f15021606050c100e0c 72
    0x9218000010989000d558060803c2d1a01d040c1414068020307044054414010700c00d180c00548012200106030046036444109545610000f0080181c1101690f03002d0b41056550741d0000703055180c1c0180841c20400d0f10040208032116401400000f104030380040380120700400062445036484800c45170a00039a0708071503100c120504c002149078200050441c2d11007070103c180b0050180800820b8040107070380350f0070000580495429025034070240580c80d40201c0034003e14842d940908025a07010b0f12407400c2500d004507101c001421500031703400035100380703070b10410414041e0b80522440740c200c20031131080c0c1e10120050301c1c6800011841c10145004e13404040205142e00e00c2a04070001844d842002400745280003400000e0a2119041c05000140746201188008070800c2001100e1180d003c40c40d40321504108101401454121000d03085110300058a4007011300c0303a80403405403d0f2a910540c0d203522900034075181c001d400a50a50880c0b4010005181c008005800103180006642c1c00c1c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 76352744 1250 76351494 76351523
    0x120622061a040806070c0f08040303030c081003020604050d02030c03120304021002120412050f0d0305160809060a0207021c030f03060b090f1002031b0d080f040b0103111c0b0a0506040b0d 82
    0x60220007405001403408c00301040100416070181c128161022550307807a0700c080d0342c680518041c4401c00f413202a4204004010900041c03c3c8108104011800902143c000300d600c00040f030725110142c1038030341c0168004000d10045244c4045551120380300342c8005c0c81001d03060310f8000c00c81d00c034911984a01e007000c0340c1c20f0000c02c0024080301e55996088070030784200400b06103001c4c0141030304403000c2c1c020201a0503080703100d82c0200002805084581c004041503541c0c590079400a40c49a20240e03403159483d82011b00001c0000f801400707592290340c8070107203405018000740948a80e0380098801e88400c1c09a9495525140403410500f5400c49642c0414a80c0400a0b030451152980b800303a803001000c640800f081001a05501e02d050303554820300140d555030207088060704103030f40007803004460400400c01324245110f0702006103402020100c20480e40326500726039480740d890448010a215003000708860f914414039511034000c0e00d003405210110f07000124480c00040004151a000c20b810 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 76353994 1250 76352744 76352753
    0x507080703060c0f0207181d0d0e040903170a02040803030c0a0801050f090402010c110406080a020a0501022d07240305010b130e0a0f1d060106050f120622061a040806070c 75
    0x552008c0b14005601245442011001c546904840d01e40b0008a00708a5000040c0c0c1803c4c422900c46a4141d60f41e00e1540311f010850050084002d020b91622540900010800603c20320040d400352410354000ca40e98940460301811840c0c0503803003e03200d0802c04414200300c0c0ca4004940382d0003542480e140303c0342c248514141d4066482c0d40c514a41080c90902d001c80c03035110000e207060700c050007110b0303070020750b41c3c0e4400482ea84d48a6040021031510a500900000507117800c24141c28002c840a80d5182a1201540031081c10321302c03c00c2d0f04025030840c0c4100c1094152140c2e03030140264019907440e01420505900501240d0310441d86041a41d600042045c0226800b00c2001520f25030305000a404400c0c4103000440c850098502601800c130002544501900884281c0110000c610742405c007209082490752034000e003070740d0b00041014000080c551044822510360624100001025801c00b5001c441507544503d20705010001040180540580040c203039a0140d45450601ca0b0300d031030383c9030 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 76355244 1250 76353994 76354001
    0x907030f0608070609090f0515130209060310090e0f0d05090103090206070f05070602010c0210020d2003070f03140105090c070503030108030414040209090a05130507080703060c0f020718 82
    0x41115540103c800c0030a540e6403004890f4104c9965010074890180041300e14012a4010365014015403880c802c1c40071541042c42c26005805d1207040010304015072080455400d0b4000c4414a03407405010b1024855034903076218078040e4113466002088131700403000c88180c3d100e203c6811030041c04404602d40041b40e1107500400000c03035016203060f8440b220b074a004081c2103100a400ca0b458000c3c0280450410700c14030a4a048400aa00401c1d1806203208800d00035030011072283c3d0826207801451408003080c4400700d40c2003180d01314540d5a860100c4000301222101c8580c0000c0606018440c00304500f0100054103440c01194400305c40c1c3c594041e841d40307a00c034110004017640404800000d5800d001700192040f50018400e088110502c401040100c0c8600359189900409441c08902a9243c1e5444654044071008102a811a0a481e154603041c8658003c280f25032003032006008200460042022044160500c3c200b861400f00020303440d40b00342d00070806030710310555912000050070781 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 76356494 1250 76355244 76355249
    0x3090b07020a0308130b0c0606100215010e18010903020a0501050c04030b04080906160b090c0a0e0a05180a0c050f041503080702060f03010e040308100f09050613020408150105030703020907030f06 86
    0x406c66550743c00c6e080002d40c0c8842c01141c81c02c1c480e40c4004203041c041800401c0b100d504a00001140b5066070074405c0120300c0c3c40c0054101e025201c11030700c0d20319070034400340f00b01e1a545010790000c0a10b07003d01c1c50202c6c20b40e00002e0a800045405000401c00581920816904550720100c1c02e43c0360004030010032a00d0040130405410544840300601c144060920b00d030380604050b105440080450005001006c600d922461588407220000a00c81ca44283e00181e04943c19065116005141144242c50141c80b22415a5281401030b0104900d15140c410506851001c1c1d03024050740403400b000841c925200c0c80068840c02d4005001421541c89030110b403959281c0032500303516561601c6840c240d40704200c0e01100410440004201c003403003031000d0f0008039804110718900715400d2880220160101030403681c0c0006e20001c0d01d4014241500160002c2c1112000810f00035950601203c1004810303402507000750071001f418000340e103520030040d42c400d0305810041840783c0d05042c003800800c0b007035 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 76357744 1250 76356494 76356509
    0xf050d09080c03220f0308071509021003020406110105060607020d0c0504020316030f090b06100c0c061107060516030522090b03010b0303120402011b06020a05040303090b07020a030813 81
    0x42d42900310130030b10070000340d080c11060300112201d480d4240540e0009090002a004034814400103002580038030f80904210703820768010820409582c08070b124245440043c80120307402042c00d010b850f030704c07020401030384c02e24000034005800e020021808078814448064095008500b0020521043d09480c3d40109006070045540340ba0001d81444d5260506490b100000e083c0200c00a0b900b8990140328000d507004142c082c01c5440c1c200401c0072100324140704509102c07a02d098940403c80d881e80300c00080c21a0703110603d940300e85e003110314206146900a1428003905012100e0b0410442c9845000b00394142441d6a1b54230080c0e00d40194140c0c3c00f0599180301c1030f00c4501282d401c8003038000e407500d95000e500034004188038104040d140d00074510440c07010500300000a000d584034848840819030a614000000c582c0ca446020681c0e01c118103041c0405d40002d0300700b04141e4060382c2d68008141499403a81071034032382e0b40007410b280e21034400a081c0716404a01c46a204104800200050034103 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 76358994 1250 76357744 76357747
    0x816020a0c06141c09031106040209060f01020a06090602091908060c090402070203101e14040b130209091c0306032004110a02100f021306080903090904050604060501060f050d09080c03 81
    0xc203079803028101445c0701b1800500900d14148015000061090040e58028844801543d44109105010202d819014110b2242c01910404101c0d10310910301c10390300130000942d0b5910b103501800380308444004007046050403513808022980c00802c440d60405075594550369030304013074000200a40100c40f00a0f506000f41c96142211490340c1c1d00c03006a58064061016042540c8a03d1100301c56800441c402c6c0c143c25000024002012903100590040d80554040c0344076050380c01041090000f1a003205c055032103008000b54000607440d07240341440d01ca16050081c0d5056680304c5104604030302c2951240201204102c4035540c990304200d46100d07440400c1c030f45032200050300075a5100d0342c0c01d8041805180026504c0715401c140221048808251181440b2900d48a000c44d10402c1c000c2041e1464003040c4001d40c5140e540401080c0180c1c0100010f0601d418a030070000d044a8049c0d01003005e00c2942c2a0240303010343c00005485005603240c00000d0340000318203240040344105505080305000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 76360244 1250 76358994 76359037
    0x2030d050a091502030901060b04050d021203040905090303040c05100c020f1216050103050903070b04120507020415180615110708060901021e0301050303030a091a070816020a0c0614 80
    0x6981c0d005e140b058491078000d105a642e16518800c441c032507030044070342121001a186016041404c0c1081c0143d0300d640459250698034981311085842c02e5502e805280c20001c01c2c8801c2c00408a4050050306040b81c56071a60b17000c810b00900b04003110140280110858031403070310280d640d4041c4030319040501060b84e910065503074040b42d40c07509600034030b40440c1c5400e001c620b80700c10010a60300c201da400100c0481a886503151011058520703106081044410001000140c5407800b4a0b4103da00e002004105a0308002c41c1500c00004075078807528503468440c0411103800300c035031035411103d01402c01e00100040490003d00740304c5280c05c0401c0c1881050300348510004154000d0040b00f40b41508602e540c501e400701c444240c1b10a116440e0f06500500100d80200240d900608050f84901d5024048003804084000310050440c3d0074008150141c0820030003950390201c0005250301880903050aa9050f95a044800c40074001c1c90100143e52100304c14080c0750300c088940002914024500c1c000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 76361494 1250 76360244 76360283
    0x2031e0a0b090c040f0f15081b040807032d0311010212090604120503010b04090c09080604051509030f1801020309030717070b03070c030c020301060f060804060b01080702030d050a09 80
    0xe2151054014405c01d4410008010000d082040107466440146d031030324520141c01110310003030140c101400d9004181c200128418120003d00003440c843d009042010300d0b500b0f01c00200340b6100d1650428019102c200000c4009003031043e141075a01d4105040c4032801100002e0080c000c508411214008050901031110000148603125610803203c0c0c000e00825581c00b10380c036020030700c0b540e012540144003d10115040c0d0300a0845c00c907143ca0482030265454541e545804001d91f000c0c2c0305900301d544807180110b00e4004190b80014824011403070003070309040c42c10343c42c4900c10b01035600081d002203c0070503178402e0046542c641c5000b41164111303038440320b103055035080c02c600c010150300c24403200040750002403003030320710a0345c6940315050001d100c0d0f1010744d0084207001c8101ea06541e10340000c9144010307501d84501600c0d4560301d007000c900c0c1c1490b014007260b45440009062041c5001004101035001003106c600d40d4601f0301c0400c903a203880600780040c00104000908030341642d0f801d440e008 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 76362744 1250 76361494 76361497
    0x501020301210201080f06011e050a08010501020712150906060f14010f0c02090402030f060720032515020703030207061a03030f070809060406020a051002031e0a0b090c 74
    0x2c81c2081d0810000d80010101200c0b85448004024046052840086c481c20f040c01c10241e0f0102040c140700940d1209990000260821086010081800844c003180900d030b20500035405080b0070f000400f0010300703010040302e00f100c0030100100445050b103940b0248890707540003070581c03550010042c04065100d4100040498080c01112240e0582100d000381c4d940c0f041c0c06500d040741180d195010054500d400b80101c20360001d1050360503118081d4400032041081244504c102e59540d54030f01c09600303200003180350719111344114400c0e50061180c2e600e258000d104000040d002c0d186010300003421403030b0412500e071800008500e2544007084401c24540c0503001000380320710400f4100010070400081c110841030350000960140d10a102d0a410400c40100502c1e085e40181c00503824810400300148055100b07410110040e0400700b098006c00404214030450b0320142c01065040d850112403954880701262a15010021080046400035900754458420410b002d04441c1c400d103400e0342044910f = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 76363994 1250 76362744 76362749
    0x1911040f0e07022401050d021c030305060112050103050d050901090b0d0507090e070c080307020c1906090803030127060503011a0a080109110607021807020a170412020411040f030501020301 83
    0x260040781c4c44207034058005200400800000c3d00000c44590800050002d0700144031000ca0b0451440d009114060f104030000901c103c0c802c5c3ea0200305860f0140004040c1c000da15004a8520305050060000800204000308290003514040341c5601009004071018041a400301041820000d40a00c80324526040a80304020644401c10036a50300d52501080310310481d441c600280b001960307480090407003c025030708042d10344101c580750ba000c9400901c120b4907135410042e540c1c001003410002e407500491000000c24140014500b150b00d020340c400032408102d00c13100005260410b4a494900c01342e0b010002400c0094000c00681d00d484180d14048200d0030b6070f80e441010768075000541504140070703c54501e58400382441140c0e09080900c00c858000080481c2c1c0860003e1140b41d0f03070101800b440e8442d040035801024460307040e040500b011040d84d81030000c2c0c0181088144500c2e01d095082010880d8142c40000311074181c0040c10000c1e000d15001580402c0c00c8036400130a02c00150042c505 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 76365244 1250 76363994 76363997
    0x6020a030c0204091a092b050313031418030d0207060c120c0b0f060f0f03030f0d0e010e03180102070609050904031707032301120b09010b1c03020c01081911040f0e07 73
    0x491803049071f403101550754102c20060002d003003000050700300707d42400c1400c03a0074402e04090b101224100502d900540080c02c074100d018070a221110081c0c5401c0101e0002428540042d040040c101140200036002e15440901201450410001c01764030070000214500d4002c029107225007460380c4000c0c04141e0075100c0070b00c0307220000d05180179442c0002c00310b050b1910050080d13260106034001040c0c0d81c0c221041d82c4a80555881056509000a00866038015000703c0074550b00c228003800f003096607151080d49411548480b806120f41038100a03000c05440007160005155130343d908c3c049032a210b4018140c51034020010500030015019004a81003030001c80c00b005900711034804170301c0075102c2440b45003880c00d12517401c1c101007200340300320760b4000c6224000802e00549100105106110503820b034240201040100014036134180300c407035606402440c140c4002d051100706a166690608541d24210f41d03603211840c1c0c490b8a41c4202c4006110402900c640d40707542c3d54540a45d81d904648a10 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 76366494 1250 76365244 76365283
    0xc020d11090609010e0105010311040b03010602010c090801061208090402161202071a030402100c0f0809040b010305060f040c02070f0305030a0207082103040204141f06020a030c0204091a09 83
    0x400c0c501c0c0c01400c2d141071700c0d108a000581a0302e484011000b8000000405c5940c9004220110f001404500210301900035500041440301461034010000e0038142e10088071640b40250904c032180c0070703503940c095941d046240a6251008080064001e1080880c90103c21041454101c1040756807072034119945059000d48005694504100d0030729a00409281c0094000700001b40040c5424041e41010407001c5ca80b824003a521b5917145a19524541c000b56a107010104286113103140c24020700442080a180620003030410401140380208449101c5200b280ca900600350360a101b0030a00b4028420400c4001100c0e42d01d0030540d8495100610b42070041c09a40008543e82d000040c024242c5008540108042d4020008000103600040c000b20392082e00c80c81038164044075510301500540085031206140703514840803c20b07001d02d50380114255002007504601281c0c000706900a082d40540f0080f074200054a009050003010820450411807000306108000e0400940180c1e208200322400303 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 76367744 1250 76366494 76366501
    0x1b0103110d0b1009080a1209080303150406090c050313050309060f120f010b0706020706060e180105010e1e06040b0d1406090a080301170109020301020f09040b120c01050304030c020d1109 82
    0x131980444940114805035020907842c0e00000d035541e00004095040d8545844100d840d0101e003411988251048244802c0059002c1074a15051043c0001088d051404010800c00349102604a00000f4501039091401270080400d00c4001c2c822141c072040c000b030840e0f1f65a051403c0003820368115861200840724400001072885055600181c1039500010740142840c1c00d0707645a8020b580b158008036031032911080700050f021080c1107014083c0f40d140107c0700304000c420101c2c9084a405a000c00e042803c10000c2c40318a007215480c015405c41b81c903502c0c07412940e501020402801d10442c0e9160880c0d0f1800700d840c1480344444440d000805902c0541d01d00341c4801d01000e035103034400400640b014008000402c03038075942105850301d4484100021074151440d4002901b26042841c1080b440d00c40002d0116451409215100e940d000403030304010240c42c100c1c0400c1c3e8640f96100c00754140040000401c0038140140d03624002c3d1940100381090b181a1490003915952000400038022810f80010 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 76368994 1250 76367744 76367747
    0x703090206210a050c04030b070903050607090510020c06030c0f070209010b031f031a18070b03011401050f0403031b0605130605060103050402030c0f06070b180601050604081b0103110d0b10 83
    0x1110300484042d0817640c14141181c50703006100360050310301c1080c00b0906000100103142441414480e0419865907070a0611b8101440fa960300c141041c1c100719001105000b21070341e01d040603039401076224981d1a40b148541c1c60042a20710584001a600c0042d071000014404a0138000b107200d40c03030154082c09200c802940203205080d1500000785070382098060a2410300c02100544d40c807900b1840212544000220440c1c100402600300004a040020041c03080d00400201101d40b003000f0302c4c5c19450700c400b260070101107001c1c500000b420028442103c094514564140c2140310350400020481e5003852003401070075684002c021103480e030804c0005601c56001340700d014440c9070090080d00b041e9201000b04102c200740729654542c411428011100030840609100b84641051509540c01f19840402c181c0ba0000c140d211034400c3c0e034108402e210703043c00400d001f80003815074044400413401007001a80900384040c0030a00b01a80814102c800c40300c2500100105072040d500c0e90b41c0000c10b07050 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 76370244 1250 76368994 76369001
    0x3210f021b06040b01060e0d0212010b0f100e0420130905100315110f070804050316030503040303050306031c02030d0c09080a03050306040b0604030302070807090204030b0f0703090206210a 83
    0xe000d0511324400c00100002030050340c02c0101d11000400c041c00c0c506a55001400128070b040003c8056950b1b1440c00d102810450f40350b01210104407210021701180660050510010001c05800f5a4036140b079450f45407501f10750350420f8141100440d480b0445081c12000720000b62140d8201d550030074020848000e080400f040569400070594030b01040c0107038168000c0c003468039280d04442d00400c600708094407920302400165108103101c0341d4440c9060101480c281c00d40081c0c08810050754010000100000100c030201c0303502d0300302075861303540d0b890010381024129010144001c0c5445400301489602000074810700c0e03c40c0c1c2e81005101d1601c035048800d40c0c02c03800b584200354440c0c0714000119000d43c015580c80f41c5d0040010509607010342c08030380d0a41041e40210050f0388a400b0500c0b00140074090280504010f110440c03d03d4503503140c1820220780608010103800b12500800d00035842a00291600c0b0f402802e41ca81d00c40142c0e10003c81c0d1348110100ca44004001800705420074071502 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 76371494 1250 76370244 76370251
    0x906050f030403050a0e091e06030f0a030f090f03060606110d0f031509020d020307110d02030703030b01020309040504080c0f07230d05060108010507120b01080403210f021b06 77
    0x920302815550303155002da0b2590f105052603010b200d203840503804960f450b4601e061186120303c0c4180c071400f80c0d0021080120202506842c401d402c0321004041c1d02d840042c0102e01e09070507140190300307400356507803d80b44000590014031204503404030200138480d0680146c0c040b14240c2d55024041c0c0070113402d02c3d40b90400b002844001500210f0303c1e141080c4a60044c1c501c00181e91704000301686d4034945e60003243e202c0c401d00c056a0750007000f0041141e030420180600d5008400242510440c0b20340b000b91030f0700c40c13a4002014590780e05601e00c5564400c03c10f552405001030000c0005080906080003c0d0304503030801081803244d804084001500414084125403800703803546071400c001800e5040c070340700c5061181e80003400c141d122000301c3c03c2040414028880c0300000545402d00420060140d01c1112503007407041d0821810489690b404020558483d03003500d81311600d000a0b000007a14030144c00d03480c0208a042c02c050065402c0e2550041100941d86040402e15008009a003500d42104a = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 76372744 1250 76371494 76371517
    0x140403470402090a060902040305160f0303050301180b03010e060907081f05070c0203030f07110405010506030403030b13090b01050f0a060914030703020a08030a0e0405060f040f02091c03090605 85
    0x40d02150040c140084600e402101031100841c0d100d488902c81d800700e0b0450744c02520542d00441e00800c011484030800006000e014400c00e0300780741107440190691206100300d0104140c2c04003040445500c1d80d000401c3c980c03008000740b12003003102003919036441050b9601031942c054540b002580d0480041e58040c5905440001502c0d40000c800550041c580100b4860038400da4039500001130341c0610081c01540703106401b0546405103401c100d5000c02d29440301038081d03072605005010581e9640e0599602aa00d464082400e0710b45401003890f007040700f1240f0041e24189018001003001111450303042e104143c03090009108244100b0044c00c0251190b040850014542072124140303220035800000310250444a9050303890380424601e03001a8428000c40c0c00100c1e582c0070080e40a22111040401142d007808107082c21030025081760313045901d00c2d02c9181d440074128a001ca064050340c3c82018024400c140c45141900a540b004c0010b4100310001030a2020104a113801442502d4508030003 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 76373994 1250 76372744 76372883
    0x11802040506030c1009031502041d100e0a0c030f140612070f090204090506030727060b0a080f070c030e010507050307051605040b040209060703140403 67
    0x56400340001403070007902003905130207502c1001c0926155401030342c245401950b18a00500e04c1c50501588040261001000d1180104010840b40503000c8a40201819080d80042103449001c03507061440c3c020383c400710424601a0420400c854035a108256202032510203201c04c2c24030041c103604a0b07000741c4a040540112001040c00c1d41040f6a4a601d41c1c0008811184210340f10405088120600d501c06038103581c00040901040c0c5d02c50003090f4200d04290000c0210f41d0400403104a002c4128440400070035090006030b080030f4041d04000c004000b5480d15544d10707003044100408100040365100c0505503841e0100300c50741d10031742600400c590103940d41c840742805d20004684035071244a06540034401403002c9808900706010003078030032951107036054810341780500303120507500600300322841184180801035403910380b08212190254146030940350483d40e0034880c0c4084c0605d07000074003141c854040c180310509005030802d510404680c1408655030005261103081d0004000d00d8152001 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 76375244 1250 76373994 76374041
    0xd05242d03120d0605040b010809060a110d060f0f0e01080a03030b0609062205030a0b06120a0b04030302030402090604060303170c0c010c0801051503010f0b0d0f02030c07050f01 78
    0x2400c0940804044000c0030390b20082a807040c40181a00148007210000f1350380e24080040b45014407618050139800e0034442060301c0d20340101c0d41c50b03210091002a4080d150a24510102104408c50b403c210602030100101d6885080b14080c81c0d00b94058055443c9450801040d500b000c031001d00e040312448401803048007100e9404074054100c9980007130704400244407202d569a66034018010141d004002403005600490003100c11a605d0b900480c0a9001000040013140038220215405071041c2e945031600200071040c2443c00c0390300e01e0080e021030484ca050208055040e0011070090b8000c4841140a8039600308000896130356200c02004150b40700c44407440c403107850b1007039640001007801450071303da03541c9000c60079512010303020f03400511441c005019514250103030010340d00074809070504540c144070358051303081c6240c000c020802c0800304590750b41070752582100100001e001810b64072030410703032510710080d04540c00850f4070380100c442c1842801014414000451241500d448a010 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 76376494 1250 76375244 76375309
    0x6010806060a0f09091e05030a02070b03071b05100509031207030b01050910090e01060906020111030f0f0a0207050d0503090c0108090c0d0204020d050408070c080708060109110d0524 80
    0x1040d9070455201b800b146124690303282d20154050010b002e1009559210306108000342003801640003c01c2128040c001d01c00d0700d1340d0001020510706544034802c07280460b0750810904d8080f40981c400c018038107010400007040008409010510269104c803c111740301d580055055980710580035001400500c0020714a1414a0403030111080c0da050203000e03503898a84518400300c0c00d811035404106180010442c85a091203030100c1e000d29a80101e046003001c9071640c0910720050218940c86182402041d0858802d5040302c4120741e10004503001d09810000150140c1c00482e1092120300841c03c0401c1a54000c1c40840c1c40b89131060003404000007140104189400c40c2e0505070f80203642800001000700f0b85104450046005007006070312400140390040c0100260341000b55260006103040000c084005403a0b81540d103031810216845000b11307c00d61450080083d0214050b05080c2403241c1c01d89140418000000e81030008440c0d00140300512040500400703d10044042d9144c0c921400c0c03 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 76377744 1250 76376494 76376501
    0x9010c140a080c0a05070215030912030c031501020f160e07020d02120a09050d0c0302120a08030c1c0c0806030106080c06090f01020a12170604090b04020f0f0a0806010806060a0f09 79
    0x80d090a2040c2800c21b50780118400c44081207803000013100000c00e101305154100801d40c403218201807440d14501c4c290f011640303c0d00015202c40c40540f103d400c0302d0021381c000c0c07000d9086402440100c070500030751125114200000c1d4840e00c0c240e6290a80490041440030600d41ea079500d844d0010204c2d150030f0720710208194040ca0242c0304001000e41c01144640e101141842e8050140303d0038242ca600714010403258142c043c411540c1c50344816000c0d000030303190100f91395100740d00700001c0340c50360100380c1c5002030303d104100c20046051401e000700c0990354001e44011f0240000360000c010168076807110581e40d4120588140c2d00540600c10703010305c2e15100328807980c40700041c415680306080542c0c5501140400c40340c0c1c031010602c1029600c2d002415481c10642c400404c5070f0601099802d82c48a031300f80040a407019000b0003c405a06455072034024410002e41006480705070480c1c0d46141711601c9450030300540507207002d0140032841e1464520601c0c0151501c2d151150a005c2c505a5a1b000a = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 76378994 1250 76377744 76377757
    0x103050a0b100c0c0504020a020715020a020306070e04060911031603020915030604020706110705010e0601050109031b0503070617011401020606010c060b03060414010e010c0504091d030309010c140a080c 89
    0x100311404e004980da4455001070700700c46110340c00601159042c07060b0b4054a0a41d4504441150701021000c00580d80000c0d040b50042e815003001d100800001303010601a0540b80c00c040610703400c00d4151441951030350010b40c4203840c4c002c7c9800803040c20100c11800c0c0e106000c00c07258030104418150344003000c3ca000075500f240e4014001841c0034443d80d5900155844e10396903401242e0081120700030300a081c0a212548240e140c00b4000135030401001070180b40b0346000103000700245030b038480303102c041c502c5941001e0100103088070200b82e070750703400281003081c04006003000130303070740ac000242884103c1c0245c803846038160060000341e502e002c01110f640f000f41205032407090300d9500b004400d4030240300c102d01540c0200e00b071603044016100e8090035100c07042d1410100da890704032402e1005602c0300a40f419141c818101040c40b02d104044402c00302002508401c95000000600556031415480551110000d4a4040d04c64444145410303050080c1c031101c90120b255400025620043c1130001d001 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 76380244 1250 76378994 76379003
    0x3070b0d0e010509060f010b2113050106080607110106080304031e060603030509120d020a02041808040906031110050a081003050a051509010c1209050c09090109020103050a0b100c 79
    0x200070003161030507825250305440e00c3c41960040424000d403030400042a41c050b0001088482c5003410030340c0300000b0100b80301000645003440801094050021041001600345c00c04024426130781c584800d00d407520029902540811500414041c3d105410f0045404880d12a13019505003460341c0c07504100100310311090300c0007400061402c4001506403041b100518040e81da81034a9450070024401d20020300317808074407d940071385401201c946d80015802c58480d4141c40104804c40c140390005030200e05664001c09940000c07401017408405544200b00701c034000c40446900104003c00c9c040a24005108080000d44c1009030816183c010305a00307401580e049a203100c01c0b6074a860319400c3c0300c8841b42c100c40a800100c282d031107491801400e51341100045000b000092400365024045c45207030710b80110f00c1c5448403103800c240041070040c0620b440f0060b22186c460700d0041e168034001d010058081b80442d11f40400f10b03030403002a108804450f00064000448404084000d4072480d518000846 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 76381494 1250 76380244 76380251
    0x607020105040e0108060f060901050f010e040f0204140f04020403080a0804080912010504020f0108010b04030b151c1e020604090e010902040f02120c0f07140a1a1501080603070b0d 79
    0x240003d901400240209400c101902c1c480c144180b0320b070300440307000d40824861141c1e01b0061215075500741c16010400c0007420400e900a01400114018011a030001130a1600c04107000410004604a0003052601212240c5001c0007080400040f03014a01028000600c2403040900f058001d07030a040c3c125000d52515420b1585140000d01500388950071b024590b5164420f00046080003c4449450032090030210074940c10a401c1131800e000d28840600306500701008582410f50005411406c2070001d8151045101009900291a040f820048403480d80184500348815140e180075150b032640108183d00d054505210500509031501420b84035540c0c0d050590010703980c5206404d0098001040035890703000c1c07918500103001e40202000c0c00440100028049800c00400b11203035143c1c05400e080ba400817071042d5905d80900c1d140700501000200002c0304041d080007005510448042914889a000720307001103c002c0704c00e4070b040d509039002d6001400341c2034008015102d810344590000 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 76382744 1250 76381494 76381499
    0x70302130203090613150f02070308090f03030601030908090406060c03080106050a080612030c060a06050f0d0206160c0b0703020114150a0e09030f071104051305070302010c0c08060403080117010614060702010504 93
    0x202c0403244901c1c1c2d10003030b00c1d2340043c1060030180c106184030351000c03429001e8000d000040021030f8681c403009100c18101503aa03100841040394030001c5c1c905141014104101d040d4803024058120360120000b5000304e0b00b11000007500302e01c200205c920300421640c0d50801510b5190601011200d600400c0309540024040b581107001c040080078400c40e40080042011403504003402800708404084501480e0b88040d5070015880b004125001d88400724181c40c03800c0b15038284042d410903d5000803900010014100c42815415049603120481821240711540c0f98100b07490740e0300342300402054001c00815001c004a129410213198030403031190075285850203000600745140c0c090703071044501e1400f8042c0c1100d1400c003403060f1644401a03803a501c12482141d01c0c0c0a940d07051a101c02810804800401c404002036014110001d14070801204d4180c00c21740350260450358240900400c008048501d102910414060705c1e04540301c0803c6020250a0082804115400a0401e07410301c0f5040000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 76383994 1250 76382744 76382783
    0xf050403080c16080a02010801120206040b0c0606030d0e01080601030c0e0a06090e0901020a0c0b15150a03050c160828110705013e01020408070302130203090613 71
    0x70301d4044400380241180455001030002c4150301501302401c581e1202c80c031200140d811195090560b009520804099906480003502911903500708c40391000d4046000030110000090080c0995422420b440d01910f07100800c4610342032000d24240013400c43d070080307801540203510900f880d0700e2601e0100311042071140072849004072940300d00002030030b20000f00b10149041110903004120500213510344642c50000400d550740302c0c40c014100907002c40c00300f0f909071040d009404100c01d0140c14445141c3c1e0f40c0e01190440d8002c15450790210b402e003400079400321516000c4070920440001105d410744d10517240c11165800000d540c8140d100c0104134200344554002440900f042c043d40e86651142203003404030b007000d11075481a810b028a00e0650003a1301c50182804803100c0030001c2d800402048000301954800c2d505a085d03505501c002404601e19038003045807400d07240207480d0074201c080034103040c4c1c04903c0b040f281da80241d0007007800b054015062a0150101900a800b06084000c1d141403 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 76385244 1250 76383994 76383997
    0x9030f0309063c0e0c060d0605090705120601020604150b011106011203021002030c07060b0102010915051b0f0d051008010e030901030e0c01020a1b030f060b040506060a0f0f05040308 80
    0x241a49102600c1e040740e8029066600c948040c401d07100e1050004080c0100e2103540e40c2003d16403e0b12440c400700b000961f905844d84804000e0800501c000c41c641003c01011303059078846000c00f0540500c040000d442540000780c01401203501c070082840e41001c1d0f081840050000000f56410420101046a000802009542d018040301035428603108070307510300070380307042e80c484110003260f4014000c1103405004e410a980311950445804100d10014400403401000202070080c81041051480c0400c0c0c0c40c190700052280110f96199810b4460800c003403560390241c041c07030440920341003020f030700000c01c0f90304540d801c90100ea003000744503a11043ca10b4296600c80d041c040c102e51003c01c00d182d6560703040c0110620040c250000e4250107010000007500c4040100000c0c142c0e1381d440543e44441c0450302010401117800458031540300a5070f181c0540500a0300488038803032820300012400501d0507004403144114540c07100803001c90011010b8540082207407040051117801c1c40004007103002c400 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 76386494 1250 76385244 76385291
    0x1a030a0b0604150612020a090b07050705010e0303040b1b0a1e0b0c04231c0606031a0f040b090c06031f06140f07080405030f07170109030f030906 64
    0x2040c888031481d2440601003150301c400c40c405462185000d0800440e038103c4020108111151005a5616550325082d511458141c1c481210401c0008001090003070104001c070a0f0351003642c88441e008200010103075030740564000c042c200c07001004118200c034100c11421283e0918541542c1911005840d80d4403411642d00d11902c3e80902d10092404100b132011142d03620014410b482400e046c00c5c0b107030b0200346c0880c00c5040154001d11950f003800980d201805640140c1000e540e040300e62945281842c041c0c507880c441107602c0c90b81c0360a0121035010004000303219210310100001e8550b10380e2100701d00c40002405520060107025403504042d242c0b50000c52003814401e044218904e02000c403d101000e0583c015010803848807109048041e51808440410400011041d1500c0d240e0402c113116100350392056902d88200700108004040c04994801100c0300e64084036801d00c5049402030a80d0182000107001404000d5038246160090f40508821405140c2c001822440c04010040007410013 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 76387744 1250 76386494 76386503
    0x2030106090b1606090b100902040303201c0c03020f0109170a0c020a0308040326040501030e030c0709050105011d06030f0a0b090103050c040f02160b040f0b0f04060606030e101a030a 80
    0x40080000032201820103c00803c8c0d80a801c520b01851501d00030401d0280f907840c03800200d412105603c3c0b00f441080f400044546100c03800c0c04080088002401d1804504400c90141c01520307040c02000106100b03094846801100c00341811051012440c4564440185101804031144082002d03841e4035551401640c4504c41c03c0b9a910300314103007a03d01404100704111188182008012000115010343e0211002800d0104121043c0d84103942103008032000103806100e0940d001400e40300507042130b8102c0d0000e8a030388041650f15000348441901d001003894209808002181202c0ea503000d104c0d91202c80c8020000f1016030346c5001600002e800ea0090b80c080d48030741c03460543d6141a2285000d200110300c0c0842c5003401185d40340d000516044405841000103800003818803481010103039549038030107c02d107410714102000018124003941c054590034500200032426138040d01c95103011034204001410320b0301d0503103c024040c0c00c8500d64054034429a22101100c1c0c0c804016414165128 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 76388994 1250 76387744 76387763
    0xf08160807050f030907030c23040209040b1e190803072004090c0806010b0408100b030f0609010c0e10080f0703110703020106031a010f060305040201091a030603010e0102030106090b160609 83
    0x9609242d950023140c0d0700310f5480d0312008003115110281c2c0b120895201c104c19100541c4a1400800007001407000c6251103402901206030307201100d40e8540b8041c89402e00300c030302000605c0880a103200381c99850150042075403080241c3c002144480701a003400f1044110100345005545001c54241c820200e400c40d4045407009050021100c18400c99024208581c01a414689000b20180e42c8512460702942c981ea1745440302d11063b1814021f400501c032403d0212203131402d10600d801d008100b104510000510540a040d02502c0d2101511b201e4403135070303581c48040344c94180381564a1080500301a0900d0b030f94602c2442d00240ca50092310005002e074000180180c49d601300f0b0381d48404047c40d01101e40340384c0300040c840f2900da54100300a464980c5000903896031148010390300480c00341c0040b400c070070035989100146800c410003184120b000f07030b0086c002002c01c1282d560a078002030240e0f00102c1c40e980400e001d440c0030913024080c5c0011700741e12601e0344101c0d9111982100d05607102a60009070 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 76390244 1250 76388994 76388999
    0x403050d020d050a02030d05040501060f080307050601080105070804030f12061e0f12030507060633020c1e030703140a030207080a0827040c03020a0f08160807050f030907 75
    0x80500001e980b020003410143d1500c03011120003034603803290506400c0316a99031004101400710035441803020b800070030305044c8210f031180111580e98100d01d0040f2050321404002044489041c0500c600403130840d102c02446480e165000d4860051000d151820000111546140d4034028010f1100600303240d03c1c450003107880c07010100c20760b5402d6048100da121000d0f408000642c410900d034412070f030701880c2c065210400c500e040701c0500b00c0c0f0307488a0b031400c04504209580c0c12080071510758030326050304100e01440c1c440c84180c2c3c503103142c41a01548400650031800d00040007000031001840002c0035510402d440c0e5480c8a140680300e07031b0303105c420380c4520071480030103404100041c05844a01d0040c518039490766900d200520890b010f00401403102c7d12400365800d4a111400d414944c000c0c0305101c05040481d004000790000b034980c5c0e0006440340b03035205515020300102030060741c03048420b8000c1401118250307080c030406003220040101c00c1203000703000302d09400514041c1c0e040380b01070a0b0051 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 76391494 1250 76390244 76390247
    0x90212010306022503032021191109010e180103080d020c06011508070206040b0601030207060207060c0c0c14090f04020a030b0c2706180a090c32220b0403050d 70
    0x321042444815500c040018242010b85c8c0c0c01149543c0000e1940c004445e078500300c2d10340c0d9002181c000390303800505010344181010011005020001401c1c0c1e80c10f841800400100000c211584100c140004514001480810801e800810064030001d00140c0b502410b8a083c6140001c05d0f40a14041c4400441100302281c0c00030189410250f140300600751070038561a09a1140c4e4050010703414540e0014040b81041400d030180c480503038002004101c84000610301400071800381408551128160070040b4200c11004090322600402421010071940d445003603c450b0702015000381d80c0020214070010004911141e054491120208107a8844e0850705c00c03021003504094140001801c14240da461940392001a40d4441e48017100501c0901c042801060b07110309950405d41159050a1525103110b405c6034103140004840401e5110001a4440321803c150004a110341141c03010415120300c500e960388105280a410014202c0b0141c0e6030981c06030541c481d500803034243c1c00a2040c41d100f80d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 76392744 1250 76391494 76391531
    0xa0801060e06030c03030301170718051b0a0507020d020604030516031505012301031d0705150a020c01120e010203040b040201021c080c0703021c03021309021201030602250303 77
    0x140a0700284007404d0b5a2001940346c2c0814041c130780c01c1c0c0c40006610301003800d041200344021b011402512052400e80c0c00302c4170140004403003200200480d208180c4101c03400c80300f1039026121517501d4a0921159030308004031060000c40a90b031058003408040045002444244481610741210905543c030350329080145111503032442d0f209600d444010440b031084802400b9421007421510415040d801005030300400c641100c01141044040054009040c002a000c0c1070301c0c011104071441110860700031a02d407064403411340c01600810000a03155004e100140040b4103003400200b040c10710360340828226002100c003650109028000e12096507014000240c00306444044002c07030f00034100000d0724080015054500f4640c002800c2c0041c9442449040d007001500380525500f0940100004c02039000802c4140e1a01484800082c0c1181c440c82221882207040c80c3c2514640e2958071508000c0d0040d40c20040c006058000219100b5110014844800d109860010380c59000303803260441c6 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 76393994 1250 76392744 76392751
    0x527040e030c1006050303040905040201030207060f0506180c0f1308060702060f012c06010210061d010602060f0a020f1c050a060506040e0609041103030703110c0a050f120c0a0801060e 81
    0xc1c6450004c0c244001c0d00c0100031030341034811000e0081081d884a02c0100c00030300c01c05034050400703490043c00d94218030150b04064006c420441d19507100e02150201d042054805481034480e240040240391480b25050018218030f64907001921031181c0e4451072641001c004407015401a0804410031503110441080a40544003c0000003446078101040d0401d082440745440101c060145c0000c01981c400c100d160783c0000030321804c0c0415950b558644445002040700381801d500c1200c0007003442440040c402d84100b555842a000c1134590910601c029032040754901403104d0200301d0011880c0241d5100280f02080c05800144c52800d801c04004035510f5402003881801d00b04010060071100d00341c106d030010001c40e1100daa40c0c03564034100001c0c2e0400904560107000200381c4c4400c1c50b80000710400e4049101040d564509621000c2219069690195962000303148492900320b080c541c850101d000400021241800c1e504c1c070001c4c01a0446500611044e0b450309800d2102e000000c801c0b682 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 76395244 1250 76393994 76394023
    0x18060812040303020303150a1a030603060a0203040309030308040204020706063213050606070b1e100b0417070e0a0905070b0304020603040807030c0215031e06010527040e030c 77
    0x182410b5980003910383c80007614001e05881000c40c00c0c10680e0f40c150400000f00341c0704c1000502400c020301140413035041120418400d0050400144440d56103000b00d0388100da1561b00d0801c15030555901f6620218064401c1c0d03002036090010344001000751203080060a101070703896600146000807172180c1c1e15540272a40c428882005200c95648400c400c100401039811008145540c844000c5180d9019420b40a00b1a4501505100c0c0c00c800b40043d90240c0b104100c40d103110780e42c80c94000c1000b84c1d281c0c468921050020801041802000640d452844142005071074125941300701c0380489520541d414412030b90349007083c50030440200010b0300100759241000d030451910380c0005249000040c0041d041c1076000454400301489100c80c1c80f90150f0081030703045204002e465040c401d4000301c030700c8104034042d445458144680b030300100e8400c0070140e403868a0250070f40340d01d20051841020201501c0003a40010280d03980e07134066008008070f0140150303101c00d003007091207280c8200c5621510 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 76396494 1250 76395244 76395247
    0x71e0c120908030f0703050d020307090315150306090204141501230306040c26060a0b07021509040e031c05060a08070303081b0d050105010207091107110a18060812 72
    0x4100b01200399125091824140c545400c1700741003d607214850030b145821250300c0081000200c41e008440241604c5c008d280f580e038800310b020b01c040121600a500b00b000749848080400c0040c0c0c50f5045000d842e44090000320720f401d50f0b040d4802c18501d040c0d030410500360035154408080c0d40e011034040428a41c4403c044031640e0010b01c4c04c000c91002030140e501958841c2a183c041c14003a0b81018240c8180c4030103050403840c10301c03c8002800d030680318544200110000091629468800c4e45d014640085c40d00407032040080d0b1003440744e4464088507400c5925100c1d468a902c0044c0080c2c240d0391400d101d004004a00010400b0880324014242803080003044000e00c0420800034144003682c0d45801d02842c02e8680c0d00c154504d0300c444040040e070b02c1c1c0000605101c800000c1d04264104d030001e0702116002c0b0340b0f800150080d82e80314401112801c60600000e404220b0b804002190141c02415000016450382900300b208032200701111a00c54035804d040200c00420000030003003d0840c1c1809 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 76397744 1250 76396494 76396499
    0x1507080a14010b070f05061305010b0103060e0a0902040b030706020303091014130c12050f06010807121704030f050304150c03140a020106081f150803070209071e0c1209 74
    0x90440d0700306018110b4282c1c0c02140f2103007001040718a102d1480d40003801c03503010f4070f854072064606240003d0101c903154244004841c40c0d5005e0301504050300e1b91003000f00140e5440142d11001401d840780240d074800d44880c0d0304559514144550700c0580707280e034050365507860b24411b0145001c0b40d0710b01d0f400030703d8500800100151000d02403142c002454600c0d0903120409400e150000320303c66002001c01c004162849010010000b0300101a40c029500342c41040eaa90030400d5280c21346441000b24000c2c00c0723028480040c0d0040d09800070116141c0d541800c1644a445d801604515048100e0b819800080c0500c1902c652595012800030549004d601007041564004c1c00f1444180000280390404503007480c1d071a000790040f00240c42e01c00200c03803403994040c103c040024a2a05400d501600d0440e000e20051201b06010080d500c0040041d031a100c2542d0130300418001c010480c00410400c44400082c0b030b000304a1002401d00b440c0d40d440c0344102c0c1030410000c00b144c440c2041b0280038407032f80c08 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 76398994 1250 76397744 76397771
    0xd030e040e10230c0703090303050a030204081e1c1b030203040306060b071e03020312041e1209081b150f04081b030615091005060706020c0606010f020303010504050403050702031507080a 82
    0x4480072390350301d0f1a0464448608007800e4019000d10340010280d40160050b224640c02e02c410141852214a01101d100c44030f0f500c44000140c0d920348004000400104c070079000345030b0008030100524030038030442c3d1410340d40e615100300701e400c0d6070030082c500040014140d0600c112504002d00840101c1e11407001d14400780d401941d20311400c03625190105600c800241480b40c850320748072815a00780140b000d041c000d480e043d540310300c0201003407001c20341a03500858054000501c40f0b24503e1000c040d031b00301d00400c4040107205510020031100b0350108100c40103108005902074002058410f000700140403002401c2e9041005c00d1110b13900951200042040114030b4482e0413a00340c1d8161114074141d00c600e00740000200b400d42040c2d8002c3d00014810040061990003440d0b501c1c0000e0640341c0c01c0d1180c900450340c100c10b10000a0040c0e2043c00113100c1d91805503c80340d0024464140949000803a42c0070a041c00901c1042c8a099007030003003006440f5400031b050540c4401c10701c50800c14000302c4c1031f4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 76400244 1250 76398994 76399007
    0xc061201090b0d0b0f0916030203120d0204080d0e010e0906061602010e060a0e030601050d0c0b0903010605041404020f040b03070303050f0c0703140c0d030e040e10230c0703 76
    0x50302001c00e8440300401c1c403540700c4810049910b50840d01914061410308400560028107540041c04e03485406450118903143e0f980c90400d036680103002d841d0203100352a0595a40d000b440a000440798200400039030b4140810409040d0549600c0308011155200005416080341c004210f009040000800040b0340d202c000303d80e03e80641c200c10a51500040c0012116440700c080d5240c2c00034000600161240c0d0480115024603904604440007aa214801d100344018020001010041c04103014026541100064503402102a000181c40750780e03040010240c0d100490180b00f8141e4281c140802d45c20840050814140c094070207015070913451011a507503056030720000d800c2180c00724820345803506a030100d91006207076200b02c0d0020394a9080c8140c0701040c1e804004c03854818940d04141500b0034a11303005800e0b4054484d0002c00a561042c4005040240c0654125000b07214642403150003a11a07004e1080c032040d400c0b203444010701d050820400c0c5c0a4680c41108400748503890001c0d610a4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 76401494 1250 76400244 76400249
    0x50906040b1303051b0a1a0304030807020a020d080d0b1e19030602130f09050c0901031e090507051009050f0d031808031810091401050c0106090e0c061201 68
    0x8020340d640c20320003412071000c50064000400f640034414030700d088000d04070b03190055017501b04d808850b146e40e0340302d424070000411b0b00305090030b0b0300906c006400310340100520b5501030303401d0040d528035821640c000784219007401d8040b03032101c4020810b00c0c49d0364560710442810340000c2e42c511018441c42d03007000c4c500319406095188a506480308400d805000c19502000842d440881991280c1c04a161407a059590740512000c20200d00400039150945010700d5000d401940c100324907040465004501500001c1c100c0c00f004401c038020781c0c1f802c101512448120501850152005070b060034200003072506c070440349034100003130f41c1030620030743e5642010b10f15804400c82e054020400e56140560310104945a4006900154003002030680c0010008048903808031079880c2414201c5400c00c050a000c000940000a910b030720709116032001c41081650540c0141042c5062003030030000d4a0a5400c2904020096a100c0640c4a6000301c100040030100300700b121428104440fa98402c00c0024051 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 76402744 1250 76401494 76401509
    0x909080706050f04150c1404090204081207080d0902042309010501060f200f12071104051603090503090a091d031c0f1b030506211f150807030c0605090604 68
    0x42d58000c0b189801061030395407c004020035251555030b561076060080d0001e100f2041d0601a41c01d0a0750520102030480d000c1c40d50044c3d000e400d003804004950f006000c0c00c3e00481e00f20380d641100e0600d0451080f0f0700c0100c08503051a244051030300d10710340ca003234070310682c403c000b0310100c450041082c54221082d1088084855844030061086c0c4500c10314000420403c0c4c0294050703c1c1402c21114070180017004004c0c0100c01da644081100c0c4240001c0380c0301100c07410b1004902a12100c1c056200ea00004110303406442101e050502c0b001c002480c58405034030815035107540300300c2c4a241c40300c01c0c09500c00d811032180155040900b00c4100c42c3c00c0b1049507000c0c200056441c00c0c24902070031198031085421850040c0e4034400b84020340040e00a005c01e43d415881140b0309160700720820405101407460704000c50103045070344440100b0110300818210801051030701c0340da0361081c0c3c4044003038440080546c000200030322459420141d46103100d03038001d00d04028080008158603120b8104440840309031 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 76403994 1250 76402744 76402751
    0x415081207050a0c15030e030306011b2f030f06040c050d030903050307080a0206150307090b060405031006050111030c0a11030102210115050319090c0909080706050f0415 75
    0x12407801d141403c1002100900700c5802c404085142d0f440088500680c12903a00c04009104a000380c2c00e03500d001c00c4501600003010440404206107865080b03454080c4980008010180d086e95545458420301000141040021000160915081044091034400003015002ea400c16882d8076040021340d001c1c1901880c00c00e182c1804261041d07a40c88020f54010060342e848070b68510300504140d014072070f100010302c80c81c0d0126045246600300420b40540060051414600e01540300300a001410140c03035220206210004160f28244211150020784090001c0c419080200141071007181c14805a00d035803043c4840c42c140300740020b501c0700c0706c0d07000340600c0061810140080c0c064418035810110042c443c0c0720000245085102e40b0307041c1c070565400c1088c401090001121070740400c45804003040e81621081c0c0d85042d807039200e2040180910f50700c040041d00c500d14242038484e0840112400d000000d03000081c49200e00c1a03c0e0041009580c6408600705a110358400d04240070681ca4090398 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 76405244 1250 76403994 76404007
    0x2090402120304032906100207030308060a03051b100801080c0603060d0204020d140601020307050c0f010908070e04110907080a0c02010204080703030e04110c1009020307030b1504150812 82
    0x60401c10f49004681c008085440c4200716442440000010317814600312103265004160207203040640000a680658001c101c91b51070f64900702c92490010389030980204640302e0100102e50188030a26501081035400c0419803220030601030f103194040880d60800291000602000303202150344d1408440c11100a6103a40328400040c090005030702c0001d40c0302e07200140e0000001c65a03040507000c0040d4155100290350ba00d00107907140c2c801d04c1c83c000d0254104890807400351400408112401806140c00f04586031100380c607604c0d040140d00054421a0b03d042003108200e510b030100d407804107059425a0076810032600140c1400c80107880118801d496081e4100310701c2c803d60580740203001c0f16003140c20705035481c00e003d85100340c100c04e40d60145042c0400d80030002c40210448201c80d024100408080740b102144000a0410303080491303160003a60360000200d051301d09014050103280d802c60204c0001e510400c42200d00a03940003403014000301c0300700104203022502061501d140a181075603001e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 76406494 1250 76405244 76405279
    0x11209030e040501090504030e0f0a030b090a0203010203041b0503030f0304020d022806021203090c121005010608060f01230c120c010b0102240103081b0607030209130902090402 78
    0x407110000e50082e01e02800018003000c25080070b4082c0d0701a0700c6548054a40b4410b1280309641200c09581003a45034104000003814441c84035405240701054508401c000c4c1d00207420780c1d10a80d400d9030202c1458003282c2c0024130302c02d000310061004030021442c00d440e0305480b00f0305000c01803001e8817a00d030316010390065490f00c030035980c0d400c2510b02c0300c8c0182e1220503040521820031030150400503c111042802c00000d0310041381d00444411000f411f03001c1101040002d0045440e1440b049405040703500744106405002c1c142c0600180d0325850b80500d41a020b00c0804006000c0365810440b410101d192140442c0b144050350314102002d840c1e9900c00b00011514111040020f08d0380003800140c010002d04065010000143c000d9003035440781060001504100d440f00410714244100d400700400020300c400300107100313034002d0040002c1c3c2a01041412814040c08079020300121307400003030005041c600160aa090100c03480b2082140e40055000700f2500d0b480204001e0086601012404550 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 76407744 1250 76406494 76406507
    0x2030c010e03130e060a0b0a0c0c0e041101020d090911040b0705100617060105010c02040e1608100c1e0315090902100f0e09070e0d0605090d0c0201120903 68
    0x400018001c1c0000d00e4120101c03079880d0b01c540041060302529400209030404180141805140300070100d0840078144100500300c0d50000c8418410310440c0306031a00014004201a402071020f400c00343c400345072a08240111890390000b040c1150442e00c4000351140c0c00040e0303803056910002c0d001075025081d00e0500c089124a4115104014010400c1810070600040c0c960b100307030510030148070070f070b540b80302c040b00d51920155500c0144d00200010721032544251804808540020004500e010f0f0090383c06003071030401001010081040344050121000030410105d036604444810401c0d021a400000c7c40d1508400021400360a0a80100e02841c42500941083c004451000c0c03122983c40814800030711100300300701e00800041603402407a074000c81d08040b40121540340d9106e00a8030100300442290f008100b0014059001282d0003203440304a030303043c0c41c07910400c00024941408000c0302c7c903001481e0034070030401240d041c40e200140da000280d9080300c1401900400d008a0f54901900d01c1e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 76408994 1250 76407744 76407757
    0xc0f08090717030301080d03060b04030305090112020307020a0506072307080c0105010e010602070e011202090603100204060f171e07090b13030201030c090501050313060e010e03090a0b070f0803070203 88
    0x50381c8030300710b8845440d2408001141240d540780112003102c0360921702541076440c180f06d01e0ac1c850f0310a21003000820b00030402450440707030502d44001d2035801c20200e441280c00c150707408001603110900d101c1c10400f04026a680100a5042448204600300c68000c00d8455028400070030f4040030540c003041084007800c0d40c0074482c402000340255a1516944e4400b09401d1017004011b1180102c00910010240d00e030906a61551091150b00c0506400b802000305014103499098810392000009072642ca2007e00080c1245540d80707441e44111520007814200b0080e4a01c001d41450000e010340540b02d00c8508000b0b0503112802c1140d50f8482c0010b4940c01d410341e100340c1441c00c00061660701041c031b01620405491007602c0802c040400d2000407240c2000c24010346001c03074001c0021070240394007030380e85c1c0d240c642c820100410180c456001c01825102d038400e031104240e1021500302401d140120b14100a090010411420080262110312210b00d0512000d482c02c80000080340c1b0262082c000c6941c0d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 76410244 1250 76408994 76409009
    0x150c0d0207240c0f0f051e13030809120705030c040b0d0c0602060a11031501140702150405030f1203060607031e0207091d0c0402031e0c04080705040c0f080907 70
    0x32610b4201c04001910061025400140221405151150049203102c8842c007040d603426040550160020000c1010501c0c0440d103640144a00d400c40a03858440d4805541315800258490903901b09006a42c464500c00464035041040180b249131800258400380110448020441203402d03c042800052080c0000e003014134a801d002c40c81940004106029264000b010000440040213481c2c1d10300060f22040c9024080d003207040029881119841103e01e201800e1600d020314030350000c0d84038803030300041009040c070209003040355243c18000d207a446a0032001078492600407600c4d4664910000b00014400e4401103140b40a05106030310321012003480c0016007079001801c80000e50349110601c0384074201400c0c078102051450351181c0c940b1001c1d080b02c0080401c551000e0401c0044e4200074080a41e02c003d1983d030907000341c10859101e0290b103030f032002a0f54840c10001282d0601c402d0341c2020b4000d50900c48040c2c03403254081619180d1440a1400320826203500d6085810320100d60300c80d58 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 76411494 1250 76410244 76410293
    0x80601030c03050d030605030d0c23060a06120203060408070c0b0307110c12030735070308070c020d02040507030f020c100501080d020616090f0e0702150c0d0207 71
    0x800c2048207a25003068901400488244c000c3c2003104801350f8a85000d03440d0503030400c4200c0041e0328080c10181c04411302c2441c585040c04103600010713000040344019040640d1024090046110040c030516020b08685050010b41128075000311303682d5140a48000c0060b08002524002c2c4840303222640080d2581c82011b50750390034a410b00500d00c0c21011072114890049510058003440c3c90324040c501010b21401031401c0005079100d48140c3d46800384140e0030300f10740014195500384002060907100e4440e09c08541c5034181c904000b469500024072590070301c0142000c11025030f41e54401222880d50484001c105959400402c5002d00b020107180220140081003c501e02900401c2c403c914032500c0008000503a600d0881d0390343d84440c2c101d001d000d6040000030601d1210901a1184a03070518105850526920380b540f01000d100b0f64810b00844500c0703010b00015603030503c4001c0621103403040d40324040c140b0000210f16803096100b010700e400d44c000f409600b0009811404444071a8012414 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 76412744 1250 76411494 76411499
    0x106060f08130b011805060406060207090b0607050d0504170c0d06090302100507080105040b090f04021c05030c0d120c09051306120b040302150907050f0a030609050c0a0506120a02030403030204080601 88
    0x8803c01d0b01800b00002c5c1690600c0c0000e9410305052058608590103a0300401c00c030b0385001c20007401803240c02501c0c4e400000402000000c034204000c0e108503032100380d45407642d603480c28003807091114454603159020f80241e80404850741e508440364044030b070001c80c00100c8042500d026842c0101e43c0050200703c905000c1000325407038004403210304032402568140803202c50201000300c00f2808444203038a00360201c0115015007480f03005804031043c440b008028040c45511030341e01d5600800b03c101110741c810810310586c0c030303032201c145403070413424800038003445100780000351103140b5130b00546004074103403100c50040d064140c122a0090000d40720300d0020b1082c41c1404041d00d41c044605070050304c111101c1c10b121312903103001e00e03110360301c564058441e1504100811035040c000740c215552203501c140d40400803c002d481013410861103040248201c400b60818000007000e01d41c8520302c21441400040700c44000d09800a500245403080141d070b0341c3e5035140035030083c0155000500c0520525001 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 76413994 1250 76412744 76412759
    0x11030a1d04060e07030b0a060c0203060f130503070b0703061203020312040302210403020f01050724110307020105060301061a070b06240301030302070905010f170c04150e06030106060f08130b01 85
    0x443c410406507050400c4a8980c4400d50704c04009c5038000350180e00210000700c07415001512280c0040040803000c000d0b054585030b291464100140c00d03a0001804070511162a803d40b007140014407000458a984c0c040a0314041d45901074a042c02c1d00b61132803000054201072091102060303024401d134085000a4400d45940e000c0d420602040303000c0c0e90030a2464030342c2d44c051030a8425555019448002c131042084034101400c405550071000c59440d0030340014560690405180300e021260300004107450103200305420344003550700c09403403000b8441541c2d0601c540c5408075559140c201341c804d040c3d920346101080c2c2400500c040e400400c881002e017410007100c6000154122802030342150529a124595107003100d0081c81814011882841d04100d28405000c05201c904c42074415a45004000d0000c1016201740f1034a50401c2c8002043c00e201c902510740807250806425002000a0742c00c00102404190000c400b0380103102038032001904000181c0d00c0d0340f44841d80b00b03000d812a942c3d20a00d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 76415244 1250 76413994 76414001
    0xf140d0501180c09050603030912030c010203131a04050d2f010204030b10050627090a0e0706030e0309040b0a0801111306020a0b010509060402070606030f0311030a1d04060e0703 78
    0x5080b984090f9001c000103c0d26a98040c2a00440340200a540741c4000d11081013071651031554454150300061040c0e2000040a2010754807410300a022092040000d240000250707004a0300120440485401c0c040400c400140b19007010800d41041c0004c01c4d01d0780220a003440302401d0440d4946030300c48440703420007410b401401c12241b01c2e80c800380080c0c9a46d80c0c000c0b003c03074160103000d4100005009845840305018400c003c0c84800c00080d01008401c0004110710342ca00b200c101480301c0c3c031080c44043c00034041001c2d9008000625082040078043e86a064892190030000b500c1940c80e20707000c1e840c42d071b1011120340081c041403000300f0400e0b0390b02e400465240c010140501800300da903240060524004507920a041c1d611502180c60781e03003081d081005030300001c0e04d520f4019500f8001140094854425070020314021014810440c4440ca0020302ca01040040440c807908180506038600780c20402248000799680c4072042950200b401250080101d03078032a1540c694030005003c0804d81590 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 76416494 1250 76415244 76415291
    0x50103080c0610030305090d0602190c11030c1f02120a030c0906090602031b16060908010501050604030b1303030b0a09050612010510050d020f03010203070f12060f140d0501 76
    0x1e0a0711403075920700c03651802e0007a4520011700858007c000c030049030701e031414403251014403c401c01401c120388610b05030300303210340c01260201140201400d5010300c48248500700d6808011801015109c040c0d2010408514008074001885014114400290b600030302c258200d000c40d0590359500c07080321300c400402901c80d01c601d01000c6a04004041549071140c400c0000351091a0010b51410b0800e01900300f04140800c1c00c0d50a50007121005410481044c669000030200c580c1c40c0728100703040c44181c03401c580042e446a4807461081208000250002c442c9541c440700403104618410690304061340505016021a907114042d9900070074284090340c40907005110503101d410b403002c0c800c4042801c80b5000d83d107104078251000e40800441c80d0184841c41500c0c07002e0f040707006540701c8201103800c1e80c009135030240100d81403c04000c40941e0003001001400d403d40f4040c080c142c680440440c003e43d1711301512502804d20200810244c41d0030441e07043c4107510034002c200341115080b81e440f0305100e82 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 76417744 1250 76416494 76416517
    0xf06030c040e010b090d140c030712030815030a02010c0f0c0b070519110d02010509041406010206070c03090b210f060f040501030c1403120a0f0f0201150b03090304030605010308 78
    0x900110b4803043c0341302a102c4941014015440f4613101c1e07110303425601c42d600300c004480d100f1074000c216103440500c60040107100b40b0315045d19881f15841d015000d02d2000702182d800c13010f04103002d50340d40d074005080d500340c5030282845055a03805007000704114100c03803805020091602000581e00700c0b070800030f0507128050300a42e8401719a0300301c13481c001403048401a000380c4030403003600914075140420f0100c076481414007914102d00d80000c00d0607107078526448914007504000b00100c0b0358050020700d03489019490030014801ca03030343d0054500c2c0424003d91a480d4004141202d08004180b2040b2403541c851403031554915002e801c852000101710760f03003406205800e2003c4410300702801490b050342c0d4411031440200f0b04002c1c0a0100d141c6081c4050703071520a000c25503e1040d034003402231640145990303605500400d082000307850107036810f842c10b0843e8542140121200d21698194040e61242c81c0c6140d40c0752035039407170f0a1441c0519000600070317502d000000010401d00200924910a4a = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 76418994 1250 76417744 76417769
    0x1506010509090109020306010504240f0801030b1b040b160203011104051503220501050601090b070b0a0905010e0f030319060b03040b04050118050f060a060503030a0c020f06030c04 79
    0x4540045a260040c05611508008124010b0260142540186501c40710602d03000c0d00301996002c40c41d000c13805106898900d84a04401c031b551301070b4007050f041010209403c10391455403650f6075020102c500201103064440181e0441d0003418240402c8600505850201c1600e8040e0443c1e04e1400000900d0202d20961030712111084101c0964182c0702200c030003c1418890b141401c6080000360310080041f003244000001a48203103035400000d85485000c1c500002c2d192802000150942d1102d0f00403400b070310300a00c4642c00082c00f12080759485a140ca5022480828a10703200340540030f1403135141d00e075000f403403058000b1300c6c8004051485000607088150004582c92445401c64005000c0e840000c0b43c1040043c01240700700d034445400c540b10300000a240c848809114114440005046551350410b4113800d00841003003101c0e0340c2021140703e040100301d03d880c00290340c078401c107000b00d010b0048440000303040d03650703e01d0012030030400070340202e41d00d141c0041a04c0085d40107004420f0103000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 76420244 1250 76418994 76419001
    0x306050d05031b01060f27150602060c03040c030f051c050a03051602030f031810050f150a17010906020d02130608010602100515100806040e0a02060313051002040815 73
    0x30f05001350000c8070740c2c207001c0c0c0c05103d0811072101c0d00b01e82c0b111072168120030519248101102030f0b108030000c03a030108003800440c81c1400c100a0030060058002a8002028000c0c0008242401c00780012243d0000700040055614079080d41031801c04800081d060f02c000d4052143c0d242c100c0d0040903c41c64035903040120b5030b1801901e510340004010840c005031301c140100486110900300070354000d416402101110f01d1071040c07240c0341010700310401229588130740522003c0034440180c00c2d00300398100d07a0f0741543c0217482c010403551903c074070811980301902030b02c00d00c11150a500101c00107411900035562941c20102802c003a510038136802c03114216500000450b83d100ba007a07681030b11000e0f4050b000c000180d090f20400b401001d04003a00c1414068000c1c1425a60154100c103802c440391655181d84c946101000100c604480303004010b6046103842c900180c0d2040100c0303074006c0c005810000c451050b410301518000c0c0c4400240080ca00c00100412114000503190102c44170240a281180c0d4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 76421494 1250 76420244 76420297
    0x3020c12030d0c051303030e030703050118030e010e100806010e06030f07020607110705010f05040503060a0b0405010b0f0f0a03061203020601092a0e0316030606031406250306050d0503 81
    0x31449409071005c0c28215002e100107446500c15000302d8100030f0446d070480342c07a601c50f682107694156248000030b2621003400201900043c1910220500342000030800c50440c1c081114202040d044200b08a904400a54285e001d03012110010001400c0f0644078500300181031700c084030039180c40d0054450760001403c600e107d22008100c403200340c80501113083c6002c0041d00c100300c0d40d01000d01480300030b10004c035841c1c40406ca103d101d541c412202040700d0440c401400110348040e00006103c680c100f0090803907500684c00c07101420b001040701607690078601021801801227420080342001c11141400900d0f50015190341070b10b42181e0b040004065a402028008513405211030110b0110090407a40500a8850100c0294040c090f61062140da150402d0181ca40e90001c85100359621020b00c14040300c01c41405802c2d00280042810f41007071b842c40d070000c0d0050940035500281942c9040e9029110740c00c454000c220207840e580303880c0741601d070264803500300910261036105410342406200 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 76422744 1250 76421494 76421497
    0xf0305070801060803310b0705030901030c0e0a0b070204020c06040b0a14220f0b0705070c050303040e0402060711040609020703080601030b0907120b030313060f020a1e03020c12030d0c05 82
    0x761620301540380340150082281c0603400000c4444003801b4080840001d0041800340185519417254014544d14105d0030005000c49108110010410182ea50348941070748986a100c1c054500c0748882a0b1a04880d00c000b401900c00d021401c01030b401100b0a10080107055041d890085403142424091a40040e540c0c068a04044407001141d4101210a001c07400501846201c03046c0600c1c1e080d0211800c235286d03c1c808410a84541c40001d2000a020302400401204200a04412006549802e1034a540d810341c210014001910440000940d00108145050007000540c0068070502c2035640d2602d5040094000c44015008242c503140050844d610a2140300000c507002010043c107929516411107001e042501e5110308143e1b10307007415102e0781c2c1c108060032854007516001068642400401880440c1181000d0305645c4210070010010781c00d01c5151450349203500e405840344140d41012850581840704150304004011440100008084014681070724440014480464007002c1103446 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 76423994 1250 76422744 76422757
    0xb04021c020a0e0a180516060503010317030c0c07030503030601080906040201090303082a070204230403030c1202070f0507080d05030606070c050a06030203090105010e04020612060a0f0305070801060803 89
    0x220308266410300844155610f001e4010070180700009000140304182d8006007240c14041e106a4484441c10b0014031440b06200054400f620700f86080d545555039116401901b10040c0301490300120000c0c0544e00d00030240c90f5840400e82c200c0380e03015a02c1c100503480e5801a01c5171030000c0c030301c50000741d5120f0002504900442d41039449400301482d68800702c583c940b020b04941d6440260483c04004103c890013007200903001500460343d03d0f02244104800c549401c40d030090f030341401e80b81c0352207006800140301d94000d4041c10086840442c4203021901101440310440c01c15101081e05001d00918140c6d513102188107400300e511031603e80c40e404c3e5640e0360a21800002075410030001c0c903a403c0600160150510801e051119151610002180420300380c00040029502100b00400d06209015940c01024150005080c80c149a00070078814400e00d10480704148800d004030f002d5456080b0b4800042a401d0050048152a8034045480b111035206016541d0f0030000e0100e10170101108a499 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 76425244 1250 76423994 76423999
    0x6140409030f030504060216050c031603051c18060c020307080c0d06020f040302030a0f210801060305150604090c0215070522150f032406030209040e0a0b04021c02 72
    0xc90202e080411409820300074030888240d40c0038400110007000d51b80104c0c200a1084c000342c11a624424141407420400129890308850034242c100049207002c104c8000c0103c605c001d1400540144c070059030340c4400020007541840380d80b0000074000d58448100600c140c801c070141c5900c01c1e50307010069603a40c0c1d01c2a0040d4801307070011340840058465402010781810004186003480d0f56500024200b14469070b00380e8201c2403541c42103080001c8104001021541c030b0201e13040f500e1851100402c5a02c05000300c8080c540d8500101e20f007061041d100283e01070005284a607129140d00d25140a00301c4684210054800c001e0341e015540c03c0c44554a100d00d07180e40c3e03070303c0c100308041007042406a11070141422580d2714200105100b2840202c40041082945861a03220841f000c010100c8441600311203034600007090440603001d40b03030f07038510480d60546400b60722044840002002007003110b4840600c0e2140103116400c020a140c4100d11541c001c40705940c0141d00d80311440900d80c20100000d6 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 76426494 1250 76425244 76425257
    0x1703090306100e1605091002010b09090309011403010e06060307020c0409080c0709110f090d0501020a051305030319030e121c0501060203040b19031811041d0703120c12030614040903 80
    0x71b1103007030912101402002c2403001103050700c4441c1c0480c824070406da500d08004d400000351130346156008000e8000301101140b002d490b5600d04070031881d9004014000b24030441e0000302244080e403080112a208030710040c420880c1c00d24a04d80151140c0c004484607400c1d000701400043c510340d8074031070b000d80c05480d840068500f406110b070202da1584510300c503030382c054903002c03052010906c01d01c064050035400c0c0d140e89039508071f210078200c103101d541d500c05132180d8402c04c02c01c09040d000d052846160381e204e043c0418242c2d044035040d4282113020f03540351241c0002103141d040c2e03442c5807564100b0702c04c4007004c10030960362280d50403030302c3e80308900840c518040304100d468451207114aa404960301c49190004018500c000301903503503170300c1481c01c1e980d4000014088115103014407544000358155802100b40d801040c00564440b0312a100c050100c00b0b0701d00f1400303180760160710001c0c1d40036030100314102082c030003520240013000d59026a0f4203442507031036403030082c1c1810310400340b203260541c4500 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 76427744 1250 76426494 76426507
    0x7030605130308040f05030c0f0318040504110904020604230406090c080414030405040501080a0b0604021e1e0c1e1912030905031813151703090306100e1605 69
    0x80c1744120400790f045038240710800840960301020b2000c440001c0c013010103943c0c1e0741100f10b61651140c6a000c0002d100380e14000c18003000800e6068041d130f240d80250b43c00a010f035038500000d202c0703006550180030881c54000c03151201000c0f008c03248040c3c8001716010000c07107032504500310032140780ba40b840c40898280008640071600c0314a41e1140f81000c00f0450340303002e8460300403d059800a0b402000142e2010040e10100000400078613400701c42130741c086091440c02c481c102001003c403206251150400507102c021032440220251040d050018601e6032503010310100b951b02e0704c1c441042c20000403440c04410082d100401e40f1800d802000460740b03070a00081e1900001c102d003401002c41855a036440c0300000590a001030080d0b10500b00040d002c41c403141040c0074400002040d540c02040c505000a0a40e0302d6a20b206425074200e24042c0c902600107414076441e6118590065030702d8440d290400018500302c00301c8000340d6094000c010b0170b80d118100c002c20314607490701c07050000c20803c1c00350 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 76428994 1250 76427744 76427753
    0xa020909090f031608040801060608180d200a020d0308160c0f08090316030302030a03060609050a06050c0a0b0f04020109050603191a06070b060103050105010914090a020f0307020703060513030804 86
    0xd1244c0e03074040c07000e85140035a150b01c078a0845101e80d00000200d00c103a003c0100864581d05030101c5401e408016140d41180200024140daa05111034211800030b80c108038a02c410410410360081e80c058100e10070440d550401400c01c0d0070407030b012034400400c80a002d07400f038428148022502e9208090091010f683d42c0c50585a170000e17142e49425100d01c45c80411181e408010280003103010350080c0d51f5405840d08004c040d00d141e904100140290448104010f46842d11040304844207490302d1600d07100740599040c1070510041d8003a103202004000d2007501051680017600881c403d0326442130040d5264280702c40d5000c2201e019600642d0817042c00c2d25039410b50400200e2500360750702500e00d0490a4005007207500440b4081d070729000500204030302d550300b51188030301600090032318040d81883d28000407582048500c41a0040c40b01401082d5103117100d4058034911080403802c0307500c915040200039036a920a10007940c1c050700b0400811414441d082c4c0b8250241e401d640c8145c2a17640384d445 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 76430244 1250 76428994 76429027
    0xf0d030909110c010c030e0c04060605040506031e01090605010305011d2403030a05130e060a090228020d030f0614060304110303040f03050d02010c050901080714030a020909090f03 79
    0x8029442c0d9010006604116820f128000444a0319140040c2d4452503030000c0340f41c8030086203c03c0c0a1440c214003444140d4010b0145c0301200c81c200e13051542ca40d11002401c81d203480510307003107100b010703004000308000801c0c1c1c00c0481541c07000ea030f041000c0d84e66030106100443c20703056607590b1035961802080040c2d03041c80031510980d40388113250358030307100d90030100345954440c1020500141010606000442c070480200d0700510011850b041d46040c81c40c00203070840c0551189403c02c03030340052082c15070040d4001411070170800780c1401243c26400300d00a1b40b90582c445041001904c0d0141c052844002e40c0302d240103070f40ba45001c03248036207000e005104031684068402e03038017000d5568814115640400c01071020f0002100300c801000d1071490010310f0842c03240c000d40156410108000c400c11790000c2a2110260b0928050b246c40d128000203076070ba507040c418609402180042044103401d91900240b40281081c0c50307aa15580c4c2d4040c1494440d83c0800c00403009400030044980540140c41d0b = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 76431494 1250 76430244 76430261
    0xd05070219030e010215010603060503010b0603070215092503050c04090c060c0312110702090108030304050c0d0201170702010e160f0614130e01050405061206070809101404020f0d030909 82
    0x40368101d04000a020811b00402da204100190301c03090240407908081c050f0002526054861a0440c1061803010b911280c4621204040c07011900010798003010410608528600d0701da41001c032064407081c01c0310050080d00090360300d0302c40c0440c024200e041c80d100300341e040da82001401c4030150801c01e007124001d816040039030810054003510814888144544441c1c4815000055950380d86441030103500c4a0503804015150402d00422000c1603011800700c41d00c2800321915003104000c1c0c40103a800000000c0302d0100030700804100184036030150700c032844c9030307890300102c4541e0301c5420941c55540c3c03042d0150300e11150390300204000d4680154410910750403112100e42c00c0000075100980501036070340c0605d0360300c2401801000142420f204103a04050f081e1111b03000c0800403480d199548070090400010010142d001034030380c031030502c1524180c8400150512062501c044d141d818104181c2c1c8c1a445008440440d214518114100c04501641900d6000341d16141c0b0b801c002c010300340c46 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 76432744 1250 76431494 76431497
    0x51507050d06090c140703050304080a03060305030c060f130c0905060a08030a0903020a050423150d03090503060604050709181104080d080610051c020c070b0d05070219030e01 77
    0x5004101164581e806040e014029861002903c1265400014480f0910035044000b20000f008100c0100398030104896010b504100d0b10769882c0c500c2d40c0101c00401030380d84064541d02000c49c0c4c41032450400704802d405520036107e0722805445a100442880610b064001c0c9109102002004191031603081650302c54030007004803c05c141e0790040c81d0300310b0384110106000108110400e100f10f150081c0c449000e0b200c182c038200980a00201c3e0b030b00a500384190903c0070203900d400004c61000c0e45c0c40085803545070240080003142c0041c07801034081e100c203001d041e209000d104001515401c1511999215080c580d8030145001e190002c02c16050b44c0307882c1c01203200b42d02c81000703c0130106114000c00c002d09002e0000d0105200101000300342070400380407244641903c02080450381c0d0b0260540c2d8050710324a0403201c112500b440071800912510031107050f94024110002181d80810010704a4281c55074018084c2d6a102e5004988900071010446180d610080d504404030307216038410309152034103 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 76433994 1250 76432744 76432747
    0x6071d131b09080f0c010e011110061e050409030905010804140312060306070e060306100e030114070206070c0308040b07030f150f060503010305030f1c060e16080405150705 76
    0x15221001c0c00210380260710008260551003c100944040198000f0084044003600389040f1003c0001c01c050f00d000300107810400d840e0018501503809000c2c0c01551348001d4000c1003081d41c0c801200c1c2c0c6200c0f244000a00c0780f4160900050242064014183d00507415914101540d040c20019640302001138820384504041c076050070f0300d100c804c00040c26440e5014800c007489250140070076281c03190007000c110030080046007042d4151180030507660030403001c0f10607a000041c07000e011244d1038801c00100d5810741c00c000060220b40c0940c5020390040301d860703023907a8466450000c02e41714515007160040002d404880014082401310400907003003c0185800b00d4000c043c0c100c0c072410f49e140b07034241c0d070403400c032000d4104445100b0103030703840041031241040c1e0f0442d8035548425440e40100a96800d40d00000665411038000c52500c00c40130714500781c4c003040000e48400150308808001c0724406003d12001803560718450084040522a80d03018009104d40d402135000d1540c0081c0142803801400700 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 76435244 1250 76433994 76434011
    0xb090a0e0c1c080a0909090b01140d0c0b1e0d02070303060e10030201050703050d020a020d081605040e061c120305130b061207050a03030c1502030c03070c02130203070c0506071d13 79
    0x1c600450001c1c6003d08515100ca5052008010310b42c40c0c40b80ad0365100e043c404544100040c4651144811146005c880f40d40f503015a100d41200f0448455102c41d0401c000038000c01135034065409441214007039901040b1140d104c80301b40540e8042903880c44001b01c5c0c10501000150720400040111602c42e1811034100001c500058083e43c001140d0390001d42c0110751071034501940100b0700366020340c0100b5864000744112402800900c80c030f0140a5140c01c5200c0010b030242c8540c0e0307281c811421a4114102c00096505100d0268220003001c00b0000f414000401c0a070074100b00700700050780c0c106030942801d0321640f0800c04d10b4040c19001554901920000080c6a900e60310700f040154000c1c0c03183c20142c2c40c0d0307181810b400b03203401004000f8070348103206001c003101c1d03910242c070707404020703420203133400d2065000040e05060b0205200c1002c0d030000081048084d0b02680d4030032041d20400498845454500081d0307652680d505280314118a9882d0030718051508210341c0e402d03040600740c0091043d8 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 76436494 1250 76435244 76435259
    0x7030212030304110609010f0c0507030b1f080106050a360204030302160e01031203060905070509010f0207050f040f020409060306021306030b0901030303020c010b090a0e0c1c080a09 80
    0x188110800030160000720410040c8101d45000e00042041110058603249160001a080001c456000360400508031030f1002000010000c143c05141c01800c0d0340040c0c508002c00c03d0394441115401001a260342c580001c0d40501400f43c0001d98030000c140000903402d110ba07621001540c01b003140ba510700c64886d0800690807500c1141c1d1440345100002d03030307200c1c11410043d14200030030941166180303941e0300c104050413110390740505480e8800c03c0040354507003141e400c9014041d00e421040300c407813500b400d00400d90380141c0140100c00d402e032940030781114140c80507625004180329850304000703c0659001c9519140d40422503100c00d9283c010b08281c0c4a149450440e0f17615001190f140307500154544401c480c1001280061103689000c0c0b0480b000c2c540822441c2c030041c0b0008050540100f4014075105082d007002d0b00c0000050039441039803a01000e1381c0302402c8040d1000303105003e624000006405c192400d1444006801071030204d5111541c0c400c1c041e41e102d00d540004100d040f84000c103004 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 76437744 1250 76436494 76436509
    0x4080d14090406080105010929100513060305040b01050103090b0604020a02030705010e071d010b250204091a07140306060702180106030203190c12051005031f0b030604031e02070302 80
    0x38000130000040039814110814100c0b0807134688400e2000c2c10998a000d5025600c40c0500d0296054400310545043e010003654140680900346600701341c00c0b48007103a4a0b5240e031010340314170f01440241055990392401581100c22100000d005410f07074400180c81da0415400030080c55000f84100d91414440d900d6160854121545100e900d030440103041201c20000c20300310802010b41c49083d1010f500d4000d5070700d014855104100030038000e0b10760590f0014200c2e9404e00301ca0303401400034041c2c403005250668000c83d03070800c00c0c1d180b040c49101040341588101185451000c0072070010746075459401c1000b00d1a00601c5e800c984c0310031502c41c00220071904851540c02000951000358403401c01d1418284040000403d9889442c98143c52107100c0d50300074981d0081e44411310000510b070301c0e6241d128142d0340e40c80d04120740622600c0000c40c0540d8280070ba42c0c0503034800c000200005075003c030805803942c074240d90160024800c000986a070a0710340484000d08030950048a400e15900c0d0302250b0320 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 76438850 1106 76437744 76437749
    0x3060e06040b060a0e0105162103050601140304081b030a020129060309010b10020f010f06030c1a040906090b1c030912110d050c030d020304080d14090406 68
    0x1d64000c504644a0381c2c1750f000040348c030303884504000c901c20780300c06003030022116488101d0031810301c244201405000160364887c0d05032140d032076030401340e04060400d83e41d04d5001c0000c00d031003000251002200c01c01c40c801840d1107a0f623014019084a102c03101c03450354120003441007411901d0b031051852200504954007034132900d55441e92801443c1103050542c1040c440408101340c182c0000da5644680003c800900042500086804c1034a0080c8001002c2c44418001070054100c0b01003c00301d505020200241020b588051140540f00103910207601c09030b0b60002c080c22414510010a0305517a10400541f9515071541c00409420261080c1c42c070b1584103004010401c40f216000f50401e00c0e00800c1c0d10402400c606010b51500d420010752482440b611040b105080d00120680d8215070440d8081c0421410503101910081040442a00c9900301002400340a6980f807080901 = true := by decide +kernel

theorem cover : BRFrame.Cov 76258994 76438850 := by
  have h0 := BRFrame.cov_init 76258994
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76258994 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 76258994 ≤ n) (h2 : n < 76438850) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
