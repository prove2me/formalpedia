-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4774
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:41:21.414252+00:00
-- url     : https://prove2.me/submissions/c621990a-1d18-482e-b875-f19d714b8754

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 858453237 ≤ n < 858633093 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 858454487 1250 858453237 858453241
    0x5090a2003011113210c17010c0504050607080d0f24170606010c05010e01060b0429031605160804170304060504120f020d080405030c0d0206070b091c02070f0527 71
    0x305075800402800c1c2d009455011007d444203500d5110b0400e485a80146618203c95212000d00c40c9041d0303800d4a200620702e52400105488805498001c040d44000140c2c0d60003605001c4005c1d07115003020a140784001e1a14800500d2810b800241c41e54010000c00920244c40042c1c000c0c08185550301c804242003040345541d1070f0405c80d0041c203802c0d004190541ca81480410f0301070320003000d403040703c1240d03040c9201d0114200300000d078060700c001c528084030418004644080203083c801c8421102900d07040f81010a00b03556080c01e4800381005480c3d10000060501c1100c1080c01c4003981403000c0c5000350724183c1f03003007402030280c8200d05c2040c50000801d0012000c01052440e004102c0313400130301d194031101280c2400f10140d0b0241c4901482881240c0300d1503018104074010002058008001c6d0381842102d445107101c840300100750044600400d02200031207880d5003a0440000101c0e401000c0090800303c400e00c0100d90350f08214031540d0b8882c516512500d40c10102d42541b0200400d11040d9 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 858455737 1250 858454487 858454529
    0xa050d050f10091e270503090a05060a0c06022d0a080f0405061f0b0a02010e01060503010c021f060b070308040201030605040b060307030911030d050c070b13030605090a2003011113 79
    0x80c21800c5c4902640e02d4038140c3d10002e0010000c00752401150448040040d01d07550720402c10944502d8603100f0105080500460100707045501a1803100c01c100090100c185411030540a110214006070804031300102d4100f40150703110250a42c000300c02041e0755000d042544132959545001082c61145806e13041c641e02d08641c0c00000b540061814911245c0c4070420000080d0203080b505101d9140340d0318100c4005014941400351030380c1e00410f41c02405401d403846054686500d0900c04480301552204000100880c000d4003c1c0700303070350003503079260744d6401c10b44001001c7d02c180350b0056200d40d04200c03031441142d81d004203e80e006002d0b402c0000b0b041d0303c1490030728643c060003403081e607041c0558a451030f5403c0e00003004180440800d41070703590503511844075428500884811803d001001a02400055041d0380881c0c0c200ea035840c1103030181c0b00c0030ba491900c584642020f018500c071012040503010f0a090081c00c4550218112150074005004150040303011184140c2410800708040e40d910 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 858456987 1250 858455737 858455771
    0x609010b0d0c120f020a120506091b13060b030702072d0603022101120c15090b071e06020c15010501020d0f0908031612030605010507080a050d050f10091e 68
    0xb50b11350103840e0940d1b9666545110001c080c0200d000e40b214004d031000140181404a0280c3c0d081c09100381700c980d1184032405002c042641050741402c5265190008680180124042c51280e0501d40c002d0050500303298a2030152100442495140f07010062200d55000441940c68165890f40ca00140c4455200101c0c48070108400c02c3c102d82c0b030b013009002088429100002d4452070b13004502404d82c8c16507a001004452051508410025410000500903400c4020090400310701401121a02c44103030031100e62140e6080d00d04a44a50380029140e2860905121000c492854009038008942c50200080d403100b509000e00d608101100c09102d445900445040b000b800f1001e040b280c07a81160002c000e486c128030507099603c0020000c1d98100b492207070084805681045e5a074078101405a0b8582e8a83d8006011010500006101e1101d5200e400d10400c0c1c1720300144058250340703007000048005140120f40005250300d0805000052080000164529804200314005011003070503201c048 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 858458237 1250 858456987 858457013
    0x40206160b010632031003060c0309031116171204080a0204140405100203180a1a151e060c1506010f08040f0605061f020609010b0d0c12 60
    0x2101030308540c540424400306244803030584549441d80c000c1402a0901d60b20b04007611402808202d410b00100d00c1581401005150010504c10603a03400640b2952000141c0e00c04080200019548140400c00d0503444802c1c01100c03100c0202501401c6001803030b81c4600c82c41350003041e0304031121110000030000100a00784448000354181c03900d560b2580032031500d031030401805074031503410b141803142c00518041d04140940e0717015004114103041d440d150380294200415410005c615110301480e1154184204c50f0305900c56178141c410559162410300007041e001d80203400c6e2880318011051a6143c11042801c80d60203c0511408501c80b074001494034402c030f0581001070301940521810388808001f03100c0c01001c090300c0d07104481c0c450090885403140116400780002e08500384100108060342d1000780c2041025140d00750a02c030400354007aa001c078500444006921602c1085200301c000c4c4039261410b0b8044510220441d411f898102c0340035024011000100300c1410301108102803452902 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 858459487 1250 858458237 858458257
    0xd0f02032d06161d12010903050304150c08010e0405030d06080a02040e0c0d031110021309110304082208070807080f0102040807030b0c0403061b080601171b07150b100e06040905040206 81
    0x11080e441f079803030b0003421074005440448145580d42400d26081c401782c0510103c9005580d5591380c00da10301800401c0044010b04247c5050108000c548111480c0f40195005003010701d0082c05103610a1042c001242d10840144031141c020340c09101d06640e454000c400f45981515100d40382161102525041903c3c8c0101294103501c00034400e0070f207003020b010460855200f5441000194010544810035120480300205050ba080003000d15000b0540e4140d100850b552145410316034030340792541d00d4649076400600c06a80042410803921030104003280d02040d040000717504087c901507040340d641c0300500005201405c0326000400c0840010709a50086070061024460320744d05002c041980c1091180307001c000384078400080c40d01d50080121041a4180901d8071180b1340e5011041150310b01c40107045c0490707440802030003001c951000f1440220040003940009c0c1d8840314410011204d040d950010103201041c086007a99594000c1a681103034120070000c10039a489200103070040c0304180200c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 858460737 1250 858459487 858459491
    0xc0a0833010f051f051c090c06110c0a0302060a140d09060603021305190c030f050405030c01060512031c020712022107020d0f02032d06161d1201 64
    0xd0602c02010005044030402e440321110896181812540007001c104100042a003c01011013580d50003501c62840301a012030000303843e8580e42e100302d01c1558540c82000010414002e500d1003003010b00c42c85030a20004c03105041464a10b6002c11654040c2c0c43c1480240620324407000c01c80b9104a00321a64591035000410928409161130310080c050307800103a0040103d945c000303501c1b030301511400380510310b000c10300d0081c2e1003034031010030191800700040d8003055111030300c0d841c81503200d01596024a00c1000516100d900c440c2200f030850700c1d0fa0384014410051140c107400c1100001c01200c0d0071005c00340c030187d0001130051503000a4800c4520040c1aa90b07a8152555155408a0a66148940c24880b041c0720600c3c0a100c04d000d0080c04800703984100d159601b4000510022003188278075101034181c6200e861080050040802c40b01b0085003405020700310b03103010303c40c2800002c1d804080c560548400171303c0240002c0004425244041c481c054464151000c0e60318506038000300c10140c402 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 858461987 1250 858460737 858460739
    0x2030a02270103030f080f0603032703030d1e140c0717070803190e071205010b0a080a0506130f03110a080d0614100503062b03110c0a083301 62
    0x4024000c41c40e0000d0400020b843d00c6c0411840c00c001c0d00241d024400060045090040307201410b9001141188080400581000001e4507900c05101414442c140200300007164803061418002000080750020b01c00c52506140c100403210309050310390001e28404c4070640b688524a44035400000c0d0f404012008100419000100701183c002107125040c0c038401e0501e00e10100c1d403c00113503501e041180845030820102801890b04146010504c18054000401d200e1545000702e00723078a4103500142c103180c02290300001405003c110440d041410400145a00081501e0703c100c09264140c0003020484621000c50508208018602215400c840e01d0340c0e90312503910355680101b0403440707420b1038a01f00d81c24150303952801040810340102c450300c51628640d81c1408011806005904615044140075038450030103005440d601e4246110762900803107100da0418551400d40042c1c0b040d44903900b144014002140d000c44c0400303081102600d90740c08216000001030350105031201e00c120002c03c82300 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 858463237 1250 858461987 858461993
    0x2031b150a0b03010b220c0315090c021b01080109020a0512090309310e0f07030503030a0623060a020c0405130311030f0306190302061207090801020702030a02270103 73
    0x403200c0d0301c2c15403c030001c20411000105002c105003142508000800c2d0340c41c080d00b40d0008580240709010020703e00081c025012500e022040541038011140f21507461034111045501004011084a80c406018095038800c1000800c81c09050042094503600850f6141ea1503005000b510074141c5402825002450805404e036906d03007007081c6130b40c8100000364081d2032030304615141541a100801c0040c14040c0028102c101038044140055001c2c07040841c3d103514650140300e1000074501c90070145d542c1c0e040106035002611031035040300590158412030f1801c142c1a80d902400c0c240c4003030320f1050301d4443c00b46059080000900b58150040d0904041141d00c04c5003c90307800581e803094403131003030000400c031445035a40145148800b00240c10008541e403071030300d1165079007042011800c1110302d42d220f45c0854542e812440d0410b0348202882c0038800b9940d084012a4043c10b0440021410b01d400f80c0c00103940e80d5140307007001c5e00418155841d008006404842c10f2420690401c1c151100d583d41c0c6 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 858464487 1250 858463237 858463241
    0x31104022b06120b0a0203060d0b07031a01030b0f0f1318170906031503030d0243020f060c0703051b090106090618030c06030c09090c02031b150a 64
    0x448901407903464007502080365103004004411032074000c44409469510012940000d500282c00c1541c0504000c08100c00148810682c074801c08640d82c020401d10808010705603110074512000b818142049804c91041d1a2142d848082c07103003c4510400325540d4602080120b40d43c40e104160355400c115600c48400070217620084603a1003289000030042103a60150546e02031445c0f0a0750010080000c54290004064a031002440082c15203207440111b803148000c90f0300034114200c80b40d00740380d0300805d5414144502ca440481604075401c00040411801500d8201c0c3c00780203104543c0303e008042c1d21785840080d103d112110704100d8034210749070b0414075074805c2c840038000700341d8080b240804000e05040d43c40074100c40d40c6480b003641d0603041140666149010a00760840311860010000200740820131540081a481d2000a2030900e2600002c0c0304603005c4e00405c010a0500c1a024056070740001180d503c0c015815001481f1800721040e6405d03e66160f250284409a84060046407503081e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 858465737 1250 858464487 858464557
    0x6132f041a0a08070509010b0c01020c0316120207050303031807170106030203210318011407030501060e010801031e03020709020c060609090c0109030b070c202803110402 75
    0x1111440b100b143d0b40e5545a65502c428003503550403800c0c120041044012a801411007110705800141c10503000004591941e0041004201c16003862014007003400034151a051282c3c40d40e2000d0700d00c0710b06000100e5602d01c070241991580b03822482c0d0f600c01e0070009000060243c0a104811060104065500c0740603004d1804207a00c039007c0d040c450140c5601c100c0092030843e281d00c0b40345080d9031302d1180100c460508543c445620395214690008400308092466205843d29140042d9950500c0070003040f030440e501485040c80015030040c404034516006000300c3c081055142d169604080c03508074100151503001032405800803038092103040010460900c1003c0550b540d00c2c19a40d15910366594481902c0240d001c5114400e060006c911844192903001c103681c207011140d460300360f484d2207408000c21f07400440b1241b1014031a1003458080100e52641381c40510701904101c1d0800d03109000f0382d0600c0002c09a55101001d101e960b100da8040d950080074080940ad51100d98020390801c08940c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 858466987 1250 858465737 858465739
    0x60f01090f0b0d050f150f151b0d050f0405040515060301240f05030f220f0b07021c0c030c06050f15151e0f03090d0206132f041a 57
    0x24600010b62130a0741c1c211503841a0306c40072071021544504420f0181424030b803802103070440f1820000d04d1100f490304004000203e141500704000c403032200c0c11075041c0405000b5130020030108201202c0324100610540301a950100c400040f1600c0b6a40c0d54140a800700180c2a00a5800720000500c030a40444100a00d400c2d08000c9002d440f00e1501103c44d0080c41800313602103407081c004910401d60043e4110b6124004648003440248101c0d065890380c500a08100d42084009802e4010803050712900c60304603000f40010181c00380414445580c10318000280c00420410103840003c1c5072252020b00b40341500180d080043e03050940558489410031940040c0000d80c84017504810f00307000b80c21040c1906a02285030800b0380b680024035846041307001d00c80080d0b030305002c40c40c0f0700c036100002540520490790003010308140e0004040d043ca0001003020b2000040d0400401c00f003000041211003c20700d9060003030444c41d90b01840e4000304c040400040e005490160350800b0451029400c0c911844 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 858468237 1250 858466987 858466991
    0x30503040611090d080c0f1b130515280f05030d080103030813150608010209130e0d080711070312121e0b0a03060c030b04050a050609060f01090f0b0d 66
    0xa0101980c085481460300c3c507a0004c0d042060040402c10f000082d040106810060720803151a4034400c40ca458003c0303025604601401d0042c038010b26286014060315030100318140300301e10f0440e502011140515507072600070881840303050040400f040c10041c02d082e5000420001d15110301110920700d015028040c007a11400005021300c9001d1802d00e412298150350b8450f055561041000007903880d220100ca403070300c0078a203500032618580568005859003a00040c0c03209a1901048400901d207061286041d142c07071000200014085a0301c003614105090415a6485056044403850b200352000207143c0101140881000110071038260b00708140e54809901c0301120144030102e5142d40011600302c0001000b017452101150030111403038a000f440c901c4904e5580d210303002600d44d0f0304c140f0000280d41c3d40342c40e10103242c41c0c03040c69004061054104035a1800798007207800002c0c003603c01c1d440703001d0010210b0016840b80e2650b82c09030540007c1d200409075250000a070301d070451640505e5140c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 858469487 1250 858468237 858468251
    0x3180f080d090e13030e030307020405090c09011a0906030c160f03033c020c032214030a0b0c04081f05060d0309091a090702160e07140d090f0305030406 67
    0x180300c1c4035110300844c9000301c88801401540c0d030070380b614038076070301d005030940030510084000d030f03942e445011300c50415640503209004000d400c100081005800800c85000341e11112416404003200b80c0d80b500000340d40300c6940b516120300c481094011b45100b009944005504070742000000f4003050203443c401c2d04d0611030300c2000510520984208540e003003240c40210035184146662903219459021600c400500c4c01980100050455204440c030840c0884c2603120769180a42020f4440c0003848a29108404c0c0b240440c0000d444406040f005410036074020040340400c07140b5404c0b20000e0004404440a0300010f6403008102030b04150016081d074a0000000c80b1424050300d414521740c0e05988441c4d140303007410b40c110000c0103030441d010800e4980c2c0034000d44035240e503440203004160175001003030414682c5c3d0340c08203060b00300d400031300390001101c041c04000340e08081d0614441c0248001940c8a41900f0800401010408030180c042ca00d0f24461a051540060045000c2c90050300c5c280072030 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 858470737 1250 858469487 858469499
    0x1b030c0601090b1e1302120106180b03060d1a0a090c050306040305030606030432161a220308120906161b0209090123060d03180f080d09 60
    0x7103010f050195082200e6203203140d494080c3e034607000d0300380b08028140c0400c00c940031080383c00c0341c0080c550002d2007046580140442030700218a103100b00750451503250001c2c2811941c0c55103000242499001d01c215400030710070410240040b941047c03050318403241d40d00c0c0002d0340c1c030040c000d0700c036003030368140c00300c1401203200c1c14082011849550075455941c9036803220303014803925074001401556214a0941c0a4944505000c50084070107500c032002e40e0b0043d0100b198500b0580c1244c40390354240c0113110304104552200c50813041c1c40c0c11240030350f61140c0d00724403410452818400011141109503002100304042c0401900b099020000d024181d903807140c2883d80e407180146c5a0719040700403c018031106511680d54a0301c40d110b0340d245030007428050790115580e0603051340d480805944409078020841030a8001010f22400408040100d0070008080b900d07000f848280030341004411083d094810500c44103040041c1807620800d4a00d65460b591540c50780092074841d80028404d03400002c2c4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 858471987 1250 858470737 858470741
    0x906030b0607050d0e010c0c0806060f06070221031c0204140102030406020c0607080c0a0b0a1b231603050405040b0a14040e07091103040507060f02030d02030a021b030c060109 77
    0x2030742d944800280540308004078280c40b0400c10304413403410445100120000114502e0900c0c0040c86200000c4c400c0e070400030308220f0b444208048040c0901410302c4201c4c090780d40c02207084400e00104416041c2149814001c6080d440b43d001500b10000c0c030f41d2140400d1403001d43c010300441c0d14000f8980307084415180120707200c0c42144a010300690055081643d6031030880000d01c0c4c018414901107140c0700001d0016420300d004d159050b200c44c4013000c00c200c450803003130260f00411050000d410750a542c0180002e041042c24000d410642111003501e10195072071103086842080c1c05600300c00c00101946002030641e441401001c1c001c50410700f0400f102d08006400b842540e40d00c42140c080d07403040c41d0601c801845181041c40c81c3d489116000034140126118601c818110030750540e6403442c2c182416443c00e21158021020003440700c409010035035020043e144a05907000b40582d40f512004d5040010340140903210001c00e1303048442d907050040000040c00390503c050b06603240c0d6070340c6185e1081 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 858473237 1250 858471987 858471997
    0x12040b07080705030a1503120804030e030610060c02030309031203090d02120403140a06060f090e0f06160c02030304060c030201241e0306110406140f04030609150c0906030b06 77
    0x2140f000c2c07011030005640341e004030004004d043c8056110f560790b42c0742e42c0c031080c00550b01d500100318040c050009040d4427082e001c074600c00903001031980f41031034252031102212501c00e440c00c22804039180011540e0903c100c5031000b600404a131007146042501801d26030065a4070680b81c860707a04841c0c1e60358008500400b44e810400e6045091504e5511900d0811034070700a04416809801a040000341d5948a2000070b89240b440c0e402080707060800c2003084500d0001038040c0c5500032060513401100000b0a0741d400f07901d668000030300d81040c090903070f00c00c2007040000754140008074020880b590703c0f62180c103545019038001e000000080e500802c0701807801c0ca82c245092230b9440207000c058606503801019a400e107044020b00d40d9691500c41c01c6a10421071000d060750001010400141d2001d2813524402940c80c01e1072a040f04c049014895200c0d5202c000d0040c0d4484540b001880044404080c0c00e4a030385209104140e81540001e140320010700560011a00d05143c152050500000340c403 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 858474487 1250 858473237 858473251
    0x6150c03090e0a020d0e010b180412030213080105040515070309030233010801090308100f121401020c2b081b0c0d0203030604110c060a0c031112040b0708 68
    0x404902e041120484400e000282000400c036000c101c10000c20406201d5171188007018000003a447c00500b0400002107044421050307440c60b01c0c020300000c40c45272900b048852203c0d040042c1c0d11282d0402d041c0320300741d450303100070115440d24080200f40324002c10366071035001603e02100069501c4207015022550f86000140050b03000c0749901f40d58206080d03801c0d040ea41d081e0002480c40000c0004000ca0002c2600700901c0c60751100141010150030110144c1c2202c8109202c203089818404c00500001c018441c1c120f16402c030a0044007400b150160a1701000c000200a40d610350340c0481d01590b17804c2599115a8810060303a0540c20815082e80c05c0003c140640e64200d580e40b500c4117884030415001c40052071a110411021078084410020000551341d41d4002e07684030b18184041100b195000b20485030030070301c10001d41d0004800819011f9000110190020340001c01c0d46080b00140aa046526905400090300f07210350420398a00030f208078899a1858001e42d14003034201d07003160007603a4030 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 858475737 1250 858474487 858474497
    0x308060a09091a040c08070b0d110301080613080708030c03090708010c0f0507021c0b0106030b150922060b04030b060409030f0c110a0e0108100606051c0f020d06150c03 74
    0x40440443d4400c090700240921a4842d0281d100c03102d80d4203050440d4812010300000280c0c88070510b030742e03006080c1d0b00d290100074941158584005191200c00060100c4030080d49294144108000030301a0344000f50407000441e2a41f40c00c048200c000d42c8241c030990003030b100d86a80050046414001c9040045250740c882040002080003034426810498080340e000321888042c1e100c60f10110b11504685010f0440d4800551511300043c0031500d694102a0103010250040341d8401108011900c1d21181980c298116000d074400841426080707003101d003034a90400c81c0010712031040c01c001d001924011034080d8a2070300c2c1d944c108001c450700481c00601159502003888440c80c05014261000c0c1e0142403500c6e4862072410003d00003441c280c010800e1840c14030300500907403904000312080b01c41202420070400341401c0740503056000c0c0303448d110000710034400000711b0881a50414031140400007003d64549010f070714420090181c500400000d0b052501280385982c1c40703000c1885810f505134450b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 858476987 1250 858475737 858475763
    0xe01140a03111201060b03040f120e06040510111c030b030a02090114030708030a1806080402031b0a0f121208010b0a0f0e090f07121104120203190308060a0909 70
    0x148100c00e40030508803c2e16550710300d0005840d1125100652144d449000307039140c24100c070b1a00030603114424045d0804c02c82440c294000e1900d4100031103094820071106000c20070354400381200d00c0c1070240001c0c8601e0060019003440c151400d80923038440c1c41143c0b02840b03251901e03414190f84060782d55019600c03582d108010030256440c0c0000d21070782400601a5117191b40c49103103c5145612400c004000250b09074181c003681c0c2a007100a60180849240c1400076003040d80010780d440306062038007920009c8011a00d040f681d1070000c03050044c007000b0320f0010655130780d05200301000b410b24000c6d03400110031500208610701c950200f030705840d00c001e00310b0b04000303400300101c88410402240f50b06010640c1d690400da9030340c40b0f01c45d62050100d0b0714550b400d4548001c1c021700c540c007008000c401041c140408020142e5040007075134140c0e04e001c55080f440b0a09400028a040c500f80303c03101036034003170300301150602d80d0040da260b210303010549500c114103540c0c41059046804482c0040d0801050030b007 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 858478237 1250 858476987 858476989
    0x3020f0906090a080d081f062007081e0d0f020307060e013905030601020705010c0f020d0506090d02031e03060a03020603090d0224070c05010f02040e01140a0311 71
    0x10b890b40300e0b8080c040c0d011050701c80300c2840c41c00031400d0500000ca0718140c04c20954034016a41c03441800200004910141d20384180900707011035440a008061640130110300e1003102c20803d0030010320000301103540c41c40c010b2060080b0755581010112a81c01510b601c6c02c1c00e035000d40107141c0306800a0340214901800c81e1180703001055920003402e095501d41002c98044900d0401e00c00800503d40c8250460710030808410500040000341401400410b100f00b007041da0300410b081003180c20a0070140d0398401c0c5071030308013035000300180000c1d40a801c0d42140e000307200002a420303100d8100042210780c007a00c84c0318181d0b640c0c00784504508806052601c50002c80d0f030709402440d003022000c1c0032120000c1d1654005003503508102c5104140ea441807618400c4940d0421140e595407001040700c0e5214082504040364440f40100400e00384400290084100802540030303070381d209c11a0400f1034456441e200001c108000030301c100785c0264080070419105180050798107003100d602c05d140d403002d079034890 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 858479487 1250 858478237 858478249
    0x601060c11060a03020a031407051902120a0906021501032310060801200708040b160602130f090219030e031201032303040f2310120c03020f09 63
    0x24000c90310103540d00c1d41d900a9072101009000e005030709031400740e102c0144140050444800900c40d0181e11040403e00c030446170130400b114055034a1079808100070b030903250141c0c9440b009001c02c0d141400b0004100d040039034400c0020045d51107603400d440f00c04850100440d02030000707000142090250f003a0011141040b52030920020045e070040d182d1010b41034400008035003465000b440541d44802d001d503111a070800045e5100c801c5c00c581d1a0504c4d0140d105c06d0498001d500800d00302e5640000c001200c084440c0203142100c3d4480c409540e1900489604843c0394070900c980441c241d50110082040c61143c000e560b0140f0f0300080401049110710030440c09080c00402c01c5400b404100840314400c03521254003030182d4010400303844140d50310345d00458442d1460303000c040c10b90020f22043c4111a1154245402c030f03013200a00c03045800c030303103107a25034040c01d4840103640c03003010343c82c085801c0c0f80c00110740650046e0241040000309035016069050f03100307044201041030b000300105940e5181078 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 858480737 1250 858479487 858479507
    0x2c13060c0f0203250b040311010b040903140901051201080a0605250f05040b0a1e0e06030f0714070302011e18020d05010f020f130803040b030109050a15140109050d020102060106 78
    0x1030444c1c5001d040a42c80b4440840400d0302c0c280d0020f2002c0c030560071110000d00600100c9201940c040000030700c9524000e00800f041008a090501d00003900c8032140c2c032035010b86c0e4411044c0c102480003543d60b0b003a240d9440000540c11584981018001101404003407480d01c0050b041c000c0200c2c0994407104111400d55082c80c1090074444c05200c0440c000c034a50003d014920744540715007105013a0300301c00c0384008154044100030021031642105040d10f13954290398021900d4403074039585d51a088170a030303519505424030b010810400308032402450b80c150403c9030840c0400d041d0440c104c2c654410383c020396800d05000740851110340888030042c2440c150407080507000e030000054812404884909a13031002c2c090103901e44011070300404100044030103000910380d550007145082e150602448007400140300d4030b0f80d400c0d038074800111000200c0d008000c285444e40e881440d12919803154642000c0003142450000d000c1d0b14008c1010f0500441809880307805030000c14541c0e1a0407000c0b90321203e6 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 858481987 1250 858480737 858480787
    0x607080d0603140309040e0d2003280818120c0a0b090601080607390b0901020d06140d111c0f060c020102132c13060c0f0203 55
    0x1c0c03910300001240c4030405051001d01000065035542031a001008141ca50026007200a5001111501e46194000c4600b908010040005581651909a41c0d50842c022050315480c454031111f61500781d035054001600704802c05880d40d6400da03c409602d2030310000119982c2d0b00550228001e51900c0740b810020b00424046582203030340001082da02d0b1040072030159110f8445600050051104000500440303500180320300c1c2540103666500851240da2004401045884000d00c1000040801c0501124000e540181c5a1800d6092006240b8000e41c4195000e0101a1500341c0116103c14507070201c500000004011006031480b80e200d034041c954101c00101d5014006180700380060b05841031501e0018024070038400c0100e0b66080c401c00751a00040c0b41c8003164030410420304e40c070620040010030f4844810b02800c0580d9604808007110a09000310404160100104503a05201001120070507109103c14462040146015202040c0c17211888003d40c02c20b00401c47c0c030140c010321744012044 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 858483237 1250 858481987 858481991
    0xe06060a09020c19060e060f0f060f1201020a110c010f0903020906011709030306040c17070c021504090605040f02070839010207020405100f05060c0c0301060b0c0f0c0607080d 77
    0x184000340e8011203540d0302c4e81121225260398a0580008051041c1913018140040c05006880c1003180c819000e0401000240700e168242001040d0b078850040f41e24843c0c048400840d0b07140c0103580b0203020000310441c00c166520404034144119445540d500c00c0f25102c2d9180c0000150565017040040c0100030701301410000803c07404506103904c026401c0c00780314020042d55030707420181e00340025134030101e02000501016502c0e0031800b4842100c000e900c01e6036481c24803c3c0601920000d0700041c42c3c111442000d250100d0b01050001c1039500c9017040740c04c208d400700048822445101c040c1e02407080c0c0035003881014442c0340ba80b007444c8000c4201d4015982c410f41d03101d8030046040c460640300020700000703581d030208040d03046085c2441065009010b00d403502c00701c54989510006240c41c54002c6501400000c911000030700000c204511401e88014020704c41c840c1c445540241c15000b49080c04040d20502021a4205602140419a5100182100d442d019082e01c1d41a40e542c00b4807007141d5070503 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 858484487 1250 858483237 858483253
    0x30a020a150e010908030a06050603191d0610080f07080d0815040f05010504050a1a04020703021005090f100608071521200c0c010e150301090603060e06060a09020c 72
    0xb082c030901010728807034524140c0384d0400ea00d050b011a403050b00f110380605000c0003800032000590128108882400501081ca20341084024000030074011b40c805240c8039103410b100c808910300c0300c000305894000c412100401c2c4a503d1143c0d89810511958007160002002d183d542c07442503130000e0340300783c3d2202404211a00c9030045001c440d1148004800d0320390340ca005108a29141c01a180c00951003030041c0034510803180811103200400e039516121f5640098150704040c000c0c0704403080c190048404000c60301d01809599100e18007051040c01d40d0180c02c2400302e030103015125010950301c0060040148505002d0608512021604110f045c4208410824100b0105522040800654540101c1d110a141c600f14004071080110118200c000380490361400200040250b204102440c1100160b92940c0100394070300c020350654464840c000001007010700860308034000f00c0744940070070412402c50030303941c603101c080c10341d02140d02180d90842008500100e80281c8a9040508140c0e6204 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 858485737 1250 858484487 858484511
    0xc081207170c09010305071110150b040e16050c060423030c07031b050303031906050d0303050f06010f0e010c1502040f051201050103081207031407120509030a020a15 73
    0x1d044121482a2402d000050155844d40d2501030b481d008882810310740d4001211076052070b02c03580d80540070b8100c6070b901c00304284110390100c0c00d00c1c020000342c208959101d441d1000c00d2000d5508032060750308a00e8030005480582e110b03404407030344402c18030058602078035255201209121081c102030b103c480e088585c4141d0b00401d200401b691080c0c20020041a441e520741032401054084d400408801d80f01410487c5803000300407607a110840754207480d08001c2e06868900100540d0704403a4222485168034000c041e0554003c50203100905c1d0344003001d030f80300d100454100d001900740e8030000740c0024a60704194080c04010403014802c440307002804005540c0c0404030f0b04983c0c02482c800a00707040030401410400c618002040f8204020b000640c15502c0e0303080e0700d225510300c08030300092880000301e28901c25402005504c200d4103005042c2c0c1000840181005100e68a074480c840c6400c01103502c0c483c00008443c562a072940181c42e44003841d403a113500c011441e0340200b03034442d01c40c20420300e1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 858486987 1250 858485737 858485777
    0x9050f070f083003090c01080c0c100203060406031b060318080904021602090c0417030415050a030e0a0807020913020f101b03020706090e04030504050d1e050309100c081207 76
    0x40303041c2c0c030307170081c0041d00d510000100002c40140c00003490801c10040d02c0c0344c2110109001c481107000c2040507a69496040105004105950ac00740c045090651100140481c9003a40c0c4100d0340299000d0000048240e00004d44d0303c030246000300131003810041805282055006001e60103c1e05101000072012500402c0344010110346955092000140601c5040c580c84c54011400f20a10000c0d0308050a083d0020303401c0c0e10300c40701d52042c020040f41d5400031718802d8101d4565840300e0390544050544a140c16511504006070480c80342107840002501182803c3c06240200d40040001007801852428018015408100c80081041500c02d5041d085215007107941494402e0380140000e82c0390002c01880f500281d0004039003549802e05110201c1e902a09440035994110b035900d030018030600c2c0c03030344201030051411400300e20010aa90180600480649520941500c41c80703d001e003000400c07039841580e50740c001d050700d0f03041c444c003984030050282c01544080107040103c01082c034002d009d42 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 858488237 1250 858486987 858486991
    0x1d0301090809031605030c19150504150e090117012909070813061109030a051e03070c140a081c140a1d06090409050f070f083003 57
    0x81c01c000000e1000640e050070040403050050718000c03050304030308020000b80c071a20890700c818820f807080b1b51002c100d1440a60000700502010045038641181e08802404981080c418684019841d40e070490078107003c2d041da01004280100302007956820450503c54007070700c11020b04602d650301c1c410a007606409002c2592881c0000d021252080c441e6010031541d00700c010410030422800d9414040c43d58000992080c4481d40490041240c980c06d900941c51409400c2d031340d6600d44144080c1201740100401c003005058212250084244514181a6640d100d0094002c0000401b070004000d41000307110322004124004201c0c02c52141d49910141c5014541c10a040010102e00c002d01c003920b802c21924600e10102150342ca0800b00052006401c200c4210710116003000004095000e036074030380c000c49a204000400c108014000c600f801ca0f90390390302001e2030325188140000401c0a036400101ca00440d40044020180c0c05103018001d505503007140207900c260080d805045546074101e50140d4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 858489487 1250 858488237 858488243
    0xf0201020f040b07020a0503010e030d0e2d010c0206160c08070c0314010605030a030e061b071d011202030706230403060504110f01052209050708010806010609060f1d030109 76
    0x113602c9101e58010040c07280c0c3c80f64801e600c640e24200340c031045072101005441241e50780c004000303030046030782100ca401c00942c0c3c02401d41c46003d084003d505502d6014071140b41a070160b000700100c40c54014140c0c0e49450a40c0c6460100480104030000c0c64421048012044c0c07040b90000e04025490381e89041c1e2448980048445c00313400c00d80302403902803d2003640c00400c012402007600c42890b4401600c803447c2c0310302c81d80c010740000403283e07440d42044e41032a140800c04011a1141540c40c00780c80b092941c07110100d83c07070002c01000010082940c2c110034580d0345c0c00801501840e07184c4070042d5440302000340c0000794504011324000781074425001400096020301004070b078a2a0034503040751340d040c88600c07440c45940900a00d09480c6d0303009094807a07071070b03200c0303150203000340f00541c00e03490030364150302c501e402c0360500d0100100503600c12015412100313a00c088810b503980700d02e0203440310202070084030b000500c0300c82c1e00b075070213481003c401824102d50100a08441c10940229003554140e24042d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 858490737 1250 858489487 858489509
    0xb0a02040303110105011a0306030a050601150905031c08071e0f030605090717130512180603091b04020f070303060303090b120a0b0325061803080a0f0201020f04 71
    0x410502d504802d0300210300c0e2210008011540c10310303c02c00402c4403888007450443d0008000103445440c108032105002d0380240446000f50394600100f8968441d0900c0080014022000001d441c1400a1900060f2205c2514a1701c050200c0e41c04aa044100510031410000ca4010000d202c1d8441142c26a03900100e5607820000c5503c09000f40a0310110790005015602d814100300c90741d54461600030b2007400600007000903440b500018000e06241801c0502640120400040004141c0004101c80c100c101d14140800300042e0800005000c12a03450b4080d4201080e078001004120769045940c2c08000c00060a02800440c0886550881c81c4100c003c80d44e505400c1c41410340100185000303080400c1000d292455210040e481c07010701405100549440350100c282035070b0300303102030001c00c41c02c803409110040a800703074416544068420440071800c1c190135903054015404200d000d80360400107243ca4915402c200301c0711000400c1e22801155800d0000d01c0030000c1031401480140850307219 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 858491987 1250 858490737 858490739
    0xf0c060207140d3c0b010504180f0638040e0c060c071a031e060d030c0203160f050a090603050c060f1c0203040b09011512020402070b0a0204 62
    0x3074034081540d007103040c0404409402041e0340e07654844034040154455801c524540a50404046560501021020b11005071035407210200503000348034510390203050600700d940d80e15028001144c1d4481a03800000f450100440d01150102b90841c0003603103e48800140550101d20402c81b02c05411181c3e00c503010318981c449034030209162052403d010445080201c0d2400108032541c405450605601540d40807441d012000014091140101403d5000a0100d18010500343c940d82c0300321283c0c1e042070740641510000e190181d4016102d880e0161000d803c0301100d8030241c0c2d10304a4540201c0e418819032001c01d11448400c0c94410003800e401c03800c204030741d0030a03082115482541c0c1140e181580303080b01c200b000c120005500e1560650503140c480d82c0e082c407564032000138407408449421a459503408401c48460766801140b0584c01191004030980b1a141d61900340c4d44146210308048000110078881d0542d6403030300f48a45480103000610b0108035554044c11a40300b12042c0018550100d0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 858493237 1250 858491987 858491999
    0x90b0301050f072001061703040510030204030305030c030405190c170c0a14130204030b0f0c1606050a090b01030c060e090405190303020f070c03150b060f0c07030f0c 73
    0x55070342006000c901c00c10a8a000383d4002c1052440311400729401c0c001289400120304290f00c008044c02c4002c0c0d41024402500c4030301030f56507020340300e4a806208182408240e19100740309840c00d595144e40c030f480c6503031590004020303260070103170059a4602603624030b14070408149401d488281d21640c0742130841c5250100070700c03d00321005448c07800c64204026055076a591020002c00b40c50500004051101103100415504a8008070304403140f880044d000c41400a410103180c42207620784040100341da907824001019001d00c41b403103204101c290050303000060240e0480b41c2d006000303103000141e00520781c84881035040282e20030f4480300c01110003031104550040d81002c52003025190b0310303030364146550741703030b58440300d078480e05064a050016001c1014441c1d011118100c40e03948c022030f03c64405040512a01c0c006120403502c1000c10544410341e208030340100101d091005100605000e40401c90000d1584a13500e0540f660081030f4011002459078142c13800c40340d000b030f882400e0180c1440 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 858494487 1250 858493237 858493241
    0x527101a040612090f0f05011e1107121215030c1e060309170307020d030e1c0309110319060b0406031212110d0207020406051f1b0507090b0301 63
    0x421081224081080709104140d0011a0382404050080300054900c0140c202400458490b4600900b40300405000b4014070070150403041d005080408000004031401c80740305c0480b4a0b1403102d0719003070010700000011920228400c0804a041d0a00c02920004402e5440c102c1e1700c00f1249841000e02d8040910512246007416806481500f1120a4031030201c11010602e11041c0300e2038042680350b64281d030802004440400303e030070210b81040d881c0d050100000c1d4481d0034180c980700000c1d2426940706000c0ba000178030180724038001c10480b240700e0314201d01200604030400d0141d92040b415400003140f505c08000906440c0503070b5030010240c00e251300c0d0000c141c82050f4045407241d07003052400d10220356660000045500c69003071000d40e0768080340c40030019001010341c2c4e0581070742c0132440984401c0305070000c0c2100c1e4400c030303420000c8903111307004c002055500110500c3d2149801c00013042c040c6c06004101c204000480c0b00f85840b03034050355440e00e400700b00c1e00100016611211484800d050034 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 858495737 1250 858494487 858494519
    0xc03040c080115230a0e04080403020d1a10240903120512070e09130212010504120e0a1815081f0614030a03180306060b12100609052710 60
    0x9080d13100240190310006000e0100714002d030070f803600c00311001c2020800324070301300c500171580070b41003003100e005605003000d43d90012844070700c1f83d4410b240001e035500840c023014015642050540d6284c41c6034412481041c02c201001e960600040c0750010001c955035018032001070300c07a41c0d1404d0380d40b008071120110115016085c9406c0c400f92040441c2c2c10f070b46142000341e002003c0f100c00d020a4030a8000101030303401100c9605955443d00c0280018810801c850402c00241a00d07407555109118061104454403071103104c3c0044200c20402d03801c825240c11101035060100c40e003801d4640c80d581405c0c20442d02c0448034403c02050002d8211829040c0a4080144611098010b42d030203041d0203c1e48400c0c034604000c003000031a410544610400b000c200f009140c200808102e05510b07518401203a500c1894241c0124114000055045a09031030b0365041e2070361981c40b41c08031403138081072204040103107814420204003688040383c0e80b094581e0462089000880307a2120a00e000e1144001d0580 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 858496987 1250 858495737 858495779
    0x7211103030703021203040602090603130b1b0d05070203041511010c1b020103110c070f0e0c1e0705011b0503070f03020f07030e1206041b060806090c03040c080115 72
    0x180402d20121380c020414003400c00900740c40560300e58843ca003d40082c4101e81000f51b01c0040402400014010101c881202c68410180340d00c02d40c694207502c81805104d61050400c1c42010030443d801c02d0380d030b500469086200760044900b01612050071504c88418025183d0015058403c0800140d809010310560042c0c2800d10003d4403c11813101d04009900a101030305041d203450880c01401c15030421105681401010768040988580e00c1400d015851302c652101000325402198a422565085500043c00100781a007082407041f40300c203480c0c100311400d0351155070b80c184002215201c40d4018554040c0b80d62416503d20b881003019015503c0c103080e9004041c03052042803612420941190022038140c00c04e984402d05590010f45085400355840c040c900485042c08100a100c2c001c03d03004185451001800760b484d901d0469039a103003240ca00741e100c1c000d200032070068868200155041402001349440150311703007410034252410f501d079000b01030701b10b08401c000524000740640e0404070 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 858498237 1250 858496987 858496993
    0x524060405010822060e01090302070b0f0901210f0e060901271112010605090f0f04030c29161706370f0603051303080907211103 57
    0x100300301c002072500000500052030303012001624441c00c0c0740304114001166000342e050140c5001840a01d010b040008821000b51103491404103000301140c00740e4100701080c1005500300410280111201e01360603c034188204604030880610003d14000c2c416211a00b80000c80c5403680c4040d81440c00000602c40400d0740d00d41464120301040c0303030140d000300c0441c0e40316400d18030a481c10085d5249000d07d511552013842c0b00590702e0041419003101d01110001c465622040e07580c0b2400e0340f84010211281ca100100182c00100064061440c6110b614043c0400301485d881c0c011103c4100048941240382a904c40d5041104100706c03a103070140780b03103000c4ca4503444064110100c005903680207004103100d9006c0000580d0840c40b66913800a8920f601f08903044040c0c04102e4540541480707001c0c0c9100001c5c0d541000c24400d01074003032180101c014401c407840c4158145c07800c60b000600648145810b001c2c051001030312003a040045280409240b0a010700080d5038030300940300101c0300c41d42d640203030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 858499487 1250 858498237 858498239
    0x105090a0b0d2402032a04030f0803040f02030a0302101b020a11040e030a031e0506030c040b0f0a08030c1b01021e1504050a0c1a1c020403020405240604 67
    0x103195410110300003907100d01a000f40001e441021010702c0848415014024408000c01920700d0740342818008007810b00081c0c0214104034908402a840b49000240048021004100004203000000c560042c0900880201c3ca0915070000b403e0602c4030205400603400740e41008000002031080d188240d940003440d803051000e89402170342f54440c00324060181800c49203842903544a64102c10000f41010054036980d2a40c14000340c02010384d242840d646c4403015a0440d017030b01641c404c00c4d005410044c010000c20a921080102030050314015540140605102444a45603240c0d03507402b511109015640354126602e29901d4038603820320242d40741c5018500000517036000302d0103104101c04030101c40c500b641a5034865140c8034008070402080010082008113000f40031a01d00840d46c46018001c3c00907a031848103124250b5012041c1024100400106001e02c0801e00081e08200c00c118000d403d041d6a500084c0860f4011100b13002031040c0c00700310159216200c115001105e6084403518181 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 858500737 1250 858499487 858499489
    0x9110906060310260d0807081e0a05061206010914060a0b0f03040c050a0b07020102010c2a0302070312030209150403030203162a1503231b0706050105090a0b 69
    0x494901d02c24000e1140200079652034410850074614142d50384141102c42c0842610b1700109080d03800c81d14003000503981404280d4000d11a002140c18217003041520b030701e98481c046c44500600e40500351651001d500070785040e0105082c0b00981c020f240c2c111000840031052040780712803103002490700c1e1180d00040d1050160301203d4059a40111048400d5900ca913500d29048501c500c0b1508110750000c840c6100081c0820600020312115100781d00910002d00c0c500e206594507010300424001041c190303202c00540402d0900b681507007500030b104807509160303240c44190b0306032035000040e00000e40020b40d81b074480c1021280105103c0094503110300c1c05140d42c400949034021243c80345420300e40e80b03000c00c2c180120148030b8690090300c1150000c0c501c8441140c00c405180b540b250500460300b100c01000b46078000d120b1041346100d203c600f2208030703103035000a92000c02c0c001e1490907440414034140300813001000281c01c10500c104400034065040004010f08070780c00501803140c40c0e06050381c1d080b003 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 858501987 1250 858500737 858500761
    0x31e0d02150a1d0304090903030e0c0d120512010b041a070b0a090804051807020105150d170c0f0c01020c04060605071401060b0c0109020a05152b091109060603 70
    0x2c8001e0100001410b011010000d00300c40d5182200010380303102c04107010505078801c0d440b22101d24403036101007211154150060f610b8560030207601d580a403d1400d503101288084420142a103841d1519614080e494410040511420b820a12000e01c02040034040502c0c8010350340d8150095210b4181001556583e805005a0017040c1c4005603448a6114007000700c1c4000345c0b030180100405403162014985041003000c0300850342d0000540c01c00c0042440c401504401c1003c0e42c0740038003803c3c007011003034039500900202d140d6030408003a01003001412040d070500600d691003150300058006030702182d000a01d0f210742e49110510691078407204014a83d00001222440c0d64010721415901c0c040000203401400c699012440000d0001a403540204e81940080070040c03089952407043d9403910b00740b10490103604408000315100b084548010048080c200560100031000101c1d4481d01101170750542d051b203002201c20b0011780c94240254a04001c03020740c0450140d84003400c6140015001c01c03 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 858503237 1250 858501987 858501991
    0x180a0f020f180918100b0607140d090e0c0409021b07030c03050105011e2303061005090f040f0803150a030f031b150b06130b090a1e060815031e0d0215 66
    0x44a6907101b03a841640c0703404080c0e420722504078646038100156071504548550300020001c00045c00c012000c2181c0c8485400c16000da83d03103075203480c01c041c1400c181000a41c00f000b02e400b41584c0b80c0d0004146242c04000040143d4462291040b0562031450709a0030b40d44181c020302103400f04070140354564903a1000c004201c441c6803030310109848585e48002145a404a0f882c0c1e0180140f00801007900d002c0b00070201110000d0f2034004081c2c1d070380c0b482040510001e9600400035001e402d51200451408406150022111000004031941c013100213000c00c0007590044035011204880b0340103060b00044a0042c18001104500c644078083e40d45030403107000910040c0d40c0b5641c8007100d500301d84469003640e040d13800d941082903440352100900901900319100051064008800105a01744120303500e078607030b00c5000b4034810300505080d0151246000248400003100d2440304d100e515990030400000440b40080728500e04e0516251454240411080302e0015036100c40307547c50f02550701c101426 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 858504487 1250 858503237 858503263
    0x506070e1806220509160b07030806060f07050105060a150801030201030c12150302030613170a030e0a0b01080d020d0903060c020712060b01020c180a0f020f180918 72
    0x140040e41c2c2e41000400c610408900031055041e80380d0b0070510441203600075401001d001c0c04940700c0c444034444800b5075100c1400758841d82032040c4050300c00a40034003142070b00230304014101030428034042905c00315a0002c1c1c80a4410740e4407403051118504150300c1c0c0d80007511029807a800b0400c000f1001401da400c06100082c10595240411080d0340c1c0725034010300309036002d0441400190110300c0900005030803400103903c0b03401a1801b00d541d14030b11208032801254040c0f01d21400241d8003800507102c0d048070117400e0034144c03540d81940c01600c0911810390ba052043c10400815414074410501c0c28030705285020a5500240f816030006070010303105002c683c0d001c10045640c100c6000d0807401c0c45a1a800020b00c2c61003001d03039000700901601f040c0008a400c0c0d080704c0500003404c0803c4000101405004e528803c2080802c003840490341000c00004040b44000d454540403840031001e507400b41c100c140440b40038407111401f5280202c04640c1180700c07000c01c109544c420819054591050f84400 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 858505737 1250 858504487 858504529
    0xd0b0a0906061707051b060a110901121a090a091a130f11090f010801050f01120308060114030a0c0923210a0c090c2d0e06160506070e 59
    0x2e900c1482402280e06c01c48050400041100500d18442d980e5002035494800d070900349044540039010041c03c0d0f0340380d0700c0141d6030401d181412a0b03141c0d00515044000100d410101e548039682511212421401034030702d00b000246212040c01c045040d0101d006020100d44804010f003c4a202500011014a0340001e10003c0114403803924a506410b00c0f259a600200002c0406c141b6040d0f602d039031412074851030028012941d0310003c40e413000c0000d004514201c411464cc10001c031348683c0b00658800018101035200340c141c0c041041c142d40049038042c14683d16200d401c10b4a0740d02000200040c0329036038010003000c00d40360040f1a980040b2800c03500801c042ca5040e82824008c1c4100b55190701340b0401d5907500755850512944052180c010b40d442ca170305282c11091440d02c21a484100c0205201403070051805950120802c605d81c6d49540701004841d41118100d95140c0004041b18015480301c0c11048500341703043c60070000300403c0714003403010210340c00d01203890f040140e150513290786c450 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 858506987 1250 858505737 858505741
    0x41d07020d031a0d03031b030c0206190e0609030c0706030b06030c0906070609060f110c0d1b0203010e010209181005010e04092f030d14090a03080d0b0a09060617 71
    0x8248080300c500100f20b5001d41e07a0120042450740541c0b0032501080e140c00542403904038180103500741d41e0b80b01d6004c1c00603445540001e1301c0d00c012500d94580070080400103d258070410a41c90b1402c0700030364000ea4150000100000110010080c0000804107400c0500c1074620083c002240341c0401400e0b40811280082c0a100a42d81d2a049405172603101004105a1040f030031304400428410400607951460614040c403101d003a03105443ca101c00500040240300e49024044541450480e4501d90400c40320f600b040041c1c2e000e0241044018044000603203842d48141042030280b1901c0055007030004a10a001e011400e0044407800e491080c201800400d48000c0820018514440c010305100130140081c04000d21003074680d0b0010f041500a85c088414420405171580160008000441c7c030070702c11321900020b04e02c040c2c030020030f004010003083e80d038039100c464240c2d003d080d4840701595501e03248000e6142008082015240401c0c00300f02282c2401406425000090b200c8803801c0e0b12080 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 858508237 1250 858506987 858507011
    0x90408070807020319050c0105181207050d0609060b0406060212030903040f12060b03030c07090e12070506071101060e070309060b060a0f080903160f080d050c041d07020d03 76
    0x2ca0354120381c0541101c198401c8070303c0e040c3ca81c0300c0311007003103d40e4000c80d00700c1741e1107610800030317141c0320704140300b00710100140da00410107618120201900240070300708001078a07a4850038080460760240c040400c0610b0b071841e040d0200c481e114800d84c0702c0e078540700007407190640c001540303020150b00218031903503505c480101c24554040d0f42d0102103402d0300300c500030842d038500c05018031000d403041205100e0060300c1c13002c05449002d0310039250500d2340004400c200d80070642e0041c04058140105a4070703a50600b507000d800e40e40c00800251241e070b00860601180c541e20016107078042401d00000c00a403410f069a00c0b42034075014184404040e2140e03019010b0000e158043d42e21402c005044950302c4244c01d2010b0310500760415911f000c902c040c0c0000d80944008400c5500381500c440200c849000240e448043e5203400890a0311028001d200498106000744a12401401030a125540700e07481d146080d0300010581c40e408549002d4070061000c040d03000614114036840500300030408020140c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 858509487 1250 858508237 858508253
    0x103050616031b1e02060411190503151008060405060a020a051c2c06012714101224020909040c060e0a1206020a0e040e0706030c0e09040807 62
    0x42400c6030010301d002083e90380c007600030a54581030784038030520302400310b80044240e0715402d088801822401c00c2e4080c1c4031003854a41e540340820b04004202c8520291601d0204c6d24020400103089980d12024080c020b00442d030302c01510007070040e10024406441c00395101d5407542000381c00a101c05401040400140e0b00613130a503801d583c4442070f00d000351800210b52501502540000d01d66241154aa450303250381521748401301e1500074401404507074600b03481003240214021422403801c81c10820145480c100e801001d010a01d9040ea603540c5003410550603028000c2907210344d0404201080300e100095580400703080c0030003100801c16604030285000c06c040c0c0302e0725068603800b142410806c000c00582d032040030240d962985d1181300c00c00d4201c0502c06038007107038066100c2030003481c8410000504e00303800a1451601a00e006001d0480010214003a244000c1e002d0032943c01040040c017040d585446050b007a0300075403030200c80114805021480250002d040078141480014941003881104 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 858510737 1250 858509487 858509501
    0x507020d0b07020105010e1305070e040501060b04030b0726060909031605031215010c0b06150d02070209160c0318030822060201060e070c0212030a02030d060509010305061603 77
    0x18214a41c1441c1000c0002c2c000c1400340640600c0c1c00159010036000d40401600300d60866109004102c01400d2445c4080540700c010400c59440d902c52001003050f005a2015100640c0309400054803402e00b000080d00c00014544c0c40c244620203800d10908034115405045e80001090700c8201141d29614241070440c070811078904c40c851108440601000380000007808210100c07802800d840c1c40c0e0341c1400400c03200c80da04040c006801c03100030001103080c41007810381045e4020a02d16103540441c2c80d603245130300809030507101c450707020405409504241c00703000ea2020b070a00090720764900250340a402d945e51120050301b003000602d204549410010b03180342c05940c0020310350341c1b0741d0019039004010342c00f440c0c003540da00c0401d8000003502e103005015036070680e9840c610840c040e40c0c5a003400c55140c0000001030746d2024102c204e030018684184014403140807036901559407554080c3c0003000f40d640580c0814007610001004202040b07011400d290003c6d5212400d01800e8070424045001e0190 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 858511987 1250 858510737 858510743
    0x714010b0f040b031018060515010f050d0e07060816080c030a0e0102130e16020f070e0405100603030801210506070806130e0706110105100603020c0102041d25050a0507020d 76
    0x2e04085079103d1011398100c03003906072141105100e199279080e84862101d640e81003050214040854880809008070050081810701f0803000032172071010309210b0715149a580c401c038041072503201071041c8410001c4e90708942e5819401d00b4000c0742009142c44000e44402018007015a42c1d07828444000c21085d01210311096101510f40c15241c0c9500c506258402c0a4601c081c0c09000314098845107070020450542d02c200d0140502034031031406007070418405005000711910301800a05207480c0445100c0c0001460003035540500035814001500404500d000745254568010500b80340007a0b80040d4296100c9094508621a515014003143e0380130400c1c840d0b070203c0d500717018076007000600008020088500315030310f8000b81d0b58540805822100140c5611000b40b800b0390041c0601806070b001411040700c090700051605540e080003400c49120500402191400d210501c01c8a200c40801a004203e070824140c00710402c0250103003aa2190320741110601031301081a0341503541c1c2818034000d07560 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 858513237 1250 858511987 858511991
    0x50a030e0319080901110f09010e09240a09020d060f120822080f030705010c0503090c0f0a091503020f01020118031202121e100f0504050c09030a05030714010b0f040b0310 75
    0x4031f42c820041250308142496400030b03d058103043c403a454440d06060050100c21544030240100c6221074001411042d480d58101803008000a4040c60500c0100050080804000388442c10300f1101d0a115925900c20340810100401c6100803075071074001c581184000b00703008040c09040584d052840700711a13004c000f10703010f20f8110203064600440140040381c0b103000200420041752030155400e020075100005c40794824082080941008034540400c0d00008042a40700d543c0c487c107080940d8111015446c200421500810031070920088850810700240020710458400502e803400751540050040c00b0455400c0f014140c0654590482d0711400400c2c1c12491189400c000001c20303c80c1d0640707061600c1070074800248c1d42a039001107990036181d0445c8a05d2030140b5081c200805482c0181451449500412241590b540c0c100102c10344c280c800e00103140c594109007840c5400002100402100c2d90400000d40b402e65200a01006054000c8900050a07001000881c0c90204007201d0740070b50714 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 858514487 1250 858513237 858513247
    0x90f1d1503070308030a240b03040201020f0d0c03020f030a080601050d0603020d0f0b0a0b06090f19080c0102060f100504110712080115031e02031f06050a030e031908090111 76
    0x2100400941c0301d4103a90078241f182c0300361207410a05201805156441a02c2c04500600040e00703602c00540e00540144100d561001070350a0190404038820600c00100302c400758002e042540600040c0c540e64009000b41d130500e40640310140800304010015030401000040ea4505160107a103d0300203147c014102d40c400c480c2c0781c6043d145031140480d05503101e10f004000101017003890700a601c0710820260505003080089824881032041a240041d40b20305014101c1d01c601c0c10070305092005142c0031008000d00300d142e01c0003900740342c8050240032190228004010700c104040089504541080c0d8001038240c00c003801410403801503810091072108402000300e022544050854140c541c0e42108550301c48030140c080d0103d82c0c05500140445201c1180081ca80040340d0146074041a41080b0b90b02d00d44c0b14030500858800c0617001100403440201d85100700503810701c119620195150000d500d44042d04018400740300b00031a050041020503400240703202e00a4211018410050340e01584030307 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 858515737 1250 858514487 858514493
    0x20712030f03180203070302090c1b1e06010f03170708030a09030e010507020d060b120a1a0a061202120c0d03050c010b030c13020a17070201090201090f1d15030703 72
    0x1c0c160008a040003a08040c0049400d80840181d224016801001024418510703070a1110304000248800100b44091100342c00090210002e4200d02e044c0702c000d0500300c1e9140b01241030003c608204a00158807820052081020100405090300d0300075021005192200c00002510f106019004000180c080306200c0f03034902d6604403124041c0700e80c07507000182c081d0b0300045a00303001d1140080d42c0308400c4c1d01c80c0e0b00428440d41c403074201d501c0d0290101d000c56500800c510b1800340e5481c2c0840d210140c42e096044c0354001900000e0300208085402d10859103014030055460903075940288c4074070064605090310329401c200c4c0021070f8601a1910038807404d1414068802e40010740b0070b06c995400c00c80c48800c43d1401103009402c00000401100020003600310103002904595103100c14407001400c50b1443c200c400f881039224080d80d6001044200d40c61000420b60f540f6580001b120084101003800742e1001c0c90686000111503012106880c1c1e502040032400302501004981c150081c44004414 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 858516987 1250 858515737 858515747
    0x10305100f090f210201050c12060301060b0a080f01050616150b0306090f102a0e04021606182301060e0907060f020c06180d150e07050f0f09040302071203 68
    0x403084c0c56404030100c0400b42c1409a0a0b918100c40303c1951107410000f24400b000483c02e1581c000c0e00c0076000040494070343c0342c1071115034802854980071815103005c200d10aa043c60501d409008151542c5040c6a50014100507486010100070100150300b040303060342c44c80980c4000c07400301e40142224006d0600101880d11211196280182c03406420799a0401403028054202e90301d9408201298600000c06205600d45d81c03e00c00c0e204108103244ca101c0907503940c0c00a1300390890885501031040402d0b1400104441551000e01d684150000c401000700d1ba0281c034241d00f400901d0011104000248841801040355402404440401101384510010001048015200c6940741d1100400401c0d1060340d541401c0003a4070341c0807000704010014103003034441a80b0700b5403014021900c100d2190b5240c0e200c466414a13280016651401d008000200420000008050540f0341485044054001c41c411f044912802c0b0300441054000c10f00b010710803c494401483c22929141180c0d01c68900100 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 858518237 1250 858516987 858517013
    0x70303030c03111614070308121915050405100302031207060b01020f07030f1e051501050a03030806040203091c020321060d241508070e010305100f090f 67
    0x8006464994041610103c070000c4a01c0c0700003000103840303c4500c83e41c03901801155041e90b0701d0b040c05400c5c000800204c6501c080c110b10410322140d001c580c0340c0421107034143c01922400d2640142400030084805800400200a8500a80e008100381e0b0b1400741115009040350720094052140c221201402c50b542070181c44a14851030302400f260b0301321001280d5859051100125580100c51300300000388042d052003080038810020030130000c0980003031003020f102e0400283d41d01d070030000301001c4840c51403640902524040b142450030342d0450b2070040c9604030041c1035078081c80e030010109051050801c02000b01d00d40b084401c030130107031b05040c2c000d45a8003c1000401c51150700c0c1d81c0c0121000944500d544107a04c040c000c0709030050f141d250320580360f81012040015900b210501207504c07203580603119030444002c080700d415034a403030744a5280003600c1d88581d10340c140c10710040c00010000b01d13181c801212000c001042e107110ba020303904014000b80700c0090404800c5231034001001846040c1d91 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 858519487 1250 858518237 858518261
    0x418050a05060613091e050411010207080f0a03030b0303070807150e060f040828022113150306050910030b240103090507090608060609010f080d120e07030303 70
    0xc4110b8071084180500390180079140851a04000c80902c54044c2c180d00441c801d403a02c0e141c1c440100b1007203650038101c440071b40b81a82c10041c00500e01300c182d6010408078006002e140001d0510030400c0350383c40c0d01d50800050040030552220403600d40340e50100240c500306034001f41002c0d134800540c50950035900d00010712081c03260a1001d903010321840410801e2042c0904401000740359a5a561018035078050011144e482c98062820042c0725400c0c101302c0c900c07000580007400725a20104a02c1c16955010000d260713080b5042150a0400c550420610308550f42c41c1c0c8400c0d4070301640340003030780508140e8100c10340141c0f01e2010000c041141c0310381001124011101500e841c0c0300d0101c614900c0444841c618042400d403045680300b07520a40c40380d5000e500a0b0b0a03900400e456841350810345205a00204607035001406019030f610304040c42d1401031012003810100c00d85458210b9440d0380c0c00e109070400303014086254004080c4181c1041c401000c242d4242d883ca42d84920b001f070700500c0c01c41090 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 858520737 1250 858519487 858519491
    0x1807050d0f061e12021011030d06060f1b08090108090f0a051c0815060f0c01020c0f0106080303070207060807090b0a0c11010302070803040816080301080d1205010b18010201020418050a 81
    0x403013070207a500031000d540c1c000c1c04803ea01800ca5030b050f91301507100001e0100c0c900c0100400b031010549841200c3c090500c694271128600c02d035480041c00003501c0e1040c0968040303126820780009004200325154900282040b4444d60b503840c5003181466001d03940d894040c02045080010002c003c181c400301c880030900b0610662814070000c55054604841450180d00ba0752b0a40815240a102401c03041e5080640d461426108110982c03e980000c42c4042060b030141c207400f510483c0a006170805013210000071415454201d070000c0d0358450500c6400c2c1030001501c0401c11061140c0644000350491100c010b5a03040c0402004008041c843e00c260340403800032082080070340c070a000321198141c201d510181580c61b6922001055800a50b48000c074000a800300000a48203101960003448610054a83c1c20381c0e0a4015059550786400380d10420b01d030000602030ba1480400f0340e095000c0910207180460b080c00c0044c1d00a101c2d5030041d0070261114408140c3c007421030342201d40b04401e01d40d81 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 858521987 1250 858520737 858520739
    0x1305191214120306010c030c020415090902040b0906060a1d0d03080f010902040b0f0c0a141c08040c0905060d0215090109051005120a060e070504080c1807050d0f061e 73
    0xb07100c0c103074001900c24500091400104001003807107441c18244c80e5000401c0080e010850000c484d100842640c031916035140c84103003420542c5428418800c102d841618460030300d140540010f081841040b641c06d0501801c0e81c1001c990210000c481118030038050194045e28119050140058004a8802c0c075004201390003c1001001b80c000d4408440e1086249402e0181c0c80d10303064040c0d0802e45d0781e13520780d100310041d01020540c0389d5100b041000018007c1c1000b00c0c10a0311148883c95000c5050b800c1c00203d105000000c2e031210600320841d02d0219000a02c3c0d2600c10006840c203551440281d4000c04000c5c248040d0291038000b040c89036001d0b29140800741e17a07078044c4026076004802e2040030031400c1c002803641d5504140001d0b4441028840050f01c191500c4400040d4817054605000181001c2406e21039240d0030032450070324240c122091423201e81d08035016802ca8000401c034404200c004190078030010100c0e00400c0d0441c1c44a00c061202c603403a440034000e00d10502894200580c81c0b004 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 858523237 1250 858521987 858522013
    0x1202070c260a1221020f071704180c1b0605010501091a0307031d03075c0d12080c0f09010302030402060903010f0b0111031305191214 59
    0x4090781c806611001000b12800000320030303648a469031640390180e2613492942060305500740300400c1201034400c00c1c10b0b00c0da84103042c10500e80803030403000c2e074503020304010500014000249010120a44070404101100c542800311001a400000d049a0000c079200303031010085540c002d02d042c3d07202aaa012a01540d0340d26100b20703100401c0d520040c0d01000c00c00310392054440e80141022140e01ea65402c8030f41d010306040c52440e40040019524001c200a501c528008016204e62540034071091000d904403000401b80c4000300246045040281e0800d210040c41d80c1e425050801c0300740c001c0244c0135029203811f010060402d8240e207030740055403500008024500c1c41045d03e0f101d10a100b41d450808201c040154002c0d480a403080ea4401d00c1030000c1001e03075500740036074060040301440200d2410321100001d03240c031700707049205183c0e030300180095400d40c2d8420075501c0445004490404c100c1050004207058000c0c41e801000c1c5401c540600b080c00e0086204074168154120404c48014a00c452 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 858524487 1250 858523237 858523243
    0x1206050612071212170c04091107110d0516090e0709020310060e0a09020c0f10020a050702060d14010b0315091509041704080f011b0804031202070c26 66
    0x30140e000ca001501d00a24045401200621304440281c201078004949001c642c1c0d0480c902141c02e4424000005014090385009024840c034000501c0b10080c14200c440e91140340c02c4840c02d2000f400350349455416824030004100c1010405941e00c48958002c2d03c0b045004003418428030402058424a240050680e01600c00c60f4071960104150703100c914102102116015400d00c07900c1d911840d0b60f8000310720381825100900d030016004005000c00389035508500c0c240a8004151201d4602c140500305410360042c00720780f840d950464110b540c444d204a100401000804143d00d44105400004100c204d8017030029802030304030400300d0710039a91007000c12004840440300d02900755200c0d10050720604005200c160028841d424030303003210b00c01104400150700103502640a550021040c030304290030038403a191040d5070020f440c507002c401240d009840c0c100060b10050030000c0311000c5911103980f41c1e06070303020035a001880741c00d02607803101400b0040042090001d00b100203c1841410b540c0c0c00 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 858525737 1250 858524487 858524489
    0x2030106051201121e080915090108070c0b36070305101a09070c05010c09140307081902012a02010305060306150909010924050736120605061207 64
    0x1040c01c2c5003c1d0714541301117042c164408111003400c02484480865903404c840c400007812004115520b851001c00018040000a007825081c00303100803046011500c2d19040c10381c01070390865500050311400c2e0340c00d4882c2112503044e03440c01c408112030b0b5080d524049100c40c1100e00031000c480103840703001c04d00b00494100d07509403520b143c4904610032403810811a0680c0c4000641801902c0400503142c86081d11814030843c800550103400a2000311001482040c003500160700619000c0c0c01c024107030f0ba5561141d1492000b14400c49190b2007168402e250034003102ea0221100591103c407501c195007404c0303400c2001c80c00301e400c03e070009860b0300b0b000540d20712800060031010009141c08081c094800d1018000458075501c80d100c85012800710f10010000003500c190062004000d107900900303d40d0003400350070801001400914000c001c0302c00702426141490200c2580850f800720201070302c1d846038003d01c80700c05070b08e0802c1c0610050740d2043e841100c0c1505c01c030030002c20303031100682c4803982 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 858526987 1250 858525737 858525743
    0x10050d12020f0706121e092f03062403030a090602010c050f0d050c0408010e21070b07110109120f0905150a050f1b1609051005060310090203010605120112 68
    0x6003429904200d000c0303821806d01c880000089604014401c1e66010641d40c64030801e450203010360040c1c1c4d035407800a40803048441c4e214603000500d04448000640c031900050a09075100c039591040082e5000c10031011112018000c0869540b004099000b902186042c400c2d00c025500e00102c00c0400c1c0c1c0508122010314181104251030a201c814076040142000703400b1440c5000c05220100d0718510034444d043e0402d10500003041c01d020002e1103844641004c039160750321000309002401c00034280035981a000545410720f4580c1c0e441781c09407180103100c882e00c00b070603c0107600352560002c0e407c503000500804445e0348078548583c60f01c06000d220700041d01c070000000d400300401e0907403d1050000e400c450462483c16407400c8541040c0000810101003d04070580003100c480011240e090214002403412500510103072030310f100c0300510728400f849405d0007060700100085406016040c514040c1c002030f513003103485e07584900004145410410000d241101c0b80c60001c01c03544e004060138030301c0345e034 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 858528237 1250 858526987 858526997
    0x30306080309010f050a020f0f072d03200904060509060609040507150c080a080619060203090603070c0501061e140f220903230903060a0510050d12020f0706 69
    0x1400b150440c5c669002910b80c40c110300802100e0180d158040c48403124070407164005002c0705050004200310303500040d220300f070080031000041000d419220001802c0f290400c620f6020400d0820250007000000b026840c2e00001180401003045041d41c040e9004050b502c04407641551820140f20441c9400e4030301400b01e902c00c4500300456100c80c0c1c0080d49500c51441c10000d428400d82e81c0a42c180c01036810700010540c50010005d0304d0400d40407a07205e846800b0410040a803500e040031b510303481420403150107628008001500507006000079080035900c50f0080211540d0ba030724500118040300c110148600c000b0304006000c9a43c420440d010107001400f080b0b00fa030035a401c100340f511041041c41c0f000740e4001c0c4141c040b0982c611984c4040d9010b9103a0302d030b03074131040710106240c00808542d104003141c00f4808500390351400201e81f5400280e0319400a800e0f100c4407143c0d2501451903020580c800710110b8440308201105813101d024040320380840b83c4004901414a03141c08080c064440011 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 858529487 1250 858528237 858528257
    0x161706010e0c040506040b0406030c1d011805060a0801030605241311030c030105041b0c240606110706091802030c1c1d010515130609050708010303030608030901 71
    0x4080408142c2e005465801c046107043d0f40d800c0864403a03002a40801d1072100e010504100d4503801d070041d0220790220740307030942e00d00080c11041c442c02010f00d081681008420b180381d80420040700d1001014200c000c1c41540c072501d91000040940b5000d020440307079141840049898106000103540794042490310729000c14030390400780f0500030308101540600c9511100120a18105400214007564049010590740e60502c3c2c14041951000d602095460740a0005010295070081c45545550345c06074a19002c2d1f40c03908460801180d81e0100303420044c1c50907400160030340d00140b8600442c0291002d032010166242d00c2a18107400c280b0401181c0040c0c603801084408407940115800040120940d0074200d1010398030030154120b0b01e4015140b561103d0503040080c0da24000034541000c2d600902140c030345041450341c1d0710180d005882c0140c201c04074000d4400c00c5030700484090121030600304000c4c0307068080100310701ca0a210903004645041030224115001100303e4000c0c0006844045180c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 858530737 1250 858529487 858529499
    0x6090103020304080d05041b080d0e010c06090c0b09190302060a200706081f270608030d02031608060d0f11150c010e0705100305072016170601 63
    0x3a510080c421600054200514a5170192612405008600076205040b150803007074201d49448800b908016030503402581d9112556902c8840521860002e02c5c0441e040c00462601001501500000514103070821102080782248000500703801d90003119100d5800708100c0c081d9400909500010b034001c4004c220f84115a8003540544820845c42c6c0c0d40c2011400201c2c2c001410556175401c03a20000f0800300901c40c03140418008106e54501c0050300d02000340c030301205941d031705401c8e00c14210300500001031085004d03040c0c2c1c4028001c4c1003440076a40e846010042c10070085d4070843c0c1400014800d4044051000c0c03145200d0b52152034080c100e03000c40001070301c8810b0186a203020803900030908400c00462a00c0342c04801026400b80180c45803100a00703151380b829211102090394159000342010400c568448010503012078090600103121b0301da22108803030019030790b1350003a402481103200c910000800114003260070031183e02e6118681e180c100c031490341f251150020303410f68000d80042c400 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 858531987 1250 858530737 858530741
    0x40c051303031817030306040b060c0705101101050f090f0a0308011404020403021008101e170312040311010f0506091819050303090615030319030f060305010507140906090103 77
    0x260b0b000e00481400c1c040e64901c4c00f080000d10b030120104c0507800c08418803445041c24010403144050803182141060b6003081020796480c001e2162503c0b44601c0740702c0c1d02450303008007035810714200c20000a009524080c1000d0f040c800050303520036203a02c5226a4198811400300300403980b2680341d80c40c0890790b440c01c0f503d10141e4024447c09a071255007044000016951114008241000c94844040307501d080b412001d0700181683c0076144071060440019907110b04043c5000c1500c205024125101000c8001c842c0b0714011076030182c00126504042c4414580c01010030119a240c113402400505212620b100a46e002600c40642048d460303004204240f1501851002640700b51084410b5401c91140c0204541007040054856820000c03c1c05850781041c400d030340d40402100c6080c4920107045005c80da0340d00c030320b102d01d0401e21101822010064429003140703040c042420310900c003a5403a410024024001604d9210108060400c0500011404400d990302d0382030092066050000c00401540 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 858533237 1250 858531987 858532007
    0x60a06180209030114161101110a080408130e040516060c0f02031606030f1406011403340e0a05010e010e0406030f0609030807020604080301120827040c05130303 71
    0x1e419522200c280c5c001c40d161850b464840d4406030b448003030482c0142000b0340305042d104080358603641031252484000740d050045401d51004c13441d040c9515074483c205010035000d051042140c09a070380100050038a8062030490045024005907013000711010702c0e15a60a00500c1400040350a560105010600c41d849590900b03002400391500072803160000702d06030540e030b0090303800320755203141c20100b480641c07043c07280c404022490130343c46041040003c0e041400e11300610074104400000070b01c101e1100c0080750130004005101c00d25820303400ca07d03603000d20844402140000e0a2000507030451034064400341c12548183c407108102000da0004507403100c45100c0b0544c1294468500000161500d0064040e0600680c40014041c00d185030081100c2d402914081c1158003a806120100c2c484400310b9044400d251800b4010045500d0441643d025600150200503407541800b1000f440304404024600006c4804001000d0820350030349440c09410769441280400007010700000e40200c2d4120 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 858534487 1250 858533237 858533239
    0xb091303110105090304060e01020714120a05011b120923010b0a1d010f14061c02220f0305060123060a0203070c050d0f03120e0307030e03060a06180209 67
    0x2840500050960b080d60b40c03e50703190b44e641e40001010030269500c41242c131447e2000344060a409403800b0b080096016a40990600c90240445030100001d0100013418000b64071000900550403050784102c1c0c00c005220803440800d5004d018444980d007144107188a01d907001c48403000c1c56201404411843c54800d440b0803e41d90b890058015680d18004c0f44001007101d10881c405c0c554a0103120052000d046c0d1094843d210558821b104901650010f29050001950181d803030f07121407507040c902c105411582c102c406100180d80d1400a15400054140c61682d90a80064aa440c0500183c01c2c1d8244009081c0fa000b00005008001610320710081e619580b01c1c4480a94805000190459000b10003030005a403000482c0320420001c540c1c000001c18040b55401c1c00c03124039072222168002c480c0340c0141040300310f80e02408990007540c0003c9a660701541120346a02581c5400b6041940c2518114400d00c2400001241e084241c05485c003030314201021b1020a09078280054041c0d00840611 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 858535737 1250 858534487 858534497
    0x5040b0f0c0c1509011512080c011814061005010e130e0d0f080f010303050f0a021f09060b040203070903120e1009061b1e260901120b091303 62
    0x80d4400103010805070060352103c007903500907804e00d00015421511008442140900d4030742c0100400c0065405100c0866000303894940c1d40d241c1e20380c460f40104103c2601e0404403c3c4512802d0601c04107504410350440034908131402525001c150340382649540c49000c0c0041c0c0b050b01040060b080060381100110030074400840d0860352984171a090019841103040040c0103100c0055109a0040386150000c0350b6022140455056490082c15486003011580342c640000640c2100d0390710070050798020715091060240100441542c1d0340182c80c10040a81e61036092025221443c03606c2c0c400c0300d01403003107901d032281d0a0380740d581c031800441c41c1040f40405000300a0802503050b00c40c1307098003461141070340d98000100c1c20140040c01d5a4201e0000c0141e180301e0002e00c2000502d003002c00016104600d00d851602c0ba40d500d0c0928501c1007291800d41c0c00c901d040c003056440314400b406060040d0003601c695004024480a0404807410900317616131105000d0081170243c1180b80c01e01005500a00d00 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 858536987 1250 858535737 858535747
    0xc0806090705071b080c030d180e090c030f160504231003050a060c080c19050906090d0c09050705072004020912060403020c1008011503091202060403080a05040b0f0c 73
    0x820a54680d195004801d1504040c4603101b9514040c016016400c8884c00c00d03051108600c0c14400c010b070b603c1d00880c1400d00340c1c1000301d6203030310082080044e4100b0082c00c481c240c1000c942c100382c40d04904040090442140040441e5514203400343c0c60100000b41c40160f103010900340e01c0100b0020142a03950800c00114000c00402c4080c0041c0310a10300a40c00072030300e1910008018110710006000c00c05502061091021115108804140c6e0300101c0ca001a101d558210003c0c8140c45010083c41d400001d107071900007002000500401100c442e2441003140e9518400103803018400e2040007000031214000c455070000900141802c1c608021780014105050a00410300c20030049100045980c1f01c4001c06c02010344c1003000700080f0400362044150582040c00140c0044010300031281803034100c0010b016050b00c2540301a140a4109030106c00c05001d54501a489100c00d440940002d080b500003e40c0101a90091074080c507030242c001c00040e900c9008080c1d01107005000c0c1141c012017001 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 858538237 1250 858536987 858537023
    0x31204141306030209010b0903070603050c070605180709150f060f030905030d09110406090c050d05060316030c1e0b0405040903090f06091e03051e01060801140a0c080609070507 78
    0x38501e40071f0308040036030a6842840c0d2040619294196200004046c14001080210f1107940c06942c1469170142001c1495103e117454001489408942e00381207201d84000003503141000e40140325501c071610420318580c2d4032003052560304401070040d0b030f02066410791045000380c402c2d807120b10180d0003a001d60b820928103a0591007a00d85070682590060014031103003d180c42d103841000001c0c2920303a0104441d540000014240780103022442940c070303584400060003a24203005d02c001421848200308110b545910f4443e00110950240d101da058200c812409106160107000081d181d01c81c50f01800c0610b40f408110140c200d50340c040b0104000c2c0c1d8000140c60412031035070f8014007450786442814a040a070701d906e5440712079803038101c014190603080010071808a00300034800800e0050020485008646602400c1203a102d00419841d0219040502e450b140034079026007091001031008800700b1100311f800160070788400d03601200c0d07070003c40c04250048000b428100d02c00c070650800650609 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 858539487 1250 858538237 858538249
    0xa1109100b0705161410021506040b03030c12030702190c0b0306061c020a030b06070b0411150a0e0a0e0709091805033405030304060209060706090c050312041413060302 74
    0x903100c0345e05104625004d400500c3e22070132411800800340300620300c041528030383d0104214054051030103a6911540e4030010388081c41102c8202900904803031030380d040504540c4440c1e1084030201c0050090507010800e03130454000b03c04221f03820200c0b404116080540700802e03a03002034615a48140c04200b13101604526000616400268150040c2c1751a1101805825201c01e061801c1c07040c0c10800c06140001e103000c0c400340e00a40c0042c0c0c0318429144101c08540450704034490340003005c4010030241074560380304c01d4a880c030b000c080e1040c00c1c0c0c1da031ba204d00c00e44251100740c0d01c2c58082030355820280a030210a61181c880f503e4400340864500c80d8640310036045520040e035890f85100d0703072000a8240d601d4410b0b0440c049401ca10744640040c1c0f5074541c3d03500c0c0e000190000344026000030304407450b43c2d903400c1542c240540103c000c101080c0340c0d250159064010303105150003801080e6440c0003520b1010155000c5070760006005444244420030401d9000e895003212481d039940c0e40000c005a1a08 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 858540737 1250 858539487 858539489
    0x10f0e0306250c0213050a02120a060513020c03030f0405030f070b09010b030a0305070f0c05060d1a09061c050f011107061404030e06160b090a1109100b070516 70
    0x1409a000078500b1851241d04411058070010038468944107480c0140c540c08202603a031154640e0008998540d1903a25000e40f04000c2020070516922050158258542d032201040300c1d822a030402601340d0991b9400141d001d21400440150418000910101c1010001c030b50b00c280b0035020740f0b140090324142a9001e0300018001e492580044040183d044404d100b60a403440d000c40040c011304043d650300918500c41d85034003c005408168403241000850200b5601034440202020780301c11408407880000c1030f64a142207486820a0011285400c2c00050507000e0b110243c0507410202c1c1c041c4034594605801c020072203180c4100440c040e0405800e1003203140c000908a0300c00c0d40d0d41e04905001080c0c0320003800c076048444c07490041c04000390f0000124100b20701c080c0c0386030340c56080095952202e41007a81c0041d0410350b15000f001501003020504441d40c074898040341c040c0010710010300800f4403048400c11140c040d584414040c1c50000320281080c28420f0040b9025503140c000c2080d402c0000f = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 858541987 1250 858540737 858540751
    0x503010c17010905060d020616150e28140f07141c021e010c050a23120a1209021f031401260a06141602010c0c02040e03090a0b03090d1b02010f0e0306 66
    0xb9500540080303090a2040f0248cc02c00380510032500d01c5410a0040034040404005100e141d0742e50798203616100c00d11451011706182000d848080b6039694030030b0044494115020300c580c810171021501c046000160740c400359000f8010940002c5110352400f40c1d403240c0200c02c2e0602250b80012400242c003080289209407082055207039403200c003c0d0410280d044424201542d40102c80000000302074281603602d1429039290048007072140d1102e403001443d0050002e034001c9400c0c00c0811840c20a0800501c40c2c0702c00b07590812041040c81c10704007480b002801024580004ea0301032b042e40d0010f001c03603a2486d034030351420790703c2601c8c0694a207801c07201e00100c000306140e01c5404000010a0b545860b02181c081c3c0e000a0001c060f60420080038140406c4000b40b01d80d50f5061228160042002075400400002e840007041584912412401d900101d440b00d401c0d1154080d843e6520b445148811100b00d140d50701800700d556203900650b05902101c10302c404100b603111901096550030007540e802010 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 858543237 1250 858541987 858541991
    0xc060901031401090b1206072709090c0503060c07030c02041a121b041a01140f0406050702040c020c010c15140c070c0524030406060503010c17010905060d02061615 72
    0x340b8002d00c0202c00e846e4080c2d0103550024820095140c0e0405c6911074081e0a2004401000340820074041c41c400450b040740d203403940f40903984020002c41c0844030050310720071401c540d456662410080700a12034258010700041542e0407101c018240703078100f90700f102d40c6c10002100001c944404248400c807002c000f0b44040d40000b808500d40001210343c050400001e032414800c01614450440a52000c2c0c0707144c0f4100700c040c84c021800c0300001029500c07400701c007151641c0d81c1e590f6041c004100b60001e501c260300c1646800f06418210b400090708840f41d01040e1200f0b41220503e454205608240c0b030316400c01540c491045065500c00000d0191140c0c5410390001d8540310a81003000c45944241c00072402a1440b001a1180080d45d0b80a20310100c0071440d0182d40b6034851030003401805055214a07055820101e640d8240c6800c403000384e16403c500d16540c0724583c2d80c1d0310079000ba070380d040e02ca9903000400f041504001d070524500500c9211045a4136180c1000140e80d4607503ea80c81d26506c0126603 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 858544487 1250 858543237 858543251
    0x906030e1c080708070315120f080c0f070f08070b0d09080304060c120c1b030e0915130213051c050a03090f0e0606180118031a060d050c06090103140109 67
    0x141c4c20021a0707400203007a190070131214903c1d816034041c01005004501407080391403071641c100301003502a41426988003c60907228107501d003450b5603825018a210059004c0c0c404007080081c0403110280444202e42c0041c0310343da181c4410500c0542c45001002c0310305488061030004107101c840203601880c441c0c000052032440c5240c00034000c842e4a001001224180140c01d400c480d80446503030740c5003540d03042903502c0748100c0c501580c11600d2000140d070800480f80c10001c41030140100c281d20701c41c00b0b44215039000e040c0c0e50b40c44200d02c540d030030300ca41405c09110240024103003e800c501e40c04800300844e124985291f00e80f20301d40396000c00f0427400038840580c01d200c0b2605640074007004040d24401c0d140e4030705110b000100b060240d441484141c0d6243c1108031042d80c8900d03010310707010014584100b981d98482c01c0008107214521840388002484501158040c10903000042181e0740160181c0090900d00301013012503803010750041d0415803590202d08101440e03498290003403c1440c00002c20b0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 858545737 1250 858544487 858544501
    0x20a090509060f09071215080304150f0801150c21031d0307020402070f020a090911090103020102060a330509010807030f0b0402240d060e01060906030e1c08 69
    0xa501d004141c1c900801e40ea82556845459140fa000d41000d01802c2c07040c80340c114000410300406060081e00c8120050080001d0101c10110081c4240c031141724040c030750f0b2039804000b82d81a81046006000150041c00100858a44030b085008241d04904e8001111000e80d120181c811291000740b00c401d40e00d40c01a05156074040c0703d130800038484c201c0c1c50560041d0320100aa140d01440101900460300001c001c1c041020749060203101550013801c4151440d01d07416414020302841ca41200c0604416140c154a89080b640003812079505a006010546e81c403036081002c0e080416003005400045042c03e1540200f1004014003040c4da011011606850f1004001060b44d06034480c0c065a0040c400600200e40403240c244000ca8020348442183c0d1510b00c00f0a4507072507a1a00300c41d030120084040d00d0341341c8051005148a50306c1c50010300a03943ca510000d0500c40d028402d203004903408060400c501e0b40280c120205030080e42e8141c4202500140820324030a00e502118800910150100001 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 858546987 1250 858545737 858545749
    0x80106050438040617062a18040e03041805040206031501091502031e0421050a150e0c040e030d0b0d1a04050607091805190f0501171513080d020a0905 66
    0x12010701c55815500d03108907c1e441c05c0c030856045050040302003000a0343c548920b00c004c00f4500040d80031740200500502424004d4580c1c10a02035951410076841140110758420b000700c602071900204441d1960f1502d0101140e00b8036502c40c0c079414043c010340c0c001003080f000c0110901c81c01998014555442e0350901a03060889008040d0014082c2032006222400300a40804c4058240b006c05850100850518524012105400404001d02c2c000c4903442e0407040e81003032030251507800032114500002000c100582e0308a03058409588e10900c0110544140c3344c100441100c4060324604e4051182d460750a0883e00107120215a540035600303201c200401040300c0b03076200b0118a8400d400b41d040c5074400c00903a107003450010f00c403030b16117011400408020440c10741c4002c90b0b080400020b2034141c0c07010f0180400344201c03011f0710554070b003081640c000800c01a00d200301c1e1100110041d524845442103041c01c060040e0f4009800b4403002d03150309000d100404614030152207160b006464030f010494 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 858548237 1250 858546987 858546991
    0xb0d050106170a05070b0703090e070210060504020a08063f0c19091508061801110906030c0307021f05010e22030806040b0409030908010605043804061706 68
    0x40c550f02c4028008003003900400c0000580344103401c0d05a0754036281c1801c072000940c0303420107070564108000340a10260005000d12022046500c2030200c01d82da40b01304012030082c002408041070107080058a01d2078940c850f40c444001c426034084003e0400101e01942c00740100e0900d548500084400044110422640445080c120381e441b428800099100d0007043c0300d481000622520b075a159110801c001c5500409099160100c440c1860701c0702d280320f41400110301070581946468407415513403180e0801c48404400c0900018070755112071840c001d003079000400050460240c00700c101282d100501d10411282c000c054041465410403081c0301c44e038100508800f42201c001512011070001015040c41595014106601595030b544041400740c14a012160351091800b8403603002c03d500400a80d003501c050800800a16448905100440f0b81c203942090400e0000d440000d907540d505515500038032064807000203038410700d4004c0b805458603504240500c00000c80c42881d24913040150079 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 858549487 1250 858548237 858548279
    0xc02030c012c0d0207090e010216032c0d0f050f01050f01080d0c0f08030621100b191a04180f0b090c0426030a0801050102060709060f0e01030b0d050106 67
    0x40003d285001000e0359451051180442881c0c03a804062a01c1e203080d4103841190a146008500e8100341d0b140050410507004481e44200b0007a01e42411150b080015034464190040e091084a18203516503020780000c415003103a5078402d400c07080c6854070083c002c0790301410420708a0f079065410851520300308030030540c0103c10440e81c00303441c1002c1910000115182da8000c005542c0da62030394004120200c4001100784001c2e50110415421100006000715004602a0007000415407040402074214582c000303100100c0409481403040e10003c10761a020400885811362925a882203400c40c1c40090455640c4180c3d0760b00c58400050400d400f41c1c6811500854448090b442c00305101c0c00c8900940c09990f514510711001003580f82818008000c1d141d17410011651204905400181050401d000780c90050240d18040754400340600391038015109a034403070041303844005404403240d070f501180260416031109020071403911010003d0785203900500020500d542440c00c401d0160344c5c088034070 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 858550737 1250 858549487 858549493
    0x24050f37080d0203040302091842181009050c040e032a0c04090623130303020a0c1202010905120c070329100806010504060602030307030c02030c012c 66
    0x42c00c00341c0c0c040304807400c1d264103c410b000d040d11141552a003140300d203650080070b441980c41042200c1020142c006a82a420707100c03028032403440c0260100d0308544108200741405e001c0c0030480021511003480103410301d440c110395071848107104807070944424110582c0d06405c0030303040014900b45030103101c00100c60b4900075454118030826961740d80c3c0025070103210440d644183ca0325411828440d503014020001d1080c408100c1c1401d01038010003a0388981d0810141800030320001c0c0b9040088140f080b0782c5202007046408040c2c40c00e40180d88104090410400c00344901c0002030081003111196040c25400065000c1140c138010380307018440701c00c90404803024003411011a40c001212000e0b2940010080f40003604030a0034401c00b200d091107150181c403280c04000000e903000180c402219811005c854190f66141c1c18032040b10594010034005030003c000150300ba0340603400051202c2c820b0701c1103030700c0c1001001155007150700d04814500500074000000005e00c4403030b030003261080701101c09 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 858551987 1250 858550737 858550753
    0xd0f120c052107154104030f031808030112060e010509030714010617100b010815010e0a082a062d040305150a24050f3708 54
    0xb055024010302c2030003040fa0010058001010a10381c0101440e04c40070ba6046a4a4105207001102413821480c81c0d03481c4008000e41002e000d85d4044510300440e003544890388810900b5001b10094050401c041d103da8074008620703000030311140000c40c024181c030900600c10001c00d00d0b00c00305079000503480e800141c0c100000c1c00100100802200e401c142d01522001000309050300d21400b40c002e503403210012055510460387c1c5c00001150000d0140901c2e071041003040948001510014000d54840303050300040084514075501032260403202e03a030018400c0d690507603680301c2c0e01c0c9003820100900841d41d05122038282c0c22010644200d4010307100300d50803414502c910345c1c00c1c82c00c50100742501c82480e01c81c5183c0790070304581c2d100b06c401071a002401e0b00c0106000380140c580d0783c10240d416403101450984a0000e01112803c840b104001501c01c0f03454883c5000200020501c002c0821a80100c1303284052036403042c9a074483c0207220b0101a50a4290407014440007016250740c4695941e81160307007 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 858553237 1250 858551987 858552043
    0xa0309110f130f062103081605070f060b13020918010e07050a050c030c010203060a09091a180a050606091303050f031801050403020a0606120c050d0f120c05 69
    0x19100e0038500c94000000f44162400b41c00700302415482c1c0c410b00c440c100e1001c145070f1440242a109114030b010740c80d086d0180c1c5800300000802030340100c0b03023400500700388110740001d001d850755151010f01a81010600300d90340c400080e05404149ea03a000001ea0003c0c0c00c840a042441055200403030380c40c01a1440c0d0f160850202c0311031700060801c402c01c0000181030460314010001c3c1c03560354940340b003200d80702c89004800c039000758020b85040380f044981c104000740c2e103550740c000c400f0807903400710542e84481c4803a0b100590b8000003a03c0c00400d04210f00e1a02c180319020442000140c2c000c0d4018043d6080c0038042c03014810ac054821182ca420120b82940840d070400111034102c0f0640c0b02440d03803079491403010014030460f4100c1c0001c5501704818001419800546806000d00581007000403c2c0d80b18843c09801e150640d00800e000d1020b0010007162a002c1445504ca0303000b00c2d070b9404a0a03281d903a0022000320f090038000411a68403120301800410007040e0740440602002d688a007180c80 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 858554487 1250 858553237 858553249
    0xe0607050f030a0b0109080709020406020105010b0702031f0b040905060402120312070804031206060f080a0c0c15020403120906030c0503070c0b09210a110105010e0c070c05060a0309110f 82
    0x40190f141d00340c480846001c00e92040810710014600103098401050b2620382c0000654014403500c00150300749800883c1c044030381c00c100c52103a80d0090003407400c241c842407550728041901030341106407940d80340080c0c5907071164024071301094402c1018003201d14241c0304011000506600301301141e4414450a250f100c45094010b422040b00e00380701065a941e4a01203071203a05241c4c010685030b0815000182040e0000c2e0000b05c0300c91180c880c01407942c3c580c40144225849011a400041c12076520400443e04003490a018002601c001502c2c15072641c2b59011040c84000a140c0080c5201408102d040d90604c640b402048041c0f806914604007000010b01d00a94000060400d66814011525418040181b0016421000d25030745118500303035040c03296908040c2c0c103030010500c8011502c0b102c0506108290581741400b0f01c11000745c403242070401d410382200c80c04031111aa0075002084958a40d4040c101074001550b000c114045140740c00c2c0c030030a06008495000b80c03101172041c01155940c0c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 858555737 1250 858554487 858554491
    0x1090b071502070b04031b02131829070e13020d02130906080c03060c0d05040c08010203040b1e090601090e011d0a030f05030702031806040b0d0e0607050f03 69
    0x1a1116a031240c4450034049003002201018007640c510026210b01040198103e4611403402a00d0350200361301161480d010f40c840007031001750f0001d03070004601e101e41d07810350160000100601942000d407000d642d815400708640b07507103000c00400582c0340750041da003a0b0b1401c6a001c030451605a8440c5512800324050314445803000e4005c9801240085001545505032076a21048821208034243e5030500c20700100711a002d0b003502e9008045082d10f89080c0000c20314044d5041d103000c41d2030302d240841010002c11f0054002c5411412041d00011006424005140280e000300d52070071103420f001401205003000b89400c0c2e00ea422614003001241000407402904580c00e1440100f07060040e000800c0c0102404034044030850740b0440303540302e000c070b0003e5990001e51007902c0b0541515191031007501c20740001c50f130300e00059108010960300c082c0203649005400201400403801c0030388851310907403a600280400500686d50325090380c0000001c000340d5400c103800b0700b0020f1a10342c0700d40440c1054800 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 858556987 1250 858555737 858555749
    0x4090e1b06030402150d05010504060909030207030b130c090510091107110a0f030606080c0105031b0706060906171203010614070c0504050c03040c05040b09270303072c0109 76
    0x2c0300042c15034a070312440e0304000101408442da038180407024100104804e01980f8065443d018020400d00d00c0c5114003c0b0040c0c1503001020000e00c1c0d583c64041d41040200720644040900c0e100c000080e07480a0b040000d01000d540210706803401d08607003d00b00d1080e43c03050810300d080031102401c1941100440707410903003080503212500220408942c0442c0d00c1d40c00814803011407034000080c0000d5500410a6540000c180d980181e0b5060044555010645000484c00001286c01c845034012a0082c910b030740c4071303000c0411859a10340324941107503801d9101d0341c103041d000140c2d141844414882e02c8042c00c0d07030341380310790a6506000c8001d1803020000300540840c20001180001d0103180c409442c000c1c00c0042c01809685418129681250070a6034202e4906050850125142c5058000c0114225000d018074146544003044050f100030700017281c010300c0b03000041d00c004490007440294400e00c0181c54107203d40c005600c50800000625840300c0641c0c0c1030050721a03080e80e1200d041011501 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 858558237 1250 858556987 858556999
    0x151a1e0c0109230606060304230a0c060305041208070906050d0f0c0216140f090a0e0f031b010b0604031205130e0f09061e090a02030f010204090e1b 65
    0xd6200c0a03180141032142018207051a81d4014100c40c1c0081c040c110240319640c8240d5480340c448406100103404292401407009214112100300e808450346003070001c0003528101c0701c5061194403011508042078009000182d29182000180300f42c02c0b4102c1036044103440d05003060725000000600402143c05a0010880000740c0580001e446400c09024045c1c81e09080200707644c40440a96582d800001102c5c000003503001c001040d0308040c0e02000c03241c2010784a180d0a1080c4020030540740401425451a9950b031454161200b208110900c000c2901400960b0384840084511210300c041c01c1d1145410303810081aa0078a48401c1c2c203460032640d04c403500c00c501c006148000c1da00d50003a600e01400348000a02d002600d00d60a070207490040040000f2100e458644001c05511104121045c001a283d00c0801e141038542c812402c50703004010340c050760344003150340c5d000a080c06480000c019003a034010406011052051040d04011025400140013250007105000a04404240e10a110784 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 858559487 1250 858558237 858558247
    0x1509062713060f02031008032b06030b07110c0d0f1b0e0f100f0320060d0e030d0609050601170a0609110c07090b061206040609151a1e 59
    0x65000849034940c4240140943e40156224500a4100702e40415401c0030034000081e04010103c226141c2d1080038101144a05540c40d1800040341c080c0180ca5a140d520a000008203565001b9107001e060325960742c03a2006140e80f820307441c000c400d0741c1e041c0c41280c516449500040c018455150030542c400d95100483e00c461201d8010442da550015030031030700040030003440000100201d4400c3c0b82690003850b40c1510303242c0c04401e00c880b40c00300410b00c0c50754086045141e41c03000c00d1581c44801c01003507140342041d031032010410303190003107175040c900c0c0d001160b200c00072081030040d8400b07171000315070800051030040e0008080400c603da42486052680340883c01882c039640020000c3e00c07803107400340b2507112401815040703588031694007180d500540b9408a24010b02d401051031402c002407a403824a50000c415400e404409070445a105a442c0400900c1032558085c00c0c900c80710100d950003a191a103c21124031101c00c0780d030300300080c0b8100404ca40481500e051100c4131a0b030302071015118 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 858560737 1250 858559487 858559501
    0x60312400e0411040c020f1504080901110c04180b0604090b0612150103080a2d030f0905070e010f0f050d12111c12020c030403030e0109030b15090627 66
    0x1050030341c900d0f180c01034107200780c02d03400300e400047c01c3d44000005000c0301c1d005080d072440e000320a4400c2e18000e0102c2000c0102004940c81410a942400000c03070a6806241d080310000d42143c1250802c442110080c0c00c0407070a21a94107602c81c0d0204c003c1e207080c0850412681c800c9950003006044a104038409080703880d4161080201d4602d01e100c064003400342e56100d0030002d80d03036000b1001513800240c208094404070086a141b2401c0c03401c0180740380702012929801640130f4089001000b01e01640c8070070a00204104100c0c05005203d60f011317842007035060160706034100800360000600c0a00f4000104201c0d00d17041080c2c10111b41000c5e841500d00480001200c000741c01c41e008401600c02d41c400c480200b00d09101300d085030405900e0b81c3c200300741d00300300d940180c1c00341c0300a80010790000d010070000319014440c10502181c051503c600f640b5240e55602401c00c034256010061700c42803500032055802c0041c001500420112603410368001c042c0f0304884061441060b40c0482040720000c903000e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 858561987 1250 858560737 858560753
    0xc1302030c0d0905011a010e012a0b1303030b090c0405040f0207051c030e0706020a060c271a0304021f02030910030e24040803060312400e04 62
    0x1c401c02c0c4030144090300e00b0f030901c940070309800510204c9000c115002e05001d0b601605030f5400021060311a240701269004022443d420641a0240d505069032504000501440e141a100326a5403180600c90951030500408690b9101e440c540a50080010300c0f100300f0301d101c195000c403103044501003200c0c459880301c0740290291000042443c41400c0b003501b51444880306500741e0380b604d03907020424480d590443c02d80c1c841b1030b840b4801c05a003040202101040c40368104035664035032424007500b40d00c4a0f40180406010a075490a4240300500c0240300c0441c03040390008000e00500f07201c60850034950000741130010601c10400840c0e081d042c4002034103009005a03280010001c000203c02004e4031400ba004d462030710400324403405205080219140a010380740c0345900340d11801802c907695691401e0f0182d00c083c0080d541442540746030b80080444030000c1c409080d6a803401614950b02c10016600d003101c0300400c407028401040e0595408074944000422a0440803120701e860701c031030811504e = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 858563237 1250 858561987 858561997
    0x70b0901090513050a0b03010204180203040f1e03030f02091338041d03090105030403230415090312050717041203020d0203090f01030506120a0b07110c1302030c 71
    0x2420000d60041c011084580740d0201c5e119070443c103000c3c40b010005400309800c030312840c0900c0d003400e0308040b545800f012583d03010310382c81403140581612801d8213031219020441940390703800c654030744038040004041d8103001e0009000380c6408250300300710a01000484140d003a0b415a500d00750798091011000030809001030810034103990484101c0352145000341c20988806040b40500d0602c440b103180348100c02c00341882c1c03982e40d0004d982800d060350011941c1c0e42c0050416010403018a2044c1072256094100704214814004400e41d00c0c2d01d484100b49284443c1355801e4184414110104041500c50240724151180d600e000307540ca00c403621b881080010740b81d4035403040c1800400c011802d1002080499411030098017142c0c041900100100e0780c034402d918030706400200c1c4922061895009410890f040700000300b00500b91090781111600e00841c0c0c600643c1d0007140c0b84184200242c0196181c800701c00b80f20003030318580c44814041404551441c1f0f03000c41c03403a4000000f580d038004803c01da407 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 858564487 1250 858563237 858563239
    0xb070210060f050f18062e02031b0a0b0604050c130b0a09050303040609180f05090d08011403070b0309030408160e010e060d2301022209050405070b09010905 69
    0x200c60300c816428110301890f0140c24040e0781c100c42d03001c0c860f20f0011640b154441d54070b800d0424507034595007440384c2c010038400c2c00101e00c3c59804d800c11400500c2c600c0314148034440c0e80155110801d200e1941c20f030341100f01032000180c024070700d8080402e0382c00d414140d005006540101d4191165008941280710700d084054a50611030008648010000021300102d811540d0300822183c0fa1010140c0344c0c8222312448010424020082100c0c8205506044000354101800038400c1c2941c1c0d2420142d41007140c12038410b4010343c140e00b00740d40c1c121048902501c41001410845400800401c1e139440e55030082c080b00440c080005808000c00304101c8014007405016101d022448600001c414541c5028800c1410070031000810326042161b2400c1c410b203802031000d0000f03010b0f601c0340d200320303d81441500240031000c40114415032090000f0011002a08040040d240c0f115003901484540764001044040c10442030101080002624005803505c00306801c3d9a0a41c0c08010b03502c94036254011 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 858565737 1250 858564487 858564491
    0xd0203031b280b0901050f04111c060207020411211b04080604030801050103020310142806030e0a0323160602090102010b030d081b070c2705070c0b070210 68
    0x1a6000c02c1120042c854891107450240030320740b00e000b1320601303072a821182100c19503681000500850300d940c0042c0d01982c400741400d510240c0c99945c404d46200a41400c4c1c1e14540c000500c0000c5041a1203151030860f113640310681018508180c0d03102ea6104409544501c8076171001040c540340d004c5220324103503c90000c0950b0345641c5c0e0010309413150b40894094010514401c00010154001e008481c80f0700c4140b002071907200d051446d10701c0740b00100200907402c10140154026040d90401074403050329902c8801d21240c0b4a0000001c0c262041d1410310603e540200c0c00a500081d0007075550316003200c101c8460080d800365291080081d0080d034107051509140b900200d82070116560013001d4004003030b4000d00030f461242c02030550f80d1003501c6901001901c40340c0003ea03004000f070100340741c202200748503a207000c0d0302d40c5820f114aa016008201c10459650348102480d8042d4106441c6401024050141d4034025002520401166502a14043e42003000580f558400d000b40c005c201c85e0070f081 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 858566987 1250 858565737 858565783
    0xa0905120a0206061801060f0c061503111003091a04020105070501090303291f02010f020c0c0102060127021614060412030603110402070c030209011d01050d0203031b 73
    0xd50b500f60940f046400b6501c24585502002e21010109040e11a05d031640c1c00020000070301190290503020003540e4890740d4045003402e2142040d209001076000b028040340c0b074090b200401011421040420b028140b802070000005001d80907490100c26120005041a6547d400162964460350304014000c1d440c015600c01019090b5004d040303948400069000210b62622001a0107034800304000d51000003030b140500d4409403404405104403040c400460070340106900e81c42640c1024817407400740d0700310030103010840d40e0400c1558018400000450131043c040800b000318817400a800007581074001512810b160681850300b41d080f0791020408450400007004691034550964048504503580390f0400c04040c0300340160419aa00880041c0090b944102008002d41c0580c8040703d180c61a41d02c00405a0f030f61140300e41c001d00e511501942c142c00504032440f100801608541d20030500707500b0200140e24000203843c0803000f08070148004034810020305207003400540d20414410750042c0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 858568237 1250 858566987 858567007
    0x2030909011805100e1807051c11010513060305070e090f07020d030506030c04051b0708031807181508010e031206030a050a12090e01090e0c0d0b0a090512 68
    0xc05a500d903a400707102004540c4581301404d01d01c1400b840707503648010481000c03915801d40040f4542c1c4451314001160f0000781d442c0045190920390755114000701410582600c10701c0340350301c4800c8041ca02441e00603d0b140b41e500103250000703420300980c403c150b9120001480e05010b00301050060b94001e0441c0000c0c5000345440d0b240010481c0e000300180116050007035100e0103400790500446c3c0040c0a00300681100d0b05000c0107010003000403140c04892603840070101c404200424801c1d0003034034000d81e646804d440d80c0d10032040360100c2661645c4880801c1220f540380c1c010a06074008281e070b0104210843e40441660b074295900040215440d1035a00c000c030144c000300420f0794419104807200e89545405c101901d03000d03401e2004d02543c100d812050000350782d0300d02e9000c105000d810103007652501c0e64840c2c9e01100302600704c2c0003043d50b9149209141c0e0420081d00c402c6c8271040b5280008074042e40d8401e000e035580540408184e81e11200c0c07400070014240b040507030310b5100011003500c07150301c45 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 858569487 1250 858568237 858568259
    0x604033914061012050a1a070206010b04081c0c05011b0e18040f0f150c1106040c14030712060902090c070c03080d0b03060907060f020c03120a0203090901 68
    0x4902221190340d4094140114080440d02c90b104541583c4200022072901030144240034810070102c1e294021119100c1c0001c3d4248803903d5040baa40d51003006515060341d020746401010303004680e4090f028041003100079400500514840e201000c4a9800d02e442c100503194850030b44002041c6509100c401a50f641c07240441420800c1103589599818481d901804200a40141401d000c5604400003030082a80c50f04208002e9204080800090f1016207424590f030b1081e00700802a0f94403071030070b0884594400c01d1085030b03010740b40242600d820300b55228200700c00680314160740944001c0f14104582e405000140003401109010301500d0210300d0304400409507036008034810001c08004c02c1c000200f0100b91507800b5403281e032645150b07096448006c0c15400c00f450140d107032601d40e81c5d0012030791000e10000d03000e014008003d002e180c1c2000c0001d4080d170b40b215544401c650269004044a51f40042c0c0d41000a0120070081d6680d500c4140890231403003006002500b011040000045540b01c0f9 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 858570737 1250 858569487 858569597
    0x151b080406050a0207031d1504030b0105041103060f0d021309080306030d0c030206011a04030210021c02010209010e060c0109050d0903030e0406050105070618050616120b03060403 79
    0x510340402c00c41d52001c04000880c05403000142c00260300f503484d08181c030401e00000102d950001c041603c90040b60003090781c554000e4008403600d4601c54010000350500c3d00030050307402c262542c520700354505000424403c40301304501038441c08003400803c09540714030801c5100503594000a01410035a414450101d500130346440303000b84580043c814843d442880307c0b17101d569150340078203e26480c01d803d040d0141040030104c5954001088000016500c1c0800c04105030b0194028001e07403c45030744640039601402405900f964010011486a6079100c0d1700c3c4103d2030411940c1c90f03200e240303044866005041804000b000e910511204894080c0c001410000301c074460340e50b850401c20b00b40184029984180704030707404282c080c000f80700066501d801c0315401c000c2c3d5260900303460b141a20b500c0c1c54881e0079038030b58001c0340814411180b030399444101d0351108106200203101901c00e030400301e6034501000344040c04208a200c0f4003200c4051254030080d5410761003003040c20404442c0c880f40004040e03 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 858571987 1250 858570737 858570743
    0xd02150307091d01064401050103050f060f060a020102130f050a080d0e0f030c0a030305091206040b0705030c0d2301080d0206010b0c120708070b130b04151b0804 71
    0x40110004440285008a24140c61056680b0060084441d001e548000010402200d880c2c521b8100c8081e40301540480301d85194902c1d200100e55403514001500b1160041c11030042c580a210412402d626400c110b259030384415500651342d044a124201d0080c021410514865038919900007003090021814006230ba004031006903040341d075060342e6036896003041541004247d0352500d4000514102d10b090400b210302800350b8110010b120005408c1c0ca0703c0c1e400c210d010a6001c02d04031180d080180d01103207001d03081c200406003410540c54100415500500c0c0d07800b001400000102c103100240c09580303009121640c144440e1078880300c2401141c0c420406800d400c21454000524490000f81034617003603860b0b03000b0340241d9081c100964040d0341f00e1020034580e0f20680018116400807040100007586c010310b24680c036034650703180074050311350068052030041c80f62000f04400314221404044c0c00581c40700d0340c2d0f0500300d0a0138a80d07000c3c04203028280e03480300107400c6004c02c282d00504141d00c6a84 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 858573237 1250 858571987 858572009
    0x24041a091008040f03030902060708030f011404111c0603080a080105040f0203010e070c020a18090c08060601021209030a2906120d032304150513110d0215030709 71
    0x7080703503021120800c045401070139402c44000d000e00802c0c080d5220800a9001401403458036140e61903400e05a80155801d200e2261410010000020b00100f0350081000445040c08540003100125090340150704000981030b40d040c01850300d50019501800c01140d000d9001900c4821504002d4460300f0248209800365003802c01e01d40d404449d501c00c80741a00e0344000003c12580350004101c910a0b03044908a03040751181801103440600301c000f01c40c1814041340c0124002c042407a28404c046080d0340004001d0b0b1194041c000e850f078000c94107200000c4c0600207180c8803144080002c1c0741409403c405885500311000ca01c140c8111001d02c00313440f034905284000760340ca8801c18090b484c2550104640150440441c8880003031094005d19042008500085080c1004103909808402c00355001c441029800010b0702807043e1034045e1903404050a003064440d0304030b503112981c0c1d0310b2050745814030807072404800408650b00c0250200c3d0a12290012946a1130302d40c5011304104600d02071611061 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 858574487 1250 858573237 858573259
    0x80304030807080606030c0a0e090a0e1204150c0302030d05010902121e01170a0507170d050408070308250804170303060f010c0f05032107020c24041a09 67
    0x24043c01156001c1c200190906241d9660402200a160441c10003402044480e022030b04950f90340190040c025143d60000080d402e071130819003841e1010807051a8070f00f02c01071200300108002420072640c134081c503040040084000d40b604900794451469904000d0b4504000440e03801440e0b4080d0030300300140a100886900d4040d84e04902100095640c070301500008014451114203025014001032414100d60440581e541e601d0f0900003140c00c0550640b1004c48803100140d400c0014540a92040c240039203094104440580c5508043c04040c000c00c1c4001030038842071200c0014550080100c60743d0a54901452526100a9110b88242e85207481d80000b03403506580003008a03400758000820341c80a54441100642c1c012050000a46110071510744034000314805000400401003240240d440340e6050300700b0ba0700707404d07c0901040219400b4099011094407000c00007441e1400d0002d1800502c0840c603460b82c128802e9800078258003005620f1010340c0300241000d45074030601201c0c02c1e460380d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 858575737 1250 858574487 858574501
    0xa0f060f0f1a040c030f180204050f0112080f0c2e02041d1302031005040201030c090803030f1f06030608061608010b090604050405190c050c0a0b0c160803040308 71
    0x141e1400400402c0301100000403000a24041d4440b0301c3e020580d007004940303058102a220100d407001c00086d00b24081c480621000c6181c00c0c0b00d45503101c151100f480009504043e400c5c1c2c803103241c0b080010154000098492843d80000046d21007280a15003200c400c00e00c144078130440d80f515404080469201c080501070060b105c1d00903134047d00d040c5025a080100c44a0400302d0b101005440350700c40900d00c0c1d0340c64000d80c4003401840000ca070030b0040824641400e10004088500010880041150561040c09241d4000c400c4940143c4050000c8496466100000c00300c104050b140507010000d000e00090804d4041d00070780116182c0100303442e00d641d542860201075460f1070611400284000005000710050440a010307101070140606090507102c1c404102102c5040c1c0b0316840c10070031000c09442081d868010a10710000070714266080c0311035180b800703642d18800710001f4056260304000816511486d03054800081100e45401c40360340240c10540b0b850350040d6010b8000524040000c0c0301 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 858576987 1250 858575737 858575741
    0x20a050a0b090105030c0f0f070c050603160f0e120a1b120212010b030115031209031211150a0e0d1407030f2007090b040b030304060c03020a0f060f0f 66
    0x4031141c81c00da0510340300d0030a004450a5000a2403007000c12001d0080d01d1000c68050b01404060003011002565007500e42403000c004c0c245503001c24841c1500300204200440151030310044100503051080c0001003004069800d860416600d5411000085200b10800300003e090803515010b0b0985034104c1200d00d0203a80c030f2001c603000f2a000041c607442a0300060415803404203810441100000c0d0041d0404002401e40d01001044029504814014402d10241051211405029040c02d04c0c00610b1559070400c0d45800e41c001e0401d108020551031101c480600039401d055019114500c8607151103009480102645d4480e00100d21994590304002e500908003c420800740303291060a01e071107a6030403507460003181c41c080b041103100d500400701d05600510b6100a010018058107606042603000c408031111016841c0c4200e05240307000c411600d02100311000d8906501d8a1200c041082c01c0c16480c1541400c0d0007020140220311000910846600000b0300d0b801009082c0305111649000c002 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 858578237 1250 858576987 858576989
    0x1a0c0418022706040806010e10080c0a03080306060d0906020c0d0c080306060304060e0d0f14070f0f060e030c0c09070e061c1814120c030313032a020a050a 68
    0x411a100c000d40c074041c00c50602c20220314900700404141c40c1c56140c0009505060080c0c4c020040551503406018060030000040301c06400d401c00108a407040074130000740351024611018082d40000004640313940c403030f801190f401c180034007410301082d00c8a181010081d4442b007001d01050092000314440b4503c16250380700c1c2a40c001807c0303070031a164002000f100360300142c42264a00c1c0d6a40b0400e082c610203001c4c07501748800030340326004c4c000c00c03041d401341c983c01c00d0340c00345601c000080000c4070008540304000d0a00701d8101070510003102c0d2a01c1c100b4010154050400154800410104003244000a072800e5040c4241d0f40e14405455500050301c0c10710743e00c4241d0764131003400e10a40110b0082c0400b0400c40c7c807416500030a45801117018000400542c0d8010b48a4100c82034603070600301c108020f15514020112020340c90f00c8080744126449000280420507281e03903144010040c0b46c4201107008040b94844002c285129500700c040c50306c814503820490141d54002800a0039190040107a0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 858579487 1250 858578237 858578257
    0x3030c0708151f2d0605030603010e07150e0f0603011e080303130f020f10050a0206100b3c03010305010c02011e1104120c17071206091a0c041802 64
    0x920043e00305507007144d84680f041204c1003903072a40300405548441c8441e11030003c15003500d81550306e041c82c1081c103081d074682c05034129481e40006e504002c442101111165480081d00c1c101c8007103010040010381050303070b0b90105940001c010001060b540342102d0599403581c0e0354080001c050b6564181d1948a005c04c03602400300d0356090400f07501050407405001082403006103a01140b4640100080d9119481d4640400084000c95104a003035010080690040a40710300001180e180404035400c5224415820941c040481054036074030707641161213040019074001e50320424414106049a9130800d00c4240c81c90342c01d00d03500201060043c1304241a03040780801c0c1a00c01501032003410040c18026003404501403042100044c0d070030700850001500e6108445929503240340c40351007401c1c1c03550344a07030304000c0d00803030810015000007441d14182103511401c042410003ea041103030380004100303150b103441a0104100b10360011234074014800ea4543c000d82e207140c0100d01804104034001c00c1182 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 858580737 1250 858579487 858579541
    0x609060105010c050c03010903110f0a2102030f0d140a02130311030705060d0c0311030c04031b0b0703081609051804061805070f05010302032403030c070815 69
    0x144074952043c140026214064011112805208030101c2d0843d03a401c5010760004400384a4070b58080410b0000c031004104a90041030400ca180c5c40b01c0a625940d6118070002200308210542814000c6c420303100581a50340b00c60384c03201d4044846a01038605130310344441500c0d030b42c400680d581e0401d100fa15401c91100e07030300404a908540e1484034120011485c66410310600500041d65558030004180540c040c0b40301241e8001e03c648003030252114188212440c0d1424010008014801170960341203e410132040c040042c184112094030303a05540045002c0c0710300080300f4041c160003150302d500413080c1290940c403003042e202040b25141780b180251a4400451810092854034800115800500a0f900092110400443d1a500038400760703040340c00c2d400441040040c0409050134a00901c02030a00707502e903281052480140c01c00d40c0012481d820141ca10300d5101d80c400b001500c20360b44942c4102d541030ba03191060140d540c9080030a10159098020000700c0a1300340a5098495524050507 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 858581987 1250 858580737 858580739
    0x11202040c052b060f1d070302070314030a090f03050c0601080d0f08150603010f1514030a091a10081e0a150e030301090f0b0a0e061009150801061106090601 69
    0x10081d03e4104000703d2240ca5070301c410020540766a18a400e00c01041980c68484081d4151005000300000c020030302d41c141441031000b0341c0403e81120010410000171300140d130f50b07a038076180d40b8401004038020180c00d941e01142c1c003508154100d0002c0070b00f82d000000b100c101d0713a030310503c4c00e60314980c02c0207990014034140d4114030418026800e00d5002079410020066494105010502c01d41003640300c10454003200340d08100c4000144400e0804540a240c0b1400040e204030794441280300c00341c6145042079441c1c1103a8284449a00c1559140016502900383c40c24800495200500d10f0300412055000385200210200c909201d00800d6002200192641400a40318070750a0056880e902c01c3e0692100b41d001007580f414402107018020005001400001b03400d01e0200726038803009110b008000c07240080c44900030480356154800021240709404100c0c40000b00c45907200d91380f010306000d030560192210b060700000102c0c141d52855544000751800c00d510556102001e592403126500303d540 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 858583237 1250 858581987 858582037
    0x90d090b0f1c0902011b02060304080f091801051806030703060b0109090204060807140702150f0c0f0c191409061210050a0f0603051c17011202040c05 66
    0x40c1ca900440400c5280c10010040c0c4041c480c2508007580e2024541e80c0d041000466030809001007401c41da074841a03448000740c0e404038580d40310141c40035007078140200d84040204000811142a1a0050401c01248030042090132140030203020744e42c030440b460349410300004088840c503881000000d0003008101c0c0396071940001099104082d5040040d520008140b90304540020001400196210452440e15040003800b03040c21608452b45403504124150142c2d0f200f0a070000d2480c06000b105070b03a5031003400a40d60a2280002615990140501c01c8204074030101d0071110041b01640c40901e01c0020380841310039000c0034041c000c402405902401070300d080c2000c18542c0400d0140c013902004214601191400c03001c5516641000d46500c10000000201d00a004190dd181d1106000e0242036a0380e403902e56108102c44016403018620201d100c922a1030645107112201c102c420980d42c582c0c1019034030056001069000300d04000e10f4a081c9445001252400b00d03074003072200c0799070340b0980c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 858584487 1250 858583237 858583259
    0xb0909030717180a030c060314060f1302130e040b0f041a130b0a0209040b0307051e0d02040c020304060815010806090907150c0309090209151e1809090d09 68
    0x6403410f08030b00d4103018898168441054010185004035000000b891906c80c008080e10040440c100c141c01ca03c109000603070b00c4089180d6640311044078590300145508808900034011810701c5406250102400100ca03c64020014055401402d000c03005075941c003c0741040020982e0014414840903a684088040351140399400c95031000d00c012061005840300030050009840c1c0a000d2030380003403c240246031600c5500d94002098010b00b81300c03450940040c0001010000058420100000150155036600601c10b10168020410003080418000082d9260841c0c000c0f6000b10310034401207960b03101800340b04410303014165034401d525501c440600c0000f40f4060042c903a05c2c8038015000c2050010304000325443c80d00c60f0340740c000d600e6481c1001030842c0c0250b407060480e0f5204001203802c80d212030707091000704004880016650484038030381c0d080c840380500070000d030480d0104104040801203007200d0f0403003100b114013203000d8591486194469020720b03140b40100d040940e0410480c1700c04 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 858585737 1250 858584487 858584497
    0xb1305060f09130c021902030727090b07080114030304090c0c140105060f01030905030414060409020d0b1815090603070f1517070203070807020f03010207060b0909030717 75
    0x100c0d11181004020408203100040c83c0d20b00400d680d0b01d45010001c030680c1001504c0610301b01000000c100d13805900480d450b01c0181c000c42481c0c0150389241c4140179000740c408090408850000c100e402c0050a08480d48102030340c6040000d6034a2000181c5940240d00968600d400103000e117240c5450035126034010140101d0070350130b02c00802030010102d1076060311241040f51550010415140100400c8140101050302c00c1c1454a800c1203200861000025a020380d414040c03500076401d000c00000303c00380501e5100002d0b031400019a861141401d8010108507001a07801c0c060403c80d407010000200001c03146400000b03800188000c0c40d00d05401800d811400c054152490307070780c0b80c58051100c00030035004401994041040c1c001d0b099402542c51001c42c1c0e00c43d80c8004581003e42000b9142e100700c0034050035448010682209655800700080c02505004001715507904c002c0c5000c401500341046041c0c42000c91038005070003200d01108849085612202d10640522011a84910343d041 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 858586987 1250 858585737 858585757
    0x8070e070c0b091b04110d09050f0a20040207030507060c090902070b0910060303020a08070320010912050c0c0108150405010e0f1506030a020c1221010b130506 70
    0x91105034001241c10300c1c250b1030140807060050090354215500901c040700344480c2140c0900e24218a001c0c0d06920f50742901c014818403400420302800c1401d2491403d0310a90201b4407500505140340104500190072002021203c241036103030a0000381044100e0180600207808110b04111070313400141a03a00200c031070306841c00d0460106403107801120481c0c00455044801320a00c0b4144124a078040000c0c027012440d1840902c002c81c21a40d0003900d801660b40001c10081c17001c1100000c0500804c111100c0f003408098800c50780c200c024100c0d020341031044003501c410b4441c00c03600d0751040c4200c00701c4649030764078001400780d8100d000044030a00710007442147c40001c15030010041c4c0d600d5024960080c0101030200b101400d00c0c403409030f400c00d0003a0101080c00c4090810321241e445510640380c0c0030240e207400503140c103001e0000a06007013201486540364000080c084103107a242c0e03644140003e1005000b074040c0c0c0e886800c0b01c0c00700c0c89000f072031602c07039203030728008100629001d4000c00407250 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 858588237 1250 858586987 858586997
    0xf0f09270f09160b0c120406050c0705190302100c12031b030606210605030102342301180c0603140c0301120224041a12190b090f090607050408070e07 66
    0x403001b00c0f00e644c6400c15081080051800120b0071030380803082000002414049840c91014889494200400031075403000034003c0301c65441d211840e40c0a406c601f081c0b5500150784001e417a480000080003041032244805081304000e4040300ea0078403a20841c01600d840380c4554541050030f813060001424054102083d03d61290004076164400380040c050503001c407414600054034900c6c8268035144400c52248100400c5228000840c407240032100000701c28203032125122450000b114090b1204e0b075600c60300c3c2d0403504181e9041000152036582210340c40e6030304200c59401200d41162190f41030318a020f0302d220500050111802052141300d800d4801040c4141c00e801c10580c3c40b0003141d42ca103040040c00030108007089070f00940d841805204416418551601c030904d81408280c65001d85003640c00c12810003440c40c003d0990b8442c0d440000001d00c80c0c60f880c548414041c0c00c0d008201c0e41030013a03000b0f51000c522007034098401d540c291180c05019181c52410161000101e107002000401084 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 858589487 1250 858588237 858588253
    0xa0c0b130203150a05070f0206010329090a0201030c050403050a0212032101081905030d1e0e0c10020a0f0b09070504050112060c050f0f09270f09160b0c 67
    0x1a508100310824200d0351810f5801d6490b110f00100e0450700f0050542c011f01480404120505078045035044c1074030f502c00e04845417113640400607110501d00400052001d1180780900c000701e4000200728451502c01d07a018071410036801e100700e0300c0d40102e1000400c00d40c00300c5040ca006180c0b0103e411a40d46000c81180e050514804140200383e0502e2510052041441c005100c8007038140703d10740e82400100101403001030b455036003559034800ca01d6159a003e59418042c1e4103004050b00078600c50140c602c0610652032220b2250392a00a40ca015501c500c0800102e10701079800030464000c220b801051001100e1041c0e16846280c040040c60b40469018844000c10180d440c0d1103442e001e0b00c00c0c030b584810340e102c1c249441e100b200c211038515130620905002213a1082403540850f000a810070054070346841c40c0703c02043c07449000312408180c0100c04110001c10701664000c0310b1080c81c0b6010540c45907281c3c90007080e1900b1001ca8840d0500d030384a0307001d03c511040c80c0c005112041506048603501e03 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 858590737 1250 858589487 858589489
    0xa180b090f0103030e010810090510080d090f1e03083016020f03030613020403060501031a15010c0b0411030a050106150203180108191a0a08030a0c0b1302 68
    0x61030071500210501c114500500034541e10010408410000b806c3c05d007039604000203003c105002d5445800d04440e11800041c0240e140142008000d080c1c1500710b880c8102034440191032030415000d940c0e0300e0b00500d0300010b06a0340303620703007121345104201e40c0040080c11a06d03000040c0d400700c03d001d00031211500d54014040304007140e405003800040c11000107400d041450b019941009141d501c04c42d401055400c0710400040100c0e500b20300d0484542c098407000b90840c40c00307805658000f910083c0344c207000109200528803400380c203000715460b016081d030b10a200b00c202c0b40f08000c596030000b81100580c0c070006022045140d0020300500c0402d051032010710000e481c2c601e80800803202a511380b40200507500f88447c200b4881a00c1e40051400c1403084600403031240e08102030107042169100106180d91300307440200b05081c0001e0002c1c050609210b1140d0350b0000d148401500400411070001914000802615540851035580040c0124262600344480d031000c0c1c601c503601030120f03104c4001 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 858591987 1250 858590737 858590749
    0x2090117040506160f020606012114060102011b02120d0f02031504060602070e0a150f030809130603030c020f12150f010506040302060a03021806360a180b 68
    0x800c9202d81c00030000391410a1101e24034102248082d01409442d048000c0c42035004264141c0c4071000386400c01082c0507540001066200700c00001e0040c0789002a811641500301000c01c0c8150001e800900c494038200b50824010f10b0301c55540001a0880c6c2c3d440740c2d10350314002c0182540312581c03402003604a11142d00700c04991055801480705a840004810710f4141400f64400078643e078009404040e00c2d101113044240001030404850942d1001c0341380e580001055a01c002d4003100415146c11a140c3c0b400c0354807a03000c00c4503588528410100a01520050300a00742941d9140e0740380051240594280080300c5004544d1a9001c1034031410482d051404100d248050003071000a031105040c04006c1030050b100c1030b008035000b03110400c400e00c00740c1c64002c21105c04c0005c0e4a0b00503a109141d4414410b4841001c4175140e00c084001102c40e0b07210440514511a0b07640442001c5000c610b40c0b540d08000c80c08000001e41000d6a50400c104501e012155020086400003000c90900500320009007 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 858593237 1250 858591987 858591991
    0x703180617010503010501050a03110a03060c0203040306060f0b07060221070306141017101203050d05070207080d0e01030908030a091401140a1e060905012d030602090117 75
    0x30001d81e4001100050340325103140180185030a4008010750b50428004c683c0500031400042c0404066201048081d1103c034041300045030400307810480c922100344003d440782d0092006031071450a10b4400300301c143c510360218003210042c6448902e804a541d032110061f400c2041020807840c01d20f6070080c102c0c255808114850412917800188440c00e01c00141203058070600d04d41d000e0781b265a07420f114945c00c01158912508140d244600c3d90f502c0d0442d03080d140c2d24071740006200d050556aa0420550850043c00c50350300000f4041c8580c2e903564904aa80380801d00c501e00869100c1211382500c0e9001e004990b02290040c074001c02d4100c4662110545a40241d910400180d5916112414444040e403400780d49804040244404950440b128807038400213410400410790b1200d00766100351052101e0421810000703402e00415a03200c1ca02c00c0249801d02c280540c0b510002d80410b589021111880c02c0f802440c81c6180341142503883d00002500002034450600c01401720310064101c99011440c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 858594487 1250 858593237 858593249
    0x1a0d08070b10060f03020f04050d020d06090501020d0513050705190801110714030a09030b060409020d050c010908030c060f0c090d0602191d010807030b10020c120303040302070b070318 81
    0xb0100c0e51502e0002400051107101003010180f06110000b2a0402c41c0f00300c4040725801c48000d2544c0c800380c0000f69003035801d01001403c00b803070810540100001034014100181e4513001c01c0190f55540d030300322010380c038100400400d280c000c60014419490502018014024008845110151500c182900b119443c0d00800c2420300e0110306641008103140c5041101c40c283d102460070104425006070440c42107000003401460764600141803a221507010442c42a0020420010348029080c001d0b1909203c2280c14006404010b021842c84c50010031101ca8000c410001c0a9a40e07034004614007805c40a01002a001010800c031190750303560801c00b60005005a00050b524082c450390982840d2030358601741c0c00d04c41401d081e160200c02c00041014582c031b080c00c00070003596411400301c0040c126132000c154092504192010055030000d03120300c01c0c110580742d880224540b81400f17943e03808202c80050059010380c60902880740007074090001548282000000e01c021100c005000c00b9440d0410 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 858595737 1250 858594487 858594511
    0xa030c0c150207030507060e0603040f0203123105151305030703050d0f02010903140d060f140117092a0907050307410c070906181a0d08070b 62
    0x13070040c450188060001000a810301008402402020880354080200f0180180c560024081e0554500388110455400903460060b41d803142c02d0034041c40c2100722003c81094002154107030340300f1001151002d0640d40010300000d40420741c409013080542c4040d10340e000c2c0815440000036141c41c100700c1e2801961050010f0200f030810100000c00005440140008581c10642460046604001d00054201da154030584d600c1c00c00d946441c0107040e10b64406100110018800540d4441d2203a0707402d45103800342c0c0d498602c00c0b94602c000050b4401070300c00c40450740024822180019510640403140107284c2c60b5a000b02c10703064002002600d04441c0c2c1c201090780007003081010382d4014880103400c03002c40540c0c0b14110454502080884c40c6118410000b0412481e603100181040c042d0751030040345c10110b60981e91146030320b074050001e511454141c0c0c283c03ca00380c1c3d90b14102c3c1c0a4420040400d00d080e0801c1007881041080f005000841914400c41c03c11960021910303840c3c45600c603156040300 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 858596987 1250 858595737 858595739
    0x4060302070203150601120f150b0d0b03010510050f030a050f030403060501170d0f21091b030b0402060d14040302070623030f0907080a051b040506030a030c0c150207 73
    0x14507003803080041c1e101301e1008a040800030b043e80c0006840343c460140150001d00d8034246000480103200c00d150000a0380c82c02200024001c180d0f40082c08042401e40d002c2c0400d2a00750141800d90310140c5201c84501c0b040b8005200508000c180d0390000480102114404403407900d039142000c05524413280d42d81c000160500c01c3c00350034040d1038010884864556115800c0a0101c0c5e15078a100c60b9890403c905045c00c2c806281c030560348402e8900c1d03a5203041d040425034592080040c129000c007100e10358010611880c0300c02c04180d00f80f080b40d0300b05003140c1c41565154200036039031b03000c080c8004010341e44160500d495805400524880c9200b17800400c100c1d418100060302000945510304860702118030301d4071041c21442c040d244c000d40d0404001e07041e5110340000e1424040c06420091040c8079150811050150000d6200420314001c0d00f05031280c2510014081036a408644183d00b507400120108002442503444004450282c100c1004486d02d645000816648101c220001a404070b10 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 858598237 1250 858596987 858596989
    0x40513090c0b0408100c0908070806190c050a0309060908030c03091011070320060c0d060603060b16060e0d03090312020a0819150b040303020c01020f0309040b03030f040603020702 79
    0x440001038298a40c2c40c504151400c40c0c80340da1840c1800d400719610f0345403030101462900500d20500580503134001e40f01d00300c2c0c80380a0305607900c070225201023510720b0358036558949440a1040b4200007890303555503481d082d0204000e40103031100c0f2404032141596107120201082d00400138501030b448000c8034550324100850058a440d26071021901da06190081c07203903034944a030044803035181d45810701500f89805505003031142c940201040080380030345020422300003900f200401e2103034594107040000700d440c1d407821011292140500e12612104000c0184007007910b070302003142c44e44610f2011400907940c15116060040704400382c1c003c41d490340500360425400c800d036030400e403480120840c100315a0b10f000404110024000b0801c0b08071200030240762207910342041600d0642c0c00290810316951f0441e5040c2607009200580041c0940000b910b001c2d0300c04590600030211000043d0b0501e41b209080100600d40b4842d1140d25220800090b0031065400001c2c00013008980c60044c0c981e00540 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 858599487 1250 858598237 858598253
    0x203040809030c150d0c09170106050a0f08150c0d0624050910051e03041b0504090c051012050f1503120d0504060603050a0b1008030c030711010504051309 68
    0x641c1c4201020740791101c0041130301058800c0040305c034101145585c115074081d500303a55950811410601c0402c10415001b50540048003219410340b0340e2000c6543c0e814003190303400c070b0f50702510440742c004564011424040444298200301001d440f43c2c1b8100d0300d001d0a01c02c440d8698001c640c2160100900e020103403010b80b041030340c08481d04100f4500803480b000206880309404101080c0b200128540c1c01c0070000324000b40143e9a40e039001a5242003900b00003111002c040303110809810340c2c1d9004501414580160071003250300003981c00e06941130004220030030840c2070f03100081200c208074603030242d4600d00406008224001260456007440000c0c00031b203441c98a0071034080ea00c980e00718002038000c0c004454141441880000ea5910740c0d01e000f038003a000990014002c0d21501860070b0603c1140c905090240c05511001c4c41c0e040d41c0c1c0d00d6025180d0046003890700d010b81042c000800811a4103414600f102c605151a61034191264000381d000024500c0411880c0d41d1200c6c002e00b04513500c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 858600737 1250 858599487 858599503
    0x1205060f100c1e11091e1801060b0c21090409110f030706080403050304081b030d2a21140702010b09240a03060c020c0a0915060809030d020304080903 66
    0xe52441c264880d40b548908100c1c0e112018240d018402040000301b1414034840714170181380a500091045040c4000c001042c0d00a8880540b029440d040001800700c220000b21121500c4030b001a051a80c02c07031000304000808200d00000552040003006896500d603c43c402d48180700d1000300c00011b4030700c02440011403074680c02d02d020381c0c410402400581e800c01485d952069051030b100e03540741e0703c61401d00860f000d00005030170199104411150386410103c042c100300c103041201000100034a154912040d0312a550581040c101c60441651481c802d6090780d841a00300c08401c0c0c2c3c01a54128540d0490764031110001241c0200310500c01481d9080c019088100d03411035051025087c08418940601c0b00d42c0d10700020700020240403801d03a01c40e079001c0b200030b581002d020041500d2598001e901c955820b80030324400c40320820b0103d4810454800c00d01d514500d008040d43c160304148080d0344102c4040c014100c10312080c00410030384261070006620030351048070142d0300c90034906c0c01d05150940c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 858601987 1250 858600737 858600773
    0xc0203012f310f03060c1b0804050d110307090c0f17070809011803031a030105041205070c0f15080c19051615091406071205060f100c 59
    0x104002c06101c41e4181548034550b0552020501c181c1207080940c0d201c980c60b26444648004803a034000014481c41d0740c00b030a440d01c90703038891811302024025401e00400c1120001880c00070107020070b02c940d0400d6098031140c03074811101d4030303000719400000a240403110f40c4061310b40c0742c50f04600c0090036448046840d400d40c031814a510a02105a0209042c05000305100c00308440d0f4000600354150035084514082c4a129040b01c11403c04d090040107001451f401d5101154850652501810148035851007144c0003005421001e410b050100c0f040c2d4029903066601d0084254045007507940258200010700c020000300503082800c020140c03045c240184614a00b450030700c00c414040a03484821a00a002494041e98401080c101884690000ac03c05402013102c0302110b0391a18170356005050540c0a0380c001d0002607101101c095a800d012102240001c0d040c2c050040c0c8150950400c1d5040303200240f03800c1c210384410020800200b121032615001882c0c5021000a014500030f44040c4241 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 858603237 1250 858601987 858602081
    0x71e050a080f01240519031208060f030a080d090305070b0906090c061206010e03030d020c060603071205150a09080f070303050a11120a0204080a0f03020c0a0302011e0c020301 77
    0x18643d644105007013603803180c0da00510980401003c2e201c40081d2200c051580644091248040d14034010201d41c000c441280c0a42c6015208101514001802c0300400e680081c03500c1c035026901440340003811000d0740803000d20005001e4140014265490305209001c2e850040185140c5171300324614000090b4005070041c20200044556503c90700e60307044e0b20480c03c1c04d02010300c5401c903020928500c2400e5100e481244042a011021030780400d0442c080c9074210111100b5a498061091000341c8504009000741c0c403402c0310000000d056540c480d48007900d00d10010b0422003a4440c0da6030b980c070031500d03c50000e50019910b4100354040c400c0c0c5400645084003008024200c070302d1051a071058013018050b58a940000510285842d01220080c209090540c1c0c0240e0302c0d03141843c81491480d00460146c00713010842c0f003e500340000b140044030b0b0140d403600d1001e4516080c400555651003490820480c06500300c0015031003d0042c0d04032001c640c0c81d040200300115039030070f0000d180c401c07040034204 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 858604487 1250 858603237 858603281
    0x140a1215060c110405150105030603100203070c1b0f0e0403020709090308012309130809040912021b0a06030b030a02221503050c010810030b04030804110103020309071e050a080f01 79
    0x2c00c2c81d1b80340030380c0e802c1c00303003080d030342da516864002446e109451441c07030125400002082039855201d152401d005100c1c00c180c9040c3c00c0354925410350782c00f050180b0390184074803100070041c002110b504a0340050090050b64621a220440380003034a103002410b8020a91007c0104012000c08440152084400070200108060389000a00c01c1d00003070400d1041c0e0125a00150621008000306c840c42d01000304104441d0f6400c1c600504c80000c1c40c248400540a440400401808400703080c2d001c5d1000200390f40319050418070300340d000b81031203001e00f03425108000120ac01612040d01050140e00d038108001100c0e50380314805030695001081a20350301d1400340041001420004001c0c003000001d080505c0f880c1d89110700c154102c10960310240c4542c2c5804280014142c0140074540904e005240d10b1141c2c03c9080c00540c1070b440156401400d50340070300e504001c0040c81e50443e95804c00c40607001c070032080d5250001144152280c0060656402030308400e4140c0000744030706803e84a6481000c00c0032 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 858605737 1250 858604487 858604501
    0x230f27060a020d02040801021b010b090f042603090a150903140d0908030c0c0d0e03031c0b0316051003270302010f0f020c0c01140a1215060c110405 65
    0x50203014010100d142e401069048240e50306806450150822000071925141084482c241a80c7c100070071541c00e501e400340c845018101391145034880d150540c6901500d8550ba40d403803101407a4058074280c440c0c000d41d040348180000c1001103003d26500401020780170102c0c10101511007004440c6101c0b0742c80d094003400040d4000c25481c00c3c0513100c0030010b0300d030841008204d02411403010000c0030b10200200300b2024400c2c400c0a010440d000b44119600d00c075060005a400c800c05955455040d403040c400002c210090608400300e0115912020481d401184c0100745004003010301005e4105080c401032101e414100c1e401d6208150514003401082040c0ea0301c83e0075511001d0601c0340c100c403a010314006150003500700e850202000d1508110300d90f62104041c00075048032210514600443c1400100c030340c4105803529208000c6840540350021045040c2d550300030b10401d203900700b40ca611803c00d0054450007554001e005649508501001346e14240070442d8025440301e00c07603032504c2c05200305 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 858606987 1250 858605737 858605743
    0xf0f060102030c2a0415090b04020a050414030f0d261003080706022515110a0f020f060108070e0a15060e0f09010b131a030406230f27 59
    0x8448071504050781c180c204980c004020211340241c1d8106080c80038200c1c01d4407a00c6120b000b210300c100d108005030303904c400421003030380308000b0a640000d406001c24407589000390f84114036034030010210f0700b8400c40e808140d404d010201c5864404140303880c00d0210780c210003002c1c0c150442e10540084590b46000d83c081c4c1245515404054512b40010908004102003641200c4102030942c41d141c00d00d644030303150303905488082141164244903400301148a03594600a860a003046420711600f8504030320412a0700030002000501148103100b40000e0b558818882c2e2400303440058040c00a86003007802c8040c14280203480100820b207004c003c940c60086803480301040c0c617960300e019409044d14000180d400b48400f40406c0d030005801d00000b5041000e0030048ca0f010081040560645995418500c1f4100f450301480c44062410000500040d0070340d0310000303500784441e40281629034024803200314400126031107004040c51109001640204200511140742440e80201c3c10318941d052541e1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 858608237 1250 858606987 858607003
    0x30f06011208130e011e0501050901090303030e010908040905061206191d1b1c150203090f0a0305090411030c180f10030f0606030e06180a06050f0f060102030c 70
    0x800402c000c224005045a446540030091000e06548001542c4a1141c00548584130100c07101d00d62107142c0c0021107501980603204030790740503110b010f401c80ca591000d401030110b80c00c40d4030003135580307480800029140d0001751001e011001e0700010585001410b0052a406c41d40078082c030390740600c04101c0d80800300b0526110145c0f1004000c1003806080d039000c0c0c451255400d07409042d00030341c000e0032017030181100d011580d100c0454850600c5c0c5444003111407115500725014003c2d2108001041400301c03d0b8000b56000300c8460708458040100b00407060514030245411400200c1c0020092054030f441d0051022000c010500c0700c1c510f00700011194098410340310a0034040c012000d0f50081c5541c0c80ea01c074600d160014150408402c02800c005004140d105004110a440c2c003001141d8a840f074400d182038201c05030004d01840c0c4400180c05020510030302001001d1082e003c0b200300241d000d006030390242c002801c1450b028280b0052a044038440200300c5811580103010040403810001346480c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 858609487 1250 858608237 858608243
    0x604080c04110f07060b190602030a1e0504050111030712111b090a090317130605090604110d05030918150904030203041202060d09031e0e0a050103020d0b0915030f060112 75
    0x641c4100e0000031910740f0b00e000d030480140041c1d08100140627a0044000c014450080d5145400d660903120758242100802802d50b0002c1c40c02c3c0030502081d4040e20207039004010080071a8148601c0d030365484071807204043d0100000340c0c82d002094002000304a4903a00c1010700302c580e0300840c04200441c2001c0e50007821709801988540c003c5090601555030b004d4140c100300c540a40d10329140d000345003884c042100454648d40b82034001403a0300c0010440c0c0d03005591102034202200004000c00144608034401942c1038042004180081e41d14a5044e12034401c0380c0b00740b40e00074a4045400d00c0550011130040d0b0007104690100000a54040300312800c0d04c664071074180b2041e101d400410418094481c034555100e1810040d8803e06802030414442c42c0800454001c40390400f0b04119400348804800c1a00008204010f2080ced6000e0b0f0040d082c0180f003007000007030301420880001c82401c403d070b5201005285070320310303521942003e120802440a0400c010205e40d4504403590180d26585103010f = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 858610737 1250 858609487 858609491
    0x1c0203030705070809040905010507020f010b03151e0403171e0402090a1404080304020910080706030f09230105060415030836010206012c09010b0604080c04110f0706 73
    0x59402c100b569000c2c0d51280101402c01c02c07d040e05403514500031b100650303c02e0094450b40c07403102d00d8041d05000e900d05400703003d0041c00d492000d6280d4040c0c000d00c0a00003041c24012090381e021941040094244114029500e480100e0705003d242d0b142c149000d003c1b0041c8107486603590004403040c03c81c0ca42c00c164140d0764541d40e0b650704100c98006195903c0741c4003140c0e070303a4010700003804881c2000c0d5015a0003283c8a401607100c100203c07410743c07041c1c480e801094101501c1042458000c4d88402c080031202400071510300315580e1a0f54990640703000c103c0c100a0f4000681c0740f5210244a119070202c030684081200c5003e00b0b081310f4405140e0f00c4001c014032000240d101c0c4041103168040403540c2c001c0050801d150226200301a0408000345140c010f104240c000105c5a0004102c4003242040800390144052112540308412100521806a81d07403182c0c900c084617142c00c40288002c004040103084140c80f1201080141c60a4580700801c5100c1400f1182c0c1d9100018202d80f02c00d58450303c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 858611987 1250 858610737 858610747
    0x1121202010b03010f15050405091b01020a0b07030903170c0429031603050703020f090f150c0706090506210a0e03030a091e170705030705120c1c0203030705 69
    0x208a0150954103115600f6508000f04500c0083c0c154208400e40c0c036182450035600c44d2140103000898500b1149051282d0018048d110034840c14511342c0d08116061056494480c420745501d242840113840350302c000707940c0b0111501419880700606400e8446101c5c02e0900d402d1260008880f4003441c004d821524031360443c050702150b96110402e42e0401202c03290798891902141c035150155545102d03102103801e220000b08610710034821105a0f40b0392000d05801c000e000c000340720500640a100b15000b000181e624622802c0d800040c00e070a0245034020084031b8141f500007025113459600a5003e280148006d01e0310301040b200c1e14804419203805840c4540d1241c0e150f0026001240e090b04060000205000c180480d40e00031184850140044410407880034403000d4042c081c001003d05074246684105461000304c600601e030141c001d404890030700040740c840033b0410202e90b1200c0c5800c0c0001640742c1440c1002c0c0100503440300da80c08905400c43c3d0b00b1402a40324800100001c04004001070 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 858613237 1250 858611987 858612023
    0x30e0a020f01180509040501021902060c180127140d05060a0c2c010306061b12020309060d060f050909100f0221071b0201020a020f0105070f05030a03050c030112 71
    0x140f032000600008046407011308003804d00d24000e6001d03801d0690442000c040210f00c85000040b858001c09085c1580740c0740c0160f90780b098138520b24a2a110f81085441c0008510755000d00b009a2190081001090103841c0781108241c00420740300030641c01111142c1d0703040003280e0041b58543d03110004003c0440c0c196503400c0100d44048031440300200e400090f440b0110095152a110030b0403040c2a00c0c00c0001c151144800d0b40d9040984074440509640414080e001849545442c501016180102d03403d040486002030701c250411103943d10b1441da100707130401c00501c40c440202c0c0102000c3c1e5400b052810000340641d00c070350400c401c415840340c0703513501c081c040c109580c100d070544100000346107031300c40c440c108610b0190001e84040300060b240040000c500b550702c00d860103440c1e6050300100111145642400400042511240d05010301032080b003000c20483c00700d99641520031030256551319494071024044401c0584181c291550610060100310003501d804800c464000701c9071002c117a0306079 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 858614487 1250 858613237 858613277
    0x507080f0d0e0609010b150a18090626100b0102070504060308070b1509130c0f0e06010e030d1205060a1e06020607020105011505030417040f03051207020604030f060216030807030e0a020f01 83
    0x40c40c9d200c1415800c4100107040c2c103450f0302130403c4e90411080400041c0007420a4448244009828401d41d040b00701500d00049403584181040041801030310302003035075040010110b0b115640160f0340c44c1c60001c0c0441c104050980d49560100045401020b030b142c94070b0100c2d1402d00000c00c0c460410a2842404050144446101c00140207105900ca15240c58011695012600b0384110b4007003024042a110365180229202c500022282c0d610000105d08100100107020040d042c40d400c80343e540c401044d030851116001010000d08035000c0d003040d1030301000034684a0300508100443e450000144a203540054024800c59a181b80143d12615141031411100b54114442e0001c000c0020703002400c43d0b1021088001ca0f40580191554070300d80000904841c030494034000c1d0300401c2040140000750100c0501280d69015040c010304151055041611b00383e881001640460303092410070586a9140c0503007020700102002400820032154003080384900c041040c2030501072526855440342c4900 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 858615737 1250 858614487 858614507
    0x7050c1816090e1005040c0e090a0b060c01020708210c040b0d0b0d03031506030912050c0f1504210f14090405041b0f060806010507080f0d0e0609010b150a 68
    0x42000320a540c1068050302130b140007113100b46401941400c081c030035040d000c2c4ea00100840d0002e071100d07100d0380d034410f10a80104500300c01d50340d00c44030a0003120500e0400f403010b40324031031240744003e40d103505c10001c0c230300341c11504499900f51010520400c020b00581c0e005480480708045503240e19000301314582d03c09882c00c051516004001d10002c035040c10351541100007410100100b00c64044d46400b022403d5500010011300b0a50003045440304042c818002070048100340c8052310501d910381c40b1007904007920340e448001000418800d1005220f004072046450500340004038060320304900d0040c0406890040050034050f40005041d0060003640c100c5408841c01441003005150031b00d8580e00c03040000401281d8400030200100302d4030006400c0324161100e84e242d071070b07041d81e030300004480640c0109800c85029109200040c0301d50f0301d40700a889449080000413443d070540d0001075180150080c0344000c01d03030400e0304901c001d494940d03260320850a00003807956200c1000c502035550700c0700 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 858616987 1250 858615737 858615749
    0x1b2104030c140c120c0102060402190e01030501020d0f090b13021203040b03011806031a0c0d0204060e1206060112110c030c0a03030507020c10050711030d0507050c181609 75
    0x81400c1d00b00c50b0a0001c40c00160324a0204c4540b0255201198020303a0390608804281c05a40906d021802600e04940520b807158840c402c0648001d880d00503003c1c0030502030f84115800e80d00030070800e08803007140c015109042c446003002c1140f08001c0c0caa44070f0004000d0420107040d1407902600f010f648030805c14800c000c040c0f034201c966680e901d075414032207030b4070911420350406c9481140041d00002c600520084942003d04180c40701c0c80a02d15900800f0702130300c4a40348120402c000c80e0122110f00203070005140326151710b0704242e826001c0c090001314008221255070800c00c204000c42e0381020032a080b101e42c004000400c1d01c5d5002c182495072284410003d82440007241c411103124000030400c00c058400c0c0c1d42444280c44003413091360b54200300218a54800780c55047c5940341445080501011801450290300c0352084001190070100c00c41400300018800041400c1805010001c1c10300f40042070303440100c000401003a0a200e1103024141c91078900c4041e04650009204041c01406005 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 858618237 1250 858616987 858617003
    0xb060f040227042a1809050601021009230a14010605190b0703030f14271501270c0503060f090421031805061b2104030c 53
    0x41c002c10421109620304820700041100c8546080090519000388000300d064030780015000c0c071031403500300d00c1599071241e02000c00144100003101c201e90089890b0090005003c00101800c0000009092100d031841c1022a1070400e0402d0b00040c00700710184401002141e00c826480389683d4400742006030408014082400d03407200701001e50019807016048070340c12603140c0c0c0018050003040c0c62801d041d20404080d0394007841950b001c00e0081d042610901c41c0c1800c002048031070314204c6d0780004001d03034010140040d40720110914141891b1954458041c5500419600c60704018041a07441c05000e2240d040007d0808002d4888442136035002400320b2364400e00c50f1400c480c0d4000d2094100703c0d16180300f0840d00000030b516007042c0d41140c0c01150000c9203030300c4001100903400c1041800d42c0c4164201a900c2664800000b030482c1c1c006076039880740d8050070250070403075904002c803504240681d5060750104812007038041152840e4901028800c00350840d0741d03a03070030281d606540d034404c00780c2854 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 858619487 1250 858618237 858618247
    0x70311060706142203170402010908010c0e0f0d0c050f0102070e07030e10050f0430030b0a14031e0327100302180d1e0803041a0f01030b060f0402 64
    0x107403491221344900e511400c490303044811208210b10b145286a00500401c072610021001e01001106a65010340181840704405036a46505404c490804c0b4200300003035100b040013003d030319151017091070708801150600840c1c0c08070b03181c800c10980c19100f80d45c42818800c1e00c19480b030340240700d080c0c020498041100c50302e1801040150240140406540190082d071840c1c14021289100ba40d01883c1100901c80980d9255a034481c40c008004400d40c00313580b403400c0300a040789800804003407104059a00400d10807000018080c00d280b09402035076680744444403400113605c3c00104500550b004030151012032080d64040785c11481100000c0c29038160b20200c14000c030441ca11040140c00054850f01c540c0080030000300c00b24010002507261010700800060a5171805105c10100b032402000c520040c0c940501030010701043c2500102e44495001c010401402000422850f6650f107010209801d481e00c481c0390340c0343d444140001803800200d40007143d81600c840b00303100320300710025104654072 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 858620737 1250 858619487 858619511
    0x105130e33220606110709020a0e010e040e010e150f15060a0908010501060807080f0c16060605090f041202210a0e0a031b08190206070203120304060f0f090203070311060706 76
    0x36001140d440b1760705100702100041e007502c161084920f0038545982e0f002d0707030104010045910244e07a100d4158841d40341d4541c42c54000c2c080c481d40350130407006030041510b040d07240c011007540000180384007104200702041103001003501c2e01c40100910300721002c4c3d503510710845099071281c0760341e00050000c0d880c00b800400c1403900500c42d42d000701c0307003a140da8050f50f5034044983ca0b130140131250201c014805010301c5030240c513644140f140691060f000401d60a841d0b0700403131114282100c070802c44542200500c42807084150041c0841e5000d4800350018505420807040c0c5404103c00c1c6800d20100040d400b10098400c1080d542c0203803005014030102a42c030b0901481807000d07110384541d100119100011110300000f03484880c2c0521610012200c00d1a40800045410000b02680c050250b10322458402e103d0074011803059100703140005008004040c108110f030f01c1500502c540c02c1c98842e800016035000034450084075400824043d03d0114580426074074001c803240200b081d8101206a004 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 858621987 1250 858620737 858620747
    0xc080703050d080603160e0604091406010302010e031204050904410d080105040507020c030a050312150d260705011b0c0f0803060105130e33220606 65
    0xa656036559210500d80f13410042603142d44880403504200c19410408000d0482e488003156444000107100198006050f1a1030843c00c184003007a10389504018018411980c0029840411240035001000d454641d442181c0306032059010b210307c24900c11001034100900045040390030803441c88040100081c4000813000100d524444111360f00d1403441215902000240d149601901640c541c4056403901c82404014540a0071250460040f109030030a140c804015895010b072140d001550358114814103100c680f0000342c012a20905580300b52140c686c0d5601d1024140c3d5040062100d2921025403140c0403030703062598446400e480031402c503041c0041940301c41c0198000a101c07078001005907a0445a00c0650f96005210204483c3c140380400c4400300555800301040c14154540ba040f40da41d4141c0e0003003580080303e4010400200300c002004040e0f840b2901032181c250312400ca00fa03440c100319080403a9a8075001d0001d13880e4810300c6407855910342030020844602085603030745610f4003c1c1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 858623237 1250 858621987 858622003
    0x90f0c03110406080609070b070c0e0f1014010518010e040c09030b0f060622210312050903040b071a01090b030715090e1f09050106021204031502070c08070305 70
    0xc03240d07242c80d0000584c444003044903841503d0200203403810508082018000f604040c1007614408542640400d20200152665004401c030302d220100e03a281080702d800170101c0640002c41303540c060a041c4443c90340c0100650b400301e030390000c84a0b64824020012114a07114446883d403143c1007035800900140c008142c901030300c3c000c03194603e8695680741090304100741075900c1500081c0c1040118003080d41c000c0e2400c0c07048250300c0a543c7e404d558001c070301d0320604050111422031314820840b004040e00030720020701c010411401841a0311300545099240e00882c814109201c60008800b4200f02201904035004100748211501307558486032088020024070396103a010307100d620800f081400d104009408952504c0c0e550091741c50425140300e16841001d028000d03443d250018459161700500d5114025049114000403698036204000307280055200d142050050104410700105a180e60200c0d505034000001503981c412030b1800e200e15101d07507400243c0d54007640c180801001800b140180d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 858624487 1250 858623237 858623239
    0x190c050c1005011202041515030b041805070b03070201060f030602041a121314030a0e0102070609050d08031003080a0816110606010804031404033210090f0c0311 71
    0x40c80340000c0310079201c11039500780a0f180c54000000142d00c0180f615402800c60001d03094603d422903076031400c80101c41802c811220b00171948440e1545002d007442c1c816600c48204c402c0b01c05041800e10340310f0310f4070380c4624011700010000c000002080d0900075081040204608002908006da503410040001d400900402c001010754040005080c1141010340301c0f4182d4440e40c8491540f5850724006c0c200c2c0e07400d08101d40050700c500c810351481e00140007814000b210b40d281c00c270102020784002410102290403017018803103100d06c103002030b03262900703204080d66104085540e2034560901d6028555415480100084000500c0c2045140c2c002c40c00350107003104620700301e608402c80300c056131150001184c0394101d0f0b21080000d12a0740c03040c5401600103020f030070088075030030100e400036402e5800740d007094501004600103489079044156521104103200c1c40350454038001c07c00400d4942c1d10025046200e45d844d010201c040c0000c80804003140d0340d000c51301410f1180e0307a15002007843c4030342d4281 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 858625737 1250 858624487 858624493
    0x1e050306070201110d0e1f090c081f1a090c0d0b030607050706020a140c15061e010819050a05090c0409080a32071202010213050603190c050c 62
    0xc1030007030340140100c003d61626000094201a032003111800103112107203d020851040c560141c41000071464403050700090f0420102e4642030906045c142485694000c070340310342c05007481c902245122009290b1102c600d0744045421038180a58000c071280851065a03c41e29601c20300040d500320030020000c044103a202807148519030010142c40342e04c21a14a4049041080a18002552a401888106034900300300c1601b0741c05e203000c1107d40e00301c100c1d030a03202e912100c6800c03071400503d46196840402101c0300321702a6036119900d242c03111203072001818000c103000400c00c000540c10a1030840700148078208041c1c506582004d000c2d2009a0316103c46010380c3c10041f40340e05160085241e0795400c48107241c903111a046045591500c6d072002001d440c007103404081e0a031200101c848101c0c1070415801ca440b50458181810790520103181350080da031040021003103d4002c2040c59040b03800c11516183c40750f841c5a03c1d0709a1808101e8201a124a81100b800ea460b4014003e0300740240440d0413 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 858626987 1250 858625737 858625741
    0x61a0703020706141605030d050910181104020901110d080f01122004060519030203070f03050604030807032a110d09090207050102040f0806071b020112090c1e050306 73
    0x255290540e00d11309654240040140c00301c001c8002210040c0a0b1040e000c6034500308500b031045040f2041902c142c500c41c1c209108011903403030107028034400302c44118500d0f44080c441e6034903021364260002e0781c039000f10b4010850351140d071f002c0c09140400b01400020344108104100000303128080c12141d80061000c0b0034004100c0d0700801e8101c1703a03860303880740b0500003e0503581540c159085101c0b40b0254019143d081c00300e4142c42d54011000c80c1ea420802078044036055104050400a02c0d07004121280400c0400704081480040c42541081d0903040c046030a0b11aa5001c6010f801c942c0303400740303011b25420030000406884400a59000d80c80d940d503100b100c501c08003480e44418035060b4580c00145104400c1c00300449a0340213180c024031480c001440d043d0b036940492250040f0b6408a00503400070b03010060b00d1500700d40b00c200205884a04148060401e89c00608207002c0d814030404850740d03600c241e03800c0009840e421400703403440240c803110f03c4122141584144042e0301a007070082c0a5000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 858628237 1250 858626987 858626999
    0x6050904110418050d121d03030f060306160c080708071104110a0c020405090c090c04061209210903050304080d020f0f190f170405011b03020d030f061a07030207 71
    0x846418010f070704c08058102c0c01a14402121100c4000c1c00c02402242d50b002c902103078a50301d403041041910a80040c50b00d0345040d0809070031102005000c00e004e60040401c208d0351101c01400004d012000742000312a02515080443c2903008100000f0710604c00003c80006015134941c0c4840580c108450501503804002807108c160b000b158065800301d81610362500052501b5080030345e0041b182001c07100244100e50008400c09001d0301d01002d0700c10009804c0c05a280d100043c00400e002c0c0c07034824812110560350380500c92036206080b00340c01c82c8000085a050b4400d004500065070004100c0c0c0c0c4803506c624100f40c4448440511102611668070420000b640100f45811195480300150000e0100000044c1d4140c0349100f04480ca032542c0e010510000d03103240d8200c81c1030b11880500a450740d00b00300024048050b03095425129003445056040001d6000030803210f003144c0c515002ca0707100b000c841100041e002c02d80124100d0100c80e001285c0600b014006008414004e40c00c54812664980b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 858629487 1250 858628237 858628271
    0x40b0307030f200405130e0303070e011106060d030f0318030e0307060c021318080301060f11012a05040902041805011d040b1e09060a1d0a060f060509041104 69
    0x80100042d85a0a0204005c2e52801042c40441014401400f00d43c0ba1034159004d810340d0f00403201078022800c1310b81078490650703001d80002ca10030742c1a0018444e43c14142c0c0000d02141d00c00400508010b11101d404030990311036041070044a05180b4903000540e41c1d0f10300500400c0c10141d4140c081e01c200c10000801e0792191411111440d006040c46c0300341a01d0406440103040d819030200b10101c0701030440000aa1090010741c001c2c106a40d807a1044035440314010103480d41c1111300807560317044c01108480612504804100c84000300c4001881e14400001511540210b81c00a0344051000c00e00003138040e030500896480480d104030810a0360380b20403621b645640c2e0a07040ca00703001500d0002800140ba1070075201d400c2001ea42c81051525034175032101c801000c0445000c12070381c01200501000301c500340100e0318041b4181444d070403451512f0742c0c0030b65990361101000c0c1070a6114222000c00c01280c0c0d01201c040c003c003401c040118035203410329114405955500d640036038603000701d182503c0d07520 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 858630737 1250 858629487 858629531
    0x191a030a0609061107020a181515021e060601210204180f06151d06042d140d020d140a030f1b0609050c0301020a0c05060a0e030703050f040b0307030f 66
    0x6220a911504000d12800100c0340e60f800020082d0380e030040c0103e81270b40c000c1103030020a8040543c1c80714200c0604003d06014a219102150423080a0000c0c0d20312008540d00354405020300e0410030003105c51031450460b101800206803943e10001c2c0100e000c0c000c900140075908049141803100c801d0701c0c000d103421079039140b14201c8104102c030300c81e0ba0600c2c4103402c0c440d02200e03241e054203116a02040000c0c8158030a90040041014046c030b0b0801ca0381f1042d814024040540c4965a030040c86e145010303505111500300a0b1042200c41c08c160115a910103082c5082500508501e00c040c90301c0c54001c1d50b41109003402d80c00b02d03041c4140014103d106a203403a0310804008920840d5004990354a00603181e0158101c4840c05400318443c02d035107003407000c2d0100501036500c19030b010285081990a02d04090441c02d00d680c02c0000d100003980c000000c8588456041c50419680d00203a0f49041c10f41c0034a4000300001c034400420301c940242d1641192800b401888010005240788030500f006032441 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 858631987 1250 858630737 858630739
    0xa0311070803070b0901150609060f2f0a06020c0601030c1502030405040f0e01092006160b041e0c05210a02010f02120d05160503191a030a060906110702 67
    0x8100d24070000310b07000388403500700b04d0450000c075104607401f1020900a045820260020345c00c0d4800304801c50307104410880c00842800d00307020540d030904012801164100381d89504441c0c007000f500704610f040240c8001c0030b0b00f18a08540718040031401c1c03511031f4800e1205a44032211148003107104018042900040002c640081d85000c1c40c280a1002422130110b0008030f003030743c42000c40607166080c00380100789803281091b141444000a20105c3c0d0601c941c41d200d0194505100c4080f2004104921120490f08a40040010341d500c1c500314001c04022003400d200300300c5110b00c100400404145132002d843c0c0488888143e21101030402500d491b8040d28030b04540c2c00001440c0c00341d4010540c0b040032000620507540442150100882568444651300c2030150340c8004000366a00b4040d5503640c9000585810340c40c0d0f040207015680160305041440010a0303449258000603140b40007980100301d406415110410400d061100040c1442141628010b041c01e4181d10301c44510781c00c03902000c0e4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 858633093 1106 858631987 858631993
    0x5070b0415061706040b04080c0d030c020c041a1002101d0f0a051203091f0504021206010b0a0336110301020301060801050913140a03110708 62
    0x4030b07991100e45103d0701c641c1c0b1542007443c0403903d1508a9000301c006001a06c2d10704000700da178881d0300f1041b031480c8110000440d03400d030140c1040c54101c2a0b034090710080072012003800241d408a801c10383e08134101c40304109a40ca08030700000c2c140b002a00c103c1d180450322000180440d005c440110740303190b141c1c0f0f00342c180504042103001e10801c8180050003100f4000d64400f980d9045c41d0544c00d000800c044006603a20104020301e0f5000b103400c440901e0103510b040007407801040d05036821b0b030040c0c880340d0301d101d00041c0000e425030407504200c030401e10f400d52010003200106a1001c0541048001e4002480294034200c0000342030110007880c40103142c2c00745031456100712041d0301c0038060390041c80100302c2d8641002c0c0940c110b030340685080340c3c15074441800c0c5120011080f4000e000c27410410101c0c0c1d80400003c1d002d01d50078421384601485c84a120141c5941f00590311421500764 = true := by decide +kernel

theorem cover : BRFrame.Cov 858453237 858633093 := by
  have h0 := BRFrame.cov_init 858453237
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858453237 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 858453237 ≤ n) (h2 : n < 858633093) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
