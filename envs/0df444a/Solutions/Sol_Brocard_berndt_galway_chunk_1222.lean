-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1222
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:50:34.473225+00:00
-- url     : https://prove2.me/submissions/c4f31fca-853e-414d-b432-bb2832752156

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 219604316 ≤ n < 219784172 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 219605566 1250 219604316 219604381
    0x18030f030901030203040c030c121b0f0501050903070905090d020c090f0402150c03030408031f0602030d0c0302040f031101080a06050d0206030405010b0d030f020d0507080d0b010504080102040806 86
    0x100080100ca200541c01e18025a807940c6508041a0031455948020481030342044000f0300c01c442c12040747c0e0748910039010128405102c4c0c941c03008418580c05411003800031300350100865030051000b025130460182c00c0c1c1d900c841e85c4031060022941c048910091582003051030201d03595050015445030701c41100c401c04e00f0f0410a40c14040c003140200005e0203001c801c00c00c1c4034400132203c2079132407240f10039007140cac0d4924181c03411100c113030000e85903000800c0300b202541d0041c0140082400035078035182d000394100440d5001d460301502a00410310140340d403c00c40460380e540d2070f84414001d180602c90f240d0b01c0c0e0111500060a00c00300509122410345043c005205036602c807021000e100c2d4048036000d0f169226802d249006008041c560340d48104a025107008054101c502c0c0e00501c80d154090b211070548001c81540c0a02c00d11038020948582000089102d842680c0310742c94114040c58094141525807540500b2603109400101c00c5510060810a980c0c140c101035080c91800001280c1a08 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 219606816 1250 219605566 219605593
    0xf020312010608071403040c030c1d040318032924060715020304030801050f01390506010807090f0221150618090903070c060c24021803 60
    0x100040c080c90041103043c001140c2c002e40b049002010425001c41c000c1d03540d0406181c29020202e151104481503c604180028014404559550900c3c900407e000d819a0b45541c2140c01c100b400c095219140750900c0301101040c6080b0070141841c03c1d010b02000c40751105011a06640d400800c0c10321660b0325165000c240403140d40c410004403c0540f04927840d04082c2c909104004192141101154030100400050540c080001412180c2c15100340203c002040e0044407800b240c0d0460038401c0400511074040c41140ca01440c0ca0480d00c440030b00740304c0440d0380c0d4180c10141c0c00c0c2c1c41f2040c258050700007405004698403070517007056002c03c0d08518010444040c0800d0300c1c94605c21403800000800040c1c02001082c0c0003d601000c010b020661703414008260105c0180c0b008080740c090f80c034040000300c4010002044031400c80d085203840b4607072450807000303c0701021224405c844081c41c00301e07048101400082c0807005030a0502c80980c40d101000c8500342c40a103101c00c15403203603100d603c202c60320 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 219608066 1250 219606816 219606847
    0x40e1e07020703080703031b030504021509060a1b080412050606030c100309060f36080913021905040311030a151a060f040f06050304050c0f03010905010603050106060f0203 76
    0x4495104ea000c58407030345141411340083c60821803880303100d0140c403840c030769481d4180d21180c802c40c42106d10141d1581c2c401d090400a001d105400c07a0440805c00180e138000d8003c2258404070a00c00603540c6c080f00d8656100c500540050348100d05d41034841940030100b01c020b001c40c66202d0400c1d0000d121750301c550380004501c0340b102e84202c07051542d120b04450500040782c03c51008809001d90501035035440044090782e04641d62032040c50007900501e02102181040201580c1c00d17002080c203410b284448080009030a02d501204030030990030048110b403801154a1800700703281c1910380716280c92031402d26420104814208a101e5008002004000303000d90802201c00709843c0f10001e0048640201c1c0402c501c900300010358001d0010802001c59540e4400500554210850800c541c65a50b10103940c01c2c00705440003080d5410040d00041070b810503001c25001c008004001140204903510303076500b101c600380c00540e450794680005100710740d04441c0c810401c10f40e61004500e40b1403141c00c3c0c03610 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 219609316 1250 219608066 219608069
    0x203090a0807110d03050406180e04020423070804060605040c0c0618080408070602160f060e221a0f09040f0305040e09070f0b0a02190314040e1e070207 67
    0x400200d410000d0110b100f01e20012010080c2025458540f00e04020303100380c00600c030780710011b492040c400400c5000c1407000e000b200e043c4069907000781c07659400c01c00503285100340b00101d076000c040a0302d04441244e01030f5000b060b07203443c1c03000e1313505190a00c1d1003602c41a0300058042c5080c0704038010070340d501c0014030031543e8001d4030000c1e60140c4100114020400c5041c05040c041c40480c001ca84803001003000e0302150050f408840c64070041548400d45c1070b40700d110700c006d842c07108101003043d240909042404c80030003c00a0041511001c8803451604419204000e4640d44031516640d45080c40c0040b0741c407903800c5a10982000724480050924003001b04002c03c2502e150702003204240c019415200a4003294005210b5480c00d94481559041d1a03c40c9040589615000140d14024034003241d9091a465000c0d100d044200b100c400000034000a08808020200340c20701c3c107001000b03001d00040c00e40403150008a0401108030f804c908501034001d0951584003061041154000401d01d0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 219610566 1250 219609316 219609323
    0x915040e0708030d020d0c02060903030406090302070b0301090b0406350708030a0c050d18060503150406060905030c0612011206090605010608090609071a0706060f030308040c090203090a 82
    0x349103206003904904007042940028400d1201103a140d4004146801800d280040a0810050a1515003040b6a941d00a450144c540e81007040818041600350f00070317201c018000c0c01114059a522460102c880c0e0007684540e41d801d60390b910f000c41d6403805008540080600c042c500080d8115030812082c2614100c0080064503008003140401d2038060010b00c0040c54403070b09030fa40700ca05010f409402c2d0b25415208595900800800c50011801801d030310403074142e0030050390400d90400714240c0e5540e002400700d802103030000c0c004a4141c0d07683c0c0030f150082c0c210b90340e912010900c0c0c070040c146402c590752072203403050009000006200c0d4400c010241141c520ba034a15180654a0a0000c001d2403905406890320303040400100e0700682158515005094082c115005640c86950068440c801c2e40a240904983c520403143d910501c20061710000e40034010009001e569a002c400382210035034000c070302003070498040009001c0003040101c01411404001d524602d003120440342c1380c80c0307500c9005 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 219611816 1250 219610566 219610571
    0x50916050111120d090510021e03070c02150c0c0102030f1912180b070807080601140c1b090702120d0f021b0105150a05210a050d030501060e091504 65
    0x4052051041264080090025003071a13500e0b50a00c144a01800f00484141c0e16480340768408403a14001e4800c480300002c58544a82041030040115442e50340054240c00412880307409480243e951080c442541c0000380c074009550b5010790501e40e040031191840381c4c1c1950014451581c5082d040070440d01e541c90700400d00c08805100d104c0c240d0b0b18184d0140c00700040c525014000c244031205200301e241d178601400445100c2c1d0f607003510445182c1c0f400c8a01e4800280f0200201c0c001c0d5010382c00c481c0e01440415006c030b0030320103005261442c000508408454040040300c504e2160b05001ca0482d806c9481d0b4405059a245100d05a41c170a125021b4044081c035a11004401c4aa0320b41d415070f641e091a00e0107000c0d20500c1e21441c503010b400103407004241019034810285407450310020810480310040d0492440c800c0740010103455107004490406c55000f0b04150304009a000d0261040030903260b00c0005803541880e00041c1501e07268015580a50742800601010b5004800154128a0102c0d1302 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 219613066 1250 219611816 219611837
    0x130803010e072007051f0507020f06090d061d07031a0901060f03060c03050a0213030803131a070e030106030b010519082406060f0a14040510090602010509160501 71
    0x485015003440300030100c000c88070015800b00c01d008180102250b00c100c80d0020596007100001c0c1e90fa400340303d080001f1484c10010040103041c03410f81450310340c60007003040c0c1c1824a00d10208d1803d81c01c001c002c43e08280d6511154545400301c21001031a07082c10310040c102c032811951943c561003510201312804600a000042449209411005c007404e08807158a140750741c0c0340382090180680d40401c00c0860308120000380350a01c2442542d00d07141c0c0d444403000c2000e00e10f40b9125090b42c0050208001242c2e81100e41000c00c0d90800b079980f9075618020300c02c195140441000301542c0c1010b010310301c02c0c1d040840402c003044078001d6013415210211501c0420f01e45001d025400f00f00c05500c2a61140600881c6000041e03040024004e14000284800c406542d4403003080344510809445400f941414001007002500c1220301d00d090b6440d00c4089032415031920002243d4030317804920040090001001880242e5081c080d403900300003040c000b4802000e285401c0c28501d41f407405580e0411010300c21 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 219614316 1250 219613066 219613081
    0x5040305031906120b04032304140f06040305070e0109020a05040608060d020d0b01060e030a0b0c090607060908041508071707050f03090102030a060501110a110f031f05130803010e 79
    0x5000800c40e1003240d1a20041c039240800c82030004031030580c0800c00c070b09a007070816620340394080c11a10743c0904d41880c2c28100348009400f8600200c01c0b032f030825142c0300121010380701c0b40300400146024200910009280070b29a29107840140c0103200c0090042c00300080450700308040d54240e80d850700300a04281d8a060110b1500904494080e50000504803100b00340160a03c0c07c40c180c2c0d8072607441c482840d500e0000e0558800c0c160500801e81e1500a001403090035062014002848000308114a00b980b08e03201c01c010360f11720310426134007903200060410001c0018460700c1696486400c124003a0724281102034504041e0100103041003092750002540c2d184154110350601d07124400c1981c0324144021054000d4108481d580ca10b5494218041040d41c001d0136045c118a07010303001000c10088503520b002030a00c000080e00c0d000071051209110584c2d040c0920f0109268060003c2c80c02000c0c4002003040d1400a0040390080c0c2d01d4442c01c0d030120300a002244d0660740c001003030a038540c0f41c164 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 219615566 1250 219614316 219614321
    0x203070e040903181521090f080319051317090607060e07050405091f11041d0f0c070b09070302031903080109290d0c120c09050403050319 61
    0x60109034000d2808003242c0c201900181c01c1c01040c1d612160b0243c0349900d4641c088050000009a07001044403501031416405078155005c0e0030100e1103901083c00151b5540d1540891400d0404031080c02d4040200511184584030541203600e600e0003d002c0c5041009103080018800c0c00090310754840346445030282c002640072a984000c01500840d0b4813030340b50500b41c00405001c11603810b00d00407814001040d14060007401c0c05201890702800810301d2031101a9042007121610100040c3c6425813080700d485000060030041c2560366001d00390100390688400007000060002401810031024880801c02c010285c4130b07416403005c0c28141d01e4a40c1c0001c98589111a80005d40c544601c1c0e4201c18907004510f4840c9001e0300c0780d150150740f81d80700c2c032800c81914070604018180300c4907516280c4070016441002c07194100e0150240c204224640c803501e0000901d41c1229844100040c5241d00b0000300022110080000130f104011a0400b41e600a01c01d1201800e811081d0070340c1001c0d0b046c0310f062035 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 219616816 1250 219615566 219615587
    0x12020d0c021018151e0e191a04050f0301060602070603020f090904082703060c07021f080115050f0901030203100f080c330c030405040e0f070506040315020307 70
    0x200781d0f18940c0c4d82c8002d0041211550103031103000504207406160490315100141034034213982e460300c406032480035086c0401e0000c01c450314139000c02c040d07000088101e400403014010707000030000c565985081800384044044a00350b40c0340282e140440402c0202d42c0407400f981070328098900941d58280046504800e4001c4032101030780903c40d002400201f220307010040c42d5101d00000d0080241e5020905401100c141d2581941c05410a00000d8245107620000b4003aa500c028518204418583c500b40d07984608191100e003c504600014000000b0400d806044c0140030316186140c154031100c040c00d14080c04902a06050700400410070704000d0702200b00203440c0c0d0f0085030080943d42c18481d0760300c40d5403092840c012201d1488065000c006c4039488910140d40030100000740000c02c8001c0216440f08081020a0105200c0816596168043c020070810b54000418590807440b1041d03082c041154815403044008000030800598031440a83e01103881000040e240d81e9031400944244244 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 219618066 1250 219616816 219616847
    0x1d010b090a0f0f0f0e010b070221010e07061b080904020c0307141b18040f0602130f0f090213030f030c02040c17010b03130b04020316030f12020d0c0210 67
    0x3010b1012400b6030b144000e010446154100b0b26070740a43d00c130100003941c00280140804d031042044140098107002d0043c9421900898950000000d480283c0b401c681b640030a9050f0760f00000c01c10401d00ba070000d1007141500c0c403082c01c1d0301001004d560b600300920620850b80d000d260082142d54080c0000c0c000d071244c0302e80141c210640700d840c401c5c40720303101c006c0c226081d20004021071580720b440c02c1c4005445070591421282000d241c4840d22209841c10a000c02202d0040c1c08020760340c507100100001c11f006042d845003420240d4280206410b181c0407941108400c0340c0705028440700505a81064021203402c00c0c0c20900c10416800d045584121b0031601941140c242600c5042d11a40024040c003201e0030300700ea90355140d8036003001000503c000e0341d00d51004ca041840ca480400c0c48448501c1d00148002c00b2640d404084900b40d140b401d07a240e0080d40e0700d00588505100340400d0301220b4003140d2884c0702400e809088041c0c0948041058440680100250b0b00e1b418007480c05061240c00c0c0806 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 219619316 1250 219618066 219618089
    0x160c050c042d020909010b030a09051f0e010b09041e0b07080a0e06060306190603170306010909060e1305010f05100617011d06030703080c060703061d010b090a 70
    0xe407024001852040100c1c0c9042c00045007880c64420040da1003507a00e040030062000e40d01c1e0340b83c104420342d56000030b8221252183d80c0c1c40c03030000080c1e00b08035a4025004283d250464202d0041c0408101c410009a8103101d0741042901d0415a03202c0941c2caa00030751000c410381030310801e0f00c680d1311358810800c401803412000c2002d1040c9030340c002e000c00b407044003541c100b031110104100034a615080103450700c075010fa005001051b0748000400009603170423150307a000190566203880383d4154400358410082c014200209201c055640a080d0764050440a0300502039546000c1c0b00c6802c00d03000030a07045140740860350380c40c01c0203020340046504a4105c1400c0c440ca003070000124141d00e900e8407401b40442c15440c40803601500401c00c2d00d0480c2d4141c246454002c4d20141c2d10082d515004003629810300610b030001c000603c610b0058285032042d500100661b01e00403a0280841e0400e0300310040c10314001e8108100c2115201c076081c151403400c00600e8030389090f20042001a43c10b6000324600c1300 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 219620566 1250 219619316 219619331
    0xa03030c031103120402091305070e180105010b03010e011d060f120a0c051f05030a0213030b10031e12030f0b130f0b04090302030d050c0403060e030a0215160c050c04 73
    0x4200313503035580542c0c004c503541c00c030a440f21040400280711460000302141c1045600308101d40d004001d8580c028034a000c5c50940c18840704419084070f500740c0101111030302c040014080c000316814580d0151144984071455400503203000d07560036000030021480748140c42f102c00c41644480c042445242d20300e40c1110884030503031500001c010150700910307024010680701d00d610100c8941c80001071250700d441e014a55121800d2a201940c00680c807030201111300c210010010780c0d12580540f250000300300d00c03450142107180c0049046400444a0041001d9260250101d00c561310385c030390f500c04903003000a00e0015464040001e4000035124990286605c0f04030565a03401e42c11441034070856440401041d0384280c20441140c1c12080c2c058012390060042c1e0700c46103030b55481182c11002e820310090500daa20b03540d4000340c41000b02c9a00b469000405c4480c01c07070343c0410000d461080c04030103801d00c3d0b1400c56400c05c1e00c01c4185404504004091820a0601106000c5000c0005020b0014003010 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 219621816 1250 219620566 219620587
    0x309091b050f1602040912120204050a032303040b0307021606050405120f030a030f0609051303051b030304060603060c090b0322050d0e09130218072d1704020a03030c031103 76
    0x260762200c146000300c1c1c44121030748542e2105100311806e81da801031401445500b10380f623b11502c03d4003450f2801c0b030741c0c1201d50002c100000700b010f080185100b0f0030301e0f55a841d14900090400200354120090116084014065588c0180541382a5501591803180034081644028a0300d003ca0540d0380301400000350055a403940764014042d81003108405000703050b41c68208404503402114244a20714000c074440340002d11070350080c00664190395056401050f50012b00e4110f500c1038600301d907800d584440400400c0b006018031031100005003421000c051030410040a548002021417062038040e1680f12038640c4407080f003075403c039000380c116400c18100d01401340c41071841c43c07550b9208207280b00001c2e40c003008000301540261b601421054110708020101454401d01801070000d009880202500c0d001c1e04040030304500d10300f50101c418a01521901905002810034008480584c140402000d0780710b050000c01182e61526052850f00c01d03a0034100c030701c11480031807402240000107985c0001c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 219623066 1250 219621816 219621833
    0xa0912051812070909082715090a0501110a0f0b2a0702010c03030605061903050a0b060f070206070b16020c010c03020c091503010204030309091b050f16020409 70
    0x211020410003901c40490080065504219000c88400e0344090750622030070000350001e0640341c0c82410201c2c1801c05421400e101c4100f160000c0b4426204000001c0c030030301c0c0118113510703100048000149829145400700b2004e1456000c0d140c10310004e0342c456841128208410b03004aa044010460803611a2a201050784003c0d14054110400100307003158080e803c0329800e84400d400c04010386409c01341d500544812004101c103509040e40c1b0040000e46488542c0101100500c01c0e007002c400343c1c030403003000e02100c0d800303407021407a1482c0c1036411035291500c1d011540103101030f0071078907240c08003880001c5d0300d4803503604010000c0d00b80d9010f11501d14101d90246a59003940d40031341da442c103200d400441d243e520364000076005a000d0010346182d0704040640c1a0007107160601c401481542601280c00e9034040d5004900150955a0030440042148100b00940e031006c04800118010306000511078041d0030b00b000f45020300055442c00c0c00400d1900c0200c4550301030000c0c403d4907001c2c24407011 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 219624316 1250 219623066 219623077
    0x60403111c0c020a08030405030d181d06012d030906020906040605120108030708030c03060a081e01060b071208070c060c0e01020c01030b0603180a020d0605010302030708030406170a091205 83
    0x14484c1c40c1e82c013190240c40441a5800da5074040c0048c4088a2440e8044035400c00d4640300c54002540c407100402e0f021700c02c90035102d201c12034148045650030403100042107600100e0280d6884003198464652030101401e84909a510b0380c500420b072004030f8103000c4024861051410352180780050006070b400e40080141051000040145000b030307a0720703100300e0340f64416910018042e0500b080000c982c000d581001d150080005013aa1103030f036450710011494030f0902c4890351290030901440114081003406060040c0402800c041d0034032044d5500c10b510a031203030840e041030000400000301564810b1288107801070f00184107202140b014031000e070102e034030794058a00500500d1140350155000e40070b180b00e14080501501c1c82c0d0b5490440c0e94084071510728070b09409005481c2c9034409a40e580c1503551042d4010080020554510302c1094500310782c0d64001410380d041031004104480e0800922200501124280017660b903e6a0450700107060608005010688014002c440366034060060304 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 219625566 1250 219624316 219624319
    0xf0601081e07050d03050c03121f0501022a031507030507080106110a030810030605090d0305060316120206090d051005010501030e100902010e090a050912030405060403111c0c02 78
    0x4600d9680720200d901d520302c600403190000d43c0305040c1c0e40002d00c00c0c401881030003541d5043c0c03810845141d050424102c1d00b501c0001c0c2c540507240f0484600301070983c80b180104800d000810030321210391103a020404440300000f862815114101000380c8080c441203110007055152a01c16290558019005060945810380042c241718008109107000305c66412076140580c00800c000440382c0d40485540f07100400c84441140401c00001c000b6000d4000e040c042d031391500281c4181c0c51180b2004044420091155100703521040c0180c1d110f400525541c0141c1e00004407140318882d550010801c1c3d4400d40303000302d400c0b200c00c2001c80c05100b0f0120b610100d0400d48070741407220381d07645c4c030045003502c0000f00410407039007140c11601201c0805030300c80b0450314410304040a0b41e4240310001100580200c0d40400e00d65101c0080207100c038020302041440703014905100c6c1c00d41c00c054690030303510040204000c05000f9203000d501d413207038000c004465031030034903406040301c840c61a9001404450b005000320b = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 219626816 1250 219625566 219625603
    0xa020712030c080115120507030204080a0c030b0702070302090f10051512070908121602060406110d14030103020d0f20090c040b091509040507081e1006110f060108 72
    0x2c2800f00001000b030117a00070b00e80e5580306142d440345569000700f401030702d01000d1680c2040300080e640002e10890907140e0043e820214024610308006680301802032081046400c04101800180e03203280305a030700f000c4012140d400740d03a9140d0740ca01c001406a04810f50109040e032030042c801300280020014150b2401341c43c0820388500e030050300e844100d0700901c070300b9400a252503407070920150060100180032916191034280c1ca41c0100c1c480354000d80046001501040c40d17804171700d1040000c2d502000b064234052807183c844680041c042e00042c04024420600c6002c14001d01c00b900c8129001c5503084031403001c0101c07100c00708000c11440c03040d5090007070320301d00009030018400702c0c01d842c210b400146a45140ca4007440400c01822052100b00700024002c0c007078882e1603119403041600c10701407520307410f0301c03401c0c58035182108001503210490440031040c2044000c101304219a4121003490400f1a048445503c071142418100034002c20684a80f00001454000c0015035190440c441c1803034 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 219628066 1250 219626816 219626819
    0x130503040816090c0816050a03090b07090e010806090a08030601020c1908071202030d0f02100609050a0e0a0f0b06060c01020f0a08060d03080403141902100c0201020901020c04050a020712030c0801 86
    0x85c1c5401c90101c1d1917400340411440140d10040c01a8002c12a103602d52400041420003070f5241a8800f001f81e64081c00210b0a400038011080109086800341072300500400b410700e08118560790b2080740c40390042c000a400f00c0410403d034004c1003003408102008182c01d114260900c00c1d030521917418404c100c0d0511640a00041e0784902504a4428a8005d0080c00008203142030984603041c01034480b0382144209212208100384521450020703201e201008582820800d031680c09903a103080440d8010b401c0110487d001488044401c2101ca0b40010b445a01c0d5548000060780b9005d402000d18080d400012009a034052960047c201c07031185441d0642c558a0303050600100a00141c0c0c01408510214003240c003290103804001d0301c80ca1790b0483c02c2d2170320710841c2c41051410012116000564401640c00b12040342c540210080c541e4548000c41c1407000c100c0000f5500c40c00d091340d40e030086e542e40000c90349400b843d07012070f0001c4d50804100410b0032000c0300c00800400040800300c0004400100 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 219629316 1250 219628066 219628091
    0xb0102070902040b04150c080a080f060604051e0307120503030a050c1e070203031b010c02060a051515040503030310030c0e010b07061802150705060a0c0813050304081609 75
    0xf950143c4030058403090405042c4004440b400c0340a00c01c81003807200d50064000003a00d0030b00100078000c0140d0715a030080c10200d007803803090030024040d10701c5400240b20504c07003a00d5000282441440c2c11404c0c00b01000140c3c0441c3c1001141d070003071144480b441900f1070500c5000001507000c1d041c01c0b4000c00080d603458407041e041d80140d00185400c1c84100c800c2d100507400c0c40e0081e0600030700080503649894501c107482c26489003142c800c0e03c0e41e6511401040031345601444a0341e03101c41c21550a01061600d1b0728040c0603000200d280c248500c07210704180b604e01d00c490058034042c18025040b20340d01d0034a050300c600c00442d1803004440103c03001e003011800d50203060b203a904880ca041036172810600c050b40d401000d09000740034003e107031002c90364000140e076491000c021602400d01403a07a0302c03081400c0070303424098000d122001c61800c049120703181c107504c191042e6000300c8401030034864119900c1c1160071403013668080682031041302e001840e421018644c10003110300d0000d08208112b0601c4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 219630566 1250 219629316 219629321
    0xc0c04050603031c020904020409091e030203032214060609072a1a01230f100f09030605090c011b0203120c0c0909060403110f10021b030a030b01020709 67
    0x7210150540c00500181d501c1582200510754442c00d0143d015060140d144085000c9030025400f5080325070301c6030681014446040041880580283c1d00500000d8054078060750380e00c005081d0b000110741e1407004945140c00201070b4017503264892810000c0c49a43c40c043c0e50354240669016208100f42e10100b90600d01480c40140845542d4044038070406840d400445441000d4005590070310300c0007074101c0921144400d2030701800800792074502d07500342c20100c4400c0c001c8007150b03a4001c102511042860b9078504881d40c1c89200d851030038880700d103d1840b0444404510760f1004001d68205001c1c40300e0710b040850000c071907106c20303680c01500324048441c404840110117006501a00003001c40303044032048c81c00a1401c01500401c6400c480700002c00300d1014141103481d91540d8204405010030594810200b00820214800600300c401c0103042040d1641035030340010a1030366000458001d03c031080100503612051460503203465081b5240040d0181074984003903801030050800100f0a0105071 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 219631816 1250 219630566 219630571
    0x1002030a0206150f120114011403061519090b18070e0904020103150303031d070f0902091903030c0203070e0709090e0c10090e07030c0c02010305101701020c0c0405 72
    0x2640208899143c1d00c0018002d010b401041d103800c01201e9841c201c0700c0e01c603007041c004940050000007920102c0d0284032a8000c00c180c00280a42030815480700555034009201a040b042126005040d014a1400102c41c401072200c129441c01503900d0000b4070b1100340d84134070114202902d8283c00300c00e80403844200c01e0b9013103607242c01060400b0442d01c41801e0060046d0f034002c2c03042c1400184036451014440b8060216401200000d840301a65480d03111030140e0b08110440c10001841c519003854000b510985841c0200c0d03003420b501240c400070035901c0c0f68074407810b5884803444603480e607240c1c100184600000c29050b030281c414110300240600c2c041c8203040c03141c04a071303903408078007400c000c0200094492514018070b0341c801d00b80148010b90390307540047d0304140035448400c400b82c0341c401c10141d0b110005005505051030014100300e0360b0740240712035902540c2440e0010b16591007407200ba004d0390320b50f00200048003100c8914a4440c4055004051000701c81040740c2e10461f80700100310075110704 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 219633066 1250 219631816 219631837
    0x50402010903240e030417030a09050d030e2106150306070c03180e1806070203030106030b120706121d030403030c03020f030309070f050d0c140a05130b100203 70
    0x280c03007082012808403c11200388030440c3c10300a140030103404101d82600e82d480310003100750304001410082009904041410184000c0181d4207010400c2c201070003107072140c800d1340e010b210310009010415101d0b001850001c03600515000078040c0ca15520201d42034403481109ea54840e140101d02c017507940c00c466a0101600030001d1801b0303618081c04036a0f1840f010070450503c00c000d019102a0700c0c2d640307083e001034109151070007402c0c40d1582c50381440300514070100c0d566421400c24400000e80c00310840b03042d240c0740c0c100400c217020071102083d541480c445000c044c5001d6030a01080c40fa5110b400506250704a040502407400030441d2061078003540c0100b00e1041e44204401c000007801100c0b00e2910b41d00a005031010040302e24480c606681c0700310750b0701d900e0f0742041c02c0902c4034904441d90100541010740350000d0030240c43d43c84d903081980c2c0380980000c0c1d46000c034004826546101c0c2c2400035203400341682c032038024003000076001341100c240c00c24440c0d02c110240000c400e00c00400e54840508 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 219634316 1250 219633066 219633077
    0xe16050111060a0c020312010905060f010f050f16150f06050a06020c041d06040c08100e030a0c2d05061305100203060d0b090f070b0f0a05160204090807030f0305040201 74
    0x9410490034001c1c0000004d8000b917000902c03015145204814000d4028000c40001043c14034003842003140302c000c41a60031341880b69040e01e50044980c014162802803d03150720161703032200300a444c1e041c0c140c031a14004001114171490502000255002114030009803038007880901d88a2042180e0b0b426140030b5040107900c46402451580b60541289125040442e4105c0d0300d10402c00f0030600340740d8122412740b192907841a0400800d481004940c1161a580e04108416032007110250307164030901055004000c6506008028001c07a0340d5400d4040280300301a5190f1480e004500d84038040d002c40a0341c0c54051030f00003c0712611100020703681558840094000500003000310002904040c1245411640a00e410000904402c42d01402204020010410000e1401c1c1c0c1c00d10b1700d440c43c1c00441c1c40901c10b10200e0200c00d202070940d01c0d20320107820b14980350307058200c61010131390f4030040281d0f2140c05c10460b14140201a0700400c42d250082e130358501c000e1600da0055060700d200780e900134001003 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 219635566 1250 219634316 219634321
    0xc1e0f030304151815051207030204210204061502011d010c050307050c100204060507051c0504060c080d0903050a0801060c0c0b0309031207020618060c0d0203060d060e1605011106 79
    0x40c03244508019005020300c80640035502c46905000100e081c00382107000c1071b0002040b45c202d1906081c0203600c1680740c42d0035442d2508042070490104108102c2460410307071a003101c011956580c2003203000e07015401d041d502030343c80e06400a010b4262502421940070245812945e070b4001801201d0388218151245072541c0c5441c50225100e038054110345505000344001529805400d00041c0010201569119203d111506105040000d0812040003034042413140c482d6040c0c0020035907003142e002d414542100741071802d00100d80e04c02c68140c041c0052910441d03100309034004000d899041e000303541c3c014076a0780381c08064841324100c81004c7c00e4a0000c1c00d042220b600c0c2d8274000d56018440c00c003030300c0c10200480f41c0186002070a490800141e0802400c100362410301d46a550100801d100091020f800c060003150903a00c21204d81100c00d6400000052041c2c6030280781108140c1d0280003002400d10800020b602c4484030900c403a40940c91500000d9a98803c020803810340341110080d0043d40c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 219636816 1250 219635566 219635609
    0x5040f05011a010f0221030603100f0c03060902090a030b180a1415071e090e040b06030c0307030f060c03060f03050a030f14090d0303060b040b030f0c0705150402030c1e0f030304 78
    0x250402400c0550500c40d0400780411000ac0703006d80040c88008207008100141020400f50540341e0540040304042c1c4180074a0f02165609600b8904903504004100340ca03444059540700801e003001e080c0c87d185c0c81800342c95020003902e040c02550220101c0d00750746840c000140700c210503001c15501000001c0d04607403461040c0e400c13005100481041400d01510315950798018101c0c07950202c4050354010b07010401c00485c1e04003400884010354084007c0c0460b0f508558800f450003180d85d002501c099603400d210601e0710701940c045009840b1180594078801c3da0307840d003142e40b4405030380100e0000e40e0300b040e40e5034032a010b503200103850b41850881038108160030007031100d88250f1240c19010181c40b9940042c00301d010400400240c0009040b296070303480d155100c42803070075000d04460341200b0104040d40204401090034400d060040b00510940d48403400040e00e091020070034690300c40c158040c81181e41b814003c2c80203524805562140304080c4c22010140c89015901c0f07080040405030391200c401 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 219638066 1250 219636816 219636883
    0x30c010e1c0e0d121206050a0b0a05160501061502010b0f0d0206030405010b04110403050105340207030b1602210409020d06080f0a0c1e0905040f05011a010f02 70
    0x2d407400340016031580e68544070b1944042e4804041c00203c4d040b00040c10b0707800014020030b80900020343d05950624034220070f180d0180b060714154400c0010205100000c0008400c43d08011a00a0028090652150102d6882c10301d8040010f01662800b540e0076140d0410031610f4500d120002c010030f00550450302030209075800144121201d5507595100f0104d551140304100f40300c0f94205405803038908510700282100d44c0035100b140720200030241200203010008540210880c40480300d9440030000e01e00780e00d0112070b500020001c10710304c020800c1289440c0400b10249040707508640440400011f40344c1c01d04131038114141c100008020038080c61002341c00503c045088490001089659641118104541c0c81074071800c58203c01c1e125001d210401c2c0041c4c020700a2800f103d440b1401024401c0f0220601c1e20481a1203521000042d050100c0400d90303112680d0040024446c60003218502c0002c4c515087c0400e02080004120301c01e132a20008120980c0100c82008500c0644120b041d0f101 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 219639316 1250 219638066 219638087
    0x201081303170405071d01050d14030c19020f010e0904060506180406050703060611030a0c0c0509040606030b42060a030b040b011d040c180602030c010e1c 68
    0x74801090303292403040410a10703051103203024102921480d400d010b24251031071b0804c0700c000418040c0c070006208903511006540d400c2507100505039504040e0301c841c035046009105c1905064014445a0042c40801e0f441080c00d041c0f00301d80ca040022450401560715540c1e40d0780c05900034414400242c00941d140c0e001d20342001008213002d03a5900807401030300c0200700484007111081d8032001030014064150003200e01504183c244040a8a100134855070f990148009080c100101900c410040c0314484044a028000140000c44a40703411b06040001e04080d00c42150700c06002d800140122080c44030364000340c03c1c10310394105803146c01e10305405682078001d0310b145040b02d17211601410350ba03240010b186000d840d0700c0106a00200000300002c58000892035810b100c0c2001a100228100c0f03021b0f0741083d0021100040c6140c130400c01121302a100e0500d00302d461140200108a254002000c0c08071640d03240c000740070011800d1504d81d10754441d8035540024944008140111501600c03d024 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 219640566 1250 219639316 219639323
    0xf060c050a0209062202090406090624180308120a0c0507150f05090715020d090b0313120e0418020907050a030221190c05180109030507080102120f0402010813 70
    0x21880c041070205c482c009440d400d80c1a103080d400100a101c1d0300700342c09070034010040410200002d610740150540f03427507a854002402c90300ea88549049050003032a1030018415481e0700d03164640d440e803a0040742da50140142d2450258070b1000104594a6400380c40b0816a881d59614244000c5a903030500c2d4404c40408100400d8481c5502801d00c1d01c0b600c6213901c82e10000f00180b10740d620301a2081c4a03840d52680360790031900b00003461096560001c00700011a00038651143c1e1f60b0b6500040c40700106502c0d81c0092101102013850802d42e584034520781c1c4a0b60b001c5030200054507900e080c5070030000074003400135041030905000408080c060301c054040017506080142c0303807550b22090b1040ea6150411002081e5080e003040c483c0021051086005000741c1c041d080208803501e0001034424058501134810220026461a045034131450882c0000e65000c1701300c1e09000c0d102c00c28035020b90004941c1540e41c484003c0062901030301030b5015406250180c55a00594440b20f0320140e040c0802813098 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 219641816 1250 219640566 219640579
    0xe040b060702090f0414010507080c03150a090c030606390c15030b1903140a02060304050312060a0b0a050a0504120f03080603010902010801050906010309080c03040f060c050a020906 80
    0xc0260701c5a03803840e44030f41401300078000380749401e04e00b025590b4064014070005078541000c0290081c0c00151040c0c0000d40f090040c0e880b80ea4042c855507030101d031040707001e8120300b907801c00052018158100c038032200004c0c1c030705201c016199039007255840f802134400d440750255000c4000355056080e01c031102a40d01e0004410300d1018903100c00c110701d4984d81c001c05040c940e4041d2041c030203a1512076055107840807940e10400c07024411000020752118000a00719030055207184d40b455001704904214a6409031003140c881c48c081c240103440b5004240300a02c1c0e1b540d802c00040b00d030302e84160724109480d04900b245e41400107507682210030f50898030814003880010072010500007105200c0d01c0d01e10348560030b19000003a1624004010000140840c0c0c0260304000340c10340141e0308609650306484042da03130101c5079070b900001200901008039000d8031450001400850405d00070009200f0348100040d944005580e0f9441190f101a1902c40a0020341088003a0001860b1002045810030341c018580b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 219643066 1250 219641816 219641827
    0x306090503090907120b01080403080402090604020d14041103030301030f0303020a1b05010c02070501111f09020a0806040b010e25030f06060504030c080109110d1b030b060910060e040b06 82
    0x2080c3d10010030f40c0c3c2040450041d28041c0c45440c0340e4042c1603010301080c44c013081142055070b0050400c0c0400751000703108a01c0000080e04603225981034400b40f0160801c01c1c03040c95424142e92206c43c90540e010340e01d50210700030f02a01c9040010840381241d034000b41d4514084046e0310b00300c009400200d078507410017058070042e00c0030070041154961014000c000000f80303018500c0001c4c0c9000001e41c06141804505082500014008181c001048510319940302d250010041c0800041001040007035002d14460408a4404000070700148528410409201d859880d070541080011048a200340c1c21501c00f40109042c055000c01e15259502d6428086401400d031200401900d10b2034110300d002810102741003051110340c0d030380c2074000c241c000020041c000407074441d24201812110400e0080b40d48955010800c00c5801a20460b105000900b0314540c0d01c074500b42c40b21000548950344100d510342e010400309002d8204d41e0040303840310b03200c401c0b0301c8144005110142100300c00e01070340003009004 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 219644316 1250 219643066 219643069
    0x50c030307030503090c09091911040f06080d1d0d020f12060a0c03020405030a020420040b0d0b060c0706121d030c0d08010e04030804020609180f0112020901030609050309 75
    0x261900341d00c40d49443d602c03403a05d1102d40781b0b4140c6071441113115010001c1484000e900c08501da070b005003c40802c1815940180c10701e0490003404d0300110380c2280c580311101c10070500680c44001a0b81ca6007058400803840e41e8000c0b6410401d00b04c6228410282c070014010628010441030702d81c61014100f01180c0d601d40000a4142c6400002011250815000c01100c484248074070314601ea914141141001c2c1000c0220b80d0701c01540d14000c4c080c940d01d10445005403044004604a0903407058047c1c1d42b03685808407c07803503400c21551461203509184981c11146494000da46024021500825400e0302e441003c89130f21486143c1920010b54841c00141004040f40c0ca200c901d82c00a0000c5940e05624140303503213071601d986040020020014014488800400c00b03ca41094051a10350480e0b10340d400003c03218490124219800008103800c9210f160803901c000d446050302051841c01aa6100030049041d6640b00c40207601000520040c400140c0300c2d8887e80e00103000d041160b0500c1903a40 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 219645566 1250 219644316 219644323
    0x8030a02010911030d08190e0a140c0a1203120e0a050724120e03130e0601030e21131e090e0304050a060f020f030f1b07060813050c03 59
    0x1102100181d442c2c2e400c41d001d21090b144200b801003400d500900ba400041c040c01044e07200003804172840d5604900d40710030f408040d5046102c180310000b007aa108003521f8a0801d003080c044406900c018010858207071124a0180d00c0401190040d414029100c0001d03a0115030342003046450741001c907a607007000300001c4c2041001e559118410350003030060b14200b040c403064007403005900105002c200d00c0b005400b03541c4010700311040012340b0b10200341ea141852495066004000425402c0d06131103e0000c1d1005180e88820b01030102038a04001903031020320a2605c4444100100031002e07075010412882018050041001f820801e01c8500499221145492201625801d2210840e030059051207890708a2054039070f5880b000c002549010f15107004a004003603503102d940180801c210106241900901103c4400d031000c05c181d82e07640740c0c5030301d000242d03400221080d040015020181d03003455000107030902c103444098854280302c2c1e17541c0300c00c1480064028000ca805014400b446540c031744040 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 219646816 1250 219645566 219645577
    0xc0b04023709090201020c0114040302090c2a0714010e10031d011b0f0201020d1506090b0408060c071415040b06040506011205090705030601090903110303040c0b130803 74
    0x1544603841c07540001d492000400290000d900e80c0d8502540000182c2e000207640c42d0ba0b00003800d00105207610300e140c040d0745015582c03002e90000ba1240401c10300c540701000801c0000d180307035055032010418a05000b00ca000c1890101c00c5688000005d01411040e4980c001d680503051400c2c092860507100407c60903c21500581c0200303840d401164500000c1802c04240384045800801c414032291a074034031010340c200400310070302540b2034000d11403510030340490f1242000c12030140410b03440011502e950388868411100043c01c80000847d404403018221402c40700304c40c1c0141415140d02c0710645060740447d5040b1608205044c030744104190078020600202c41c02c0e800d031901c40c901360804da01c4079000100700d1485075203082c00708802030384c1240034107001d409100c4001400b42d860b0f407005450602d198000e00c0e41441071000002e6104030640103819058403a0356000041c66a4140651344c82c00306540040002c1c00011090086d800d0038800340103424080b001004105035600c0b441821540301 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 219648066 1250 219646816 219646879
    0x120f061208091c0c0e04020402120f04020306100b040e09070302090c12010b0c03180a080106081c080601050d1808040e090c030c1005030912030c1201050405070c0b0402 74
    0x820b4000c1d503442c0c01c1d01e480b400c0a081002c0002c2281c40341e82d400d0200000d81c000c42c0440e10f00b00c000718066446075815606441c481080240d51400c00d00000c240d40b00088504901c244680070000b81440c0820249504481c0305001c22070030309040c2000c03040b4500c0004e00c6101c491007460000000340e690320403d1401030000b40c0d141d80c0d0310301691225003c078403416001171008a03000c20031f000c3c0c580c1001040340e44030780d190041c0c050a0800000020081d2030726500003811036090500c01700340000d01080400c0c040035509203d046000c0e0103013064410080c1110498049602484008101c181c141c000303480d02e1984601d4030b031060394250340c0c452054000c1c0c4c0200061503860020460101410000b00460010840081c00d20711407900001c2e10310766040ea01641000004000700f00f2448040107040d0f0400b58020286840340762402515800b5040000140c0706548a0000081d80d030615200c3e150041c8071583e604146d00c1801e4554881040000e04200d8006e030700030820b8610914258407041c500c008 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 219649316 1250 219648066 219648083
    0x27060d020607080a032d05040606150306050301051005030c060c240a0e0c1302090607060212090d030501030f082209020a11011e1112040309030b1501120f0612 70
    0x44c49402021104d0303643c0226070702070f0a1105035150003070030341d012020700c2c0426030b001c6460b5659184c0000684041c0d8098820700d89801040c05116415407c84002d5480c150004c0050f50360341d40d00192a68030610806400d42c100c440d82070424107000c0020464926020b04403200c9030481c01302c01c0840b4000713103810003407a03003920700b40141d01850340101c1071b0580040b001044094240c00010b10134444901c0100100341d40040c9101180d241d20064521080d0050421501c42e04100c20303c0f4292402100d1681160181e1249440d171103010b031082d107042c1d940080d0032440c9140380b55a01c0005034042e00007a5801e449425941900e05450049100544182d400141c0c80310039040d805044241640050070469051468034141e00021482c1642c1e903851501c000300d20380c113101c41c400641e445086a509081d201c4001008240358001da903800450707110300e507a444113540b244202146112440e141600060031001102c0f10700c03030290000c00144d4240000042c0c82d07075131031404003107da68101040b0703a8101e = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 219650566 1250 219649316 219649327
    0x1b030212160c05070608100509040b0c03090a0b0a050618040f20100210360201090506030a0501031101030e100506010201110a0c060507020304060f081e19060527060d02060708 77
    0x200300c7c444010051600350b4814000b401c05541e03041550304000c11110350f010001c400200d00e40da00304240e9101d00e8000e41604258104103007000054542110321030b01a588ea100340c001d190980820580c41990480780641c001c00d202d948422000d242c100301402e11640e6070622031000da44000802c0004c00942c0c0051030b5044a0071501026203603007040a0b900d4401071f40a81a5a60351010f0306a0790134255840d44280c030070075100694104041c0e8000a410060110420103940010b86c000d0703059034010040504420345d40c1004400ba9414400700c2c00182d000748060100c0204650485600248140000f10f0b8140d80c465500d02d00d50040c0d00200001002e8134146810300c101e0703109841c1c000f1a81e20203146000d09081000d80200f029400c0703039041180c4040000d0144c204030603500840d0b46401d440d2261801c004600000c1016070a500591803880d08200003024501044618050041600203102d400c40b1010f03041ca540340000d007882d4020000c10074001c0140d885070010803503244241901c58441 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 219651816 1250 219650566 219650581
    0x2040e011b02030a0c02011101090c260c180a0b130902040609140402130f1128090b070f02060c0d0f05070804091a040606031b030212160c05070608 65
    0x40154074060303082d900108800d0051076400403080148580a0801c64010404400080c6c0108607412025011a16500020030081c0c8861014490302c500a078059103d508282c0305c0e40c5d1911514040e1035480040319500401405d108040180d101491b000001800c08020002c105045502c40c84203003056034888031034046181c07074480e82d00a8050000104184009502034504000000d88042e1107600c000e80201021030060700540701c11803c000c814880105091400c0040b600607055241d042c0d100d000b40d94a80a6a9061300c58003419180e0f150310b001460118090019130180106880c0c83c912a000500035845c2c004c010715050030840c004000c508401c580c02080c071100300401404004081007504081000541030300e095407403482001484031500f050b03c0d0010115482c1141e0018240580012490f40590102e03c013400351034080b000078045140124101c3c0b00e141c4894041e860741c1000703d824011520f4000e10304c10f8681c00d010700c03190865100c10303140c40c01d5030b0300032000203004030100405c1 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 219653066 1250 219651816 219651851
    0x905010306090b130504141903031a0a1802040f0b03090601060f0e060d140a090b090102130b0a0509060409060503011103090a030309050c1e150a05040b070c0302040e01 74
    0xb44200401000720290300e00028100d0800003501c004030a444001003400d0026035403442d5041d003054000c03214103140103a6456002d03800018140e000c40e150242548214040345064680340400501208420b4149490010503540c45081105056400e0102140400800394858046d0100d40f4035191286880c1e600d041c50301605030004000c0000b40e00850290980007100000009401c40f049a1034009021a410041450318426460b08008a0034010420032680c002080e00780030f50740b04421a03070ba0181090030303841100c001d00b003000d9a51404000c80307035a0030003400d1564254030303040d40740942400000d48a80c0085c0c00400001e0f40c2d03404108150b03d070912030119003908221002c0d0a41ca481c500d429210a0b001c000a003d150f20b5445843c2040800d200a60080c4002401142181d51400f90f041e900401100490300800c011061301c0400e40c005010b490040c4100c3c0e035010b06d0309007401c809040541102c4000c8900c1d03c3c18003008401031f40c40c0d0180d0160880664000214504a800030581 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 219654316 1250 219653066 219653069
    0x24110c0604021e011b050c060a050304060e12160c12150e1603020618040219020115030503031902042c060108010e0a0b0622030510060819020102010b0d030905010306 73
    0x21064011010f20160b40c200b901240344069115050b840c444090801a040000c181a00359000000180e0388030320b40d4000c000741d4004c9015120401041ca008850b407640c0724110704038020229802d001402c500d070302410310309084030700c034030749200f5455a5115a006400b00c605002c1f901801c40c00c48011100603188a080100b42c0400c000f045402440340f881c602c88501c0e80000b0703004410009058410440d000c00200c000d174400380c81199101d00e10051011508041c154540040d428642000c4075401c0d100c40c180306484d00200650720b0758403030b85403914080c3c184210308004d081c0c01b40701c00106486454440464450340740266607010080078540200d0010041c66141070100341401401132000c94450303107601c00c0c4036000c00503480d044400002d049005010034520840031b442c0401034607110082080040b280300c0c204951054000c0005103090712880d02581c4025484526030120300045007120002050041c00000740f2503c944012030a42064687c00340d02142110808006950b8075108220 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 219655566 1250 219654316 219654349
    0x105010f0e0901140f0901060503060a1410030507090308040603020310090c09090e010b040509010905151306090201110105070305010e01140d0b041a04050a11060724110c060402 78
    0x40e108007540c000550115040c0640f100310100000c00d4070040c0c03600758841c6840b101c0208507900355a9603d030010303c2030388221460340c01080d00c0180001c4640c4a580143c59080c002081400c01e2a1468401c4004110080000b07040000c7c00d0030000125400c5001080a86800c0d6405a507e2800c03005a01c86105903600038801c3e5407810651508030f41d4480080401e40c1c0c000c00300450140c181d045028058492143c0042c1d00c40d10301000d03c8189001540701d0180c1902c03c0c0c081d100141c40200031903240718000c0b0780b0007031a4085450360300f0010781c2e81d42c040f5404500c141070460109640101003070854100b11102c038046940d50300103000110000000c01c0c010700c1c0c01141e00d0b0889030311501154004005040007803800010310041020032422000b00c4204146902480b12a031806080440c0d951541d45030603500218220400c0c0520700340700781140c1c40603410240340c880c2030a0620505103804201114103034801c0c3e840c3c40030b41c00c52100300300074a14030070180f004104134181401000b241000d130309a0507 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 219656816 1250 219655566 219655577
    0x2303010b0f0d1502040f0611060705161214031602010e030a050403031d060a0503040c0f12020d02130203090a0302060a05040b0c0a12110406110a080904180501140105010f 75
    0x2004698402d280b0008071544440b00c15520846482d814020f8011600310000800901b50041202e692044d901c062800001d001c5035002e0300c640000b911940300d055020000d40d080c6040d40f401141c407000b40c00c0c01000c1503190181551915100c100c103107800c15038805c02c500000318a84854075609009000980320310502540c40c0003c0c402001d00103100e94400102840740e01601c240b401c0302036a666030340070280a06141c1e610440800d0041a0703504c201d8017140c0c44174007101c020800106ca01603032001d481c003c10a514030504035408100344019401d108a034005081c805100c0150f18a0016501a40741d88005104a4040b0304c0c0c040d04010005203480005440d140070000400da010703410b540c01112108009964500094084501b096071448401c001810403c4010405944400802c120741003a5038100141d0030380c41d000c944601c031100700500072600c18040744115103000e60121421040614442c000c2494541c1c4050a40b0039510400d11003003a034100400075960002c1c8004030303016541c0f070309 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 219658066 1250 219656816 219656839
    0x3042108240111030c0f0d0809100e0a0c0f0602010b0301020f09011103040906030804060806121f0b030f010204030515130b130b0a050417070c0b0c03042303010b 71
    0x12624a21540c40d901040d00c24041d4841c4860b4003a20600f00c40c14000f0083e60f035142c1990078110f07a035142203500d2480300e1181c101001c0682d4402c1d000d550158040e00301900c2880205a01c1102400c0200b00149a41c00f03130b440480001000161b0303103002485500702c0d40c10101d103001400307805c580e003d441041c0a41d004010f6810344840b03a2040b20501c50090800b40d4018140201c1c03541385028079000f0035401b40c5024004024408900064011203400ea524903003031b543c0d6141072040a1a00d10044012540b01c64101d26030b50000f60070110700201c4501d4005180d10581d000241b50185100d10181a41d60020301802407000038001d502200110b80340c2d021082c10450240300c81d80f9440c0c000a03000c0f01c94080820041c0070300c1c081c0c80c10b145e90031020003141c50030700c441e1980051405403400c495101c011345881c000c0075403100940c1d03001504800d600191929002d1004110703408640c42d01001e000402c8017291501c600c0782100b60000711036461510900020b0241030844101340081c8d442031034032045 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 219659316 1250 219658066 219658081
    0xa0609170f0d050c04030b07030203090d11100e0c0d0c05090a14041e0c0312080603011109090903090d0804092003010302010f0e0a080c01030f1406011d040203042108 73
    0x1180c94610202c003002032180d4035071940c9000c90046820041440400c8000d02943c20390680107913008200070007c1d503160b066000d001783da51000c655050b0100c0d4101126041c100d480315404101c90429100c16682c15244c40000100b11000b0400101d0317500201020500c03503401d14150f1075600241e90282001000c240c603480360700741a00240b000b010300c0041c1c010450306420400395824000d81c480030520030240c507840c0c503d8071011481030590000b00f4000010b8081c0c54140200301107031540450041c6420061028000d0230800180070300c5880c4420012740301a070721b402110442030f5000d011103c3d140d60030070483c0d009490300f003044120203e20400d21455108088001c0306d0450380e09081030002142040400e40d24121000c1380303d0f6100d4840000050000c0f40401c0a01126100366010000b400c080e10786001144c90741d07803118801014107000a5259401005885501c4001c02074141c2c00007502c2000030140d0f80704581c1200d03290320112030145561142540380c04070314118101004603207000403 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 219660566 1250 219659316 219659347
    0x80105030c0f090a0609020712120c0f0309210f022401060e18010603050610021b010c02012705010311070f110409080f07020f150f0d0e0a060917 64
    0x20304081c0f1440d8110007103a0b11450b00d80c080d000608250b001591140000d0605000e210740d4012039a0104048020322026901c4030f01c81d05445020350344402c0821008080120001c000004007224404030110340661841c0b82d003502e10714036030707229500d00c104210000402420074020354065101c81400001151100c0701a49407070781501c096180440c3c00242c0200040d1458540030569080d626414001080b0f0f654940c0005104a41c00d480d25188100840300c103e9513103011210f24a03008044000d040229842120510081401450400e00c1d44094241d10b003804181c18018501c0084515810803e951300b600079489629010300d0b2203400d00000b510394001071280610020908503101d00d07040000ea556511407a6040d4101e1000c0e500c901c00c604000f021980268000d80c450101504040d1152502010340040e400315048881d0800c09240106995500304540621f0421340743d9401c00000c107001c001d1b548002e4080c01011400409905095400c0c0074513030801c0c3d04450f03080042244d240f2560 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 219661816 1250 219660566 219660589
    0x3112d121204090e19120c060c0c03020c01050702091302190602011505090108030307030903050d1e1505060d020315090f0412030219050c01090b180c0f0108180c100906080105030c 79
    0xc0c80300001418002d0200c403500310f1f100004124030310308a10710284540c0708001009003440b94013101c940c1140c100c0156454000c0040007980041541c0003d40841a200a1441c00b203101511540e03909400046641ca010003a800c0b800c0140c4d91082c81004c0e603400b0440c1d15009007815200e912643d41010040ca0300d03440b00a2180051540310071003002050720038812030300b11000303a107000c01241c80c1841d07541c1c0740300c01e00c4e000e03202c2105d0070610a1001d0b1121812400102c80008005a251120640e03446000c0c0d000205420400400d001a1700074544403140b8461080c0f5004503c03102620b0540342c03040b5402c0ea00c003020810584188244d030b61307400c05240ca00301d08882a04082da2103242e8841168050501c10000030100340380502400404100c0c04070080381e0481c07083c20b907558140c841061240e030040c00005640050024408604502c0c40c181d4074400c00002c034016120114401008940c041e44030362060000074081241c1041030b181c0c00a0400e0150504801402d9201f00e400001440041e50307 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 219663066 1250 219661816 219661823
    0x60105070605250512100b120c070210090e0709050901120507031505101703070b0a1d0303100f031203020c030d0c0903112d121204090e19 61
    0x3254045140c1c1c3c00c20b00d41c8508400c00001003100c07080d6480360300900741e81005401c41403862090700401d0446245000050680d03164049030303402c0540342000b45c21812000b6001b90100502040700f9000b41c0c5580c08400e843c800252a1403076141d180058070301c9010300c000c0c555010440c2c04281400f56660702101681192402c0c4051100d480c6941041c60505101d41c2c402044006007038541c8440c0881e80d00032912459592a4030608a5541c10900300b00c2e160415003141a50003c100900000c3e80b80b90702e45820442660340001d20720000900c1c4010308021042406182d4070200070808490018152000505482401c0c0048940740d980c0707921503002e00041d160b088c19008203801c5440c400400540740681d800c01c0050200f1501d040000d80050241e00040c0d4031180a02c420150ba81088614808030301c03503514002c281502c0014400c8035244560000c0ea41c02400f9010b452b0a030402084406c03114641c01c0c0c0010707070702e5280c50004000c5070f6418a000c14950002d0f1094501a03d10710880b80d41949c0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 219664316 1250 219663066 219663071
    0x90506090a1401020c09090a02030c06040e0a0c03020f070302010f0b030c1f0c0b07110d030209060d200d0204080c010908100b01030b0a06050a020d050429070f141002030601050706 79
    0x1200c2c0141d041803400d50449400111540400031815800100050141c2c000c0c0c058409041001050256621603401030081414452004c503440e5042da030b1202c0400c03186441c005040c4840d001c0744041e2030b4000c01c42036006039151402c00301901518400e400350b1010171402041b825454401040107004190f080c07881c20001c5802d102c5200d40502046104981d1000b804119850060f074090000d1a00310365241c0c0603c52000c02c3c0c040c240c024800c680c02c0800050900f8200707950307031100390050300400c0c440503400f60703004a100d555400c19101a03c0c0b0b44030404009038485c7d05191495180c882020380003810030a0781d050400400c80041241e0240e1910745078007040214070303540140c0c040d000e004034494024002000c00582142d120002d490983c68039030075180740182c289004c440500490084124158502120035001030006040e011361a0605205c80d0400007280c44030030a042400d00d0580c0d0710700c48a0800d008044040c4488201d260713040b0307811401c508207400020418040c1c0d64004184d070740d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 219665566 1250 219664316 219664349
    0x10507110c061e040b0301150f1b0606090606020c1206010b03060904110d060207060b040501060504050415080f03040f0e07050d0207050307051209010e0f150a110d050307090506090a 80
    0x402ea00001a440f01c03030340140644d030382d17903d410400c4160705c2442018000090b040213100d03054485c904030080c8507070b2996158441c80400100724100c034200d410494041c1c0c0e503084001582070060103010001c1c20343d81c001d002d44899003418000760281214500c0f900380c120703030014010890754406484e00404240c541d21682ea4417460080010080c0c110525884021a0345500400c20150000e00c1054070842e010304c41152400140000c2da9028041c0340c0103d103041c0020301503406c1c1a8001c42000c07070440c05a055072035070785034000c2c10031071080e06025864100060a0011030380e0008404014814151a2802c40c0340500000f003490044004540d99141c001405d541804020016124030907003000594064034041216103060b40e0181c4017460216507103c018079007514003400e2140c0b00d200060500030007054860089070003580320201c0801407094484450100000c100101e042d6681181c441c031f039990070a450080e11900c1d0756441a40b26040801c203061040d10b840003103000300c4403446120038954 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 219666816 1250 219665566 219665587
    0x515070b0f0910050405060601110105040215030a0204030c0b04080601060212040902070f06050f040203160506030a0b0a0b04060302120a0207050a0b0603120f030f0901050402011d03030f0703020c03010507110c06 93
    0x1807500c5030143c1900348424407003405404581d20f07004010907220800e01010074060103003641c400703c1d00654080440d669a00c0c10b60208001154001540d80340185013035146c0c0e9034510510706581020308a0000071809021140040120601404403030008022920f542807641c1c00030320841c000c0d451800e0300402e0490820030380c20007017540b05a03c24018012031410700404181894202e5059100344290b0a10a5031100301014a0381501c001038072040c903642d01e5140d01400341c481ca0420a03001403061000003105042040a40054500d80c0d5000d0380e2001c821030780852880c0040c004011041c4108a400001080040e0140c072650f801804100c160f92420002070810300202000d401c0c0107000a01031825985042c019480742d1207484000c070740b03900d0f20b145d02030803a5003c4500a0101e285610744040d101603010501803440c1009080306c1c58000402805007080c0c00240084015a020a10842c2c45280030f000f4a907101c2624600040d150304001c2c3c2c0076950f800400c8209010303903c0040c003403020 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 219668066 1250 219666816 219666823
    0x6030b161404180605120703020f0a08060702030703030c031a130e06010902040303120c080c0315031e010c1404060e0307081b030d050304050705040f0b0901030c0515070b0f09 77
    0x205110300c40300c607103480d903803c202c01a45004000d07008103145001d00c0480d29140181d10060440c0c60300e0020005181035500340400c0d1769111014650140520f41d0029041c2800c105040c4101e070701d980903584075401d83c50090180d9081c0700701171003414200703001038039005e00c0038004000e100804c840342c4511130310384c21340040102081c841101c1140200000411400038580041085030300c00d54801e503d40f84001180001c4030f8942039464001034410000c03030310100001d005141c022020f10080010380280718002442c1c40007206100a01d4601e100120b2040c5500303204100501e1410b0522030400f414807207031400c603403142c0c2c007a1509010300b00400d1281a182045040094046582220720f000e035918640c2d10f40054500c0760340d01ca8451002c0010005100f48150b0f4050365000340101841c40c00e0000300409496034684840b038850707075201c0005440c2d8520361558003c601841d0610b503600c0c1080e0910951102110050a11038000c0001c07500190b03100c00400d900034442000b1104c0d0340c54010f038180c203 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 219669316 1250 219668066 219668087
    0xa0906060314071406070201050903070b030a15090902100f020f0a0b090f0a08090906011b200105120f072c0a050a0605073306030b06030106030b16 65
    0x803464100044200008079815414034034424080311400b960b03400d41c2802440b008034255410207010301190b4015401a400380001440003003e40702c900c0d4580d80c1040007034008841e101d040c561280c003e1401d0b05100c0344400b002c1c1c501c00b401440341c04070a80200f50007104030400041040791104610580d10700c24094410020440400d483c0c4010342030070b01035442e401c140d40c805050b0040184101128070000362120b09641d200d52603c0c1080041d101708410100c0090074681441010031440f07254400000281002c5842101104134102114606211241c1281c0401d810702c1010050304100c040140c618903404200c110b400343d00c6680e03003041200e0003080040800b0340404070b92120f004040300c5002c1c10685180c1551501001907580741000303040035a0344a2000800c80400c00d8030089484501c442920303201d0100201d02d24004890040d9840d9080b060b100c503080d6441e0400d0007001541c5440640003042200240010f40c10354590180704240585041c4258002d4915400c21900a40d401d08 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 219670566 1250 219669316 219669323
    0x1021f0e10091205250c08070902070c0e04120c060f051303080f130f0f021008010303020c180c0310051002010e0613020f0111010b0a090b090a0e0c0f01030e0303270c15030a09 77
    0x240b23002c1e0b8070b10300071002c0d4200700021151521012400f0403140c0c50079a505218581108101145040c002003c0c4c5405208000640300300d074aa11104400d0b07400c2d8002c4501445052003e89894505820700078126240a4903c0142049210900c40c607800800da52030207103500301101400407030341c51508120041003000002d40085032811104891600105014101c9001c0c0d000d544015120604016207908400540d8500b6400c80c3e01142c2401607540141d80c2c080d50200c20601407a03110301c0041d0700f85220010b000c0060b911141c0c01c2000791010b000c0d0a4121502c0900711072141c1c2d240c3d00003a018510304c204241007040307a031070720340f1810001d4100300185440501900081900c0721b0410003e00100c200c610b008880c4007011600003801c81c0300d80450400c641c405081003801000c2000b001d54a00d0880604141c2c650807581181403081c402140225000311140011008010714414100030966505c81d49420100040c4481c1e164202486428a8070b41049540c941d07a1f6410040288a24800035 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 219671816 1250 219670566 219670573
    0x7020c220e0a0c0302150a020d030b1215070f020c0a090506010516050d0e090f06011112030a140709080703060504020607050628020901021f0e10091205250c08 70
    0xc5062201d001d000a083d240241d500c8506003681b142424014400c2e503103114010b83c0460403181c20340c1d00c698006003805000401041c0184101500189070064954100b5000a220b0041c0548560007089021074244140003401a0088903400542e45845500c505208951100001101d0b40e2007207081f1008480c100c2e000c0c1c100c810160030b2507030b81c80040e40c108030042045810124024500010301901c01c42c40b504180b051695520300445982c0e020000652481c41041c02c082c1d0646400c1000d1480780d03c10540001e403922105041003010040a8100c2e002d0101f0b18909019012020401c242546d07040a8041801e8944d0302c0803c0c403074403131100c01510a00900f000d01410441002c0c0100b5481680aa005070382c41104410340101e00c52070366414050f80c01002c0a82c88440520310f01002040398100002c1c0c40303840c11030725034203012410004000d0980c2c0c54208504008298000c001174014601d09030381050800070010502408141c00206216044d284107000c005018021101030200035065 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 219673066 1250 219671816 219671833
    0xb07022515080f04110a0911090406060809060a0c0c060c020c0406091512020f0301020301030308040c0821090d080f0409060911040b0f090d0c090507020c220e 70
    0x100a2800d6039008111904400340d003000e030001c1c420990a030248803402209501ca443d10381c0d80d6001c4c0d4422001081d0012140781c00051400700f02d21404200340d4441000d1660f86d0040ca08220480340c1541100081c4211441070100c403a8001940a9112460309030005020f080160166420708031030300c00520103410000200d003c0d540c00729410102e203a09407400e1001684601400040e00c00c240700c04050708981c0071b810004100c03051040c24180d40003410080c09040301d100401d0990b8030076002030300403d80900038001040901d411000052900202070600c000d00031034401000c7d12032052140b080640419807001300d6403020402ca043d254402030710b0347e541e01c01c40c0e40c20585400502c41c02c90807074904800003880b603659016070040d075070f58544840d2401d030801c0805c00a07030704403030000c01d148081881082501e0f10340d01d00e1810981e00410103144080d1418144405075800240584210b400c036007041002d82c0c4a004a0386e180c14901100400c2d40d0f000700c4003180041c00141c80259491254208 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 219674316 1250 219673066 219673123
    0x50d030903080a0b03030901050702040f02040b0703020f0a0f0308190e011e021815070609060603060b10090b09010507151a01050a08010e06041415040606020705030a0b0702 76
    0x50040c611036126604035544001c00d1508a420b40040207405800030003091400b0b40c8540000e001a5100620000d90000001c9270107049070025003101180400000341e80d018180c04010054800200d100100f090401d140d46112081e132541800a050000c1070000c207086000022401d814032004c0d07501000304182c445049806042401e0000c02c00c0d04a800348540003102ca4001c0f10303160310302c03420b03e00c0a00c83c0c140c050000f134140100c1c81401468081c08000c0c00607100d80180d551040c02034001181c80c60075428194212122000030034490145034210054054101d030130b0104803440c00b1700d000e0f00ea011440c016103581c802e0b113800030580c4044c400f501041040d5a801a50380c0c2c29101e010052091206c1c0c01500c40c0d21980f071058000c110032800401904810007800303603120750050000300340780c41d95400b0b8160141d01646c1511419800240003801810140705060007401144000e00300c4a14100209071a00d00d142000341041051800145085000f088080f00c0c03070441141d80030921007002c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 219675566 1250 219674316 219674321
    0x40c08150103020a080d0503191e05160306051003091103160323030301120507051507020405090c0604170109021203120c0307120f0608060709050a0504020c030a0507030903050d03 79
    0x124418034555801144505c0d00081e80c058458460315240d02d140c583c8900c450249c1c1d41801e030404101e4480f0f1000c0014840c405503040c42503056100402c0d00d0501c200561a1002681000e41c201880d11408101503070b24000400010340c05805c0014000c205401d06407500c0c2d4042c490342e41c0520501407902006165080c0301402c0764010070341c2d00130070b810043e6601091a004c0203010141da0081c4014041a9410540c1c4034a1038452801c5034840350752400800c4140c080c401a144054101190302c0f019820070b4041c040c1d0021205001d00030568040f000120b2500842c05114030840e030350460b851079403030300354400d481058004103d8440c0e220a027200a03941c3c3d000c02001307540311060740003003021110b848060324014001912030044080743c40e43c00200a00c00b40c188521155100c00e0002100142840541e0107034104e035441000081c10b0606114031245103a2146005900c10440040c400c24040161740c200b03210341c509203980312090308048035072520076000580b00780a12050281400c0c0c066 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 219676816 1250 219675566 219675569
    0xd0c060e1809070614120117030705150105091003030f05070303090215040302150909161806030c110c0607020f1203030106030c030c08040f1b0e130c080303010f050405040c081501 79
    0x45d42c0b41030300b034160580720310b1003030181050704890501e040005104507044098088800b200040c11a0309220840d1a0f65240001d01c140702040100300c035005000504000d060507500103808010b080ad254515a8001c01d15002c2d031005c4406c0250110384041050310036080b80501580081821813020382540c1c56101e030340d1151104070312841c40e000c43d106201d58102c0c29610400001400c03e0550754490b2040e14140f440c00340d0440420500000c00341d01800420040d03005081950707000a002460315101a111200c14240b10700d06901510005555a030340500310742032a54152100c90141420801041d0000c1c0e004540d910b90380404400426840d50540c03140082085660342401040004031040d0703104107060314050225164910304c04080344000545007c0025600b12080d191651220a0700328480c01360344a280049038021040c0078029202070460180203ca0041c6245501d41400c0041d1080340d440b9007809162144005020f010040d4180c40c001c0602406554171076401c801e411a20038001d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 219678066 1250 219676816 219676829
    0x130b04030c0503060f101a0d05040c080c120705040c05301302010c060515180a050115080109090201030204050a030807170c030901050c0a0515040b060d0c060e180907 73
    0x3804c00040c59441520015400360120b084445081401c01001040311b8000030200c1800f058100040540d9070240e2241910031401502c9a001050500d18618205a0410300c064410007407001000c451003001314010b030459008079070004050342c204509480300d015011510150091941c011030301c1c0003001c540342c00750b0744c90311a45204a0381c404802e4805410b4031030019001030041080940021203580c0925045007400d9a03100b500d0000c400003a031034000007100d90074800d016a0502c07622500e94040e19016001c4001c10040e1b1041c2100c0082202c61f05210704403050b921446d81d8000d41e4000d034110340103880058041c4102c15120704100034981e014403000c03034050750035200310101106000d06131751980ca9030708040c500d0b003d88800112096005030103c1034040c010140c451001504c02c200e42031400001404a08141ca8a41000000d084008120754019070758200104005014440220250b8105007090340d0198000c002180311040070302410506103441c03100f0b00ca40d0080000d0f040c8100d921 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 219679316 1250 219678066 219678073
    0x123040c03230115030c063c0e030106060e01260a0207020117010b1b0c0406080610090506030307022110290603010504050903072f01020c1302130b04030c0503 70
    0x42111500c2e81441307440701400154102005110852080da0041da400d100300c50407040103544090002e40340070040e106940c6010044a681800c281c00c80d0340f04013402e070224000c005191521501900c0e404215001604028000e15445066902d4010414110400005242c451701d48052240e000b5840403805078003141c0310500a904c07049400c054141a82d8002134860300b4144078130b4401c44d0003003039041c550b003803801081d0030a400c03a2100e10462006000d0ba40082216040a150040e1080f5482e0000c500690420042086640340042260700c5594191446240204003c022030485465007159003000d00452400351450842030b04840d61124141c1d50b0685000360382402024980c02110115401ca001480100558a030540c4020f91102d036004c02c0d82d10b8003055a407080000d1a013681d000b40c00d0421900d4004842900e00e2800b00420030a0004214140075000045c500c0c41c0c00280015900340c00044181248820350034840007004c849804540b00c585a1420100e0b4051901502d0f000e4030 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 219680566 1250 219679316 219679331
    0x5091504092102071a030403020705060c10020d050109150602062d10030b1e15040209100914090405030304060c090b0a030618050105010c1415010305030c0601080123040c032301 78
    0x485c0001140d00503641a00100604c0307180105205403034000c440560518050000c120070040c495000507d61030380c0400000946604002c010b0302120014040b01d400e1845699080c480f16800040762600101c4c401d140403105240361180c10090810200f6004a0b000d41e00140a11034140042000c292403190030141d446642d100c048a80300d2500c050010b48030380e500c2010510420000c1c800c14000e2034007070720161900d0300420114003203041100b2001d0006460700003c11001511760031901c00100c084444a10354140350b101c0a40d08e00024002802d03181e43c441503003c28501503000c00008009020400d51140c002c2039010340181101c4c8542c04054890400e44070200e11a8071130b0034180c50b016102c545042c0307015103e4003441007000c0245071803885000c9500241402c03421b14580250f203e88021a03860040046103030030203034181d00c000000d0703041402404682c9211221130403c8000e080d055680c1c0d54a9050910502030b296001510341c0544404502e1860100e4001c04815214540284900b4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 219681816 1250 219680566 219680609
    0xb04060b1c180b10081e240103060f09020301051608011509060c06110414030c01020d14180d030206061801030f12020f0111130509150409210207 64
    0x8480c40c56491202d41500301d06480051100510240c01450070721500703a005460345009494001400d00d00c1d250002040984680032104101c0d42403551a07420106035820109203070001144410700000300f145413100d0210203c45401e51006205680050091000c1d040c49078904181c030001d51070b8000003c52150012600d144801701c18403c0e00c055640b126a403d1401d64201e8500035a0b907021207200da11176101400d2000c2039030107000580f183e81c088400c4a20346030105031134a030749001c0d400c0c15034004c3c003642402d443d08290040c0542e1008601155601d40c10590312010b402c11520703681d4810400101841403640c0000e04522a0380e080e50940340d00c040c0c1490030300c0d0181013444010100c603004100840000d12211413642c40383c000d40115103031410525460f90941f50701044019245501203910381c0e021454202400c0142016507150b01c40e03060901c050180010000c60241c00795407944c1488013002101008172030a40c00c41c211200c54070140301030080d1106000e101d0300302182d5a800c40d40c07030340 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 219683066 1250 219681816 219681821
    0x90708180303060303120408070b04030e0a14010806010318020405010b03220f060221160f05070c090c020a0212010e0709050705091e10030b03060109090b0c030a0b04060b1c 76
    0x280c40020005c42c24411030740b99084d51260018021100044140208000140001960341c007480c801d850b80000e140300141404820320a80c0d02c1021420400d10b080c00140e600214110f80121084c0381c003013040e1a03002e0381c2c0d00528925080082d04030345003d0001601510000166001c0e5040391017000d4440c0728100210302d04240744002410310074032082039000007541540102605501c0050314107085c40f0440d0140441c410890b024404445844110201c09900194202945001c1d060690038030b4029244c0315504d00041c00340001d01e555441542c10703d24020811a031440d540100900195010300c0e041c2c0f400381565100c4a070562007010030106414456005051140c0002d92794103003051401403c00c041404003e0480144030000154081031340c85003a030380d0a92343c20720b480c01b02e038000950050516007203050384248140c81c50244e41c0d4000544c1e12440d81d8004ac020345401e84c6a0721106000b10040521030440c0303500c01d181c0784002440150b031030301a060448401810103107102d0711400c2c01c400d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 219684316 1250 219683066 219683071
    0x15030501030b010b2101030b04030e09071202070501060b04150212160b06040e03130503060912040e090c04060e060306071701091a0d0b18210304020d02090708180303 73
    0x50303240210014044d0514100280011540d03000b0710030080031090300010440f20087e0010795401102d070303040005143e00000c00714000781c000d0f01c10360043d00d05001c00034a88001d08118100c4203030002402410300000350400c82c054000c9100859503142e0312a41e060300c8113582d90400c0e025020360b150303202d2460301410541d2030f42c810300d01c94494003000300c0c1d8a943c42c0d40c200900c2a5803050799581c0d004100c1c0400c01c0a4611008200910311905040604251170410000d103040c10b0b560190000f901d00c0105c2e041650111201c403c1d00600c01c3d12401e01441c1030041c17803607401f900189050000641c196908034a14082c0e102601a100c060f20742d9034080f185900103002405c0b0400e141401086000340591000c1040d014180804000c501c100c0002405c0741c600c1c8409691070b98102e014440c2c0d19058100c426a0103511000a2030184418001c0d414981045042030511103404070004065454000760500082d074010700ba0310003071a2106002d0600c4206840ca500100898601400a1400002140d0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 219685566 1250 219684316 219684323
    0x102060a0b0f06070302010e010c091a0f12070212071b08010203130213060302040203130201030507210c09080f060a1107050a020f0111030c010e1605012111040605041503050103 78
    0x10312200342c01090040903400603408404565a0301c40600403018284135801d541d8100b5900c101c1748600e890380b013851005642421b0001104100040100c00c40503804a950304504221302540607030b10700d44140c2c180000728000340305040d0f0000310101000b920b01c015411050f0140641e001d11070711500c3c003500700d0208480508220455001c103401518007004104800d41421202141003500c2e5808281a0303041550542c1c800000c40c00c51404568140c010154040050310301703486500044c42d01002c1200c25203a1032a54560f9034a9a00c582c140700e00c2c0803001400308142101c03000842d41c0c031440e5681d681110005c885031303d000700030b14000425008445645030424020040e0101c02e4080020034002c02c00d5480c14400d0603000010329405c244040d054441141c0000038051090480440c2400704201c4000c0220041820900083e0382001e00282090480c01745890038850100056000386042143c500040b18040750024426905c10010010384090107000c00e00c0100042c0c046d001c0d60303805e02004 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 219686816 1250 219685566 219685579
    0x10804020904061d0312010812030103081305120c010306052713060c120b04050f0c03042a030c05030a0c060f2a110d03020706030c020c041a0102060a0b 67
    0x5005071500c1564181c10a00410f000070b454501c0701d07002c6aa000000d18240074917000412803041d07810401001030b004042e400301810344a940e4046070b480502c01404020642d40e004500c070399114002d640030300094000030f003803034a082e0210401d00b41da903802d4915480c0041c3c241800030605e41020075116481e014840520714488921315418a030704980240455000d03841c1a4600c4c001ca0554040d01c00c650803d40c64021150060401c410242d031a00b01c00302d40118180010300450716108000150f2040000c108640c0f6515649442004030021081800c8254000714411480b02030203811041180e00c5404108182ea0f5204d01341070702c8140004010784410402401004aa4000d41e030a42001c8018501841155022031030081d1035840c3c0362030384851014400d010703c204002d4a5120000090840e45040642420340c0d00070360b030b40e4441c000e240401d0740303c00810420394020003075200040380083c02408500d641354280c0a41e81e4400494074018030074800410111301442c42114030368070024043d03 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 219688066 1250 219686816 219686821
    0x120904090303200301080609010c02032b111c050f0414070306020301030602040501091d15041d01091a01031e08041e03020a0f18050a060503031803010513020108 71
    0x10000100000326050302450388070415454607400612008035a0644100b482d80c495052a0b0400d2420000038083c6866a150803508441c940e00041994028040d0042051041c207171240761030b441c00c1c0c5c1800103078421401c040c00c1c020142401005000b21076190503400059072490415035007610410303100c204c410a00c2e44d01140200d89015a161100c007007403000c449a15617295a81812a0b00981c015540243c1c0820103108640e4071000e500e0003011118445a040441c0031040e009a00000d001c440c8149100c4502800c15261900311a40c1d20b82954525103211086581960284c091100300300e0700e48020800d420b50341e00001100905032070300481d4801c15142540201d080541c0b0000c0b080d52025024400020352070f0102004034a0302e1401d080482c0000d1551042c00b00c0b401c0c2c030340c103c0200a05d410340c080c400b40da80113040d00340c0f00400300300100301c03500c501d80d82e080142030507006150103000000f1072034080e1340304007188411444298001c020f10303941c802e08800410240a40240064406400b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 219689316 1250 219688066 219688069
    0x90b0a031104110c0607030f0c0905060a0810090e0f0705040212070c060213081f020307270506221203170601031407090801140105241603110105091209 67
    0x400d07224035415081c1545044c01c030009182c40c000301142d1140000b502d80d100c1e003100d00321a02800c40002100d081c0458034604000014440780168a089810040d500c1c0c001540c880341550030500802c2e0807002002411b0f40010704903102e503650341c580d859900c121180001c807814244200c40c01340f484030403880111344a81d0402c03100407054030410750340342c1c0d02409020350560007001c001000700710380704c02080d681a150800b1000301c124403d6003050740f0310510401c03180c280c115180362030a0442036141884001e1981d440064001c00360042d42d0408000724120008401c104264507100805a22080342240c0c0d51808030000d03100694001c00086210201c89051020120030076044030050502181d41050117403401c5d0b031408103c0302d000c0014505c01c01040000801c0c81290b14803240340602080c1581041c0119100c0050307a956042900d1300398950b03207200101d8074180c2d01600051809050204010700780140851a03801e00b107002e5502e0000860b10801c0d002030000041c071404d10f0690308041e079840 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 219690566 1250 219689316 219689321
    0x206030915060f011b03020a020a0b0901030c08040506070f0908070603021c0603020105090d061407030f29210316140f0a1407030602070605180601080303040f1416090b0a031104 78
    0x1703000c5080d442004c00c841300590302e030080c2c0c0d005401c0007034400751554100800101034504481d00b0034144240c0100340400300d0004070310154800c0040c105203c5024500d0300c01c4403401415404000280686140454115410f8000301078052111101d545111114602c05080765114400280460341c01c003c0040241015500002030901540d0001064003205c9601700c810394048500b1070010b43d6400448406409500c54100e00803100c611920043c1d0300e0b901210414403c042e0a24480c900300790002d15070100300031818503d240c000041c4c036103481c1c1c2002c008031520385101040394807244082400b0012000003801d200307a0f10b0a100200004007540d15050030107002c1941000301409401004404281140010701d002e5110300c1e400500c0d442c05e00d03100001414020304440c1c281d0010780c010000c400000080c2c2c0e411541004038484007030030768a00300140c00f640001200950064644506050b407420039a08100c841c0e510701880b8260101c410801115600d0000902c0f41c035650303100203154146503 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 219691816 1250 219690566 219690617
    0x5060a021b0d06020c06190b060405040207020609030f01200a1d030c041802090a1b0e04021608090907090503031b03040803040b180901240c0206030915060f01 70
    0x10b04128600c51032501c85006903884030020b040c80340e101c282800002c4445a107140c3c0c0d881024941000050040b50000d0403610542c4074488c40740b50041160819561408100c0388840340c001c1c120741c076140003020264080e141e000d02c6000200c0c02d0302c1003014a0b2500da0f08a50300015259188801c032002d4441621118009014140d0507109124014501d40ca8a200d014600300c11100994a54042441042480000200a080d10a05011959410140480200c3c9403150b050800b0406841c040001c9002030003600400d100309040006a58180f041c00c600901c107504040e54030940d65507820006030f40c001d545d4816290583c3c02042018501caa20300600030704103032604203582c42e0556a11015107140c2154000c140142c00002d00d120601640ba2070215010000395504940d40d0324125945003031055012000142c1d1801c1c00713015910354480c0f60306441669008107200d03268208840e500d603683c40f900c41003844a0f18a080841c8081c0381002c82441201016510204c0c01c030300d560705480d1f0241d01c1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 219693066 1250 219691816 219691819
    0x6130c020f010c0504080105010506090a0e18120c01050601020f19030201020408012c0f102301030318120b070c03120507051e0a0e060a12110408060105060a021b 71
    0x110111100300c0e01007809104803d48141d564691079070308281000b421540b06922242c0300c1d5604002550749512645880c00450303d80e0600d0281a41e07610032400030290450070810030380d000b0b104000c0d24681c12440a850442c846000810241d92070300300583c0e4030b042105502c0419407001c41000200a0300c841f400782040d1181c4009030600d90348901250a5580500750030066452034007005000c54820341c264545800048000d1400e900c8441c01f0944944070050200034864440c40c940301c9076400504621880502091144503960350782c140288110b910709850780150b480108002100400c2807005001c80780c10032001030580d21070400c1981c40e05041070084051080c4403502000c41000c520800d886041261116a80e50b49114074070300000d104c035408130714516424004031111030b500009010201d4811390300b0f40c0c2c0d00d000c2c01c00103807840900003e207584a6400c1108462005600c08082c0c01141c01d180204c92440c0d0f2280104526170040d0100c19005910920318825507803807000d10a40c203c0c80 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 219694316 1250 219693066 219693073
    0x8030702030706150302030d080103080f07020a120b0f0112051c09151e0503072106080a060633050706060f2909010e06030903090613030309050906130c02 68
    0x409a42d01c1c000c2d60045001c03d101000c22550170020f50400780045406000c80e8075020402c2e6065130b40b410001d01403803c1c02c4903625400300f000e00c11901e8915210300a408819400c00b20031030f051400f18144c0070111050800c09020130000035041841d0b0903502d4146501401600440350500c40241858103004018010420b05030b0000800065040e05088009001c2d602c07189803e2a151407103462070070b810760003400c10500700b081081442d4850100d021001e01c0b09000040c0b049042c070315601030700c103d810001180c0540001c120411100340d01c060102c964050001c5040054181b407a20b4105804040750104d102100403400d40502c258010056188601000a010340c3c0783c1841d0f05a540307041d000a070008551841c008c0803900081c00c4001c140c50f103913521600d04541400002d008600c0345508501030007000c030104401120920582e0003581d000b8000c80c1d182e00c2c089a0711002c24203e803000b03a010443d1184007240382d041c10100305114078000360806042e960307264184002082014030b400110302 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 219695566 1250 219694316 219694327
    0x10c03030b0f19170703020901060503040203100e0d020705060703090e0c0c030a030509100c020c010c05030d0f1b0206070818011404050c0a060528050f0c0d0e09060d0803070203 78
    0x140c0782d07050102d1107441c51805021180c2000354102c0000b0280c1329800d004e52002c03008200603942c000070035041d01c0852420b180c59454900c0481e203020f01d030701940d420079820107010519985000502c04030180c069400c403250300d551030060008611440e04003400065840005001c3c0134a144103664024201404d081e180c00c0800542c1da00795008089400c0010f0346880c24024900803c0082200580c0034040410440651200280d0383c0c02d100219a4180303d030800b05d02050042c20700035591080071000e41402030341c0f0200450001405288100600c0c40d85008a00741c03020702c0011801c1c0700c2c03009500d03192800d0301d1b044020742e10b020205401c42c4180d034075800319058008000c4407003401240b0900007007100c040000208204545a43c01c01710800a0502400c10802c401443c01c28440854025403182842030b10b004462a2241c201880c1c03188034001801104104002980030302281c0b80e50324a900d0090400420a680c46e060302c3c0140c1c0001a5882d04000c500b200004503082103030717401200d2416 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 219696816 1250 219695566 219695569
    0x7030c05060f040b01090213090f02070203010608030406080708010608010603200706051b071a25121512060b040b0d0b09010c020109020102030a230d020d0e0705010c03030b0f 77
    0x11034221003102d005481030040c00204000c202c1403901504021200794142100088140c038069228401c90304402d4544025401c41102d580c11100200e80160091101c651102801d0350740741e00a01c42c40001444040000c0e00d042d2240e40c0082c141c03806a80c80000e0b80c0d2130003108030003910901a0310510001644441c228111200008140e0320340324801c0420300d850458440e26402505030841b088110b030070800301e400140c14907030a40005ca0440554003540e107614030860b00c1a981b10740d83c0030080203a101e0044200360004141c0740241003081c4140034008120541c52001e040d84d1054118484408510703100103602c1c0e0b00700c030703114403000383c400500c1095900000c4e00107800000c095450100f260180110401300f070040d4408481c4600003032020315510f80c0002e54038410858508200943c5603801584141c00c040b0018000308400401a200c9009284007402584580810f043c000d01d828000d42c144100450b07044100d40341611002006450760303c00b503028020359556180e0040780d041001075603 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 219698066 1250 219696816 219696823
    0x30e0616140a0e0f03010e1504060f06061206051504063c020f010209010e0607030306030b0a0f0c0c02061c0603060f02030601090e010b0a0f021c020607140711010507030c05 76
    0x7035842e070356402d100202040e091013080d03a00840c08030302a90400141014500d40091101c120030340c00c0c000c4030596541d0f41002170041c030700380e0180350102d402d01400241c0c0d82c2c2d001101c0701d03291014810811900795a80304100302c0401690750458055424481040700c14041c0c4680607060900d0a40f020f000c2000f814100388080c3c1c40c905403105a2940302141500d42e904002c0a80300d071250300000c51074411250006000c1701e40c0414520311a040014a071010548a41c04c42c00040da0f0040e001141820700d40142005404400791030380480d03190101c2014100c1c81502c6550055030050203031890b08a00c09011040c507004140d41d41000c60f100c4c0b00000008500784035007020010720b054016228140080010030114417648050b9011104500500c0002c07500001c88212240c903051123074000100c148142d0030247d41080c020500c004100c0c008082c0b0303402080c6e140c400c100703d07030310401d002302210041c000030f008081026005130540f40030f160103035000c2d400800075240241490510803074203a4560b4074 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 219699316 1250 219698066 219698077
    0xa09020d080c01060801061206020703020708010204061e020307030e010503060f0307080a05060606041503050a091505010609060c030c0b13020306040501140c09030a03120b1c02030607030e061614 86
    0x1011007000401d02c007000000e1198501500c00c10b8001d01c84145484d808442070041c030000540145e0340010f0342800c00d8000c028090080501500130740d181c9550b00340243c1407100906800c04520080c80344c88075a1840802112240c0341d1549440010509083c011247c0342c0005010300e40041502040461960701000613200800e030110050403151b0540c60601e09120002d4034841c019081807101380300341d403002c01c1100c514a5030b5280009180d9102ca0060020340040c000140c00da01c0e0b84407403641c283d60315400050584d002d139110340c0b4845a0b2070340202c84105002001500103031001c2d407843c00083d62050041d801215421481c48220700640001e030604100395011903070303030399221000320809101d06030300c83c1d0113000620782901f40017011001ca500c3d0ba10b458801420450482104141141f1913480484031031400b40c8a0002e4860140445804031034001d0140d01c13900c0358000154a40740f2a01440064404400140c1a42c0d2900e851041207003d0416481051180b0b528103c3d284d480150060030703 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 219700566 1250 219699316 219699323
    0x3180c0d080c0c010905100302130905240609060d020c0c090705030906010f060815031f020403170304080403020105210a140a151203020114091f0b030d080a09020d 72
    0xda44040c0598038620b03100a8114039414008001070400490b40c4201f2414004074481c2405a0f5410815810420b100e41d0345d00200c7d820307032600c01800300c0c10302c3ca1a001d16010b41000710b000007130501c080c200704560090000c02a4042c0003009500702d885007503005441c0d01d161520445416165840010f0709032407084601600003903000c07040044030a410490b05006100ca1000747c03c40c01d00380880244101c0e40140350315107055402104c0c0190b40c40400c2400ca0032080d81400244105003001040301a500a01c001d42c4d52002d135030800801040c00c0e10449004a90001c41989071900e1a401940c135600080224282c410741d01b01d03a0403602e54030144e150700c00d202001000a00040c000c03a441c01030040901008001403a144018a04030071800205054070762240b81480144100e140272405090131070034504032508640140000e00070001a80710203091148040400c110441940008403043c08020304d42c158810031004000c41e004990700d0760407071030241001c104a03c064000c20343c0c8804852045 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 219701816 1250 219700566 219700583
    0x10b3c070c0f031211160303020105011401110703110307090504050303011a03070f1103070c03052b0903030c030c020d0b070201050c07030e06160c060503040507090902010503180c0d 80
    0x11001c0041034020000039003622048a00c4490540c1c8a410071a02d13405200d80c24000240c9200b11400c0042000c504814810703c1c2d045d000d00e0701d03454001c1c040c10082c0700c3c416400c0f5120910854642c0955825103004c2d0441c4020440c080c556150898100011380c1515010302400c01c000c106030a140c00744034402c40c000e400540c1d4a52500384c101c1d2114810b0380800e10300c10002c1c0306004040703502118100707000e0114a005140100311620040c1903202d00c042c02810341110080020401001081c2c00710824240c481c403113848800021000840100011074000250b072401050000078016080415800d010713140078810240310385c2c04109102c0b04d5010944030020000204000c0300c1c0c0c24000c0070b5000140240755402d01c6180d075000352841003098000e07441480b011039403176603226104051a01054000c00c90311841551610041c04550003903405032418041c92402243d5082e060080070300c030300e50603501c45145580f402803030722030700e91614580c403440e000742d201719601580d607290b28010107401148113 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 219703066 1250 219701816 219701827
    0x803040c05030a121403040b0612030c011d061003020d0b07020102090409030302031f08070b250309170601030804120311030406030209040f0509031b0312010e01030614010b3c 77
    0x9000c2e90303000017005410701d07420030812002501c5c2000756504040c05a600e840b0721101c2200b202d0540c060021110b03025071a0040410740c0040c88030341b140c18010014103480194595140d195030104103400040c2d00444090515030005070390216080c0c1c00740180c4001401c0ca8a2200060142e034560102980003d401009024801c541d90382d00e40705400314103440510052070700040c02e840f40074070301c00d110f002040400d504203581020040c41280c580c0103c4061031080e0503240c003414010f030301e000300440c800340c2c481c0c0782e400403c0c0003c00c14140c2c3e0b006603499040c01c0c50640c0020851101c82c0c81101008008503884010315020005040a4001a1070240c2c98100203070a0004466039040d0381c0207801d043c0810b201c00c1050100c00c84080c0b4110380f01c40f07101c045140d08168598442c4421210100c0b03030510000406581144c2000d060707920410040c13003412490b8180b8201d00e8000c0c0940f041814040000086411605010901040d484d402000664814015112441c91140c01071003c00500280 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 219704316 1250 219703066 219703103
    0x325031505010618050102120a12090b010e09150a1d100b0f03150a02130b0d0203180303042103060b0d06080c01020f0c0f04060e0403020c010306050109120803040c05030a 75
    0x340c0d03041c41000044c440388a28a00300000b9034a150502081c0941d0b240050242c0520f4032a00103a050060858024003203802603140484120209114214451f80b1890200701c0212005c26803c2c20a503048010301c105440f04840000200750307101c01e85522174840d8007154030003d014022201c24000600c000500c8880450a2141c481010102d42e4403a070006011542d04000010f040d07500f21213007550041c0c030303800e40088100300700b5483e8200c1d119140c40030401610341261034004500c5074200c14541840705540310443c030783d24081030f00c00401c2014080500d40485030090011501204549001716101c2d98440c0d4003120341d8005810040200d440e540c003400601c104128000740b5140c288010008000800d074203503280c201904426204043d8141d040c562990ba81d000326011346017401015075a81480d00d0040e55405201c02c1285c082414404001071030b6008044480803141410800f00c3c007688503a1320100c03507a000800440d20b1480100c004034698404224820106d071003281500f060098100 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 219705566 1250 219704316 219704327
    0x100321090e0405061b040b0403150204170304060905060702030a020f041b08041119090504150c05030406050a050106050706050606040801060e0711010209011d032e06050f03250315050106 82
    0x1403850170709804000810008201c030040350103c94200c4809913921052408100103803081d580500028461502c4007487c40c20044020001c8a05507100ca0700c910f80c1d15400e0042c1ca0085140196040e003110050202600301481c010750740c40c00003800050401c101203a03034100032926100440000700d91b0740810003001038010f00e000000a0840321880b80080141e0803034005055400782030904ca0b1140301081c104a503241a08200081c241e8090001c25414400104290000c40e42600e0a42c10800031842002a501c074107070580b806650344518044642c2c59200c06444007030078042d00200704020000304140c0038400c2d5800f50400b03004079500c0b414020b0000300080c14800c03c01c0c4503a40b0411100301c2983e08015002501040148940024140350b00042e0038100c1c01c4c83c20b0142c41d035013400c140c44d41c44035100780c505030013207203150800800b5188e070180844100c0c0d82c0c00694155000210142210030a11206100740c040c03402c03148950f81c0c49aa4509445c0c0d480300a0320030454850005110898104 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 219706816 1250 219705566 219705601
    0x2031f050625170a0f081315020f0c03030406050105011418090603010e0f01020307020d0801180902032a090604051003021002010605040e03070b100321090e040506 72
    0xc41c1c0385401c00c00daa0207031584010610b801e0580340786004211100300540c0c0c03400302a112203114000f03602c031300c032104024100740044d01c02100044e12040005103507041d50081c510166402c03220b0441d1113100410114020f40c030450312944808010b000814800100f00021803081d4403030000810154580800504091001c10203003440700c109000140b9088a084140c040c02c080440d0b11400544801c0042401001c900070010501d0007659085080190150025409001150300703c848802c0c0f04d00080324010400c1c06a50741c01c1400c8412043d00f0b88a42c0c000301c032200d00082c1035a1f0a4a0b12092450101d48011103024a484070a9a500680d20306800b01c2580300c0070556050000340340c0803200001803801030000078400c002911079060000d100358891000fa04024000300810700040140e143d90703802c0194100c0300c1d01c20043c0040e500c0c894400303d1104a075404903090342d14444242e624141e60781e03881c201d1410002c00900015201c46400502c40c0501d01600c003400a5061407200400b500d8a40e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 219708066 1250 219706816 219706819
    0x140403060c180b09040b060f0c0d0915050f030a021201080703020109090b0d0b19060308040e011502030a0e04151d3d03050f0f060702010501150507020a0902031f05 72
    0x500c2044041c80800c12113004903411500010028007950003c1d4071800f400449104940011440120b500070025642850703840700e03200c0c042c1e496980c1300c8e64525581c04801ca5800641e040c480c0d0264407503140301031a0840c106e981c002d4282850000c2400c00218241d0040006900501d010415960400c48800240107032090130b00030308030303c4000300d444003a80031001003170b1607000000220340100d40180009c00010070300c0f05210540ea40d0070000c413550824003e900701c05035410000129203a01050000c848a00c0b9005036040c120350810070344c0c180510b41c54098006440740e586421206030f1401d51070140072802c40c1c0a04020709180415528000244000c41150403241403101e180da03032002c0d4000300d000551056081440e005446502ca1300a0717030004003288101541c8400244011861761003000940302150200d6a80100c1282a02c00030310a1001851103920312000c030a2003900107001641c005403205102070f90700c0501030120b0b442103501e00c41c52680e1001421555203034207100d0340184030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 219709316 1250 219708066 219708107
    0x90e0603074b05010507150c0e1513030231020315010306050a05060c0a08070b090f0705010903021216170d03151715070f1116060f140403060c 63
    0x7040b80310740500704003074043c83c0d0500c900410810104560540d001102a44481c030900c42d88910351409001010140111481814403030f00c0390742c030400c0c00f0f410307a0400065029900c504030302e0f64082c00741d000106090b03842d031103c400300c0d0648000c028482c1c0b912540e1000d680142c0d2442c0128103200500d2006803003604260422104115540c1e5800703103c0240d03842104c041e50741e0403c44810501d0081c6901c4001c1c60381d5008624001404007810b0114407c00901060384d016060301c1040e203484942c3c600030507000c110100c10500140c180320005080031501c46045820601c0308200112442400781d00c0804a101d040f41e0410075118148106949540503040511175902c820110710040b00171405032201480214443c1c1019000c03c2046800b0074440d190500100d04000c5001010041000c0c0102c02240100e00c0b2001e03001d00000e04560301c0754403002016107013800e0440c11600703410310303000900c100036150156015481035080100000d500c640c6001800031084040a0b04008030700c900307240349aa = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 219710566 1250 219709316 219709439
    0x11010c0c030f080411150909010f050108010f120f08040e090c010210111e0915040f05011d0907030e0f030d0b0d020d060c051b010b03060901050601090e060307 70
    0x60704c200303089044040c00c8070070103a51b03080c0c540c0d5494140240741000d98070030242000000d10001e501041000c0d034100383c3e00e000040e82c030385a9048070100705101c1d101c02c5d146044002c0c03003c034446020081501e032056a10030310705582c030420340c0c260303000a42d54004640c0008040310a59a010010034072044200c2d841803186420341400c9031501d00502d080075402500b0404d2104403104104100c03041404c0080101d980400c00c40405100e5030464004d01e408011b103201c000c00c52f98082d149110b4242003082d40b04030301c4800682030142209018004405040e122401c9007a655028000e40c1800b000307050055480f92090043c600a07a03040f0109d590203000b41001030005038940c14100c40710646c0102c40800c120740070300b00440712071240310b00001640e100201021080b00042d0070900800c00100c00b1a280740d11a80ca1403801c076641660b0321404200070f075070100700b0070b5034100296901ca0744c020141ca240a03601d5422041e2800840d00342581100c19038500d0903c81c14010080760341c004101d04045228 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 219711816 1250 219710566 219710573
    0x1c030506100e040e01020c030705010e0105013002060d32010b0a0e0a0308070b151e040207020402030a020316080103030203030103032007080f0d1704030f11010c0c030f0804 76
    0x384032491a039410040e0b02c801c41903907070325250082540346038510000c6544020341f10b52980c4941059104668039402c2668042c132094050040300d042e00c0e004500010400701e0b080c3c040343c0c0f0100d0342c1d8420803180e4000202d6409640c45c00c0c040c048003101c400012664108209500130710900a1404191084050251540e1180011141e5054503040c5040a41c0c604041a007921a803088200182d400900c040300841003002c03801c054034030907100e2115118151210390130040c2d410140304489800180041100780e05000c000b03070038090010080d000502d00b032026004141640d0085404229864000090052304000424081001603461404a1040d410b50341c000b903e0f8441840041c04002d148107d08100001d4441010030b10781000302114a0305aa8084180d2a81500986048503029600310359000f80e01620f07606056031803c09820203140d80340d0b9425100036001d0320741b02040000429504c0403003203003441184544189074480d00206102c910307006080380f6070068000308011010b814007001 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 219713066 1250 219711816 219711829
    0x9050612060f0a170715050a080402010e01121d0f0303010e040803100510090905131104020c0102130f050a06170a050702030f0708030910090f03050d020d0e1c030506 73
    0x80e4122100c0b19241801d00015a022880e60480407030a190f204019040260028840d422509841c0c200c1d03001034071010003a50030380030301c24002d0b000c0317542000050010f40c445c0b03d034980300e00c80c141007a107040407159040404681100031a410420007441d40c8031841c4800b0007460140c0c150b40401180b442d81480c0150300070380f4000c1c100800511010010a4499020202e080c1c0900009440760040000c02d100c020500070701413041190151400000ca903c4401c80c88141c1c95203a040188802c00149402c28000203500400701014903550a124404401130324246000080130540710180c502d9043c60b081101e4000c01c2e42c048814040b403a41e144460b514504806680841a8840011a6a69584181e003540324800c13a090120704d00050b58000c00170048055801960319004a8485940303603140c0c82c044400d50f280240440b0300007400d03980043e10402c020012202c2c5080003600307010300b440011095034914500030019030464420300000c1240103808400126180c81d0503c00c40c01e02101041c1c1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 219714316 1250 219713066 219713071
    0xa11100e030d05040501061802091206060612190c0c030e0315180703151a0f030312090708010c030e0c01181502010b0613151707050705160303090609050612 69
    0x10b400341c41d00005401d0000a5201c1401002c030340c080461200051010a0300950003034189074440c0b4508003c9180502000503080e100d480c014008614080300e1607401003d01000402030340d2031180c0000f860050030361501942150340042d481d80a6640c10398a00540741450008a4a00a5110315000017105c242508070300e4018000c4410381c000700308074103140b509107036243c3c1000e0034602e07600b00503005504050b440580c988003503400241e6400200b80402074403c2548404650652041c442075421000005006401c82102402c0714041b03a501d201d12405d580d00c1d14403176000700c0d503901d40c025001e0a043c4a640c44000c024681022804002c2e60191000809ca0161148041c0141c2200418038000d5100702200d00c4001d10081e10352061a8810001c540a405074040301c5050a50185085002e60f03a89036031040307601c2540c0351541e01c0c5d030401c032801e80010409a803c2c2c45045103090400d11030103088800ba41c066070341c503c0c1090404074040c28100190744210b0140c0c008004140046400c850a143c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 219715566 1250 219714316 219714337
    0x30b06070210110d050306010f050a0c0c0b0309010f0204030b2e08030a03051f151202030a02130519061803060e0c030606030706050306041d060c0406030b010305060d0f05030408030a11100e03 84
    0x2d84450b05042f003140c024500c0d55000b4000690700d170001c501031303551002852240d542e210080c0202c240e01c0c001c4a050303006510005105581c49400304081510b01c07040f01c0121b40c02a002500d251820f0041c0103c05003496000310782e280c0000814441513549401510740c401999151400394201c031144000903642280300d90049031480702050f0181602c281d240c01c5604011810554507403c1c03c0c0300c801d000358420b044901c1503070211140050b06082c03100d283d08032040240b0103020500d103008030a440300840300c04e00300034501a030749001c0000760b082e209000c00c0015140040038421210000c0c58a440c1c0d01401d600d200b54802d80c81040b01d1580700c0c040f01c2c0d1008040e2400b00300c82c0305103000c07100e5110208a4040c1103008060403c49000280d0b00507104940481d81c2c180840050030b0010b4088540554900d9000120b0030540d90100e9000790b580c26405104c2c80c00c80c0d1030b0568400d01d20b8210b0700140d20702400100c907a580b0030f44c070110810010700400c0f43d240c010481d581118259640d640b04511040307 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 219716816 1250 219715566 219715577
    0x109080a02012f0c040e0706090e04020d120e0a05092a07020418050c0d08030114030c09011d0a1505010f090e1315140106030b06070210110d050306010f 67
    0x4030340b8000d05250002c400f04a40001d0a901d00c00d032060b40c4038440412124013461402100c0313400c06200003510001c8428a40b00c201066003041c400e207464070340080059801c4440d41a03c000040c07804594103d0280c0030f581c6007160209000108682d070210360b07121510403440384040c003400311b022031403800c83c600c034480106c1081e12801d000c840310390244c584040e5001d481d0001490070b240301d030144054400d1080054441c02c2c2c0e000da0070001c081d440d502020f00f090700280014041d4907a05402e0038135015005044403400689240000d03182d100c01d0308500c8207800f0a50591040141600303c85030402032407001417103c3d00c01910100c0500303a56100b83e504000d1405281d018560040300c0e140081e1084200c00822860030b034044880200000808032007480d0400004400001c2c11300c585c601031904002c0549040e4a070010440190050710074460f030140b02001340c480141d4900600c0200e0300782d6510354194054400000d02d0600306040e10f0441440003c108100c400d0b030f404644413007a4503490421 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 219718066 1250 219716816 219716837
    0xc0a0c060908160312020301030c0e09011d0c03010606020303060f091b0a0e011d0a0303030f0605030304080609011b02060106050a0306030516090b0301060b0f0318150a05060109080a0201 82
    0x2020341000c0c4000b40910800060007501c22000303010050500e80a40c640e802c3c4c41809451400482c442480044c0c40310007141c10510031211034901e07098220071490004a054103040500080d8a015a10785480940c0403038002030081c1003e001d200e00518850029504516100d008103940341a0420901e02c0381c00b48600080741c2d9444818100702d1108804000307502c0c0c000c001c8010b00075062002e4002d01064000d45000ca021182d041e01c809015809404025020300d565010b8010f081c51940b0b40580503110100420151000c1010f8801464000000c00c800d04105c0c007160308507507185038000d000b05041141e0f10300340341c1c0008209045070140d20b4170550314014242c08600911642d040107040c0d0040700c59416800d20740c41240c90683d8040c40c0c0800224108000305403c9950178440c08000c14010301c4265585035603607016540c0075082c0b00c05412064030581b401820840c1e80001232000c2c01c150014002ca10007035101d550742c008020f081c1008030509140c04195a041d243c1e00007410440d4103d82e = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 219719316 1250 219718066 219718073
    0xf12090f1b011d04060e09010504060510030210030b011202280e060f03090114040311070501081005040b12030309030403060b03030406121d0607021f020f07030f05090a09020319050c0a0c 82
    0x5c0300004101c944048507075801c040c00800d011309030550302529003908290108120004207128001201d900501078106180d2003241a005420540725613418484442040b050302455400200410348419003408618488800203a05501071035501808003c5082c540703001d0313030f00c0f0001141c03292075800002c01c0d200d585038007442e4007400c002c580c20a8020b07401001c3c841010380107220100f404881405940429855400459a030107044400300c1021405030340c10042d508040d804281c61003405095002041c0768503040503c0c50380280c03840841540b00003000c0050202030305c03d285644c071046020350b01c0c05162000c02820741600085104400d80e03220b800c9510202074145101042d1682026115645000007029480d03011644111840e6440300d03810503000c3c0c0d4a81300b12514908a10001740c00e00d42c154804a07420b40105943c0070a20904011214180ccd880f11b403540014040c1c50b001603941c0c604103910b0640c3c0768103252858251400c046c00c0c01000e15425055441206d2075181800740441c1606 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 219720566 1250 219719316 219719321
    0x7050d15060b07060e01050f0609130510060f1a0f07080a12060801050106020f06010819080c121b030a02150a020904111b120a050f12090f1b011d04 65
    0xc2c88291040c00000d040420010030303420030f00004002c0c1c0001c010360368a0002480c0f22940c200c4000d54400388400000b0004030400c9110b14415002d54104c0703c041d15607411541c219419604410090740301c480c0200010f500e450b0a80c081c1c98940c000050801c2e14180b031030300e020700810703800038020700d00410070b01c41d403070310650561386051b42210007031002941daa007440740200303000c0c050702005000300152400c52404c0010010304a8200d400100360508021342d5414451000b01e03400c40320070104200d050606241002802c040030b0440c81c110740c0e201200c01c965480c040f40e0090003003454205201c01c013500340e00415a02c0d0002030044135081141e4806540c00300a214511a140c1c0c42444c00c2d0b0907940c0d20801002610580c551030215006000c80b9481859681d80080e00c480741d1010708220000c0042e2050010b441d035032102e0010941400c43c9410717000d84c0c10703404440340400360380001c60315400d0941c2000940032050340c00d19941c40180515000a012000500c1d0a01d1a00040f03421f00045403243e6 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 219721816 1250 219720566 219720569
    0x9110703020a080315031506090705040807050f0102030708040914130b070f0504090f060e010b03010506030a02071a1501020115062c030d0c1205030705071118010b0a030e07050d1506 80
    0x10143d07000b110303603204821f24101e400c1d60b01c54001d03004400082d560320b01550844040d06d00d039034001c01183e1b141100304103590a102d0001c03030450100b07220407030001d0500e001a00241c148448080342d014801c1441400d0b00d880146120b9211021400d0607010a615242c00394008490703140140c43c0300d070303c45402d0b501d030300c03c580c80002d00a1800d26012030b80b10045c0c0c0104151641c1d1280300c1041d0b6070f41d0248120301e0100380106540480308002140402c0005d80c01858124410401c0060210b0302c00141a0701300400c82c0c0a2075545000c070380d44841036a0a12818a19440c00e00c0030170440c3e0300b0f00000400c0c00080702900c148002115400c00800800101414500c00d030040448440100c4050f0041481d0340e03155044503142c0a46c4502202c0300d002744c0903644038050998980b81000040e407240c40301016110300c0d1540180c50403422001d41456100c145010b0103a20760f00d60f6446c103440100900321811164040d041d900155030034405a0358076824684016001001a0303100070000d42250000d0106 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 219723066 1250 219721816 219721819
    0x120403230a020c01021e151305010203011716060f0c0212010e0325031b0f020d03031a030601030b0a02070836030c0f100201090f0b0109110703020a080315 68
    0x2042802070140d000485000c3d01c2000e0b402d0b1003c02c075084558440000c802024000190000329600042000c9411915480503103640d4580e0107205075254542207a001780c00001d60180d4000011403403031420055030340803801180114007840d141104c002c000c001510841c07810050f01a01400a41d61044520840751003880c008001c0043d0b01003181c0c1c5d0701d038050034400310740d03003100b48512201c070400c626034070b8045416488541016142622100038480c5808045545a503010300482c0075841e00346206c0b6555109880005280d5203048500513101164a0b01c85e1082c0d10400c01400007801c540fa0103500804504405a01c030f45003840c0000c06c5001d4040740d4501c070446e2452200d00c1c188100b03000011005041d104008a1130341106241d00c0743d80401c050ba8100816110704222030920f600c849188031701a00c00060204900c0e03071040c00856000c14281c0b9403603480d00051218603031610540d40c3c601e01d407820180c0340c03904690300a9210074603454043c06200c404030004054100501e001e4004900 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 219724316 1250 219723066 219723137
    0x51306050a09030f05070c091d0307110a0b0903070302040c2a0201080a02090603070e360c0301120305070c05150c0d050a0509040e01150e040611120403 67
    0x1c1ca99480401401e0550041d800a44c04050999019002c1c0d0120f420070360f000740810b0182410422824090034401c3c41510307505110100c40d401400c42400585034107403054001420b6501000100420814a6041440711a030200000032566400045250850b9410b860105000d61041001d0302e013121007402880b1100a80803040b0740d031442d140a072040c010300c00d03220551282c542c10143ca040b402104035041e040441013001ca00098080c0e1100f0041d620000d0100f030560500075044010b501226040e0421140b4005d603121040030700815095004101580640c190b6140950348007103201761540223410312800080807130500400c0000b50005e004082c0c801403900e8a80b10001c40540c4c010b0b01e50031180c1c06038000501070301e031084c421180990510348d96142411403c10402004051610039012190760312a04401600955104a0000d05c05401c5841e05031410303080040c03c1da4800c000b02c10840710104034950070205100c15071a00b158240c0707040581d140703c00d15050850080f10213001e00a22 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 219725566 1250 219724316 219724321
    0x301021809180610080d170415090804080714090f0721060b21090c041e0504030c1a0f0f06030307051204080f030301121106070c03050106060e190302010305130605 72
    0x2207001a071481192001700403a00804c042040c2110074480341900044242c0c01500843c000c103c0c6480000e6154141600000c1c6101c815980c90442d42d009900000f880e03008203000300121012007001c4c0d0113003502660f005e41c5510302a4407a940794500101038405100341c400408603481900d4216035100b400034001005a15103400b40400c454000105010390102d00003210164007601c840c440d406159008010101030040d5000c02000d4040c44140703285400380900c16902010b241d008850041d4003030380f64851045960f040c03600500320b0101c034103940b184003001803000040c1c1c000b205990064160007440e100341c40c0c24002a095114995015103503101c0c038007400d900c641008006100700c81e40401101d84e0031a40b034418685038082485182d213407030b600131440d80108003120011440c10a00030000c0b0b151284a58448520b451035800550362617543d202e0038024590411340100c90751002700c03003078246000d1003500c520900781240802810581c8a43c08100240c00b142d4901c1c0034258400780c14405031 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 219726816 1250 219725566 219725581
    0x902040909020a080f06010509090a050106030b06011707090b072a0504151805041110030621050a0312060b040902070b070305040804030b100905010902031503010218091806 76
    0xc0030011026840b03040e142000080c1d6501c0082c1e00501c040c485c1014121585ca450104801070720300034000d0071240207082d82c0c480000d0007032252402851040b002c40c981400c110000509482103002410005042c8030203000c100c1d500090740000304c501c40141c0c195a82418a07090301019402c240020365101100e10410300d074040b40b020350003075650075901040562002c400f0007034000450b201d00c958840c071b9040e0381e580c9012103800c1183d001c0e00030240d805420241e40046408424445143c0001a6540c80f060005c060140f4248660300701c2c82c010003c00c81d0840c1c0324a510f0381d158000040a00c41035070800510102c29400c480300901c10100040d80b90355560402c040a907018034000c4942c601c02c42e001030001d90091240038051504a40e0b102c7c203060a44d0b031031007081c2801503d00c0c40b12181d07680001802a210380940c9000c1d0031070400150312801c1c540485048540400941d1b44a64018816581c0c20b8180740014800444202c0b415030365512101e440304c65040d1f1031403c1860314001e480800130352 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 219728066 1250 219726816 219726821
    0x309060403030f0c0c030e0406051c0302061605042c0702070801180f080703020c0916030e07030b0a0f0204030501181203021204020922141204030506010603020304080409020409 78
    0x540d01030380741031021002682280c8104c0c1d1002d92500c0c080303100031840300c01003031040d400c04400003005030000441c9034407031000400388141c9100c0407650342c01c42d09100040550501c011078102c005c621040001c00200e01015145005d540038040700c0380303040140031030340049840400c00e15840e147c42c03014060500328402900c0303002c64000c16405600304804e05a884480702108983c3c0e41c1c200b11a00307607412882d074503407442d0b074043e4005070110300c0380d00c04511455640620071809a102489d140e644603c0000700501990f844048200c0c0640100c903003000403603001c0b1100b5900512040c000544403819400707440c02800790390006003081d880d01c3c852440b031883d0440c19400c0c560158860009943c1c401c3e50403016842009900703e00d0900c44004280141864902d407a04810840040010007080b604014000d0019140a0343d54149490144205440c28000d520503640030900d084d16043c15520741039aa05030611940c01015070003c0080e0900c140541030754060414000155036469650926001 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 219729316 1250 219728066 219728071
    0x6130e101706060103020f071a010510030b1806010212071217040c14181003030e010507030903110a0314070509130218070e0d060e010b10140703050708030906 70
    0x320008102004a504400000d8540e01041e9880003000382da40c911004402039003117410801900305c02031168200140c41c0080426002210162801e410b6141804015a91b440b0b00d6444090500c0c103584416030b500c030b4080c101003100c264641c1080645400c0d00403490072181c101e11a41b07500001c5810340802c0410f4014003001c00342966a42d2400100e100b143c81c944800740c800408a840303203041046180120b40c8810b00755078008003080084040000214540101201c20b40c0031018806000e208154102e21400036014080c0703041800e20100369405800c0740c01d039010241040d1034001c80100f003690b0f4010380704061036020038581000c00102c0c144d1680c54646d03000e9144504c541a00051000555111040c03d098000b0640c481401070202011100100a4141d400300b1107500354641d403030303240c4500041c4143e202c0c9400040b8940540c440a00311000c90044a10505040f032240542540c0454240110180c0407030a59803070b4001d18082e6800d03c81e10800426521010041000c2800e01140481c07 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 219730566 1250 219729316 219729331
    0xc180411030706020a032d021e190602090d06020c0a0506071707030e0c0406180b0409050a02060c0316061b09030c0b1e0705210705071406130e 63
    0x252080a403008140e1038101e18010000140c0c0000d000e10b01082c42014030b503445100f0301c1480c214000c0038062070b420100d410188840503074410006040700c0501030400140120044010700003044103140b0018520681550150449401054140f0703280c2d19035901c4281a98010b000b1582c8001034140e00c0d8071900b0b400300a58890207030b44001466240100c0c4400400c000000d1081d1680c0c1c1c07100300035401050703503a4100d41580b14044401e03505481d5880f41070003400e080b021911851041c100c292080d18002113105004509002e87c000c0000d0000a02881c551341c100c45280e100c0920b145100e10350700400b94003904501e25900d80005110030f5502a008240395081402c40752407070880300340c440d654544401003807451003103020425001203502401c1c00d810b4030700103107080000c118650402e40d04000d0301500c080c1c020b03002000e0113030714503190103101c203003034803d240c0c18007846031500d82d280c0d00e45106070f0586c0400c018110302560345000485007065601030800030110744480f20824000c0b01241c842 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 219731816 1250 219730566 219730583
    0x315060302030606030a050a180309080d0c05070302100c060207080301090506030307020f120f01060b030901062301031d01020d0c080a0218060906040f0b0918040b0402120c1804 78
    0x2141191203402124882d0b08041d012078555110780c0c01c810020440102600840c656a07140c0c80007020702183c3c0ca404907070080d501e2403003a9081400490418018601c0d880078801e1242d50400000d102140540403680c045540f84140300300910309540061070380304006d042c0c51000500e04100450714006d141078800c000c0080060f0b940b40303024540e0724468040041d40c450741d81c2c0c0c0038407000d1130110b2071805c01d001300c2c000380e400a44103000c4080c01c2da1a030383c1050040680c0402040b4002c0c1d02407007030324002c01c45402e1240104880c01c0c00c00360f82c4810818420304040c5c803444141c00b07222031006451080a2502c0c000c644c1e860b00130074000010000504c045c400188558041549402d860082c0c0300038010700f12000600014160802c007050b40031554854100c0000c3c08001240240b010042004051a03500e8582d55043c0304100b000d000108120765820101400903c00031a0342c0d946030552107079055032102c002018483c0040d16101d50441d400354401003424003810700c0014110200d000b03500c6003001c0b = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 219733066 1250 219731816 219731819
    0x12030e0909100b0f090411010e10030e0d081b030c041d040c0506030108030d020904090c082107200d02090c0d060909030807081e04030512090f030d0e0309100315 71
    0x10000f004c0d40e41c010503a40219008045000300c1e21940507405030f200705041c0b002c18610008086440c4c40030650414000c07984d128100840c1140602c9164400c3c0c0182c9840e0200d460242c0c0400e41e800d007400c2c18a082c01380c0100005210900c1c0c241210b010b00403a02504403100d9010b00758a4130644200d500720b4941008050009190401c0f10540e07040c6c910b80e101840c140030448010740025040403030003070340c442d4075200c0e1400466951801c0001030000c8102034400140c0c914003640a0030b8041806861600003001000c010810080c02440c80e4102d1121803501c1710700300400280c0741c090741140070754095000310521100c90458002040d192804c5002031003420f640305880021201076641c080c000c00d41d150005045107118580150f0301c240c1028002c3c4400210410208400c0070466085000c40c800156094501d100b0107503441d413140201c4010401100034a202c05c0e120b018030104505400e44440b1701070075002043c801d448840401030300e03210b0500415500240640f15550300d0102d801c268550 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 219734316 1250 219733066 219733069
    0x90c0f090c0327050304031424041101030915050108010f0b01140f03070512040609110301150b0f0c060f0a110f070f0f12020105091b01080112030e0909100b 69
    0x81c1110b9090f0301d6007401d9024a90300c82d0a42203030090102242e06000030440840051b044014100301c05840b80020030411081120301d021600740d80c0c108810b41c065079410000040d4110842d10038200080c81d0104407200e51b072406440d108a180c00c5503902e64201000800c8482c0c056000c4410200100b0701807290710360f0300c0d005580b204d1030302a007140c980030104100030808000400940d0046070310302d0101e15026030b241000a21200070b80b81100d4080c2c980b52003070244100e03482040c504040842c000c2110b800a03070603c80c002280d80c450080c6008011079120008080f9a0035141c40800100989a1a24100c1d050520110040340c42140d018038100c10f440c46c00101e0030a80c5c10b0740c0302c540c0081d4903080054460210004220b882101d10135001880c1000180d29441114010300168002141905080c2989418107007401c04010850820150004d060307a0300420060440701c405260348812a030605048030350101ca00c0c2c401d50001504014030606035000600c0d40c11012042d4000c200c4102000e0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 219735566 1250 219734316 219734321
    0x1d101202120720070b0307020c030304180b1503070807020f100518060c0a0507260a09090b0307050f040204050d050a06050c0a0801150c050706030605090f0105010503040b0901090c0f090c03 83
    0xa151030762907002c1030042c448140d1105c02150410b0483c0100c44e4801006000a4956032080c3c0245038a80f400155600486029001d00b0f0428001200c2c0c10a0040115006196500000344484100140100031034034081c001d0180384202100c20301515098198000740801800064a0903000400010f03507176418203201140c054080e14043d21301c0c51820110000031149500300c40004c1e105255100b03100b01d121500618102c03040c0c0102110070f501c4407440311016000169590221805034100801a050fa0703501044240c2079502c221048a0501d14480218009000b02e400c0180c100c80c07c2c1540781d050020001700c07245c410b44203407410700c095980c80c0c6a812560003425400c2d004034207840c1c018001c500c4244186120202c00d0728084a040c0000d486441c900211070f031050b000300350358190600085c1485441181d000c107011040c040e0951410380003c1003844002c0015001a900c0404280003070742c00c0d000701d1245600000d83c0b440f1a03840b0407641d001d01f4000d02c03402d461140341001c81c50075107002c0d0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 219736816 1250 219735566 219735617
    0xd0605030714100807141b0d030603150903050d0c0305090f0a021f0c0b1501021209061617071b080f100f020904060f03050606011d1012021207 63
    0x3074800c090b201c03e00c1c0b074255012000034081000f4030199000d48074241d40c5810162101071103c1c50341d481c0c51840001054105401c60403800200740c2882000d102062200300d0440c80c4101034103000902107991b080441e824042c59591313040950030100e100d540b080d4950492030085001030280e80340180308000b900e503a1522040000d4008612070801d52103101810034100e012140380c10207001c0203d203036444503401041151040c480f52040c081d4021035590410420028440c504107141c60030361020300089083c09101c0200250300c01601c0844108004c1c0e103d600b040c1a00543d082e6222005890105c0c21700c002600328020020245500240c404030014804103144e941c1c0e000780600048080060000e0580c006040c08500d408100030b90b00ba40300d520030700c2d006090001030080c1c06415464210708041c80a05498100408400c240d0080041d48160307840310f00040340d5841041c1c114078810344406c004e0100c103c1c82c20340301007090314100600b8100580710f042d907a650107050140900d6081e081d035014 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 219738066 1250 219736816 219736819
    0x1005010e01050d111c06090b040c090c02060105091810050402040f0902060d2a0e040f02040503100b0301090821010e01271404050a1a0105010507030302031009020d0605030714 77
    0x2012180c07803d001201a00c21721001128a032842104e85648081c2c0740b24040c1290081041d5041005011413240220041c0c006a2010311082d1103004000b5503904040c042c69216140c2100414800b8105400051100c2907d0040d1492111000c4000004203421103080e4080d80c2040002000e40c461489560b950350307130003821075040181206c84003004054902c421510155403220042101004204890307860009640d2100700340c00f814148401c2e22003440170060445d00502040c040b40e03802040408414040703000005000e84010f000030701521030101d014252440015005000d07020b4600010510001a4896161a40c2c3d80551034030440742403166200515215003059451406c00100b10050404000c0c045501240c200000c070446006039412260355120121803020081e812168440000d40842c91110b40d614010010b030040c451414010201580080050703001e43d42d10007040c000c0c2500150454660036910000e030018406401094800d2141d81c03800070f80d514034407480e0600940d0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 219739316 1250 219738066 219738083
    0x20604090b0a08060c070615030b062202031003030e0f01020304140a0b03152b0b0703020d050403030204090f180204020703200307110d2607051005010e01050d 70
    0xa01100d05005281100303585912200c0d054001411150402c5254007403140410b2040ea21912854650110368014007084050900b51f1010030202d14040e10300307a4048020741d1003100450200c00c540030350701d0003001004e071440d101005000c0209034521424059900c640c0703c11201a60b850101700b0f40000b403880860050b40100400d11601e000403043e1204000040c140c04507541d103c041e020101e42080354030004410484189811924001c1a4100c1808a0301c00c00c1c07846000d0800c03100c1c03509000b41400362070a801000401c00252295044820300750424000b045242440d1038020080d5005104802c2d412b41407590300f40e4012498850066410402108194514050390a2001035040828150244150007000b01820644090245000d074005030281d0741e22075051500425180ca43e660141c002c0000b0340b074480c00103200280900304001d03c5c80c0d1104101003003281030600c0d4452248000c00f02c0c0140154400c0300f400a400c45030603600c0840c06200b00303a0301d40060040040c2c0004c8040c00048 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 219740566 1250 219739316 219739319
    0x60f09091b0102010f06080303100b03040b070c020109090903080709060932030703030908100b0f1207050607200d02030a03030f0908030c070303110a0207050f03030c061608070201020403020604 85
    0x4080101012106041c0004170b544a40110640c08031403680c0e02c148104d400010420034040489100a400780003d81035590460400e91100d42c1d00c918000c0080c03081c090034408070000d6a004400ca0380003800e5502c003c8c8045412441c0c01031120b882980d84002240050001140950042040005640701c5035410000c440544600250303c403607140240d6816000f08541c050551030600444010794040c4d16407c0441e440c006015141c03401078004107080f1460310301c40351080e984c3c240740c016403c0c1c0100c1c0c2d078201902d40e942100d07050071007592006600c45400640f030810800c150080401d105144c24441d0034101040042c40648000d1100095240c0c014504541c0024001d52010a1031070003400f0024081d2a00c0c0e88050441d0300542b030750620b24201003100000c1590501440301c180316040d4409042c4a400302000e591600d550181a2080340c03042da880b62a501e040054900703060320a41111403900f091440e0007140001a00c40c1c1c0000341100001481c824014022103013183ea001d810745103040d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 219741816 1250 219740566 219740593
    0x50f0f21070218071d09070539100b030d02120703090906180b180105041e1d0d050906040b091f0203030601170103080703080705070b070206060f0909 66
    0x3540304107400c076030109010076040b920081e00035080b841070105441d8607a026640300200054240e01c90262407007030020f0720803c5244d980c498269107c414004c4100d889a1071002c016491240706030312094150032000d400000c8100e000038050b1944480103e0401c5500c5c011030a05031112400d000601c0580e00803034042e5070001002004040c09030080c03078407085083d25010300c03e0907034130940c0c458852034070080000c540c001458481d0181224040344d1510041d1300000003a0303036a42c414802d040c0710303135a110241004422041111034400101c4041000500280c032071121564102490140c1e2501c146900c1c003049a00a00c02c8903001c1c0340003421541414030b81552030025502c520711a5410429a029005910002c0085400603401603000f071600d0303107026400103202c0c800900c0031800c4655010010000311350250100c8e402d09415160100c0e4030765400400750b03041d1090590007071109982604211069a01150160080340100c2c0c440c04c409202c0000c004849006a900d4041a0805c1c0c01c5c60039030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 219743066 1250 219741816 219741883
    0x3151f03020607030f090317042310031505060f0705012904050403170907031203060501090306090f080d0b04050106210b300c0406030510020306130603050f0f 70
    0x1746558900b14400e81e840e40c0c2c0346000d0b1110701070500f5030004041740a002d0111301c078007541d01c51440000707001d2030107100d400000c615050100380841455610350085060504880741c040c05014040d0006603241d03481501003120f81e114803400d071000d51900650041b2041003140a4801004100602c2456248401040004c0c58007070070031001e01c2007990041240c00300c100480d030f105540140c00342c02c2040c954184032020103101650442054030705981070015a0b00680c00c1c40549410120001d092030744c500c3d00807644a08000042d18141d004640082504482c0e00941e08541c0291800c1c001359a03a00c00a8880d030704040700c071010f102019041840f26208960181c02000c0008191b5084400111500000e10a850300c8200d907a00c45809290944503007044000825142501d007008118510780744d40791100c1503080c015401c0c540000100d6811f5840c8800e5503048120f9440030001165645081980e0344151411a5280d001e61300700740c00302010200d10554810035022188240f0601e21010240 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 219744316 1250 219743066 219743087
    0x10e070303030e0c100e0f010306050109060c110402070507060219032709180b091203010b0d020403080d05010617010312050705031315020601150f0c0305070203151f0302060703 78
    0xa80300c2c40020301d11541d52044110710301d000945815103201b50b070ba014820329801d41d0038260b05050803c40108500d990089022044800514118001d0b1480d0711b049281d0401c1000041d48c4117001154030700a010010904400b103803401d40803901e207420f816021070044039000314007402142c440300e116051043c2c00d402081008050900e003000c40c2d074030b41005004232200c0c04168a02c10300390940c1401040590064140c0080e002030041119903201151801540300500400545440104110051003643d4058070301566200340515120b000095507400102000d00c90000040c1c41c0008050300701044003207090680750000030100c4140c46120003501c143c2c0c0940c0302107500348410000a95840541c50035200500040c0207285075000e24008000e00d0520103800c4100c10f005e94004030a04140c00c00b0781c18040c05030a040101c2e0790841401c0648040c0241680a5018001c41180c1d4500903403100354684900c00a00190844005004440102c85000d010007900104100407140109024107122030 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 219745566 1250 219744316 219744341
    0xa0c0806090706230c070e06030c010e090c2101080303100b07030e060906070f0c06020c090f060f0d0501051612020405090a02070c15050c0c010f0c02090a1d0303061002010e07030303 80
    0x900d8017195121044c50408a644030105520640e004d00007107140031b20200c5c503024824078213020340c500c803d00010703d4000302030101400350800103000d901416480510a1301006a54000205980c0d285207103038580d801292055641500010080781c203203100c1e4269100240c05507921484e604041041c0180b0354000c2c86619800342c0280005000100003802e6410303068440d00f49a01c01c98079010f0007034905850040700920a4083c001007210700701d040361140340e10100071182130b44c1e0045000c000c100b03450071002000d400c65080c5404c2159414004080024589080c2c3d03c0c6a1001882420201240594050182d206110314085590160960081c2007054000c0703802048141c0c1e6001195022071084060300003003080410344942c0307264140060440980e0a00701841c4034510408010140882c07405c009125661180216901d81c0c4c850303001079000240001101110f07801d18110381e0743c0f5081243e14510486210310451750b140d03c1030140701c081070303101c400030b21902d0f040d0707601600640205400354 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 219746816 1250 219745566 219745637
    0x904030503061e0a08010b0901080304060503160e04020c0105070806060a090303081b070302060403021203150d051612020f030f030a050c011404060605010305090610170309030a0c0806090706 84
    0x10709007543d804e13042d0801440740f0320001400d1955603007403102061050b03000382e1f199002403104005050708141202d600c500c11400b002e42a030743e20082600c04c10301144114bc0c00c24400300b00544c00c1d02c415880540a1318241c0c880f108566505e07010450144603c0341c0b54800201c180a0800000780510703865500400b6504140c100310b201540741d8216500700d81c03010380040c0d0090042c002810b405000303200100d600400c032a841c44c9800861210201520307402c0368052890403191b007060207400e1040311001b1208088100c0301569598800c2d07d2040a14000d078803803e1000741240407490005103003040850007001071424000c02c020290355981000000a160755265020341030b081d03180221140c4507504c81c581c0010a181410001021101e00414443c4c0650200051000bc0303282c001c8140c0868110303041c8000215070203550309046014202c215600f600c40e100b01e50081003109084201511082000c5641c0d643c0c0d20703100a03039100141c0c0301c1c40e070204040c801c0041c545118644420918121103498 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 219748066 1250 219746816 219746869
    0x10f0513031a040c120512071109011e1d060f1305010816080d0207030b060d0203060a1a010c0c05090c07120309050c0d020612150d030518090403050306 67
    0x1080c41d0080c9402030340c0780d02c0b0354803810002044809001351001d024480d0346a851805103a44455452503400c0824403d0f900100b030030f07000c000389102e00d80c45015010f462803d055a4444882c0c0b6040800c00030149000000c3d6400310341281c2004200d00044c40482886c925500c601c0300740404181d80034210313500090340f2400503440811701d000c0c00780245600801040004000752041107a1101500510b070141c00070b6a03400081580002c9860980b9003120030207070030380c031040001503090b02d080b08002e4143c000d250401034482c0803039104560441c0804c007613000038010500110b440c0c410403100286443c0c030100c010f00081c00c06415550380422450201483c10800b0785680040c00030525540c00080d4540c040241082018403981e80e986200b0b5420b203001c5135440d80007403d40e0082000e48261205000000342d00584030745003044c0e28a501604082136045a400c0040c42984000ca4204070104811682091400d264800314070440c0c043d990141151202e8003002504192041c0860b6440e400b00740 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 219749316 1250 219748066 219748073
    0x90201090b250803010e0106050423030102090d0605041101080105101d12010e0c151803010204030c030507140a060e060306010903051e15100302060705070b070308060405090c010f051303 82
    0x2004200b490042c440c0503120341c9020600f030b407440016046401000400d010420003540c0d0b00060302e648244e900c806050107050301c00070a0080c002d622145500c401807001c143c0600c84d05030f20035070040d1301070311840c509540e65900540d401302c020303c6540d801441141403c41d4443c415410303511520141d81d804e2040146e03d1f000100317a000181c2d85d54219940d05c6160381d000780010000c846072000291085145070107480380341d00803805585840142c5e0200041948411741c0e007941114059030f40701d402d40c499140c5070300b801360707131900d0f6402180301d0340074028050346c084d1030002d240c1d0084805940e6282e001a0441e0140080707500007405c0941401301c44000400062814040000c50400284411601c1480104440d151898035208019440d29500a104d140100f100210b42941d4069030425500d02130782c60414942641c40d400701c600340001003907a008055110b42a58011542100c090243e81c440001c1140c45902c01020207010a113005040d20001d8019005000007104131500820402d03075a44 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 219750566 1250 219749316 219749377
    0x303011d07120908570f01020306011404030f020f0609130c0f0e0f0909030d0c0c06060501030e0a021207030c0909120206101a0c03070c06030b0103090201090b 70
    0x40301110f02d00404602415080c415082950307150040c24461a03d0420045d000d8010034145403140c2e500d03100225850303518010b540704c4004113403200702c1242e000348940110f042c002c7d00180e91150001c2c119921110701810726906840c1034a4000700c4020755903400381d0030001a203d1040c90640c015509128005090b5620180d1000d03803090b0742c501041c001d1115900030021000003a002c42480821144128581c1300c282810a80d10029030321000c036512070840240c614040c80550046240c10008000110f40c1e001660082d0030344140c90230310078039413960019025940304c400f960100c0c3c7c2c4800c070480007500d4800c405104c003204140c1552101b584a071038580c40704031140c10441c0c126440e05000c90810001551201c00035041e4070103000c036400c2038502010240101d108031210940c075948082074030400e62007200c2e00084100c048075500c800c503181007039488448c0c0c880c1c10003107881c001c0240e440354040e009441c3d480b41e05030b490401180c00d008560400740c1105d990031000751051160210641a0300303 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 219751816 1250 219750566 219750581
    0x50607300b010305070c0506041104090f141c05120a020f1602090a090308010e060616030809070f050d020d0c08070303110f010605181b0f0406110303011d0712 70
    0x10001203001c500d034030000750a540d800b401c800b0402480419150200300041000e43e0402d80c00524855030407079010000d00540b00c01c50307000e401e10740003800244c2001141c41103c00540014010386613440b40f520b03001c6107421703421074104d004074400f00401030b00d50b02d450002590000c10074400504200c1510200461500304d05612280080d441d131242c419841c0001c0403035442081d202082c485103030f495074002d21081062150010071401030b40460216030b80d800a44415840b1000030140c3c0e81104d0034000c21a40c029140e90019014440003c02d841122200c81d900b0350324041c0111100458a0f0f0a000d50811108005e0311014181800860340d658107000c04001103010f42e0340e500c214080884400d040410403040000968900f207000c00c010344811104c0d228401c40d10070042c9159880f4680ca04894030781d074400c4001500001540240584044050001c0d41c040b661602114004d4490160303507031100380540120b0f0300e105c504100d01802d0018000303138029030902e00748000e90342d00700340e100c00d96080 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 219753066 1250 219751816 219751907
    0x30b030708071707050301020a0207030803041707060b0f04050108251a0c070806040b240d0302010507020705030105060f04150f031208060d0c030b06061209010c02061003050607 78
    0x410760f1442c4400c4104091405418100c0085160002c040e40203551500d2902c4010102d1002000050a224031030310030750f03070b074800302044c0650724004e03440e02d40014410700d82c50074416210081c444c1c2c0107050074458103058410f130000814000d1200c0300080407400039044683d081e07a01409001c105001500c00680e0b410101008943d10b5610310101e80d428008503800c24110396002104000208000000441c0c104c2d0910940d142e000d805062148501c0d400c0799a684e4000c4003110b610780405605500582c0701391060303401c0d0f91041e0b8a9602700b41c00d0f120f05807803041e406010503002d21031500c0c2c66482504031120800c02d120740207555840828011207035600903524008444000600241c1084289520030821940041019219610b107000c020640c00042d000b070080800042e4561101c4007104d011107603100b880b12243c41c00c2404503018160300c0b42820b005009080118010307080c603103000340540c0d600c2000f900d40c82e40c138110b040301c1d02c00c1c149e03101410500d0300d28034108101c500120054282d00740c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 219754316 1250 219753066 219753089
    0xf0405180307200303070b0106050f04150903020a090902030a15060509010305030901090f0b27041401031101030e0d0e033f090f0d080d110406230307030b03070807 72
    0x460107000f080d210401c8041d01070307041001303024001000e200e499419a0200d0524a480321450f0000f0700280c002c581204140200b14140140440c0d04441c20301c007128801c403030032520240ca038040481554800350000f90164002a0403070006100c0401c07001400090340302c0014a66a40c00000c0e803405c0083e4000d880c290000550361500b5680807580402a01a41c031520703100618000420006224080500f6241194035041c6402c2c40060300d54240301250007401070000f02e543c09001c4ca1580000e21044480f040e04c0c010b07406541d40203008240000500c00302030403150b840c803402619001034401069916003d4800b0f108145034403140ca24051802c8000e086a9103804100c1c08600000c1b95155003624040a001e1a04943d40d50003d0b018916410380d030848065200307103090002ea0058800482d101824103000c103140080c004050421240c0c41d03940d5100f0b00c082d400399044882c41841071010380c5802000010002c0e4001e40044011f03940190448000c0350f40c0305074003410700360b0340e40141c2d42600c1e = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 219755566 1250 219754316 219754343
    0x20105090609151e03060d0b040606090219030e070501050a110109060f0509060a0b0603070f0315090e0613230f06100f1409040308061306080a0b010e04020f0405180307 74
    0x1030039040225884081303101c1c2c1e46136040c5100010748505c002c01005203422a614001070030018190822401020011801c0d9100c410500540c080c4c0025001060006440c00103484e1004100240c2c00e01240c5c03040c0c481d05d00c2c020441d40215603180750ba40022041c4c1d9264502000040d0f260310680302103021405c00003400e81406202c0c6800d0140c05400300d252542803a0311456265921002c90303402403614244420014481d21085d4050702140301c0c103040c4503501c0a80040c0d0482c40c1c1e04169940d0391a1429992a596404003850010000c850050540c0c00d00c00b20f00070103500c0198a511494107d001111442280084918500704045820050080c5d02a004010140c240c45064018101c0c01c01c8a5403000442000300341403a4004002408000030342012035219103407402a998100c2000c603003800060740710840156105001d820884654600c9000014242da540400900a5500400440620440108010203064050b0103401ca11003030410802100100700020b0000d64410b000184a42 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 219756816 1250 219755566 219755587
    0x170c040501080c1c180b01180501150203030105060717130906080d0c0b04061b051e0304034505030105011a03130c2c0a020a0c02010509060915 63
    0x301000c1d0100842800510014107040c0d44150401c1607402d2900002811704000b014490340c1d03241203507000c1c11152951002040c1903c40c0074502c00700c07080e0340e0401d0100c0d981c0c0b400c0785100c824042118000581082c801032000380b910b5002030004034081c851641c05134108405840203070780440119141c0c0a01c1c40e00400184402c3d0240c00010003a0781c000c2d11541c2c0320510041c2c809030303140600034441c3c00b07400300107810805e156000702c1c0c0c070340001c4112003803110113603402031f00a41c00165100649505524100a01ea54040c00c60788038582c180d5070282c1d80c180d0341d20345002c1041c01c8186245040c1c00c1050584100d80c01c0540001038040c07606041201328a01003e0500711403041e0072014031145007014082141c2840821a900003101c1042c240740a20142807203440d2000c207802040804200112155603584004513034000b681c0c203414118000d40300c020364081207104000ca0344000c40c60b000c0b003402c00741d070050018021801020f0120780c42c06440c0e4000418039022111074540b0b030203002c5040c1508 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 219758066 1250 219756816 219756827
    0x160602040602030702030f0f190602070804031b120317070201200909060301021810121b0e01080103120e0d080f03010614040b070210030f0c020105010501020f03190e01170c040501 79
    0x80e910104041d00c1c00c443c0c1d1021040c1c4404100d40c00070640c0389d201a1620420506138100c94005400a0300152a580c0b031303240017030300e28410075400d143d10944124007103024602e0046030040c00346c2c980c4646095000b044145081740308010a2901595a180ca00c0441d910208907a4802030700190941540d46000c00c080100d0004080c1541340070340e20521292a40301d41390011201d5181d0704a40300f8412810307041007224990b089200e641030031801d1021040c0c80c5005801c031103000301c0881c0c4613645514001e034011146e0240920028011100ac038000401c421b010742c05448003040d000e405048505410303140d12045600ca49540140002c00000410085a0207080c0300c1c0d0701110142c440786410f203400300c410100d0207040c401030310940c0c3d203910420916000c1c0d4002103418000d00b0003480344100314000a402004244620340c05801204181503c80305d003c41107403000b8083d04118584180b985204407106075a880b1034070b051010062100310748165800015204488004006d540e860030000010031 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 219759316 1250 219758066 219758083
    0xb0d12090801290d05190b060f15160206071406010f061d040f1b08090f070909020609090f160507051f0605060a080a1107050a0816060204060203070203 67
    0x15a450f0458403000d910443c0501a44000c070440456541200500000e107030300400c000060662113058000103000c0c400384240101d803030040f0103079611980e90500784024055900c0a2aa02a102c140b0401c0d0100120000d800401400441481000001c0c3d021a110f680911025940d40842824404071f1400030440c85014080d100b400015031450031401500449200802020b11900544104525152580584100307400d000040c00414068024008100c00d81c50014000802d41b10004480c071400041c4008424020f000400782d4919017208500240304185040780d10090401000003990b84140905000703000d0041891807500b004805032510b0608803498205000e01400382601189020aa400c030303201c0c02c0c04d040c4104042000005008024a400c480c0c0c1c000350124215104582c04180345110302c0100c18108112619002030480720b02070002c008045a1004204000044000000e41002c0f0411070640143c80700c00da803550300b070703811542202d00144c1c4082010402c5d0302e0200070181 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 219760566 1250 219759316 219759329
    0x610030e06041511190906020607091205030c03071406090c09071107031b14060c1e010b06030a050402180f0105040b0d0c08010603020111030901050414040b0d1209 72
    0x4052081030140da00e6500c010005014075140b0141282181c2064111003a658030012880f40e8a02d0030701003013403503015059041c01c00601c43c2031020402c2400001d0281c00380341c20fa01c401503081e241002d050000c0c0d03603d01040303030503000620010070409000c00c0a801d1091140700044900d0078034003211032800c4802000d030145070784030000242e6652260b540c0a900840c90340b60000550401d0b00c06c240c5040110750004208803c8405030010350961460403000355000703d500318451841140401145010785c05000d40a508074451b140044039200750b28010080000e0004200850b080c000101c0b2500104d0740c640100c1e403144100070841c50300142c3c4801c1c46424002803003081c01c004201e0401070205005007400b496586006010310f69822400c0c0c480b166100c003c01400340c0d2181c454a01a01072440101d020840072201c0044aa2002c804d54205107010f940d418281840c01601c50542031010701d009401c165141c0c001c080b242c46003007038030f400a401510b040d903006035920300040c4100c0c074540c043c8 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 219761816 1250 219760566 219760571
    0x5040e0a06060804020d020301090c060503161103091c060207051f330e010b04090623060304020406080f010507120c210e031b0706050414040905070b0c06061003 71
    0x703101e00c54009180a802940580750018800150710119004110a88ac06010301910020003c0c0c43c40c2d20400a6204400201d881e01c04d00e0100d4000f5158a00e9030200c0b2581500184005840381c105031401c0d019a05186c40c036000e5100703554540e50102da02009058a1a0700103000b0320fa41c2c07150341c120b50303440160605000c000c40f9881065501020780080c0e2810100050600c10390910043e4100d40c0015082c4107038006180e503502c12507001240d00c18821b1030f004a0074403000290508004001034074450001b821080d082d0107500c04c00049900042c0700300e074801c3ea0780c0408102000c08000500c00d00c2142000042c2908110ba0040c1410040c000e41800c2541891903c401c0d103640035401564010000a41003491042c0644c0d910262003c0b00320302c0854880030540c03032000854101c55040c0320101105840113552039a004458622840c007424040c20641060b580c00d5040031350101500900880c00c0e01d007015216020809103a02500512080c0c1d84680c00b032043c2c3e80392900c0071641215150404 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 219763066 1250 219761816 219761819
    0x1020c090717193801020705060a031b02061e220302030706050a27020402070b04051c0201020f090909070806090304050a09060812030a02040f270c080c0a120c05040e0a06 75
    0x146040c084038645044504640000c0c44c10260f4001c11584024140c002e00c480c1c0c58241541000b0010400e08000003400182002405c444a0001c20458011450064041c00050b07201e1504480b0440140100c4c040802004030301511100018111244a1090f17000c0d5603541d40504161003a5903019200c0400e0700e103041010b0f030140616809042c20040108034641d109019400010002d00a440d4041c01b903190340c5041104000340418000c0c03000486000f896040062202e04038201c0c0200d00c1c180d8885603040080340e585107071030580151302c042080b003180c46660b02c03540d50701d00300f80064910310000e51001c90140400d00e0000742d0351024105400781004101d06d8154500d41c0c1e4420f58140700d00b00030b400004200780103505d8040700d0240c00281e280b24000f540c1c9071038012109140024a07900b031000da0303c1a004000c241c1c0110030000c1c003641e1faa841c03c6d0b10380c442d2a41c802d03440000c401c000d01034410000f44801625001e207895000321925095155860400c0c0032004000080c210a01e07280780010 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 219764316 1250 219763066 219763121
    0x206061c080a09090b03011b0e0310090b0603060c030603060a2f1305040b090703090305040b0c0c040515010918020c060a060302121f150e0f040309080c01020c09071719 74
    0x3400c038208c140c51610300c4841030038501181c1080d01c8100010401d504010070117061044c01c1e5551801541c01360200d500a5a076021200c03541e010545a40c2e60640224002c00c00c0e5145070307007000ac280780003103101e0800000b00f40d80e0b00c80181400400c06070710781030100b500b000c5003a008003040020807090301e0034803c02c10f0100020349a031a008040700107265407401e140d41414071900030307200030b00840765025030340f110741803d02a0745a021081c4981b1a0742800c3c00030343c40098101454a01c440181c60301034017241081b500350410301800881f080c0e025820710801005081c1005404d0050041030000507070329046005104079540c200013060401d6007e0b6180349c4400d80d141c2d900e4440340c0c420303803400211000c00d241414440e5421758040f041800200c414410041510756449001d580b190f01d810400c10740d201696604e6420075418140560400c42006280b401e044848690002503850007894007844000307101c2e4034400691b138101001c610f075403100c0d034501c4442c4604402c40050070160409107003d4003 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 219765566 1250 219764316 219764351
    0x2512030903080a030914011b05090d030e011b030305040b0708101802090402040e061305091e0c030d11010f0612060c0909020f070618030206061c080a09090b0301 71
    0x310041030198000f804100b201e10981c03210b2501e90348620488103200048030000d0107000c1800b0f044604182c3c400c42c0b0b1030309502640455480c0a0003a0801041510f103460a90325902c0c0002100d0500035045800708080c6110307601064007602c03a0b1000195030034907003094402440024148414440c82c032007805545006001c00d1411556043c0d50101c5400a11441d000640140002190841d00100e40483c1c0c200092400d207125007000d40300300c0704a0303555807080300c1502c8040d2a00705407900311101c9541d8514904480e004201030580840c7c6000320b0100101c1e1820340300c010000300140d0b400c2803043d0080b00030301694800051446003885042d080040720b40010250381c00040c8030a0740c0c1c0001d0500c150243c60000000c0c100070b0720171520b6068905030600182e1000004685061401c080c21122668108850380903a400d540100215980d000c10300c40c00020708040701c44070094a056050025291700001c0c50140b61a0740e0b004195464601c500054803203030459a403190f4103020390070307406101c41c2 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 219766816 1250 219765566 219765569
    0x1005091612020a0e1803031008010e070506042d03230105091e0f0f030301051203120a0213030b130204062921010308040e1f03020607021225120309 65
    0x203007008003c0e032a0303a461881008105ea261405c240030110800110119410002c01144c48641c003d0140610541d072590b11500d150007030340c1d84881c2c02d02052104840255408481100300b034000d200c0c4008215900a005034142e00458450341e80300036144070500b080e980c456140740039074028000c9050000e022600c8002030881103010280c200603072032008004202c8403605000420aa03040750011801e8141c4070b91090003420b006030325901c8036004103100007040703400072407000c50040e500b078594001120181d40030340c0140070070000c002404808030300c079010344500505140380c180340260250b00c14802030303441c1070b84400d400b003184c0720030f1500c0814440004400140c6000d10103544a946000b05404101d0156042842400d048000b008115035a001001640c03001d0185424540d01d00b52081c03143c00c4884500c070010000300100308014140900500170071380c030050034818403180f00089180b0700642c051034150350303c0102c0d00000c104994248048054600d8800001100c07641c2e880252100f01e65 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 219768066 1250 219766816 219766829
    0x30910020708071202060411030f19031e0f14070b040308042a030c1a0a0f0201091a04060b0f10200d0824010915021005091612020a 58
    0x10300e035042000b03100495240c160b10035841904412026002036a13a1011201169030001007002d02d40d442c076001500302200101c50300103006440c1003990040d200c60500c10120180801e030425074900007002d44100714501076581d560740f84c248041c00000c0c00362600d00d06d4550500000c00c0814041404048900c4c0c0c0103801d41040e8a59445038600301d00007104a8a980107150740881c80007100503040c84040301160b0149a00c401c00c1d985603403070388600180e00c0c4102815040104030a4210b240030781c144150383e80c0030340000207080d20203444a00c8010341c18003080c0e640e00c49000800042202c0c5100344008900d003a980c05054011440102c0c0c00710b1180080d10081c04a003d203a50314004102c0006e0f000e0706284000d5804081d407000d000b4041d401f00360340d40018100d865a8080801c028103601c0d0254850583d6004601c42c40c0181c00c80810740300e0320010085028070143c8010703014440c0240c0340504503941c004d140c1e003000e45503148141541c54200c103114602082c20100569500740140c0b0a4504 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 219769316 1250 219768066 219768071
    0x1603080322050d0201091a01150c050111040f061101060807060c050c0d0807030f080c0301050402071a150f0108010513110424030c020d12020901020304030f08031605030910 76
    0x140994250592400760001000d52040d529482d10060303040d0805403009205502003541c41400d40b03041c03510b038a0709014810a4080d00861078a16a108070814112140200000210510294080201276010341c01900030740c90301600400c081030303206002c0c2c242c0c80c41140080251768240720388203454241c4d40c4501010046880301c50343c240001480400e8081c00000c1c803c070311840c03107490040c1940e0400318041d0003180c410100c4018047c02036101e10f1180b04518286865170b070800b01004001d4120b08025640c0710f038040d000f070030000d6840c44518024014405030304000c0780b18204004a203004014014100001c082c010003094641c80380395402c00c1c488210105102c25641036091243c06254050147d020b8001e4003441e0f804480d8648070041262a071342846000c1c040c00d03041c2c2c0e54181301c110403000540042412840303a1174580c09007084280500c10340380f40c1641c0342c944103505076824506840b84a4000240410804100180d01c0442442d0405500798038060301495250080805a61903454 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 219770566 1250 219769316 219769351
    0x4050703020d020c0a02120f0601050904030c0b13050709270303020c07141f02030d1a120f010f0c0504140301060902070b040b0106030b03070504150906031416030803 73
    0x140250151100b00c0c1c0000300864850755401c00070b69070f41d07100000680c050094026203070b400032004194003140039040c0c00203201c1c60f440c02042c131024120081080d0b04000d406d111800c00111001c140b54000c04c1c130303510014110001420101e0600390550b0003040c000b4545076038404882805024124484544101d40c040000c0c5420150003034441d41c580c074045401000c80c049001c40034904003001c506d0040c2e6200c2100321100e80c840d1007100706513600f000541d006100b65024014540c0206620350306180070000a0800d0348041032101c809198404000c4c0c00400000807036000034414005a484446000c1c07141c1c44032404040c019102e0350050000e8030403000f61510690324250840001030071080c0c0c08560f99441c500340034401c2441601d040740c466000f0400090164800d0240c1016030a00070050314156181c8000c00c030040c00c1e45e4100900b5a82c0e4110001a0910280300702c0c0b0041d4060761500c03014260086845082003109021250300091103402030000c0380c941e0040e41e0b480904450f40c0c1c40c03141c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 219771816 1250 219770566 219770581
    0x309010b03033901021603030605030d1b060b0a090207200a12030215100602010f1103010510030906090501090c0e0f0c090d0c061d0f0f150d1514120c0405 68
    0xc800d07094100e80790b00011b07049081d000b560404600c0c090090740c04104207620392081540b030701415503403140050403aa501d841c217110b40340c5100705914400c000000b0100c041d4408200082c1d21039012105446d80030802c00140a4407821200c00e420a190803019003895800011b0b00d1210180240402e0520603c403040c20180200890041d0340d0301c404d4054041d00c2c00d0200d207150f00305103000c0e041c015400c241407903080c0b80050040e103d041c5d580c20800c9003103a003090700303000d1544030a80565041607150300e0700c83c010400500c500b1050364001c0c80040b540e00035604201545100750744c84010803042940811003c4031a01c0030705034100f0360001e003031603079000e6072800208198402c15018014007445040050401c0d08803c100e2604400c0d080e0b80f02d12100100b0410840c02c0c4240070607900900401c2c1558030034504881c000400d9402e0b1100300b0304190408056004548064440c1030032581c5404040c4003c1c21240c03910000050101c51019840244040003602e40c410f416800c0d024a03112004143c02 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 219773066 1250 219771816 219771907
    0xd030e0109091104170c010c060b0d020402030a020c01050f01060203070b0a0e030309060a0f0e07030b060d0c08030a02060105060901021009030e060a080a0605031216030e0d03050309010b0303 84
    0xc1c11080000d102050f050102e804080c0d1103841000389081c5180c001c541d5a040101d04103d003101d058441455070140e42d01c1c1d10014290b00001598800350b07010035100141c2d6188043e600540c141403006840d9903108000c4ca084850152a884c41c480340e010040101c00c1d1f0000803902d110742d0010074020b40307403110790104d009070524503610311042c0008420044034544c000f50791442402107207408e022040d0724000ea4011548408100005034100c8030b82400072803030701c030001908802c003c1d1150400300030a4503584144200c90300460503d4000085104801e03130304101c03043c098401200c0303c40c80e000a540c0040c0d6151341800e410304403203807542c0c09031042c9802182c6501d0035840140905503148000540180a8034013192050f00c400d02e000c1011a040c103000400e00301e04481c01105500c1e1060506200c140c0c0e880c4190b0440400c40810001a09905c2e001c0524680900c01d40b00c598a90400712100750940d079080c1c03541402540248a1000b01107403a0043c103000b21001d8100121210154070071344070 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 219774316 1250 219773066 219773069
    0x3190905070b1801020124031403121303080709120f060f0c02210a050f0c010f0c03020304050105070c080d0c0e180601080a050c31060201050703060807050d030e0109 73
    0x742000b001c500f07500010b503090326030080765000364001c0082041190601900c2141380c1c2e80c0c0501e400f10744000b0700016003000e0440c0c40d100c0411040328113084502d00d401c8a02c0004654a84440719003a130701c0d4007003507000020a0b4000d07a030707420410000e908001c09036803084c072103800c041c104842c1c5148010501c80982d0066540741c2199009003c601004c7d080030703540d407080d0181c025130007044168250f03000601c1c600382c07904000c107a51800d01c0c0818016030b0803150b810000c031414255507281659408400144a0080000c440c4e84000d071f02c0e4075250410314219032005041c00184080000c0031400a15150201c03140000030324800a4480d40c24041107400c11280c1c2186030b01320b0030070040241070320442c1c01c203680f040600342e03900c0d1501e54561203107a054a00648400c0d6081e4014002c0c070003c080504030384404205210060100f0711000e00320451090019404140581d540700c040c04031240c2e02d4003c84000e400780c07000034040c1d2803404021a5841e03084040107020400030946c2407100e03a06c0bc100700c40 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 219775566 1250 219774316 219774329
    0x1111c030c120c2a050a0f03141201030b070e15180a0914072604031e1701050f09010504050c0903060405150f060117040204022b0605010201020319090507 68
    0x1145402074041c10510000c030f02c5030b1a1341c1c08082d80115004441140218055002004e482015682d40d074140c81c2410081080f42030114210f114072000d50920050208107060942e101e40f50352450800b01a1000090320000400c8885261640240c40d140e1407510120102c901d402c0e030f0741c02d002e2103099001c0c0c000d0340244c1c1d010b5800c2100054192a5810401c10145d8041080003140c445000a80300c151900340042d444406610014280c20000041d240d030050080c01e0842900c81c0b0421040170424245070f5070004903681c0703980803031507070b424030262805030406070356803483c3c03400c903c001500f1100148070f06803007107031a8800a44403018141c1030750310800e030240032101c6500b840d03d00151601003c02d114200803030303008001134444210902c010700601c0180c507540b00407036030203410700729900006000b40d070880d80030010300c01c0c480f8110174075032545d503d44c03032000e00d0750196050313100113480455002c281168014814842c5007050300f211410090155075000a04210344d14040d410704c00c440c0d001c3c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 219776816 1250 219775566 219775571
    0x303132102030d06050a03020a030602030a180f110102060108120f040506040f18060f09020a02010e1006050a0f0f2303010203040609020906030d0207050d0312090c030201111c030c12 80
    0x201150700000980a64403202100384002c544a0b4180840305076203100107580028403ca0803c00302d019640110382040c191200418443c01da9078400c0b915072348081d801c94001d81d503580710b00c0500107001e80c0080035490920203000720f03516000700e15a4a42030b0090741c0e482110f000442c3ca5000300a80116001480d02a01c01c54496940d0741c07001c0c440410910405035807100119005001c02003a01c644405c2d54070816410009909041a05001790441c10b404015596560b1085d1345d140744c1007000c1c540038034441201052890405c400d02136010f200346e10050f0054007090f030a21501e12f4016a01040d541c0400518040000c1c43e00422594282c0b0f114090300355200006000600002c3d0300100a454000e03a00c40f986034840c03009150f41c84c6290681000140c0010300240600e00e000c50000c42c0980c064600000d40325480950740045503a152012114003918140030002c5582124a03080ea10307040707001800c0403001040200c80c60828010080081560700c05084202e0350281000c0844640000d104 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 219778066 1250 219776816 219776873
    0x21602031501080607080721021201090b030706021606080405120307030b0406060c0201021c03090605090109020102120301060f050d0e100e190c090b0a030f08190f02030313 76
    0x101c89208900b8007860115001e140c0004808078080c0220b90b0184d41145da0341088074001c0720310f80e040c55815010364003495800f0000071662607401d0f26828040c0c207102000145c4100d64404061030b0000c50780c800c80554109007080550f45203d050204103e50341801c1008042ea11854401e00b0080c40c40740400c1c080b4004001d02010750340c1030b44008140d15003981c0030010f40391200010348201c90410702c0240160f0120070525070300100c06904044e4142c4900300420841150f946850503a102103d90031801e039035904211080d90390421000c0d800058101c200ca1075541407900040c01d0b410844044414024000b600c1c054039030480d4002c41da0300000d40c09580c0f40704075503905230002d40341c080a82d000340d21440aa1421310f120300c0c414041c010303a100a00c20303d02c40c90250342da00902110202d4a07403044060400102080c2c200881c3c0d850680300e244601d03990000d05042c0381e1601070f8840d00404001074031800140315038000048036000b80075105290b45d036450700d1520100100b845c00031820750242d06c104 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 219779316 1250 219778066 219778093
    0xc11060903040302040c0e090a0f180503031509160503071715131a010309020301060519030303140402060301090f0f0c0c020103110c0606060a031107080d050609091002160203 77
    0xd4410f40c0c1c400c031418401400c10000c12100100406102c40d44900aa000b03c0d1101d1020350204036880400d83c1e01184441203489440260311041c1800d9800e900000204884640410201c6803070381000c54413182141000f04400058280f40c1e204e210921030004041081c0c00e010310000d94001210510101c2145040300b580d00d200c415011003103000d211405d490450150345d41c0038030b20312a40da40100c41318104803407004401a194141d42a609035503102408a03168603040030840034004174400401c0310515600d0f00070b003200c400c0c0c41d1150420389400144030042ea6610b0450b41110710014001c280d0701481ca03040d00080c101305270741c00b49440c6010346040c0082e0b00640b080d44514000d880402021000b81041010391003220300c081280d80080c00001c546107054005000362030028600002d01c142049000e40050348644016100d1500208183c0e4061000340122640800243e0b62403820781001d1010956074200400f4081c0309540104810107042c600034592400c3c03640040841c5e05a041c02d50 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 219780566 1250 219779316 219779323
    0x5030c1e0c010c023405040204030501050f0112020a063b010e09011d04031806020c130207112701030b0709060813020915030f010c0f03060302060702040c110609 71
    0x2042410301d50800d25a10710060020821315140d00440c05d002c10f501184001001d2800100030420440d16040c450201d0180c03a1840900050351203a0000991810312514003000000c050b40300120001905422500607100e800c0903001b100ca09041040e80f800c1d0705034107030590820074016410103401ca41020782902ca28580038016050007a22034903110741c41541401040740d400d000703c642c240e2034909485c50040301000e010b94800d00918051203400344c1c1000c01880144503600c80d100503888100344031203d01d44100f0b0090341030340d10b900461601080f6941d007000100d1314100300340314031500c038654980b05241c1000d6120314001e1106e070303c1c86503031030f49002d41440d202610013100044e4036040104116002c0c1e01c0d12030082d1001006911024296401c00254a2008114448044081800182540301003140c0b4640c03840300340c00450a10a4bd0790300074a803c440e00c00364020142861400c1015071030389412a0a0aa0199004a0800c0c103142c41955024030f00700c8110ba90f03100d910200b000b20030010 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 219781816 1250 219780566 219780577
    0x302060c07060e04020c060f06060c0601120c0905070210151d010321021e03090a170105090c0f0105090301090c0e01170625020c10030603060501210305030c1e 70
    0x191114501030fa60071061208070b0003100030400c01d130342c0303e60302140d03a01d80d240c00d8250b48400d009080c54541400d0158070b500305035084c0c8c8981440c1500c04540410450b003006110040c000b014420401840d107030000956921441109038142660355080c40001608100c004024020345091aa01400c03010030b140c2204009100076150120030407250410740b80b442000322480c02c1d160303004002d0070f4541c0c8103d003c0c00b20b0144034443c2d1803108004905950b05c82454000041c1000521414215042d500040c2541c2006008003010f4100703427403009059881c2d0503078080a920a00c1d00c5a2160001d10100c1c0c01010f1866014103603030174018002543d14070040300c01e4141d5500c401040000391071189010765800090750040380c003c8500e080b01402c100c2547d4411003115841c1b04a0b41d1004040b0007103100d00031200c06400000742c81d1407090040c02414020540105650f00181d000e80c01c0500c10035507114017000000701040f40000114403600104c400740c0b004103c4996554450000c4d07088641c049602a = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 219783066 1250 219781816 219781829
    0x100c1a01060f110d09030b0c12041101021005040b011205030f04080a020a0801020c030306010806040f09060506010306050a08070504020c1c0309060b030c180a090b0901270f06020a090302060c07 85
    0x103c261482032182e000c55505419003241d100e07410300c90308540d901c0c1d10040004081144409062080240d20344032680840d010314000c00501e401100c400d000241004003055220203d00c0c14a800d22000920f22100b00741121050b40300491101d956280c0903046d0311450f0460112030740c0102d00424181d0000c1404d2103102c2c0308451200460350356542c824241d0023050071800b8a0340040c0300045495008080082c0d111400030700005108420f0080d00c41110010320080d0f0341c1f07680d19010000346503018840c181c050720b0100d075628107051a001ca003030b5031b41040b401414020354010a1458081c1003c101c00110103021040040880b840410014010b01181f0002e9035142d007056000c007030b58100801e400c40d03076000241001c0c400c2e02500c216100306080140c0703450903d5a0701d4150318040389000700c0d80c034095907125001054a000041010003c140e40410200c0100011180400000c684240a00482e5840500540c03210070305c407010b030f071148441d81c406074000d8400a0440c21400c0b01141c034805880701c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 219784172 1106 219783066 219783077
    0x4030b0a060302090a090c030f0c170a0606140303031512010f02121b0a03090c212f0f040f090510050a0b100c1a01060f 53
    0x1151991003155940109104600c0e084850503001194400240718000c91501d450203101124030008003207100e03a60b0300104005003a40c0440c020425401c00342c0358054024241500c0780b0000ca1304139070b01450b001c008600c072140d48185044010010b40110f083d0340e519407582801e172044600ca00c2e440014443c1c041010398007400703064091900001e016131940000c0078440c0904401030005002020300c58034034035099031040155829102c0c030b4600450711000c00d007040480001c19800004c610705031302c00c40700c7c8200c414082801141d4441d1407001e42c02a8100005440c00c4100542550340b16915040c401840c5401400315030703280c000034400610700c101c900d5884202c0c0c0c001d11080b0340d9900555107405c20703000030303126440e40004695424005030b0384460000d03104500e283e03402020b21540c810044240b00705404140c01803c80044841843d503102d140c00b90546201d02c1c0807100181 = true := by decide +kernel

theorem cover : BRFrame.Cov 219604316 219784172 := by
  have h0 := BRFrame.cov_init 219604316
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219604316 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 219604316 ≤ n) (h2 : n < 219784172) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
