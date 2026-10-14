-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2308
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:18:46.147037+00:00
-- url     : https://prove2.me/submissions/08c2e5ec-6256-4e21-b35c-f8d55a84a4b4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 414928057 ≤ n < 415107913 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 414929307 1250 414928057 414928067
    0xb0604060812070f0c241814010e1012060807080d050a091a0409050f07021e01060b13080106050d0c06080a0b030a030807080a0c0203160c120c0303020c01 68
    0x21100420000c2142c04056400d115080e08030050444415491500c80380c0424030f102d0401024021034809004103c4d030404441e241440345111360710510000010042100369404094002c66980c240100b442649180048074540b121858a40c1c0c07001c422410704540c02d03404800c04e8407000b004841003088903203c1002a130344843c98030507540585c0c00162044e01203840b4102600d40c0d101503040c00b2202e00e485040da00034022095880d10160720001c1800c025400a5000b5a0341000e040c480c03400940c1070082c8000d440e10140c1c4a80003015030014402441c001096003e28001d180034a161511015102c41e0010320710300c1031245000725801e210300402d941c903047c1d2404145c10783c0591162492407410f00240c408543c010301034004503689010504d9161001c0c44039410543c46540c4030720b81c41c07801c02405001818042c00112070380380780100a103800d9030000120317041c0c0d04083e61800c0140e846071501c80e100c2c044940041044000748200c0404102d0340e011504240ca20035001c0e80c058203000c2c001102d07 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 414930557 1250 414929307 414929309
    0x110d05040f0c080a080f0a030207170c061315050c091201150b190c031e05030403030501080c13270305030405150c0d0e0708031b06010e01050f09090f07030f0b060406 73
    0x1c05c3c031034100034902a6188000042008411a040250500300b0030785030605e07010304403a91400b01c180009101c0848071818008244e00c0b8041d4450540c0c89001a11582d42002c0c0e02155100d80c0b680e1180841c1d210f01c003c070145e40c0441c4004040c12400c4170402285406030640039180b9405d0141d07400c01044c8144210141c0715418242c50800031090400c500460f80800303000002c0d4240001d004a040080b110b141c01446140403e03219035659080924005044500c16404030307860307401c00f0400c24900c0d560741100049494580d44082500000c80b160b015410a5642c0341c958064903d0145004161300440a94411802201a1801068880d90001c840c2d03108440380605040d003008a07000b8051198014800f52441408a840c01a12084507a00d10741c46882d420801540303043c0340c90440ca0f810440a8054900181c81c007210354075080216004070b440c442450b20900d40f036030005010b003101700700490300480844100c0e2134840c4da0b404c00c80c0b07000b00c0c0180c2c1514111040e0000a9013820b203802450 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 414931807 1250 414930557 414930563
    0x1032918090a0221161e050a140112050f0702100501030201170c1c06080f0f07030303091e080d050f0702061b0904050405010b03010e0d0503010306110d05040f0c080a 73
    0x20071070303032015400c1192869407800e010483d1815083c05200c040d0041289100d02407003110b40e110206e0401540540802904c085910301011076602881141c45003401c1034200c0302d01110f10704200c2207040060f80d2164031480f04005032032405007042103400304118901d0080d221902030b02e13040900d8100000c04c0d900d00f408080e021a110342c2d0000010400720403025840b4851076106403c00ea080c41800b071600c1215043c40400d140c40709d40500400c58140004061061008001c028100c07114582c81c0e224101484040c0c02d00d6a294680c00501022021942144002400f010000d8104c2c0c0b40c04e508a070460107484500500d4200040c07900c818440506004000035001411150350382d0300d135080e078452580003040050704240700202240d11075002c2e40f401703240314200200c1c140b1050000e16084404400d00c003c0b03180d129003149090550131004a0b03040d83c1e0081f8010520329104100d4600c980b0940c3e60603014607140c13400704018400f1840c034501e40c0e0b500c92949041c00507600c0701495520b0307100c40406 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 414933057 1250 414931807 414931813
    0x20a0b03010311060d09050f01060609060314192a0909180f02120f0c03010c020105010f060f02011e0b090702030301050105220521010b011404050f0103291809 70
    0x683c50b18081028056001c811200407807110343c0d80d610b1600f4094a210410241d0303444980c1800102d4015040c80c02604c0b007840d08010880c071900b04145181400f8008881c200b018684900340024250400000d42c03045825600100340401d05403a10509017107000d200143c0c0790741d008150002d09000718841100301d03d40480102d42d051700c0721601015044800c9a110041100400d2300d07c2041c05400300b10351004e8054035a0100380d0b4241803d4400324a07500045924013001800346c000302589190646c1c003107180c44003041c0c0e0707090b20903801011813200c0c514148904c3c0300c04500e2100207400010b500001598142410b03240d9278810780e41c0380402e019203400700c0c0b421700c4003450b202d00c1c100320744080b441c50402c000704040d5144045600c20442e5901c403100040211160b54500401b4015a20214800e19201c44c20b44060209010305014500405204d030104240902e0b80368071a8000c07407100d40112030641c00c40f03000006410000030140c04071a000d0545529030050030b0109051061003a410000a = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 414934307 1250 414933057 414933083
    0x1513020607060c23070308151c0606081207050c0a051c0602040f030803090d0c03091716060e0a0906050d021c0f111c03021c0201090519020a0b030103 66
    0x70b240e000d4a0311409103010000006915104010400e0444c1e00c40503144003000d698072085d04005107841c80080c100401d0000c4a607a8256944030703500403015000c00d402c004100f0030081c0c0b51103400340080341c0c42004244a054030520141407104000c00605125000304ea8165000720103000000001d0320030b680c0d000b0350303140c3c42420452070344580b840050321031803005240680321608085400180c1c3c006458100c070200c1005441e510802451a05854074213000e140900755a5000381402c406001c3d40c03280007080911841c1c030440400c856815a441c02e101304080380d4032424014110828030844911030104000d0020301040c0e036110302015108050a050640d40b00c84d0248020101074200354241d880c940c85003400461500c02c1d10132021440b522040c0350010780c00c403c02000c0040e03541e002c01e00c0f00c0e041c01c613000082c1e00003a811148001248030b03d030541c030700020103030300402d03110b000900180145040146e900350813500300f04010f032007103800b9030700c95854029000320f9000900000304142c00c4004 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 414935557 1250 414934307 414934313
    0x90f0109050711060f07090e09070909020f1e04150f0311010e03030301140a092c120409090606120c0311300d030213050405040c030c081513020607 65
    0xd070b41c04042401c15064802d0821100751800d44103c0e101603443e00c0000034408040c0e44440d03180024a891810480c03d403c5c83c26080380c0311209441901202035407042c0c4d80e01152258045e0710b000b14402810707400202d00c0c2c018103404002000040d03601c141c0c90603111a2481d4560298001a507088aa103d4280303030850b522034081126041c00e0f1418003021614201d015070f400c10085000c0d060b201c1c50b0b0032889807602c00b0700034801a16000a024107042803485509500e00840030b6945040000000c1401700004250702e0602c013041c0ca00f583c0c40c0ba000600130404607020303000561200d203d610304002c2199240001f044060000308020046844000100080b40c1c036008040c01d0f40070000c080301c0362003232500312840382810800000100300c8034031070105140610502c201180082141420f51030102469040c00100025002c4c0034401c0d85d54101140c02d0102d080005006903501229204007d13403500481c9907035011824041081e44102070002e00116100f9034402012640541524200b40703190b9 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 414936807 1250 414935557 414935561
    0x302101b080c120106020706020f0601030803060f13240f1202010f1701060f03150303080a110702030d050c0d0203120f070c0606180b0402030f01060e010215070905010e090f0109 78
    0x90041c902c1a00c090181d0700740304100403040c500a15003500241a00c900d8440041d04010510050590a41040c0010004100401d046950000003101c01d108601440000220090107070283c03411600d162070001c0540740c000301e003100314070400c2d040d101004940d90380c1410514032060261103030342c020307110158005500a641c0340c400d807186800c00c2c40c2e2282d0704c0c0002d28140102680108005000d0301d841d0524142c1511601d0404000c1c02480c245040c11500d0207061f203540a0501e5418590b50404194041024002c4e075200d541e00070203446002c400460014800e030401e000351101801285190340c4031600000884060321707084403001c3c466944c0d5a00d0f46482e10001401582400203003801032001500700e119950150401c080584650350340d005403c0100d0300c03405150b90160b8810403d0245440b049544141103c8032868080c1c000020400101e042c029071408281c09502d040084c01a00c940104980c2d003070b5482a66001d184044080421040310b400f030f540500384a084000601c81101070b0b03 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 414938057 1250 414936807 414936811
    0x91a0f1821070f0b0f0f070509150903030d050c04030b0601020601080604110f09070309060501050f0f04050601030902091006230a0c0c0b070311010609020c0709050403030603080c0a0302101b08 85
    0x755480c0c0783e0b4800380d0b1141d0f0003641c4215680107059000400700800745800307503146900181c16190060a06082802003a1101400310030400c44040202d00000966000c0044800040300c510003030180b41420f400c8520300b030b0014001110b40c1c01900d40000e6207540b0000e0090b040303911041c02449152565160080704003902c100513078115031841655000ca4454000807809a440b03641c00080680140c01c1817002c80c1c1048c0c101030f01c0350500b00e00f4408a56079074452540c2048040340e0018498036150011b9005000c40c0f440250403d040ba02040300c2150700c401e02c84101c48150700c0b0740c801ca000d45000c0c80030740d00c004d0003e43c054400903c05020810320445c42680760740c3c4a481005882601c6d003442c0285a005580e0440000703050b2851040c01074000e0140000034110200c0c15030618805800e15511b5026900074a050a40e90b100014181442500440015500485450b54481d0200c0d6130030389890b00c4030000da000d03100d28004010810202c2c4a80040284a0f4000441e10044200216a03a00340 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 414939307 1250 414938057 414938063
    0x50402031e1e0105060a031527031806050d20030c0901021c0903080f0d062c160c021207061106090604110103091a0f182107 55
    0x2414141510070400c07109800340401140008155400c660790091003034001c242c9004440b64104070502c60591224060201500e500c00c4841ca4108a81859140100b003841500402176107002e6400700340328080c0961a404d98003c4e91048050200070404503070098040c41181c00140b03041201d0b2801001301d13404070003044082415140c07040c004c1c0040007007580042c0d030f0031312244000140b622030a6804020b003080510000b64014540815994003a04a018521001e0950040008c1c0300516003183c500321241412155420004c82e03840705414801080c2030200e200100c3c1c84003105a181c2110302740c6152041e40300000c00310300905202070031a02540121002c9030032600c03001c101d010028003400490080d00050756510f9011f052804054500400031f03000d0f004940000702844086106032940e5100c042081c200400c0c1c02e4600e103414103000ca4104142a560004802030004030004000324070b00801007100c0c403070340100b200c03c1c1c110345580102103240b080845041d28900401c50b0080a4184940 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 414940557 1250 414939307 414939313
    0x5011a090d0c030602030123150a1e0207030b0708040f20150d110703091211030d08010f080312010315110705010203040b0f0405150402031606021b06030705030a05040203 75
    0x901079032030611158483d0411520b4075004001402641c41140c007808441d89561405065054180c0c040f6910f0142c607070707599540080003d005424640038003e068141581004468803103410040c000f9103884040c0011074071174810b00d01007071403544200306990056812041c01c07e0034807079950711085101c0d605a0080c1500501e4107550800d5130764060303950311056003502140da849070150a00c1c4210359050384959040b0b9028082c0501007640b080c11141607401102d40a5041442070402c10b611248080fa2070740d15114180b030118020341d01c840d01a04845001c811801d82984402c40107499001d0790f09070840100d640c00040021079851044580c44074400c45000a5041030b403161a5500c2c4c2c89a101a18180e40020a1100b040310020301250300c5400266a241a41016501d850321240007117081a01e040048010409641d0f007488400644901400910f0206d941d440c0060b454241c105968442c00050b1b203001080d9007071441c1100d1042042e45c2e1058616903504145a008160281003640c0500c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 414941807 1250 414940557 414940579
    0x4080d091511040e061005030c030606040909080c12041203030b1215011d0c040b0a020111030901092303040b07060912031413030806130b0405010308030402011205011a09 75
    0xc030300b8814250b010340e1105519a445003400130401300c140d005000c3c103001719241e02014250f50750040c1943d130021364401000d941c9449d0782e0001100b601558000044141c0b900d02400f0410040324002c2801040120503103007001d115961302195401603228114608080b00a468000391080e44941c1041a004110609641e10249041d00d4401030641c00705907298a0fa005100c0c032000001e03174419010b481d80d8590340314500900e04070028002e41c410500101808102c80303017464000e421100e150400c04e00c880e0b0710383c900103031100e000e421090320580f61204101e42414040c2c03040310100307480c03c0010008500d000d1501c2560b810503485000156401552144480002150440c0c03901c0e03000042d42e40400c8842281c2c2494004041c068244070382c144182d2581c0e000640c200c40003640c4084100c940010800380f00f001840070b080c90f0f040d2581c4c05440d010010040050400285000754000c1c1e072100e08550380500b581d411910280218070665404107225005500001d008052040020b005c00180c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 414943057 1250 414941807 414941843
    0x114060d0c0b0a0f170c250f2301020909070f0909060f05040501080c13021b060c0309160f0e06210a11060708090402160f082104080d09 60
    0xd50007000354480003449808441e1030050340034a0307940520403031070710b201464200211404000d2095031002d070030444865044c081085c540745510711f800350300b00700e462416496614080c44000c8910800c50b15006054400a1072640d0501c01e40c0e195203000f41c407281302c0da15603100070fa52444485036200c04005685801140341c0c80c0d14000e20b40200850b01940b0f03980c1d81458108402d58805030001c0702154804154032903a0741d110400028400c036403500050380d5400705489080c3c2d5500071400c0c4111407050304180f055154103200154841d41004041d107401c0303004402c50001d1446c1610800f58520603101050011141000d021a0000720040003a1140c90002c07142c00d00130604010012496000b0102034000c1c0611034601d1107a014044610500e41a001d550304000d50060703440a41c000d55006c41e00c095000d4803503401c04402500304185903042e242c01e1400031610f511000440e40d81040c43c0c049004450310402c0054000c41d40104100d04044030358400c3c40c0103207030316034081d60a4120001c44082e0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 414944307 1250 414943057 414943079
    0x627080a030309050d140d05070e0301060f0f0f050307091109040603030f0908010509120304020307030218100b03150d06060f080703050f03090343170114060d0c 71
    0x52688a82c40100d41c0325030714101181400031601c080c0d0144110822040c180c44406c1d400c5030030858280c5400205500c1c1d0b08000c03118202c1c0c076880307039802d0b610b01000840c2200c1c011141c02c00300d5072400b07a08920079482c2c2241c480b40500d02d118a07509030307008600c1030000781400d400c12403903104030349642d42c00c1069603c001000d90f01507a10940100c1c2924161100c42039001040402400c40c0398020700150502d140102d5031080c0301d25080413a030303401002040865405110b424019034009050300c50791081d60b040d08448040c2a41c60461443e01c0040c0000c00002d00c40507a40304082184100d29940c0c101010b100c07404060b260704807015030707844101107030b909031100540c030141803132800501c411421843c03c64034002d14020601d0303c03584240703c1048075075400911108100ca611700102c161b0014040301c40e1a88041c034510302c0022070300d940f08429120800c802c4a0403580315003808001e5030710516070030303080364410100d00c5000310f003010000d846414004a0b06c25907511032051300300c2c0b1070394800d21084 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 414945557 1250 414944307 414944323
    0x702120a0213020a020118030f0c050316120815011b1b180e0708060612030c071212030b0d1b05040608030903010b1e0d060f050702070f080304062708 66
    0x5102603012801c04130141d42449034045900410074000b44044454802038840c0600020380d008120b2007440760002c0200c18416034844424110341030764828068079081d242c2c0d01d0702e92030b413a000505041c0011019441c0a140f4043c01c901a10f030303600743d400c00084842c010304803075400fa111640100b040313090380a850300c0040014045000e600101101180301203040d0b030031814825002c0c0e07000c2441400030f450302042c0d650300004120f5080c402d10161126003821400390b84807580060140385000510000f0709110340070300700d1044e0340c4609180d070210000d40c1124a001029600140d80144900c0011401c0c4549104514a41d055101d801d0392600000d0540b086ca07040440c807038101095458490409025030f0722540b1084482e10914002c0100340b240c009407520243d48941030017810071042c0051079010280c1d800c5a00d1003484140703401080696a00d40070f1150441d44030032070303100107080103012055070203646080c0e0b9651074022441c0840b085c0e06044110b01c1010a03203800c6d00245d42c10f01008050 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 414946807 1250 414945557 414945589
    0x21008040318030503041401030b030610050f09250e120a020a09021e0306040612080309060a0e072c0103032304051f03092310110702120a02 62
    0x101061500d460001c20040340c180c50201c14041a200520000d40040180c2c3e09079034014000c0b99000d04028012805070200021180e0540915010721944041140381e0509a56054400060750a942014400504000c030340d012500790031040c06e4078241403101000c001d1500780b40b912206200c083e500150002490030410419540070002410443c100012a20000d108121045041c007912000c880052544440a900031282c0000061071581caca59010f880500508900308445512500d0301501651094401d500c8500c00c50000502801c09401a20102402e43d0302501707403285400340e941c0c01001811412280701044040040031180110b02c3c3d140210b010703940e1840a03502c01c420a00f40d48021100510704200c0801c0203000c01d1322405441414212000c00c0051003020403c0220010548100000e1a1030760200140030203003240d1440000b603070b004409403031555a64a50041c115440079402c00140070050214030090314280154141000c614416030302554950b034001206000354074118 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 414948057 1250 414946807 414946817
    0x7090608010608070b0421060504031d040605031c21200306150304151a041d0c04050403120f06090501090b09190207050316060b010503161404030210 66
    0x400a44009000742e4006141c0d400240c003070942400411461752041e0700a6004150050a5040c0340480c0d440080520f241c20a41c10040c5060500d002810520011511180e4100c03442c6208002d01d410700c900e00483d80005c0c0201060300c51050320144000075800440705120703210001c0185204241d07502070300c001000b40c0018200c407091882400c1884810340100341ca040900c100030158484071040a00c099101802d551266240d10b05542c20401c0642c01d07540e05800c140d2504114420848440c1601d6012103080c089584a996039403111400d04030100c14661083d480c040d0790b8141079000e9034100d8064038000c10680f007918070460586122800b0005055601d4004000c107020311300c07680f40906064042401901d080000191003490302800b6488011002907000c14a40c2c503650448040b0b036400303c00d82ea159200d040e207030184801a000280c820908003100e524141d0320030740450f8410020034a00b1010480e20403001c840400341d904041c0d00706c0000700804001741e45c1342c401c00c400d11515030b520 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 414949307 1250 414948057 414948059
    0xd0507090e040b0705031008030c07050a1a030f040f0507080703060f050c0702150d0c03020306121c1b08030a05150306012909040504050f01050c16110f03070906 71
    0x500d6038105074404400509218280b0001840e202c240039042511403508907281e031580c210030742c0c907400d2036400900ea5100002e203d040f0b01402144080440e20304540c180e0605984416034521084e9030384690030852010000104507410150000d900302d405081ca0382600b0280e540c0300da190034015000422164402c4004008000c0ba40c00740c100a81c60070a41801642400e0840140900524100a02c0740c5204d4052079000000c80050300c080c01100c43c1c0a00c03a102c00c0d980050008e51003038560f00e006104104000c403068100041d001c0d41d04074141c0d14402403c04004c021514800d40d074540c110900341c450b258001140d900d40185000d026240740c00500e174200314001d082c40d5411030b004980a43c20001c0100101e1820524101811180310f00d80308107000b803500420524803644006652051511040c002070210001d42d110303084c2900c00081000d82c4030388280461030300803900491140081107003880d000a0300c408640e6280203001c0d25030b048507042000002d080c142e0310b0b00150102c940e5290 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 414950557 1250 414949307 414949321
    0x180306130501050603160632040f09051506031305011e0e0705010206012607120210020a08180f09040803071403011a031b0a0309021e0a0e09010e030d05 67
    0x11500384c1194040700141100421188181002c2c03559202d1f04042c446408012550f081c5041c0580440c8000e803240407400b1001800368494607001405100c00c0941403280106d201c2000d4400d007402003c1ca442c898141c245400c0c00c214150344010514401c0402d0ba15826000035424000d17220241048054406690701c111280030844428043c4142550300c203207420005c598000c0390480c1540c00d200111000000c02c0014902d00602c00441500140b28607840042d0005001d050791b0700342c507c219030f20704809124010407a5100c2c2c0040d0040c00c8110104510460b900f0302e00002d00510034082d10341c0041c401810001051003030b08480c1515510000001c101c0400c0c0c1c0300c0f15415207034100d0128030742154189450740440703241c655040e9102e1440000030490b16880f103000b942d50203890503007040e501c20742d10000801500000c41c0403030150515a5000400d62418040d01403884405440d140d080c6d440e0603000d100c0c02c48040c1c0145032075562201c080c1410b640030b100502580081c20f02c08034240c1000c603 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 414951807 1250 414950557 414950561
    0x50603070810023408030a06050d050f06310201170f0603070b2503180801062310030510052805040b0102030d050907180c090902090f010302180306130501 68
    0x2184401207a0318408800d0783d002c06004c1c00050782900044055260340e190300040004041c2c6400c82680400707001c6950040260005c0c54180d03400010096481540304c1c4401d501c10080d103900c40d001c0021010900903000c584901c02d500038580145081c544070380030045101600c00d816181030146a944508001c030a040400c035450003000d19025007880c0420482104016040f40124074207840c030f14440103000e1502c1100070400e034a98003031007009016901c03410349000300301d10f114851309907603070a411650340520a05084d040d0b0001a0030180099072426045004240c010010000c01d040210301203131a8a682d115201288000d4018091062024484100e040c5182d8000c1e44100d0600f510401581d130701009035103844e9209000031449840c0c4600706400c1c88040d401a101840540781d89071014072482c1c1003501030800648a0829864035440c8030f5059100e8118500d8020009400300b030f0855101358001c03c2441c200e4040100d030b0a440d0000030b0b0600c1c0069648940b80b09400381c0b01802c1c0320081c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 414953057 1250 414951807 414951847
    0x100b030c071709030d05090315090a0302010608071503020d0615030204030b1b0403080c1513021e031e030f0a02060402010807110706050d4208060a05060307081002 72
    0x46030807401c01c078403c0002a596000000070804011000c07500824540b010040103900b00819440c1c0005460a04074866903124082c0040d8015828203000142c1e0000c00b0030600141d415540b03030340745010400d090640c0603501c00710485500555644000840400d501c0880388905510750300540c0e52465420500c071030000203420b0754a05816440d00c40013001c8818111022607034400301041e15190500242400c01813240c030000d0114100004000041d10b038210f40c0f0300f010744210746c00007540d07070f02d0001c0200f4810444042034041e4841c0800040000244030038101f095505030440749040800c0d50642800e42004160402580c085005c1c4006c40d0713003012407603600540d00c0c5040002424500d4030a66500c41d140310b00d0003400000203903560710409035000315540b60003c4541c0e01142c400d40449042440f01025840400c8942110010380030824064030000c8800c401c0c010301d050b880362082032006141c0a400c0590500c44d84e10005170700c3e00180032115414055580040c0c4540d0b812074205261104 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 414954307 1250 414953057 414953093
    0x504080c120d061706130c0b03010e161d09130f141203040c031101050708031003020a0626091e150c07031209031101021c0b0307050a0608100b030c07 66
    0x4a00045007130f05500054460384280a6000c3c400c110f56542404505024903800684600c6000000800d1400c05011802e02950991001040380c183c00d902c00c49102c0c4424000002d110054090400b60789807010300250010b9070030368540d0b460406a562045c7d00e0640d504211000038a145040101401c14007100c0c42030544003250030715501c1c00c1e0382c40c00800b80312800024107500001601c07031280d910603415108820713841440b00f61380b03050000500450400c1d5210492042500d8400800d40911500c07942140c01c00140000003041d0080c0000f140c0d440300207040c3d880c203200e90890403111400803910f8060b0f01c4000e0010341610039400b416005200c1d401450054003120411600b80000c1c0c0c083e156061a040d100b000242403c40303840c00b150009200c004000540d07001246441c5551a05540c0d00c00e114007032401004590703030316000e050311484903203d629400103041d08200701141c042c0030450b0b031200c1001120301800e40c40c1c220203d65604151030000c8418008900a4104128000100711102c2 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 414955557 1250 414954307 414954329
    0x406080102072a150507051e03120c0a0c08070203010902060a1e0203090a030b090106080706120f0e0721060507030c1101050f16020c030f060f012103030504080c120d06 74
    0x400d100030840b400799130200c2c210822800007244c205014080c03144900640200d2400c0300000b445100d180d560340c00c40150f0f8041e0126179000305841c000307024112101249980c8070b54000b80309507100c0d003074103401c5094203981654941c0325440060f644c910050810142d01d0301c0302c8000d41042c030400d0714400001d815150955000b0014043c0740d85d00d00039600122a4003617280c881c0c607542c601440c0c2c007600341640050382910400b60040380c0700d90000d07188440002c8060041180c2c4500c0401503003a180d4840f102d5000e03030001102030100c041c20b402020540300c500c090880340100c0d1030340c85200304c9008407600400241d41d82c08003150386070301c01c2000010a541d00d00034029810840c1c80c061251401400740740041c440b0002c0c00d65141d000340034003000204000c4c19203012455001041e500d600040341c0d190188400c8400100b10042d04100800d80c41c008200f8040d02050341e950150010302e00903201761317082c1c5400d0251704012001045a0800342c141c07540626154480404054181c1d40e054100a040312 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 414956807 1250 414955557 414955559
    0x30e0601082107110d03020607020d1b030c051f150503063102031c020d0c08070b0c120702010e16080a0219030c080d021606021b0406080102072a 64
    0x142e4a480c0325803402d0000d952669480340b061421410005030498983e80056004440000b85074000c192544644440d0f001d417800021101022201d541118404001002280000e000400c2c03055200c030782402c2c400c208403950004461310b40c80644c804400c215540c40d444852420391245210000700051400390001c10117030608079040814403524624116002020480320b4504001d03e8884100c42d0741c014041e500c501c800e100c202d104041001c500d2101510440400040300b44c0305821307a2181d107421440c0340d82403000540c1d4003130b0030320300140c083c54640d01c040c0030607910f8404801a0500034440350f000000c0d11100440140e0420381c20040204004038114410405407402003251075805904031b80411030400c3d0341d034103c5122001038001030034440e00d0042c041600d400c0000c00128102c0a80c00311001c42445240c450440b0895024050050300020014100002c485212002c4a4001031011a001d619094501d003241c00003001a00c1d940302c100e0030f05009903c900141032a0001340780c00d514506d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 414958057 1250 414956807 414956833
    0x504051305091f02120106080f0408090409080a0f1d0f0d080d05130327050d02030c030321150d1b12030e030607020c030601060e0a15030e060108 64
    0x3a0298210a010300e501e800c000307080d02a040c08001e8000c45001c082504104580301c0310300c001d40100d444000f484041d000040b410900840d00d0380d01ca01e401d0700070b1410503903581e95030170280d030851035135590007903141c03143d85002035007000241c14404030b596210b00031110551b10040c0b0a8001c8a2014070248000301024240e8450b240f2056410100b07a501c1c01d082001c607e4201c41c1d500c03844072502031991030002401542920b1810101501d0300940c0d0b0110b4203a0000802e064808202c0444103240072404410030580c00c083c034442d402140020300b80d80301d14403100e01203403c5038080b22602d080e004901c1510b8154020008423740c02c00303c0c2c24003150021a089012400e6007110110103881c00c01e41e400400d003015102c0c801074014141e0501c07002003034826480c004d4440c1d240004410b2080c080c40000078805807002075003840041c6c0040013062147d28080703050380d1012020b40920b8000319110780100e41401041c03035005505080b650000303125201a0809810000306800c100c4194010148004003 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 414959307 1250 414958057 414958069
    0x42406080705040b01020304030c090506010f0f1d1f080604060b0f0a030213030c03062a080106121d0606040c230d0e0604050f100903050d0504032a1101050405 70
    0x40c2c075410b803400207004542e070f03006038514007c540c80201a5004081c000c103403800c0c540c000601900782038903603010221000314103a0314800306a030701a0000701d100822407016591007445a081c402c4c00341481141e100c112900c03d404540c51114640410604002c0c0308040c2014407030349004151050b2880d003070081903143d01c102403046200c04002c0640110f0711145105a1501304c1d40110391000d041150103503640f4060b00074020000d00c40d40894052007003500d61042c82d1001d035919842513901c40c2c00503820402c042d07861007404501c200d120366480141ea200400382852036506603003172a0003449a45440000c00081c0c0e5204800d0034100400d04c0301440c81c01c1210140202040c3c030b8001c1241e11040740e640030700d00410b8182c0b0308200c42d00c034580600c000e020f404544002d00108080030303500501c10382c0317807010151004008018009141000f10a01030f500c5607121680041c840d1401c2e0300e1414245101c0b840f12011109c044084c6150f06c60401c5c1001183c1c2d00750101c0034003c0c2042400c05183c5400148 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 414960557 1250 414959307 414959309
    0x1b1b12121407051c0509130e210d0f0b120f06090304080601090b01140403060203040c0509070504180204090c0203040906091404030c111e03060c0403080702060d090b0424060807 78
    0x30610359030000113280c5000f01e081d20b40c280d0001d000c404005408490328005040340480010344d5024111041c150003008071a40c1c142c4402d1102007510780b07195030341041c2c010a40c2c50b0440c3d003a9035681070500515558401d00d189941c061500600500d1001100641080741c064040b0106074020803081154841c0843c1c91411680f421500151082414005a80c800f407070025100041100250200c1041281e90155000302c1c000d032020500c21b074461080c440c001209403601408a1000d000412500110300f8055803040c00e03405004d0b05265540b10f48d0016500380031101400750b080803406004c200510300c0340900505007040e051207040068001c0c105103a1010740050304100b0020350100a101c00100c207801d1891000d45180c10445a80c52440c180d084040c0e0040d100703020b2100030903c05003088007a1020b5a40196070030346850051b80c204100c56000c6000d0780c92140c0c44201040106010300c010303601c610b00032080303d14501f8205880300c0850b17000d8080c04130820700d0840144082c0780c00181c2c4030 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 414961807 1250 414960557 414960583
    0xc1d130501080c01030e0d0e010f050f0a050c0606040603020922060203090319050a09030f05150705041a03010b09011812060b010e01080405070e0c0d060f0e071b1b1212140705 77
    0x2406c407448ad82000c441610500e100361007070080c0069420f0306c55920000402c87c40d10804107903580c5403194020441520748620004e0343c84050315004c90110036a2501c40090820402119440403001d50b854200340d82088a050800760000f00c0d00e1300d048103285203080c0c50807003507240003850120024000750000180780409000d85036044c00042c204002001060812110050403124920b040807000308242d00c00c0c01440c00440505040359124844032090300d050311040420141000407a03001141d2402c94284074030129808803c0014540131204105d000c4540200004584031131000005030010484006043c10000b9060801009c80c40c0403ca440649800b00352000c00c43c1c1350443e070007909005c0d46009090381840d0090003e8040c59480845084030034800c0c00c881c141d40c9000d01514100003440c64102541080a50b0000080308045008201241119421a45501d821061503680c929000c2150f1003815a080501c0403500815604038403411820741c0c601e004229075803d5252051101c40c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 414963057 1250 414961807 414961817
    0x40312030b0f041b0e030a05030d050907030c06020c0f09041515260105070810150507081b0709020c0a020f03150c0a030605040c1d130501080c01030e0d0e01 69
    0x35840d90781c0040e800c08507034003c2007030019a8404540c1078980f441d4442ca440400c140c44e80c1c007200ea08020450844e83c0f5040006907080003078000c4548040c050081c1918040e001c0c44402100268246880b60040e20041d4000d010103032111081c085200d065210b03c0e03125074100020080050245400e14074400500c2c040440c03480c40f1031908107211400d0b5000400d14000c501402c03154207d44406521518400300024002c584411109848000c2c050344c180c04c610000d19000d101c2041c0c84c16514941c1c3d2b2440c60001c0c50708400da01c1c1e070b02a07900800d03030900840b65010318404403032a0400489000e450760745421840e06400d50507046d51101c1c900390003030140c00b2004040d103d9a4041c881e0091800c00031600303820910709143e8007211035000c0044a404a454000702062a09040c8503121040c1401d4442201030301a807031f0b01e4003d000c02c450185138000820b142d1100f01003e0341c011a0300801f1844001d0400e002960f0000d0107071072580c805242941c1c00165082141e03a400740815040c48828242 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 414964307 1250 414963057 414963071
    0xa02190e040603080c2a0f01080c0c0706050d0b0901050102031b030f07030f090e060a0302040504060b04090318121703060105280306060c05070b0c0f0703120305070504031203 77
    0x708002e0552076001804200001c00c02c1e040e90000483d001c110300c0310307071181091074800030120242925030b8200107540100c01002001d90950050300010380040c1070048941c01e111501010328981101904003170700080c0301142d200e0100c0c0c12801603884440c01160b8060b0300d5818040002d42e0303030007445140c6070900d0030041c02d80078124081c021100c030000d031040410341c0d56040381405800f49082003540000204003180010300d0642c41c1c0c0c00c507402114018035609066186400f04409003070302070000e417102170342d440d110011aa81c6218003405c041c4203440b402d8501c42820341c8240c810304641e001400c1c039a62410030100050498010041110078014116103903160310004a405001e0002d116108464860350303885150b401c2e04171490440d00f0b0b43d40c1481b086480b200219103d080021006005902a203002d04c410418034010b090421304100c2200c40120b44842070030718101855000303072100d41c1000a0761090f16454011950701450030300300140b600b032a541d1b41072186200c1d0700f00c09007007541c3c0f044 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 414965557 1250 414964307 414964309
    0x1b0831060203040501090201180e0a0c0e10020604140d020a082d180a05060d1a0604090f05151309030903061d060106081509060d020303210a02190e 65
    0x54001451600036900315202d10301413400c18004d05801c101640810214070b5407001030340c03206400d0010f039004070341d0000031521480c40c00d0303000d800e0718132410040c04501c2c2d0f0b2044894803084d044950a0320160b00822590a007802c212404400600c0c041e86250061107003031160340d40014507004000d80c0014842d5491000c0301720381030078041c2d5141d18010711007890704090302d16103100040e040c2c0c400c022507148140500c003420481c0d8850f5512030984c001900f4012881240030a5000310860500c0f0700038085111a4400020803030b40c02074008240d41c5542e20200300c0001010300c10700d03601025100f0700902580288000503607400051541c039083c15111107165040601c5900e40e90002c5074400410700400d00039400002d01010200a8031800d480748000000f10b1130b1060251a01500a10440d440060910f1003400034802c8001d00481d0019584044140180c40410041481c14401181003c400100200c642a82e0001400080360f17103005114001e402c0030001c1510300100010f0605044d034010f180 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 414966807 1250 414965557 414965641
    0x30e190e0907080708061801050708010b0c0106260708010c020309130608061602060a09080415050705030d020720131e090b07030f1112130c091b08 65
    0x1410143d218014030400042c0480c00140c440d000d04820b0b0501002c03459443c1c203d908890b0111020800a1910303401040220245030061001c080400000f041258031840c4820342e01075050400703207009240e00313464120000140241c8000e00101002440340b0400030703074002e680c0d0068041540c42002d0390203000b840d20503250700000003003803204240d45641c0b0704184820003c02030140d428015005040010b8002c01070f912402d980d256000d030400c2d003094100600c00001c0d0000c40508400d2100820850300450002c0029100d030300311015000d07035586480d1411844404100003a240c09590401d01d00020359501e01181d2185440d4400014a03210340440c140000041c1d002504841d501d071040250a00156030086841369031540c8050100c01038084080c421200c0303044619001030030078443ca0802005d4006016007061018180855141c07440d10380c001000745643c400801c00e0303a00c071607603180c1da02196807020b81442142440541d620741285021115034185402c446100880304402d80c040c0540 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 414968057 1250 414966807 414966809
    0x30f0709080d0f030515150f0708181f020a200904030909051006020a08030903040e0c07060b1008040f15060603060801050105061e13050d0f030e190e0907 68
    0x181160b031042e215003409040c203000c2c110b1000000c0d003400000b44800050b280e2901d0800d01c068240e86039007620008201042d000140340f41582d0104001c500b012402d100080d00c14415420408240c02180400300031010140240122801000c0001041c11907004608225002d421480c01c200f401a0400d0881e05500c40c02c5025502202550502c82895800104013055a06040d820441900c407482d81c501640c0c200d00c41c200040e880203400c10001b40d0700102458000c0040002ca0342403545899030005404030032268000345141c042806000c0c0030550042004040050b148010a40b20542d4010f184040081005e0310380d04c0b00010003001c02c214bc40000100196409080140f90703245d0743c00601400300c40c40303400b501e582070500201d850328044084130043c40f0b101c2c103500ca802900265550041d00840780302180031031201302c006a503441d0305d80c00311201c0348614082007181d182031902a20000314420902c0c0a182c0405480c4000c030f0b0000c00c24070668404e078121040c0b95076900e408034a04089 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 414969307 1250 414968057 414968069
    0x1e0c080403021e100c0e0a080601050a030f0c0807120309050108010315050910020c071403151801020d020706020403062009061e0c0a05071a0a031107020904120e03060903030f0709 79
    0x60405c10141d40c0303902450340700d1050000c407034200c2415a10241281d4818003801a1980030f49081400c000081416244c8ac0c240d0344a001c03006845079641051604002e030035070000c0f10707440c01820300f501016440b08409c401350409082090265041d44c4810200d009145c0034807510550354008038036441002c000c8038480300c01224056580340c190a08440d2196024480e211044081d081e61420781c0c40c1c04101c990362400400000b034942d80d00c901c60304a04050400b40301240d55420401b028510b84540004e0085a00800b0051313031340c0d0729519002c8100c9580000b040704d540b42c8a048070301070f020300000711042d58200311500ca840310041261009050f02010034240221400100180d000d1804200c50300071900403c15a03075490398ac1d01003500c0003144240e2240b8030045c00c00c5414103a60007030380044c0307481d0f24002940d401c11143e079002c1b84584100351416242503403070856007030301940c1c000c6004d1403a0105030b01910090615440d6180c0e64000035040041400700c02d80002c003858807884880b801000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 414970557 1250 414969307 414969311
    0x316020103020d206903160516030e0a0f09050103060c050f0306040510033f080118090f0305090315010324020c011e0c080403021e10 59
    0x280c9080601e0380e0340984144070310b0070001c2d41120980640d00107050200000c0051400126213030130380600c18504d0b5880480d0402090880126451640c85c10907282c030034410003d9580e0381060b0980c0a0b8030780800d90b0107001c12000300223400c450320310510450b00c01035040c00d0103120080b41c10005044003000c0d40005580022902000503513402c079070060360480e80100410406d03440d042d401101e0701c0c481d4185110703108404001180701d904081d40650b5120007254026400d4948079503da0910221900e642c40401040303696404100700841010715849041d411851890a800e10010b4074408052294180072091180b8506a0341c1302a000721100c1c6034450100284c440d040e15002c0c4c456040300d442d0034060b20500c460038011501610314581a83e821465015001c14500482c0e41c20000b40d13800d000c885502807000b206014024025a48400218402c0e500d0b80c60707823031442e9400c64078040c0d004020042e1800901c00405d80104001480c01304103540c07141010704402880b80b81c0181da10070f03c49014 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 414971807 1250 414970557 414970601
    0x61d0c19090227010203090a0b0d0923060f01050d15060f06021006051c08160503180118060f050c070b130e0f060112090201021005070c030801080316020103020d 71
    0x3414802d608011800710072889041c00f09401240d40e801052031413500440455002d0007000354a002800d0342c4818007802144180c0540d44954990780b0000c02e0b20710145007240d07213404c4071400f8001c003a0320694444d0b61444543c540b000049030107920b00c8010782840b41280e041d01441c1c210350085005082d802c285030704160350300c0c0b80003541ca21075407000f400c07118608400401c0910b001303101c01e403040b1640101d0a0085200e03407a1140c8076403041840503010340c2e1b00c5592400041044c0094111040c140090510588407800050031041d040b0703180d80c00d40e110150041c04000d4001c8800d42c848045890b245840b050f02d600381341e01d04280b0b50051180700901146051403070340c01000203c1901d9039080d5000560b00c078104110800170301a0b0303085010800d84140900d00304400d034000e940e4a40148101c0e21040000740b0784c401103440c207440e1080040d40b2174610b4800d140d00b040300c05005082540c011480c02070f540095101140d010b050080c10150005480c2c4407030322564000346882a01a45d00304510 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 414973057 1250 414971807 414971827
    0x906121903031d06010e0901061505161718030a02030303040609030504090f0b010311181302090d05060406050c16020609150d0507030f02040602030d020c120c0307061d0c190902 78
    0x213400240314404031010600009081c0c0081030050804844002a20041d03440c840c9a007910710303400c4900c291400d10a05015800030501c005006e10031080100c0c1c18641d1000810120502d164245412501a03848543c2c01401a1400000c0b2b951080e080040010b04400740e11307080300c1e14031030396104107140c078241450441103401079405101418000d80341001109034041150741c10340100e540400f0709034842580255a82412042c01c0740b031b140b106800518010300480064071521441d00150348540c000c104000802905100d059001501e4440c19805c01c00409110401d04c1400ea000a0007103002054190315034640240c241000612200003a031a10030781480d2000912044910f0000a8100154411007404920844041e6545076001d0341c580320a210b28140a5803144107050040d10804070f90b8140b04280201800c3c8910440e4061507440701e0600303205050f524020310705071000d01060720100d18580000341083d0340c0e4000750782c4048c2c0309480e000400030046030340d40f29441c400d000045017101 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 414974307 1250 414973057 414973063
    0x70b090106050a0e01060c060b060c0f03040305071a030a02070f0b09010b132c030f0301030b0f09070b03010501030f060e150307090b0f0d08070203030403060504020906121903031d 79
    0x1d60b101502c1443e8100e03541c071540c20b40399400784105d03004039031800011808503825402444010101401c40f5140c25107610507145052120340d4540c820f6040410103004001d000d00030032000b408500c440c00100c0000070243c00603440701600d41c5900316400980c00c000c01c03004209054411b41c01c41c01d9080c007440c4c0b8005941c00790074042c244502c07403103407035400c585580424400d505d0f8040c035a40340160081701100501c040d0b0040300044040b80d100512017044007506c00b43c000d6001c2e5200d0000c1d085d4a0800b0b688030381690a01a0222019411a203010301c00c1c107034014242c1341103c000b4a07011420b1000704103540f000300f076690801707203c4000c0d01d410010f00c16030400720340382c00080070b800302d800503030307403044682c0c12100c000b800306a0009290000d0800c510f40104261442400742440354503001ea16400689990700550007101d415494108000540c0380c40003201d64008000e54231b4500c902e03121401a80c4910348050002e45d00c6c4c45952681003030511070390003400c81030120b49030409504a40029255 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 414975557 1250 414974307 414974309
    0x70f050a121b17090c0d05030c0a05071802070f02060d02070203070906080c04060e04030c05071508010302120d090303031a040f05090705100f20012a021603020411070b090106 77
    0x1140d080f01074070b2860100002d0040c072602043c0083c0c03240e072184108200c400b85000c5002d580c14881071100f844403403414003040c030342e0034401d4008042e42c03031800c000c800c0d00e8082846400303d514130500054003c5840c040b0140c0c1403aa0403038500b035552a030181080c2c001d014010000e034040c82050b00100311085203500aa080d00e940004030740d0500d000404100c25205540105202182d0030700205001a0081d4092805035100d03105640100b6110a890b0090044a81e064000200204010415410300008420b5040c606501404c2182a2141c000d45851801e1000408040d80c4d6180c0c40c0030140c00b00004041107000400c240003101c8210040c502508080da500e80c05405987c6001a842c544082c85400a16180d1604440115000016542c90003801c0501c910102e040c480007031a15070030702c0b5a0500c242c08034a024007082c1c051008000c0c58604d00300b0013040d5400300f850410a844500100c0c000c80b541140c0108011007541c000c00990700500600506c2c0221a1050040b04001074000030 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 414976807 1250 414975557 414975611
    0x20010c08100f0302130e0316030f090e161d03070303080421020a08030a02091023180d08040515040e0601050304030f081003020909071d070f050a12 65
    0x910740c90702d41859034404074061100951100d200c1c107450000b0308013a0000e002180b40442134900f01010402440c3c07458100b8413040300010015022203190f1030701703e074908028280307400c4000380c2c500e80700700c1032490429451314142c107000d071403915903150900f4070005c5018840050240c0c0c1d100350343d901d405064850309540c2150000d0b016140c0c40e000d119210941c1d13403020f8296004100d5010395884e1f980e0346501c06407641d04034039020800d284194039403160840800089686401e803050707407803400900c050b1006403408070020040086030407080780702a01c03039041c110444428504020501c2e00c0c0c055403059900c4180c00800042d424032200d2981c202074011101180e1182010f660744a00458851008450060121304105820200e462140141c613510841e040e0345404125100d400040c41860700700d9420041c0c0d82300752801c0c40340512900c950307a814040a03e10751210b00302031001034182008000410104a400306025424034400e681001e00c0c03842c026010081400d98410004500d18080c0c074035 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 414978057 1250 414976807 414976831
    0xc0c030c060b0312041d180c01080c09151c090309170a050f0a0515040803010306050606070b010305030a0f080103122105040503070b060d0b1605040b190e120d20010c08 74
    0x42c1000100743c01f000e503241c0b10b01c0083e0100343c0f000d10042d40e0502014144181c42201130041c0741d21511240e07124000f8130a030300c1103a915842c40781103c05181c800d030071544001c503040c0416900040d411000010550b12079805808031030519030142d80c541010150080c02034410380390825034584000c903103048228011000c0e1801702401e0848551000300c291001080381400b00010170204441340c0c03005400c520300500d081e06d8100251120a030b9100203070429505038100051032821903401c0340b4030780d4407010141080c81a940c034640f00c04441089000c42c51060115004030b0180e00e0f600c210381c1020841000500b0030841c200340c24010303502d802c251400c80310509080d01042e0946050001d6490459104003800302d151f8a800d0140e54200031120000705000f024040880c3c00d00c450405403511307840380c056801482050304401000c2c4a0241c86a41c010300e81604400100600440c001e03501c0b00301da0a11240fa408007803010380341e5919800502ca81c65290041303420055070b12103022030241403c9a0340c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 414979307 1250 414978057 414978061
    0x4080a030e1b121b0d020103020403060f0c09082b0507020d03080a0c090b031609080d11060c120c070515070f0914031005060609091008010c0c030c060b0312041d 71
    0x114039600c0c5000c0f400d00b04c130320240640ca00070030315004039100001403040c0b60150a040d50b0795140310950708100030030304d841a00c510101414550050880f0000d10440d03004015900c0700e6228000301c400001c102c4d070000c2c03862203981d9040da17020708110b48100b64041c0ca03e008170091818002c11060044c1e4801440781e0505070104113041c40780d1100002c1d00d151080300e074a151241b680c00b64401c03c03506500010b00c5070130070000404007001e114100340307020584c450800041c00280198106500100729030b8640c0c00c00d1062040e82070342d0560440c0c2c4030b00c5580010741d9400d010300b40103242c5111003515503401c02c0103404110f1103075030060180340c08074541d0b225120250b459201e0112080411015140c256101442c060040e2081d604503c0d004840038103554501592600840d100c0302045500c120190881a82000441401d00c50084a4012440c0040e0b4880c91594014050101502c002d03010548035259082c1d0b0b40d4050040780c04d0620040051070356a40c1c5c1c3e0810500f07003104680c2c0d50303940040000c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 414980557 1250 414979307 414979339
    0x222060806030d08070c051f0e010609050412050309030910030b0102101b05180303160506010e0f0408070303020c0604050c1008090d0f020a0f03080411061204080a030e1b 75
    0x183c50780300c070690350b2550081969040d07812074808400303200c1a01d583c450043c880c0e143c420641c0c20303000d080319072358030104842c911813a4680c04c0d2051030b406981920310303000801c004910508600c1450010364900642d607900da90340e040d4a1401443c8500d607018500d000100c2e0100d401d40c2c49180803150030b030255004803906d02421811244064040c100f15519006490720080c0700d14002d100c8084c0c03041000b4421005840400d2460304854089c40840a4200c00c150030300c00200040ea004010342e0070b041c040c510f4000400c080d243d102820050082202140c5201014002d8065038002d0f4a04411503a4515050400b140e65410542401d4000c5902d00d042c083c001c0d2143c9050f5110380c94000092503801c10320700e01284c0d2721448054150440c002d031104034000802c556049c414140c003a41c0d42c1e050605141c20946100d0002100491203050b007044020888803000103c1540b158000340e80326120700042d14181e01070300b0344545101444c0182c07000c955a44d608030100002014043e10341c1003212003c80 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 414981807 1250 414980557 414980563
    0xa050d210209010c0201030209040f2c0708070506071a0a0603110307051804020409080a030204060e0405130b041b0905011d06030a1106040308271c080d022206080603 73
    0x22000b64002881c8503024800f65000f50010101050050030000380c1100988a1030211040e0400002e0214040801c000c0c620608044841109060401414200d8a480102591002c0303d11859009440116041e07060013a10200950f40d551001400e440c0d6180c1081e0802c000c000d940000c443c2c241e1100480311060030002644000c5e960040d0100014103025000a1042600100126401525042200b0008801c0c0e00a01001d1502d1f8a0143c1c545082250140c00d00010401c0c150007145030408011041a0002c41104460b411450a0702035440320309140d495080c507208001c1380b03546140d20016000b460359102c5412909801d0034154040c0d802080781042d90010351781d25925071700900280000c40d040b12060b5101c01d2008107140d2410341d50340c1e01c40c40c0d039805c0306c904900090428801c051a900c000548210b03040f0045500c403600342d03101440c41d640d40581d400e010744151740104110071441900d034103c44880401c1400385211500030100942d030b0400c01d0282030002400240451a01d041c00 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 414983057 1250 414981807 414981817
    0x313060807140c100b0409020a030b0f0601020c012f01051609090501030b04022707050c1b0a060e010504090e01090c06050909130305120901050105010e010c050c040e0a050d2102 78
    0x1d0000703481c80c4e070b0441d501440604401d0320b034294465601e04000340180d0303c10a880008510074400703c10f5a10f450591000c1c000c000505803815900b04206412840c2e90182c4540040c0300c2d5420300c0840d440500501031010105021703100d0b090b40c0781005004440444120480282c0100d586484031641c403401240141c1320280720080c480301c401000b0400520309403071107012400071175642c94004108550885213491058881d000410380c0015580d140f0310090084030301c001100d02050b002a01c450300403170f4000e0384910848081010022601c04540c0c840d0048500800380204140240380c0324a19290027801032040407035a188041c2c100080c00f500038815600302040050040d405507960507060102c003c5000e404404009003007040791424082c41c0c02c8540500c400f0400095a5070415002608090011500c036061054040e5140c1c001030380000c0c80d19004000b66400b058620341922810310300f0390900c50080c1140900524004240c4d482130032201c500c1c2d81010402c0140703140100d150708a10403 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 414984307 1250 414983057 414983077
    0x15041a030f12071e0f06061706060112050702070506040f0e0f2202060d020c0d020f2a1807030f06090b030c090408040b040f090f050f130302031306080714 68
    0x400e11482d000b0800801360740750701d80e50310015080a01800e64032241503070340e80e00040351010b9503101c0034440c2000704101c58400f060200020301c82420107000291480320a030440800080c2c4510000701d150307100303001c00f10003028042c04080d12240ca030120003030303070550074060b81d440c00c000c090010714042e1508280d1400703406091500100c0000549080d00b90702034901081c1d0b00302030108540721400d52144010014581590040c04640d05800c5009040488a50007400160301081301e40c511070049200f40b244040740302d5040b2056034030150109042114400250740c003601d440c03040045e00c94041c0c208a211031082d2501b048560345031142e9a04a44420b0540380e019405561241c039142001c4454030b4100c0c1c0076000c214103043c0c0c0c0b4032248580754403035081009260000b42003007000c201a40503040d0703400040306080c400380c030780148800c1910070028500c81a40f4046040036017414002c1c400c4038011003a072500b0010841d1502c00190180e007068640e0b00024403400b0f0319144243c914020b460207119 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 414985557 1250 414984307 414984343
    0x20c120604120804110a03030c03030f0218090a0f0509030d050f040b0a05091c09090f021608030c07060c0e0306070207030302120702010e04060303020601030b100803090915041a030f 80
    0x8040e0841d00d4100c02841164175143c2c00d00c2c0310185075a0002d51000441c400d54a040d001e091074078008099034007643e41009881e0045c0920305840489080c074407100502940c24100569800c030a1101030440d00d02c001000e9407514083c0300b50880c0c0480100920000380000f03000b144c8508241821181080707801500e280c0c2c0c03440200e60702d0001508066001100c0320100d8100c0c010100c0c21151510160b640075020400c0034004103c01c03601400341040b602d10076041107040800100c005807003030066010007440d146000001801d0200400107807024240c01103c00c1040611418000e0000519200f03154070038451880041c0314148009940c40503258958050102d0001803138014000e178010b00c80490502021103800c10540d102c03445000020f5000c2d900900803540f56003031140e520280030302000e131011092141404071410000c01c491483d40c2c25500c0342110f40d241e5a1807040d07072625455103540300707090103071410203810b641d40800c3c2d050b0000c80039200410300c5841c031541d03101030305c03450849000c1c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 414986807 1250 414985557 414985583
    0x114193506180c030d09060e040b0607060207080f03010308040f0e040f0314070501111e16030c0309083c060118022a10060b0319020408030a020c120604 67
    0x40050080c5a10440c0c010103c80700c00b9100e10002e818000840d41100000307480500800005601402c52010460241d8040041d08010808161144101c80d8060640e41d0001140c1c0200020482190a400078044101c0c0e217030750310ba1912045075801846401c1d051051200013250703131201d1030801c0740100ea00503c000004446540c007a140c0d01c014a00090100d8230a0000030302003102030280e8021545d07100d02c002c7e0b43c0e084a4400b2000000d00c010f910304910018000600c001902c040c600f01c54075003600780f5024540702e0303240c11116001c40350030601c0b40d400303100400d1901c0c1c0200107041c0d8101e1141b860b05070b80f00c1d0a8042112118003c1920711903940d11010040011100e5602da03402102c01100002d882e04030b101503442038078580044000c02c81c2e01c2c09045810425428480907440c004585028040b080c64880d4a0856000141031602c610b510b1042108001c20b4030350465004005083c16030391504032640000c1c2d01da8900f102554080d21440e80c4101d60300c0008a6180d00c101da0103c0c011600b1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 414988057 1250 414986807 414986821
    0x30106080402041a0607030207031b15050309030d06080105090d1b02010e1203031e07090311060d0e010e030904110a0504030f051603150c170114193506 67
    0x10300813165401d07107040c040c406284602d842c2c41008010700f5010ba00100141469860000800141981400e04038000b41d03e040c0160780301c000014240c40594603025840b515034080150461107055000c1000610782007000614880c1904000c0c8200070316401c0d40c9012141d9a815075250054210b284014030303226004c04010f601a000c100c080e041c014280c840c03a20103d0058629692041e95240c640d11099007105005031a1000c40300e602001e02e00d03140200d10704d95aa10f001d6403001a1640e4825203011036849003200c2554407242000907010020b10100341e4510505440c0d51102c40440e004a04007003130800e4000040044440c0c2d00d850360b5510b89068030b0f544035524403403e00b100c00c50f000d006009600c1111040c0c08042c001035030041c1c0d241c1d0440e40c4034442d120201d4803c071080c0030500c083e8441d0303440b264183c0b40009045654215000b01ca020014002900200b4148a20400c9180203400480c00c00c00c03519124489120603000211020102c2554801c000d0262134015400d0740320700c000601c1 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 414989307 1250 414988057 414988061
    0x10806060d0c140304050105060a0918140a0203060f01050a060c020a14120f0601051f0822060203180c2d040e0307060b03011d0c120712060b0f0603010608040204 71
    0x20704400c0d072801c0d20141d107840b070030f000c1c09500954055916a4445060121a251200c0040000e10405c2d900b08803055035043e000791203112280c0b002c0d12100000c0755010041d1028000c000001364005c040e981c603032501c412801040341080c02400c1c000c080c4814045a11801628200b21064005100411540c130f481c4240a01c1461400d1040c0c0090b800700d03c014034610204000541080c0110103400035605206c14001000c00a02d800c00100c20300300d03608141c1c1c5402000d001d4001070100c901c540a00301c03002c0b00c0724142c0c280d203a00030070f498800802c03c4481e8205100f5403090541200942e14507448075400c210b40d5420189030304508100007001c0c0390125450030460090788901a1000c5103c61240c110607040d80c020207015149580c0390b1110407100d00e820f20400d07880c1010900c40e108111403010b00346030b8038524440c040b4091001c007a500c40509030108180c0c2c004044c444505d0311881081d20f01341001c1e03c0e80c0140b1034013a001640c07018500d8600001687d0581d0f130300e076961800a40e219020000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 414990557 1250 414989307 414989321
    0x212061b0a02032208070b09010f0518091807030311060702010c200c090a05072712020a030c0810150b0306010c03090b0d02040e01050a0302030d0c050f101406010806060d 75
    0xa00070104c0000381200003403001500421028411030f486d0301a031000034001503052034000003004020011001d6030910f01250403084d0318140c40e001c0301543e506d00c103003520b4800c4050880a901c00c040000040551000c18041c01805600603a103941d280d01506909840c0c4103007400d000305011f03144655402c100b1000124080f4100c4003192000403400021482c440b00c2510020115a1070b6800c121300c039a0001c1d0414051015030100c50030034600d80300882e85102c40c4d80100d144c403601002d040c1e001d554540c450803003c1c54014514501c26a640d4600c96900c0b410446204403141c1402c00074440c01140c002c08030b04503524030510741e246503035035801180c0603801d1000440a1111404001c140303034003000060b1004c011984c0005a503203040c070f148040300800580c03209204d940d1362001400140c40c0814150700092903828000030862081c0340c4141448400060020a44100014036000c10a02c0d0005c10389aa000500c80750240c56002c01150b0303c100486115400c07403402c10054000da03003990300c802c0c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 414991807 1250 414990557 414990607
    0xe040c06080c040312031b0e092206020c010504030f0905030a080901030221010f090603150207170f030a0f0504030806060c0c03120c011121070c0212061b0a0203 71
    0x94501500c031781c0e0b1210418404614040004c0e524441901031100c0005605400002c905124100030420300005034281001031074402500a83d1000f02107481c202e80c80001125809030f07056480d0440120054020041114182d00041c0c1900034a0380da5402440362505441016015040d9680a92209103184d80070308030003070406a00708000e032030416811510711100320080d02e801c00070394035085000c600a15550045c599003450010200005039020822582c003070301c00280980c607800701d03040403c18885200c1c0440305040f00010b03021040b0f210070703008500c0341d0031b85902048034903148a58501106c03011500140490014000b1410500e81440600443d01c08181103542c9020603002190425081c4031484140c580c000c12102c141290a0180e0340c1900c52880045042064070b2000c040403c80d0b41203900c02c0e401140c008601c48a1180140c40c040c030350041e15055541130b40120841d51100101c490510420105c95640c15603ca000221001c1c0303881c0d9801107003040c46c404141c5070100d520744220 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 414993057 1250 414991807 414991831
    0x10614070f0f02030606030115090507030e0d0822030e01030b0616080405040509010e0a030c020f0904080702040506090112110d02031c020105160504030b04030201110415090e040c0608 81
    0x440021034109445554502c100e03a68400c030940b03881030600e0600050b00d907a21a904140400051000305030032281160154180032503140c640032416401400d103e49102c0960017100210340000e50080c4500340522034000c50100d0245161002d01030765200301c40000c0000d410704585145035842500f00d05e42140d00246224580070038070052980104803140129104d12012a0421240c81d00d8401e150344030407090024009980000c5425403501c507054401170900c2180305010080d92554102c440e0746c100b020b403c2110b6414541440c0645400881c0101c1c03140341041c001441d0390400c40c0e4442c0c1220009140b088002116a035002030510325501115045005040035101581d000c0020013029580e5507000002081c403084000d0075120014688290424000700001c41a60300004030740449070840318020341e944542ca000c80c0540f1110044072016800030070045a1740c03654020685040c04652203c1c0b00556a4040e240c0000c0070413035029101c021800c80410031a0f00800096a01075140c40310 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 414994307 1250 414993057 414993067
    0xf04031205011403160e061003150b03010513110406120b0916171b0711030105010803091003060e040204110d0c05040e01050d0b01140d20040c17010614 67
    0x140030101d0388241d01003d00000036142030900c505040c06881880080d9104c2140302a0a2501c021140701010740a2409003421018858446100b6441820100d6141120111a982d40d072002d82c2e07550401c0c05950300c184c15040002943d01300314401d072440c0400c041406030030035240c031205842e000300b41559680380341c1c0c0380c91000e40f00b81d0340c254090b48200721a01040c0038800304403030010840001c136401030400302880c8080c07140c1541d03990041c0d8a01e03c8010b40043d035519040c540b886015044000041e019030902c00007084130800440508010203090702c25111f05855070340c040741518020310420003021020004200581400c3e0462500480144100ca01d42040c4642d06811191144800d0380016800310701404a1001824841c2c010714084074a20b0700040030343c45a0300c030a00107105009d020b0722226a0050079445d50401c00304503542000550400307011000c0d0807110b912419000510640ca001a0055440c1c080c03044140400c21096038040c45a09005094407205840c2440e1882e070601402 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 414995557 1250 414994307 414994337
    0xc120b0d170703080c03070207090203040f06090506010302010f05090f0f03191506090e1e0f03390a06150504050109022802030d1e0e070e090a03080f0403 68
    0x1181a214101c2410071580c403000c6040007030107440c0c0030b000d00419100c10000c0c0581281d0018840d02a00c010305401230342e82d1075515040e0360280b441400100300b2406c0c080460305000e4045500d904030b83c000e0301c9800f24450b400c0760444252141d050000d90208000e0600c2c001030824214580c0b4550300542101d5124440250400e103007480d1050441d91007143d40c10b00c0300c200540303028840042041d10018452102013400007501c0303299032550440c00c140c083e58801c0c6c800301d040050284c800f803400182d941d40c80034884010041d1600400c0070f05c40020b00d00070321a03101c0300034100d4101c404107140909030307010280d07403104090081054000f070741c2d180710308000c11250f0300c1e4403071940204401c40c1c0040c3d0b103201114019072814224041d418000f10020510341201e41c01104031050303400000c900141c1d078021040030040c42c0840951002041d440c003070392481d000800140c00c0c030503192050030703510403036035517103403407650760b4505800100080c402501046d41d402e2076115007a0403a1082c2449440c4007403c5c2 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 414996807 1250 414995557 414995573
    0x160f050a170d20090409021801150806030706090e07090f170d0e0a0b0a030608030d060305120406020d080601050d0c02100b0d020a0501050a0203120403080601120c120b0d 75
    0x200c079a18500c00025000c4054029114001100c40322102c0c44051500d1812800032502803440524000c80d261100e200031956103e0606401d04c0c0040010501c650310307001d0304800c0007110314513040407411000118900e80750000342103040700d0340340e5140c0141504108181c1c018001c040c4c03644050104251011034689007140c1c0c000081d03d00894113807030780381041520034034040f0409492014000c0ca0f40c0320404985807004031009850b2240c4540f81c0d6802a050101c0040c605030f4013440e8a0702001c02e9081c100c52442d000002102c0c0550101c401d6100d50340140318640c8654460080940e0000c880d00a1660240b03003000e41c0858141020307030420403111080d4080e0360903516540011b800c100416020783c0d100d4807503204071070780030350381c400e0320a400740d000c40c940e0328190044c00d05003c80480c1e0403220910030800c458801201da54101c4880c1400c1c60090700d0400b050303c0c2c05007c90805000c4902100162080d074049028540e1851498041c004003000240302222140e9081052500c1c00e02c0810080 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 414998057 1250 414996807 414996833
    0x909050709090b2707152f0d020d0e040b0d02030a030f0f0201020a091205070b070c05041a0906040905031303081902010627021213030e06160f050a 65
    0x16a18406944c640b411131043c05030034041d140c280c1400d41564604680d40d00044080a03600d4001c0108106c4140030800c1e0390f5034942c10996034070440701056040710110390505a1041900c60400c07209084011581070382c071070070718200b40741c00584a03140003111440c240c2c0018081c0d041c094101d240d001c05940111381407144c180015000701d83c0050a1034403680c1d0050036401c101c95944021400c10050400041030761000344101c3d02c1d0080c80c0340b0003405000d410f220362001815103a6681d81c5d28a99440c0c0001c07601014071810f8855860300c0d1074120703200840f9004c10b11341d2800800c0c4500384c0d50f41400300001804946001d54051205008100c00d00340d4046443d0b0145018040da0303529420020702c00d05003008941110421a414820100844d40d070041510241840c0743d100703011020f0004814000900440d15054510000a4280075103084070b041c540354000d01980e00c1b00c0b80b1055940a0160714403c0039600c1565001601741e500118440c4541011442d205000340c0c0c1c0400b4151700c1d003c881840c0e07 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 414999307 1250 414998057 414998063
    0x8070308041b05060d0905030f0406020f060c0a090905040c03050d0c1707030507032a2012030913021902070e07030e0303010509060d02030d0e04061a04090905070909 73
    0x40d0a00340824800000324601e100640314056030400350810300494154003c0c190700c030040c3d58441820504100c0240240c5e16034840c505d03179003901d8580c0d85000030f51310b41ca010b8083e09140240d2010540d4000b44104683c00c0c5429500c030241c0c1103103011801001480001c100750f03606a80d802d0b003c00015803d102d042000710715a038903a441c0d000d10342801410032107000c8154417100000c019540000e5000340580b00c410f40c05082644420400d5480910070000c500e072440360000b114880c01d13080000041c000d54030355821803440040d02d944201488941d0801820001c80380d031041c8280302103490b04a5003075509410b17400000d81000040820000700c1649410010003503003005405210b085401c15982d07500440038501840300f000c003500c60a403070344818001c0c240228158000550540c0300c07032003600138081e4098112802c283e4219001019940342c12031080c480c2d410003100141458200012181c5005112503480c030f0940f41c05c100e0001051152822151805804000200c0d50582d105040702180 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 415000557 1250 414999307 414999317
    0x7021215010e0a060f0e1f0312020106030b070e0315071704050a12050a0903060515060d05091b09160e030a0602030405010c1b030e120f010213050d0f08070609080703 73
    0xd00c12207680903154985c204000c200c0910000704000501da00744180c00c90000c421080c07503040d246c0403900c0d07481001d410161140710000101e145465055102c10b00701d0340501c007003031007075114403000302d880150302031007260700d80d11040c3c00c0c41c1c40140200c58543c114410341420b07060800284500714103480112400e8039640c02288840041c801d08503428000c800c1ea0b482d00e03d240140d0b0480141c00b0303500c17a00002e070055aa64001500a121507103d111034940d00500f810f40310341c0410a0040541400c8400c41c815018203040708944070a042041206040c0c004c050010640e00c40011070803804551000904008044d00040b6a54409021840b00035001310005696881c0c541043d07400e54410241c01c104100030b945145600480c825180034280b5031500d0181e140404410000323004034040407001c02103000b10703c10190402d00550081c0010403056a180c500103984204218036203140b4240602440a044098030005016030f0082403d144149000204200c890b00c0da40d030603070804441140490 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 415001807 1250 415000557 415000561
    0x10e10020909060103050c070803060a03080c010203090f0d05040b090307030204061503111215040e010e070f0807140d06090f0c030614221a0c0a11060c07021215010e 73
    0x200b8004041c942c01203082c20280024100710300d40d51500e101c1c124019052000c04000714041e552480f1944004680151380280c4807504600914000c0d0300c241d407041c4141c403070710b840c1c0304061001181c0641c10098680310103080916054284a00354405107a50741d15000c1d8082c0800140c0d07852081102070020781c01011070302022050042c4c125280100a4102080300740001e501400007409180d0340900c1494000c6000c064803004180501043c10720700286508110010740c0c01d900003c1c00c402100c8082000d0703c1030698501c0e010f5201c62107405a2004024003d4040d10b045c00c2084110b800c441c8980c1000601c0da90549461041c1504d064007100c1c3c60002c48030130003e102082c0200e980800305c548858002c1d042c01e030020509803520310304e418220b20160070290188080d450b403001c22507018440040349480d00344141440360740080c151402040000c1e41c0ca090310035000410318801d400040c2c0180c43c02c0d1980d003c0000300100e4200751070041c4034250312544003195290000e4000c4c6900c00a44c11b086c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 415003057 1250 415001807 415001809
    0x325050d051e1c1202090a0b0307031406091f1203032a080604110c06040515090607020718020f0a02010c020f01020a090302060906250b0a061d0702010e100209 70
    0x1d0500064102c690740000f84116080000010001022003a030414415944070b11310100040e00600450300d9018940d180001000340c01c000007180700d107425550030401014000901030b050501234031036541151403500065210091100010324000003840a481d0550380d69400041901302c10404800017921100c0c000e02961210001030606d003c11903461810404681004020751001032400e84517a0300c0781c084a001808030012100d80320780180035180a8902070500c1a640d0b817900304040c030b03002075540000b800300c240410f5141c000c071001d60262140501c3c00044420f88605491855070030b0303a0811a0782d180545c820018801049180c00100b900302c2c46580c044d0400d9003c03807180704a80d00422420019035172140c0f002040e0b81e13048510945560704c6401003840c1d4017600300d21240040701c101f100704c42580310080d10351000c1d1169080781c5280c0e40d11001001070354014400d04414292042a0b03445811504400320303070011480c800010390442c080030140c5803000e038000d00d0b07a030a0b41c005141115 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 415004307 1250 415003057 415003093
    0x305030c0313022d060703020d0e010905100801140402030c070f0203030904021207140f0d020c070902030108250609060509280504060b03090606150409061d150325050d05 75
    0x70311800b201c100b8180711247d14083e49a001416560041084204001016a010b2002c800207003901904025402c4400003014203024003c0c01240d40c0b0950218100149203064001c681c411f075400240c142c2040c4031540c0d800307660a8107800c126814042403140c88019255440075140c3c8000c038040b18042804c011002074411780b600002200c1e0545c1c2007001c1c00706402000101c0d00c40140010006a46400782e01103c0c0c140340c3c041c3c0180c01c0080c000000051243c41c000340d904e04d892041c0014010106c5c1540c0400b1500e0258032440000c18409182085128000c0300601920000500688451203020300d2810301c0030860003440b18500540318050041741080d20500c0040c01e08a200076280d400c1c0102020360702c2030010a020b21403842c0e1f003a615007440000c000da0b00288510720050050f162039035448110f49124140d0085180180c0b00007400c4014403122014181301e001d005041c80e4042d515000300803258200c02d44800149038140011152034412002c0141d50246015001d130018110181003 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 415005557 1250 415004307 415004389
    0x7060203060f010305090309010c0c030209010308040e011d01090f0e0109050106091104080705100c050f030904111204080d090804081623101b0c0905090a0305030c031302 75
    0x304042c9090304002c886c03280001211200142420118245642440c05804072845508000c3d00f00200da0000030810400c00d01410550b0440ea2045001740c0c0c80c3d00621040c0401181c0d81c426501c21080102b00544c0f0650100c020182041f00100d1552100b00c041420364128200440d102c2e992528104402246e034480e08001c11114811140f5051a040400e617455405000b15486013000140042495000300f04003200c0c1e40c0d010098031203d240340e504103502c03600a840362501a40c213020704180e010440c00c041b1084d0020000b000c0455840b0b6407610741080e00030702c426403203e9503038030001c6000c5070b4914054001005c03078800424800d15204103d030600100b1ba80402540000c040c404020161002e03012000010282c41081c2d00038a46103003225540100258200084212400035007840b00050044043d50071100c1c080c03180342c0b1611180e558403081c020014002460a10108064001c00740080d9000b15250a01c080c2803c05c40d0009100200c2c03901d16290501004011508103c410245400b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 415006807 1250 415005557 415005559
    0x80c040917031513150506191d040906020403200108040b0a09020a0602030901020d020d09030303020f070209010f0e0a14070521070f0908070f0b1c0207060203060f 72
    0x4402000c1039541e421010318804403032490020044002080400e84154030380305440c0040101e95040c50b4015810000e181c2038010401d806905140490181003100031503c0705400c3c001c4d5807103a0311010340d0032100c0200040d41c144000381c3c5c4d0112101242d856020707503070245000c0d50740140d07036600d036107400c8003090114441128221400c8035004226a004140e00e94002e4012842140580c1c0d010000d030300421214000035031000700c9250128216900102414074801d084e02140d040c29010704003a661007100300d510310f00281c100b02060000a00c207801401402510320200c5007400b44a5000600302d10302600070745003003480d0319420071070300514008c2e203034202811502c2000214840c44015100c0e5000074a044140800020400c0504a000f244c0703550310580c001d2462004d0405005c01407009450114000c0007d411441c0458409030101e4900d00704c60b018405a10880d15090301c82006400c600e000303104003400c11100c10003030901c50005040d458032900700169030f89094810403000710340c50b801c0c103 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 415008057 1250 415006807 415006811
    0xc1107152303041205070b0c03040618051b06040b031f0605090901060c02030c0d060e010609142a04060203092b11030a081209120307090b09010306030219080c04 71
    0x110100d0001c08072030b00250800e41040040e2152001955248034110001340503500c02000c00c43c5141001c0003031340c01a44580c10a00150510f00800c0f6140c00007210301510541210000281880501c0c5030345e000c490000c1c1031203052568030007001000b0341046800c4110450ba03030a0300210046281143c070041e10147c241242031411110105000794014040d031f105008200c0e4001d025503600b0001c0603c03604008122422802941ca4000d024200e200b1540c0815800d165011688041900400b020012026120129a80c03a03240051840103241486441401ea00d0050007590103803070002c00180000d41c00955890040400f405444943d48100140a100aa01c00d604101c1174101c800f45c442e8014410b0000510402d0000341842c1d00b24400a10008000442c00c2c030712000c11902d94441c00c0554142c0f12401382e01c49803164184000c4551100152220700c0c14400384200401602610b44103240001d07a450303d95000c1440c0c0e500750407501300c0c0300000900c10080c1520400043c440c01c2c4c1c2c00d0f541 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 415009307 1250 415008057 415008107
    0x803041508060d120c0c210204050720060108060a02031302040b01021006060e0a060e18040606030b09060a050604020a21020f0310150c030504090c110715 68
    0x1040e4903500e80d605024080041c2640820015612414034070411500044011000c0380900b5024040180e003000446c2d484101200c00128000e0441e081c003401e030300103440301207c0b801036402c100060900602d45414004400c03600382c01c0140040390400002c1007107004080550401541c145040e030018402d040fa03500400400668a21b40f0600460b81c81d41590702084042c00c02c2f00503411319007107400069450346400000208a61300c000038085000007500d03003003d956100d000484490389022403440d00200c58441e996200b007501c4050551060040f040000c001d0788030b6503440c00440094070030020a1380280c090010484c00b5101d425000101101c04515160507280050001190355441209092403203080011031a5140c0441ea42d0750000070500f035403403402c00070846624440e40608114505d0f04600903400303a01032034040341c0041c0c140d01d9031810b15240404990160a904032840304000080413911130703140040052101074031502141018503590305200500740419003910642404480c68 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 415010557 1250 415009307 415009319
    0x51807080d12200901170a06050103200f0f090a090f0509210c010e0a0c03031b02150714010f0c02190c0b090d1209031e02030d05180603130309080304 66
    0xd000b2005080e0700c0e1103840f881c41800503a06d10064040030071950b08100b08010b003065a66002d04251042600d040180c1c0052400c540d11151160713081d400400f008004240c00b1000b5400607041c46001d80d645549054030f00390106144031042d51183c000c0c60744079081c180312082d0071b020701640522007000900e201c1c400c1c000d40f0990320016508103000e6400c00108500c0c40d020a4204411403202072044810102084c58142d121280521054000464003011040c0f03190512109a0362140c00420010202102e50104d0819a1110070103c070402c03010030f080380c0c201400b8010748084203014100018650100341010b0309081c9040b072000d40c02040000c40200250f0184105e00a0301c03c42264941c440c1d01c0c035008210a0705449034081d0003000c0302114070903510361007040c940c2074901c21244204c1d0000441c11000c425800003400030342c150031800a03444200d00c200c024244c61040311407980c440000000114030680e201fa165905118080c401c07131414190004078040c018200140203620346403402d6 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 415011807 1250 415010557 415010591
    0x200a060807110a0c0801060f0b0702010e0112050f040b070c020603041209080f1606030204060e0f060f0f130e040203060106030504050a02040501140f03010606020a06051807080d12 79
    0x2006050510400e0008296500e11030385407401c40d451107000716010642c003400e01003030019251040e001650f01784000840d1040c46100c024045402c1044d640382010100d81c015079005091200040c10005101c40141c070780c6040e030003004e0040401c5041d40d4581c0c00c0c00c1c18402100c180003800c04081c020041030030710060300d401080b25406030b002842d000700c0354a074400c1111210016400303480544600762069a0000c40440d80740b180d001444048003050756202d9050b401ea0007140f0940010401841c007114213030401c0403200025880c010861864070424188404d02a00550300901400c0400300d14808040300d110140c0000c0e10300170300202454a0281d000a940d40c0d0140102010151a6000f2404110080100d0f04603264001c00900240da1100b509030313582c01841c0080b901c1503295500f42c2c42c00e4201846040151010b0340c0c0500403032401910b588014007006004080381036014102d041554409224440c080e04454000d420b40f41c40c288802400726210310303401d0103114030f080002540003802c1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 415013057 1250 415011807 415011809
    0x50406051303020904030f02060a0b090c0a120609060e090105060d020d0503120a1b08091b0a0504090605161404031e0501050a1b0206090309040b1c080403200a 70
    0x10345840c507a20488454560300356103090b80300070740000200081c041059041074150541c080f541d821950350f40d031042401e5003a180308010243d003061121011451440c0120018000c02e9814140022480000d1501204071400d0f544501c03106560b40e4014000d119103074159a8202c046d180c020b02c01802c00000140c001c5155180080c0705040c080900001c02005000340c400c1c000044010390303407520b840c00c0d1550162035180c2024400d00c52507000403101c50700a403521405070050000400391072541c116004140c0b071440d051280d0000c10300c500000c0a540b64000c19031524402c0402040e941030030036140c0d80030b401c102220024000c0745180100300c1150b210558044a0704030f0003c199941259489000604807480e01411650030f1100b000f01c51850394210305044101c81c01c032816080c0260208030b0b120303070056610070b8894008010b00300013032815030451800d0729401031401c01c00005414009a4666002408640002001c0790810600001842e003010314110361801c5044591034134002141c41000f = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 415014307 1250 415013057 415013069
    0x1030c11032a0307150c031a0405060102070b13030b010b0715020306131805330403020c0622050d1e080408030f04080105090d0801170312160e100504 66
    0x10100c2100020b440440042c100c01d0821429241ea9460504262529581d05604d4400f49810301e07549080d03e44c0f20303204103220010700080e80199403e5520400015203405072003141140300b8031001240b4010145c0050440404560400082c0c610310302d040c41000c0d105074081a0304038028131900003c24002034010780700401a0100590325941c150004007500c04400025001c145040b8006040141d8200000c00701d5001d00c08039007008c40c03825038102c006030300c102c5100310340c045145003281260344000c1d082c0d030058403070300580389502000408100c45030411080344400100003186441641080241000905810fa6208181754081e4403042480003116030001081a1040c1203070050081e04802d071406000500203a0356100c01c050214580c0ea0440d020b0403486503e004049510030700005240d4541c4c8800b6100c00805070300c2c1400103c0c0100318108008410300082214002c0a0841421140f1603c10481c09804261001b107000700200d441d100f4040c0210744cc9904041240d82010a8400b1904 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 415015557 1250 415014307 415014337
    0x909010609180c0f080703122001020c011422080408010212041e080319060b0d06050406050a051014090402030a06060206070906120905030d05071710140609010e0904080901030c1103 80
    0x84502c00807101c840c602140415271405031108420510700c107400401d42d00000d00001d02c1341a1050390491b119400070340b02141c1d040001c25200c0e1a1032a0383c07218120707080c041c02103181410b83d1003a6507070980e80140d0f22000160320403030401003042001c00804503142d0700403010081c00c840070ba403131816600c0080c0c064a0b80d2860030001c0860445203410240160040f44805038662a1040742d00024000b9030086912680c1405408149130514483c00400c40d00020030a90312a1802c0b041a20303c400640d0300c58046039810021303800d107038a55000071401625003450001d542403821600038104500a03280d13904110740c50200b000515884050150345004000001403040602c3c50902e2440c80740207110113025080504010740640c0040486100d101c03031141100d11540c8140400b111041e460082c200b00c40411400c9022600709030019246441041c10200301404c0c030640000c00c402002c4804507410100040c802c11a0350b414040c880c081256400c1c00c101c90701c94a415562280a03d0300c100c04224 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 415016807 1250 415015557 415015583
    0x201030518070f150309050309040b06040b04140423041707050708030c0601050a030f2301290103020702150a0201020415032301140909010609180c0f080703 69
    0x1d54044101450341114200310341100c1d0741d5207a00082c1e00c6051040d01c0f58110001e54550390b0354040e008000031607502101861a1414600c05c11004110481d60280c014409000105484070048028405001c241c0c603c0522004068100710551b0700103042c5c0000e0800103403180c1d40c0c550300004c1c92a0460b5000c8611190807040f1489100523001e104409130081c402c10f10001240b2501000503d00c0300040010340d030641e0323252002d00c07850003003501c0010b091440b007013424004910000391b483d18003080030400303102146034a062642520220840f1603840740d204190503016544000800c1d00120f001c1c2410b600300109900000e01c0f0b10301e00002041c5804000a00310f0721039100b98101c03000361500c4c4000c5070101241c040c000700284400c01c0040e81071400c00b00c113203c80d0174910240c03e0482e98914241c4010307400360818804078250182144040d59202e0034081441c42c514090304c000580c1051604001401c681018284c44407240e000a48000d0045000d0104c410040303854807e890301b20320041c41d50 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 415018057 1250 415016807 415016821
    0x7060e031608121018020a020102070f0b0a05072318060301030c0608061914040b030712020a05062104080702030d090303030e06010e0a090f0c0605210c0702010305 72
    0x600c100411503944401c1c20128004001a1a000c0c01d1042080e0448039219034801022a103446560700036641595a031009007482d000c010b8009140c680013a00c0003601300308450b078131404402200030044500440c41420400f001e1064800d9550144003854411100c6440040c0c4440c16070981343c002c0010200001c1c442140c00045042c0d846c507080140c80541c0d25a92800c00022100e041d0084100281c40800860341c0c40c90107401d0403000103d0301070040100c3e1324000351914503c0200313a03240d4010791240e20600507603506010170401000d40902c00c0c03400d40e80c248100076441055800091042c5402d100002403030240d2980c13108400d054246941c0d80e500d80d030419100758010204002d40c1072207030030010764001e40e0010b81e09003242c2c46a103007480305404803d88151202424021540700c0b410302c100240900324245c1081e0080350040c1028401060303141c80c0e480c5100c2c0300e45c00c158003080c0d0001c2e070380c06070406805c25800c0c052040714840e40e06050070400240385125000c0e02a0400d41c650000c150340b = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 415019307 1250 415018057 415018063
    0xf100605090102011d0609060f070801090513051f0e032d04330201050f07051c02040801091a04050606040b0a05120a030905010f0804021302120a0e0607090b07060e 72
    0x24070100003126045c000042d4807207940c0d41008036042c0d00d16004403c0410620444407140c18002c0c42c090725041c09582c01c0c104910300a0100415802060788005540d001040e0144840406401c006080b40118031024601c44242c580c2185000785030352007002880f4001600001c001c654404402c0350341304c02c00d40d1804c0ca071240d01590b0031503242c0e68500450241c0c1500000745140104c4160351070000d0b61180c4200070f908840c0e00700d4010b50800151800074107003e20940040010450540b410522408107205240490300300d07800000440c1c0d907402c0001d0078007030304484228800a24446201007840e240e03490075103c05010f042d560266865444082142c1e680d481070744043c00300134202403840342d04003061742d85e1451000c1c000d8010600043c800308036035204d1f04005600c81c0c000c1d286e024241c0c07103640c02d01c503400f10304070070007000d041d401c2c00102c1d0483c40300a4002d00a40c0104404608210050441c508040002e010b070f00070703c08419410003265088000780e0b02d040360843c1c00011030300480f40100d81 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 415020557 1250 415019307 415019321
    0x80a090b0c0706020c0909031902100914250603020315100221180105160b070207082b120b06030a0e1011070f0c030f030302120f10060509010201 64
    0x40103840801c8010071028005107450071030340240d00721401c2e40244414800076410942d245507003508200300e00300c1d03c204020122035080301e85204498112510212010845061107030031a8410744100100155880412400581c1c0004803450070301e0400c0611601c0c81c0c810f60b441800306040e00400003c120480b02200c200e4401000f40405410201c0140001d49034a1801120807140d00120024203000b060401a211940c039440120398810310040015500c1d83c03c0240700301540003ca050b45400214020342a078000c01854008000300c50800c4030007401d11409400c0c80101c1c0500e4000d942a1101000004414a10b04e04100c1c0d81b184400280001070140001c0c00368000700000288018500b640c1d00040e815001e41d03064400c01c007240306c0c403901503e5486201130251101400a407001c6501611000d0301c0394840d111410b0030982d03e545418040038601e806801082d0301184c000941e12819180130303448423f01c0d4035104130380352125000841c00002d00441080203400300d200c0c126a4000d43c8001 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 415021807 1250 415020557 415020569
    0x1511090915040507050306100905060406120f0c0504060206090607090b070f20100201090c03061e05070f03060e04020d031d090103080901030e071d0402040f051816060c080a09 77
    0x3c092440c1441d0080c0041d8415075802c0e0280048818074029140318441c0c000580d540144905d15140c42c1071070841f25541c4210b00400010b44d14000000059014401c0e2180c1004030f0b200c04d91120b04c0c1032006030600702d0081003841c3d10f0b00000d0400c1035050313018500c0c0050b6406510b0a03030f100d014500300a82e00076902c5000400b02c0e90320750000803146a07050501111020700320b5020b002c001e000c1c0b400f2400da03002c102c2d006003040355402c81403002070703944d400c065841d2422808080c103c510362850041a44d4041e52800042440809440791080d4035004400241c1880808403040d82801c0e4042070006403015000f808012192408507680d0100b8401d03450010401010303150656124241400d650b8480c120841c007281c078110542c032107000040b40300011141444062070000001150380900120020801c0341c0c05695030314400302102d502e1181c03900651800c032004043c8010421802c4c0740c6442203580a00d503212800d400c2120a92219256550507441001c0a4452068080660306218590030070 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 415023057 1250 415021807 415021811
    0x5070206071a010603020703020c0f03011503080904060f210201050c0a080d1a0616170406050d0f1b0e0d050312070f09060903030e2209151109091504 66
    0x2903801d02402c0c0300000c048003003900c9920b000c0c0e66a0b180c00e40480c49100c1c0000c01581013003aa00715213107070600041240d042c0180002c14081c0c80c214a030042c40c030181d00100d5180e0400301d40461141814860030b0060003214000c1c410030740c01e110869036079111180d1480c3c010104074422000316441103003611b414620310400c441c08444a8600400a500300f980c0408509103400302804e685000d0440040031000e0241000d0324041d901c1c2e4681829240c90902504c440c4031140c143e11654003403500900040000e962816112545007041d00140d80040b001e4103180d504065128908103000c40c1030b0f030200401c40c140700e0122110680803a80d1140e101c24050028000811705000c450440c09034680b00d103000e07503a001c100003034500e41a90951ba040c01218000341c460003060001070700036499480404001007200115080140c00d40c40d2030300d1002c040e510302c180c5502000c401c0090100750502c2c1c400c604d16050000790459189071080d805188115480703044a00045601c841d140240411071038805482 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 415024307 1250 415023057 415023067
    0x203060907030501180f1203060b160201030e01050403080606090d1202061806040b0408070519050309010e0a120605060a1505180d0f030807031d07030b010e09150705070206 76
    0x80e281d00c982a91000350b4655007403000318040101c0003e0508030003035100003400070f100000e0701c90381c0c00050107041c0c1405141d603034440801e09a1440b005004e4841041e11084814106880010160341e01c1151011450b810302085c040000d0700044200c0d4840c005841c450f4a8102e4240000c04d1254049000b0b4800a21420100380581e40880c172280f107486c80014004601d075200003070a666160032079000e0800d01c1310030007160020712064020440940030340110380f21300c0ca00001514070414180011140c1382d000041c0b030145942c100d04080d020100490f200d070700041c54806c1202a003180325030010b01095071100012029595080301a02400700348081c1c3c00c0c9140c1044002d409a80513020744045100ea06c8642034080c5413060701d016000744d001920a00990960388c056549100241c0401c0525480e000c0710004440e0312a02c0300000040c100061888034a5811705130710703100d0306800008103030104104001c0c4212000600f8912450740d1102e4116580e1140c800312b0341d034060308500a500510000b4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 415025557 1250 415024307 415024321
    0x2c01090206031311060304030f140409051602010c0311041815030303060914091c0e06070b04060e06090a0f020f0a090b03102711060406020601060206010501090e22020306 75
    0x783d000c200f80d21500316010f80030903840412615000440c3c00500003500e000d580410301d445080f411440000d0001d4040c106a00c9038402401e4030022240b09000394180c81d405040254240902140310a0700e040800c190720b200a810f11903881240103181040c038800310403445441259000b00009503492924103032181d00c07490010301500e018440c0c3c80c241030820051840c074864180e005170081d152280148080402200e100f220248a840f8102c28000d4250f1000c00e151150b80c02021b84512801d011a1140b406250060403a98124107544044c0d000508000c01c0e103000084404180350070808400303500c0c48a100150401c40c0100d4000e410421000c80041e210380150028071020004406440f42c00307400749440e07400c0791200106c7e01c05e0240003880151301103007000d01c1c09203000e006000c49540300b40c400010440b15401a481140164041401005169414170119015142c246024114103160120020450740098000013a006105404020b4180551900c64083c0d9000e01910402e240810f = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 415026807 1250 415025557 415025581
    0x8090a031e051005010b07030804020307030804090f0e0105010f0302060d0e120a110604110f01051e030115170a270803090d05042402031b0a0201090501032c0109020603 74
    0x84100c0e0b852007900c1c222900345015002c1c0358107880b5218101c6051804580b0201c84015025005036094040d8590120100c0c1c2d8080050015107105607011464140c419080f0302211001088100340780d2400b4014084110b90b4800d090072a5011542991030b284149104401842800020744080c4509600c040500b1402e9003e42026002da03190380044d881c0c01d02e01076850b0b00088074020050060310b1a2088a403800119503442c4400600d2b102e81000c08281202e0790740c1006181e1004224004001000070b5202c0301504011031a0614040c881208158088001c0481c041d04500c1540c0d11207100c00324a84041452400304044140c00410120050411149584c8160352000090240b01541040d490161007141e049030450401c4074210104a83d8581042c86580424801c50004110194800305c0201d66814900c41e101c010300807800745407001601d102c089900060502d070070020094a00f0b0214110041e00c1d8481a12000d00410480c415600401644900960141000c4244001a6020b03 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 415028057 1250 415026807 415026863
    0x309040e24071103031003140a020411030a110403081215030307030306080d1b02040207050c120606040b040c021e120a0207050a140a090c050f04090b0f0a08070308090a03 75
    0xa901c070344820000c000b00050726440100c500140006d040481040060b00403180100e81416200a0b0307034001c03003258002010354814031080b00c2852800b10034842500a14414441c0c140c001c8a14a46441c2c03031665050000e0080010102c5a0001400041c3e140c1e190003036070728504070303004050303d81e81c10700d620b40a030043c025801003030301911a0f1100581c01501584290000c146101e05200c0c0d500215406c12001e0b50100004813010b0050068140c03141d00c4171503016180c1c014801c050070070340c60001c041c04100e0b4048641913120b503051000c096003550300800c01c24171403141180d04901002c0c521380103d140070216220141d0b05d03107000803144001c59001ca5588140c4070215829044165904510b9411452020200c0c1e4041c0c00007001304103040440d441040c81c00f500d0700f806420701020f04501e00b035580040c2c2c4080e100503107980145c2c00034905582031001c030301001c07601e10301414100514103a413902640001000040f00064101e50b41e96580c2c0540c00440d072010010648804800e18043d0385460 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 415029307 1250 415028057 415028071
    0x9060203010b19030c0504050d2d1103070303121a1009080105060607080f0a0e06040609031b0b1602210706080106050a05253509030309040e24 63
    0xd02150a083c141c800e000c1d50481c0d0709640d403803a003058102002c03c02005180c210444200404946018448541d48004170600910070b04e0350300007500504203a80c071a143d0340e806034480c0d04080303c207100188d0007122590005000b810005440301500b482c2c900f031804c0c0300c10700750b038813030300304020700c00516401662203050700c800000070700950300c40070144009405000c200500115043c4008528003d0303101c0505022505450318035003440d034003004036240754000d8001c007001407030060051060100c2c0c401042c01030007212004003c2c1e14a4000044100c1c0178901040721901c00d928500b209540d00e42060031211461072804c1941c5965415850f0313501d81d294402c4c00c001c180f00800000c0c101d4010001e5501d8005191540d51074810999906940c7d402c50f00b0010078003c8010440030085081c080d02100441954403541982c40d0300404001c0105800032500c2d10000b50820010b111918040161800400e0655000c1030006101c6407140c10400c9160001492690b41c40381c494134802d9000c905802052 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 415030557 1250 415029307 415029337
    0x16120c0f110a08150624040f0f061110050a1d01050610020a0305041e09020c0c0f030c031504140f0604120c0b13080c12071101030903020d03020d09060203010b 70
    0x2d51a003c40e500d502c01680b000010108800c0002c44a082c44d41c0482c241030300410000311145906c4080c0d54082d00540c004140701555204248205490004c050001e4070290800d01c8405100c40381d40c580d21060444c803800300c5ca0310f507804507003400441e800c40d1100542d003000b41080074600001807802071204840707261003a15600a803120250001c51120945a0075070744403480d081c00e20f8040c0d0328982180098043c071a850440000300c010081c4060406050010080e00151000008000c0100d5013441507e2007900148100142a60f00154104850044450a4400e0354440c01c00790541e6803d44100c40d818040c3c021b000f0503981000c200a8030451080c1d18042e54000850811940c030070500e24010008110300d07001c1504190030f80e4190082e60720405043e0b2900c410051500d04085510311000c80c0c171000801c440c01005890711010b00325020030300e070030070541c40b454030003e641e0074590699105050780040d076481c041800380c20038000303a50401d800390b649503503d9481060950001d002030000034 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 415031807 1250 415030557 415030559
    0x5070506010b160f0201091a130605030105030703061d01020f03070201050c07020906210706090806010503030703140309030702100e1c24060306060f08100216120c0f110a 75
    0x403201c15a0340c0c18104100c4000f1000655032a0301d8550308040d402c1c0d05216505000041c289541c00c08541e50311060081c0744d40303554440342a4001f004154204106000d020700050000b40c60026022084039002200403510b403e000c0c0b000300c1c0d4113030440507480855000080c90b4000104a42c01140100321550081020740c1d0b80c0c0309000558007500d0f0000398000502070109455192100e4054045042c150009501100142034a85029800d510039401702e48a144c0c10411040280301141c010700c0181c001d140b41c0301c805c0e903005001c0c04038191460250140413000c101e0480702001541e444a5029148802c05181600042d08100c15a20b07500c2c81481e06401414000d044102c46036001030340318040b61a540c04c08085080201030a0302003680300e6941d0700b00000822780c0ca004000080c83d11203001c10a180c14603601c5420300f04210204c032086070040003215440302402d401c0701c0150750002054400c2e400c00b50000c80d10450141005404002c840100e00c0c04e2103100a01d501d06454103c070100101c1d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 415033057 1250 415031807 415031819
    0x110303040c031505012624070f030b03030403140717031206030a050d14090904120323071b050f0115090c090e0604060e01060e0913112404060507050601 67
    0xd644240140340d02080111030801c000a0041d0444003c160b034042134500003880c55200c08480c518000c5441e072107081c00d80912a4889d04140460f00e07a0900b03241c06c0c003415070030901180d070702d1241c2d11003705071a001051200e0302d161309001041c090b1011000d06800309401004ea1a0740f500144490300500042101281c1c0328074001508111860340040130b00140262000d069400300703048030403025260020003245046035182d00032180b085204155081290282c50701c020100d49458908080181c030440111000d071381d40e0746940b60300c40121b20b06403e0f003c40b132000c140b803203496242004180340308051003803045a0040d0003138600c0702820300d01c860b84a031b81c44a05206650103203800c03402044e036560003800614946031500b03502801c06000420959035800101e003100c00240d00c0000021030050740c04d503c500d81340410170741140d007801810784000c0e40d5440f400000c3e15074031f044512540285211442003c1061a265951001c0c9455140c0b115600c2c40080c000d40c2c401c260071201801003500109003 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 415034307 1250 415033057 415033061
    0x4110a0807020c010f270815010e15030312041104090f170f091903050d020d090b03010b03010b130302032409010606080105190b03040609110102010504020603060d03110303040c0315 80
    0x155191baa2800064141061688194101201c010011140c03980c80868140002c1290b00311244082c1d0300012150300d000c41e03095400344050810701101000d1544a6155940001075840c00700072080840c0c40c030f8499213000824090151401c45d00076003008100c2061084c010380c0c100c12140925058441100c05c1003d92400740310300e801c40c0c40381802c10300c079102c09404c00320b200407000c1c07991500d1508981d031a03448541c5008000d2a08000590021491004140e82b0071041c50080440c09212400c41d41889540c0d003060205004030f00c0400d2011030403074200300010820000554001c2d05944038605040e0300e00c42e4818505904501d0381e041c000114107400740500c07400c7c044070450303628160164205400c102c010543d10f03401c0313600c0c0542984080388001039031004501640c8260301c00584034a1134030381219201c40050549040da49001d0405c000740c0c030b405e0102e80e4000d81c1110350b040540c40d10b150a1720b4105414101d11042e07c4040104020451040415070a0300d000348491580000040c001c041 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 415035557 1250 415034307 415034327
    0x102121830060c2b0f06060207060302091e18070e010314040209011a1b0d030b0f0d02010509040e0a0809040e0601060504261b010311250204110a0807020c01 69
    0x90601000302845040d1010b0301c00c84c41000841c005803010001d5034007a400d0364910070b0a48203681d51110100540368041001000500c2281419070608055100080719a902500840040d03108480f114110340d503029034003418001805441034181c04d02180c000c01c3c60041c038003080d001c41d03c2c2403e0700c500100801c000c01d10455000700b001032183c1c00c2c466503002c800c41d07080403020000b4091000c0e011003210a44041070ac842624018070320f05120070301c02010395031603290060044058026030a83c6849411008805580a00704036907141142c4d03001c540184080d40d40407566001d040308a40230447d880004040c0700b0030407541448a002c00410042d00c4500070310800b004904200320170007100c410a05000103030019402c0b95908807021403100c505081e00507003103510444c8840040c0107150307014421981c441d2448902182807180d403101c2c441d40503844080041e20650403007040b200715501c03900802103004141e200c15484101603c8003030100041a1030650141c05809510140d46d44110f107603c1d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 415036807 1250 415035557 415035571
    0x2151008190507060c05100f1104150206060d03080703090c0b0c0304090e072603040e0f09010f0204050102030d1a032b0201090b0708040f02060408070e060609010212183006 76
    0x407000340c21f8242058010803121004001380c0351248448140b41590340003500040100c0380c058691001b070700710001d0910b000200680d2003540d604c4801d402003540500c003141d0142c214100065658070760b041001c07100c061544051094600001c9507641001c4c040081c0c01102c01d1400300703201091402e41d0051b10344645000e03c900c2070101074007112041c0c400007009428440c0303040c01d80380f0b80b80d01c1340400030120604880c140f110f41103030b00a000440f0340074499a1280040c4410450415085c200003e48907c117402a01c030825468040040381400305140c2c09c003d0360340050440e40b00c54a1590340d81c245000980111401038402c0218500707407401806044083d580c000516035495a030518262a174440c044d0007584d6100c0b42c40640401601c8040042000d4507038827008000ca9403411689488c01c8400030300031405102d06109002160f41c001800d0b0090300742c0318070916142c01904c0903410030b0166803200d071a840160744803141840c4408110f01c0380c42207030541c000d200c0246c8030070b569503071840190784003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 415038057 1250 415036807 415036813
    0xb1906030204171c0c0f3c0209071808010c020127030f0c050c040515030c010e0d0303231611010c0806271e130302151008190507060c05 60
    0x45007130640b0444504296034400c0342401800c0016850310402c0380340ca20b03158001881080c0c0410007824a030b107140f2018115025400e104048150b0108810000c040c3c401c0c2d050245010b06911541c1814017034101501c1138000800030000c11210080c00303401d507030140c1d543d140f0307101d01d190400d050101a1010445e8040d143c008280790a101c0c02c4840c641e6030382040d900c901804944000131350321070040c036001c3c0c08130311030110040121100b014202079803100141e05202080c400304009442e200800740346203805040c0024400c034003140810403048881d02a807900160f507010030010318890b001c91103011103540c0e0741d40c3e502d05092112078200c0d8040f040c0398001c41c183c200022814640b4804551941c2d4100c4800f600341c4040c21020b00340312070306075913213600807124007074a0420180c0511a0b03640318071190b4983d81c400c1d11984001e0f4960441440c0b50b5a070070304400c0050f201c00f000c600301d0b5008104110032600c10b03901981c800043c10091f05c44c00c6805024000300024424800c0c081c0e0b1185540200103 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 415039307 1250 415038057 415038103
    0x4020d14010501050c031207110a0b060f04020c0a0f020307030c030b0f01060801060c021002010605061215010c0f0605092d100c0905010c05010b0d0f03080f0c040501030b190603020417 81
    0x4c1505d80d4028056410046105524031820800b4051012010b01c150f0be4078486003002c80800200c8484000c641e0300892041c040191003500c001442c03041e1903004401d0894440640c00480d061400a40ac00f0300310500c1400c1c0002001442a10740e4810507884120300000c0e40c9422088032403010a200b4000000d48400719140545403003401c110180c1c02c28000002c403a56201301082064101150300c03400041d016040012403651442d50301d0034a0402d20b071a0003003100503929100302802000001c0c1180740e5a9001900e03040c81002064108ca44840c500700108040c0801034242800405204149005990060f02c4074035440c01400c1800ca5a9120100d6050a14004550b0080c04000550310740d33480d0a414000c68403810020b21203d400b400702600611001d041c0a480c600c00a444105e08001100400031199844030544080d29400d03e000300d0103d00140001c1c00c400c1106841051000d0ee464001401070b41550003881145c170811400c403480c4200b20031f13113511900300011410703c880c40703400 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 415040557 1250 415039307 415039327
    0x804020d120306031202010c020c03030a0512090304080109150c031b0f090905100524040b0d02121f050604050d030327150b0609032a04020d14010501050c03 69
    0x405800c1c0a6041c40e0015485a50b82c603004060700c0803100401c0583d40d071303a01c034884560b41800421a0100268029460108242c0f401085031240883c8258100380f0040815a0403031f045c0200c50003401603100038800c1e038485040c902c4a544052002d246141e00d0304589101e07190203401202910440c0b03442c1142c60b125524820740d242c10310210124100502487c0208041f01c0c40d100b001e0240c517140c4085413105090100384400084503012207800251540e00391100c4c01d145500712002e681c00c030421503881305d94020b6a40040e015105020300c00a08100c20002e036242240321410b01004100c10780a03030740e550b61080c801184140d00416401a03070315880e54010a0094102590f08080341c401d0f05800c100200c0080d40c180b031000300441c0c0c52021140f8120141c03595000780300b18490219002032230303d00d540000030394640c0840c540c0311990911040d55810301c4003100c46c02c210359001038000d5684202c000c8070040202081b1815100305245000003040e9948190241c0c1c0485002400961070808218 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 415041807 1250 415040557 415040573
    0x6030a11040c0504050414090d300b0925050c280b0106021c08070e090603030d0e0105040b010605090a0e0411061c050108120a0e0d05010e1b010804020d 67
    0x202c10000d200701000000380c0394549100700e85004040c0c0c10a1503d508000098905202d86c1d80d42441c00c200c1b54841c1c0c101c05c0107043e5440f6041c00451004040c5000781400c4540140150241d000c3d4070a05400030007004e1045411089601c840c3c0080307501c501a5007030341c01e580b54021402c00d4400c0340d005040c91002c10072624184008801e4551079021034042659561421410980040c00141c008001c0b800906520741c0c03034816400381c9410614440d240c001801840004403080c01d0b07102d0300d07140f40494941d85040c004c540b40d130010994144000442c0599403406000c00f518125107181c98000006219403152040d149161001800710022a1402000645041010300143d07106210580b84200c16a5003600070044d1011812200d9141e008410708002101c0050b8030000c11a005441e8041a03040d2803411070300c10100500349940307485158000715111504030079000f03150350b1809004411405001601d00c00e5609d03501da407074440c0300026004403a44038083c0c90080d00000c03110720321000a0046d07 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 415043057 1250 415041807 415041821
    0x7060f06090207080d1505090a0507090f17070902070206030c0f0c0a12031a310c020105010312110705060f0c0106091d011b110708010e01020a0806030a1104 69
    0x2050012032080d0301c40340d8610490348003210481d101c02c00016088030313092440c0980a60000703445614580f691808020038800b88005241c212820f64131000660b001c0d00907440040a0031880300718950103078856a0031100c010038114162040d03c100d05000941e014a80200c484055014005c503045403a2402030001d0b036003000207402d040c071009124a00150301d0030040b0003540c500410352510303200e1454101030100c0f00d02c50703442416140d0000380c0c00c02942320450f1030004003198600c05030511810031640100d442241a4418002e03007003002201d403040c0d05400050503280505603080d070000e6400310607284180d9200c60345405800640c1e081002d40f8005d4007400302c10318803030801840c101100e9032060850302c0b1a00050501507071003001c190100840d12034928103010040080100780c000c00d131521101c0d01c0c1c1c03274900390400031141107843c122581400003070001c040103402884032039881c02c40076000c1d4001d800300c000000d0f24440010910700d80001d01032070f5250000381862101d5641000c1c40050859 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 415044307 1250 415043057 415043081
    0x6090f0906080c31020306090708070e1e060705060403030e0d020c040c1403040f03090b120417090306010807090b040209090402190503030c070915270f110a0e0102030c030706 77
    0x1138101140d042c4c001101268010300a8500140d9074600300d400c001c0720040c094a00410000c640c0100031459800000700600040e00b151502d43d00c88081c3c0d01e20610700d081c0400d02d60080004296941080307000140c5500440c80f0341c4041c0300251481c50284d6580c1108440b50300168003481c2c8090003410254401824025140f400911010555480ca11650b1003901c0881e00039030104030303074020300d070b44900508082d141440ca1103151201c0315030203904120010f80003800c40305010398a015441c00c0f000448840b4500581940ca0365a50fa1000c0d503105c6a2034480e0110203403c01d80e01d81e0a5150a100320f0f4074410004242c0c10340d586aa0b000e1008240780e000000751440b8021102250944c0c00300050b02e08080303402c006100f40350a0182c0070040d6803c0d210741101402c5001d605100001041c020a010051420000b60302410084251000340500180b4040c00a140401428162401c50700406180800740c44a1030061310b01001203135240b02e10001c661403600240881c0300011199045001090340d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 415045557 1250 415044307 415044349
    0x20c0717011808040e100906060f0905010305010f05060c0f06070c0b0c030606070b0a0f1e060518040212010213030c06020c0a0b0405010c06090503041d0f1302040902041506090f0906080c 82
    0x2486551f80030480d90603401c940081024441403ca0080e031260314003000d0700c020300c0e052005516090510103560014029184506408a00015283c00400083e10f90714100803ca4009081000000d404002e0526058a17548880340000d071090001104aa0003040003400341c501d81710b0346440e43d4000c83c0010b8111000591142e1f561001e52035940554010042c6000c0055100d006620a03a0b0031103200e13a0029002c0c070403900207000054403080342294041c2d015203c914200e0340c1045010b00910507410b144801d005200c2c0080b0522200708041d0041c0c1e20725400320751910100b54100100302c4100c2c0b0511001050800007848070f03501c1030082e40365052103882c000c1840d80d0315a441b181035410503003000044403501103441c00d8450f40c050340590003a02c80301210a01d400d00c1010700486881c450800f0703014648904580003103449652041c0760510746a14107040158a5400c02800881c280c40313500c9400c030105c10085071900491090200700c0310504010030204803c641400142c0e240210318180e404 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 415046807 1250 415045557 415045559
    0xb060f10031d0105061819020f0d0b06030609011406120a0e24040813031b08010c02010b0321040806100305011109100e04020c0717011808040e10 64
    0x600d8900208003800a03603100460a200c49580c1040d0b000484440041241c0c10141409030075201c5d541d010a80889072401055550784d071041404840d0011144800320910001d0600d020200c000054900042200d200380460b01d003617010041d20740825aa0154030017900001007120724903a4034050165132020f0011800c0c00c4552040150400f0111009520907440f4802c400d81e60a05110030000320b6030b0a940c0090446042c8052501e000e0000c03c01031441300d00085204040f0b00780c43c41c020046038001c2c90051240381030711400c10b2528262017146115800d004040030110300601403c100c41d9005001090f22101d140052001d141511002d00c800ba1030400c0701144644060100f10301c1140c445000348806451864910308413000800c1c0100d0348c40e010b211940e219510705050107035031011071409000000c00080050b000317100308030101c2034500c0f9041d1700049210300d0244412800c5100c0000f004880c600c2419180b44500a030802010307030b102003009110780d0598118164110b199a041d5001e52 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 415048057 1250 415046807 415046809
    0x1030e0f0606030d14030411010e0604120c050114090603060f04020301080609070f0e0703091a07120b040b09060d08040914010e1501080121051005010f0801090506040b060f 76
    0x300466994803155a0000010003030241801c015012030380d282880c0c00425041c85d000441c0c854080908024409400140c41d032086d03a101d1351304d2411100d4010320103503a803607440020719205441003a0403952200c1c2800b0002e102c0d80124039040342020b2800030640b400310128100005a0300041010303034406144000000e5a85503440914040c0c005c5800405c00c078100b01c40c0341490100b8a03400340712010311848052200c4250111025001462420041920303256407a0815007280c0c03000b41204500c003080f0400900c25031001034410030000d401380405c01c06100d8014002a0381a80c43e023140c202000d0b038042943c50a160441c520000d00482c40c43d42440c0d100c80a0000391050f0703c14020f845482200107200e04e2080c4a10035800000d4928000c480d0a510703000a000c59070305101c4e4819502207452903445010311074845108045c4d22800742c80019000b60181d030010542070184c40110800d011000c600100b0500c940b045058102004060a503160390358800030040c0100240c2c0c21200003182c2f0f0500b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 415049307 1250 415048057 415048063
    0x60112020c01021c06061209110f010203190503060a08010e06060907170708160203191809021207020f0a03050306130219080919080910050f180a0605030c0d0b01030e 73
    0x1d04d220350001c00d16171b02d0480e00401580c0000a801406441c00e06e058001401003d07100c00010340c26a5031060802804005074214050324003180e50030b61722204100411940702c0d0003984070354811030f04271800702e0319200601d00701c5503194030440280d409580410f90600c2c04007900b5502c82c00914140381503606040707990300b542c3d9060301d901c1c01007030020090101c1607180e569619010907107480118244001840f002410440e205155030503c4a0790003035030391036041d00c0d4044004e00506107040d5a034460550741c8001d40f0800301c891400501841901d4804e0702004154092015095914142542c948800700003060720980c00704001c00b0341c20456040240e440301c0e15a61001c007035455148183c07411000d01401d2500c001030344107443c2407a400b2030000071449020381d01c040074181d40c2c03101a2500500291481d00c03e008410000c20008517207405400a503c400380c1e1800c500340d4409100d00d9032850151000d0100f0765411060000c00c3c4025000c00d04142c0c03010340500d60501d07000c50700090300050581 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 415050557 1250 415049307 415049347
    0x70f021f110c07121a0c1b0102161a01060809060c09011812020a0911160206120906090708160605070c0f0b090f0a0b0a050a020c1521060112020c0102 66
    0x8a484c681124460a10101c1c0071709420404248410528500d401a401002441007900e1540c541c2144c0500c42e40484007541504e0360014080305401c903403030250800baa90044000741c0518403000000001c035501d441110f509004840b43d9005040c582c407018240d9a007038000804042c100290f210040340901c0c035051f01d4000500d1000054244041c1034018485400c0c95608100980d6091080c6c80100030072040880d56280c1c040205409600c0382840080d5961082441c0c840c0f0000b05c40b0180b20708258045000341c06103a00c0c2d421210140d036610712082d00d86840741160051030511010070420039002d500100307080e41c442e403404c01c612519414540d5103804241c000340c180b503002152035407507804d203410f1001c0d5058049401240c100d01c1c05000314002c0c851a01024208803000c940c00070030328001c000b08503022030002d101c002080304174bd40300c010b150411200c505c80555101000c0e01c0001c2d1140c0001d0081c0c0040c0e4601d0410803078151510080c0d4010610101f2a660030440300890078000303109c200c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 415051807 1250 415050557 415050569
    0x50a060f0218010f140d020c01060b09010f031503080c100c1d010e06040308130b040b030a0c081009020319061401082d1b070b070f021f110c07 63
    0x161101810101c1d160200c00629101c0e040c001c42801c513030003140c0c0240c480814001001d50443d544c1a10070703a4400a0700407024441b150351700f0480042100131901025084a60702a07985100000107038104031309584d41c10043c090316162145080c00403070145001460044c009408032042c100c10a0345110031113010520310030011f1740304001da016140003502e901c51220024038103800c1803071038940040e66511940c4070091268200090294181c030380f070100701c4000c040414030340f6140c40d503d20582041d50f004464295906140c904895200340c040d61015004030030200c1d85c0c50120307007004440402507101801821614004010b0701035044054002c03c0c003d00b856030104814070030888000340c22010702600281c98118440210420030311403110004d40c1806485500c200354503440203240711900b00d91074160310900000b640b0001e100c0f101c0960340c0a03089c259110f412042105c2000c80c0c888010312000d10040c2031000042c108480d540e0082d244411200480a1810860403e15441e1840320750080d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 415053057 1250 415051807 415051811
    0x3080a0e0a0308040309050a081005130c080d08010504020403120e030f19051c050f072d1a1b0c010b0a0f0905060402071a1b1611100c02010804050a060f 67
    0x1300401d0383c065007100040505840c107021032810008001d0701d0f0b480e6200480403459403840040c01c00d000c403141d1a0242d07604480d8400707000d40c44001d51600c07100c1209140010900110000540382024405c403005c80741c2240248001020380341049440740308101551381e0511948040324120b4000b0712a00000352020440b8003907655140c40d1546c00e0900e046140010120202c89890602c1c2d00070341181ca1101040b40103982d20013092410007030119466590080800c1010784a1040040c7d1032050001d139405010b203460b107880c2c030101281003d0400c44035031040c50307548034406100241c000091311b4001c01883c00440d4180c0c040004c14075038621540200840300000344200032140741e612540d80c2140045d5030035403511410340c454041c2003c09803007100c042c0c00e499001071402a0200b402c4211004902e00b01c079902e48041e0030214544800d60019595042500c0e071761071292801d244085109000b9031520f5040c1943da030019940c0c0d0b00700500c00c2d110390154156400014000748140390000b1008200 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 415054307 1250 415053057 415053061
    0x180e04020f121911091b0d0603150204080f06070917070b0d090209101a0703020c030607120c02060124020a0b07020106030314030405100e0c04060b07171603080a0e0a0308 75
    0x202c12a046414403c0d00038a50701051144100031b41132180392611140d904256a6050340c14881d000381441e0748060200000c05c10282d2007820203400500c02c8503401d00032200e000c08404140e6071120016940000854000d0a040018001000c051203000d5041c4050340c426503a94400c1c2c105682c45106403403091075649112101b1031525000058000c101c00e0740c0484903130b007450000c01c1c2c074040020521103910b00200d00c1400b003600c200002c0401c5140a42640c0b00c3e418446c0000c0c0005020260740009941031000d0000120320002c0c3d4181224107118030010340444a01d0314090110481d130040c0b0441c011710003044007207000d01c1141805085190300005405195090081c01c202c200d90210310b00c000d040080c44046000080d0300d0f544514a04000250042c42d4503102e40341085414032960818242040052090f60030742c0501804c902510704444020002040b0201e180b04640c181c640d550350480340741000c40e21481c01e03603501c86280d200005000315001030310382c074004070490120002058001 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 415055557 1250 415054307 415054313
    0x504031406040311060106090306021b01140415020c0615060c030301031a0a0902060316030b031203150306011a070303140c030a061502211306020706180e04020f1219 73
    0x11400821138070641c050440782d41001c400800e0040340d48000382001e0740204600801d0a6059803515054131100003c1110364485030300c840010504603010b175014466500344200c03120941c000c03038000420341e801070001c2d0741c0c408150710300390341030301808a0704450305004080c2c600004000443c080d6026001003100c3c3c0100020180003803600a044010680c140030042005072500810780f60000c1007000f11864036815441c00700d0050030b446010725810300c100755009802400e00c400035801890710650003d44485070b007041c103580700000e1040030304034206156510480c0740000b014181d598400c0c0b6011925a000640c1120000c5041d2010194440000240607080d1502d20500d00240300030210f031824a40c1054020f901c6214080c2c0722485c2e25000c5101c030b40c0318220881116104210305402d03800f45511544000c1d940c50041c000e26002c120744054a400c480e000d903208000301c40080b81400d0083d590340d800c0c45089103056a503180c02034000500341ca01c001040c000001c844949401000400714681 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 415056807 1250 415055557 415055567
    0xe090a020f0a091e23030c0303190e0f09040f05031201030606080c030a1e0f0602070303052205031e0705010609050a110304020306070c051006030f0308160905040c05040314060403 79
    0xc1001c01c000740c40c2000800c80600c909901c24941c1021701010400716002c50086401c01803045c0040d60300d40400600d0018010340044120707000c0c2e0065480f81003000c1c0038810302041c0004000c0c104d0b03004a41b40b0000d000100308080c10f83c0c42500c118140c3e070804803560b82210a200080e00100c0d011612100d060150204c01c00800502c9201140101030b0103201d9280c11001c80b407051100a4491042d40500341482065080c0840b442d80c021000c40d41daa006080090050200350fa120690390301801d10041c040403208025443c0c180c1040c05140f6124208140e040b03030b0b8a0030a441030440b2824410b0001040082c811400100305440c0b0100d040d16281003018110346e81c5a003026400c3e9400c0c000c2c400543c070001100d90784400070341490250f2600d00d082492401808054440d6860b0a0500110800a03001508048036120b03442c1d1030056126901642c080100410014000410003203040200f840c29070400c03144841a8203003145000d03105d860380c40e001c0000b03541404003035000b0f00602040507406 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 415058057 1250 415056807 415056839
    0x7110607050a0f030c0804060e01180b063a0201171e0c0a0504090513290112020d0204110409020c070f06020316110103021312030f020c010e090a020f0a09 68
    0x180340405c0602090341c40034040b00c40280024006603990001d058241c0025440100000c0c0d5660403102d00340c0311442c1104001c0412140280103c5000e031203a440002600c1041414480341c0513407510540e07000d125803400c000c09802c140c1c100050b03c003240b000c0d08e01d41d5800900a00000c0c1b520030402e03000b2201c44954040c06040180c84420400021b800c4071781c003000341c1d404e407403101c030b0042419220002c260445030028200500b0600d26898091509089138140d81e601800b6500014a203a82e20801103955141080000c0e4100021001c00d40c01440c055000b41c0380400d1040056003010b444800c402c040b600035145001f80c0f54418481440030f02445c481d8000204814401107280400d42900904018525440100304450384100b16006a0081d011f0307800980e03440e10741c0d400b05684c1714ac1c008558803280710150003107610501101c04c4984003180c2c60f049548180c450200040428041c007200d407a00815009540707509110b0b1030300030469140103002c01d05a56a8281c6a1410000c2c240320328182 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 415059307 1250 415058057 415058087
    0x406020a020c1e041d0102030702070f090b010c150608010c030b04060e060d080a0203041a03420d08070f0b1e0c07032001150e06060d0507110607050a 66
    0x4020190f40300c00103c50002c0c41c508429500460045101040303901c50003503041002c01c40c1d50010003003180045d40000d440c021620006004041240d0340c141c0c50044810180c42c88e40044d092100d2040864a804920031215888500006640d5903030b629060031a00c500342d070f403000280c035100544020325080c0207040142204d009240c01c43e040400000361000004113008001c0b0102180c841320b100d0081c0165001040050801810520641d00c0c00710b060340103c8662800c6003520540d0810010340300c42048146030782d10104510302c0c0d044900301d4950b40020300702e99801140030108200040010001d0007040d84200078400141d0b6441ca0185808070000700740b9814030313410491240031100300c0d2020075044804c40d001e155682049003400c4840075803020342c1148200204600e07119640c0c0c1540302491030f145000c0041e80c00b90300d4006c440380030030302a034426a000708107101040f03403107100f0350003a5044072480c18440c4400c03610480c031600b440c008640c8140480c3d00820123561598000e20070602e1680 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 415060557 1250 415059307 415059319
    0x3081809070e040b0411161712100902031003020108060a09021803010c0807121127040b0402041202040b01090f06050c330402061b07081e12160b0406020a020c 70
    0x720801065880b1f0084140c6000b105c80f001115105110b03050010f1800304076040da000d69650600980f080c0c400405841300200d0a05244000888007114800e49000d0001c01c01c9001c0b00c1840d40d001116080303030151017694084498640012000094401800c0e20320100c2d1915210340c0303101c01003500316844210140103003c100d0041280caa6407000800d1507902d6505070001d00d03100b2002c070101c070038056100b1070b1851b031025031000300c0001d5000700121480311080f17400740f08552070241440164003c52140200d01c651a071031100040c41c180c0c0000c0700411040c035120b0f031203d40c0c0e2071111744101815844138001c0358002403200ca41000601010060f68000c5040c0c50b402c1c0c20001c4002620168501040140300249000c07604540e500400c40b1304200c17034021140d442c89215103030541c0f0781080b4810007105114254450103160203006140d10305070780000140400705882407000b1b0301036200510803042104800d40d564002401901401c1c001c41c056480161559148400a841d0800700341100380f00311 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 415061807 1250 415060557 415060571
    0xf0103020a1202030a060302040e030d0c02030922090c031a1506090d050f030a0306261e0102070f06050601180509010510020f12120106081003081809070e040b04 71
    0x142c100c1080848a4407a000040c1c1c0d90740e95102000080015400082d440b9051000149607550000081e0040c292005010464580c00032416a500e01c940102b2076008481499003100140c14030301030306a4113400c900041580c0f040c5603540c05949201d85c104980d910a0414807146070200200d12035489051114846400d41600700040c140e40100141030b0f2041e001724045004100041c0188489840801304a0307403903043c1103401801405181c02080100310b200c1c2c411607401c0343d00e40c01e90381050345900050469140c442c550b40c140083c0c1074209080541d002c20080001802d080d070050100f80c013030320300010705081140005212212003582200d007110568014841565100180350460b04103c88086c0f0707108600d00140e0030040c516504403468010400f201100707903405401020380410782130140c0751581c1c07200410b0394148410755080e43c8225061200b400000d8103900188141c11032400305090000580e0002140800105e50f1240003c0c0800030000c00e03403c0500648881c20340c100c030140411 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 415063057 1250 415061807 415061827
    0x12030f0f070e04020313020a0e180109020a0501031518060e0a090507140d08040e150a060206070507032f010f0e060613090f030f0215040f060c050f070c050f010302 72
    0x2c1d00001d61644036607400800700340c02094130401c54401c6a400b45c012404103a98690782856464121000504030303e840181090494042c810801040c0e0700030240d5007401c0c1081c0c011802040f0000f403001d6001402400890442c0604001c00e00e1404030030004648241820038104202070007030305220120782840c0042000400203c1c610054584500300504240d400800095541c0075480029101c65800a40071030081c0e9040c040300e200380b442a03151038009030600113001f001c0015204410058000c0300109801604c0b810040400c140203182007480440c80603c03d0761b5960900a0f1421b000e40d100c0c0d0414010182070145813151030b20701c0020030551003170044843c0c0f81e04008112600c01c3c1100c80d503003100c1402a50004c000f0320303008201d4446000c1149030140400c030700300f0800340152192042054541460105541c030855024250007520044c40e500e040c09041d51030103450038410140542401d3304d100c100038040440c02005000c10079843c02040c005001d111032465410507004014010b00 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 415064307 1250 415063057 415063067
    0x81801030c050c030a18120c0e06191415120402010212044707030e060a0c0b060d0512070212070f17070b0a03020409050a0c270812030f0f07 62
    0x224424508210440020314104441c124020f03400c10701c1c0002080f04911f0600c0441c4901c8404d94007002042d40054546400300b0000d0b0b006030b00b20074130303019410009024008120132009440700300030b404183c2d060704013410b42c510741e000018000039411241c401c01095690400c1440720035120850580d103401d062102d103400000140c05143c2a0000b909100f039085800006407042418082c0381d02401c0c88032400c03110440e80d00c960802d60000700c0c88e442603101454541c0403100c1030603594488a0095041d951a0903aa200042140e5071012514509101040f028030860341d00d480c46c03115041d039403c003610400121524024803440d80390701011003070009908625110095444110400744d00d50000d405052038000c0c5600079002000001c02c481140c260107030068002d84112040512495403092180001c0b10340c100b0b95440013405442c07004455070100407241040c04a1007000100164032004060304d0885102002c1128210000821015803000d07625a6088a0704085c0070310103003080040288 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 415065557 1250 415064307 415064317
    0x7060b0a092a120b1305070305010512010e030409091b080c011101060e070806060c010f1506050702030c120111030c0c0706020a08040501030c0e12010c0305090a020904120903081801030c050c03 85
    0x2982c3d51030101101559443d2a8017400144000c814040d91410000c02800343c8000e10416001750000e1140014001d018081d0304c107603843c20401181094034000d00b420242c482e13018241c8015640301d000300d405401c814a1000606060001055100034110004004094030821142c0b103900d42281409840710302c01625401094500d040e8106407110000a03801d48182200729a841d0300e0051214070040c0c0d65040524902416050340b40c4866944009445521601200a40c5900003006c2d030032643c903083d880e800103180f444000103418100318171240c5140d48244c4515484010116403001c2070002000000e01401e550710140845401541d1507070110702550003018107040e2140c400c41070a5224103034604540340700424910f50340881c0f03441c4500070a414203004000038181000990803003800580301c08143ea020b0302036180d41d501c0d5140c2c6001c40c3c5c2400c600704c0810000c01c07000404070312600007030144401c400c081540c0d1403050f0350014040307590290903501804418403550b4400080442990 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 415066807 1250 415065557 415065587
    0x120603170702011b06230705340302011a040c0c03030c17040b1806061507110d03120f090b061c1b080f0f07050607060b0a092a 56
    0x203611880d042c401039601200480d0036070f00100c030b641d40e400207000054200044028013041c143d40340140508416800100486184001c18010444001a600c00700c1a40c40b81070640c03120105400e4540c1c0e036240c1c83c80740d00034041d00140c0d1a0032034100703020f80403e070781c40c04840e00319801c101000600c0300142072841618805001d15580302c624480d0140507001031030f03810103224089481c030320306450102880d00055030450700c0142000901c0caa11310300000d0250003004010405c0040340c00040c1034011035841401d0480d0006c00c03908244e002070f11031040e0300e22910310035118078910391003040360b83d03088a0ba8060081c48042c01c02c02c035003001c43e15000c1e240303030401c0c070943c1c1107240308010300c120920001c0518801001280400d10000041e24078000c14426682c03110103583c80c002555106945d5111202c18070702d921780005900700602c1c5000e1000b408418401c80e008503110402d00c00050350026241d00c66038504c0c0d00c1d40d40e40e002c84c0c14801441c1034040b2211142c158203080d801e40c0282003544a1400b1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 415068057 1250 415066807 415066853
    0x5070509030124060f120207030f020c0406051e01050408060124021504150b0901030803160207080c0d05100e0a02040b06030708041401240e010f0308030406110409021306120603 78
    0x1407404074030406e03042ca00c0c4030f403c2d44295610219850024241d0381400351240050141c0e041c0030015103480c1c0034010803218000d1000d466451000c207400041c41079601c0060511400304070000d80c039002800654002c0000040d90000c81213528010844017800031400000c54000002603070b82c10552041c2c003a013041d00401903203008103400c10301800800d441c882c4140e01840300000003003000044402180b2031030000e1084500745000c1c0505a90f02c241e6405484010b40054000041d00c2c1400580500d4681c091011280991401d80c0643d0480c2e000340c40102c3c190308158141815400c060103a10010001501e59616500d040d680041400d84081d2004000c2e0401e0312481120358802d401c40c401d48502e50b1924002101011a1188041150302c5000811704214000090610403a0300c2e800459070446032840c0345903225a90392000b0807640d008040504400e02002c07a030880c10744060003c0205408651130f405e03050071800f07010090660b40c0d01901c035007030040900020720064113a801c809401417074 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 415069307 1250 415068057 415068077
    0x1091b0f0b0f030a0b120a150915181709180c091005040b0f0d0c080402060318160801231b0903030d02160303060b13121103010507050903012406 64
    0x2211000d040d101c02c003294403244000100b54020001f25060000707610841440081c1604030850b04199205c4c04e6010b420f2040015506042041980200002c003c540c81c0c1182a11101e41d6410840d501c0703004036000e44440801e201c0054180610441204144411000c600d850152624501ca100d2400313414047c031815100c0041c4e00d4040c0050700c1c050460b114007140c803070341010000151500003e100b00010f50510350a03001030382c0101c404500654018180915580d03400c01420304004240254007898418403104640200c00700340400040c00c920400030030000c0071004040031421b020490114040305100074000e03030ba031030605140e1703004e40c2d4012003e4490b03005400290640c007038002281215400003540c05c0001c0031080d00c0300d1826120340c5003007000544904008425000b05202c0401d03401c810304d42401040c0c50a10030000c12407160384842021548180801c0c00d48405883d0b030008507401048640b1540b40a0082407e04000e00e00e006a20910310741090444d01c003071f445114240145c2a0b0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 415070557 1250 415069307 415069321
    0x1401180516050d1e061a040b061305010c05070905040b180105190f0b041d0601080c010801090509210307020d111b03031603081b09090a050c0c01091b0f0b0f03 70
    0x10790140d107400100400c494045000c2012046c20b12840980c8620b25000b04429035292810031b5070030441c00c0342000103006040c40010360303014aa584d000d40792132080c500d001036494441c0c0a0148902d104032044003107800e140b0090a56194182d261071500d9041c9001c102d04600d01007041306030182883c00200e2070404034041e00004201d0b08a06981060401440d42e4544078225010a180d07588102219071030b80c0d13120445900c81d042080c2d0a800038490800400c90050140c0185801c050982d0603109c280c0200401c5d080303041d2100101d404255804406c00448680501c081d60302180315040262191000391000e6803180c032158100c1101110503c2016a0784c0c80400c2038651003032140026160702c45c0c850801402e40d08048500040400303480c029410711840140689030607180140043d2401c3d1601d810303041c0074010085c0401c070340c80002d002400300c4400c2406035502d1540128120543d01a803003140c003c414245400c6610440504101000030340003603002c841d0002c07000034045849803144d01b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 415071807 1250 415070557 415070603
    0x209030a120918290402091c1a011802070804090c0e0a061407120c02030a1a010909050307030f02101109030105062b0203100207140106060f020d0c1401180516050d 72
    0x81d1007d40c000b0498480b500d0340d000010b008000c9035004000144d421402401c016a406909000304032802c40a00040110441c03960040d10b4028865a06982040c2e10b61089070103c4268450450003e5030031010fa8845040155951018020380d1506440d20700d5001824903140c400c00c00c005000d4a13040300200c84551049a000144690040541c1d050509904002d00401000403108801d4182c84000103814012480380303540d603c0d44a4082d6003001d0103524103452000c60b500c922801d5015109034111024281d21940c21003d80d07000c65180c0743c05242060500716180106054019420365607510711581c5a8440781c5103203000d401c3c07200410801803020906081c8409a00d1103034500100e55002041810340180b44219511002000065a41c0408494150351f146100340513802086008842c20f21518030f07100060f0003401c0380ea5040d002c90114030308446180060850f0010032582c0c05041080a001c00c0d00d01d42c906600041c2c0f0241018001044800e241030020710311141e4440380c0088608007 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 415073057 1250 415071807 415071817
    0x2100e0a0501081f0b03191407080a060512010c0306050312040e04080c100e1506280b12040c06170f07120504050622050d030209030a120918290402 65
    0x81c0704140304c0b50703614010fa00140d0803c4d1001c800018900818101c40201c5225903901c041c00c0e110065215116440c06907041080a05856281354840030042415250602080c0542d0400000065000000f041c002e080300e0312500b00c1440380d00305090180c8580c856409440070768002652002c0e00d07465a207081072481c81450100d56440c0522070818001a071180c1c84040800010801d90f801007501000c40c0042120449090350300400e0070341d804908005803901982100080010108126214a607002d21034102d103c00640c1105440c2c200010000301c000c91900a1485080188800b04141d011058080c0010100c0d1968010040041c1d030451140d10000c0069030941c1c003c102500b0241400e5031a0601241c51a20300c00e1600683c0c0000f401a00d40c0020031074004024040020013243e00310042d5020545103541440740c01b0b860004500f010b00d8990b41064280c64001e0380901e031490a5040940441004520341e1828580e01006500d0780ad60401295030808042801c3c1d8030040000d0080c051 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 415074307 1250 415073057 415073101
    0x314060306060103022808220b0703241203020115060c020108040807060e0f0c120c191a0306091b07150608030d051509070c0b090703060507030902100e0a050108 71
    0x8961902c0c2c03034468101503641c3c001e64020180f4400c4000d0504002d008801e80b41004040c2489e40d4000b42140c1d102c3d50002010084101c1c071050170301044200711940c010550452640b8495030894003041603024464003000d40031018010701e226240000207814282e050030040c5c18085110009410400350804851040350b21010801600d02c0c2d000d60b080c0c0e6900781540c61802071042d00103480c81490851040d42004082c040142400c406400a0000540c214880030642c8100c0100c0401c0703010580b0003603914581d0140d800c40c3c8920300502081218140a4400160300e40300318071249400030324034102c030341190b0013105c5c551a02c43c0e890b40850082446911031406400003040d2418550003640086014220340360807130541045420801c50345003015500c80d4045001407488a001890808a0641c0107058070300b6075445503502d84400d41610310490701040025610821181186460700070001d0200305880d00102c000f410382c0c0420b00c0c0055174080c02c0d040c012144e00040643d0882c0c2c0d202c3c069044 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 415075557 1250 415074307 415074367
    0x609020a02100608070521010b09040b040b15060d05090a12090905010905091e030f0409050105130c020c060c010609020703030c110609030a05070320030406031406030606010302 78
    0x11800c100948407100e000708020402d081240000c1c00d004005011015944010803a82400d074010b962100c04204100500d0703419525160340c0e211650714110040d00c520300440c01c6520311b1a062401c201100341c010040310035898280110b412a40351482595810304d100e0368000b603561541000c032413509403409801030400c203020703080740901a40140080c0440d0211081032000d81d898544007000e07550102d504403031a501c40580842d0507054403011465013801481600d282c6840c9460140c09540300341c1051540c562194010449401c00d82c4001100c00003c440400100c04080d100a45500d2481c04a5204400101d20314100c0301080d0300c40710041c84003800440d51510b092901a01a115112059002c0790480800861821021070107510880d007050103141307000f05a01081c3c44030340000d40b00743d0420a0b218081012070790101084080c0f210303008000c5445618100d4000e0a80e03456207007444090303651109102c0c2c140c400041c2c054012409080c00741e19440d00c4d28805080c0100303060030b602c40403 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 415076807 1250 415075557 415075567
    0xf0f080340080d08040809090615210915061009120b060108010f0b030112140a030e040e0a3206010609060f0813020f0a0506040b030f0601020a020a0b0d060902 70
    0x5a210195102210b100c41d0954001c2030700200191813080040360041d001c8102002200c01628000400940c06000200800c04000d140706520001e50003e90b500318007808816255031020805600340b40d40004510001c2c582c20b0f02c611030b8403ca180c0302624a034090110103142c00a10350040302c5810161200e05075021415495040c800c18030b44041d00c4482c045505640081100a00480c0704c02c15101c04101c0c1d43c1c0746900e0031112403002e4080110030b45101140c2024401c0c0d00354144408031b0b20340d000380d55060002441e02d08100423905407400d41c41065000c0842880003421060f90454440e1600501400d8158103000c0b69590300000d0803c84aa030040b100042600341d0003281c00030a55030982d48000303054800c1c98040d5001d00d426906400c40e60076548401c40140342c8421043e0785850054200410b013541d90000c01c54980084d04a07000030030000c4100a060f00170b24601c264802c00900c020116100d2540104440120038028640459400030701c442220150f60800d1006040e503540840d500c1c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 415078057 1250 415076807 415076917
    0x28020c0f010203010306051023031609090201140418050405010f06120c2c0601110d0512090105040305040b0c0102070b010311090718090c1b08040f0f0803 68
    0x2c3d4030900045030507514010104c5c1e104600c5a9480c4281d9070b030501e0000e10703118000c400600c09003507ca01c0e580d241c8100324070160018401c0104500030544401c0c00b2444c10303020f200252840800b0309a540c1c5014044c4001c0000100c0700300301e9001e82d0441c0300c00103103680b00d5007001409003400c00b825146483c140b02000a40d070416180c00c42d0f0715809510340346803140e10390611a01c02003160f000c0c1100c40000c080002c0422802240c40c5030000c005060610188800710226801c0880c0740801d01d004c1400800e404018415a0141a51164819000f0400d9103007907500604203000718000c0842c01c0038040380340303005a00250304071615582c01c160810b07010341c0d482c98a010b842040c900068041c0c400180414607003809410044442141c412002c0b00c218101011a03000b800c0f800203a4042042d14071407042c10f20079007130445031441d0103041510740c4d0f0303802c2c4134200600103207550091000d6203d050b01040951b0f80401900d4000b00c0c00280740e04400c0d03810303c030450350381281c124070016024992103c5010b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 415079307 1250 415078057 415078061
    0x31b02280f0503130605090907030e03070b09030c01180c0e0402150c03031b210a06031e050c0108010e07031508030307020c0a21152c01110328020c0f01 67
    0x4001491344248a00f55241c1c24200c0e8540a1546503903013103a8140d02140615000e508400e80d41408002100d0400f94180c4400000c00c0c0700b65840562a0000203211a82200030b0003210102250004504401d11543c1d032010859101c0744030b80840920081d001c41c08540d07e0324000084842d60b003036011303240e01000d003000d1b80769441620354540301c0004080d600844503465041d2845c3d680c00800800b42d100c80c14031000300031070000303040c81c1000f60b6840005c00003450071040d2103038000180c00d0032060f610b49032925a241441290a56062100807401081507003802940b9a500034403524000c180502c080940c4240291250800d00081c04003204100e01154001078200c1d4010040361040321403a540c00da10a842561311805007022200104040c0200341003545641091011351f070700081c0040b0311f002456594004484034141d20504e2601da625160302401f480000600080d000341c0ba40c04c01c0c00460180040e0800c070081100c120030080561982d20390306030303a04081684280c42145001541c1980 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 415080557 1250 415079307 415079317
    0x80d0207051c05030304060b1c030201140c07050d0e010203072a0905010503070308031f12060e0303061318050607050d0e060c0f03040519030906031b02280f0503 71
    0x70181181c0c0b880d040001210450b950420794010019518589070f640340c01026040750b500103038114001d482c08041c5802035000580740d240c0664000034106034480c005840c0f68001609545079030900b072103c0c00204002203132036039419465050030b000c4a050800182d045020b0664040c0c009022140071004480c0c80c441070079607035542e81594a40554861480f0f004441c0c0a004081d056440f103c03003400010700101c0215040040c404084e05a1580d1540701c20248955400040003600310720801c80401005008102042c0902005582903240003804500400e10b2100d070700d040152100e0300d5070900d00c8112090303100560407800b528003500e0428009001c0358410b00007989560315244100410b002d010036154019840c0100180c900034501110041c113803c0600240c80c82d00414001c1012810528406200688aa120030894034138289001e01100d0190300c0b44204040c40000007140e850340440c400e404440548003503900340c07a003103c0003d08100c80d590001c207015194642c0ca8107014000020306 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 415081807 1250 415080557 415080559
    0x501030803010e07180b25050c030f0304060e13090b072001020415080c1c0b0f010f0f0807050c0f03070605060102030f031911220501050903060c09010207080d020705 73
    0x84034545401d0421170312090303140500540310901407020b000c0c1260b001300510b0082204810018100420b203030210818a408100711100e620441468030076040903c00c40c040300b181c03400030794201813070904003811600102840920414094000d0b20030641c0c5641714802e103d0300a1103c46035441c255401401e00c50680300700b40001e00d15403070072200741141402203e0940b4122420913140f02e910820654040e940506140e501d06814000078800290700c640e5006014004c541c041a034803200030610a2007040d0001c0b05040180f0100ea00541030b41208202d185c0e01041d181107260303039607001412542c070b0090b84255401d5000d03c1003020307512000000901083c42c0900020400d03074540c1c1c0016a0f8a10a00e96040e0308101c061000a412100080c080c100f222511400803841118205240d02140d100101083e40c02208a500a0000d81845100c402820080c24a00e2814941e800020340e9803000512075022400d0015484480380d100317010000051289108550b20501c2400f0040d40302e0030540111 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 415083057 1250 415081807 415081829
    0xa140a0206090c0307180b060403021f03060e010302010e0d260712020312012102040f051b04050d06020d06080706050d11091008060a1e0509090303101215050103080301 74
    0x3c242c643c9400704e9180d04030b45052400d41704030795229402d03030064194200a503074007800500c80003016858400c003080341d07a8615095060024010f140180480d009504501c001c20302c140010f00c0141d81003c0d11600d8040c00f1201d0100c40d0f0740626100b0700605103442110701044141010040c440300a0000d0071006100304501c1d0003541411404a981b0b002d030b5442030b940d03561914010400f0f203c07245250075845c440301c81e00220300500c2c0d8001c50142d40559403015001665001048600307544811242a00c00c02407112a00d400d14080c0014840903a0306006010254000344215810340d460307100303400524154003641c100f207a5911005d08944c0000502c1c0c0034480c00c5ca002d82040300c2c030380021a100b21000500005005480d0001110b06102c01060940c001c000179001240140700b00240449450151040303d0003e424101407000050300a0050079103030f403051052100d0005207901d03843c2070f504003004103450744100b0b0a010302c6400e100c4011321903c500d01000401805201e40045041e80e59030101d07 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 415084307 1250 415083057 415083073
    0xc061506050d0e030a17070507080310240e060c1905010b1908030f0d0e060c2212021c06050405030d0e0f0601092c030c120712050a140a020609 63
    0x103d00d071207200e4840c25600140050080640f4180480030050700440c1920300107040803d55035401401e640141d0700c884101415107400c003c910300c9101402e130010340081840e2265203500a000d4049040030703103014491440440c0d5100b45180070400d9200c0c0c9940c4c0400f142c2c052019090950082c2488154035008007440104d4040d110380c0c0070b181c2d00c00c4864810013145010198804e0744000d4001e070300300c0c080302600c0340d001c648100d1041080b14004c03070000d1200b45c0d450101924805451361402c640003a03000c5029010400d0340825081e46280381d4054404407100c5500d10f07030b150315041d100d00009006a1501060000f4404000041d095103413004200b0802c000040c1c040654420068a0f500c4032988402d005010b030710341e55000807548071260740003034034041d40d411107041d0384080c02030061380c03e82d101181d0100840820010312980f55904829146001c07a951560401850300d4030030b00e03050040c001514040d4a1042d100d40120101701c000050b1914040c010082d00c446059441c40240d20840b08 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 415085557 1250 415084307 415084331
    0x6011107030b070809120313020402040e041209060912060b0406050901140907050c06060130140606071e050c0604030605040303050606180f0a090509030301150c120c061506050d 78
    0x1a0b08070004034131188075030848c1c1c5e460589100b18840107030201c0c0c1154081c4000280044001c1151380200c0c031441180d4207101b171a0400038041d5030154001c86c200800300200b00032482d02c01100310110740e00030700d010130240080008078000e0b02d800c1e4406508030511100008084108038420f00740d00400f1158000507480701c030b0f0112071900a034100307540036401c0280414030765801142810070031411a181400c60541c13075683c003000320f01c01445050046898428103034061000090150740071004541090801580ba1148000000301c14000200c0b400d500e4162030601608100b011074120000b003100303030746070349a10742040a00740c2581c0c200c3c0405c1c24803001c40d4081c544501a942c0f901d0411158007460384074141044540c212007141c454000e001130b00003090030b4200e8040c240c8914134202c01140e0701c1d450074006a0720603000f503988000b001060281000040c125181d0803010030528a040340c880c400d00c0c10054000c24244000e41450040f05400040054108003c2c105072100c0180420520003896 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 415086807 1250 415085557 415085563
    0xd0203040609120c08060c0a110d1407030e0604030f030806040915090201110d0807020d0f0504090c030b030d020609011109030c15070b1003170a02060a0506011107030b070809 77
    0x10290502150b0b51000600c031080f15902c80f43c402c903004002e200c114960340c40005082a009940744503840c9400916054203e40022550200f1030b84d08004101d10801c2890091030126400e140100601d00020454181840703018400080070008205030382c1c66980e441c001400e40c040311012000f007240140081c08914003441641c00301500000d40070b4460700c6c4000304400038040c610007281030102046010740303000010005022014103603120110709050081011f454003400054510822000c2d48211602c103905c281980d04580791400041038200c1c100005501521055403500d8041c41401a006400c5600054560150840310000c000d0a42802c000c5d406a00c11421030903095070120245003d542031000c05246c804282c08400e608012640e03403030320526030f0140d0f4080c1001100080c1070090041d08509082956207440d0060316150303121030041c0d12914020450440f0310307514400281540d000f0006034418a000d8800d4400c0d0503202d162418180009962000020b40103d000030800300e000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 415088057 1250 415086807 415086809
    0x27030301150f02070302010e0a0b040e04140a0f02090604060305060a0516020d0219030c020604030605090c060316031a060f0408070644011d06090105180402120d050a020d020304 78
    0xc3d8080c140303a03810740d001500c510b90f40c102082c0e04841500000203000e038528000d03002130130b608080c00c012b608141c10541c0045102c0040c580306030304005c21070380c0010f4440f0030000c40540c0c16244000940c0c2e8042c005802850240e2019000b03028010800c840003140e98020751240074140c4e4002e0302008a114203e81c2ca0380c0110440d0056070083c0d02004c400003000c0c1d010f940e8144249048030420350310b45c0c041203807a00151700868800c0d032110107000c0f13078803c10b00c0b020410001c00d03034211341140f526498420400c0c1d9043c82010a160752006800010110907440010401c00940b00c1d40d501c0001e175609415030341c031600c00c6048500880e600814200d105149507616002100c401d0700a5510414203a1b0300054064001c0026032031b082401416156960102030080c0759202150035640210750301760900d2070005040c940310381280c00040c0700c03030b655040c02050140c01d42d5590090950701c5101080b00d620b00c10240500d980b28040000f400580e01100070b0848003029130030b44108000440b016680e80c015 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 415089307 1250 415088057 415088087
    0x33d020a0509031b060d050405010209120a0c0e06060d0506040f180b01080601060c08181c060c08010f150302070c080c130903200c0a1e05061806032703030115 70
    0x4104081c06c3c03450703ca0703041260440c0c001c1000629000c1d03000d000620316411801d18000c540c016010400c1807141d051805001000703812580c08442c6000b4001035008d108910404800641c0c420116240b5192a030100d203400c0341035581000004102d4001d04d8850140c0c030f0007100c02903090000850700010204859048815540f40d074120f1800759a100c1c64560080d03064220b80c0c0c00d4105130010381d40d803400410703008100b40f50300d030014000d00c0741450001d44000301595018480c0480c01000351320441503012049600c40f05070003c0f00b16010030218080d102e4020b001d00720488433400450f9100020642d0798446404a51780444100919048400d941100070040c000c85d0000401c1080c0300c104015a01035184a282600d60f03070350918000900d41070031600850f0503107038002c504403107041c48400000044c0204884541c20b0440c281901000020260700550049001102203101100c601c0306100000c801840e41c80101286138a240f590b07a00244211402c20f40100780052500d80540300c40b04400f14 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 415090557 1250 415089307 415089319
    0x18010b030312220812041a07140a020304171506090c030a05070c08071b090608060103151d210405011b0201050d1811033d020a0509031b 60
    0x20700c1a41c284407076110220b0b400f95206240800d0b07000101458010182e180584816409504180c180040b00c0c1510300b500801d00c0c031006061100141d00f00410500d48403881c02c0d116510552030200b281113005a03400144c030a486413461000500000c950001001c10480410f48a0b688684c00c010380c410058500c0d480e6100e00b080810700d405020340080340c1c0b01c402400d01c0c003038074402503403045c043c1c0c0d114075000d036558403c0401c0305511848451008000740028032082c0140740c00e10018035102d110621000b00300c9021005c2030100e154a613000030360780c1414010442d03100d16002180c280c583c1d61041c4d00e200c8040032216201d107001c1e0820165001d40f081a0b4071207a8104e41c503108030144404118007039042c010248420f0200f071130503000d0300800070304e04030100c008201c03545014a280604291a144240c108540329080300450b04881d4000c019440d55610640103144003040d103500e40704490a95150000820b000d0b040d0300080100380c0f911094003143c6407280304c420318803c44a090461168408 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 415091807 1250 415090557 415090561
    0x9050f04090b0a0903170403030f0c050c0318031c0f09050411070303020309100510030201181a030a060b270409050316050712050606030601060201020301050d02011b050618010b030312 81
    0x900303e98090400d107442410400254440030a8181025a0498046000a848c0c145070821340b203050150700820980b5007085070510540030001e0340c990296441e50003080d500013101c410719076400c12404070380d00c1034000d00444440200300d0081880380400d000c840424011000040c0b02d081c0380c40384130012107024070241e041c03082c00c3d981140650b00203004400c1c280318443c49032a60792039520403a0301409010703070129101403035480050190824681740e0034040b45101c004010801c8040c0c020307640c002070b10980c5541e0341d46500b6040e00400864200102203080030a03900104080301542200c104501d490007442950b81c0341c10042a901070305130081c03041e0014881e43c01407023020007590030001d01c5801902c918036161461140754005890054846c0d034801024011241010b010260142c030b2544025840c40d81858040765031103940d000024100301c2e070004d1000c2e00304401d42c645144903602c40c0075140d01e03081110000c04c40721292011800c4a5280074500f554034a800000c030385a881030010710702d0140e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 415093057 1250 415091807 415091821
    0xc060e03011e020a090608220302030c0a06060e0619030201030b0604050303121f06020a0308040201090902180301110c1e010b0907080405010506091302130b0a0609050f04090b 77
    0x888804498540542d252510104240034401c00591001d034040b1005840b1200010024080e4400364008400c3c445114144071603040780104456084030480c406282c144220300d022407071849444a4402a8020706180c03c00b00a8190400c07400c869140c00781032080d0310f4070320421401e541d071800710380e000280c41441000107500a822001085000900c1c4038100385c0c4d5200400d080da07002e0194490a0f140d031008100300c004420705008400b050b0804c058030360302d08009010355251059100a010310594a0001e401c5a00c240c1c2c141c0064a983c3c903055440d52400c985502d5650344010400d0301c81d5092002c822000a02c502c01d036041c1c3c03422140240360380b48050100c0783da445040103030071409540f00c0900703240d640c4511080d140943c080b9070395024640f4150a059084034400340c8280c0c811400a4103010300c00100d99850303050aa01114075080d030303494800d0a58018001d4144181e00a400ca500003d24140c0010014044034000e89a2500c0c031910641048202c81049100400c9031070100c001c2030316 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 415094307 1250 415093057 415093067
    0x70506031f0f0b0a200d05071a040c09020906073003150e0a060807031a090d0e06090d0506151f09060c0303020405090c071a04110d0203070e0a060e0c04030c06 70
    0x40e10242103d1060056980e12101b4240707500e00080101182001034494200b00c03400104401881034504280c1c10350038141c5d20b158116105100342880c10f90042501c803440d56400e4102d490040c0e002600005004ca10482500c6940311041084500c450969022080c2c45c044d000d1210b49088900301c0020050802d102441c40c8140907105040716552508081031500c020000398010b075001c2c0b16281da00010410300e9250001006001c0502ca4000354068101c0d0b42d0002901011000d00701e4041c3d807110140401300f8802c200841380034201d41310702d4086c4a81159403140c248020641900c410f40d402809010b900c007858030604a040c0016158601007081601c24091031409510901d00586032075942c00c00114000c2c0192101000f0400c001130b00d400b0001300840d00c0c01003c907200d02502984c541516a5004900d00c050ba19002d10039100720482190741c14448013000d441c4c0300001c80d80074203050b84440001c201e107005404138080c0000201d09400c41441c1520126a4040d96074403131103082c0304044034 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 415095557 1250 415094307 415094327
    0x6140708180304050a060305100801020c0303010927060605040b01090311060f070602030108100b0301181e0609081206030f07060507060b030607030b09070c0c0306050702070506031f0f0b0a 83
    0x201c50100b48008103e43c3e44414003034004000c41c1c0e401240c1414112007160301214164041d500366841009403e0103001c000c07090b02d0444000c0c0b100003407090140220301680300e544d07141e02c4070310482102d041030030000309a00210076030b08141d404000500c07010005480224090001500c400e1128002a50600e03040c0e009010b60703925955102d040c03008130355901c8241c2c0c01c20f0300444029000710b03004500b111818030800c0303040e100440080c80f104c45240c44012501003590b4000e0851085400990245008002c401c010654001c104001002c00c60918145c5600045844010040c09801007822803400003001c40d0b2818242001d800c1480c60000181c46a600c0290202c4149850712030104040d81c040c00181c0c450807464901140064003842040b04a0724020100c80910480c50148404031724a410464156039100c840014103441d0110140e28007441540069407114001041205002060245110a1442044614a00b0303214a5240d812801038010148006070520203100c04500c100d01341a = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 415096807 1250 415095557 415095601
    0x13050406110307020606190e06010f050415050702120105090d0c1a01080a060e121c110a180f0501120c0e0307080a14030c0a020603040602131206140708 67
    0x5840c1d0a00400e10800d5082101d1074005a0000340400049084c103003110203d01c141380f44031420b050b08100d200c562146029101368100000400040340707031400703842203602503c8103c03600800c030790507040001c19079070010204a000d000c5440807030400c032405020303503401046204041c0c40541d1100008480a5001c0c45007a42d0288031120681c21070408019001e020b0407031074000d0600c01060b41841403c0d200404407680082d8000d10080e0892598141500c48800442c07a00c820a401c403003481070060303c0c2d62907009455100000e00001819008000c4c206034074240a1040641c950f40c0ea100c028046182c03107041d010039200004110070f061140d2000052020300d0412000007000e0b030020918004698000184590000c4103082c14440b07800c2500800d12490002540b6106903e29496154a03150900a0059201002050401c030f065010780309411454007000104917510381038544d040941320030a44009242944007030091070b899005d10321035038468603000700946504004160f1441640415 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 415098057 1250 415096807 415096811
    0x10612050718200a020f0607021c1202030115110f0303060f0d0b040305090a05041a12031b0717030702090612010b030109060b0a0509090703060f0b0301180b1513050406 74
    0x41d40607007603510783c2525815681c0c81d0700f900c4d0f5811a10103440c00c0411102110303079610042c204445268000364010901c8030802c00c150303585180480694a0500d4004000d40031030000c800851b030002800e00441003a03010340d030b8420110f00c181465070b40301c3d040f0641c1e40209820070000102d445c00e0010740300f04040da0160044000e203c0c0d541790145821020748080313000400000b0040790078903000030610003601044504010b1244074002e0140c920440d14070040c090010009201a8118180300b5640ca802072400300760488514110300d5a294050b5004454448080ba901d00c0c0319484008144c404141c0d01406254042c2c4442c41006141250040b84c41a41c1d92582d0311030f00180c03028003130b005010344124001b0440c0107060703040002c1d40041d0f4110f14001c440c84070030046541c00c002100d408890300080006109040b140c103402c040c200e0320792415015070038082e981c0380e04501c181c1c00ba00c40c0381c000d103860281c940b07d40c42c0507507075200034609481d803100d4007145e0464a00301907413105070042d11036540 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 415099307 1250 415098057 415098071
    0xc160203030703030c0801050a06091806080706020309010216180b0307050409030305060f040b0102060408070f120f080c2a1908040f05040b06030403110f010617010612050718 77
    0x7451030303004a80c100d0000c0d803039039002d031185604401d04e18003514080b07403014a003504040004109056034411006406c03410106285000015071041016010b03e605032102c680d140c99029541351b004030441030061240340d400020f4803881403801c00c1602c44c0c0b4a94200c800e0f22070343c00c1070b0107019961080c075030600809200180a6480344918994544a500c0101d4585480f07005c0000c1c491100e500302e4011340c00c08840e1039041c0e034046013880d44264031110751511130085040414601101c07460081042c00701e90440c6042e2500565859071005140e5207d9079141d988110351903c5005040764040c1d13281c400701114900451015403190900700784000c03034000e04a00e1100d590200984c0c4410703100c0c000c2c0000d0a21480c0324102d8958080c1905a17401c8c400b00e0501c1d03001c501c2500c001400036042011241d55482115024011403203091030100092010341d8484e0001040c2c031414010b210903a40c605180050200c0c0c0203007206282c5030300302014016087c50485001000000c0c40c0007070303290343e41c4c1e038903 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 415100557 1250 415099307 415099309
    0x120608010501090e0c04140402011107120803180a050618030d0f020c0609070506190c0b0405010c020f0c030604030f02100c0c20150f0f04030501090c1d0c1602 70
    0x800c4500a112003140400c07104d6003e01d0f918100b18882030014004e5007809565203000d4039181002d604240e0a180504030090100c600e54140750941d000a00070080200c1c080007070105080166014014000300005204034080c0d1807a42c5240b0100300402d9504241e000508021109004071240007a000540349008154240001181c4e00205402043c80d404200218440c0c4200030903940005444000e2002504080004800740680d403020307000c81e00c0c284075000020344500380b10300001c0d80c0b08200f9080e074203040c50014041d1940c481c00d08014490324403801401c07000001c280360040c03c00b0380940700d551601d4400701c1d03081c4000c100000c254451848102041c1c2d03414822400420510b5980320b084280d40c0c5084c010034940380d06c00148030201040c420b0080c1d40e81da45200f40110310011125503405c4502001d10302c60240100c50303140094007150020134414190004140e180c450050204220345450724007a0600c3d8200714800100d012a002030318940e1450010040c500701594134004240c4241c1c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 415101807 1250 415100557 415100561
    0xb040605040617240c0d09060504030e040c0c02180a061701020a12091109061c0c03060b010314070804030203070803010605120108120d1802030304030803040b090303060a0612060801 80
    0xd804004142c0d000f800c3e40d00000c10a000d40b82002c441c4030203500004140403405022004040c0a02c3c0400e0300016584030201d04a522904949510030414005450203017005000c2107440070440c1d0296080074050384445205071440481558010f010218801802c105600c001100522100780c10741d40d807201161402402450a41924072a000540e0303644103102c00420402c030041c9031010b4241451400400a85c941c540300c03d8000068892144982c4d4203400a400c40f1074141007501d50f403010b04c8480061010a110440c1540d004000901c0f828520500460440e024a141c0c003401413108004902c4c8684640901c0790084d000744122801c4c400c4680310390140354800e0380040045840020001c10700c0c10608180ca004008580107403210032103010b1207080034070441c04030504140d510905206080d00007c003504e1300f107030003504a988954407480e12548a40c0300ba1419581c200c2d100340000c0844100100f140c3c404c0c200030b0903a5102e42e19040e01074410400344c60400080ca0b444030004140c4ca8424 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 415103057 1250 415101807 415101809
    0xa0807031202070503060720161e0e060d0b04060222030b1003030503010b0a2309012a1103100c1d06190509120f06040c090912030b0406050406 63
    0x565a00070004a20318000c1c2c6410311075801940641c0246081010450b0030400040501c5900840a01c2c141105859581000300700c100302c804001c4c02100c00b0503060101c204016402c4c2400320f121000381c1e124030103180b804400300d5089500030a15a80f000000d41e20401d0203401c68410080903061060515845c0360134a040c43c0e80305079643c0e04403010010f0019642d0b030260801c00e5500303042451815500c00504d144414010380400141c000381c1c010401d0b00c0b90b0803000d241400010050010302651100d006940c2c8a807840781d0014400c40307151001208003001802d10488030800a8001c41d82d2551038501d0214850040c0394503008046800310140d840b4010b039920440207070b9a0045c00f4206103c5200c010607007540050040350107000c800e460038024101006101c800b801c01c4ca031911301c4540050015100324082895900071800300c3d5468200018513030380118403d0900982c081c0d10744402500321a00c000c405000d004800e140b440d100c60007030780401c25510024001141e441e4030b800118040d5411 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 415104307 1250 415103057 415103063
    0x60f0a1208071104020a0804030e030703020a08030d110f070201080601030204030b040606030213020708041406041509061409100c0201090b0427052404060e0f060a0b0a05040e060a080703 82
    0x1000480c00b04001655040100c0c15004540c21810300300301d60002880d40f03000500060600076114903e8030681d40421003c401190300400c07003107049413540d81035501c0380c02481c1050401800c00328241140040f40040da080c1c0c804500180781051155001180c4810002c1e1000b418942d0800020021130317a00d880c114482d500901d804203045103148103200103030b840405120340072441446070000103540300c411241181d403c10030b01070703000f55940300081071803140f039200700c1602d2844140c0c0e0100705e42104420003100c80c2c0b52900c81c0700c42800e14840b0614803071104a154080c5c265040110680c1c0100c03000c0c118940180741042540362103502052066005400c02c9040482100745010450440401d0840004040200344658101850b60302c00320300c1100509270001d14524410501da8a030b41c1e1084009100045080c151800c2c9254080000c43c42a20903038025200e00b003012900111480442d10840d050380d4846160602d0907a445502e0180546a00c0d031005d40c1c40c800040380b4408000c0d400103580 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 415105557 1250 415104307 415104323
    0xa06120c1229090105150306120a031d010918020c010603080a0e19050a0e1f140909060903160c05090c21040c05011b0218010824060f0a12 61
    0x31030381800302c040a4904168500c190240e400500031501d450860036110903402c51420b407a038840b54000f1f01d4080c80380c1e290868510807500c10f0300506a100e1496070050035180002c001d0080c40000440c0c512080340208004c543c41810492200340c01c644c010403101c803001d800004c4150720307581c5107801d951040c03000100092035248a41198501940c003801d042c1d024100e151040391602d408150050102e02c40e800c1c980c0a40c0e00058070340480303000c02e07085031a602c0c05207180642c2c40b121064a9014207210182c040c801c15000541c42c1280011402e01866042e0015030501440080c091300c05204200f08071003041e950702e0300082c80c3e1655190540280d03805902d031601c0f00e007541e90140c1c101c040d51007181002c18600d030a020120328003044d03140641e00d00f841d00b015881003221007215041d031a41e00c000d400c546000c0000010110080107a81600da04074259410321425102e48007004035203402409004051030041246850081c0301c03000c0c031032805020a0440395030f424545401c200c414100b030310000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 415106807 1250 415105557 415105601
    0xf080a020a0516060215150103020a050d05010e0f0106050a08240603011d16080105060a210905060a270c08070e061912200a12110a06120c12 62
    0x394046c0b18083c6100c0340442c2c548401e107450315208403502e001d5101103051560000c0d41142e124821000c5404000e9078040a00c102c0d651100084150502141c290190042c0e010011030f0710792060003101da00540030760300d1400c551034001d40c190103903034122071b07180c0d80d00100001148a500e410300038500800b103c0c00901b01d40c40318100e0000030080c0081c80011043c03100c1144544440c0c10002c40d5054400a0310002d4858812450540da5180d41520b42a8010610201d0400e401c10380d40280400610031070644030f80743c40b440e5481080d00d00303441801500e145c1180d8600702c16003082140450150040005845c031070340d5007400509000850300203130707810702c408010807031030341030410501c1249032074403485040713503840d24101301410702414030000d0990508500d1126030b10071050f036840c00f43c80010300c04e0a13000d64410204031030542d440c4040314020480450501c4070f24001030840b00301c4e40c56451709104844903a5402c4020000c00b20390748240042038018001c07141c600d100d08561000b014404003041 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 415107913 1106 415106807 415106819
    0x519140702120105060f0a0b0d020c01150815010e1005010804030c02060a0903031214060108090f190201031505060a1101180b1b070f080a020a0516 65
    0xb280d081c030384411000e4010b5002a000705011600c01800d1060701050111882d06407040e41003c0805015410b60101190001c1c4640d503440da00003c3d510404680d9241782c2ca0032a000b075802c076481803070b498400d81c80d06810513026000d100310b41d0f10f452410401034000c0300304a00615042150b036901150070540102903100030168010640ca8a8500000300144100b103d4403040d800101d401c500c07503010801907c101109040620300700c41e200d60b41e1070015205004050020b400511404070807091888042c00408140511000e2500c10f000302800010706a815072078220024949405041007583e42c0e8108407400407035642800c117102d0303a440c040781d80140759600048440450b8000d0041c100140ba1030a2441041e8000000b0703880a0a5107040c2c4182c001c82500a000b9442028160081440040944002c0c0f540c0d01c1152011100d5695180c18960000101000502400414014 = true := by decide +kernel

theorem cover : BRFrame.Cov 414928057 415107913 := by
  have h0 := BRFrame.cov_init 414928057
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414928057 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 414928057 ≤ n) (h2 : n < 415107913) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
